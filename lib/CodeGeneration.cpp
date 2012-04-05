//===------ CodeGeneration.cpp - Code generate the Scops. -----------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// The CodeGeneration pass takes a Scop created by ScopInfo and translates it
// back to LLVM-IR using Cloog.
//
// The Scop describes the high level memory behaviour of a control flow region.
// Transformation passes can update the schedule (execution order) of statements
// in the Scop. Cloog is used to generate an abstract syntax tree (clast) that
// reflects the updated execution order. This clast is used to create new
// LLVM-IR that is computational equivalent to the original control flow region,
// but executes its code in the new execution order defined by the changed
// scattering.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "polly-codegen"

#include "polly/LinkAllPasses.h"
#include "polly/Support/GICHelper.h"
#include "polly/Support/ScopHelper.h"
#include "polly/Cloog.h"
#include "polly/CodeGeneration.h"
#include "polly/Dependences.h"
#include "polly/ScopInfo.h"
#include "polly/TempScopInfo.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/IRBuilder.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolutionExpander.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Target/TargetData.h"
#include "llvm/Module.h"
#include "llvm/ADT/SetVector.h"

#define CLOOG_INT_GMP 1
#include "cloog/cloog.h"
#include "cloog/isl/cloog.h"

#include <vector>
#include <utility>

using namespace polly;
using namespace llvm;

struct isl_set;

namespace polly {

bool EnablePollyVector;
bool EnablePollyOpenMP;
  
static BasicBlock *Header;

static cl::opt<bool, true>
Vector("enable-polly-vector",
       cl::desc("Enable polly vector code generation"), cl::Hidden,
       cl::location(EnablePollyVector), cl::init(false));

static cl::opt<bool, true>
OpenMP("enable-polly-openmp",
       cl::desc("Generate OpenMP parallel code"), cl::Hidden,
       cl::location(EnablePollyOpenMP),
       cl::value_desc("OpenMP code generation enabled if true"),
       cl::init(false));

static cl::opt<bool>
AtLeastOnce("enable-polly-atLeastOnce",
       cl::desc("Give polly the hint, that every loop is executed at least"
                "once"), cl::Hidden,
       cl::value_desc("OpenMP code generation enabled if true"),
       cl::init(false));

static cl::opt<bool>
Aligned("enable-polly-aligned",
       cl::desc("Assumed aligned memory accesses."), cl::Hidden,
       cl::value_desc("OpenMP code generation enabled if true"),
       cl::init(false));

typedef DenseMap<const Value*, Value*> ValueMapT;
typedef DenseMap<const char*, Value*> CharMapT;
typedef std::vector<ValueMapT> VectorValueMapT;

// Create a new loop.
//
// @param Builder The builder used to create the loop.  It also defines the
//                place where to create the loop.
// @param UB      The upper bound of the loop iv.
// @param Stride  The number by which the loop iv is incremented after every
//                iteration.
static void createLoop(IRBuilder<> *Builder, Value *LB, Value *UB, APInt Stride,
                PHINode*& IV, BasicBlock*& AfterBB, Value*& IncrementedIV,
                DominatorTree *DT) {
  Function *F = Builder->GetInsertBlock()->getParent();
  LLVMContext &Context = F->getContext();

  BasicBlock *PreheaderBB = Builder->GetInsertBlock();
  BasicBlock *HeaderBB = BasicBlock::Create(Context, "polly.loop_header", F);
  BasicBlock *BodyBB = BasicBlock::Create(Context, "polly.loop_body", F);
  AfterBB = BasicBlock::Create(Context, "polly.after_loop", F);

  Builder->CreateBr(HeaderBB);
  DT->addNewBlock(HeaderBB, PreheaderBB);

  Builder->SetInsertPoint(BodyBB);

  Builder->SetInsertPoint(HeaderBB);

  // Use the type of upper and lower bound.
  assert(LB->getType() == UB->getType()
         && "Different types for upper and lower bound.");

  IntegerType *LoopIVType = dyn_cast<IntegerType>(UB->getType());
  assert(LoopIVType && "UB is not integer?");

  // IV
  IV = Builder->CreatePHI(LoopIVType, 2, "polly.loopiv");
  IV->addIncoming(LB, PreheaderBB);

  // IV increment.
  Value *StrideValue = ConstantInt::get(LoopIVType,
                                        Stride.zext(LoopIVType->getBitWidth()));
  IncrementedIV = Builder->CreateAdd(IV, StrideValue, "polly.next_loopiv");

  // Exit condition.
  if (AtLeastOnce) { // At least on iteration.
    UB = Builder->CreateAdd(UB, Builder->getInt64(1));
    Value *CMP = Builder->CreateICmpEQ(IV, UB);
    Builder->CreateCondBr(CMP, AfterBB, BodyBB);
  } else { // Maybe not executed at all.
    Value *CMP = Builder->CreateICmpSLE(IV, UB);
    Builder->CreateCondBr(CMP, BodyBB, AfterBB);
  }
  DT->addNewBlock(BodyBB, HeaderBB);
  DT->addNewBlock(AfterBB, HeaderBB);

  Builder->SetInsertPoint(BodyBB);
}

class BlockGenerator {
  IRBuilder<> &Builder;
  ValueMapT &VMap;
  VectorValueMapT &ValueMaps;
  Scop &S;
  ScopStmt &statement;
  isl_set *scatteringDomain;
  bool parallelCodeGeneration;

public:
  BlockGenerator(IRBuilder<> &B, ValueMapT &vmap, VectorValueMapT &vmaps,
                 ScopStmt &Stmt, isl_set *domain, bool pCG)
    : Builder(B), VMap(vmap), ValueMaps(vmaps), S(*Stmt.getParent()),
    statement(Stmt), scatteringDomain(domain), parallelCodeGeneration(pCG) {}

  const Region &getRegion() {
    return S.getRegion();
  }

  Value* makeVectorOperand(Value *operand, int vectorWidth) {
    if (operand->getType()->isVectorTy())
      return operand;

    VectorType *vectorType = VectorType::get(operand->getType(), vectorWidth);
    Value *vector = UndefValue::get(vectorType);
    vector = Builder.CreateInsertElement(vector, operand, Builder.getInt32(0));

    std::vector<Constant*> splat;

    for (int i = 0; i < vectorWidth; i++)
      splat.push_back (Builder.getInt32(0));

    Constant *splatVector = ConstantVector::get(splat);

    return Builder.CreateShuffleVector(vector, vector, splatVector);
  }

  /// FIX 3
  Value *mapInvariantInstruction(const Instruction *Inst) {
 DEBUG(dbgs() << "qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq\n\n");
  statement.getParent()->getRegion().dump();
 DEBUG(dbgs() << "qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq\n\n");
  Inst->getParent()->dump();
 DEBUG(dbgs() << "qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq\n\n");
  assert(!statement.getParent()->getRegion().contains(Inst->getParent())
         && "Instruction was not invariant in this SCoP");

  // As we first check the GlobalMap an instruction should not be cloned twice.
  if (VMap.count(Inst)) {
    return VMap[Inst];
  }

  assert(!isa<PHINode>(Inst) && "PHINodes cannot be mapped this way");

  // Get the omp.setup BB
  // I assume there are better ways to do this (argument for this builder)
  BasicBlock *ompSetup = &Builder.GetInsertBlock()->getParent()->getEntryBlock();
  // Assert the name of the ompSetup BB to start with omp.setup
  assert(!ompSetup->getName().find("omp.setup") 
         && "Could not find the omp.setup block");

  // As the omp.setup block could be split we have to move until the last split
  // This is a VERY VERY UGLY HACK to find a BB after the values stored in the
  //  userContext are loaded again
  while (true) {
    TerminatorInst *termInst = ompSetup->getTerminator();
    if (termInst->getNumSuccessors() != 1) break;
    BasicBlock *tmpBlock = termInst->getSuccessor(0);
    if (!tmpBlock->getName().find("omp.setup")) break;
    ompSetup = tmpBlock;
  }

  // Save the old insert point
  BasicBlock::iterator oldInsertPoint = Builder.GetInsertPoint();
  
  // Set the new one (right before the terminator instruction of omp.setup)
  Builder.SetInsertPoint(--(ompSetup->end()));

  // Copy the instruction as it is needed in the subfunction
  // HACK 
  // To reuse existing code GlobalMap is used as BBMap here. This should only
  // cause overhead but not affect the result.
  copyInstScalar(Inst, VMap);

  // Assert a new mapping
  assert(VMap.count(Inst) && "Invariant instruction should be mapped now"); 

  // Restore the old insert point
  Builder.SetInsertPoint(oldInsertPoint);

  return VMap[Inst];
}


  Value* getOperand(const Value *oldOperand, ValueMapT &BBMap,
                    ValueMapT *VectorMap = 0) {
    const Instruction *OpInst = dyn_cast<Instruction>(oldOperand);
   DEBUG(dbgs() << "Old Operand: " << *oldOperand << "\n");
    
    if (!OpInst) {
      /// FIX 1 
      ///
      /// Operands which are no instructions could be arguments which 
      /// need to be mapped 
     DEBUG(dbgs() << "Old Operand is no Instruction " << *oldOperand << "   " 
             << VMap.count(oldOperand) << "\n");
      if (VMap.count(oldOperand))
        return VMap[oldOperand];
      else
        return const_cast<Value*>(oldOperand);
    }

   DEBUG(dbgs() << "before vector map: Old Operand: " << *oldOperand << "\n");

    if (VectorMap && VectorMap->count(oldOperand))
      return (*VectorMap)[oldOperand];

   DEBUG(dbgs() << "after vector map: Old Operand: " << *oldOperand << "\n");

    // IVS and Parameters.
    if (VMap.count(oldOperand)) {
      Value *NewOperand = VMap[oldOperand];
     DEBUG(dbgs() << "  New Operand: " << *NewOperand << "\n");

      // Insert a cast if types are different
      if (oldOperand->getType()->getScalarSizeInBits()
          < NewOperand->getType()->getScalarSizeInBits())
        NewOperand = Builder.CreateTruncOrBitCast(NewOperand,
                                                   oldOperand->getType());

     DEBUG(dbgs() << "  New Operand: " << *NewOperand << "\n");
      return NewOperand;
    }
   DEBUG(dbgs() << "  after New Operand: " << *oldOperand << "\n");

    // Instructions calculated in the current BB.
    if (BBMap.count(oldOperand)) {
      return BBMap[oldOperand];
    }

    // Ignore instructions that are referencing ops in the old BB. These
    // instructions are unused. They where replace by new ones during
    // createIndependentBlocks().
    if (!getRegion().contains(OpInst->getParent())) {
      if (parallelCodeGeneration)
        return mapInvariantInstruction(OpInst);
      else
        return const_cast<Value*>(oldOperand);
    }
    //assert(0);
    return NULL;
  }

  Type *getVectorPtrTy(const Value *V, int vectorWidth) {
    PointerType *pointerType = dyn_cast<PointerType>(V->getType());
    assert(pointerType && "PointerType expected");

    Type *scalarType = pointerType->getElementType();
    VectorType *vectorType = VectorType::get(scalarType, vectorWidth);

    return PointerType::getUnqual(vectorType);
  }

  /// @brief Load a vector from a set of adjacent scalars
  ///
  /// In case a set of scalars is known to be next to each other in memory,
  /// create a vector load that loads those scalars
  ///
  /// %vector_ptr= bitcast double* %p to <4 x double>*
  /// %vec_full = load <4 x double>* %vector_ptr
  ///
  Value *generateStrideOneLoad(const LoadInst *load, ValueMapT &BBMap,
                               int size) {
    const Value *pointer = load->getPointerOperand();
    Type *vectorPtrType = getVectorPtrTy(pointer, size);
    Value *newPointer = getOperand(pointer, BBMap);
    Value *VectorPtr = Builder.CreateBitCast(newPointer, vectorPtrType,
                                             "vector_ptr");
    LoadInst *VecLoad = Builder.CreateLoad(VectorPtr,
                                        load->getNameStr()
                                        + "_p_vec_full");
    if (!Aligned)
      VecLoad->setAlignment(8);

    return VecLoad;
  }

  /// @brief Load a vector initialized from a single scalar in memory
  ///
  /// In case all elements of a vector are initialized to the same
  /// scalar value, this value is loaded and shuffeled into all elements
  /// of the vector.
  ///
  /// %splat_one = load <1 x double>* %p
  /// %splat = shufflevector <1 x double> %splat_one, <1 x
  ///       double> %splat_one, <4 x i32> zeroinitializer
  ///
  Value *generateStrideZeroLoad(const LoadInst *load, ValueMapT &BBMap,
                                int size) {
    const Value *pointer = load->getPointerOperand();
    Type *vectorPtrType = getVectorPtrTy(pointer, 1);
    Value *newPointer = getOperand(pointer, BBMap);
    Value *vectorPtr = Builder.CreateBitCast(newPointer, vectorPtrType,
                                             load->getNameStr() + "_p_vec_p");
    LoadInst *scalarLoad= Builder.CreateLoad(vectorPtr,
                                          load->getNameStr() + "_p_splat_one");

    if (!Aligned)
      scalarLoad->setAlignment(8);

    std::vector<Constant*> splat;

    for (int i = 0; i < size; i++)
      splat.push_back (Builder.getInt32(0));

    Constant *splatVector = ConstantVector::get(splat);

    Value *vectorLoad = Builder.CreateShuffleVector(scalarLoad, scalarLoad,
                                                    splatVector,
                                                    load->getNameStr()
                                                    + "_p_splat");
    return vectorLoad;
  }


  /// @Load a vector from scalars distributed in memory
  ///
  /// In case some scalars a distributed randomly in memory. Create a vector
  /// by loading each scalar and by inserting one after the other into the
  /// vector.
  ///
  /// %scalar_1= load double* %p_1
  /// %vec_1 = insertelement <2 x double> undef, double %scalar_1, i32 0
  /// %scalar 2 = load double* %p_2
  /// %vec_2 = insertelement <2 x double> %vec_1, double %scalar_1, i32 1
  ///
  Value *generateUnknownStrideLoad(const LoadInst *load,
                                   VectorValueMapT &scalarMaps,
                                   int size) {
    const Value *pointer = load->getPointerOperand();
    PointerType *pointerType = dyn_cast<PointerType>(pointer->getType());
    assert(pointerType && "No valid pointer type");

   DEBUG(dbgs() << *pointer << ":" << *pointer->getType() << " " 
           << *dyn_cast<PointerType>(pointer->getType())->getElementType()<<"\n");

    Type *castType = 0;
    VectorType *vectorType;
    //if (VectorType::isValidElementType(pointerType->getElementType())) { 
    vectorType = VectorType::get(pointerType->getElementType(), size);
    //} else {
      //dbgs() << "no valid element";
      //castType   = Builder.getInt8Ty();
      //vectorType = VectorType::get(castType, size);
    //}

    Value *vector = UndefValue::get(vectorType);

    for (int i = 0; i < size; i++) {
      Value *newPointer = getOperand(pointer, scalarMaps[i]);
      Value *scalarLoad = Builder.CreateLoad(newPointer,
                                             load->getNameStr() + "_p_scalar_");
      if (castType)
        scalarLoad = Builder.CreatePointerCast(scalarLoad, castType);
      vector = Builder.CreateInsertElement(vector, scalarLoad,
                                           Builder.getInt32(i),
                                           load->getNameStr() + "_p_vec_");
    }

    return vector;
  }

  /// @brief Get the memory access offset to be added to the base address
  std::vector <Value*> getMemoryAccessIndex(isl_map *accessRelation,
                                            Value *baseAddr) {
    isl_int offsetMPZ;
    isl_int_init(offsetMPZ);

    assert((isl_map_dim(accessRelation, isl_dim_out) == 1)
           && "Only single dimensional access functions supported");

    if (isl_map_plain_is_fixed(accessRelation, isl_dim_out,
                               0, &offsetMPZ) == -1)
      errs() << "Only fixed value access functions supported\n";

    // Convert the offset from MPZ to Value*.
    APInt offset = APInt_from_MPZ(offsetMPZ);
    Value *offsetValue = ConstantInt::get(Builder.getContext(), offset);
    PointerType *baseAddrType = dyn_cast<PointerType>(baseAddr->getType());
    Type *arrayType = baseAddrType->getElementType();
    Type *arrayElementType = dyn_cast<ArrayType>(arrayType)->getElementType();
    offsetValue = Builder.CreateSExtOrBitCast(offsetValue, arrayElementType);

    std::vector<Value*> indexArray;
    Value *nullValue = Constant::getNullValue(arrayElementType);
    indexArray.push_back(nullValue);
    indexArray.push_back(offsetValue);

    isl_int_clear(offsetMPZ);
    return indexArray;
  }

  /// @brief Get the new operand address according to the changed access in
  ///        JSCOP file.
  Value *getNewAccessOperand(isl_map *newAccessRelation, Value *baseAddr,
                             const Value *oldOperand, ValueMapT &BBMap) {
    std::vector<Value*> indexArray = getMemoryAccessIndex(newAccessRelation,
                                                          baseAddr);
    Value *newOperand = Builder.CreateGEP(baseAddr, indexArray,
                                          "p_newarrayidx_");
    return newOperand;
  }

  /// @brief Generate the operand address
  Value *generateLocationAccessed(const Instruction *Inst,
                                  const Value *pointer, ValueMapT &BBMap ) {
    MemoryAccess &Access = statement.getAccessFor(Inst);
    isl_map *CurrentAccessRelation = Access.getAccessRelation();
    isl_map *NewAccessRelation = Access.getNewAccessRelation();

    assert(isl_map_has_equal_space(CurrentAccessRelation, NewAccessRelation)
           && "Current and new access function use different spaces");

    Value *NewPointer;

    if (!NewAccessRelation) {
      NewPointer = getOperand(pointer, BBMap);
    } else {
      Value *BaseAddr = const_cast<Value*>(Access.getBaseAddr());
      NewPointer = getNewAccessOperand(NewAccessRelation, BaseAddr, pointer,
                                       BBMap);
    }

    isl_map_free(CurrentAccessRelation);
    isl_map_free(NewAccessRelation);
    return NewPointer;
  }

  Value *generateScalarLoad(const LoadInst *load, ValueMapT &BBMap) {
    const Value *pointer = load->getPointerOperand();
    const Instruction *Inst = dyn_cast<Instruction>(load);
    Value *newPointer = generateLocationAccessed(Inst, pointer, BBMap);
    Value *scalarLoad = Builder.CreateLoad(newPointer,
                                           load->getNameStr() + "_p_scalar_");
    return scalarLoad;
  }

  /// @brief Load a value (or several values as a vector) from memory.
  void generateLoad(const LoadInst *load, ValueMapT &vectorMap,
                    VectorValueMapT &scalarMaps, int vectorWidth) {
    if (scalarMaps.size() == 1) {
      scalarMaps[0][load] = generateScalarLoad(load, scalarMaps[0]);
      return;
    }

    Value *newLoad;

    MemoryAccess &Access = statement.getAccessFor(load);

    assert(scatteringDomain && "No scattering domain available");

    if (Access.isStrideZero(scatteringDomain))
      newLoad = generateStrideZeroLoad(load, scalarMaps[0], vectorWidth);
    else if (Access.isStrideOne(scatteringDomain))
      newLoad = generateStrideOneLoad(load, scalarMaps[0], vectorWidth);
    else
      newLoad = generateUnknownStrideLoad(load, scalarMaps, vectorWidth);

    vectorMap[load] = newLoad;
  }

  void copyUnaryInst(const UnaryInstruction *Inst, ValueMapT &BBMap,
                     ValueMapT &VectorMap, int VectorDimension,
                     int VectorWidth) {
    Value *NewOperand = getOperand(Inst->getOperand(0), BBMap, &VectorMap);
    NewOperand = makeVectorOperand(NewOperand, VectorWidth);

    if (const CastInst *Cast = dyn_cast<CastInst>(Inst)) {
      VectorType *DestType = VectorType::get(Inst->getType(), VectorWidth);
      VectorMap[Inst] = Builder.CreateCast(Cast->getOpcode(), NewOperand,
                                           DestType);
    } else
      llvm_unreachable("Can not generate vector code for instruction");
    return;
  }

  void copyBinInst(const BinaryOperator *Inst, ValueMapT &BBMap,
                   ValueMapT &vectorMap, int vectorDimension, int vectorWidth) {
    Value *opZero = Inst->getOperand(0);
    Value *opOne = Inst->getOperand(1);

    Value *newOpZero, *newOpOne;
    newOpZero = getOperand(opZero, BBMap, &vectorMap);
    newOpOne = getOperand(opOne, BBMap, &vectorMap);

    newOpZero = makeVectorOperand(newOpZero, vectorWidth);
    newOpOne = makeVectorOperand(newOpOne, vectorWidth);

    Value *newInst = Builder.CreateBinOp(Inst->getOpcode(), newOpZero,
                                         newOpOne,
                                         Inst->getNameStr() + "p_vec");
    vectorMap[Inst] = newInst;

    return;
  }

  void copyVectorStore(const StoreInst *store, ValueMapT &BBMap,
                       ValueMapT &vectorMap, VectorValueMapT &scalarMaps,
                       int vectorDimension, int vectorWidth) {
    // In vector mode we only generate a store for the first dimension.
    if (vectorDimension > 0)
      return;

    MemoryAccess &Access = statement.getAccessFor(store);

    assert(scatteringDomain && "No scattering domain available");

    const Value *pointer = store->getPointerOperand();
    Value *vector = getOperand(store->getValueOperand(), BBMap, &vectorMap);

    if (Access.isStrideOne(scatteringDomain)) {
      Type *vectorPtrType = getVectorPtrTy(pointer, vectorWidth);
      Value *newPointer = getOperand(pointer, BBMap, &vectorMap);

      Value *VectorPtr = Builder.CreateBitCast(newPointer, vectorPtrType,
                                               "vector_ptr");
      StoreInst *Store = Builder.CreateStore(vector, VectorPtr);

      if (!Aligned)
        Store->setAlignment(8);
    } else {
      for (unsigned i = 0; i < scalarMaps.size(); i++) {
        Value *scalar = Builder.CreateExtractElement(vector,
                                                     Builder.getInt32(i));
        Value *newPointer = getOperand(pointer, scalarMaps[i]);
        Builder.CreateStore(scalar, newPointer);
      }
    }

    return;
  }

  /// FIX 2 
  /// 
  /// Not all instructions are cloned, but their operands were.
  /// This leads to unresolved dependencies (into other functions for openMP code)
  bool hasOnlyRemovedUses(const Instruction *Inst, ValueMapT &BBMap) {
   DEBUG(dbgs() << " has only removed uses " << *Inst << "\n");
    for (Instruction::const_use_iterator UI = Inst->use_begin(), UE = Inst->use_end();
         UI != UE; UI++) {
     DEBUG(dbgs() << " == use " << **UI << "\n");
      if (BBMap.count(*UI)) 
        return false;
    }
    
    return true;
  }

  void removeInstruction(const Instruction *Inst, ValueMapT &BBMap) {
   DEBUG(dbgs() << "\n\n removeInstruction: " << *Inst << "\n");    
    if (BBMap.count(Inst)) {
      Instruction *I = cast<Instruction>(BBMap[Inst]);
     DEBUG(dbgs() << "\n\n eraseInstruction: " << *I << "\n");
      I->eraseFromParent();
      BBMap.erase(Inst);
    }

    for (Instruction::const_op_iterator OI = Inst->op_begin(),
         OE = Inst->op_end(); OI != OE; ++OI) {
      Value *OldOperand = *OI;

      if (const Instruction *OldOperandInst = dyn_cast<Instruction>(OldOperand)) {
        //assert(BBMap.count(OldOperandInst) && "Operand was removed before use");
        //Instruction *NewOperandInst = dyn_cast<Instruction>(BBMap[OldOperandInst]);
        if (!isa<PHINode>(OldOperandInst) && hasOnlyRemovedUses(OldOperandInst, BBMap)) 
          removeInstruction(OldOperandInst, BBMap); 
      }
    }
  }
  /// FIX 2 ====================================================================

  void copyInstScalar(const Instruction *Inst, ValueMapT &BBMap) {
    Instruction *NewInst = Inst->clone();

   DEBUG(dbgs() << " copyInstScalar: \n\t\t old: ");
   DEBUG(dbgs() << *Inst << "\n");

    // Replace old operands with the new ones.
    for (Instruction::const_op_iterator OI = Inst->op_begin(),
         OE = Inst->op_end(); OI != OE; ++OI) {
      Value *OldOperand = *OI;
      Value *NewOperand = getOperand(OldOperand, BBMap);

      if (!NewOperand) {
        assert(!isa<StoreInst>(NewInst)
               && "Store instructions are always needed!");
        delete NewInst;
       DEBUG(dbgs() << " do not copyInstScalar: \t\t: " << *Inst << "\n");
        /// FIX 2
        removeInstruction(Inst, BBMap); 
        return;
      }

      NewInst->replaceUsesOfWith(OldOperand, NewOperand);
    }

    Builder.Insert(NewInst);
    BBMap[Inst] = NewInst;

    if (!NewInst->getType()->isVoidTy() && !Inst->getName().empty())
      NewInst->setName("p_" + Inst->getName());

   DEBUG(dbgs() << " \n\t\t new: " << *NewInst << " \n");
  }

  bool hasVectorOperands(const Instruction *Inst, ValueMapT &VectorMap) {
    for (Instruction::const_op_iterator OI = Inst->op_begin(),
         OE = Inst->op_end(); OI != OE; ++OI)
      if (VectorMap.count(*OI))
        return true;
    return false;
  }

  int getVectorSize() {
    return ValueMaps.size();
  }

  bool isVectorBlock() {
    return getVectorSize() > 1;
  }
 

  void copyInstruction(const Instruction *Inst, ValueMapT &BBMap,
                       ValueMapT &vectorMap, VectorValueMapT &scalarMaps,
                       int vectorDimension, int vectorWidth) {
  
   DEBUG(dbgs() << "copyinstruction " << *Inst << "\n");

    // Terminator instructions control the control flow. They are explicitally
    // expressed in the clast and do not need to be copied.
    if (Inst->isTerminator()) {
      /// FIX 2
      removeInstruction(Inst, BBMap); 
      return;
    }

    if (isVectorBlock()) {
      // If this instruction is already in the vectorMap, a vector instruction
      // was already issued, that calculates the values of all dimensions. No
      // need to create any more instructions.
      if (vectorMap.count(Inst)) { 
        /// FIX 2
        removeInstruction(Inst, BBMap); 
        return;
      }
    }

    if (const LoadInst *load = dyn_cast<LoadInst>(Inst)) {
      generateLoad(load, vectorMap, scalarMaps, vectorWidth);
      return;
    }

    if (isVectorBlock() && hasVectorOperands(Inst, vectorMap)) {
      if (const UnaryInstruction *UnaryInst = dyn_cast<UnaryInstruction>(Inst))
        copyUnaryInst(UnaryInst, BBMap, vectorMap, vectorDimension,
                      vectorWidth);
      else if
        (const BinaryOperator *binaryInst = dyn_cast<BinaryOperator>(Inst))
        copyBinInst(binaryInst, BBMap, vectorMap, vectorDimension, vectorWidth);
      else if (const StoreInst *store = dyn_cast<StoreInst>(Inst))
        copyVectorStore(store, BBMap, vectorMap, scalarMaps, vectorDimension,
                          vectorWidth);
      else
        llvm_unreachable("Cannot issue vector code for this instruction");

      return;
    }

    copyInstScalar(Inst, BBMap);
  }
  // Insert a copy of a basic block in the newly generated code.
  //
  // @param Builder The builder used to insert the code. It also specifies
  //                where to insert the code.
  // @param BB      The basic block to copy
  // @param VMap    A map returning for any old value its new equivalent. This
  //                is used to update the operands of the statements.
  //                For new statements a relation old->new is inserted in this
  //                map.
  void copyBB(BasicBlock *BB, DominatorTree *DT) {
    Function *F = Builder.GetInsertBlock()->getParent();
    LLVMContext &Context = F->getContext();
    BasicBlock *CopyBB = BasicBlock::Create(Context,
                                            "polly." + BB->getNameStr()
                                            + ".stmt",
                                            F);
    Builder.CreateBr(CopyBB);
    DT->addNewBlock(CopyBB, Builder.GetInsertBlock());
    Builder.SetInsertPoint(CopyBB);

    // Create two maps that store the mapping from the original instructions of
    // the old basic block to their copies in the new basic block. Those maps
    // are basic block local.
    //
    // As vector code generation is supported there is one map for scalar values
    // and one for vector values.
    //
    // In case we just do scalar code generation, the vectorMap is not used and
    // the scalarMap has just one dimension, which contains the mapping.
    //
    // In case vector code generation is done, an instruction may either appear
    // in the vector map once (as it is calculating >vectorwidth< values at a
    // time. Or (if the values are calculated using scalar operations), it
    // appears once in every dimension of the scalarMap.
    VectorValueMapT scalarBlockMap(getVectorSize());
    ValueMapT vectorBlockMap;

    for (BasicBlock::const_iterator II = BB->begin(), IE = BB->end();
         II != IE; ++II)
      for (int i = 0; i < getVectorSize(); i++) {
        if (isVectorBlock())
          VMap = ValueMaps[i];

        copyInstruction(II, scalarBlockMap[i], vectorBlockMap,
                        scalarBlockMap, i, getVectorSize());
      }
  }
};

/// Class to generate LLVM-IR that calculates the value of a clast_expr.
class ClastExpCodeGen {
  IRBuilder<> &Builder;
  const CharMapT *IVS;

  Value *codegen(const clast_name *e, Type *Ty) {
    CharMapT::const_iterator I = IVS->find(e->name);

    if (I != IVS->end())
      return Builder.CreateSExtOrBitCast(I->second, Ty);
    else
      llvm_unreachable("Clast name not found");
  }

  Value *codegen(const clast_term *e, Type *Ty) {
    APInt a = APInt_from_MPZ(e->val);

    Value *ConstOne = ConstantInt::get(Builder.getContext(), a);
    ConstOne = Builder.CreateSExtOrBitCast(ConstOne, Ty);

    if (e->var) {
      Value *var = codegen(e->var, Ty);
      return Builder.CreateMul(ConstOne, var);
    }

    return ConstOne;
  }

  Value *codegen(const clast_binary *e, Type *Ty) {
    Value *LHS = codegen(e->LHS, Ty);

    APInt RHS_AP = APInt_from_MPZ(e->RHS);

    Value *RHS = ConstantInt::get(Builder.getContext(), RHS_AP);
    RHS = Builder.CreateSExtOrBitCast(RHS, Ty);

    switch (e->type) {
    case clast_bin_mod:
      return Builder.CreateSRem(LHS, RHS);
    case clast_bin_fdiv:
      {
        // floord(n,d) ((n < 0) ? (n - d + 1) : n) / d
        Value *One = ConstantInt::get(Builder.getInt1Ty(), 1);
        Value *Zero = ConstantInt::get(Builder.getInt1Ty(), 0);
        One = Builder.CreateZExtOrBitCast(One, Ty);
        Zero = Builder.CreateZExtOrBitCast(Zero, Ty);
        Value *Sum1 = Builder.CreateSub(LHS, RHS);
        Value *Sum2 = Builder.CreateAdd(Sum1, One);
        Value *isNegative = Builder.CreateICmpSLT(LHS, Zero);
        Value *Dividend = Builder.CreateSelect(isNegative, Sum2, LHS);
        return Builder.CreateSDiv(Dividend, RHS);
      }
    case clast_bin_cdiv:
      {
        // ceild(n,d) ((n < 0) ? n : (n + d - 1)) / d
        Value *One = ConstantInt::get(Builder.getInt1Ty(), 1);
        Value *Zero = ConstantInt::get(Builder.getInt1Ty(), 0);
        One = Builder.CreateZExtOrBitCast(One, Ty);
        Zero = Builder.CreateZExtOrBitCast(Zero, Ty);
        Value *Sum1 = Builder.CreateAdd(LHS, RHS);
        Value *Sum2 = Builder.CreateSub(Sum1, One);
        Value *isNegative = Builder.CreateICmpSLT(LHS, Zero);
        Value *Dividend = Builder.CreateSelect(isNegative, LHS, Sum2);
        return Builder.CreateSDiv(Dividend, RHS);
      }
    case clast_bin_div:
      return Builder.CreateSDiv(LHS, RHS);
    default:
      llvm_unreachable("Unknown clast binary expression type");
    };
  }

  Value *codegen(const clast_reduction *r, Type *Ty) {
    assert((   r->type == clast_red_min
            || r->type == clast_red_max
            || r->type == clast_red_sum)
           && "Clast reduction type not supported");
    Value *old = codegen(r->elts[0], Ty);

    for (int i=1; i < r->n; ++i) {
      Value *exprValue = codegen(r->elts[i], Ty);

      switch (r->type) {
      case clast_red_min:
        {
          Value *cmp = Builder.CreateICmpSLT(old, exprValue);
          old = Builder.CreateSelect(cmp, old, exprValue);
          break;
        }
      case clast_red_max:
        {
          Value *cmp = Builder.CreateICmpSGT(old, exprValue);
          old = Builder.CreateSelect(cmp, old, exprValue);
          break;
        }
      case clast_red_sum:
        old = Builder.CreateAdd(old, exprValue);
        break;
      default:
        llvm_unreachable("Clast unknown reduction type");
      }
    }

    return old;
  }

public:

  // A generator for clast expressions.
  //
  // @param B The IRBuilder that defines where the code to calculate the
  //          clast expressions should be inserted.
  // @param IVMAP A Map that translates strings describing the induction
  //              variables to the Values* that represent these variables
  //              on the LLVM side.
  ClastExpCodeGen(IRBuilder<> &B, CharMapT *IVMap) : Builder(B), IVS(IVMap) {}

  // Generates code to calculate a given clast expression.
  //
  // @param e The expression to calculate.
  // @return The Value that holds the result.
  Value *codegen(const clast_expr *e, Type *Ty) {
    switch(e->type) {
      case clast_expr_name:
	return codegen((const clast_name *)e, Ty);
      case clast_expr_term:
	return codegen((const clast_term *)e, Ty);
      case clast_expr_bin:
	return codegen((const clast_binary *)e, Ty);
      case clast_expr_red:
	return codegen((const clast_reduction *)e, Ty);
      default:
        llvm_unreachable("Unknown clast expression!");
    }
  }

  // @brief Reset the CharMap.
  //
  // This function is called to reset the CharMap to new one, while generating
  // OpenMP code.
  void setIVS(CharMapT *IVSNew) {
    IVS = IVSNew;
  }

};

class ClastStmtCodeGen {
  // The Scop we code generate.
  Scop *S;
  ScalarEvolution &SE;
  DominatorTree *DT;
  ScopDetection *SD;
  Dependences *DP;
  TargetData *TD;

  // The Builder specifies the current location to code generate at.
  IRBuilder<> &Builder;

  // Map the Values from the old code to their counterparts in the new code.
  ValueMapT ValueMap;

  // clastVars maps from the textual representation of a clast variable to its
  // current *Value. clast variables are scheduling variables, original
  // induction variables or parameters. They are used either in loop bounds or
  // to define the statement instance that is executed.
  //
  //   for (s = 0; s < n + 3; ++i)
  //     for (t = s; t < m; ++j)
  //       Stmt(i = s + 3 * m, j = t);
  //
  // {s,t,i,j,n,m} is the set of clast variables in this clast.
  CharMapT *clastVars;

  // Codegenerator for clast expressions.
  ClastExpCodeGen ExpGen;

  // Do we currently generate parallel code?
  bool parallelCodeGeneration;

  std::vector<std::string> parallelLoops;

public:

  const std::vector<std::string> &getParallelLoops() {
    return parallelLoops;
  }

  protected:
  void codegen(const clast_assignment *a) {
    (*clastVars)[a->LHS] = ExpGen.codegen(a->RHS,
      TD->getIntPtrType(Builder.getContext()));
  }

  void codegen(const clast_assignment *a, ScopStmt *Statement,
               unsigned Dimension, int vectorDim,
               std::vector<ValueMapT> *VectorVMap = 0) {
    Value *RHS = ExpGen.codegen(a->RHS,
      TD->getIntPtrType(Builder.getContext()));

    assert(!a->LHS && "Statement assignments do not have left hand side");
    const PHINode *PN;
    PN = Statement->getInductionVariableForDimension(Dimension);
    const Value *V = PN;

    if (VectorVMap)
      (*VectorVMap)[vectorDim][V] = RHS;

    ValueMap[V] = RHS;
  }

  void codegenSubstitutions(const clast_stmt *Assignment,
                            ScopStmt *Statement, int vectorDim = 0,
                            std::vector<ValueMapT> *VectorVMap = 0) {
    int Dimension = 0;

    while (Assignment) {
      assert(CLAST_STMT_IS_A(Assignment, stmt_ass)
             && "Substitions are expected to be assignments");
      codegen((const clast_assignment *)Assignment, Statement, Dimension,
              vectorDim, VectorVMap);
      Assignment = Assignment->next;
      Dimension++;
    }
  }

  void codegen(const clast_user_stmt *u, std::vector<Value*> *IVS = NULL,
               const char *iterator = NULL, isl_set *scatteringDomain = 0) {
    ScopStmt *Statement = (ScopStmt *)u->statement->usr;
    BasicBlock *BB = Statement->getBasicBlock();

    if (u->substitutions)
      codegenSubstitutions(u->substitutions, Statement);

    int vectorDimensions = IVS ? IVS->size() : 1;

    VectorValueMapT VectorValueMap(vectorDimensions);

    if (IVS) {
      assert (u->substitutions && "Substitutions expected!");
      int i = 0;
      for (std::vector<Value*>::iterator II = IVS->begin(), IE = IVS->end();
           II != IE; ++II) {
        (*clastVars)[iterator] = *II;
        codegenSubstitutions(u->substitutions, Statement, i, &VectorValueMap);
        i++;
      }
    }

    BlockGenerator Generator(Builder, ValueMap, VectorValueMap, *Statement,
                             scatteringDomain, parallelCodeGeneration);
    Generator.copyBB(BB, DT);
  }

  void codegen(const clast_block *b) {
    if (b->body)
      codegen(b->body);
  }

  /// @brief Create a classical sequential loop.
  void codegenForSequential(const clast_for *f, Value *lowerBound = 0,
                                                Value *upperBound = 0) {
    APInt Stride = APInt_from_MPZ(f->stride);
    PHINode *IV;
    Value *IncrementedIV;
    BasicBlock *AfterBB;
    // The value of lowerbound and upperbound will be supplied, if this
    // function is called while generating OpenMP code. Otherwise get
    // the values.
    assert(((lowerBound && upperBound) || (!lowerBound && !upperBound))
                                && "Either give both bounds or none");
    if (lowerBound == 0 || upperBound == 0) {
        lowerBound = ExpGen.codegen(f->LB,
                                    TD->getIntPtrType(Builder.getContext()));
        upperBound = ExpGen.codegen(f->UB,
                                    TD->getIntPtrType(Builder.getContext()));
    }
    createLoop(&Builder, lowerBound, upperBound, Stride, IV, AfterBB,
               IncrementedIV, DT);

    // Add loop iv to symbols.
    (*clastVars)[f->iterator] = IV;

    if (f->body)
      codegen(f->body);

    // Loop is finished, so remove its iv from the live symbols.
    clastVars->erase(f->iterator);

    BasicBlock *HeaderBB = *pred_begin(AfterBB);
    BasicBlock *LastBodyBB = Builder.GetInsertBlock();
    Builder.CreateBr(HeaderBB);
    IV->addIncoming(IncrementedIV, LastBodyBB);
    Builder.SetInsertPoint(AfterBB);
  }

  /// @brief Add a new definition of an openmp subfunction.
  Function* addOpenMPSubfunction(Module *M) {
    Function *F = Builder.GetInsertBlock()->getParent();
    const std::string &Name = F->getNameStr() + ".omp_subfn";

    std::vector<Type*> Arguments(1, Builder.getInt8PtrTy());
    FunctionType *FT = FunctionType::get(Builder.getVoidTy(), Arguments, false);
    Function *FN = Function::Create(FT, Function::InternalLinkage, Name, M);
    // Do not run any polly pass on the new function.
    SD->markFunctionAsInvalid(FN);

    Function::arg_iterator AI = FN->arg_begin();
    AI->setName("omp.userContext");

    return FN;
  }

  /// @brief Add values to the OpenMP structure.
  ///
  /// Create the subfunction structure and add the values from the list.
  Value *addValuesToOpenMPStruct(SetVector<Value*> OMPDataVals,
                                 Function *SubFunction) {
    std::vector<Type*> structMembers;

    // Create the structure.
    for (unsigned i = 0; i < OMPDataVals.size(); i++)
      structMembers.push_back(OMPDataVals[i]->getType());

    StructType *structTy = StructType::get(Builder.getContext(),
                                           structMembers);
    // Store the values into the structure.
    Value *structData = Builder.CreateAlloca(structTy, 0, "omp.userContext");
    for (unsigned i = 0; i < OMPDataVals.size(); i++) {
      Value *storeAddr = Builder.CreateStructGEP(structData, i);
      Builder.CreateStore(OMPDataVals[i], storeAddr);
    }

    return structData;
  }

  /// @brief Create OpenMP structure values.
  ///
  /// Create a list of values that has to be stored into the subfuncition
  /// structure.
  SetVector<Value*> createOpenMPStructValues() {
    SetVector<Value*> OMPDataVals;

    // Push the clast variables available in the clastVars.
    for (CharMapT::iterator I = clastVars->begin(), E = clastVars->end();
         I != E; I++) {
     DEBUG(dbgs() << " insert into OMPDataVals clastVar (" << I->first << ")  "
        << *I->second << "\n");
      OMPDataVals.insert(I->second);
    }

    // Push the base addresses of memory references.
    for (Scop::iterator SI = S->begin(), SE = S->end(); SI != SE; ++SI) {
      ScopStmt *Stmt = *SI;
      for (SmallVector<MemoryAccess*, 8>::iterator I = Stmt->memacc_begin(),
           E = Stmt->memacc_end(); I != E; ++I) {
        Value *BaseAddr = const_cast<Value*>((*I)->getBaseAddr());
        if (Instruction *Inst = dyn_cast<Instruction>(BaseAddr)) {
          if (!S->getRegion().contains(Inst)) {
           DEBUG(dbgs() << " insert into OMPDataVals baseAddr " << *BaseAddr << "\n");
            OMPDataVals.insert((BaseAddr));
          } else {
           DEBUG(dbgs() << " do not insert into OMPDataVals baseAddr " << *BaseAddr << "\n");
          }
        } else {
         DEBUG(dbgs() << " insert into OMPDataVals baseAddr " << *BaseAddr << "\n");
          OMPDataVals.insert((BaseAddr));
        }
      }
    }

    Region &R = S->getRegion();
    Function *F = R.getEntry()->getParent();
    /// FIX 4 
    /// Hack to include arguments PolybenchC 2mm and others
    /// 
    for (Function::arg_iterator I = F->arg_begin(), E = F->arg_end(); I != E; I++) {
     if (OMPDataVals.count(I)) continue;

     for (Argument::use_iterator UI = I->use_begin(), UE = I->use_end(); UI != UE; UI++) {
       Instruction *Inst = cast<Instruction>(*UI);
      DEBUG(dbgs() << " test inst: " << *Inst << " in ");
       if (Inst->getParent()->getParent() && R.contains(Inst)) {
        DEBUG(dbgs() << " insert into OMPDataVals argument " << *I<< "\n");
         OMPDataVals.insert(I);
         break;
       }
     }
      
    }

    return OMPDataVals;
  }


  /// @brief Extract the values from the subfunction parameter.
  ///
  /// Extract the values from the subfunction parameter and update the clast
  /// variables to point to the new values.
  void extractValuesFromOpenMPStruct(CharMapT *clastVarsOMP,
                                     SetVector<Value*> OMPDataVals,
                                     Value *userContext) {
    // Extract the clast variables.
    unsigned i = 0;
    for (CharMapT::iterator I = clastVars->begin(), E = clastVars->end();
         I != E; I++) {
      Value *loadAddr = Builder.CreateStructGEP(userContext, i);
      (*clastVarsOMP)[I->first] = Builder.CreateLoad(loadAddr);
      i++;
    }

    // Extract the base addresses of memory references.
    for (unsigned j = i; j < OMPDataVals.size(); j++) {
      Value *loadAddr = Builder.CreateStructGEP(userContext, j);
      Value *baseAddr = OMPDataVals[j];
      ValueMap[baseAddr] = Builder.CreateLoad(loadAddr);
     DEBUG(dbgs() << "==== ValueMap[" <<*baseAddr<<"] = " 
             <<  *ValueMap[baseAddr] << "\n");
    }

  }

  /// @brief Add body to the subfunction.
  void addOpenMPSubfunctionBody(Function *FN, const clast_for *f,
                                Value *structData,
                                SetVector<Value*> OMPDataVals) {
    Module *M = Builder.GetInsertBlock()->getParent()->getParent();
    LLVMContext &Context = FN->getContext();
    IntegerType *intPtrTy = TD->getIntPtrType(Context);

    // Store the previous basic block.
    BasicBlock *PrevBB = Builder.GetInsertBlock();

    // Create basic blocks.
    BasicBlock *HeaderBB = BasicBlock::Create(Context, "omp.setup", FN);
    Header = HeaderBB;
    BasicBlock *ExitBB = BasicBlock::Create(Context, "omp.exit", FN);
    BasicBlock *checkNextBB = BasicBlock::Create(Context, "omp.checkNext", FN);
    BasicBlock *loadIVBoundsBB = BasicBlock::Create(Context, "omp.loadIVBounds",
                                                    FN);

    DT->addNewBlock(HeaderBB, PrevBB);
    DT->addNewBlock(ExitBB, HeaderBB);
    DT->addNewBlock(checkNextBB, HeaderBB);
    DT->addNewBlock(loadIVBoundsBB, HeaderBB);

    // Fill up basic block HeaderBB.
    Builder.SetInsertPoint(HeaderBB);
    Value *lowerBoundPtr = Builder.CreateAlloca(intPtrTy, 0,
                                                "omp.lowerBoundPtr");
    Value *upperBoundPtr = Builder.CreateAlloca(intPtrTy, 0,
                                                "omp.upperBoundPtr");
    Value *userContext = Builder.CreateBitCast(FN->arg_begin(),
                                               structData->getType(),
                                               "omp.userContext");

    CharMapT clastVarsOMP;
    extractValuesFromOpenMPStruct(&clastVarsOMP, OMPDataVals, userContext);
   DEBUG(dbgs() << "abcdefghijklmnopqrstuvw\n");
    Builder.CreateBr(checkNextBB);

    // Add code to check if another set of iterations will be executed.
    Builder.SetInsertPoint(checkNextBB);
    Function *runtimeNextFunction = M->getFunction("GOMP_loop_runtime_next");
    Value *ret1 = Builder.CreateCall2(runtimeNextFunction,
                                      lowerBoundPtr, upperBoundPtr);
    Value *hasNextSchedule = Builder.CreateTrunc(ret1, Builder.getInt1Ty(),
                                                 "omp.hasNextScheduleBlock");
    Builder.CreateCondBr(hasNextSchedule, loadIVBoundsBB, ExitBB);

    // Add code to to load the iv bounds for this set of iterations.
    Builder.SetInsertPoint(loadIVBoundsBB);
    Value *lowerBound = Builder.CreateLoad(lowerBoundPtr, "omp.lowerBound");
    Value *upperBound = Builder.CreateLoad(upperBoundPtr, "omp.upperBound");

    // Subtract one as the upper bound provided by openmp is a < comparison
    // whereas the codegenForSequential function creates a <= comparison.
    upperBound = Builder.CreateSub(upperBound, ConstantInt::get(intPtrTy, 1),
                                   "omp.upperBoundAdjusted");

    // Use clastVarsOMP during code generation of the OpenMP subfunction.
    CharMapT *oldClastVars = clastVars;
    clastVars = &clastVarsOMP;
    ExpGen.setIVS(&clastVarsOMP);

    codegenForSequential(f, lowerBound, upperBound);

    // Restore the old clastVars.
    clastVars = oldClastVars;
    ExpGen.setIVS(oldClastVars);

    Builder.CreateBr(checkNextBB);

    // Add code to terminate this openmp subfunction.
    Builder.SetInsertPoint(ExitBB);
    Function *endnowaitFunction = M->getFunction("GOMP_loop_end_nowait");
    Builder.CreateCall(endnowaitFunction);
    Builder.CreateRetVoid();

    // Restore the builder back to previous basic block.
    Builder.SetInsertPoint(PrevBB);
  }

  /// @brief Create an OpenMP parallel for loop.
  ///
  /// This loop reflects a loop as if it would have been created by an OpenMP
  /// statement.
  void codegenForOpenMP(const clast_for *f) {
    Module *M = Builder.GetInsertBlock()->getParent()->getParent();
    IntegerType *intPtrTy = TD->getIntPtrType(Builder.getContext());

    Function *SubFunction = addOpenMPSubfunction(M);
    SetVector<Value*> OMPDataVals = createOpenMPStructValues();
    Value *structData = addValuesToOpenMPStruct(OMPDataVals, SubFunction);

    addOpenMPSubfunctionBody(SubFunction, f, structData, OMPDataVals);

    // Create call for GOMP_parallel_loop_runtime_start.
    Value *subfunctionParam = Builder.CreateBitCast(structData,
                                                    Builder.getInt8PtrTy(),
                                                    "omp_data");

    Value *numberOfThreads = Builder.getInt32(0);
    Value *lowerBound = ExpGen.codegen(f->LB, intPtrTy);
    Value *upperBound = ExpGen.codegen(f->UB, intPtrTy);

    // Add one as the upper bound provided by openmp is a < comparison
    // whereas the codegenForSequential function creates a <= comparison.
    upperBound = Builder.CreateAdd(upperBound, ConstantInt::get(intPtrTy, 1));
    APInt APStride = APInt_from_MPZ(f->stride);
    Value *stride = ConstantInt::get(intPtrTy,
                                     APStride.zext(intPtrTy->getBitWidth()));

    SmallVector<Value *, 6> Arguments;
    Arguments.push_back(SubFunction);
    Arguments.push_back(subfunctionParam);
    Arguments.push_back(numberOfThreads);
    Arguments.push_back(lowerBound);
    Arguments.push_back(upperBound);
    Arguments.push_back(stride);

    Function *parallelStartFunction =
      M->getFunction("GOMP_parallel_loop_runtime_start");
    Builder.CreateCall(parallelStartFunction, Arguments);

    // Create call to the subfunction.
    Builder.CreateCall(SubFunction, subfunctionParam);

    // Create call for GOMP_parallel_end.
    Function *FN = M->getFunction("GOMP_parallel_end");
    Builder.CreateCall(FN);
  }

  bool isInnermostLoop(const clast_for *f) {
    const clast_stmt *stmt = f->body;

    while (stmt) {
      if (!CLAST_STMT_IS_A(stmt, stmt_user))
        return false;

      stmt = stmt->next;
    }

    return true;
  }

  /// @brief Get the number of loop iterations for this loop.
  /// @param f The clast for loop to check.
  int getNumberOfIterations(const clast_for *f) {
    isl_set *loopDomain = isl_set_copy(isl_set_from_cloog_domain(f->domain));
    isl_set *tmp = isl_set_copy(loopDomain);

    // Calculate a map similar to the identity map, but with the last input
    // and output dimension not related.
    //  [i0, i1, i2, i3] -> [i0, i1, i2, o0]
    isl_space *Space = isl_set_get_space(loopDomain);
    Space = isl_space_drop_outputs(Space,
                                   isl_set_dim(loopDomain, isl_dim_set) - 2, 1);
    Space = isl_space_map_from_set(Space);
    isl_map *identity = isl_map_identity(Space);
    identity = isl_map_add_dims(identity, isl_dim_in, 1);
    identity = isl_map_add_dims(identity, isl_dim_out, 1);

    isl_map *map = isl_map_from_domain_and_range(tmp, loopDomain);
    map = isl_map_intersect(map, identity);

    isl_map *lexmax = isl_map_lexmax(isl_map_copy(map));
    isl_map *lexmin = isl_map_lexmin(map);
    isl_map *sub = isl_map_sum(lexmax, isl_map_neg(lexmin));

    isl_set *elements = isl_map_range(sub);

    if (!isl_set_is_singleton(elements)) {
      isl_set_free(elements);
      return -1;
    }

    isl_point *p = isl_set_sample_point(elements);

    isl_int v;
    isl_int_init(v);
    isl_point_get_coordinate(p, isl_dim_set, isl_set_n_dim(loopDomain) - 1, &v);
    int numberIterations = isl_int_get_si(v);
    isl_int_clear(v);
    isl_point_free(p);

    return (numberIterations) / isl_int_get_si(f->stride) + 1;
  }

  /// @brief Create vector instructions for this loop.
  void codegenForVector(const clast_for *f) {
    DEBUG(dbgs() << "Vectorizing loop '" << f->iterator << "'\n");
    int vectorWidth = getNumberOfIterations(f);

    Value *LB = ExpGen.codegen(f->LB,
      TD->getIntPtrType(Builder.getContext()));

    APInt Stride = APInt_from_MPZ(f->stride);
    IntegerType *LoopIVType = dyn_cast<IntegerType>(LB->getType());
    Stride =  Stride.zext(LoopIVType->getBitWidth());
    Value *StrideValue = ConstantInt::get(LoopIVType, Stride);

    std::vector<Value*> IVS(vectorWidth);
    IVS[0] = LB;

    for (int i = 1; i < vectorWidth; i++)
      IVS[i] = Builder.CreateAdd(IVS[i-1], StrideValue, "p_vector_iv");

    isl_set *scatteringDomain = isl_set_from_cloog_domain(f->domain);

    // Add loop iv to symbols.
    (*clastVars)[f->iterator] = LB;

    const clast_stmt *stmt = f->body;

    while (stmt) {
      codegen((const clast_user_stmt *)stmt, &IVS, f->iterator,
              scatteringDomain);
      stmt = stmt->next;
    }

    // Loop is finished, so remove its iv from the live symbols.
    clastVars->erase(f->iterator);
  }

  void codegen(const clast_for *f) {
    DEBUG(dbgs() << "\nVECTOR ... " << Vector << " " <<  isInnermostLoop(f)
          <<" " <<  DP->isParallelFor(f) << " " <<
           (-1 != getNumberOfIterations(f)) << "  " << 
           (getNumberOfIterations(f) <= 16) << " (" <<
            getNumberOfIterations(f) <<  ") ... VECTOR \n");
    DEBUG(dbgs() << "\nOpenMP ... " << OpenMP << " " << (!parallelCodeGeneration)
                 << "  " << DP->isParallelFor(f) << " ... OpenMP \n");

    if (Vector && isInnermostLoop(f) && DP->isParallelFor(f)
        && (-1 != getNumberOfIterations(f))
        && (getNumberOfIterations(f) <= 16 && getNumberOfIterations(f) > 1)) {
      codegenForVector(f);
    } else if (OpenMP && !parallelCodeGeneration && DP->isParallelFor(f)) {
      parallelCodeGeneration = true;
      parallelLoops.push_back(f->iterator);
      codegenForOpenMP(f);
      parallelCodeGeneration = false;
    } else
      codegenForSequential(f);
  }

  Value *codegen(const clast_equation *eq) {
    Value *LHS = ExpGen.codegen(eq->LHS,
      TD->getIntPtrType(Builder.getContext()));
    Value *RHS = ExpGen.codegen(eq->RHS,
      TD->getIntPtrType(Builder.getContext()));
    CmpInst::Predicate P;

    if (eq->sign == 0)
      P = ICmpInst::ICMP_EQ;
    else if (eq->sign > 0)
      P = ICmpInst::ICMP_SGE;
    else
      P = ICmpInst::ICMP_SLE;

    return Builder.CreateICmp(P, LHS, RHS);
  }

  void codegen(const clast_guard *g) {
    Function *F = Builder.GetInsertBlock()->getParent();
    LLVMContext &Context = F->getContext();
    BasicBlock *ThenBB = BasicBlock::Create(Context, "polly.then", F);
    BasicBlock *MergeBB = BasicBlock::Create(Context, "polly.merge", F);
    DT->addNewBlock(ThenBB, Builder.GetInsertBlock());
    DT->addNewBlock(MergeBB, Builder.GetInsertBlock());

    Value *Predicate = codegen(&(g->eq[0]));

    for (int i = 1; i < g->n; ++i) {
      Value *TmpPredicate = codegen(&(g->eq[i]));
      Predicate = Builder.CreateAnd(Predicate, TmpPredicate);
    }

    Builder.CreateCondBr(Predicate, ThenBB, MergeBB);
    Builder.SetInsertPoint(ThenBB);

    codegen(g->then);

    Builder.CreateBr(MergeBB);
    Builder.SetInsertPoint(MergeBB);
  }

  void codegen(const clast_stmt *stmt) {
    if	    (CLAST_STMT_IS_A(stmt, stmt_root))
      assert(false && "No second root statement expected");
    else if (CLAST_STMT_IS_A(stmt, stmt_ass))
      codegen((const clast_assignment *)stmt);
    else if (CLAST_STMT_IS_A(stmt, stmt_user))
      codegen((const clast_user_stmt *)stmt);
    else if (CLAST_STMT_IS_A(stmt, stmt_block))
      codegen((const clast_block *)stmt);
    else if (CLAST_STMT_IS_A(stmt, stmt_for))
      codegen((const clast_for *)stmt);
    else if (CLAST_STMT_IS_A(stmt, stmt_guard))
      codegen((const clast_guard *)stmt);

    if (stmt->next)
      codegen(stmt->next);
  }

  void addParameters(const CloogNames *names) {
    SCEVExpander Rewriter(SE, "polly");

    // Create an instruction that specifies the location where the parameters
    // are expanded.
    CastInst::CreateIntegerCast(ConstantInt::getTrue(Builder.getContext()),
                                  Builder.getInt16Ty(), false, "insertInst",
                                  Builder.GetInsertBlock());

    int i = 0;
    for (Scop::param_iterator PI = S->param_begin(), PE = S->param_end();
         PI != PE; ++PI) {
      assert(i < names->nb_parameters && "Not enough parameter names");

      const SCEV *Param = *PI;
      Type *Ty = Param->getType();

      Instruction *insertLocation = --(Builder.GetInsertBlock()->end());
      Value *V = Rewriter.expandCodeFor(Param, Ty, insertLocation);
      (*clastVars)[names->parameters[i]] = V;

      ++i;
    }
  }

  public:
  void codegen(const clast_root *r) {
    clastVars = new CharMapT();
    addParameters(r->names);
    ExpGen.setIVS(clastVars);

    parallelCodeGeneration = false;

    const clast_stmt *stmt = (const clast_stmt*) r;
    if (stmt->next)
      codegen(stmt->next);

    delete clastVars;
  }

  ClastStmtCodeGen(Scop *scop, ScalarEvolution &se, DominatorTree *dt,
                   ScopDetection *sd, Dependences *dp, TargetData *td,
                   IRBuilder<> &B) :
    S(scop), SE(se), DT(dt), SD(sd), DP(dp), TD(td), Builder(B),
    ExpGen(Builder, NULL) {}

};
}

#if 0
namespace {
class CodeGeneration : public ScopPass {
  Region *region;
  Scop *S;
  DominatorTree *DT;
  ScalarEvolution *SE;
  ScopDetection *SD;
  TargetData *TD;
  RegionInfo *RI;

  std::vector<std::string> parallelLoops;

  public:
  static char ID;

  CodeGeneration() : ScopPass(ID) {}
#endif 

  // Adding prototypes required if OpenMP is enabled.
  void CodeGeneration::addOpenMPDefinitions(IRBuilder<> &Builder)
  {
    Module *M = Builder.GetInsertBlock()->getParent()->getParent();
    LLVMContext &Context = Builder.getContext();
    IntegerType *intPtrTy = TD->getIntPtrType(Context);

    if (!M->getFunction("GOMP_parallel_end")) {
      FunctionType *FT = FunctionType::get(Type::getVoidTy(Context), false);
      Function::Create(FT, Function::ExternalLinkage, "GOMP_parallel_end", M);
    }

    if (!M->getFunction("GOMP_parallel_loop_runtime_start")) {
      // Type of first argument.
      std::vector<Type*> Arguments(1, Builder.getInt8PtrTy());
      FunctionType *FnArgTy = FunctionType::get(Builder.getVoidTy(), Arguments,
                                                false);
      PointerType *FnPtrTy = PointerType::getUnqual(FnArgTy);

      std::vector<Type*> args;
      args.push_back(FnPtrTy);
      args.push_back(Builder.getInt8PtrTy());
      args.push_back(Builder.getInt32Ty());
      args.push_back(intPtrTy);
      args.push_back(intPtrTy);
      args.push_back(intPtrTy);

      FunctionType *type = FunctionType::get(Builder.getVoidTy(), args, false);
      Function::Create(type, Function::ExternalLinkage,
                       "GOMP_parallel_loop_runtime_start", M);
    }

    if (!M->getFunction("GOMP_loop_runtime_next")) {
      PointerType *intLongPtrTy = PointerType::getUnqual(intPtrTy);

      std::vector<Type*> args;
      args.push_back(intLongPtrTy);
      args.push_back(intLongPtrTy);

      FunctionType *type = FunctionType::get(Builder.getInt8Ty(), args, false);
      Function::Create(type, Function::ExternalLinkage,
                       "GOMP_loop_runtime_next", M);
    }

    if (!M->getFunction("GOMP_loop_end_nowait")) {
      FunctionType *FT = FunctionType::get(Builder.getVoidTy(),
                                           std::vector<Type*>(), false);
      Function::Create(FT, Function::ExternalLinkage,
		       "GOMP_loop_end_nowait", M);
    }
  }

  // Split the entry edge of the region and generate a new basic block on this
  // edge. This function also updates ScopInfo and RegionInfo.
  //
  // @param region The region where the entry edge will be splitted.
  BasicBlock *CodeGeneration::splitEdgeAdvanced(Region *region) {
    BasicBlock *newBlock;
    BasicBlock *splitBlock;

    newBlock = SplitEdge(region->getEnteringBlock(), region->getEntry(), this);

    if (DT->dominates(region->getEntry(), newBlock)) {
      // Update ScopInfo.
      for (Scop::iterator SI = S->begin(), SE = S->end(); SI != SE; ++SI)
        if ((*SI)->getBasicBlock() == newBlock) {
          (*SI)->setBasicBlock(newBlock);
          break;
        }

      // Update RegionInfo.
      splitBlock = region->getEntry();
      region->replaceEntry(newBlock);
      RI->setRegionFor(newBlock, region);
    } else {
      RI->setRegionFor(newBlock, region->getParent());
      splitBlock = newBlock;
    }

    return splitBlock;
  }

  // Create a split block that branches either to the old code or to a new basic
  // block where the new code can be inserted.
  //
  // @param builder A builder that will be set to point to a basic block, where
  //                the new code can be generated.
  // @return The split basic block.
  BasicBlock *CodeGeneration::addSplitAndStartBlock(IRBuilder<> *builder) {
    BasicBlock *splitBlock = splitEdgeAdvanced(region);

    splitBlock->setName("polly.enterScop");

    Function *function = splitBlock->getParent();
    BasicBlock *startBlock = BasicBlock::Create(function->getContext(),
                                                "polly.start", function);
    splitBlock->getTerminator()->eraseFromParent();
    builder->SetInsertPoint(splitBlock);
    builder->CreateCondBr(builder->getTrue(), startBlock, region->getEntry());
    DT->addNewBlock(startBlock, splitBlock);

    // Start code generation here.
    builder->SetInsertPoint(startBlock);
    return splitBlock;
  }

  // Merge the control flow of the newly generated code with the existing code.
  //
  // @param splitBlock The basic block where the control flow was split between
  //                   old and new version of the Scop.
  // @param builder    An IRBuilder that points to the last instruction of the
  //                   newly generated code.
  void CodeGeneration::mergeControlFlow(BasicBlock *splitBlock, IRBuilder<> *builder) {
    BasicBlock *mergeBlock;
    Region *R = region;

    if (R->getExit()->getSinglePredecessor())
      // No splitEdge required.  A block with a single predecessor cannot have
      // PHI nodes that would complicate life.
      mergeBlock = R->getExit();
    else {
      mergeBlock = SplitEdge(R->getExitingBlock(), R->getExit(), this);
      // SplitEdge will never split R->getExit(), as R->getExit() has more than
      // one predecessor. Hence, mergeBlock is always a newly generated block.
      mergeBlock->setName("polly.finalMerge");
      R->replaceExit(mergeBlock);
    }

    builder->CreateBr(mergeBlock);

    if (DT->dominates(splitBlock, mergeBlock))
      DT->changeImmediateDominator(mergeBlock, splitBlock);
  }

  bool CodeGeneration::runOnScop(Scop &scop) {
    S = &scop;
    region = &S->getRegion();
    DT = &getAnalysis<DominatorTree>();
    Dependences *DP = &getAnalysis<Dependences>();
    SE = &getAnalysis<ScalarEvolution>();
    SD = &getAnalysis<ScopDetection>();
    TD = &getAnalysis<TargetData>();
    RI = &getAnalysis<RegionInfo>();

   DEBUG(dbgs() << "\n\n\t\t CodeGeneration on " << region->getNameStr() 
           << "  Vector: " << Vector << "  OpenMP: " << OpenMP << "\n");

    parallelLoops.clear();

    assert(region->isSimple() && "Only simple regions are supported");

    // In the CFG and we generate next to original code of the Scop the
    // optimized version.  Both the new and the original version of the code
    // remain in the CFG. A branch statement decides which version is executed.
    // At the moment, we always execute the newly generated version (the old one
    // is dead code eliminated by the cleanup passes). Later we may decide to
    // execute the new version only under certain conditions. This will be the
    // case if we support constructs for which we cannot prove all assumptions
    // at compile time.
    //
    // Before transformation:
    //
    //                        bb0
    //                         |
    //                     orig_scop
    //                         |
    //                        bb1
    //
    // After transformation:
    //                        bb0
    //                         |
    //                  polly.splitBlock
    //                     /       \.
    //                     |     startBlock
    //                     |        |
    //               orig_scop   new_scop
    //                     \      /
    //                      \    /
    //                        bb1 (joinBlock)
    IRBuilder<> builder(region->getEntry());

    // The builder will be set to startBlock.
    BasicBlock *splitBlock = addSplitAndStartBlock(&builder);

    if (OpenMP)
      addOpenMPDefinitions(builder);

    ClastStmtCodeGen CodeGen(S, *SE, DT, SD, DP, TD, builder);
    CloogInfo &C = getAnalysis<CloogInfo>();
    CodeGen.codegen(C.getClast());

    parallelLoops.insert(parallelLoops.begin(),
                         CodeGen.getParallelLoops().begin(),
                         CodeGen.getParallelLoops().end());

    mergeControlFlow(splitBlock, &builder);

    return true;
  }

  void CodeGeneration::printScop(raw_ostream &OS) const {
    for (std::vector<std::string>::const_iterator PI = parallelLoops.begin(),
         PE = parallelLoops.end(); PI != PE; ++PI)
      OS << "Parallel loop with iterator '" << *PI << "' generated\n";
  }

  void CodeGeneration::getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<CloogInfo>();
    AU.addRequired<Dependences>();
    AU.addRequired<DominatorTree>();
    AU.addRequired<RegionInfo>();
    AU.addRequired<ScalarEvolution>();
    AU.addRequired<ScopDetection>();
    AU.addRequired<ScopInfo>();
    AU.addRequired<TargetData>();

    AU.addPreserved<CloogInfo>();
    AU.addPreserved<Dependences>();

    // FIXME: We do not create LoopInfo for the newly generated loops.
    AU.addPreserved<LoopInfo>();
    AU.addPreserved<DominatorTree>();
    AU.addPreserved<ScopDetection>();
    AU.addPreserved<ScalarEvolution>();

    // FIXME: We do not yet add regions for the newly generated code to the
    //        region tree.
    AU.addPreserved<RegionInfo>();
    AU.addPreserved<TempScopInfo>();
    AU.addPreserved<ScopInfo>();
    AU.addPreservedID(IndependentBlocksID);
  }
//};
//}

char CodeGeneration::ID = 1;

INITIALIZE_PASS_BEGIN(CodeGeneration, "polly-codegen",
                      "Polly - Create LLVM-IR form SCoPs", false, false)
INITIALIZE_PASS_DEPENDENCY(CloogInfo)
INITIALIZE_PASS_DEPENDENCY(Dependences)
INITIALIZE_PASS_DEPENDENCY(DominatorTree)
INITIALIZE_PASS_DEPENDENCY(RegionInfo)
INITIALIZE_PASS_DEPENDENCY(ScalarEvolution)
INITIALIZE_PASS_DEPENDENCY(ScopDetection)
INITIALIZE_PASS_DEPENDENCY(TargetData)
INITIALIZE_PASS_END(CodeGeneration, "polly-codegen",
                      "Polly - Create LLVM-IR form SCoPs", false, false)

Pass* polly::createCodeGenerationPass() {
  return new CodeGeneration();
}
