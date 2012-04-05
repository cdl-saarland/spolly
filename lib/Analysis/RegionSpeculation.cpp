//===--- RegionSpeculation.h - Create Speculative Information ----*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//
//===----------------------------------------------------------------------===//


#include "polly/RegionSpeculation.h"

#include "sambamba/Profiler2/Profiler.h"
#include "sambamba/Profiler2/SCEVHelper.h"

#include "polly/ScopInfo.h"
#include "polly/ScopDetection.h"
#include "polly/CodeGeneration.h"
#include "polly/LinkAllPasses.h"
#include "polly/Support/ScopHelper.h"
#include "polly/Support/SCEVValidator.h"

#include "llvm/PassManager.h"
#include "llvm/Module.h"
#include "llvm/Target/TargetData.h"
#include "llvm/Analysis/Interval.h"
#include "llvm/LLVMContext.h"
#include "llvm/IntrinsicInst.h"

#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/Twine.h"
#include "llvm/ADT/SmallPtrSet.h"

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/Verifier.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/RegionIterator.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h" 


#define DEBUG_TYPE "region-speculation"
#include "llvm/Support/Debug.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

#include <iostream>
#include <fstream>
#include <string>
#include <list>

#define RegionMapKeyForRegion(R) std::make_pair(R->getEntry(), R->getExit())
#define FunctionForRegion(R) (R->getEntry()->getParent())
#define ModuleForFunction(F) (F->getParent())

using namespace llvm;
using namespace polly;


static cl::opt<bool>
ReplaceByParallelVersion("spolly-replace",
               cl::desc("replace functions with parallel ones"),
               cl::Hidden, cl::init(false));

static cl::opt<bool>
ReplaceByParallelVersionSound("spolly-replace-sound",
               cl::desc("replace functions with parallel ones (only if tests are sound)"),
               cl::Hidden, cl::init(false));



STATISTIC(StatIllFormedRegion       , "Ill formed region");
STATISTIC(StatViolOutside           , "Violation outside the SCoP");
STATISTIC(StatViolInside            , "Violation Inside the SCoP");
//STATISTIC(StatNonCompMemAccess      , "Non computable minimal/maximal access");
STATISTIC(StatCompMemAccess         , "Computable minimal/maximal access (validOnly)");
STATISTIC(StatUnsizedPointer        , "Load from an unsized pointer type (validOnly)");
STATISTIC(StatNonVectorizable       , "Non vectorizable load (validOnly)");
STATISTIC(StatLoopCount             , "Number of Loops (validOnly)");
STATISTIC(StatContainsLoop          , "Contains a Loop (validOnly)");
STATISTIC(StatContainsBranch        , "Contains a Conditional (validOnly)");
STATISTIC(StatLoopProfilingCheap    , "Number of Loops which need profiling (cheap) (validOnly)");
STATISTIC(StatLoopProfilingExpensive, "Number of Loops which need profiling (expensive) (validOnly)");
STATISTIC(StatBranchCount           , "Number of Conditionals (validOnly)");
STATISTIC(StatFunctionCall          , "Number of Function Calls (validOnly)");
STATISTIC(StatFunctionCallReadnone  , "Number of readnone function calls (validOnly)");
STATISTIC(StatFunctionCallReadonly  , "Number of readonly function calls (validOnly)");
STATISTIC(StatCrucialCall           , "Violating call in all execution paths (validOnly)");
STATISTIC(StatCrucialBranch         , "Branch with violating call instruction (validOnly)");
STATISTIC(StatNonCrucialBranch      , "Branch without violating vall instruction (validOnly)");
STATISTIC(StatFunctionCallIndirect  , "Indirect function call (validOnly)");
STATISTIC(StatFunctionCallPrint     , "Puts/Print/Stream function call (validOnly)");
STATISTIC(StatFunctionCallIntrinsic , "Intrinsic function call (validOnly)");
STATISTIC(StatFunctionCallNoReturn  , "Function call which may not return (validOnly)");
STATISTIC(StatFunctionCallThrowing  , "Function call which may throw an exception (validOnly)");
STATISTIC(StatInvalidByRS           , "SCoP discarded by RegionSpeculation");
STATISTIC(StatValidByRS             , "SCoP valid for RegionSpeculation");
STATISTIC(StatMemoryAccesses        , "Number of memory accesses (validOnly)");
STATISTIC(StatAliasingInstructions  , "Number of aliasing instructions (validOnly)");
STATISTIC(StatSCoPWithAliases       , "Number of SCoPs with aliasing instructions (validOnly)");
STATISTIC(StatAliasTests            , "Number of SCoPs where alias tests can be inserted (validOnly)");
STATISTIC(StatChecksAreSound        , "Number of SCoPs with sound alias tests (validOnly)");
STATISTIC(StatContainsCalls         , "Number of SCoPs with function calls (validOnly)");
STATISTIC(StatInvariantTests        , "Number of SCoPs where invariant tests can be inserted (validOnly)");
STATISTIC(StatInitialScores         , "Initial scores");
STATISTIC(StatNonAffineLoopCount    , "Non Affine Loop Count (TODO !!!)");
//STATISTIC(Stat , "");
STATISTIC(StatNumberOfAliasGroups   , "== Number of alias groups (validOnly)");


static int  FunctionCall2, FunctionCallIndirect, FunctionCallNoReturn,
            FunctionCallReadnone, FunctionCallReadonly, FunctionCallThrowing,
            FunctionCallPrint, FunctionCallIntrinsic, CompMemAccess, BranchCount,
            UnsizedPointer, NonVectorizable, LoopProfilingCheap, CrucialCall,
            LoopProfilingExpensive, LoopCount2, CrucialBranch, NonCrucialBranch; 

#if 0


bool polly::RegionSpeculationPrepareRegion;
static cl::opt<bool, true>
SPollyPrepareRegions("spolly-prepare-regions",
       cl::desc("Prepare speculative valid regions to enable codegeneration"), cl::Hidden,
       cl::location(RegionSpeculationPrepareRegion), cl::init(false));

static cl::opt<bool>
SPollyDisabled("spolly-disable",
       cl::desc("Disable speculative polly"),
       cl::Hidden,
       cl::value_desc("Disable speculative polly"),
       cl::init(false));


static cl::opt<bool>
SPollyReplaceViolatingInstructions("spolly-replace-violating-instructions",
       cl::desc("Replace all violating instructions"),
       cl::Hidden,
       cl::value_desc("Replace all violating instructions"),
       cl::init(true));


static cl::opt<bool>
SPollyRemoveViolatingInstructions("spolly-remove-violating-instructions",
       cl::desc("Remove all violating instructions"),
       cl::Hidden,
       cl::value_desc("Remove all violating instructions"),
       cl::init(false));


static cl::opt<bool>
SPollyDumpCandidates("spolly-dump",
       cl::desc("Dump all speculative candidates"),
       cl::Hidden,
       cl::value_desc("Dump all speculative candidates"),
       cl::init(true));

static cl::opt<bool>
SPollyBranchWorst("spolly-branch-worst",
       cl::desc("Assume the worst branch is taken most of the time"),
       cl::Hidden,
       cl::value_desc(""),
       cl::init(false));

static cl::opt<bool>
SPollyBranchBest("spolly-branch-best",
       cl::desc("Assume the best branch is taken most of the time"),
       cl::Hidden,
       cl::value_desc(""),
       cl::init(true));


static cl::opt<bool>
SPollyViolationProbabilityHigh("spolly-violation-high",
       cl::desc("Assume a hight probability for violations"),
       cl::Hidden,
       cl::value_desc(""),
       cl::init(false));

static cl::opt<bool>
SPollyViolationProbabilityLow("spolly-violation-low",
       cl::desc("Assume a low probability for violations"),
       cl::Hidden,
       cl::value_desc(""),
       cl::init(true));


// Variable to mark that we are within a branch and thus possibly
//  not executing some Blocks
static unsigned withinBranch = 0;



namespace {
  
  /* 
   *===  FUNCTION  ============================================================
   *        Name:  getFileName 
   * Description:  
   *===========================================================================
   */
  static std::string getFileName(Region *R) {
    std::string FunctionName =
      R->getEntry()->getParent()->getName();
    std::string FileName = "spolly_" + FunctionName + ".score";
    return FileName;
  }

}


/* 
 *===  FUNCTION  ==============================================================
 *        Name:  insertInvariantCheck
 *   Arguments:  
 *     Returns:  
 *=============================================================================
 */
void RegionSpeculation::insertInvariantChecks(BasicBlock *testBlock,
                                              BasicBlock *invariantProfilingBlock) {
  // If the region does not contain a call we can skip the placement of 
  // invariant checks
  DEBUGDEBUG(dbgs() << "@\t InsertInvariantChecks " << containsCalls << "\n");
  assert(containsCalls && "No need to insert invariant checks without calls");

  // Insert tmp variables in the predecessor pred of the regions entry block 
  // They save the values of the read variables befor we enter the loop
  // Insert a check within the loop for, thus test the tmp variables against the
  // current values
  assert(DT && "No dominatorTree available");
  
  std::map<Value*, Value*> temporaries;
  for (std::set<Value*>::iterator loads = loadInstructions.begin(); 
       loads != loadInstructions.end(); loads++) {
    
    if (Instruction *I = dyn_cast<Instruction>(*loads)) {
      if (!DT->dominates(I->getParent(), testBlock)) {
        continue;
      }
    }

    IRBuilder<> builder(testBlock, --((testBlock)->end())); 

    DEBUGDEBUG(dbgs() << "@\t\t INVARIANT load " << (*loads)->getName() << " " 
         << (*loads) << "\n");

    Value *tmp = builder.CreateLoad(*loads, (*loads)->getName() + "_tmp"); 
    temporaries[*loads] = tmp;
  } 
  
  BasicBlock *ITB = SplitBlock(testBlock, testBlock->begin(), SD);
  BasicBlock *ITBpost = SplitBlock(ITB, ITB->begin(), SD);

  StringRef entryName = testBlock->getName();
  testBlock->setName(entryName + "_new");
  ITB->setName(entryName + "_spolly_cmp");
  ITBpost->setName(entryName + "_old");

  DEBUGDEBUG(dbgs() << "@\t ITB: " << ITB->getName() << "\n"); 
   
  IRBuilder<> builder(ITB, --((ITB)->end())); 
  
  // The integer 64 type the pointers are converted to
  LLVMContext &llvmContext = ITB->getContext();
  IntegerType *t64 = Type::getInt64Ty(llvmContext);

  Value *result = 0;
  for (std::map<Value*, Value*>::iterator ltp = temporaries.begin();
       ltp != temporaries.end(); ltp++) {
    Value *ltpf = ltp->first;
    Value *ltps = ltp->second;
    
    Value *load = builder.CreateLoad(ltpf, ltpf->getName() + "_load"); 
    Type *type = load->getType();
    Value *cmp;
    if (type->isFloatingPointTy()) {
      DEBUGDEBUG(dbgs() << "@\t Inserting float invariant compare \n");
      cmp = builder.CreateFCmpOEQ(load, ltps,
                                  ltpf->getName() + "_cmp");
    } else if (type->isIntegerTy()) {
      DEBUGDEBUG(dbgs() << "@\t Inserting integer invariant compare \n");
      cmp = builder.CreateICmpEQ(load, ltps,
                                 ltpf->getName() + "_cmp");
      
    } else if (type->isPointerTy()) {
      DEBUGDEBUG(dbgs() << "@\t Inserting integer to pointer \n");
      Value *loadAsInt = builder.CreatePtrToInt(load, t64,
                                                ltpf->getName() +"_64");
      DEBUGDEBUG(dbgs() << "@\t Inserting integer to pointer \n");
      Value *tmpAsInt  = builder.CreatePtrToInt(ltps, t64,
                                                ltps->getName() +"_64");
      DEBUGDEBUG(dbgs() << "@\t Inserting integer (pointer) invariant compare \n");
      cmp = builder.CreateICmpEQ(loadAsInt, tmpAsInt,
                                 loadAsInt->getName() + "_cmp");
    } else {
      assert(0 && "Found unknown type while inserting invariant tests");
    }

    if (result)
      result = builder.CreateAnd(result, cmp, result->getName());
    else
      result = cmp;
  }

  assert(result && "Could not compute a result for the invariant check");
  Instruction *I = dyn_cast<Instruction>(result);
  assert(I && "Could not get result Instruction");

  // This is a hack
  // Polly wants the condition to be either constant or an ICmp instruction
  // so if the condition is a AND we just create an ICmp instruction afterwards
  if (I->isBinaryOp()) {
    result = builder.CreateIsNotNull(result, result->getName() + "_icmp");
  }
  
  // First erase the old branch from ITB to ITBpost
  ITB->getTerminator()->eraseFromParent();
  
  BranchInst::Create(ITBpost, invariantProfilingBlock);

  // Use the result to jump to the ITBpost (invariant) or NIB (not invariant)
  BranchInst::Create(ITBpost, invariantProfilingBlock,
                     result, ITB);
  
  DT->addNewBlock(invariantProfilingBlock, ITB);

}		/* -----  end of function insertInvariantCheck  ----- */









/* 
 *===  FUNCTION  ==============================================================
 *        Name:  createCall
 *   Arguments:  
 *     Returns:  
 *=============================================================================
 */
CallInst *RegionSpeculation::createCall(Instruction *I) {
  
  FunctionType *FT; 
  Function *FN = 0;
  CallInst *callInst = 0;

  // The IRBuilder for the basic block with the violating instruction
  //IRBuilder<> builder(context);
  //Module *M = builder.GetInsertBlock()->getParent()->getParent();
  Module *M = I->getParent()->getParent()->getParent();
  
  DEBUGDEBUG(dbgs() << "@\t\t" << *I->getType() << "\t" << I->getNumOperands() << "\n");
  
  unsigned argsC = I->getNumOperands();
  std::vector<Type *> argsT(argsC);
  std::vector<Value *> argsV(argsC);

  unsigned i = 0;
  if (I->getOpcode() == Instruction::Call) {
    CallInst *C = dyn_cast<CallInst>(I);
    DEBUGDEBUG(dbgs() 
          << "@\t\t Found call => using the called function as last argument\n");
    argsV[argsC - 1] = C->getCalledFunction();
    argsT[argsC - 1] = C->getCalledFunction()->getType();
    argsC--;
  }

  for (; i < argsC; i++) {
    argsV[i] = I->getOperand(i);
    argsT[i] = I->getOperand(i)->getType();
  }
  
  // Create the function which has the same return type as the instruction
  // and uses the same operands as the instruction (as arguments)
  FT = FunctionType::get(I->getType(), argsT, false);
  FN = Function::Create(FT, Function::ExternalLinkage,
                        "_spolly_call", M);

  ArrayRef<Value*> Args(argsV);
  //callInst = builder.CreateCall(FN, Args); 
  callInst = CallInst::Create(FN, Args, "", I);

  // Set some attributes to allow Polly to handle this function
  FN->setDoesNotThrow(true);
  FN->setDoesNotReturn(false);

  // TODO see ScopDetection::isValidCallInst
  //FN->setOnlyReadsMemory(true);
  //FN->setDoesNotAccessMemory(true);



  assert(callInst && "Call Instruction was 0");

  return  callInst;

}		/* -----  end of function createCall  ----- */



/* 
 *===  FUNCTION  ==============================================================
 *        Name:  replaceScopStatements
 *   Arguments:  
 *     Returns:  
 *=============================================================================
 */
void RegionSpeculation::replaceScopStatements(ScopStmt *Statement){

  std::map<Instruction*, Instruction*>::iterator it, end;
  for (it = accessStatements.begin(), end = accessStatements.end();
       it != end; it++) {
    DEBUGDEBUG(dbgs() << "@###$### Set access statement for " << *(it->first)
          << " with " << *(it->second) << "\n");

    Statement->setAccessFor(it->first, it->second); 
    it->first->eraseFromParent();
  }

  accessStatements.clear();

}		/* -----  end of function replaceScopStatements  ----- */




/* 
 *===  FUNCTION  ==============================================================
 *        Name:  replaceViolatingInstructions
 *   Arguments:  
 *     Returns:  
 *=============================================================================
 */
void RegionSpeculation::replaceViolatingInstructions() {
  if (!SPollyReplaceViolatingInstructions) return;

  DEBUGDEBUG(dbgs() << "@\t Replace violating instructions "
               << violatingInstructions.size()  << "\n");
  std::set<Instruction*>::iterator vIit;

  CallInst *callInst;
  
  // foreach violating instruction
  for (vIit = violatingInstructions.begin(); vIit != violatingInstructions.end();
       vIit++) {
    // create the corresponding call instruction and add it to
    // the replacementInstructions list
    DEBUGDEBUG(dbgs() << "@\t\t replace " << ((*vIit)) << "\n");
    DEBUGDEBUG(dbgs() << "@\t\t replace " << (*(*vIit)) << "\n");
  
    if (SPollyRemoveViolatingInstructions) {
      (*vIit)->eraseFromParent();
      continue;
    } else if ((*vIit)->getOpcode() == Instruction::PHI) {
      // Skip Phi nodes since they dominate theirself 
      continue;
    }
   
    // vIit is not a PHI instruction and we should not remove it, so we 
    // create a call instruction which will be used to replace vIit  
    callInst = createCall(*vIit);
    
    assert(callInst && "Replacement call is 0");

    DEBUGDEBUG(dbgs() << "@\t\t with " << (*callInst) << "\n");
    
    
    violatingInstructionsMap[callInst] = (*vIit)->getOpcode();
    
    (*vIit)->replaceAllUsesWith(callInst);
    (*vIit)->eraseFromParent(); 
    
    DEBUGDEBUG(dbgs() << "@$$$\t "<< callInst << " " << callInst->getParent()  << "\n"); 
    DEBUGDEBUG(dbgs() << "@$$$\t "<< *callInst << " " << *callInst->getParent() << "\n"); 
    
  
  } /* -----  end foreach violating instruction  ----- */
  

}		/* -----  end of function replaceViolatingInstruction ----- */





/* 
 *===  FUNCTION  ==============================================================
 *        Name:  postPrepareRegion
 * Description:  
 *=============================================================================
 */
void RegionSpeculation::postPrepareRegion(BasicBlock *testBlock,
                                          Region *region) {
  DEBUG(dbgs() << "\n@@@@# postPrepareRegion " << region << "  "
        << " TB: "  << testBlock << "  "<< testBlock->getName() 
        << " " << aliasingValues.size() << "  \n");

  insertChecks(testBlock, 0, region->getEntry());

  IRBuilder<> builder(testBlock->getContext());
  DEBUG(dbgs() << "@$$$\n@$$$\n@$$$\n");


  DEBUG(dbgs() << "@\t Replace dummy instructions with original ones: \n"); 
  // Replace the dummy call instructions with the violating ones again
  std::map<Instruction*, unsigned>::iterator it;

  if (violatingInstructionsMap.size() == 0) 
    return;

  for (it = violatingInstructionsMap.begin(); it != violatingInstructionsMap.end(); 
       it++) {
    DEBUG(dbgs() << "@$$$\t "<< it->first << " " << it->first->getParent() << "  with  " 
          << it->second << "\n"); 
    DEBUG(dbgs() << "@$$$\t "<< *it->first << "\n"); 
    
    Instruction *original;
    CallInst *I = dyn_cast<CallInst>(it->first);
    builder.SetInsertPoint(it->first->getParent(), it->first);

    // Use the original opcode to determine what kind of instruction should be
    // created
    switch (it->second) {
      default:
        DEBUG(dbgs()  << "@\t OpCode: " << it->second << "\n");
        assert(false && "Found unknown opcode during postPreperation");

      case Instruction::Store:
        //continue;
        original = builder.CreateStore(I->getOperand(0), 
                                       I->getOperand(1));
        break;

      case Instruction::Load:
        original = builder.CreateLoad(I->getOperand(0));
        break;

      case Instruction::Call:
        unsigned argsC = I->getNumArgOperands();
        DEBUG(dbgs() << "@\t Instruction call " << argsC << "\n");
        std::vector<Value *> argsV(argsC - 1);
        for (unsigned i = 0; i < argsC - 1; i++) {
          argsV[i] = I->getOperand(i);
        }
        ArrayRef<Value*> Args(argsV);
        original = builder.CreateCall(I->getOperand(argsC - 1), Args);
        break;

    }

    // Replace the dummy with the orinigal instruction
    
    DEBUG(dbgs() << "@\t\t Replace " << *I << " by " );
    I->replaceAllUsesWith(original);
    original->takeName(I);
    DEBUG(dbgs() << *original <<"\n");
    
    accessStatements[I] = original;
  }
  
  DEBUG(dbgs() << "@$$$\n@$$$\n@$$$\n");
  DEBUG(dbgs() << "\n@@@@# postPreparedRegion " << region << "  \n");

}		/* -----  end of function postPrepareRegion  ----- */




#endif

/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////

/// Helper functions, most of them will be used only once, thus can be inlined 
namespace {


  /// @brief Cast all subexpressions to int64
  const SCEV *toInt64(const SCEV *scev, ScalarEvolution *SE,
                      IntegerType *Int64Ty) {
    Type *type = scev->getType();
    if (SE->getTypeSizeInBits(type) == 64) return scev;
    assert(SE->getTypeSizeInBits(type) && "Type size in bits to big (> 64)");

    switch (scev->getSCEVType()) {

      case scTruncate:
      case scZeroExtend:
      case scSignExtend: 
      case scUnknown:
      case scConstant: {
        return SE->getSignExtendExpr(scev, Int64Ty);
      } 

      case scAddRecExpr: {
        const SCEVAddRecExpr *AddRec = cast<SCEVAddRecExpr>(scev);
        const SCEV *start = toInt64(AddRec->getStart(), SE, Int64Ty);
        const SCEV *step  = toInt64(AddRec->getStepRecurrence(*SE), SE, Int64Ty);
        const Loop *loop  = AddRec->getLoop();
        dbgs() << " toint64 of addrec: " << *AddRec << "\n";
        if (SE->hasLoopInvariantBackedgeTakenCount(loop)) {
          const SCEV *BTCount = toInt64(SE->getBackedgeTakenCount(loop), SE, Int64Ty);
          dbgs() << "BTCOunt: " << *BTCount << "\n";
          const SCEV *tripCount = SE->getAddExpr(BTCount,
                                      SE->getConstant(APInt(64, -1, true)));
          dbgs() << "TripCount: " <<*tripCount << "\n";
          return SE->getAddExpr(start, SE->getMulExpr(step, tripCount));
        } else {
          return SE->getAddRecExpr(start, step, loop, AddRec->getNoWrapFlags());
        }
      }
      
      case scAddExpr: 
      case scMulExpr:
      case scSMaxExpr:
      case scUMaxExpr: {
        SmallVectorImpl<const SCEV *> scevs(2);
        const SCEVNAryExpr *NAry = cast<SCEVNAryExpr>(scev);
        for (SCEVNAryExpr::op_iterator it = NAry->op_begin(), 
             end = NAry->op_end(); it != end; it++) {
          scevs.push_back(toInt64(*it, SE, Int64Ty));
        }
        switch (scev->getSCEVType()) {
        case scAddExpr:  return SE->getAddExpr(scevs);
        case scMulExpr:  return SE->getMulExpr(scevs);
        case scSMaxExpr: return SE->getSMaxExpr(scevs);
        case scUMaxExpr: return SE->getUMaxExpr(scevs);
        default: assert(0);
        }
      }
      
      case scUDivExpr: {
        const SCEVUDivExpr *UDiv = cast<SCEVUDivExpr>(scev);
        const SCEV *LHS = toInt64(UDiv->getLHS(), SE, Int64Ty);
        const SCEV *RHS = toInt64(UDiv->getRHS(), SE, Int64Ty);
        return SE->getUDivExpr(LHS, RHS);
      }
      default:
          return SE->getSignExtendExpr(scev, Int64Ty);
      }
  }


  /// @brief Check if the given region is a loop
  inline bool regionIsLoop(const Region *R, LoopInfo *LI) {
    return (LI->getLoopDepth(R->getEntry()) - LI->getLoopDepth(R->getExit()));
  }


  /// @brief Check if the given region is a perfect conditional
  bool regionIsConditional(const Region *R) {
    TerminatorInst *TI = R->getEntry()->getTerminator();
    bool check = false;

    if (const BranchInst *BI = dyn_cast<BranchInst>(TI))
        check = (BI->isConditional() && BI->getNumSuccessors() == 2);
    
    //DEBUG( 
      BasicBlock *BB = R->getExit();
      unsigned count = 0;
      for (pred_iterator PI = pred_begin(BB), E = pred_end(BB); PI != E; ++PI)
        ++count; 
      check = check && count == 2;
    //);
    //
    return check;
  }

} // end anonymus namespace



namespace polly {
  

  /// @brief A SPollyInfo object represents a speculative valid region
  ///
  /// All information needed to compute a score (at runtime) are included, thus
  /// there is no need to rerune any pass. 
  class SPollyInfo {
    
    typedef RegionSpeculation::RegionMapKey RegionMapKey;
    typedef RegionSpeculation::Violation Violation;
    typedef RegionSpeculation::CRegionT CRegionT;
    typedef std::pair<Value *, Value *> MinMaxPair;

    RegionMapKey RMK;
    
    /// @brief The speculative valid region which is represented
    CRegionT R;

    std::list<const Loop *> LoopCounts;

    const std::string nameStr;

    ValueToValueMapTy *profilingValueMap, *parallelValueMap;

    Function *originalVersion, *profilingVersion, *parallelVersion,
             *parallelVersionSubfn;

    /// @brief Information ...
    bool containsCalls, isValid, checksAreSound, BranchIsCrucial, EnableVector;
    bool hasCrucialBranches;

    BasicBlock *aliasTestBlock, *invariantLoadBlock, *invariantCompareBlock;
    Value *aliasTestValue, *invariantCompareValue;

    /// @brief todo
    RegionSpeculation *RS; 

    /// @brief The scoreSCEV represents the score of the region
    const SCEV *ScoreSCEV;
    unsigned branchDepth;
 

    /// @brief Profiling structures 
    struct ProfiledValue {
      sambamba::Profiler2::KeyT key;
      BasicBlock * const guard;
      const Loop * const loop;
      unsigned offset;
      bool isCrucial, del;
      ProfiledValue(BasicBlock *guard, unsigned offset) :
        key(0), guard(guard), loop(0), offset(offset), isCrucial(false) {}
      ProfiledValue(const Loop *loop, bool del = false) : 
        key(0), guard(0), loop(loop), del(del) {}
    };
    typedef DenseMap<Value *, ProfiledValue *> ProfilingValuesT;
    ProfilingValuesT ProfilingValues;


    /// @brief A map of all memory accesses contained in this region
    //@{
    typedef DenseMap<const Instruction *, const SCEV *> MemoryAccessInfo;
    typedef DenseMap<const Value *, MemoryAccessInfo > MemoryAccessSet;
    typedef MemoryAccessSet::const_iterator MemoryAccess;
    MemoryAccessSet MemoryAccesses;
    //@}

    /// @brief A map of all violating contained in this region
    //@{
    typedef DenseMap<const Instruction *, Violation> ViolatingInstructionSet;
    typedef ViolatingInstructionSet::const_iterator ViolatingInstruction;
    ViolatingInstructionSet ViolatingInstructions;
    //@}

    /// @brief Aliasing Values are grouped in this set
    //@{
    typedef std::vector<Value *>* AliasGroupT;
    typedef std::vector<Value *>::iterator AG_iterator;
    AliasGroupT* AliasGroups;
    unsigned NumberOfAliasGroups;
    //@}
  
    /// @brief The predecessor Blocks of the entry not contained in the Region
    std::vector<BasicBlock *> entryPreds;

    public:
      /// @brief Default Constructor
      SPollyInfo(CRegionT R, RegionSpeculation *RS) : 
        RMK(RegionMapKeyForRegion(R)), R(R), nameStr(R->getNameStr()),
        RS(RS) {
        containsCalls = false;
        isValid = true;
        aliasTestBlock = 0;
        aliasTestValue = 0;
        invariantLoadBlock = 0;
        invariantCompareBlock = 0;
        invariantCompareValue = 0;   
        parallelVersion  = 0;
        parallelVersionSubfn  = 0;
        profilingVersion = 0;
        originalVersion  = RMK.first->getParent();
        branchDepth = 0;
        parallelValueMap  = 0;
        profilingValueMap = 0;
        NumberOfAliasGroups = 0;
        checksAreSound = true;
        EnableVector = true;
        hasCrucialBranches = false;
      }

      /// @brief Free all allocated objects
      ~SPollyInfo() {
        DEBUG(dbgs() << "Delete " << getNameStr() << "\n");

        if (aliasTestBlock) {
          DEBUG(dbgs() << "Remove aliasTestBlock\n"); 
          delete aliasTestBlock;
        }
        
        if (invariantCompareBlock) {
          DEBUG(dbgs() << "Remove invariantCompareBlock\n"); 
          delete invariantCompareBlock;
        }

        if (invariantLoadBlock && invariantLoadBlock != aliasTestBlock) {
          DEBUG(dbgs() << "Remove invariantLoadBlock\n"); 
          delete invariantLoadBlock;
        }
 
        if (profilingValueMap) {
          DEBUG(dbgs() << "Remove profilingValueMap\n");
          delete profilingValueMap;
          //DEBUG(dbgs() << "Remove profilingVersion\n");
          //profilingVersion->eraseFromParent();
        }

        if (parallelValueMap) {
          DEBUG(dbgs() << "Remove parallelValueMap\n");
          delete parallelValueMap;
          
          //DEBUG(dbgs() << "Remove parallelVersion\n");
          //parallelVersion->eraseFromParent();
          
          //if (parallelVersionSubfn) {
            //DEBUG(dbgs() << "Remove parallelVersionSubfn\n");
            //parallelVersionSubfn->removeBody();
            //parallelVersionSubfn->eraseFromParent();
          //}
        }

        if (NumberOfAliasGroups) {
          for (unsigned u = 0; u < NumberOfAliasGroups; u++) {
            DEBUG(dbgs() << "Remove AliasGroup[" << u << "]\n");
            delete AliasGroups[u];
          }
          DEBUG(dbgs() << "Remove AliasGroups\n");
          delete[] AliasGroups;
        }
    
        // Delete allocated GlobalVariables for profiled value struct 
        for (ProfilingValuesT::iterator it = ProfilingValues.begin(),
             end = ProfilingValues.end(); it != end; it++) {
          DEBUG(dbgs() << "Remove ProfilingValue: " << *it->first << "\n");
          DEBUG(dbgs() << "Remove ProfilingValue: " << *it->first << "\n");
          if (it->second->guard || it->second->del)
            delete (it->first);
          delete (it->second);
        }

      }

      inline Function *getOriginalVersion() const {
        return originalVersion;
      }

      Function *getProfilingVersion() {
        if (!profilingVersion) {
          profilingValueMap = new ValueToValueMapTy();
          profilingVersion  = CloneFunction(originalVersion,
                                            *profilingValueMap,
                                            // TODO What value is appropriate
                                            /* moduleLevelChanges */ true,
                                            /* ClonedCodeInfo* */ 0);
          if (RS->SD)
            RS->SD->markFunctionAsInvalid(profilingVersion);

          createProfilingVersion();
        }
        return profilingVersion;
      } 

      Function *getParallelVersion(Module *dstModule, bool useOriginal = false) {
        if (!parallelVersion) { 
          if (useOriginal) {
            assert(dstModule == originalVersion->getParent() 
                   && "Unexpected destination");

            parallelVersion  = originalVersion;
          } else {
            // 
            parallelValueMap = new ValueToValueMapTy();
            parallelVersion  = CloneFunction(originalVersion, 
                                             *parallelValueMap,
                                             // TODO What value is appropriate
                                             /* moduleLevelChanges */ true,
                                             /* ClonedCodeInfo* */ 0);
            if (RS->SD)
              RS->SD->markFunctionAsInvalid(parallelVersion);
            parallelVersion->setName(originalVersion->getName() + "_sp_par");
            dstModule->getFunctionList().push_back(parallelVersion);

          }

          createParallelVersion(useOriginal);
        }
        return parallelVersion;
      }

      /// @brief Some getters to access private members
      //@{
      inline const SCEV *getScoreSCEV() const { return ScoreSCEV; }
      inline CRegionT getRegion() const { return R; }
      inline RegionMapKey &getRMK() { return RMK; }
      inline Function *getFunction() const { return RMK.first->getParent(); }
      inline bool getChecksAreSound() const { return checksAreSound; }
      inline const std::string getNameStr() const { return nameStr; }
      inline ValueToValueMapTy *getProfilingValueMap() const { return profilingValueMap; }
      inline ValueToValueMapTy *getParallelValueMap() const { return parallelValueMap; }
      //@}

      /// @brief Some test functions
      //@{
      inline bool testsAvailable() const {
        return aliasTestsAvailable() || invariantTestsAvailable();
      }
      inline bool invariantTestsAvailable() const {
        return invariantLoadBlock && invariantLoadBlock->size(); 
      }
      inline bool aliasTestsAvailable() const {
        return aliasTestBlock && aliasTestBlock->size();
      }
      //@}
      
      /// @brief 
      void createInvariantTestingCode() {
        assert(containsCalls && "Without calls invariant tests are not needed");
        assert(!invariantLoadBlock && "InvariantTestBlock created twice");

        invariantLoadBlock = BasicBlock::Create(
                             ModuleForFunction(originalVersion)->getContext(),
                             "InvariantLoadBlock"); 
        IRBuilder<> builderLoad(invariantLoadBlock); 
        invariantCompareBlock = BasicBlock::Create(
                                ModuleForFunction(originalVersion)->getContext(),
                                "InvariantCompareBlock");
        IRBuilder<> builderCompare(invariantCompareBlock); 
    
        Value *cmp = 0;
        for (MemoryAccessSet::iterator MSI = MemoryAccesses.begin(),
             MSE = MemoryAccesses.end(); MSI != MSE; MSI++) {
          Value *BaseValue = const_cast<Value *>(MSI->first);
          MemoryAccessInfo::iterator MII = MSI->second.begin(),
                                     MIE = MSI->second.end();

          // Check if all instruction for this base value are load instructions
          for (; MII != MIE; MII++) {
            if (isa<StoreInst>(MII->first)) break;
          }

          // continue if a store instruction was encountered 
          if (MII != MIE) continue;

          // TODO checks are sound for scevs which are all equal and constant 
          // (or something like that)

          Value *loadInst = builderLoad.CreateLoad(
                                    BaseValue, BaseValue->getName() + "_tmp");
          Value *loadInstCur = builderCompare.CreateLoad(
                                    BaseValue, BaseValue->getName() + "_cur");

          Type *type = loadInst->getType();
          if (type->isPointerTy()) {
            loadInst = builderLoad.CreatePtrToInt(loadInst, 
                                                  builderLoad.getInt64Ty());
            loadInstCur = builderCompare.CreatePtrToInt(loadInstCur, 
                                                  builderLoad.getInt64Ty());
          } else if (!(type->isFloatingPointTy() || type->isIntegerTy())) {
            // TODO only int, pointer and floats are supported at the moment
            dbgs() << "Type " << *type << " is not supported yet TODO \n";
            cast<Instruction>(loadInst)->eraseFromParent();
            cast<Instruction>(loadInstCur)->eraseFromParent();
            continue;
          }

          if (type->isIntegerTy()) {
            cmp = builderCompare.CreateICmpEQ(loadInst, loadInstCur,
                                        BaseValue->getName() + "_cmp");
          } else if (type->isFloatingPointTy()) {
            cmp = builderCompare.CreateFCmpOEQ(loadInst, loadInstCur,
                                        BaseValue->getName() + "_cmp");
          }
          
          if (invariantCompareValue) {
            invariantCompareValue = 
              builderCompare.CreateAnd(invariantCompareValue, cmp);
          } else {
            invariantCompareValue = cmp;
          }
          
        } 

      }

      /// @brief 
      void insertInvariantTestingCode(BasicBlock *BB, ValueToValueMapTy *VMap) {
        assert(BB && invariantLoadBlock && VMap && "Bad invariant test block");

        DEBUG(dbgs() << "\n\n\nGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGG#\n");
        invariantLoadBlock->dump();
        DEBUG(dbgs() << "LLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLL\n");

        Instruction *I = BB->getTerminator(), *cloneI;
        BasicBlock::iterator it = invariantLoadBlock->begin(),
                            end = invariantLoadBlock->end();
        ValueToValueMapTy::iterator VMapit, VMapend = VMap->end();

        for (; it != end; it++) {
          cloneI = it->clone(); 
          cloneI->setName(it->getName());
          cloneI->insertBefore(I);

          for (unsigned u = 0, e = cloneI->getNumOperands(); u != e; u++) {
            VMapit = VMap->find(cloneI->getOperand(u));
            if (VMapit != VMapend)
              cloneI->setOperand(u, (*VMapit).second);
          } 

          DEBUG(dbgs() << "\t map " << *it << "(" << it << ")  to: "
                  << *cloneI <<  "(" << cloneI << ")\n");
          VMap->insert(std::make_pair(it, cloneI));
        }

        
        VMapit = VMap->find(RMK.first);
        assert(VMapit != VMapend && "Cloned entry not found"); 
        BasicBlock *ClonedEntry = cast<BasicBlock>(VMapit->second);
        // NewClonedEntry
        SplitBlock(ClonedEntry, ClonedEntry->begin(), RS->SD);

        // Similar to the loops above, but this time the compare block is cloned
        I = ClonedEntry->getTerminator();
        it = invariantCompareBlock->begin(); end = invariantCompareBlock->end();

        for (; it != end; it++) {
          cloneI = it->clone(); 
          cloneI->setName(it->getName());
          cloneI->insertBefore(I);

          for (unsigned u = 0, e = cloneI->getNumOperands(); u != e; u++) {
            VMapit = VMap->find(cloneI->getOperand(u));
            if (VMapit != VMapend)
              cloneI->setOperand(u, (*VMapit).second);
          } 

          DEBUG(dbgs() << "\t map " << *it << "(" << it << ")  to: "
                  << *cloneI <<  "(" << cloneI << ")\n");
          VMap->insert(std::make_pair(it, cloneI));
        }

        // Add a mapping of the saved invariantLoadBlock and the 
        // invariantLoadBlock within the loop
        VMap->insert(std::make_pair(invariantCompareBlock, ClonedEntry));

      }

      /// @brief 
      Instruction *insertAliasTestingCode(BasicBlock *BB, ValueToValueMapTy *VMap) {
        assert(BB && aliasTestBlock && "Bad alias test block");

        DEBUG(dbgs() << "\n\n\n#################################################\n");
        aliasTestBlock->dump();
        DEBUG(dbgs() << "KKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKK\n");


        Instruction *I = BB->getTerminator(), *cloneI;
        BasicBlock::iterator it = aliasTestBlock->begin(),
                            end = aliasTestBlock->end();

        // Handle the case no VMap is given, thus the original function should
        // be used
        ValueToValueMapTy EmptyMap;
        if (!VMap) {
          VMap = &EmptyMap;
        }

        for (; it != end; it++) { 
          cloneI = it->clone(); 
          cloneI->setName(it->getName());
          cloneI->insertBefore(I);

          ValueToValueMapTy::iterator VMapit, VMapend = VMap->end();
          for (unsigned u = 0, e = cloneI->getNumOperands(); u != e; u++) {
            VMapit = VMap->find(cloneI->getOperand(u));
            if (VMapit != VMapend)
              cloneI->setOperand(u, (*VMapit).second);
          } 

          DEBUG(dbgs() << "\t map " << *it << "(" << it << ")  to: "
                  << *cloneI <<  "(" << cloneI << ")\n");
          VMap->insert(std::make_pair(it, cloneI));
          
        }

        // return the clone of the aliasTestValue
        return cloneI;
      }

      /// @brief 
      void createAliasTestingCode() {
        if (NumberOfAliasGroups == 0) return;
        //return;
        assert(!aliasTestBlock && "AliasTestBlock created twice");
        aliasTestBlock = BasicBlock::Create(
                            ModuleForFunction(originalVersion)->getContext(),
                            "AliasTestBlock");

        IRBuilder<> aliasTestBlockBuilder(aliasTestBlock);
        aliasTestValue = createAliasChecks(aliasTestBlockBuilder);

        assert((!isValid || aliasTestValue) && "No Value to check for branch");

        // TODO SAVE THE ALIAS TEST INSTRUCTIONS IN A NEW FUNCTION
      }


      /// @brief TODO
      void insertProfilingCode(BasicBlock *testBlock, Value *testValue) {
        BasicBlock *profilingBlock = 
                BasicBlock::Create(testBlock->getContext(),
                                   testBlock->getNameStr() + "_pr",
                                   testBlock->getParent(),
                                   testBlock);

        // Redirect the branch of the testblock
        BranchInst *testBlockTerm =
          dyn_cast<BranchInst>(testBlock->getTerminator());
        assert(testBlockTerm && testBlockTerm->isUnconditional() 
               && "Unexpected testBlock");

        // Register the profilingBlock 
        if (RS->DT)
          RS->DT->addNewBlock(profilingBlock, testBlock);
        IRBuilder<> profilingBlockBuilder(profilingBlock);

        BasicBlock *nextBlock = testBlockTerm->getSuccessor(0);
        profilingBlockBuilder.CreateBr(nextBlock);

        BranchInst::Create(nextBlock, profilingBlock, testValue, testBlock);
        testBlockTerm->eraseFromParent();
        
        // At the moment not necessary, but for the future 
        //BasicBlock::iterator InstIt  = nextBlock->begin(),
                             //InstEnd = nextBlock->end();
        //while (InstIt != InstEnd) {
          //PHINode *Phi = dyn_cast<PHINode>(InstIt);
          //if (!Phi) break;

          //Value *val = Phi->getIncomingValueForBlock(testBlock);
          //Phi->addIncoming(val, profilingBlock);
          //InstIt++;
        //}
 
        sambamba::Profiler2 *profiler = sambamba::Profiler2::getProfiler(0);

        // Profile the test block 
        profiler->profileBranch(testBlock);

      }
      

      /// @brief Create and use a profiling version  
      void createProfilingVersion() {
        //assert(!profilingVersion && "Profiling version already created");
        //assert(profilingValueMap && "ValueToValueMap was not found");
        
        std::vector<BasicBlock *> entryPredsClones;
        unsigned entryPredsSize = entryPreds.size();
        for (unsigned i = 0; i < entryPredsSize; i++) 
          entryPredsClones.push_back(
            cast<BasicBlock>(profilingValueMap->lookup(entryPreds[i])));

        BasicBlock *testBlock = 
              SplitBlockPredecessors(
                cast<BasicBlock>(profilingValueMap->lookup(RMK.first)),
                                     &entryPredsClones[0],
                                     entryPredsSize,
                                     "_sp_profiling_split");

        if (aliasTestsAvailable()) {
          Instruction *aliasTestingValueClone = 
                insertAliasTestingCode(testBlock, profilingValueMap);
          insertProfilingCode(testBlock, aliasTestingValueClone);
        }

        if (containsCalls) {
          insertInvariantTestingCode(testBlock, profilingValueMap);
          insertProfilingCode(
            cast<BasicBlock>(profilingValueMap->lookup(invariantCompareBlock)),
                              profilingValueMap->lookup(invariantCompareValue));
        }

        sambamba::Profiler2 *profiler = sambamba::Profiler2::getProfiler(0);
        
        // TODO insert score profiling
        

        // TODO loop trip counts
        for (ProfilingValuesT::iterator it = ProfilingValues.begin(),
             end = ProfilingValues.end(); it != end; it++) {
          if (it->second->loop) {
            it->second->key = profiler->profileLoopTripCount(it->second->loop);
          } else { 
            assert(it->second->guard);
            it->second->key = profiler->profileBranch(it->second->guard);
          }
        }
      }
      

      /// @brief Use Polly to insert parallel code
      void createParallelVersion(bool useOriginal) {
        assert(    (useOriginal || parallelValueMap)
               && !(useOriginal && parallelValueMap)
               && "ValueToValueMap / useOriginal error");

        DEBUG(dbgs() << "Insert Parallel Code for " << getNameStr() << "\n");
        
        // Enable parallelization for CodeGeneration
        EnablePollyVector = EnableVector; 
        EnablePollyOpenMP = true;

        //
        Module *M = parallelVersion->getParent();

        SpeculativeRegionNameStr = getNameStr();
        EnableSpolly = false;

        FunctionPassManager fpm(M);
        fpm.add(new TargetData(M));
        fpm.add(new CodeGeneration());
        fpm.doInitialization();
        fpm.run(*parallelVersion);
        fpm.doFinalization();
        
        parallelVersionSubfn = 
          M->getFunction(parallelVersion->getNameStr() + ".omp_subfn"); 
        if (RS->SD && parallelVersionSubfn) 
          RS->SD->markFunctionAsInvalid(parallelVersionSubfn);
        
        if (parallelVersionSubfn) {
          dbgs() << "\n\n\n\n\n\n\n\n\n\n hjkl\n\n";
          parallelVersionSubfn->dump();
          dbgs() << "\n\n\n\n\n\n\n\n\n\n hjkl\n\n";
        }
        EnableSpolly = true;
        SpeculativeRegionNameStr = "";
        
        // If aliastests are available insert or rewire them
        if (aliasTestsAvailable()) {
          dbgs() << " contains Aliasing instructions " << NumberOfAliasGroups << "\n";
          BasicBlock *entry, *enterScopBlock = 0;
          if (useOriginal)
            entry = RMK.first;
          else
            entry = cast<BasicBlock>(parallelValueMap->lookup(RMK.first));
          assert(entry && "Entry in parallel version was not found");
          dbgs() << "\n\n --------------------------------\n";
          dbgs() << "UO: " << useOriginal << "\n"; 
          entry->getParent()->dump();
          dbgs() << "\n\n --------------------------------\n";

          for (pred_iterator it = pred_begin(entry), end = pred_end(entry);
               it != end; it++) {
              dbgs() << "  === "  << (*it)->getName() << "\n";
              if ((*it)->getName().startswith("polly.enterScop")) {
                enterScopBlock = *it;
                break;
              }
          }

          assert(enterScopBlock && "Did not found polly split block");
       
          // The clone of the aliasTestingValue (no need to lookup it again)  
          Instruction *newCondition = 
            insertAliasTestingCode(enterScopBlock, parallelValueMap);

          // Use the aliasTestValue to jump to the sequential 
          // or parallel version
          BranchInst *bI = dyn_cast<BranchInst>(enterScopBlock->getTerminator());
          assert (bI && (bI->getNumSuccessors() == 2) && "Bad spolly split block");
 
          // Exchange br true with the test condition
          bI->setCondition(newCondition);

        }

        
      }


      /// @brief
      inline bool isViolatingCallInstruction(const CallInst *CI) {
        FunctionCall2++;
        containsCalls = true;

        Function *F = CI->getCalledFunction();
        // TODO allow this via profiling
        // Value *VF = CI->getCalledValue()
        if (!F) {
          FunctionCallIndirect++;
          return true;
        } 

        if (CI->doesNotReturn()) {
          FunctionCallNoReturn++;
          return true;
        }

        if (CI->doesNotAccessMemory()) {
          FunctionCallReadnone++;
        } else {
          if (CI->onlyReadsMemory()) {
            FunctionCallReadonly++;
          }
        }

        if (!CI->doesNotThrow()) {
          FunctionCallThrowing++;
          return true;
        }

        StringRef Name = F->getName();
        if (Name.count("printf") || Name.count("stream") || Name.count("puts")) {
          FunctionCallPrint++;
          return true;
        }
        if (Name.count("clock") || Name.count("time")) {
          return true;
        }

        if (isa<IntrinsicInst>(CI)) {
          FunctionCallIntrinsic++;
          return true;
        }

        return false;
      }

      int64_t evaluateScoreSCEV(const SCEV *scev) const {
        switch (scev->getSCEVType()) {
          case scConstant: {
            const SCEVConstant *Constant = cast<SCEVConstant>(scev);
            const ConstantInt *C = Constant->getValue();
            return C->getSExtValue();
          }
          case scUnknown: {
            const SCEVUnknown *Unknown = cast<SCEVUnknown>(scev);
            Value *value = Unknown->getValue();
            ProfilingValuesT::const_iterator it = ProfilingValues.find(value);
            if (it != ProfilingValues.end()) {
              if (it->second->key) {
                // TODO
                return 0;
              } else {
                if (it->second->loop) {
                  return 100; // trip count
                } else {
                  assert(it->second->guard);
                  return 50; // 50% probability
                }
              }
            }
          }
          case scAddRecExpr: {
            assert(0);
          }               
          case scAddExpr: {
            const SCEVAddExpr *AddExpr = cast<SCEVAddExpr>(scev);
            SCEVNAryExpr::op_iterator it = AddExpr->op_begin(), end = AddExpr->op_end();
            int64_t summ = evaluateScoreSCEV(*(it++));
            for (;it != end; it++) {
              summ += evaluateScoreSCEV(*it);
            }
            return summ;
          } 
          case scMulExpr: {
            const SCEVMulExpr *MulExpr = cast<SCEVMulExpr>(scev);
            SCEVNAryExpr::op_iterator it = MulExpr->op_begin(), end = MulExpr->op_end();
            int64_t prod = evaluateScoreSCEV(*(it++));
            for (;it != end; it++) {
              prod *= evaluateScoreSCEV(*it);
            }
            return prod;
          } 
          // FIXME Should they be seperated ?
          case scUMaxExpr:
          case scSMaxExpr: {
            const SCEVNAryExpr *MaxExpr = cast<SCEVNAryExpr>(scev);
            SCEVNAryExpr::op_iterator it = MaxExpr->op_begin(), end = MaxExpr->op_end();
            int64_t tmp, max = evaluateScoreSCEV(*(it++));
            for (;it != end; it++) {
              tmp = evaluateScoreSCEV(*it);
              max = (tmp > max ? tmp : max);
            }
            return max;
          }
          case scUDivExpr: {
            const SCEVUDivExpr *UDivExpr = cast<SCEVUDivExpr>(scev);
            int64_t LHS = evaluateScoreSCEV(UDivExpr->getLHS());
            int64_t RHS = evaluateScoreSCEV(UDivExpr->getRHS());
            assert(RHS && "Division by ZERO");
            return (LHS / RHS);
          } 
          case scTruncate:
          case scZeroExtend:
          case scSignExtend: {
            const SCEVCastExpr *Cast = cast<SCEVCastExpr>(scev);
            return evaluateScoreSCEV(Cast->getOperand());
          }
          default:
            assert(0 && "Unexpected SCEV type as ScoreSCEV");
        } // end switch
      }

      /// @brief Compute a score for this region
      ///
      /// Profiling information, if available (the profiling version was used),
      /// will be used instead of sample values for branch probability or loop
      /// trip counts.
      inline int64_t getScore() const {
        return evaluateScoreSCEV(getScoreSCEV());
      }

      /// @brief Iterators for the internal containers
      //@{
        MemoryAccess MA_begin() { return MemoryAccesses.begin(); }
        MemoryAccess MA_end() { return MemoryAccesses.end(); }
        ViolatingInstruction VI_begin() { return ViolatingInstructions.begin();}
        ViolatingInstruction VI_end() { return ViolatingInstructions.end(); }
      //@}
     

      /// @brief Register a memory access for this region
      bool inline registerMemoryAccess(const Instruction * const I,
                                       const SCEV * const scev,
                                       const Value * const V) {
        dbgs() << "\n\n Register Memory Access: \n\t\t" << *I << "\n\t\t" 
               << *scev << "\n\t\t" << *V << "\n\n\n";
        assert(I && scev && R->contains(I) && "Bad memory access");
          
        IntegerType *IntTy64 = Type::getInt64Ty(I->getContext());

        MemoryAccesses[V].insert(std::make_pair(I, 
                                                toInt64(scev, RS->SE, IntTy64)));

        CompMemAccess++;
        return true;
      }
    
      inline void registerLoopCount(const Loop *loop) {
        LoopCounts.push_back(loop);
      } 
      
      /// @brief Register a violating instruction for this region
      bool inline registerViolatingInstruction(const Instruction * const I,
                                               const Violation V) {
        if (!R->contains(I)) {
          isValid = false;
          StatViolOutside++;
          return false;
        }

        assert(I && R->contains(I) && "Bad violating instruction");
        ViolatingInstructions.insert(std::make_pair(I, V));

        if (V != RegionSpeculation::Alias) {
          // TODO At the moment only alias checks are considered as sound checks
          checksAreSound = false;
        }

        StatViolInside++;
        return true;
      }
    

      
      // Use the less equal comparison since we want to discard equal expressions
      #define PRED_LE ICmpInst::ICMP_SLE
      #define PRED_GT ICmpInst::ICMP_SGT
      #define IS_LESS_EQ(s0, s1) RS->SE->isKnownPredicate(PRED_LE, s0, s1)
      #define IS_GREATER(s0, s1) RS->SE->isKnownPredicate(PRED_GT, s0, s1)

      /// @brief Create a pair of minimal and maximal access to this base value
      MinMaxPair createMinMaxAccessPair(IRBuilder<> &builder, Value *baseValue,
                                      sambamba::SCEVToValueMapT &SCEVToValueMap) {
        DEBUG(dbgs() << "Create MinMax Access Pair for " << *baseValue << " : " 
                << *(baseValue->getType()) << "\n");

        MemoryAccessInfo MAI = MemoryAccesses[baseValue];
        // Store all possible minimal/maximal accesses 
        std::vector<const SCEV *> minAccesses; 
        std::vector<const SCEV *>::iterator mit, mend;
        std::vector<const SCEV *> maxAccesses; 
        std::vector<const SCEV *>::iterator Mit, Mend;

        bool possibleMin, possibleMax;
        for (MemoryAccessInfo::const_iterator it = MAI.begin(), end = MAI.end();
             it != end; it++) {
          possibleMin = possibleMax = true;
          const SCEV *scev = it->second;

          // The zero case is handled anyway
          if (scev->isZero()) continue;

          // Only negative (or zero) access values can be minimal accesses
          if (RS->SE->isKnownNonPositive(scev))
            possibleMax = false;
          // Only positive (or zero) access values can be maximal accesses
          if (RS->SE->isKnownNonNegative(scev))
            possibleMin = false;
          
          // Test all possible minima
          if (possibleMin) {
            for (mit = minAccesses.begin(), mend = minAccesses.end();
                 mit != mend; mit++) {
              if (IS_LESS_EQ(*mit, scev)) possibleMin = false;
              if (IS_GREATER(*mit, scev)) mit = minAccesses.erase(mit);
            }
            if (possibleMin) { 
              minAccesses.push_back(scev);
            }
          }

          // Test all possible maxima
          if (possibleMax) {
            for (Mit = maxAccesses.begin(), Mend = maxAccesses.end();
                 Mit != Mend; Mit++) { 
              if (IS_LESS_EQ(scev, *Mit)) possibleMax = false;
              if (IS_GREATER(scev, *Mit)) Mit = maxAccesses.erase(Mit);
            }
            if (possibleMax) {
              maxAccesses.push_back(scev);
            }
          }
        }
        
        // Test if one min/maxAccess vector is empty
        if (!minAccesses.size())
          minAccesses.push_back(RS->SE->getConstant(builder.getInt64Ty(),
                                                    0, /* signed */ true));
        if (!maxAccesses.size())
          maxAccesses.push_back(RS->SE->getConstant(builder.getInt64Ty(),
                                                    0, /* signed */ true));
        
        //minAccesses.swap(maxAccesses);

        // The baseValue as scev
        const SCEV *baseSCEV = 
          toInt64(RS->SE->getSCEV(baseValue), RS->SE, builder.getInt64Ty());

        // Create LLVM-IR for the collected SCEVs  
        std::deque<Value *> minAccessValues;
        std::deque<Value *> maxAccessValues;
         
        bool success = true;
        for (mit = minAccesses.begin(), mend = minAccesses.end(); mit != mend;
             mit++) {
          const SCEV *s = RS->SE->getAddExpr(baseSCEV, *mit);
          DEBUG(dbgs() << "SCEV2ValueMinAccess: " << s << "   " << *s << " \n");
          Value *val = sambamba::SCEVToValue(builder, s, SCEVToValueMap, RS->SE,
                                             success, RS->TD);
          if (success) {
            // maxAccessValues is right !
            maxAccessValues.push_back(val);
          } else {
            success = true;
            checksAreSound = false;
            // TODO remove val and all operands
          }
        }
        
        success = true;
        for (Mit = maxAccesses.begin(), Mend = maxAccesses.end(); Mit != Mend;
             Mit++) {
          const SCEV *s = RS->SE->getAddExpr(baseSCEV, *Mit);
          DEBUG(dbgs() << "SCEV2ValueMaxAccess: " << s << "   " << *s <<  " \n");
          Value *val = sambamba::SCEVToValue(builder, s, SCEVToValueMap, RS->SE,
                                             success, RS->TD);
          if (success) {
            // minAccessValues is right !
            minAccessValues.push_back(val);
          } else {
            success = true;
            checksAreSound = false;
            // TODO remove val and all operands
          }
        }

        // Compare the created values 
        while (minAccessValues.size() > 1) {
          Value *A = minAccessValues.front(); minAccessValues.pop_front();
          Value *B = minAccessValues.front(); minAccessValues.pop_front();
          assert(A->getType()->isIntegerTy(64) && "Found wrong value type");
          assert(B->getType()->isIntegerTy(64) && "Found wrong value type");
          Value *cmp = builder.CreateICmpSGT(A, B, 
                                         A->getName() + "_GT_" + B->getName());
          Value *sel = builder.CreateSelect(cmp, A, B, 
                                         A->getName() + "_sel_" + B->getName());
          minAccessValues.push_back(sel);
        }
        
        // Compare the created values 
        while (maxAccessValues.size() > 1) {
          Value *A = maxAccessValues.front(); maxAccessValues.pop_front();
          Value *B = maxAccessValues.front(); maxAccessValues.pop_front();
          assert(A->getType()->isIntegerTy(64) && "Found wrong value type");
          assert(B->getType()->isIntegerTy(64) && "Found wrong value type");
          Value *cmp = builder.CreateICmpSLT(A, B,
                                         A->getName() + "_LT_" + B->getName());
          Value *sel = builder.CreateSelect(cmp, A, B,
                                         A->getName() + "_sel_" + B->getName());
          maxAccessValues.push_back(sel);
        }

        assert(minAccessValues.size() == 1 
               && "Expected one minimal access value");
        assert(maxAccessValues.size() == 1 
               && "Expected one maximal access value");
        
        return std::make_pair(minAccessValues.front(), maxAccessValues.front());
        
      }


      /// @brief Create a SCEV representing the score of a Instruction
      ///
      /// @param I The Instruction to score
      ///
      /// @return A SpollyInfo::scoreSCEV 
      const SCEV *createSCEVForInstruction(const Instruction *I) {
        dbgs() << " I: " << *I << "\n";
        int score = 1;

        if (const LoadInst *LI = dyn_cast<LoadInst>(I)) {
          PointerType *pointerType = cast<PointerType>(LI->getPointerOperand()->getType());
          if (!(LI->getType()->isSized() && pointerType->isSized())) {
            dbgs() << " not sized: " << *LI << "\n";

            // Statistic
            UnsizedPointer++;

            //isValid = false;
            // TODO only disable vector ?
          } else {
            if (!VectorType::isValidElementType(pointerType)) {
              // Statistics
              NonVectorizable++;
              dbgs() << "   == Disable vector instructions \n";
              // TODO when to do this ?
              //EnableVector = false;
            }
          }
        }

        // TODO Differentiate between the instructions
        if (ViolatingInstructions.count(I)) score = -1;

        if (const CallInst *CI = dyn_cast<CallInst>(I)) {
          if (isViolatingCallInstruction(CI)) {
            if (branchDepth == 0) {
              // Statistic
              CrucialCall++;

              isValid = false;
            } else {
              BranchIsCrucial = true;
              score = -100;
            }
          }
        }

        ConstantInt *CI = ConstantInt::get(Type::getInt64Ty(RMK.first->getContext()),
                                           score, /* isSigned */ true);
        return RS->SE->getConstant(CI);
      }


      /// @brief Create a SCEV representing the score of this BasicBlock (BB)
      /// 
      /// @param BB 
      ///
      /// @return A SpollyInfo::scoreSCEV 
      const SCEV *createSCEVForBasicBlock(const BasicBlock *BB) {
        dbgs() << " BB: " << BB->getNameStr() << "\n";
        SmallVector<const SCEV *, 32> scevs;

        BasicBlock::const_iterator it = BB->begin(), end = BB->end();
        assert(it != end && "BasicBlock is empty");

        for (;it != end; it++) {
          scevs.push_back(createSCEVForInstruction(it));
        } 

        return RS->SE->getAddExpr(scevs);
      }


      /// @brief Create a SCEV representing the score of 
      /// 
      /// @param R 
      ///
      /// @return A SpollyInfo::scoreSCEV 
      const SCEV *createSCEVForRegionElements(const Region *R) {
        dbgs() << " RegionElements: " << R->getNameStr() << "\n";
        SmallVector<const SCEV *, 32> scevs;

        // Handle all subregions and basicBlocks within this region
        Region::const_element_iterator it = R->element_begin(),
                                      end = R->element_end();
        assert(it != end && "Loop body is totaly empty");

        for (; it != end; it++) { 
          if ((*it)->isSubRegion()) {
            dbgs() << "SubRegion: " << *it << " \n";
            const Region *region = (*it)->getNodeAs<Region>();
            scevs.push_back(createSCEVForRegion(region));
          } else {
            dbgs() << "BasicBlock: " << *it << " \n";
            const BasicBlock *BB = (*it)->getNodeAs<BasicBlock>();
            scevs.push_back(createSCEVForBasicBlock(BB));
          }
        }

        return RS->SE->getAddExpr(scevs);
      }


      const SCEV *profileValueIfAny(const SCEV *scev, const Loop *loop, ScalarEvolution *SE) {
        IntegerType *Ty = Type::getInt64Ty(SE->getContext());
        
        switch (scev->getSCEVType()) {
          case scUnknown: {
            //Statistics
            LoopProfilingCheap++;

            const SCEVUnknown *Unknown = cast<SCEVUnknown>(scev);
            Value *value = Unknown->getValue();
            ProfiledValue *PL = new ProfiledValue(loop, false);
            ProfilingValues[value] = PL; 
            return toInt64(SE->getSCEV(value), SE, Ty);
          }
          case scTruncate:
          case scZeroExtend:
          case scSignExtend: {
            const SCEVCastExpr *Cast = cast<SCEVCastExpr>(scev);
            return profileValueIfAny(Cast->getOperand(), loop, SE);
          }
          case scAddExpr: 
          case scMulExpr:
          case scSMaxExpr:
          case scUMaxExpr: {
            SmallVectorImpl<const SCEV *> scevs(2);
            const SCEVNAryExpr *NAry = cast<SCEVNAryExpr>(scev);
            for (SCEVNAryExpr::op_iterator it = NAry->op_begin(), 
                 end = NAry->op_end(); it != end; it++) {
              scevs.push_back(profileValueIfAny(*it, loop, SE));
            }
            switch (scev->getSCEVType()) {
            case scAddExpr:  return SE->getAddExpr(scevs);
            case scMulExpr:  return SE->getMulExpr(scevs);
            case scSMaxExpr: return SE->getSMaxExpr(scevs);
            case scUMaxExpr: return SE->getUMaxExpr(scevs);
            default: assert(0);
            }
          }
          case scAddRecExpr: {
            // else, create a placeholder and use the profiler (later) 
            GlobalValue *GV = new GlobalVariable(Ty, false,
                                                 GlobalValue::ExternalLinkage, 0,
                                                 loop->getHeader()->getNameStr() 
                                                 + "_loop_ex_prob");

            ProfiledValue *PL = new ProfiledValue(loop);
            ProfilingValues[GV] = PL; 
            return SE->getSCEV(GV);
          }
          case scUDivExpr: {
            const SCEVUDivExpr *UDiv = cast<SCEVUDivExpr>(scev);
            const SCEV *LHS = profileValueIfAny(UDiv->getLHS(), loop, SE);
            const SCEV *RHS = profileValueIfAny(UDiv->getRHS(), loop, SE);
            return SE->getUDivExpr(LHS, RHS);
          }
          default:
            break;
        }
        return toInt64(scev, SE, Ty);
      }

      /// @brief Create a SCEV representing the score of a Loop
      /// 
      /// @param R The Region where the Loop is embedded
      ///
      /// @return A SpollyInfo::scoreSCEV 
      const SCEV *createSCEVForLoop(const Region *R) {
        dbgs() << " L: " << R->getNameStr() << "\n";
        dbgs() << "\n\n scev for loop " << R->getNameStr() << " \n";
        const Loop *loop = RS->LI->getLoopFor(R->getEntry());
        IntegerType *Ty = Type::getInt64Ty(RMK.first->getContext());
        
        // Statistics
        LoopCount2++;

        // Use a treshold to score only loops over this treshold
        ConstantInt *tripCountTreshold  = ConstantInt::get(Ty, 10, false);
        const SCEV *tripCount; 
          // Test if there is an loop invariant trip count (+-1 offset) 
        if (RS->SE->hasLoopInvariantBackedgeTakenCount(loop)) {
          // if so, use it 
          tripCount = profileValueIfAny(RS->SE->getBackedgeTakenCount(loop),
                                        loop, RS->SE);
        } else {
          // Statistics
          LoopProfilingExpensive++;

          // else, create a placeholder and use the profiler (later) 
          GlobalValue *GV = new GlobalVariable(Ty, false,
                                               GlobalValue::ExternalLinkage, 0,
                                               loop->getHeader()->getNameStr() 
                                               + "_loop_ex_prob");

          ProfiledValue *PL = new ProfiledValue(loop);
          ProfilingValues[GV] = PL; 
          tripCount = RS->SE->getSCEV(GV);
        }
        dbgs() << " tripcount " << *tripCount << "\n";

        const SCEV *tripCountTresholdSCEV = RS->SE->getConstant(tripCountTreshold);
        const SCEV *loopExp   = RS->SE->getUDivExpr(tripCount, tripCountTresholdSCEV);
        const SCEV *bodyScore = createSCEVForRegionElements(R);
        const SCEV *loopScore = RS->SE->getMulExpr(bodyScore, loopExp);

        return loopScore;
      }


      const SCEV *createSCEVForBranch(BasicBlock *current, const Region *R) {
        dbgs() << " Branch: " << current->getName() << "  " << R->getNameStr() << "\n"; 
        if (current == R->getExit() || current == R->getEntry()) 
          return RS->SE->getConstant(APInt(64,0));
        
        Region *Rcurrent = RS->RI->getRegionFor(current);
        if (Rcurrent->getEntry() == current) {
          dbgs() << "   == rec for region " << Rcurrent->getNameStr() << "\n";
          const SCEV *Rscore = createSCEVForRegion(Rcurrent);
          const SCEV *Escore = createSCEVForBranch(Rcurrent->getExit(), R);
          return RS->SE->getAddExpr(Rscore, Escore);
        } else {
          dbgs() << "   == rec for BB " << current->getNameStr() << "\n";
          const SCEV *Bscore = createSCEVForBasicBlock(current);
          SmallVectorImpl<const SCEV*> scevs(2);
          scevs.push_back(Bscore);
          for (succ_iterator it = succ_begin(current), end = succ_end(current);
               it != end; it++) {
            scevs.push_back(createSCEVForBranch(*it, R));
          }
          return RS->SE->getAddExpr(scevs);
        }
      }


      /// @brief Create a SCEV representing the score of a conditional
      /// 
      /// @param R A Region where the conditional is embedded 
      /// 
      /// @return A SpollyInfo::scoreSCEV 
      const SCEV *createSCEVForConditional(const Region *R) {
        dbgs() << " C: " << *R << "\n";
        BasicBlock *entry = R->getEntry();
        IntegerType *Int64Ty = Type::getInt64Ty(entry->getContext());
        const SCEV *entryScore = createSCEVForBasicBlock(entry);

        // Enter the conditional
        branchDepth++;

        // Statistics
        BranchCount++;

        const TerminatorInst * const guard = entry->getTerminator();
        assert(guard->getNumSuccessors() == 2 
               && "Guard with two successors expected");

        BasicBlock *branch0BB = guard->getSuccessor(0);
        BasicBlock *branch1BB = guard->getSuccessor(1);
        dbgs() << "   Successors: " << branch0BB->getName() 
               << " and " << branch1BB->getName() <<"\n";
 
        GlobalValue *GV0 = new GlobalVariable(Int64Ty, 
                                              false,
                                              GlobalValue::ExternalLinkage, 0,
                                              branch0BB->getName() +"_ex_prob");
        GlobalValue *GV1 = new GlobalVariable(Int64Ty, 
                                              false,
                                              GlobalValue::ExternalLinkage, 0,
                                              branch1BB->getName() +"_ex_prob");

        ProfiledValue *PB0 = new ProfiledValue(entry, 0);
        ProfiledValue *PB1 = new ProfiledValue(entry, 1);

        ProfilingValues[GV0] = PB0; 
        ProfilingValues[GV1] = PB1; 

        // Profiling support is added later
        const SCEV *prob0 = toInt64(RS->SE->getSCEV(GV0), RS->SE, Int64Ty);
        const SCEV *prob1 = toInt64(RS->SE->getSCEV(GV1), RS->SE, Int64Ty);
        
        SmallVector<const SCEV *, 32> branch0Scores;
        SmallVector<const SCEV *, 32> branch1Scores;

        BranchIsCrucial = false;
        const SCEV *branch0Score = createSCEVForBranch(branch0BB, R);
        
        // Test and mark the branch as crucial
        if (BranchIsCrucial) {
          CrucialBranch++;
          PB0->isCrucial = true;
          hasCrucialBranches = true;
        } else {
          NonCrucialBranch++;
        }
        
        BranchIsCrucial = false;
        const SCEV *branch1Score = createSCEVForBranch(branch1BB, R);
        
        // Test and mark the branch as crucial
        if (BranchIsCrucial) {
          CrucialBranch++;
          PB1->isCrucial = true;
          hasCrucialBranches = true;
        } else {
          NonCrucialBranch++;
        }
        BranchIsCrucial = false;
        
        dbgs() << *branch0Score->getType() << "  " << *prob0->getType() << "\n";
        dbgs() << *branch1Score->getType() << "  " << *prob1->getType() << "\n";
        dbgs() << *toInt64(branch1Score, RS->SE, Int64Ty)->getType() << "\n";

        const SCEV *divisor = RS->SE->getConstant(APInt(64, 100, false));
        const SCEV *branch0ScoreProb = 
          RS->SE->getUDivExpr(RS->SE->getMulExpr(branch0Score, prob0), divisor);
        const SCEV *branch1ScoreProb = 
          RS->SE->getUDivExpr(RS->SE->getMulExpr(branch1Score, prob1), divisor);

        const SCEV *conditionalScore = RS->SE->getAddExpr(entryScore, 
                                                       branch0ScoreProb,
                                                       branch1ScoreProb);

        // Leave the conditional
        branchDepth--;
        // Test if both branches are crucial
        if (!branchDepth && PB0->isCrucial && PB1->isCrucial) {
          CrucialCall++;
          isValid = false;
        }

        DEBUG(dbgs() << *conditionalScore << "\n");
        DEBUG(dbgs() << "dsaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n");
        return conditionalScore;
      }


      /// @brief Create a SCEV representing the score of a Region
      /// 
      /// @param R The Region to score
      /// 
      /// @return A SpollyInfo::scoreSCEV 
      const SCEV *createSCEVForRegion(const Region *R) {
        dbgs() << " Region: " << R->getNameStr() << "\n";
        if (regionIsLoop(R, RS->LI)) {
          return createSCEVForLoop(R);
        } else if (regionIsConditional(R)) {
          return createSCEVForConditional(R);
        } else {
          if (isValid) {
            StatIllFormedRegion++;
            isValid = false;
          }
          return RS->SE->getConstant(APInt(64, 0, false));
        }
      }

            
      /// @brief Create an alias check between the given two values
      /// 
      /// @param builder The IRBuilder to create IR-Instructions
      /// @param A The minimal and maximal access for a pointer
      /// @param B The minimal and maximal access for a pointer
      /// 
      /// @return The value: (min(A) < max(B) || min(B) < max(A))
      ///
      Value *createAliasCheck(IRBuilder<> &builder,
                              MinMaxPair &A, MinMaxPair &B) {
        Value *minA = A.first, *maxA = A.second;
        Value *minB = B.first, *maxB = B.second;
  
        Value *result0 = builder.CreateICmpSLT(minA, maxB,
                                               minA->getNameStr() + "_lt_" 
                                               + maxB->getNameStr());

        Value *result1 = builder.CreateICmpSLT(minB, maxA,
                                               minB->getNameStr() + "_lt_" 
                                               + maxA->getNameStr());
        
        Value *result  = builder.CreateOr(result0, result1, result0->getNameStr()
                                                            + "_v_" 
                                                            + result1->getNameStr());
         
        return result; 
      }


      /// @brief Create alias checks using the given IRBuilder
      /// 
      /// The return value is a i1 type value which is true if all checks 
      /// are passed, false otherwise
      Value *createAliasChecks(IRBuilder<> &builder) {
         
        DEBUG(dbgs() << "Create alias checks for " << getNameStr() << "\n");
        assert(aliasTestBlock && "No aliasing block to insert instructions");

        sambamba::SCEVToValueMapT SCEVToValueMap;

        // The returned result
        std::deque<Value *> results;
        for (unsigned u = 0, e = NumberOfAliasGroups; u != e; u++) {
          AliasGroupT AG = AliasGroups[u];

          std::vector<MinMaxPair> ToCheck; 
          // Fill the ToCheck deque with all inital min/max pairs
          for (std::vector<Value*>::const_iterator it = AG->begin(),
               end = AG->end(); it != end; it++ ) {
            ToCheck.push_back(createMinMaxAccessPair(builder, *it, 
                                                     SCEVToValueMap));
            MinMaxPair AB = ToCheck.back();
            dbgs() << "\n---------------------------------------\n";
            dbgs() << *AB.first << "\n\n" << *AB.second 
                   << "\n---------------------------------------\n";
          }

          for (std::vector<MinMaxPair>::const_iterator Ait = ToCheck.begin(),
               Aend = ToCheck.end(); Ait != Aend; Ait++) {
            MinMaxPair A = *Ait; 
            for (std::vector<MinMaxPair>::const_iterator Bit(Ait),
                 Bend = ToCheck.end(); ++Bit != Bend;) {
                  // Get the first two elements
              MinMaxPair B = *Bit; 
            
              // Create a test for A and B and push them back into the deque
              Value *AB = createAliasCheck(builder, A, B);
              results.push_back(AB);
            } // Bit
          } // Ait
        } // for (unsigned u = 0, e = NumberOfAliasGroups; u != e; u++)

        while (results.size() > 1) {            
          // Get the first two elements
          Value *A = results.front(); results.pop_front(); 
          Value *B = results.front(); results.pop_front(); 
          
          Value *AB = builder.CreateAnd(A, B, A->getName() + "_and_" +B->getName()); 
          results.push_back(AB);
          
        }

        dbgs() << "Result: ";
        dbgs() << *results.front() << "\n";
        return results.front();
        
      }
      

      /// @brief Create the alias set for this region
      void createAliasSets(AliasSetTracker &AST) { 
        NumberOfAliasGroups = AST.getAliasSets().size();

        unsigned groupNo = 0;
        AliasGroups = new AliasGroupT[NumberOfAliasGroups];
        AliasGroups[groupNo] = new std::vector<Value *>();
        // Iterate over all AliasSets in the AliasSetTracker
        for (AliasSetTracker::const_iterator AST_it = AST.begin(), 
             AST_end = AST.end(); AST_it != AST_end; AST_it++, groupNo++) {
          const AliasSet &AS = *AST_it;
          AliasGroupT AG = AliasGroups[groupNo];

          // Iterate over all Values in the AliasSet and remove all which 
          // are not usefull for profiling purposes
          for (AliasSet::iterator it = AS.begin(), end = AS.end();
               it != end; it++) {
            Value *AliasSetValue = it->getValue();
            
            // Test if the aliasing value is produced by an instruction
            if (Instruction *I = dyn_cast<Instruction>(AliasSetValue)) {
              // If it is, test if the instruction is contained in this region
              if (R->contains(I)) {
                // This invalidates the soundness of the checks
                checksAreSound = false;

                DEBUG(dbgs() << "Skipping aliasing Instruction " << *I 
                        << " since it is contained in the "
                        << "speculative valid region\n");
                continue;
              } 
            } // end test
            
            // Add the value to the AliasingValuesGroup
            AG->push_back(AliasSetValue);
          } // end AliasSet iterator

          // Remove groups with less than two AliasingValues
          if (AG->size() < 2) {
            dbgs() << "Remove alias group with less than two members\n";
            AG->clear();
            groupNo--;  
            NumberOfAliasGroups--;
          } else {
            AliasGroups[groupNo + 1] = new std::vector<Value *>();
          }

        } // end AliasSetTracker iterator

      }


      /// @brief Validate this region
      ///
      /// This function need to be called after all memory accesses and 
      /// violating instructions are registered. 
      /// The return value indicates iff this region should be considered as 
      /// speculative valid scop.
      /// 
      ///  - It creates the set of aliasing Values which can be tested
      /// 
      bool validate(AliasSetTracker &AST) { 
        DEBUG(dbgs() << "Validate speculative valid region: "
                     << R->getNameStr() << "\n");


        ScoreSCEV = createSCEVForRegion(R); 
        DEBUG(dbgs() << "\nScoreSCEV created\n============\n");

        if (!isValid) { 
          StatInvalidByRS++;
          return false;
        }

        createAliasSets(AST);
        AST.clear();
        DEBUG(dbgs() << "\nAliasSets created\n============\n");

        if (!isValid) { 
          StatInvalidByRS++;
          return false;
        }

        if (LoopCounts.size()) {
          // TODO allow this
          StatNonAffineLoopCount++;
          StatInvalidByRS++;

          return false;
        }
 
        // Collect all predecessors of entry which do not belong to the region
        for (pred_iterator itPred = pred_begin(RMK.first),
             end = pred_end(RMK.first); itPred != end; itPred ++) {
          if ( R->contains(*itPred) ) continue;
            entryPreds.push_back(*itPred);
        }

        // Computations only done if the region is valid
        createAliasTestingCode();
        if (containsCalls)
          createInvariantTestingCode();

        // Some Statistics
        StatValidByRS++;
        StatMemoryAccesses        += MemoryAccesses.size();
        StatNumberOfAliasGroups   += NumberOfAliasGroups;
        StatSCoPWithAliases       += (NumberOfAliasGroups ? 1 : 0);
        StatChecksAreSound        += checksAreSound;
        StatAliasTests            += aliasTestsAvailable();
        StatInvariantTests        += invariantTestsAvailable();
        StatContainsCalls         += containsCalls;
        StatInitialScores         += getScore();
        StatFunctionCall          += FunctionCall2;
        StatFunctionCallIndirect  += FunctionCallIndirect;
        StatFunctionCallNoReturn  += FunctionCallNoReturn;
        StatFunctionCallReadnone  += FunctionCallReadnone;
        StatFunctionCallReadonly  += FunctionCallReadonly;
        StatFunctionCallThrowing  += FunctionCallThrowing;
        StatFunctionCallPrint     += FunctionCallPrint;
        StatFunctionCallIntrinsic += FunctionCallIntrinsic;
        StatCompMemAccess         += CompMemAccess;
        StatUnsizedPointer        += UnsizedPointer;
        StatNonVectorizable       += NonVectorizable;
        StatLoopProfilingCheap    += LoopProfilingCheap;
        StatLoopProfilingExpensive+= LoopProfilingExpensive;
        StatLoopCount             += LoopCount2;
        StatCrucialBranch         += CrucialBranch;
        StatNonCrucialBranch      += NonCrucialBranch;
        StatBranchCount           += BranchCount;
        StatCrucialCall           += CrucialCall;
        StatContainsLoop          += (LoopCount2 ? 1 : 0);
        StatContainsBranch        += (BranchCount ? 1 : 0);


        for (unsigned u = 0, e = NumberOfAliasGroups; u != e; u++) {
          AliasGroupT AG = AliasGroups[u];
          StatAliasingInstructions += AG->size();
        }

        assert(isValid && "Something went terrible wrong -.-");
        return isValid;
      }
    
      /// @brief Pretty print all contained information 
      void print(raw_ostream &OS) {
        OS << "\n\nSpollyInfo: " << getNameStr() << " \t In: "
           << originalVersion->getNameStr() << "\n\n";

        OS.indent(4) << " ChecksAreSound: " << checksAreSound << "\n";
        OS.indent(4) << " Has crucial branches: " << hasCrucialBranches << "\n";
        OS.indent(4) << " #MemoryAccesses: " << MemoryAccesses.size() << "\n";

        for (MemoryAccess it = MA_begin(),end = MA_end(); it != end; it++){
          assert(it->first && "Bad base value");
          OS.indent(8) << " BaseValue: " << *(it->first) << " accesed at: \n";
          for (MemoryAccessInfo::const_iterator mit = it->second.begin(), 
               mend = it->second.end(); mit != mend; mit++) {
            assert(mit->second && mit->first && "Bad access");
            OS.indent(12) << "-" << *(mit->second) << " by " << *(mit->first) << "\n";
          }
        }

        OS.indent(4) << " ScoreSCEV:     " << *ScoreSCEV << "\n\n";
        OS.indent(8) << " evaluated: " << getScore() << "\n\n";
        
        OS.indent(4) << " #ViolatingInstructions: " 
                     << ViolatingInstructions.size() << "\n";
        for (ViolatingInstruction it = VI_begin(),end = VI_end();
             it != end; it++){
          OS.indent(8) << *(it->first) << "\t\t" << (it->second) << "\n";
        }
        
        OS.indent(4) << " #AliasGroups: " 
                     << NumberOfAliasGroups << "\n";

        for (unsigned u = 0, e = NumberOfAliasGroups; u != e; u++) {
          OS.indent(8) << "AliasGroup[" << u << "]:\n";
          AliasGroupT AG = AliasGroups[u];
          for (AG_iterator it = AG->begin(), end = AG->end(); it != end; it++) {
            OS.indent(12) << **it << "\n";
          }
        }
       
        if (aliasTestBlock) { 
          OS << "\n\nAliasTestBlock: \n";
          aliasTestBlock->print(OS);
          OS << "\n\n";
        }

        OS << "\n\nOriginal Version:\n";
        originalVersion->print(OS);
        OS << "\n\n";
    
        if (profilingVersion) {
          OS << "\n\nProfiling Version:\n";
          profilingVersion->print(OS);
          OS << "\n\n";
        }

        if (parallelVersion) {
          OS << "\n\nParallel Version:\n";
          parallelVersion->print(OS);
          OS << "\n\n";
          if (parallelVersionSubfn) {
            OS << "\n\nProfiling Version (Subfn):\n";
            parallelVersionSubfn->print(OS);
            OS << "\n\n";
          }
        }


      } 


  }; // end class SPollyInfo
} // end namespace polly

/// @brief The default constructor
/// 
/// - Create the SPollyInfo ScalarEvolution object
RegionSpeculation::RegionSpeculation() {
  DEBUG(dbgs() << "\n============ Create Region Speculation =============== \n");
  
  TemporaryRegion = 0;

} 

/// @brief
RegionSpeculation::~RegionSpeculation() {
  DEBUG(dbgs() << "\n============ Delete Region Speculation =============== \n");

  for (iterator it = begin(), e = end(); it != e; it++) {
    delete (it->second);
  }
}


/// @brief Register a violating instruction for the current region 
bool RegionSpeculation::registerViolatingInstruction(const Instruction* const I,
                                                     Violation V) { 
  assert(TemporaryRegion && "No TemporaryRegion to insert access");
  return TemporaryRegion->registerViolatingInstruction(I, V);
}


/// @brief Register a memory access for the current region (TemporaryRegion)
bool RegionSpeculation::registerMemoryAccess(const Instruction * const I,
                                             const SCEV * const scev,
                                             const Value * const V) {
  assert(TemporaryRegion && "No TemporaryRegion to insert access");

  return TemporaryRegion->registerMemoryAccess(I, scev, V);
}

/// @brief Store the associated SPollyInfo object for the given region
/// 
/// The SPollyInfo object from TemporaryRegion will be added
/// to the SpeculativeValidRegions map.
void RegionSpeculation::storeTemporaryRegion(CRegionT R, AliasSetTracker &AST) {
  DEBUG(dbgs() << "*\t Store TemporaryRegion " << R->getNameStr() 
          << " in " << FunctionForRegion(R)->getNameStr() << "\n");

  RegionMapKey &RMK = TemporaryRegion->getRMK();

  assert(R == TemporaryRegion->getRegion()
         && "Region does not match TemporaryRegion");
  assert(!SpeculativeValidRegions.count(RMK)
         && "Region is already contained in SpeculativeValidRegions");
 
   
  // Validate the TemporaryRegion and create the scoreSCEV 
  if (!TemporaryRegion->validate(AST)) {
    DEBUG(dbgs() << "*\t Validation of TemporaryRegion " << R->getNameStr() 
            << " failed.\n");
    
    // Forget the TemporaryRegion instead of storing it
    forgetTemporaryRegion(R);
    return;
  }

  SpeculativeValidRegions[RMK] = TemporaryRegion;
  
  // Print the SPollyInfo object 
  //DEBUG(
    //TemporaryRegion->print(dbgs());
  //);
  //assert(0);
  TemporaryRegion = 0;
}


/// @brief Delete the associated SPollyInfo object for the given region
void RegionSpeculation::forgetTemporaryRegion(CRegionT R) {
  DEBUG(dbgs() << "*\t Forget TemporaryRegion " << R->getNameStr()
          << " in " << FunctionForRegion(R)->getNameStr() << "\n"); 

  RegionMapKey &RMK = TemporaryRegion->getRMK();

  assert(R == TemporaryRegion->getRegion()
         && "Cannot forget an unknown temporary region");
  assert(!SpeculativeValidRegions.count(RMK)
         && "Region cannot be temporary and speculative valid");
  
  delete TemporaryRegion;
  TemporaryRegion = 0;
}


/// @brief Create a new SPollyInfo object for the given region
/// 
/// The new created object is associated with the given region and stored as
/// TemporaryRegion
void RegionSpeculation::newTemporaryRegion(CRegionT R) {
  DEBUG(dbgs() << "*\t New TemporaryRegion " << R << " " <<   R->getNameStr() 
          << " in " << FunctionForRegion(R)->getNameStr() << "\n");

  RegionMapKey RMK = RegionMapKeyForRegion(R);

  assert(!TemporaryRegion && "There is already a TemporaryRegion");
  assert((!SpeculativeValidRegions.count(RMK)) 
         && "Region cannot be temporary and speculative valid");
 
  // Create a SpollyInfo object with the Region *R and the internal ScalarEvolution 
  TemporaryRegion = new SPollyInfo(R, this);
}


/// @brief Initialize the RegionSpeculation for a new ScopDetection run
/// 
/// Save the given analyses passes and init a new temporary map to match
/// violating instructions to speculative valid regions
void RegionSpeculation::initScopDetectionRun(Function &function,
                          AliasAnalysis *aa, ScalarEvolution *se, 
                          LoopInfo *li, RegionInfo *ri, 
                          DominatorTree *dt, TargetData *td,
                          ScopDetection *sd) {
  DEBUG(dbgs() << "*\t Init ScopDetection run \n");

  // Save the given analyses
  assert(aa && se && li && ri && dt && td && sd && "Analyses are not valid");
  AA = aa; SE = se; LI = li; RI = ri; DT = dt; TD = td; SD = sd;

  FunctionCall2 = 0; FunctionCallIndirect = 0; FunctionCallNoReturn = 0;
  FunctionCallReadnone = 0; FunctionCallReadonly = 0; FunctionCallThrowing = 0;
  FunctionCallPrint = 0; FunctionCallIntrinsic = 0; CompMemAccess = 0; BranchCount = 0;
  UnsizedPointer = 0; NonVectorizable = 0; LoopProfilingCheap = 0;  NonCrucialBranch = 0;
  LoopProfilingExpensive = 0; LoopCount2 = 0; CrucialBranch = 0; CrucialCall = 0;


  // All TemporaryRegions should be saved or deleted 
  assert(!TemporaryRegion
         && "TemporaryRegion was not 0 during initialization");
  
}

/// @brief Finalize the ScopDetection run 
/// 
///  - Forget the given analyses
void RegionSpeculation::finalizeScopDetectionRun() {
  DEBUG(dbgs() << "*\t Finalyze ScopDetection run \n");
  
  // Forget the given analyses
  AA = 0;  LI = 0; RI = 0; DT = 0; TD = 0; SD = 0;
  // SE = 0;
  
  // All TemporaryRegions should be saved or deleted 
  assert(!TemporaryRegion
         && "TemporaryRegion was not 0 during finalization");

  std::set<Function *> changedFunctions;
  if (ReplaceByParallelVersion || ReplaceByParallelVersionSound) {
    for (iterator I2 = SpeculativeValidRegions.begin(),
        E2 = SpeculativeValidRegions.end(); I2 != E2; ++I2) {
      
      for (iterator I(I2); ++I != E2;) {

        Function *orig = getOriginalVersion(I->second);
        if (!(ReplaceByParallelVersion || checksAreSound(I->second))) continue;
        dbgs() << I->second->getNameStr() << "  in  " << orig->getName() << "\n";
        Module   *M = orig->getParent();
        if (changedFunctions.count(orig)) {
          orig->dump();
          //Function *F = getParallelVersion(I->second, M, true);
          //F->dump();
          //assert(0);
        } else { 
          Function *F = getParallelVersion(I->second, M, true);
          assert(orig == F && "Use original did not work");
          changedFunctions.insert(orig);
          F->print(dbgs());
          assert(!llvm::verifyModule(*M, PrintMessageAction));
          break;
        }
      }
    }
  }

}


  
/// @brief Verify the communication between ScopDetection and RegionSpeculation 
///
/// This is called after by the veryify function of the ScopDetection pass
/// and should only be used in DEBUG mode
void RegionSpeculation::verifyRS(const RegionSet &ValidRegions, 
                                 const RegionSet &SpeculativeValidRegions,
                                 const InvalidRegionMap &InvalidRegions) const {
  DEBUG(dbgs() << "*\t Verify RS \n");
  
  typedef RegionSet::const_iterator RSci;
  RSci ValidBegin = ValidRegions.begin();
  RSci ValidEnd   = ValidRegions.end();
  RSci SpeculativeValidBegin = SpeculativeValidRegions.begin();
  RSci SpeculativeValidEnd   = SpeculativeValidRegions.end();
  InvalidRegionMap::const_iterator InvalidBegin = InvalidRegions.begin();
  InvalidRegionMap::const_iterator InvalidEnd   = InvalidRegions.end();

  while (ValidBegin != ValidEnd) {
    assert(!SpeculativeValidRegions.count(*ValidBegin) 
           && "Valid region declared as speculative valid");
    ValidBegin++;
  }
  
  while (SpeculativeValidBegin != SpeculativeValidEnd) {
    assert(SpeculativeValidRegions.count(*SpeculativeValidBegin) 
      && "Speculative Valid region not contained in SpeculativeValidRegions");
    SpeculativeValidBegin++;
  }
  
  while (InvalidBegin != InvalidEnd) {
    assert(!SpeculativeValidRegions.count(InvalidBegin->first) 
           && "Invalid region declared as speculative valid");
    InvalidBegin++;
  }

}


int64_t RegionSpeculation::getScore(RegionMapKey &RMK) {
  assert(SpeculativeValidRegions.count(RMK) && "RMK was not found");

  SPollyInfo *SPI = SpeculativeValidRegions[RMK];
  return getScore(SPI);
}

int64_t RegionSpeculation::getScore(SPollyInfo *SPI) {
  return SPI->getScore();
}

bool RegionSpeculation::checksAreSound(RegionMapKey &RMK) {
  assert(SpeculativeValidRegions.count(RMK) && "RMK was not found");

  SPollyInfo *SPI = SpeculativeValidRegions[RMK];
  return checksAreSound(SPI);
}

bool RegionSpeculation::checksAreSound(SPollyInfo *SPI) {
  // TODO Only Aliasing instructions will be checked at the moment
  return SPI->getChecksAreSound();
}

Function *RegionSpeculation::getOriginalVersion(RegionMapKey &RMK) {
  assert(SpeculativeValidRegions.count(RMK) && "RMK was not found");

  SPollyInfo *SPI = SpeculativeValidRegions[RMK];
  return getOriginalVersion(SPI);
}

Function *RegionSpeculation::getProfilingVersion(RegionMapKey &RMK) {
  assert(SpeculativeValidRegions.count(RMK) && "RMK was not found");

  SPollyInfo *SPI = SpeculativeValidRegions[RMK];
  return getProfilingVersion(SPI);
}

Function *RegionSpeculation::getParallelVersion(RegionMapKey &RMK, Module *dstModule, bool useOriginal) {
  assert(SpeculativeValidRegions.count(RMK) && "RMK was not found");

  SPollyInfo *SPI = SpeculativeValidRegions[RMK];
  return getParallelVersion(SPI, dstModule, useOriginal);
}
  
Function *RegionSpeculation::getOriginalVersion(SPollyInfo *SPI) {
  return SPI->getOriginalVersion();
}

Function *RegionSpeculation::getProfilingVersion(SPollyInfo *SPI) {
  return SPI->getProfilingVersion();
}

Function *RegionSpeculation::getParallelVersion(SPollyInfo *SPI, Module *dstModule, bool useOriginal) {
  return SPI->getParallelVersion(dstModule, useOriginal);
}

std::string RegionSpeculation::getNameStr(RegionMapKey &RMK) {
  assert(SpeculativeValidRegions.count(RMK) && "RMK was not found");

  SPollyInfo *SPI = SpeculativeValidRegions[RMK];
  return getNameStr(SPI);
}

std::string RegionSpeculation::getNameStr(SPollyInfo *SPI) {
  std::string name = SPI->getNameStr();
  return name + " in " + SPI->getOriginalVersion()->getNameStr();
}

void RegionSpeculation::removeRegion(RegionMapKey &RMK) {
  assert(SpeculativeValidRegions.count(RMK) && "RMK was not found");
  
  SPollyInfo *SPI = SpeculativeValidRegions[RMK];
  SpeculativeValidRegions.erase(RMK);

  delete SPI;
}

void RegionSpeculation::registerLoopCount(const Loop *loop) {
  assert(TemporaryRegion && "No TemporaryRegion");
  TemporaryRegion->registerLoopCount(loop);
}

void RegionSpeculation::releaseMemory() {
  DEBUG(dbgs() << "Release Memory RS\n");
  for (iterator it = begin(), e = end(); it != e; it++) {
    delete (it->second);
  } 
  SpeculativeValidRegions.clear();
}


void RegionSpeculation::print() {
  for (iterator it = begin(), e = end(); it != e; it++) {
    (it->second)->print(dbgs());
  }
}


StatisticPrinter::StatisticPrinter() : FunctionPass(ID) {
}

bool StatisticPrinter::doInitialization(Module &M) {
    return false;
}

bool StatisticPrinter::runOnFunction(Function &F) {
    return false;
}

bool StatisticPrinter::doFinalization(Module &M) {
    PrintStatistics();
    std::string error;
    dbgs() << "\n\n Write Module to " << (M.getModuleIdentifier() +".ll").c_str() << "\n\n";
    raw_fd_ostream file ((M.getModuleIdentifier() +".ll").c_str(), error, 0);
    dbgs() << "\t Error: " << error << "\n";
    M.print(file, 0);
    file.close();
    assert(error.empty());
    assert(!llvm::verifyModule(M, PrintMessageAction));
    return false;
}


void StatisticPrinter::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
}

Pass *createStatisticPrinterPass();

char StatisticPrinter::ID = 0;
INITIALIZE_PASS_BEGIN(StatisticPrinter, "stats2",
                      "print statistics earlier", false,
                      false)
INITIALIZE_PASS_END(StatisticPrinter, "stats2",
                    "print statistics earlier", false, false)


Pass *polly::createStatisticPrinterPass() {
  return new StatisticPrinter();
}

static RegisterPass<StatisticPrinter> X("stats2", "print statistics earlier", false, false);
