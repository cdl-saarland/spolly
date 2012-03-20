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

#include "sambamba/Profiler/Profiler.h"
#include "sambamba/Profiler/SCEVHelper.h"

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

#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/Twine.h"
#include "llvm/ADT/SmallPtrSet.h"

#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/RegionIterator.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h" 

#define DEBUG_TYPE "region-speculation"
#include "llvm/Support/Debug.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/CommandLine.h"

#include <iostream>
#include <fstream>
#include <string>
#include <list>

#define RegionMapKeyForRegion(R) std::make_pair(R->getEntry(), R->getExit())
#define FunctionForRegion(R) (R->getEntry()->getParent())
#define ModuleForFunction(F) (F->getParent())

using namespace llvm;
using namespace polly;

namespace {


} // end anonymus namespace



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
  DEBUG(dbgs() << "@\t InsertInvariantChecks " << containsCalls << "\n");
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

    DEBUG(dbgs() << "@\t\t INVARIANT load " << (*loads)->getName() << " " 
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

  DEBUG(dbgs() << "@\t ITB: " << ITB->getName() << "\n"); 
   
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
      DEBUG(dbgs() << "@\t Inserting float invariant compare \n");
      cmp = builder.CreateFCmpOEQ(load, ltps,
                                  ltpf->getName() + "_cmp");
    } else if (type->isIntegerTy()) {
      DEBUG(dbgs() << "@\t Inserting integer invariant compare \n");
      cmp = builder.CreateICmpEQ(load, ltps,
                                 ltpf->getName() + "_cmp");
      
    } else if (type->isPointerTy()) {
      DEBUG(dbgs() << "@\t Inserting integer to pointer \n");
      Value *loadAsInt = builder.CreatePtrToInt(load, t64,
                                                ltpf->getName() +"_64");
      DEBUG(dbgs() << "@\t Inserting integer to pointer \n");
      Value *tmpAsInt  = builder.CreatePtrToInt(ltps, t64,
                                                ltps->getName() +"_64");
      DEBUG(dbgs() << "@\t Inserting integer (pointer) invariant compare \n");
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
  
  DEBUG(dbgs() << "@\t\t" << *I->getType() << "\t" << I->getNumOperands() << "\n");
  
  unsigned argsC = I->getNumOperands();
  std::vector<Type *> argsT(argsC);
  std::vector<Value *> argsV(argsC);

  unsigned i = 0;
  if (I->getOpcode() == Instruction::Call) {
    CallInst *C = dyn_cast<CallInst>(I);
    DEBUG(dbgs() 
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
    DEBUG(dbgs() << "@###$### Set access statement for " << *(it->first)
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

  DEBUG(dbgs() << "@\t Replace violating instructions "
               << violatingInstructions.size()  << "\n");
  std::set<Instruction*>::iterator vIit;

  CallInst *callInst;
  
  // foreach violating instruction
  for (vIit = violatingInstructions.begin(); vIit != violatingInstructions.end();
       vIit++) {
    // create the corresponding call instruction and add it to
    // the replacementInstructions list
    DEBUG(dbgs() << "@\t\t replace " << ((*vIit)) << "\n");
    DEBUG(dbgs() << "@\t\t replace " << (*(*vIit)) << "\n");
  
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

    DEBUG(dbgs() << "@\t\t with " << (*callInst) << "\n");
    
    
    violatingInstructionsMap[callInst] = (*vIit)->getOpcode();
    
    (*vIit)->replaceAllUsesWith(callInst);
    (*vIit)->eraseFromParent(); 
    
    DEBUG(dbgs() << "@$$$\t "<< callInst << " " << callInst->getParent()  << "\n"); 
    DEBUG(dbgs() << "@$$$\t "<< *callInst << " " << *callInst->getParent() << "\n"); 
    
  
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
  (dbgs() << "\n@@@@# postPrepareRegion " << region << "  "
        << " TB: "  << testBlock << "  "<< testBlock->getName() 
        << " " << aliasingValues.size() << "  \n");

  insertChecks(testBlock, 0, region->getEntry());

  IRBuilder<> builder(testBlock->getContext());
  (dbgs() << "@$$$\n@$$$\n@$$$\n");


  (dbgs() << "@\t Replace dummy instructions with original ones: \n"); 
  // Replace the dummy call instructions with the violating ones again
  std::map<Instruction*, unsigned>::iterator it;

  if (violatingInstructionsMap.size() == 0) 
    return;

  for (it = violatingInstructionsMap.begin(); it != violatingInstructionsMap.end(); 
       it++) {
    (dbgs() << "@$$$\t "<< it->first << " " << it->first->getParent() << "  with  " 
          << it->second << "\n"); 
    (dbgs() << "@$$$\t "<< *it->first << "\n"); 
    
    Instruction *original;
    CallInst *I = dyn_cast<CallInst>(it->first);
    builder.SetInsertPoint(it->first->getParent(), it->first);

    // Use the original opcode to determine what kind of instruction should be
    // created
    switch (it->second) {
      default:
        (dbgs()  << "@\t OpCode: " << it->second << "\n");
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
        (dbgs() << "@\t Instruction call " << argsC << "\n");
        std::vector<Value *> argsV(argsC - 1);
        for (unsigned i = 0; i < argsC - 1; i++) {
          argsV[i] = I->getOperand(i);
        }
        ArrayRef<Value*> Args(argsV);
        original = builder.CreateCall(I->getOperand(argsC - 1), Args);
        break;

    }

    // Replace the dummy with the orinigal instruction
    
    (dbgs() << "@\t\t Replace " << *I << " by " );
    I->replaceAllUsesWith(original);
    original->takeName(I);
    (dbgs() << *original <<"\n");
    
    accessStatements[I] = original;
  }
  
  (dbgs() << "@$$$\n@$$$\n@$$$\n");
  (dbgs() << "\n@@@@# postPreparedRegion " << region << "  \n");

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

  void profileValueIfAny(BasicBlock *entry, const SCEV *scev, 
                     //sambamba::sambamba::Profiler *profiler,
                     DenseMap<const SCEVUnknown *, BasicBlock *> &LHM) {
    dbgs() << " === profileValue " << *scev << "\n\n";

    if (const SCEVUnknown *tripCountUnknown = dyn_cast<SCEVUnknown>(scev)) {
      Value *tripCountValue = tripCountUnknown->getValue();

      SmallVectorImpl<BasicBlock *> preds(2);
      for (pred_iterator it = pred_begin(entry), end = pred_end(entry);
           it != end; it++) {
        preds.push_back(*it);
      }

      //profiler->profileValue(tripCountValue, preds);

      // Fill the LoopHeaderMap
      LHM.insert(std::make_pair(tripCountUnknown, entry));
 
      return;
    }

    // Handle non constant trip counts e.g.,   for (i = 0; i < n; i++)
    if (const SCEVNAryExpr *NAry = dyn_cast<SCEVNAryExpr>(scev)) {
      for (unsigned u = 0; u < NAry->getNumOperands(); u++) {
          profileValueIfAny(entry, NAry->getOperand(u), LHM);
      }
    }
    
  }


  /// @brief Cast all subexpressions to int64
  const SCEV *toInt64(const SCEV *scev, ScalarEvolution *SE,
                      IntegerType *Int64Ty) {
    Type *type = scev->getType();
    if (type->isIntegerTy(64)) return scev;
    
    switch (scev->getSCEVType()) {

      case scTruncate:
      case scZeroExtend:
      case scSignExtend: 
      case scUnknown:
      case scConstant: {
        return SE->getSignExtendExpr(scev, Int64Ty);
      } 

      case scAddRecExpr: {
        assert(0 && "SCEVAddRecExpr in score");
      }

      // TODO add add mul ... operastos
      //case scAddExpr:
      //case scMulExpr: {
        //const SCEVNAryExpr *NAryExpr = dyn_cast<SCEVNAryExpr>(scev)
        //SCEVNAryExpr::iterator it = NAryExpr->begin(), end = NAryExpr->end();
      
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
  
  class ScoreSCEVEvaluator {

    ScoreSCEVEvaluator() {

    }

    int evaluateScoreSCEV(ScalarEvolution *SE) {
      
      return 0;
    }

  };

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

    const std::string nameStr;

    ValueToValueMapTy *profilingValueMap, *parallelValueMap;

    Function *originalVersion, *profilingVersion, *parallelVersion;

    /// @brief Information ...
    bool containsCalls, isValid, checksAreSound;
    
    BasicBlock *aliasTestBlock, *invariantTestBlock;
    Value *aliasTestValue, *invariantTestValue;

    /// @brief todo
    RegionSpeculation *RS; 

    /// @brief The scoreSCEV represents the score of the region
    const SCEV *ScoreSCEV;
    unsigned branchDepth;
  
    struct ProfiledBranch {
      sambamba::Profiler::KeyT key;
      BasicBlock *guard;
      unsigned offset;
      ProfiledBranch(BasicBlock *guard, unsigned offset) :
        guard(guard), offset(offset) {}
    };
    typedef DenseMap<GlobalValue *, ProfiledBranch *> BranchProfilingValuesT;
    BranchProfilingValuesT BranchProfilingValues;

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
    std::vector<BasicBlock*> entryPreds;

    public:
      /// @brief Default Constructor
      SPollyInfo(CRegionT R, RegionSpeculation *RS) : 
        RMK(RegionMapKeyForRegion(R)), R(R), nameStr(R->getNameStr()),
        RS(RS) {
        containsCalls = false;
        isValid = true;
        aliasTestBlock = 0;
        aliasTestValue = 0;
        invariantTestBlock = 0;
        invariantTestValue = 0;   
        parallelVersion  = 0;
        profilingVersion = 0;
        originalVersion  = RMK.first->getParent();
        branchDepth = 0;
        parallelValueMap  = 0;
        profilingValueMap = 0;
        NumberOfAliasGroups = 0;
        checksAreSound = true;
      }

      /// @brief Free all allocated objects
      ~SPollyInfo() {
        
        if (aliasTestBlock) {
          dbgs() << "Remove aliasTestBlock\n"; 
          delete aliasTestBlock;
        }
       
        if (profilingValueMap) {
          dbgs() << "Remove profilingValueMap\n";
          delete profilingValueMap;
          dbgs() << "Remove profilingVersion\n";
          profilingVersion->eraseFromParent();
        }

        if (parallelValueMap) {
          dbgs() << "Remove parallelValueMap\n";
          delete parallelValueMap;
          dbgs() << "Remove parallelVersion\n";
          parallelVersion->eraseFromParent();
        }

        if (NumberOfAliasGroups) {
          for (unsigned u = 0; u < NumberOfAliasGroups; u++) {
            dbgs() << "Remove AliasGroup[" << u << "]\n";
            delete AliasGroups[u];
          }
          dbgs() << "Remove AliasGroups\n";
          delete[] AliasGroups;
        }
    
        // Delete allocated GlobalVariables for ProfiledBranch
        for (BranchProfilingValuesT::iterator it = BranchProfilingValues.begin(),
             end = BranchProfilingValues.end(); it != end; it++) {
          delete (it->second);
          delete (it->first);
        }

      }


      inline Function *getOriginalVersion() const {
        return originalVersion;
      }

      Function *getProfilingVersion(sambamba::Profiler *profiler) {
        if (!profilingVersion) {
          profilingValueMap = new ValueToValueMapTy();
          profilingVersion  = CloneFunction(originalVersion,
                                            *profilingValueMap,
                                            // TODO What value is appropriate
                                            /* moduleLevelChanges */ true,
                                            /* ClonedCodeInfo* */ 0);
          insertProfilingCode();
        }
        return profilingVersion;
      } 

      Function *getParallelVersion(Module *dstModule) {
        if (!parallelVersion) {
          parallelValueMap = new ValueToValueMapTy();
          parallelVersion  = CloneFunction(originalVersion, 
                                          *parallelValueMap,
                                          // TODO What value is appropriate
                                          /* moduleLevelChanges */ true,
                                          /* ClonedCodeInfo* */ 0);
          dstModule->getFunctionList().push_back(parallelVersion);
          insertParallelCode();
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
        return containsAliasingInstructions() || containsInvariantInstructions();
      }
      inline bool containsInvariantInstructions() const {
        //return NumberOfInvariantInsructions > 0;
        return false;
      }
      inline bool containsAliasingInstructions() const {
        return NumberOfAliasGroups > 0;
      }
      //@}
      
      /// @brief 
      void insertInvariantTestingCode() {
      
      }

      /// @brief Set the alias test block
      void insertAliasTestingCode(BasicBlock *BB, ValueToValueMapTy &VMap) {
        assert(BB && aliasTestBlock && "Bad alias test block");

        (dbgs() << "\n\n\n#################################################\n");
        aliasTestBlock->dump();
        (dbgs() << "KKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKK\n");
        for (BasicBlock::iterator i = aliasTestBlock->begin(), e = aliasTestBlock->end();
             i != e; i++) {
          dbgs() << " i: " << *i << "  " << i << " " << i->getParent() << "\n";

          for (User::op_iterator op = i->op_begin(), E = i->op_end(); op != E; ++op) {
            dbgs() << "\t=="  << *op << "  " << **op << "  ";
            if (Instruction *Q = dyn_cast<Instruction>(*op)) 
              dbgs() << "Parent: " << Q->getParent() << "\n";
            else
              dbgs() << "\n";
          }

        }
        (dbgs() << "#################################################\n");

        ValueToValueMapTy::iterator VMapit, VMapend = VMap.end();

        Instruction *I = BB->getTerminator(), *tmp;
        BasicBlock::iterator it = aliasTestBlock->begin(),
                            end = aliasTestBlock->end();

        for (; it != end; it++) {
          //dbgs() << "\nit: " << it << "  " << *it << "\n";
         
          for (unsigned u = 0, e = it->getNumOperands(); u != e; u++) {
            VMapit = VMap.find(it->getOperand(u));
            if (VMapit != VMapend)
              it->setOperand(u, (*VMapit).second);
          } 

          //for (User::op_iterator op = it->op_begin(), E = it->op_end(); op != E; ++op) {
            //dbgs() << "iiiiii    "  << *op << "  " << **op << "\n";
            //dbgs() << "pppppp    "  << parallelValueMap->lookup(*op) << "   " << "\n";
          //}

          //tmp = it++;
          //tmp->removeFromParent();
          tmp = it->clone(); tmp->setName(it->getName());
          dbgs() << "\t map " << *it << "(" << it << ")  to: " << *tmp <<  "(" << tmp << ")\n";
          tmp->insertBefore(I);
          VMap[it] = tmp;
        }

        (dbgs() << "\n\n\nYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYY\n");
        BB->dump();
        (dbgs() << "UUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUU\n");
        for (BasicBlock::iterator i = BB->begin(), e = BB->end();
             i != e; i++) {
          dbgs() << " i: " << *i << "  " << i << " " << i->getParent() << "\n";

          for (User::op_iterator op = i->op_begin(), E = i->op_end(); op != E; ++op) {
            dbgs() << "\t=="  << *op << "  " << **op << "  ";
            if (Instruction *Q = dyn_cast<Instruction>(*op)) 
              dbgs() << "Parent: " << Q->getParent() << "\n";
            else
              dbgs() << "\n";
          
          }
        }
        (dbgs() << "UUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUU\n");


      }

      /// @brief 
      void createAliasTestingCode() {
        if (!containsAliasingInstructions()) return;

        assert(!aliasTestBlock && "AliasTestBlock created twice");
        aliasTestBlock = BasicBlock::Create(
                            ModuleForFunction(originalVersion)->getContext(),
                            "AliasTestBlock");

        IRBuilder<> aliasTestBlockBuilder(aliasTestBlock);
        aliasTestValue = createAliasChecks(aliasTestBlockBuilder);
        assert(aliasTestValue && "No Value to check for branch");

        // TODO SAVE THE ALIAS TEST INSTRUCTIONS IN A NEW FUNCTION
      }


#if 0
      /// @brief TODO
      void removeProfilingCode(BasicBlock *testBlock) {
        
        BranchInst *testBlockTerm =
          dyn_cast<BranchInst>(testBlock->getTerminator());
        assert(testBlockTerm && testBlockTerm->isConditional() 
               && "Unexpected testBlock");
        
        BasicBlock *prevBlock = testBlock->getUniquePredecessor();
        assert(prevBlock && "No prevBlock found"); 

        BranchInst *prevBlockTerm =
          dyn_cast<BranchInst>(prevBlock->getTerminator());
        assert(prevBlockTerm && prevBlockTerm->isUnconditional() 
               && "Unexpected prevBlock");

        BasicBlock *profilingBlock = testBlockTerm->getSuccessor(1);
        BasicBlock *nextBlock = testBlockTerm->getSuccessor(0);

        BasicBlock::iterator InstIt  = nextBlock->begin(),
                             InstEnd = nextBlock->end();

        while (InstIt != InstEnd) {
          PHINode *Phi = dyn_cast<PHINode>(InstIt);
          if (!Phi) break;

          Phi->removeIncomingValue(profilingBlock);
          Phi->setIncomingBlock(Phi->getBasicBlockIndex(testBlock), prevBlock);
          InstIt++;
        }

        // The new testblock terminator
        BranchInst::Create(nextBlock, prevBlock); 
        prevBlockTerm->eraseFromParent(); 
        testBlock->eraseFromParent();
        profilingBlock->eraseFromParent();

      }

      /// @brief
      void removeProfilingCode() {
        if (invariantTestBlock) {
          removeProfilingCode(invariantTestBlock); 
          invariantTestBlock = 0;
        }

        if (aliasTestBlock) {
          removeProfilingCode(aliasTestBlock);
          aliasTestBlock = 0;
        }
      }
#endif 


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
        RS->DT->addNewBlock(profilingBlock, testBlock);
        IRBuilder<> testBlockBuilder(testBlock, --(testBlock->end()));
        //RS->SCEVsambamba::Profiler->insertIncrement((const void *)this,
                                                         //testBlockBuilder, 0);
        IRBuilder<> profilingBlockBuilder(profilingBlock);
        //RS->SCEVsambamba::Profiler->insertIncrement((const void *)this,
                                                    //profilingBlockBuilder, 1);

        BasicBlock *nextBlock = testBlockTerm->getSuccessor(0);
        profilingBlockBuilder.CreateBr(nextBlock);

        BranchInst::Create(nextBlock, profilingBlock, testValue, testBlock);
        testBlockTerm->eraseFromParent();
        
        BasicBlock::iterator InstIt  = nextBlock->begin(),
                             InstEnd = nextBlock->end();
        while (InstIt != InstEnd) {
          PHINode *Phi = dyn_cast<PHINode>(InstIt);
          if (!Phi) break;

          Value *val = Phi->getIncomingValueForBlock(testBlock);
          Phi->addIncoming(val, profilingBlock);
          InstIt++;
        }

      }
      

      /// @brief Create and use a profiling version  
      void insertProfilingCode() {
        //assert(!profilingVersion && "Profiling version already created");
        //assert(profilingValueMap && "ValueToValueMap was not found");

        //if (containsAliasingInstructions() && !aliasTestBlock)
          //insertAliasTestingCode();
        //if (containsInvariantInstructions() && !invariantTestBlock)
          //insertInvariantTestingCode();

        //if (aliasTestBlock && aliasTestValue) {
          //insertProfilingCode(aliasTestBlock, aliasTestValue);
        //} // end insert alias profiling code
        
        //if (invariantTestBlock && invariantTestValue) {
          //insertProfilingCode(invariantTestBlock, invariantTestValue);
        //} // end insert invariant profiling code
        
        // TODO score needs profiling
      }
      

      /// @brief Use Polly to insert parallel code
      void insertParallelCode() {
        assert(parallelValueMap && "ValueToValueMap was not found");

        (dbgs() << "Insert Parallel Code for " << getNameStr() << "\n");
        
        EnablePollyVector = EnablePollyOpenMP = true;

        // 
        SpeculativeRegionNameStr = getNameStr();
        FunctionPassManager fpm(parallelVersion->getParent());
        fpm.add(new TargetData(parallelVersion->getParent()));
        fpm.add(new CodeGeneration());
        fpm.run(*parallelVersion);
        
        // If aliastests are available insert or rewire them
        if (containsAliasingInstructions()) {
          BasicBlock *entry, *enterScopBlock = 0;
          entry = dyn_cast<BasicBlock>(parallelValueMap->lookup(RMK.first));
          assert(entry && "Entry in parallel version was not found");

          for (pred_iterator it = pred_begin(entry), end = pred_end(entry);
               it != end; it++) {
              if ((*it)->getName().startswith("polly.enterScop")) {
                enterScopBlock = *it;
                break;
              }
          }

          assert(enterScopBlock && "Did not found polly split block");
        
          insertAliasTestingCode(enterScopBlock, *parallelValueMap);
          dbgs() << "adsoijdsaoisajdoidsajoidsajdsoijdsoijsaoidsjidsajdsoij\n";

          // Use the aliasTestValue to jump to the sequential 
          // or parallel version
          BranchInst *bI = dyn_cast<BranchInst>(enterScopBlock->getTerminator());
          assert (bI && (bI->getNumSuccessors() == 2) && "Bad spolly split block");

          bI->setCondition(parallelValueMap->lookup(aliasTestValue));

        }
        
      }


      /// @brief
      inline bool isViolatingCallInstruction(const CallInst *CI) {
        // TODO 
        return false;
      }

      /// @brief TODO
      inline int getInitialScore() {
        // TODO evaluate ScoreSCEV
        return 0;
      }

      /// @brief Iterators for the internal containers
      //@{
        MemoryAccess MA_begin() { return MemoryAccesses.begin(); }
        MemoryAccess MA_end() { return MemoryAccesses.end(); }
        ViolatingInstruction VI_begin() { return ViolatingInstructions.begin();}
        ViolatingInstruction VI_end() { return ViolatingInstructions.end(); }
      //@}
     

      /// @brief Register a memory access for this region
      void inline registerMemoryAccess(const Instruction * const I,
                                       const SCEV * const scev,
                                       const Value * const V) {

        assert(I && scev && R->contains(I) && "Bad memory access");

        if (const SCEVAddRecExpr *SCEVAddRec = dyn_cast<SCEVAddRecExpr>(scev)) {
          IntegerType *IntTy64 = Type::getInt64Ty(I->getContext());
          const SCEV *start = toInt64(SCEVAddRec->getStart(), RS->SE, IntTy64);
          const SCEV *recur = 
            toInt64(SCEVAddRec->getStepRecurrence(*RS->SE), RS->SE, IntTy64);
          const SCEV *tripC = 
            toInt64(RS->SE->getBackedgeTakenCount(SCEVAddRec->getLoop()),
                    RS->SE, IntTy64);
          const SCEV *tripR = RS->SE->getMulExpr(recur, tripC);
          const SCEV *tripB = RS->SE->getAddExpr(tripR, start);

          MemoryAccesses[V].insert(std::make_pair(I, tripB));
        } else {
          MemoryAccesses[V].insert(std::make_pair(I, scev));
        }
      }
      
      /// @brief Register a violating instruction for this region
      void inline registerViolatingInstruction(const Instruction * const I,
                                               const Violation V) {
        
        assert(I && R->contains(I) && "Bad violating instruction");
        ViolatingInstructions.insert(std::make_pair(I, V));

        if (V != RegionSpeculation::Alias) {
          // TODO At the moment only alias checks are considered as sound checks
          checksAreSound = false;

          if (V == RegionSpeculation::FunctionCall) 
            containsCalls = true;
        }
      }
    

#if 0
      /// @brief A map to keep track of already computed SCEVs 
      typedef DenseMap<const SCEV *, Value *> SCEVToValueMapT;
      SCEVToValueMapT SCEVToValueMap;

      /// @brief Create LLVM-IR instructions to compute the given SCEV
      Value *sambamba::SCEVToValue(IRBuilder<> &builder, const SCEV *scev) {

        // First try to reuse an already created Value
        SCEVToValueMapT::iterator i = SCEVToValueMap.find(scev);
        if (i != SCEVToValueMap.end()) 
          return i->second;
        
        Value *V, *LHS, *RHS, *cmp, *sel;
        SCEVNAryExpr::op_iterator it, end;

        switch (scev->getSCEVType()) {
          case scConstant: {
            const SCEVConstant *Constant = cast<SCEVConstant>(scev);
            V = toInt64Ty(builder, Constant->getValue());
            SCEVToValueMap[scev] = V;
            return V;
          }

          case scUnknown: {
            const SCEVUnknown *Unknown = cast<SCEVUnknown>(scev);
            Type *type;
            if (Unknown->isSizeOf(type)) {
              V = builder.getInt64(RS->TD->getTypeStoreSize(type));
              SCEVToValueMap[scev] = V;
              return V; 
            } 
            
            V = toInt64Ty(builder, Unknown->getValue());
            SCEVToValueMap[scev] = V;
            return V; 
          }

          case scTruncate:
          case scZeroExtend:
          case scSignExtend: {
            const SCEVCastExpr *Cast = cast<SCEVCastExpr>(scev);
            V = sambamba::SCEVToValue(builder, Cast->getOperand());
            assert(V && V->getType()->isIntegerTy(64) && "SCEVToValue failed");
            SCEVToValueMap[scev] = V;
            return V; 
          }
         
          case scAddRecExpr: {
            const SCEVAddRecExpr *AddRecExpr = cast<SCEVAddRecExpr>(scev);
            assert(AddRecExpr->getNumOperands() == 2 
                   && "Found add rev expr with more than two operands");

            const SCEV *stepSCEV = AddRecExpr->getStepRecurrence(*(RS->SE));
            const Loop *loop = AddRecExpr->getLoop();
            const SCEV *loopSCEV = RS->SE->getBackedgeTakenCount(loop);
            
            if (const SCEVSMaxExpr *smax = dyn_cast<SCEVSMaxExpr>(loopSCEV)) {
              const SCEV *opr0 = smax->getOperand(0);
              const SCEV *opr1 = smax->getOperand(1);
              if (opr0->isZero())
                loopSCEV = opr1;
              if (opr1->isZero())
                loopSCEV = opr0;
            }

            Value *step = sambamba::SCEVToValue(builder, stepSCEV);
            assert(step && step->getType()->isIntegerTy(64)
                   && "SCEVToValue failed");

            Value *loopCount = sambamba::SCEVToValue(builder, loopSCEV);
            assert(loopCount && loopCount->getType()->isIntegerTy(64)
                   && "SCEVToValue failed");
            
            Type *ty64 = builder.getInt64Ty();            
            const SCEV *stepSCEV64;
            const SCEV *loopSCEV64; 

            if (stepSCEV->getType()->isIntegerTy(64))
              stepSCEV64 = stepSCEV;
            else
              stepSCEV64 = RS->SE->getSignExtendExpr(stepSCEV, ty64);

            if (loopSCEV->getType()->isIntegerTy(64))
              loopSCEV64 = loopSCEV;
            else
              loopSCEV64 = RS->SE->getSignExtendExpr(loopSCEV, ty64);

            const SCEV *addRecMul = RS->SE->getMulExpr(stepSCEV64, loopSCEV64);
            Value *loopStep;
            dbgs() << "\n\n\n\n\n " << *stepSCEV << "  " << *loopSCEV << " :" 
                   << *loopSCEV->getType() << "\n";
            dbgs() <<  *stepSCEV64 << "  " << *loopSCEV64 << "\n";
            dbgs() << "ADD REC MUL " << addRecMul << "  " << *addRecMul << "\n\n\n";
            if ((i = SCEVToValueMap.find(addRecMul)) != SCEVToValueMap.end()) {
              loopStep = i->second;
            } else {
              loopStep = builder.CreateMul(step, loopCount);
              SCEVToValueMap[addRecMul] = loopStep;
            }

            const SCEV *start = AddRecExpr->getStart();
            if (!(start->isZero())) {
              Value *startVal = sambamba::SCEVToValue(builder, start);
              assert(startVal && startVal->getType()->isIntegerTy(64)
                   && "SCEVToValue failed");
              loopStep = builder.CreateAdd(startVal, loopStep);
            }

            SCEVToValueMap[scev] = loopStep;
            return loopStep;
          } // end scAddRecExpr
          
          case scAddExpr: {
            const SCEVAddExpr *AddExpr = cast<SCEVAddExpr>(scev);
            it  = AddExpr->op_begin(); end = AddExpr->op_end();
            assert(it != end && "Found SCEVAddExpr without operators");

            V = sambamba::SCEVToValue(builder, *(it++));
            assert(V && V->getType()->isIntegerTy(64) && "SCEVToValue failed");

            for (; it != end; it++ ) {
              V = builder.CreateAdd(V, sambamba::SCEVToValue(builder, *it));
            }

            SCEVToValueMap[scev] = V;
            return V;
          } 
            
          case scMulExpr: {
            const SCEVMulExpr *MulExpr = cast<SCEVMulExpr>(scev);
            it  = MulExpr->op_begin(); end = MulExpr->op_end();
            assert(it != end && "Found SCEVMulExpr without operators");

            V = sambamba::SCEVToValue(builder, *(it++));
            assert(V && V->getType()->isIntegerTy(64) && "SCEVToValue failed");

            for (; it != end; it++ ) {
              V = builder.CreateMul(V, sambamba::SCEVToValue(builder, *it));
            }

            SCEVToValueMap[scev] = V;
            return V;
          }

          case scSMaxExpr: {
            const SCEVSMaxExpr *SMaxExpr = cast<SCEVSMaxExpr>(scev);
            assert(SMaxExpr->getNumOperands() == 2 
                   && "Found SMax expr with more than two operands");
            
            const SCEV *opr0 = SMaxExpr->getOperand(0);
            const SCEV *opr1 = SMaxExpr->getOperand(1);
            
            LHS = sambamba::SCEVToValue(builder, opr0);
            RHS = sambamba::SCEVToValue(builder, opr1);
            
            if (opr0->isZero()) return RHS;
            if (opr1->isZero()) return LHS;
          
            assert(LHS && LHS->getType()->isIntegerTy(64) && "SCEVToValue failed");
            assert(RHS && RHS->getType()->isIntegerTy(64) && "SCEVToValue failed");
            
            cmp = builder.CreateICmpSGT(LHS, RHS);
            sel = builder.CreateSelect(cmp, LHS, RHS);

            SCEVToValueMap[scev] = sel;
            return sel;
          }

          case scUMaxExpr: {
            const SCEVUMaxExpr *UMaxExpr = cast<SCEVUMaxExpr>(scev);
            assert(UMaxExpr->getNumOperands() == 2 
                   && "Found UMax expr with more than two operands");
            
            const SCEV *opr0 = UMaxExpr->getOperand(0);
            const SCEV *opr1 = UMaxExpr->getOperand(1);

            LHS = sambamba::SCEVToValue(builder, opr0);
            RHS = sambamba::SCEVToValue(builder, opr1);

            if (opr0->isZero()) return RHS;
            if (opr1->isZero()) return LHS;

            assert(LHS && LHS->getType()->isIntegerTy(64) && "SCEVToValue failed");
            assert(RHS && RHS->getType()->isIntegerTy(64) && "SCEVToValue failed");
            
            cmp = builder.CreateICmpUGT(LHS, RHS);
            sel = builder.CreateSelect(cmp, LHS, RHS);

            SCEVToValueMap[scev] = sel;
            return sel;
          }

          case scUDivExpr: {
            const SCEVUDivExpr *UDivExpr = cast<SCEVUDivExpr>(scev);
            LHS = sambamba::SCEVToValue(builder, UDivExpr->getLHS());
            RHS = sambamba::SCEVToValue(builder, UDivExpr->getRHS());
            assert(LHS && LHS->getType()->isIntegerTy(64) && "SCEVToValue failed");
            assert(RHS && RHS->getType()->isIntegerTy(64) && "SCEVToValue failed");
            
            V = builder.CreateUDiv(LHS, RHS);

            SCEVToValueMap[scev] = V;
            return V;
          } 

          default:
            (dbgs() << "\n\n" << *scev << "\n");
            assert(0 && "Unknown scev type");
        }
      }
#endif

      
      // Use the less equal comparison since we want to discard equal expressions
      #define PRED_LE ICmpInst::ICMP_SLE
      #define PRED_GT ICmpInst::ICMP_SGT
      #define IS_LESS_EQ(s0, s1) RS->SE->isKnownPredicate(PRED_LE, s0, s1)
      #define IS_GREATER(s0, s1) RS->SE->isKnownPredicate(PRED_GT, s0, s1)

      /// @brief Create a pair of minimal and maximal access to this base value
      MinMaxPair createMinMaxAccessPair(IRBuilder<> &builder, Value *baseValue,
                                      sambamba::SCEVToValueMapT &SCEVToValueMap) {
        (dbgs() << "Create MinMax Access Pair for " << *baseValue << " : " 
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
          //SCEV *start = 0, *recurrence = 0, *tripCount = 0;
          //if (SCEVAddRecExpr *SCEVAddRec = dyn_cast<SCEVAddRecExpr>(scev)) {
            //start = SCEVAddRec->getStart();
            //recurrence = SCEVAddRec->getStepRecurrence(RS->SE);
            //tripCount = RS->SE->getBackedgeTakenCount(SCEVAddRec->getLoop());
          //}

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
        
        // The baseValue as scev
        const SCEV *baseSCEV = RS->SE->getSCEV(baseValue);

        // Create LLVM-IR for the collected SCEVs  
        std::deque<Value *> minAccessValues;
        std::deque<Value *> maxAccessValues;
         
        for (mit = minAccesses.begin(), mend = minAccesses.end(); mit != mend;
             mit++) {
          const SCEV *s = RS->SE->getMinusSCEV(baseSCEV, *mit);
          dbgs() << "SCEV2ValueMinAccess: " << s << "   " << *s << " \n";
          minAccessValues.push_back(sambamba::SCEVToValue(builder, s, 
                                                       SCEVToValueMap, RS->SE,
                                                       RS->TD));
          dbgs() << "\t Val: " << minAccessValues.back() << *minAccessValues.back()  << "\n";
        }
        
        for (Mit = maxAccesses.begin(), Mend = maxAccesses.end(); Mit != Mend;
             Mit++) {
          const SCEV *s = RS->SE->getMinusSCEV(baseSCEV, *Mit);
          dbgs() << "SCEV2ValueMaxAccess: " << s << "   " << *s <<  " \n";
          maxAccessValues.push_back(sambamba::SCEVToValue(builder, s,
                                                       SCEVToValueMap, RS->SE,
                                                       RS->TD));
          dbgs() << "\t Val: " << maxAccessValues.back() << *maxAccessValues.back()  << "\n";
        }

        // Compare the created values 
        while (minAccessValues.size() > 1) {
          Value *A = minAccessValues.front(); minAccessValues.pop_front();
          Value *B = minAccessValues.front(); minAccessValues.pop_front();
          assert(A->getType()->isIntegerTy(64) && "Found wrong value type");
          assert(B->getType()->isIntegerTy(64) && "Found wrong value type");
          Value *cmp = builder.CreateICmpSLT(A, B, 
                                         A->getName() + "_LT_" + B->getName());
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
          Value *cmp = builder.CreateICmpSGT(A, B,
                                         A->getName() + "_GT_" + B->getName());
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
        int score = 1;
        
        // TODO Differentiate between the instructions
        if (ViolatingInstructions.count(I)) score = -1;

        if (const CallInst *CI = dyn_cast<CallInst>(I)) {
          if (isViolatingCallInstruction(CI)) {
            if (branchDepth == 0) {
              isValid = false;
            } else {
              score = -10;
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
        SmallVector<const SCEV *, 32> scevs;

        // Handle all subregions and basicBlocks within this region
        Region::const_element_iterator it = R->element_begin(),
                                      end = R->element_end();
        assert(it != end && "Loop body is totaly empty");

        for (; it != end; it++) { 
          if ((*it)->isSubRegion()) {
            const Region *region = (*it)->getNodeAs<Region>();
            scevs.push_back(createSCEVForRegion(region));
          } else {
            const BasicBlock *BB = (*it)->getNodeAs<BasicBlock>();
            scevs.push_back(createSCEVForBasicBlock(BB));
          }
        }

        return RS->SE->getAddExpr(scevs);
      }


      /// @brief Create a SCEV representing the score of a Loop
      /// 
      /// @param R The Region where the Loop is embedded
      ///
      /// @return A SpollyInfo::scoreSCEV 
      const SCEV *createSCEVForLoop(const Region *R) {
        const Loop *loop = RS->LI->getLoopFor(R->getEntry());
        IntegerType *Ty = Type::getInt64Ty(RMK.first->getContext());

        // Use a treshold to score only loops over this treshold
        ConstantInt *tripCountTreshold  = ConstantInt::get(Ty, 10, false);
        const SCEV *tripCount; 
          // Test if there is an loop invariant trip count (+-1 offset) 
        if (RS->SE->hasLoopInvariantBackedgeTakenCount(loop)) {
          // if so, use it 
          tripCount = toInt64(RS->SE->getBackedgeTakenCount(loop), RS->SE, Ty);
        } else {
          // TODO FIXME TODO
        }
        const SCEV *tripCountTresholdSCEV = RS->SE->getConstant(tripCountTreshold);

        const SCEV *loopExp   = RS->SE->getUDivExpr(tripCount, tripCountTresholdSCEV);
        const SCEV *bodyScore = createSCEVForRegionElements(R);
        const SCEV *loopScore = RS->SE->getMulExpr(bodyScore, loopExp);

        return loopScore;
      }

      /// @brief Create a SCEV representing the score of a conditional
      /// 
      /// @param R A Region where the conditional is embedded 
      /// 
      /// @return A SpollyInfo::scoreSCEV 
      const SCEV *createSCEVForConditional(const Region *R) {
        BasicBlock *entry = R->getEntry();
        BasicBlock *exit  = R->getExit();
        
        const SCEV *entryScore = createSCEVForBasicBlock(entry);

        // Enter the conditional
        branchDepth++;

        const TerminatorInst * const guard = entry->getTerminator();
        assert(guard->getNumSuccessors() == 2 
               && "Guard with two successors expected");

        BasicBlock *branch0BB = guard->getSuccessor(0);
        BasicBlock *branch1BB = guard->getSuccessor(1);

        
        GlobalValue *GV0 = new GlobalVariable(entryScore->getType(), 
                                              false,
                                              GlobalValue::ExternalLinkage, 0,
                                              branch0BB->getName() +"_ex_prob");
        GlobalValue *GV1 = new GlobalVariable(entryScore->getType(), 
                                              false,
                                              GlobalValue::ExternalLinkage, 0,
                                              branch1BB->getName() +"_ex_prob");

        BranchProfilingValues[GV0] = new ProfiledBranch(entry, 0);
        BranchProfilingValues[GV1] = new ProfiledBranch(entry, 1);

        const SCEV *prob0 = RS->SE->getSCEV(GV0);
        const SCEV *prob1 = RS->SE->getSCEV(GV1);
        // TODO FIXME profiling support
        
        const SCEV *nextSCEV;
        SmallVector<const SCEV *, 32> branch0Scores;
        SmallVector<const SCEV *, 32> branch1Scores;
        RegionInfo * const RI = R->getRegionInfo();
        const Region *TempRegion;
       
        // Score the first branch
        while (branch0BB != exit) {
          if ((TempRegion = RI->getRegionFor(branch0BB)) == R) {
            // The branch contains only BasicBlocks   
            nextSCEV  = createSCEVForBasicBlock(branch0BB);
            branch0BB = branch0BB->getTerminator()->getSuccessor(0);
          } else {
            // The branch contains another region
            nextSCEV  = createSCEVForRegion(TempRegion);
            branch0BB = TempRegion->getExit();
          }
          branch0Scores.push_back(nextSCEV);
        }

        const SCEV *branch0Score = RS->SE->getAddExpr(branch0Scores);

        // Score the second branch
        while (branch1BB != exit) {
          if ((TempRegion = RI->getRegionFor(branch1BB)) == R) {
            // The branch contains only BasicBlocks   
            nextSCEV  = createSCEVForBasicBlock(branch1BB);
            branch1BB = branch1BB->getTerminator()->getSuccessor(0);
          } else {
            // The branch contains another region
            nextSCEV  = createSCEVForRegion(TempRegion);
            branch1BB = TempRegion->getExit();
          }
          branch1Scores.push_back(nextSCEV);
        }
        
        const SCEV *branch1Score = RS->SE->getAddExpr(branch1Scores);

        const SCEV *branch0ScoreProb = RS->SE->getMulExpr(branch0Score, prob0);
        const SCEV *branch1ScoreProb = RS->SE->getMulExpr(branch1Score, prob1);

        const SCEV *conditionalScore = RS->SE->getAddExpr(entryScore, 
                                                       branch0ScoreProb,
                                                       branch1ScoreProb);

        // Leave the conditional
        branchDepth--;
        dbgs() << *conditionalScore << "\n";
        dbgs() << "dsaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n";
        return conditionalScore;
      }


      /// @brief Create a SCEV representing the score of a Region
      /// 
      /// @param R The Region to score
      /// 
      /// @return A SpollyInfo::scoreSCEV 
      const SCEV *createSCEVForRegion(const Region *R) {
        if (regionIsLoop(R, RS->LI)) {
          return createSCEVForLoop(R);
        } else {
          assert(regionIsConditional(R) 
               && "Found region which is neither a loop nor a conditional");
          return createSCEVForConditional(R);
        }
      }

            
      /// @brief Create an alias check between the given two values
      /// 
      /// @param builder The IRBuilder to create IR-Instructions
      /// @param A The minimal and maximal access for a pointer
      /// @param B The minimal and maximal access for a pointer
      /// 
      /// @return The value computing: (min(A) > max(B) || min(B) > max(A))
      ///
      /// Additionally a new Min/MaxPair is stored in A 
      /// A := (min{min(A), min(B)}, max{max(A), max(B)})
      Value *createAliasCheck(IRBuilder<> &builder,
                              MinMaxPair &A, MinMaxPair &B) {
        Value *minA = A.first, *maxA = A.second;
        Value *minB = B.first, *maxB = B.second;
  
        Value *result0 = builder.CreateICmpSGT(minA, maxB,
                                               minA->getNameStr() + "_gt_" 
                                               + maxB->getNameStr());

        Value *result1 = builder.CreateICmpSGT(minB, maxA,
                                               minB->getNameStr() + "_gt_" 
                                               + maxA->getNameStr());
        
        Value *result  = builder.CreateOr(result0, result1, result0->getNameStr()
                                                            + "_v_" 
                                                            + result1->getNameStr());
         
        Value *minAB = builder.CreateSelect(result0, minB, minA, "minSel");
        Value *maxAB = builder.CreateSelect(result0, maxA, maxB, "maxSel");

        A = std::make_pair(minAB, maxAB);

        return result; 
      }


      /// @brief Create alias checks using the given IRBuilder
      /// 
      /// The return value is a i1 type value which is true if all checks 
      /// are passed, false otherwise
      Value *createAliasChecks(IRBuilder<> &builder) {
         
        (dbgs() << "Create alias checks for " << getNameStr() << "\n");
        assert(containsAliasingInstructions() 
               && "No aliasing instructions to check");

        sambamba::SCEVToValueMapT SCEVToValueMap;

        // The returned result
        std::deque<Value *> results;
        for (unsigned u = 0, e = NumberOfAliasGroups; u != e; u++) {
          AliasGroupT AG = AliasGroups[u];

          std::deque<MinMaxPair> ToCheck; 
          // Fill the ToCheck deque with all inital min/max pairs
          for (std::vector<Value*>::const_iterator it = AG->begin(),
               end = AG->end(); it != end; it++ ) {
            ToCheck.push_back(createMinMaxAccessPair(builder, *it, 
                                                     SCEVToValueMap));
          }

          while (ToCheck.size() > 1) {
            // Get the first two elements
            MinMaxPair A = ToCheck.front(); ToCheck.pop_front(); 
            MinMaxPair B = ToCheck.front(); ToCheck.pop_front(); 
            
            // Create a test for A and B and push them back into the deque
            dbgs() << " =-=-=-= " << *(A.first) << "  " << *(A.second)  << "\n";
            Value *AB = createAliasCheck(builder, A, B);
            dbgs() << " =-=-=-= " << *(A.first) << "  " << *(A.second)  << "\n";
            ToCheck.push_back(A);
            results.push_back(AB);
          }

          assert(ToCheck.size() == 1 && "ToCheck size is invalid");
          // The last MinMaxPair is not needed
          MinMaxPair AB = ToCheck.front();
          Instruction *I;
          if ((I = dyn_cast<Instruction>(AB.first))) {
            I->eraseFromParent(); 
          } else assert(0 && "Last MinMaxPair should contain instructions");
          if ((I = dyn_cast<Instruction>(AB.second))) {
            I->eraseFromParent(); 
          } else assert(0 && "Last MinMaxPair should contain instructions");
        }

        while (results.size() > 1) {            
          // Get the first two elements
          Value *A = results.front(); results.pop_front(); 
          Value *B = results.front(); results.pop_front(); 
          
          Value *AB = builder.CreateAnd(A, B, A->getName() + "_and_" +B->getName()); 
          results.push_back(AB);
          
        }

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

                (dbgs() << "Skipping aliasing Instruction " << *I 
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

        createAliasSets(AST);

        ScoreSCEV = createSCEVForRegion(R); 

        // Collect all predecessors of entry which do not belong to the region
        for (pred_iterator itPred = pred_begin(RMK.first),
             end = pred_end(RMK.first); itPred != end; itPred ++) {
          if ( R->contains(*itPred) ) continue;
            entryPreds.push_back(*itPred);
        }

        if (isValid) {
          // Computations only done if the region is valid
          createAliasTestingCode();
        }

        return isValid;
      }
    
      /// @brief Pretty print all contained information 
      void print(raw_ostream &OS) {
        OS << "\n\nSpollyInfo: " << getNameStr() << " \t In: "
           << originalVersion->getNameStr() << "\n\n";

        OS.indent(4) << " ChecksAreSound: " << checksAreSound << "\n";
        OS.indent(4) << " #MemoryAccesses: " << MemoryAccesses.size() << "\n";

        for (MemoryAccess it = MA_begin(),end = MA_end(); it != end; it++){
          OS.indent(8) << " BaseValue: " << *(it->first) << " accesed at: \n";
          for (MemoryAccessInfo::const_iterator mit = it->second.begin(), 
               mend = it->second.end(); mit != mend; mit++) {
            OS.indent(12) << "-" << *(mit->second) << " by " << *(mit->first) << "\n";
          }
        }

        OS.indent(4) << " ScoreSCEV: " << *ScoreSCEV << "\n\n";
        
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
        
        OS << "\n\nAliasTestBlock: \n";
        aliasTestBlock->print(OS);
        OS << "\n\n";

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
        }


      }
     


  }; // end class SPollyInfo
} // end namespace polly

/// @brief The default constructor
/// 
/// - Create the SPollyInfo ScalarEvolution object
RegionSpeculation::RegionSpeculation() {
  dbgs() << "\n============ Create Region Speculation =============== \n";
  
  TemporaryRegion = 0;

} 

/// @brief
RegionSpeculation::~RegionSpeculation() {
  dbgs() << "\n============ Delete Region Speculation =============== \n";

  for (iterator it = begin(), e = end(); it != e; it++) {
    delete (it->second);
  }
}


/// @brief Register a violating instruction for the current region 
void RegionSpeculation::registerViolatingInstruction(const Instruction* const I,
                                                     Violation V) { 
  assert(TemporaryRegion && "No TemporaryRegion to insert access");

  TemporaryRegion->registerViolatingInstruction(I, V);
}


/// @brief Register a memory access for the current region (TemporaryRegion)
void RegionSpeculation::registerMemoryAccess(const Instruction * const I,
                                             const SCEV * const scev,
                                             const Value * const V) {
  assert(TemporaryRegion && "No TemporaryRegion to insert access");

  TemporaryRegion->registerMemoryAccess(I, scev, V);
}

/// @brief Store the associated SPollyInfo object for the given region
/// 
/// The SPollyInfo object from TemporaryRegion will be added
/// to the SpeculativeValidRegions map.
void RegionSpeculation::storeTemporaryRegion(CRegionT R, AliasSetTracker &AST) {
  (dbgs() << "*\t Store TemporaryRegion " << R->getNameStr() 
          << " in " << FunctionForRegion(R)->getNameStr() << "\n");

  RegionMapKey &RMK = TemporaryRegion->getRMK();

  assert(R == TemporaryRegion->getRegion()
         && "Region does not match TemporaryRegion");
  assert(!SpeculativeValidRegions.count(RMK)
         && "Region is already contained in SpeculativeValidRegions");
 
   
  // Validate the TemporaryRegion and create the scoreSCEV 
  if (!TemporaryRegion->validate(AST)) {
    (dbgs() << "*\t Validation of TemporaryRegion " << R->getNameStr() 
            << " failed.\n");
    TemporaryRegion->print(dbgs());
    
    // Forget the TemporaryRegion instead of storing it
    forgetTemporaryRegion(R);
    return;
  }


  SpeculativeValidRegions[RMK] = TemporaryRegion;
  
  // Print the SPollyInfo object 
  DEBUG(
    TemporaryRegion->print(dbgs());
  );

  TemporaryRegion = 0;
}


/// @brief Delete the associated SPollyInfo object for the given region
void RegionSpeculation::forgetTemporaryRegion(CRegionT R) {
  (dbgs() << "*\t Forget TemporaryRegion " << R->getNameStr()
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
  (dbgs() << "*\t New TemporaryRegion " << R << " " <<   R->getNameStr() 
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
  (dbgs() << "*\t Init ScopDetection run \n");

  // Save the given analyses
  assert(aa && se && li && ri && dt && td && sd && "Analyses are not valid");
  AA = aa; SE = se; LI = li; RI = ri; DT = dt; TD = td; SD = sd;

  // All TemporaryRegions should be saved or deleted 
  assert(!TemporaryRegion
         && "TemporaryRegion was not 0 during initialization");
  
}

/// @brief Finalize the ScopDetection run 
/// 
///  - Forget the given analyses
void RegionSpeculation::finalizeScopDetectionRun() {
  (dbgs() << "*\t Finalyze ScopDetection run \n");
  
  // Forget the given analyses
  AA = 0;  LI = 0; RI = 0; DT = 0; TD = 0; SD = 0;
  // SE = 0;
  
  // All TemporaryRegions should be saved or deleted 
  assert(!TemporaryRegion
         && "TemporaryRegion was not 0 during finalization");
}

  
/// @brief TODO
bool RegionSpeculation::speculateOnRegion(const Region *R) {
  RegionMapKey RMK = RegionMapKeyForRegion(R);
  dbgs() << "qqqqqq" <<  R << " " << R->getEntry() << "  "  
         <<  SpeculativeValidRegions.count(RMK) <<"\n";
  if (SpeculativeValidRegions.count(RMK))
    assert(0); 
  return SpeculativeValidRegions.count(RMK);
  
}

  
/// @brief Verify the communication between ScopDetection and RegionSpeculation 
///
/// This is called after by the veryify function of the ScopDetection pass
/// and should only be used in DEBUG mode
void RegionSpeculation::verifyRS(const RegionSet &ValidRegions, 
                                 const RegionSet &SpeculativeValidRegions,
                                 const InvalidRegionMap &InvalidRegions) const {
  (dbgs() << "*\t Verify RS \n");
  
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


int RegionSpeculation::getScore(RegionMapKey &RMK) {
  assert(SpeculativeValidRegions.count(RMK) && "RMK was not found");

  SPollyInfo *SPI = SpeculativeValidRegions[RMK];
  return getScore(SPI);
}

int RegionSpeculation::getScore(SPollyInfo *SI) {
  // TODO
  return 0;
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

RegionSpeculation::FunctionPair RegionSpeculation::getProfilingVersion(RegionMapKey &RMK,
                                                 sambamba::Profiler *profiler) {
  assert(SpeculativeValidRegions.count(RMK) && "RMK was not found");

  SPollyInfo *SPI = SpeculativeValidRegions[RMK];
  return getProfilingVersion(SPI, profiler);
}

RegionSpeculation::FunctionPair RegionSpeculation::getParallelVersion(RegionMapKey &RMK, Module *dstModule) {
  assert(SpeculativeValidRegions.count(RMK) && "RMK was not found");

  SPollyInfo *SPI = SpeculativeValidRegions[RMK];
  return getParallelVersion(SPI, dstModule);
}
  
Function *RegionSpeculation::getOriginalVersion(SPollyInfo *SPI) {
  return SPI->getOriginalVersion();
}

RegionSpeculation::FunctionPair RegionSpeculation::getProfilingVersion(SPollyInfo *SPI, sambamba::Profiler *profiler) {
  return std::make_pair(SPI->getProfilingVersion(profiler), SPI->getProfilingValueMap());
}

RegionSpeculation::FunctionPair RegionSpeculation::getParallelVersion(SPollyInfo *SPI, Module *dstModule) {
  return std::make_pair(SPI->getParallelVersion(dstModule), SPI->getParallelValueMap());
}


void RegionSpeculation::releaseMemory() {
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
