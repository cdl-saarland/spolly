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

#include "polly/ScopInfo.h"
#include "polly/ScopDetection.h"
#include "polly/LinkAllPasses.h"
#include "polly/Support/ScopHelper.h"
#include "polly/Support/RegionSpeculationHelper.h"
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
#define ModuleForRegion(R) (R->getEntry()->getParent()->getParent())

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
   * ===  FUNCTION  ============================================================
   *         Name:  getFileName 
   *  Description:  
   * ===========================================================================
   */
  static std::string getFileName(Region *R) {
    std::string FunctionName =
      R->getEntry()->getParent()->getName();
    std::string FileName = "spolly_" + FunctionName + ".score";
    return FileName;
  }

}


/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  insertInvariantCheck
 *    Arguments:  
 *      Returns:  
 * =============================================================================
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
 * ===  FUNCTION  ==============================================================
 *         Name:  createCall
 *    Arguments:  
 *      Returns:  
 * =============================================================================
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
 * ===  FUNCTION  ==============================================================
 *         Name:  replaceScopStatements
 *    Arguments:  
 *      Returns:  
 * =============================================================================
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
 * ===  FUNCTION  ==============================================================
 *         Name:  replaceViolatingInstructions
 *    Arguments:  
 *      Returns:  
 * =============================================================================
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
 * ===  FUNCTION  ==============================================================
 *         Name:  postPrepareRegion
 *  Description:  
 * =============================================================================
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

    /// @brief Keep track of the version which is used
    bool parallelized;

    /// @brief Information ...
    bool containsCalls;
    
    BasicBlock *aliasTestBlock, *invariantTestBlock;
    Value *aliasTestValue, *invariantTestValue;

    /// @brief todo
    RegionSpeculation *RS; 

    /// @brief The scoreSCEV represents the score of the region
    const SCEV *ScoreSCEV;
    
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
  
    public:
      /// @brief Default Constructor
      SPollyInfo(CRegionT R, RegionSpeculation *RS) : 
        RMK(RegionMapKeyForRegion(R)), R(R), RS(RS) {
        containsCalls = false;
        parallelized  = false;
        aliasTestBlock = 0;
        aliasTestValue = 0;
        invariantTestBlock = 0;
        invariantTestValue = 0;   
      };
 
      /// @brief The default Destructoru
      ~SPollyInfo() {
      };

      /// @brief 
      const SCEV *getScoreSCEV() { return ScoreSCEV; }

      /// @brief Return the underlying speculative valid region
      CRegionT inline getRegion() const { return R; }
    
      void inline setRegion(CRegionT newR) {
        assert(newR->getEntry() == RMK.first && newR->getExit() == RMK.second);
        R = newR;
      } 

      RegionMapKey inline getRMK() const { return RMK; }

      /// @brief Check if the profiling version is used
      bool isProfiling() { return aliasTestBlock || invariantTestBlock; }


      /// @brief 
      void insertInvariantTestingCode() {
      
      }

      /// @brief
      void removeAliasTestingCode() {
        
      }

      /// @brief Set the alias test block
      void setAliasTestingBlock(BasicBlock *BB) {
        assert(BB && "Bad alias test block");
        aliasTestBlock = BB;
      }

      /// @brief 
      void insertAliasTestingCode() {
        assert(containsAliasingInstructions() && "No tests for aliasing available");
        
        dbgs() << "\n\t" << RS->SCEVProfiler << "\n\n";
        RS->SCEVProfiler->allocateSlots((const void *)this, 2);
        
        BasicBlock *entry = RMK.first;

        // Test if the aliasTestBlock is set, if not a new one is created
        if (!aliasTestBlock) {
          // Collect all predecessors of entry which do not belong to the region
          std::vector<BasicBlock*> entryPreds;
          for (pred_iterator itPred = pred_begin(entry),
               end = pred_end(entry); itPred != end; itPred ++) {
            if ( R->contains(*itPred) ) continue;
            entryPreds.push_back(*itPred);
          }

          // Split the entry block according to the collected predecessors 
          aliasTestBlock = SplitBlockPredecessors(entry, &entryPreds[0], 
                                                  entryPreds.size(),
                                                  "_test",
                                                  RS->SE);
        }

        IRBuilder<> aliasTestBlockBuilder(aliasTestBlock, --(aliasTestBlock->end()));
        aliasTestValue = createAliasChecks(aliasTestBlockBuilder);
        assert(aliasTestValue && "No Value to check for branch");
      }


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
        assert(!parallelized && "bad remove profiling code");
        if (invariantTestBlock) {
          removeProfilingCode(invariantTestBlock); 
          invariantTestBlock = 0;
        }

        if (aliasTestBlock) {
          removeProfilingCode(aliasTestBlock);
          aliasTestBlock = 0;
        }
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
        RS->DT->addNewBlock(profilingBlock, testBlock);
        IRBuilder<> testBlockBuilder(testBlock, --(testBlock->end()));
        RS->SCEVProfiler->insertIncrement((const void *)this,
                                                         testBlockBuilder, 0);
        IRBuilder<> profilingBlockBuilder(profilingBlock);
        RS->SCEVProfiler->insertIncrement((const void *)this,
                                                    profilingBlockBuilder, 1);

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
        if (!RS->hasProfilingSupport()) return;

        assert(!isProfiling() && "Profiling version already in use");
        if (containsAliasingInstructions() && !aliasTestBlock)
          insertAliasTestingCode();
        if (containsInvariantInstructions() && !invariantTestBlock)
          insertInvariantTestingCode();

        assert((aliasTestBlock && aliasTestValue) 
               || (invariantTestBlock && invariantTestValue) 
               && "No tests available");

        if (aliasTestBlock && aliasTestValue) {
          insertProfilingCode(aliasTestBlock, aliasTestValue);
        } // end insert alias profiling code
        
        if (invariantTestBlock && invariantTestValue) {
          insertProfilingCode(invariantTestBlock, invariantTestValue);
        } // end insert invariant profiling code
      }
      

      /// @brief Use Polly to insert parallel code
      void insertParallelCode() {
        assert(!parallelized && "Already parallelized");
        
        (dbgs() << "Insert Parallel Code for " << R->getNameStr() << "\n");
        // Remove invariant profiling code
        if (invariantTestBlock) {
          removeProfilingCode(invariantTestBlock); 
          invariantTestBlock = 0;
        } 
        // TODO TODO Reuse already created aliastests !
        removeProfilingCode();
        
        // After the profiling code is removed we set the parallelized flag
        parallelized = true;
       
        FunctionPassManager fpm(ModuleForRegion(R));
        RS->SD->addValidRegion(R);
        fpm.add(new TargetData(ModuleForRegion(R)));
        fpm.add(new CodeGeneration());
        fpm.run(*FunctionForRegion(R));
        
        // If aliastests are available insert or rewire them
        if (containsAliasingInstructions()) {
          BasicBlock *entry = RMK.first;
          if (!aliasTestBlock) {
            for (pred_iterator it = pred_begin(entry), end = pred_end(entry);
                 it != end; it++) {
                if ((*it)->getName().startswith("polly.enterScop")) {
                  aliasTestBlock = *it;
                  break;
                }
            }

            assert(aliasTestBlock && "Did not found polly split block");
          
            insertAliasTestingCode();

            // Use the aliasTestValue to jump to the sequential 
            // or parallel version
            BranchInst *bI = 
              dyn_cast<BranchInst>(aliasTestBlock->getTerminator());
            assert (bI && (bI->getNumSuccessors() == 2) && "Bad spolly split block");

            bI->setCondition(aliasTestValue);

          } else {
            // TODO REWIRE already inserted tests (see above TODO)
          }
        }
        
      }

      /// @brief Create the ScoreSCEV representing the score of this region
      /// 
      /// The SCEV representing the score is parameterized. 
      /// It is build from information known during compile time and Unknown 
      /// values are added for information only known at runtime. 
      /// These information will be replaced by the @getScore function, thus 
      /// @getScore will create an integer value based on the created ScoreSCEV
      void inline createScoreSCEV(SCEVCreator * const Creator) {
        ScoreSCEV = Creator->createSCEVForRegion(R); 
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
        MemoryAccesses[V].insert(std::make_pair(I, scev));
      }
      
      /// @brief Register a violating instruction for this region
      void inline registerViolatingInstruction(const Instruction * const I,
                                               const Violation V) {
        
        assert(I && R->contains(I) && "Bad violating instruction");
        ViolatingInstructions.insert(std::make_pair(I, V));

        if (V == RegionSpeculation::FunctionCall) 
          containsCalls = true;
      }
    
      /// @brief Return true if profiling tests are available
      bool inline testsAvailable() {
        return containsAliasingInstructions() || containsInvariantInstructions();
      }

      /// @brief Check the region for aliasing instructions
      bool inline containsInvariantInstructions() {
        //return NumberOfInvariantInsructions > 0;
        return false;
      }

      /// @brief Check the region for aliasing instructions
      bool inline containsAliasingInstructions() {
        return NumberOfAliasGroups > 0;
      }
     
      /// @brief Cast V to int64
      Value *toInt64Ty(IRBuilder<> &builder, Value *V) {
        (dbgs() << "toInt64ty " << *V << "\n");
        Type *type = V->getType();
        if (type->isIntegerTy(64)) return V;
        if (type->isPointerTy()) 
          return builder.CreatePtrToInt(V, builder.getInt64Ty());
        return builder.CreateSExt(V, builder.getInt64Ty());
      }

      /// @brief A map to keep track of already computed SCEVs 
      typedef DenseMap<const SCEV *, Value *> SCEVToValueMapT;
      SCEVToValueMapT SCEVToValueMap;

      /// @brief Create LLVM-IR instructions to compute the given SCEV
      Value *SCEVToValue(IRBuilder<> &builder, const SCEV *scev) {

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
            V = SCEVToValue(builder, Cast->getOperand());
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

            Value *step = SCEVToValue(builder, stepSCEV);
            assert(step && step->getType()->isIntegerTy(64)
                   && "SCEVToValue failed");

            Value *loopCount = SCEVToValue(builder, loopSCEV);
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
              Value *startVal = SCEVToValue(builder, start);
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

            V = SCEVToValue(builder, *(it++));
            assert(V && V->getType()->isIntegerTy(64) && "SCEVToValue failed");

            for (; it != end; it++ ) {
              V = builder.CreateAdd(V, SCEVToValue(builder, *it));
            }

            SCEVToValueMap[scev] = V;
            return V;
          } 
            
          case scMulExpr: {
            const SCEVMulExpr *MulExpr = cast<SCEVMulExpr>(scev);
            it  = MulExpr->op_begin(); end = MulExpr->op_end();
            assert(it != end && "Found SCEVMulExpr without operators");

            V = SCEVToValue(builder, *(it++));
            assert(V && V->getType()->isIntegerTy(64) && "SCEVToValue failed");

            for (; it != end; it++ ) {
              V = builder.CreateMul(V, SCEVToValue(builder, *it));
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
            
            LHS = SCEVToValue(builder, opr0);
            RHS = SCEVToValue(builder, opr1);
            
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

            LHS = SCEVToValue(builder, opr0);
            RHS = SCEVToValue(builder, opr1);

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
            LHS = SCEVToValue(builder, UDivExpr->getLHS());
            RHS = SCEVToValue(builder, UDivExpr->getRHS());
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
        
      
      // Use the less equal comparison since we want to discard equal expressions
      #define PRED_LT ICmpInst::ICMP_SLE
      #define PRED_GT ICmpInst::ICMP_SGT
      #define IS_LESS(s0, s1) RS->SE->isKnownPredicate(PRED_LT, s0, s1)
      #define IS_GREATER(s0, s1) RS->SE->isKnownPredicate(PRED_GT, s0, s1)

      /// @brief Create a pair of minimal and maximal access to this base value
      MinMaxPair createMinMaxAccessPair(IRBuilder<> &builder, Value *baseValue) {
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
          const SCEV * scev = it->second;
          (dbgs() << "*\t\t Access SCEV: " << *scev << " : "
                  << *(scev->getType()) << " " 
                  << (scev->getSCEVType()) << " (" 
                  << *(it->first) << ")\n");

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
              if (IS_LESS(*mit, scev)) possibleMin = false;
              if (IS_GREATER(*mit, scev)) mit =
                     minAccesses.erase(mit);
            }
            if (possibleMin) { 
              (dbgs() << "*\t\t\t New possible min: " << *scev << "\n");
              minAccesses.push_back(scev);
            }
          }

          // Test all possible maxima
          if (possibleMax) {
            for (Mit = maxAccesses.begin(), Mend = maxAccesses.end();
                 Mit != Mend; Mit++) {
              if (IS_LESS(scev, *Mit)) possibleMax = false;
              if (IS_GREATER(scev, *Mit)) Mit = 
                     maxAccesses.erase(Mit);
            }
            if (possibleMax) {
              (dbgs() << "*\t\t\t New possible max: " << *scev << "\n");
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
        
        (dbgs() << "SCEV TO VALUE \n\n\n");
        for (mit = minAccesses.begin(), mend = minAccesses.end(); mit != mend;
             mit++) {
          (dbgs() << "mit: " << **mit << "  " << *baseSCEV << " \n");
          const SCEV *s = RS->SE->getAddExpr(*mit, baseSCEV);
          minAccessValues.push_back(SCEVToValue(builder, s));
        }
        
        for (Mit = maxAccesses.begin(), Mend = maxAccesses.end(); Mit != Mend;
             Mit++) {
          (dbgs() << "Mit: " << **Mit << "  " << *baseSCEV << " \n");
          const SCEV *s = RS->SE->getAddExpr(*Mit, baseSCEV);
          maxAccessValues.push_back(SCEVToValue(builder, s));
        }

        // Compare the created values 
        while (minAccessValues.size() > 1) {
          Value *A = minAccessValues.front(); minAccessValues.pop_front();
          Value *B = minAccessValues.front(); minAccessValues.pop_front();
          assert(A->getType()->isIntegerTy(64) && "Found wrong value type");
          assert(B->getType()->isIntegerTy(64) && "Found wrong value type");
          Value *cmp = builder.CreateICmpSLT(A, B);
          Value *sel = builder.CreateSelect(cmp, A, B);
          minAccessValues.push_back(sel);
        }
        
        // Compare the created values 
        while (maxAccessValues.size() > 1) {
          Value *A = maxAccessValues.front(); maxAccessValues.pop_front();
          Value *B = maxAccessValues.front(); maxAccessValues.pop_front();
          assert(A->getType()->isIntegerTy(64) && "Found wrong value type");
          assert(B->getType()->isIntegerTy(64) && "Found wrong value type");
          Value *cmp = builder.CreateICmpSGT(A, B);
          Value *sel = builder.CreateSelect(cmp, A, B);
          maxAccessValues.push_back(sel);
        }

        assert(minAccessValues.size() == 1 
               && "Expected one minimal access value");
        assert(maxAccessValues.size() == 1 
               && "Expected one maximal access value");
        return std::make_pair(minAccessValues.front(), maxAccessValues.front());
        
      }

      
      /// @brief Create an alias check between the given two values
      Value *createAliasCheck(IRBuilder<> &builder,
                              MinMaxPair &A, MinMaxPair &B) {
        //(dbgs() << "Create alias check for " << A << " and " << B << "\n");

        Value *minA = A.first, *maxA = A.second;
        Value *minB = B.first, *maxB = B.second;
  
        Value *result0 = builder.CreateICmpSGT(minA, maxB,
                                               minA->getNameStr() + "_gt_" 
                                               + maxB->getNameStr());
        DEBUG(dbgs() << "*\t\t - result0: " << *result0 << "\n");

        Value *result1 = builder.CreateICmpSGT(minB, maxA,
                                               minB->getNameStr() + "_gt_" 
                                               + maxA->getNameStr());
        DEBUG(dbgs() << "*\t\t - result1: " << *result1 << "\n");
        
        Value *result  = builder.CreateOr(result0, result1, result0->getNameStr()
                                                            + "_v_" 
                                                            + result1->getNameStr());
         
        Value *minAB = builder.CreateSelect(result0, minB, minA);
        Value *maxAB = builder.CreateSelect(result0, maxA, maxB);

        A = std::make_pair(minAB, maxAB);

        return result; 
      }


      /// @brief Create alias checks using the given IRBuilder
      /// 
      /// The return value is a i1 type value which is true if all checks 
      /// are passed, false otherwise
      Value *createAliasChecks(IRBuilder<> &builder) {
        
        (dbgs() << "Create alias checks for " << R->getNameStr() << "\n");
        assert(containsAliasingInstructions() 
               && "No aliasing instructions to check");

        // The returned result
        std::deque<Value *> results;
        for (unsigned u = 0, e = NumberOfAliasGroups; u != e; u++) {
          AliasGroupT AG = AliasGroups[u];

          std::deque<MinMaxPair> ToCheck; 
          // Fill the ToCheck deque with all inital min/max pairs
          for (std::vector<Value*>::const_iterator it = AG->begin(),
               end = AG->end(); it != end; it++ ) {
            ToCheck.push_back(createMinMaxAccessPair(builder, *it));
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
          if ((I = dyn_cast<Instruction>(AB.first)))
            I->eraseFromParent(); 
          if ((I = dyn_cast<Instruction>(AB.second)))
            I->eraseFromParent(); 

        }

        while (results.size() > 1) {            
          // Get the first two elements
          Value *A = results.front(); results.pop_front(); 
          Value *B = results.front(); results.pop_front(); 
          
          Value *AB = builder.CreateAnd(A, B); 
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
      bool validate(SCEVCreator * const Creator, AliasSetTracker &AST) { 

        createAliasSets(AST);

        createScoreSCEV(Creator);

        // No invalid regions at the moment
        return true;
      }
    
      /// @brief Pretty print all contained information 
      void print(raw_ostream &OS) {
        OS << "SpollyInfo:\n";
        OS << " Entry: " << R->getEntry() << "  " 
                     << *( R->getEntry()) << "\n";
        OS << " Exit: " << R->getExit() << "  " 
                     << *( R->getExit()) << "\n\n";

        OS.indent(4) << " #MemoryAccesses: " << MemoryAccesses.size() << "\n";

        for (MemoryAccess it = MA_begin(),end = MA_end(); it != end; it++){
          OS.indent(8) << " BaseValue: " << *(it->first) << " accesed at: \n";
          for (MemoryAccessInfo::const_iterator mit = it->second.begin(), 
               mend = it->second.end(); mit != mend; mit++) {
            OS.indent(12) << *(mit->second) << " by " << *(mit->first) << "\n";
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


      }
     


  }; // end class SPollyInfo
} // end namespace polly

/// @brief The default constructor
/// 
/// - Create the SPollyInfo ScalarEvolution object
RegionSpeculation::RegionSpeculation(sambamba::SCEVProfiler *Profiler) {
  dbgs() << "\n============ Create Region Speculation =============== \n";
  SCEVProfiler = Profiler;
  if (SCEVProfiler)
    SPI_SE = SCEVProfiler->getScalarEvolution();
  
  Creator = 0;
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

  RegionMapKey RMK = RegionMapKeyForRegion(R);

  assert(R == TemporaryRegion->getRegion()
         && "Region does not match TemporaryRegion");
  assert(!SpeculativeValidRegions.count(RMK)
         && "Region is already contained in SpeculativeValidRegions");
 
  // Validate the TemporaryRegion and create the scoreSCEV 
  if (!TemporaryRegion->validate(Creator, AST)) {
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

  RegionMapKey RMK = RegionMapKeyForRegion(R);

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

  assert(!Creator && "SCEVCreator was already initialized");
  if (!SCEVProfiler) {
    dbgs() << "1111111111111111111\n"; 
    Creator = new SCEVCreator(SE, LI, new sambamba::DummySCEVProfiler(SE));
  } else {
    dbgs() << "sssssssssssssssssss\n";
    Creator = new SCEVCreator(SE, LI, SCEVProfiler);
  }

  assert(!SPI_SE || SE == SPI_SE && "ScalarEvolution changed !");
}

/// @brief Finalize the ScopDetection run 
/// 
///  - Forget the given analyses
void RegionSpeculation::finalizeScopDetectionRun() {
  (dbgs() << "*\t Finalyze ScopDetection run \n");
  
  // Forget the given analyses
  AA = 0; SE = 0; LI = 0; RI = 0; DT = 0; TD = 0; SD = 0;
  
  assert(Creator && "SCEVCreator was 0");

  // Delete the DummySCEVProfiler if one was created
  if (!SCEVProfiler)
    delete Creator->getSCEVProfiler();

  delete Creator;
  Creator = 0;

  // All TemporaryRegions should be saved or deleted 
  assert(!TemporaryRegion
         && "TemporaryRegion was not 0 during finalization");
}


/// @brief 
void RegionSpeculation::insertProfilingCode(CRegionT R) {
  RegionMapKey RMK = RegionMapKeyForRegion(R);
  
  assert((SpeculativeValidRegions.count(RMK)) 
         && "Region is not speculative valid");
  SpeculativeValidRegions[RMK]->insertProfilingCode();
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


/// @brief
//void RegionSpeculation::updateRegionPointer(RegionInfo *RI) {

  //for (iterator it = begin(), e = end(); it != e; it++) {
    //dbgs() << " == update: " << it->first.first->getNameStr() << " ==> "
           //<< it->first.second->getNameStr() << "\n";

    //RegionMapKey RMK = it->second->getRMK();
    //Region *R = RI->getRegionFor(RMK.second), *tmpR;
    //assert(R);
    //dbgs() << " === current R: " << R->getNameStr() << "\n";
    //while (R->getEntry() != RMK.first) {
      //tmpR = R->getExpandedRegion();
      //assert(tmpR);
      //R = tmpR;
      //dbgs() << " === current R: " << R->getNameStr() << "\n";
    //}

    //it->second->setRegion(R);
  //}
  
//}
  
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
