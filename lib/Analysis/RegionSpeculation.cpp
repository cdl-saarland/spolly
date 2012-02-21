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

#include <iostream>
#include <fstream>
#include <string>

#include "polly/RegionSpeculation.h"

#include "polly/ScopDetection.h"
#include "polly/LinkAllPasses.h"
#include "polly/Support/ScopHelper.h"
#include "polly/Support/SCEVValidator.h"

#include "llvm/Analysis/Interval.h"
#include "llvm/LLVMContext.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/RegionIterator.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Assembly/Writer.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Support/IRBuilder.h"
#include "llvm/Support/CFG.h"


#define DEBUG_TYPE "spolly-detect"
#include "llvm/Support/Debug.h"

// Use the analysis results of the ScopDetection
#define AA SD->AA
#define RI SD->RI
#define LI SD->LI
#define SE SD->SE

#define VIOLATION_COUNT 4
static int violationCosts[VIOLATION_COUNT] = { 2, 2, 2, 2 };

// How much is each instruction "worth"
#define INSTRUCTION_VALUE 4
#define ITERATION_TRESHOLD 10
#define ITERATIONCOUNTCONSTANT 20

#define SPECULATIVETRESHOLD 500

// Probabilities is spolly-branch-{best,worst} is set
#define BRANCHPROBABILITYHIGHT  99
#define BRANCHPROBABILITYLOW   100 - BRANCHPROBABILITYHIGHT

using namespace llvm;
using namespace polly;

static cl::opt<bool>
SPollyDisabled("spolly-disable",
       cl::desc("Disable speculative polly"),
       cl::Hidden,
       cl::value_desc("Disable speculative polly"),
       cl::init(false));


static cl::opt<bool>
SPollyEnabled("spolly-enable",
       cl::desc("Enable speculative polly"),
       cl::Hidden,
       cl::value_desc("Enable speculative polly"),
       cl::init(false));


static cl::opt<bool>
SPollyJustScore("spolly-just-score",
       cl::desc("Enable speculative polly score computation"),
       cl::Hidden,
       cl::value_desc("Enable speculative polly score computation"),
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
       cl::init(false));

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
       cl::init(false));


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
       cl::init(false));


// Variable to mark that we are within a branch and thus possibly
//  not executing some Blocks
static unsigned withinBranch = 0;



/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  getFileName 
 *  Description:  
 * =============================================================================
 */
static std::string getFileName(Region *R) {
  std::string FunctionName =
    R->getEntry()->getParent()->getName();
  std::string FileName = "spolly_" + FunctionName + ".score";
  return FileName;
}





/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  getViolationProbability
 *  Description:  
 * =============================================================================
 */
int RegionSpeculation::getViolationProbability(BasicBlock *B, Region *R) {
  int violPerc;

  if (SPollyViolationProbabilityHigh)
   violPerc = 100;
  else if (SPollyViolationProbabilityLow)
   violPerc = 1;
  else
   violPerc = 10;

  int exPerc = getExecutionProbability(B);

  DEBUG(dbgs() << "@\t  Execution probability for " << R->getNameStr()
               << " is " << exPerc << "\n");

  assert(exPerc >= 0 && exPerc <= 100
         && "Execution Probability should < 0 or > 100");

  // Decrease the violation probability based on the execution probability
  // Since the execution probability is based on profiling information ther 
  // are used to compute this result
  violPerc = violPerc * exPerc;

  // But violation probability is not only based on the execution probability.
  // If there was an test inserted the results can be used to get a better result
  ViolationProbabilityMap::iterator it = ViolationProbability.find(R);
  
  if (it != ViolationProbability.end()) {
    DEBUG(dbgs() << "@\t  Found violation probability for " << R->getNameStr()
                 << " " << (*it).second << "\n");

    violPerc = violPerc * (*it).second;
  }


  return violPerc;
}		/* -----  end of function getViolationProbability  ----- */





/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  getExecutionProbability
 *  Description:  
 * =============================================================================
 */
int RegionSpeculation::getExecutionProbability(BasicBlock *B) {
  int exPerc;

 
  // Profiling information is mapped for each BasicBlock
  // Other functions can update this information and it will be used here 
  if (ExecutionProbability[B]) {
    exPerc = ExecutionProbability[B];
  } else {
    // Test whether we are within a branch or not
    assert(withinBranch >= 0 && "WithinBranch should not be < 0");

    exPerc = 100 / (withinBranch + 1);
    ExecutionProbability[B] = exPerc;
  }
   
  return exPerc;
}		/* -----  end of function getExecutionProbability  ----- */



/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  calculateScoreFromViolations
 *  Description:  
 * =============================================================================
 */
int RegionSpeculation::calculateScoreFromViolations(BasicBlock *B, int *v, Region *R){
  int score = 0;
  for (int i = 0; i < VIOLATION_COUNT; i++) {
    score += v[i] * violationCosts[i];
  }
  
  score *= getViolationProbability(B, R);

  return score;
}		/* -----  end of function calculateScoreFromViolations  ----- */




/* 
 * ===  FUNCTION  ======================================================================
 *         Name:  insertTripCount
 *  Description:  
 * =====================================================================================
 */
void RegionSpeculation::insertTripCount(SCEV const *tripCount) {

  // Do not count zero tripCounts since they would not help the alias test
  if (tripCount->isZero()) {
    return;
  }
   
  enum llvm::CmpInst::Predicate predLess, predGreater;

  predLess = CmpInst::ICMP_SLT;
  predGreater = ICmpInst::ICMP_SGE;
  
  bool insertTripCount = true;
  for (std::list<SCEV const *>::iterator it = maxTripCounts.begin();
       it !=  maxTripCounts.end(); it++) {
    DEBUG(dbgs() << "@\t maxTripCounts Iterator: ");
    (*it)->print(dbgs());
    DEBUG(dbgs() << "\n");

    if (SE->isKnownPredicate(predLess, *it, tripCount)) {
      DEBUG(dbgs() << "@\t -- is less\n");
      // The current tripCount is greater or equal to the one stored in the
      // list, so we remove the stored one and use the current tripCount if
      // there is no other SCEV which is greater in the list
      it = maxTripCounts.erase(it);
    }

    if (SE->isKnownPredicate(predGreater, *it, tripCount)) {
      DEBUG(dbgs() << "@\t -- is greater or equal\n");
      // The list element is greater as the tripCount so we do not need to
      // insert the tripCount into the list
      insertTripCount = false;
    }
  }
 
  if (insertTripCount) {
    maxTripCounts.push_back(tripCount);
  }

}		/* -----  end of function insertTripCount  ----- */




/* 
 * ===  FUNCTION  ======================================================================
 *         Name:  registerMemoryInstruction
 *  Description:  
 * =====================================================================================
 */
void RegionSpeculation::registerMemoryInstruction(Instruction *I, Value *BV) {
  assert((isa<LoadInst>(I) || isa<StoreInst>(I)) 
         && " Instruction was neither load nor store");
  
  DEBUG(dbgs() << "@\t\t\t Register " << I->getName() << " " << I << "   " 
        << BV->getName() << " " << BV << "\n" );

  if (isa<LoadInst>(I)) {
    // TODO map contains
    if (storeInstructions.count(BV)) {
      // This 
      return;
    }
    loadInstructions.insert(BV);

  } else if (isa<StoreInst>(I)) {

    loadInstructions.erase(BV);
    storeInstructions.insert(BV);

  } else {
    assert( 0 && " Reached non store and non load instruction case "); 
  }
  

}		/* -----  end of function registerMemoryInstruction  ----- */




/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  getLoopIterationCount 
 *     Argument:  Region *R
 *  Description:  Return the iteration Count of the Region R or 
 *                ITERATIONCOUNTCONSTANT if not available 
 * =============================================================================
 */
int64_t RegionSpeculation::getLoopIterationCount(Region *R) {
  Loop *loop = LI->getLoopFor(R->getEntry());
  int64_t count = ITERATIONCOUNTCONSTANT;

  SCEV const *tripCount = SE->getBackedgeTakenCount(loop);
  assert(tripCount && "Could not get the SCEV value for the iteration count");

  //PHINode *indvar = loop->getCanonicalInductionVariable();
  //assert(indvar && "Could not get a canonical induction variable");

  //Type *indvarType= indvar->getType();
  //assert(indvarType && "Canonical induction variable has no type");

  //enum llvm::CmpInst::Predicate predLess, predGreater;
  //if (indvarType->isIntegerTy()) {
    //predLess = CmpInst::ICMP_SLT;
    //predGreater = ICmpInst::ICMP_SGE;
  //} else if (indvarType->isFloatingPointTy()) {
    //predLess = CmpInst::FCMP_OLT;
    //predGreater = CmpInst::FCMP_OGE;
  //} else {
    //assert(0 && "Could get predicate for unknown type");
  //}
  
  DEBUG(dbgs() << "@\t TripCount: ");
  tripCount->print(dbgs());
  DEBUG(dbgs() << "\n");

  insertTripCount(tripCount);

  // get constant iteration count if available
  if (SCEVConstant const *c = dyn_cast<SCEVConstant>(tripCount)) {
    count = c->getValue()->getSExtValue();
    DEBUG(dbgs() << "    -- Constant trip count " << count << "\n");
  }

  return count;
}		/* -----  end of function getLoopIterationCount  ----- */



/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  regionIsLoop
 *    Arguments:  A Region pointer R
 *      Returns:  true iff R describes a loop 
 * =============================================================================
 */
bool RegionSpeculation::regionIsLoop(Region *R) {
  RegionScoreKey RSK= std::make_pair(R->getEntry(), R->getExit());

  return (LI->getLoopDepth(RSK.first) - LI->getLoopDepth(RSK.second));
}		/* -----  end of function regionIsLoop  ----- */






/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  
 *    Arguments:  
 *      Returns:  
 * =============================================================================
 */
void RegionSpeculation::collectAliasSets(Instruction *I) {

  Value *Ptr = getPointerOperand(*I);
  const SCEV *AccessFunction = SE->getSCEV(Ptr);
  assert(AccessFunction && "Scop detection should have checked access function");

  const SCEVUnknown *BasePointer = 
    dyn_cast<SCEVUnknown>(SE->getPointerBase(AccessFunction));
  assert(BasePointer && "Scop detection should have checked base pointer");

  Value *BaseValue = BasePointer->getValue();
  assert(BaseValue && "Scop detection should have checked base value");

  DEBUG(dbgs() << "@\t  == Base value " << BaseValue << " " << *BaseValue << "\n");
  DEBUG(dbgs() << "@\t  == Instruction " << I << " " << *I << "\n");

  aliasingValues[BaseValue] = I;
}		/* -----  end of function collectAliasSets  ----- */





// maxLoopCount[0] = positive maxLoopCount
// maxLoopCount[1] = negative maxLoopCount
static Value *maxLoopCount[2];
/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  insertAliasCheck
 *    Arguments:  
 *      Returns:               | v1 - v2 | >= maxLoopCount  
 *                                        <==>
 *                v1 - v2 <= -maxLoopCount || v1 - v2 >= maxLoopCount
 * =============================================================================
 */
Value *RegionSpeculation::insertAliasCheck(BasicBlock *BBAT, 
                                           Value *v1, Value *v2, 
                                           Value *currentResult) {

  // The builder for the alias test basic block 
  IRBuilder<> builder(BBAT, --(BBAT->end())); 

  StringRef s1 = v1->getName();
  s1 = s1.substr(0, s1.size() - 3);
  StringRef s2 = v2->getName();
  s2 = s2.substr(0, s2.size() - 3);

  // The difference of the two integers v1 and v2
  Value *sub = builder.CreateSub(v1, v2, s1 + "-" + s2);
  DEBUG(dbgs() << "@\t\t - sa_sub: " << *sub << "\n");

  Value *resultP = builder.CreateICmpSGE(sub, maxLoopCount[0], s1 + "_" + s2 +"_Pcomp");
  DEBUG(dbgs() << "@\t\t - resultP: " << *resultP << "\n");
  
  Value *resultN = builder.CreateICmpSLE(sub, maxLoopCount[1], s1 + "_" + s2 +"_Ncomp");
  DEBUG(dbgs() << "@\t\t - resultN: " << *resultN << "\n");
  
  Value *result  = builder.CreateOr(resultP, resultN, s1 + "_" + s2 +"_r");
  DEBUG(dbgs() << "@\t\t - result: " << *result << "\n");

  if (currentResult) { 
    result = builder.CreateAnd(result, currentResult, 
                result->getName() + "_" + currentResult->getName());
  }

  return result;
   
}		/* -----  end of function insertAliasCheck  ----- */




/* 
 * ===  FUNCTION  ======================================================================
 *         Name:  scevToValue
 *  Description:  
 * =====================================================================================
 */
Value *RegionSpeculation::scevToValue(SCEV const *scev) {
  
  if (SCEVConstant const *C = dyn_cast<SCEVConstant>(scev)) {
    return C->getValue();
  } else if (SCEVUnknown const *U = dyn_cast<SCEVUnknown>(scev)) {
    return U->getValue();
  } else if (SCEVSMaxExpr const *S = dyn_cast<SCEVSMaxExpr>(scev)) {
    SCEVNAryExpr::op_iterator op = S->op_begin();
    Value *val = scevToValue(*(op++));
    for (; op != S->op_end(); op++) {
      insertTripCount(*op);
    }
    return val;
  } else if (SCEVUMaxExpr const *S = dyn_cast<SCEVUMaxExpr>(scev)) {
    SCEVNAryExpr::op_iterator op = S->op_begin();
    Value *val = scevToValue(*(op++));
    for (; op != S->op_end(); op++) {
      insertTripCount(*op);
    }
    return val;
  } else {
    (scev)->print(dbgs());
    assert(0 && "unknown scev value");
  }

}		/* -----  end of function scevToValue  ----- */



/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  insertAliasCheck
 *  
 * ---------------------------------       --------------------------------- 
 * | ----------         ---------- |       | ----------         ---------- |
 * | | pred_1 |   ...   | pred_n | |       | | pred_1 |   ...   | pred_n | | 
 * | ----------         ---------- |       | ----------         ---------- |
 * |     |                   |     |       |     |                   |     |
 * |     \-------\   /-------/     |       |     \-------\   /-------/     |
 * |             |   |             |       |             |   |             |
 * |             V   V             |       |             V   V             | 
 * |         -------------         |       |        --------------         | 
 * |         |   entry   |         |       |        | alias_test |         | 
 * |         -------------         |       |        --------------         |
 * |               |               |       |           |      |            |
 * |               V               |       |           V      |            |
 * ---------------------------------       |   =------------  |            |
 *                                         |   | originalV |  |            |
 *                                         |   -------------  |            |
 *                                         |                  |            |
 *                                         |                  V            |
 *                                         |             -------------     |
 *                                         |             | parallelV |     |
 *                                         |             -------------     |
 *                                         ---------------------------------
 *
 * =============================================================================
 */
void RegionSpeculation::insertAliasChecks(void *C, BasicBlock *BBAT) {
  ScopDetection::DetectionContext *Context = 
      (ScopDetection::DetectionContext*) C;
 
  assert(aliasingValues.size() 
         && "No aliasing values, thus no need to insert a check"); 

  DominatorTree *DT = SE->getAnalysisIfAvailable<DominatorTree>();
  assert(DT && "No dominatorTree available");
  
  BasicBlock *entry = currentRegion->getEntry();
  // An iterator over the aliasing values
  std::map<Value*, Instruction*>::iterator avit;
  std::set<Value*> aliasingVals;
  // Insert aliasing pointers to the set of aliasing ints if they can be 
  // derived outside the loop. The set stores no pointers, instead the casted
  // integer values.
  for (avit = aliasingValues.begin(); avit != aliasingValues.end(); avit++) {
    DEBUG(dbgs() << "@\t  -- Base value is " << avit->first 
          << " and Instruction is " << avit->second << "\n");
   
    if (violatingInstructions.count(avit->second)) continue;

    AliasSet &AS = 
      Context->AST.getAliasSetForPointer(avit->first, AliasAnalysis::UnknownSize,
                                avit->second->getMetadata(LLVMContext::MD_tbaa));

    DEBUG(dbgs() << "@\t   -- avit: " << avit->first  << " " << *avit->first << "\n");
    //DEBUG(dbgs() << "@\t   -- avit2: " << avit->second << " " << *avit->second << "\n");
    AS.print(dbgs());

    assert(!AS.empty() && " alias set is empty ");
     
    for (AliasSet::iterator outerIt = AS.begin();
         outerIt != AS.end(); outerIt++) {
      Value *outerItValue = outerIt->getValue();
      DEBUG(dbgs() << "@\t asit value: " <<   outerIt->getValue()->getName()
            << " " << *outerIt->getValue() << "\n");

      if (Instruction *I = dyn_cast<Instruction>(outerItValue)) {
        if (DT->dominates(I->getParent(), entry)) {
          DEBUG(dbgs() 
                << "@\t instruction is not dominated by the check basic block\n");
          // This instruction/pointer can not be tested because it is not loop 
          // invariant
          continue;
        }
      } 
       
      // The value outerItValue is loop indipendant so we can use it for the 
      // alias tests
      aliasingVals.insert(outerItValue);
    }
  }
 
  if (aliasingVals.size() < 2) {
    DEBUG(dbgs() << "@\t There are not enough pointers to compare");
    return;
  }

  // The builder for the alias test basic block 
  IRBuilder<> builder(BBAT, --(BBAT->end())); 
  
  assert(maxTripCounts.size() && "No trip count record found");

  Value *maxTripCount = NULL;
  maxTripCount = scevToValue(maxTripCounts.front());
  maxTripCounts.pop_front();

  // compute or insert the maximal loop iteration count
  while (maxTripCounts.size()) {
    Value *val = scevToValue(maxTripCounts.front());
    maxTripCounts.pop_front();
    Value *cmp = builder.CreateICmpSGT(val, maxTripCount);
    maxTripCount = builder.CreateSelect(cmp, val, maxTripCount); 
  }
  
  // The integer 64 type the pointers are converted to
  LLVMContext &llvmContext = BBAT->getContext();
  IntegerType *t64 = Type::getInt64Ty(llvmContext);
  
  maxLoopCount[0] = builder.CreateSExtOrBitCast(maxTripCount, t64);
  maxLoopCount[1] = builder.CreateNeg(maxLoopCount[0]);
  // A set of all aliasing pointer casted to integers
  std::set<Value*> aliasingInts;

  
  for (std::set<Value *>::iterator aliasingValue = aliasingVals.begin(); 
       aliasingValue != aliasingVals.end(); aliasingValue++){
      // TODO assert v1, v2 to be pointers
      // Cast v1 and v2 to int 
      Value *pointerAsInt = builder.CreatePtrToInt(*aliasingValue, t64,
                                      (*aliasingValue)->getName() +"_64");
      aliasingInts.insert(pointerAsInt);
  }

  // All pointers to check are in the set aliasingInts
  Value *result = NULL;
  for (std::set<Value *>::iterator aliasingValue = aliasingInts.begin(); 
       aliasingValue != aliasingInts.end(); aliasingValue++){
    // Iterate over all coming values to check each against another
    for (std::set<Value *>::iterator otherAliasingValue(aliasingValue);
         ++otherAliasingValue != aliasingInts.end();) {
      result = insertAliasCheck(BBAT, *aliasingValue,
                                *otherAliasingValue, result); 
    }  
  }

  // After the code generation this terminator of BBAT can be changed to a
  // conditional branch to the new (speculative) parallelized version or to
  // the old non parallelized version 
  // TODO
  //TerminatorInst *oldTerm = BBAT->getTerminator();
  BBAT->getTerminator()->eraseFromParent();

  DEBUG(dbgs() << "@\t Create new condBr, " 
        << currentRegion->getEntry()->getNameStr() << " -> " 
        << currentRegion->getExit()->getNameStr() << " | val: "
        << result->getName() << "\n");

  BranchInst::Create(currentRegion->getEntry(), currentRegion->getExit(),
                     result, BBAT);

  DEBUG(dbgs() << "\n\n\n-----------------------------------------------\n\n");

}		/* -----  end of function insertAliasChecks  ----- */


/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  insertInvariantCheck
 *    Arguments:  
 *      Returns:  
 * =============================================================================
 */
void RegionSpeculation::insertInvariantChecks(BasicBlock *pred) {
  // If the region does not contain a call we can skip the placement of 
  // invariant checks
  DEBUG(dbgs() << "@\t InsertInvariantChecks " << containsCalls << "\n");
  assert(containsCalls && "No need to insert invariant checks without calls");

  BasicBlock *entry = currentRegion->getEntry();

  // Insert tmp variables in the predecessor pred of the regions entry block 
  // They save the values of the read variables befor we enter the loop
  // Insert a check within the loop for, thus test the tmp variables against the
  // current values
  DominatorTree *DT = SE->getAnalysisIfAvailable<DominatorTree>();
  assert(DT && "No dominatorTree available");
  
  std::map<Value*, Value*> temporaries;
  for (std::set<Value*>::iterator loads = loadInstructions.begin(); 
       loads != loadInstructions.end(); loads++) {
    
    if (Instruction *I = dyn_cast<Instruction>(*loads)) {
      if (!DT->dominates(I->getParent(), pred)) {
        continue;
      }
    }

    IRBuilder<> builder(pred, --((pred)->end())); 

    DEBUG(dbgs() << "@\t\t INVARIANT load " << (*loads)->getName() << " " 
         << (*loads) << "\n");

    Value *tmp = builder.CreateLoad(*loads, (*loads)->getName() + "_tmp"); 
    temporaries[*loads] = tmp;
  } 
  
  //IRBuilder<> builder(entry, --((entry)->end())); 
  DEBUG(dbgs() << "@\t ENTRY: " << entry->getName() << "  " 
        << entry->begin()->getName() << "\n");
  BasicBlock *ITB = SplitBlock(entry, entry->begin(), SD);
  BasicBlock *ITBpost = SplitBlock(ITB, ITB->begin(), SD);

  StringRef entryName = entry->getName();
  entry->setName(entryName + "_new_entry");
  ITB->setName(entryName + "_spolly_cmp");
  ITBpost->setName(entryName + "_old_entry");

  DEBUG(dbgs() << "@\t ITB: " << ITB->getName() << "\n"); 
   
  IRBuilder<> builder(ITB, --((ITB)->end())); 
  
  // The integer 64 type the pointers are converted to
  LLVMContext &llvmContext = ITB->getContext();
  IntegerType *t64 = Type::getInt64Ty(llvmContext);

  Value *result = NULL;
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
  
  // Create a new basic block which will handle a non invariant case
  BasicBlock *NIB = BasicBlock::Create(llvmContext, "NIB", entry->getParent(),
                                       entry);
  // Update dominance tree information
  DT->addNewBlock(NIB, ITB);

  // TODO fill NIB
  BranchInst::Create(ITBpost, NIB);

  // Use the result to jump to the ITBpost (invariant) or NIB (not invariant)
  BranchInst::Create(ITBpost, NIB,
                     result, ITB);

}		/* -----  end of function insertInvariantCheck  ----- */







/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  insertFunctionCheck
 *    Arguments:  
 *      Returns:  
 * =============================================================================
 */
void RegionSpeculation::insertFunctionCheck(Instruction *I) {
  containsCalls = true;

}		/* -----  end of function insertFunctionCheck  ----- */




/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  insertRollbackCall
 *    Arguments:  
 *      Returns:  
 * =============================================================================
 */
void RegionSpeculation::insertRollbackCall(Instruction *I) {

}		/* -----  end of function insertRollbackCall  ----- */




/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  addViolatingInstruction 
 *    Arguments:  A violating Instruction I, the kind of the violation
 *  Description:  Add the Instruction I to the list of all violating
 *                instructions. If this Region should be executed speculatively
 *                the replaceViolatingInstructions call will replace it with 
 *                a unique function call
 * =============================================================================
 */
void RegionSpeculation::addViolatingInstruction(Instruction *I, unsigned viol) {
  DEBUG(dbgs() << "@\t Add violating instruction " << viol << " "<< *I << "\n");

  // Save the instruction in the list of violating ones
  violatingInstructions[I] = NULL;

  switch (viol) {
    case VIOLATION_ALIAS:
      collectAliasSets(I);      
      break;

    case VIOLATION_AFFFUNC:
      break;

    case VIOLATION_FUNCCALL:
      insertFunctionCheck(I);
      break;

    case VIOLATION_PHI:
      break;

    default:
      assert(0 && "Cannot determine violation kind");
  }

  // The corresponding call is created as needed
}		/* -----  end of function addViolatingInstruction  ----- */







/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  createCall
 *    Arguments:  
 *      Returns:  
 * =============================================================================
 */
CallInst *RegionSpeculation::createCall(Instruction *I) {
  
  FunctionType *FT; 
  Function *FN = NULL;
  CallInst *callInst = NULL;

  // The IRBuilder for the basic block with the violating instruction
  //IRBuilder<> builder(context);
  //Module *M = builder.GetInsertBlock()->getParent()->getParent();
  Module *M = I->getParent()->getParent()->getParent();
  
  DEBUG(dbgs() << *I->getType() << "\t" << I->getNumOperands() << "\n"
        << *I->getOperand(0));
  
  unsigned argsC = I->getNumOperands();

  // Remove the called function operand from call instructions
  if (I->getOpcode() == Instruction::Call) {
    argsC -= 1;
  }
  

  std::vector<Type *> argsT(argsC);
  std::vector<Value *> argsV(argsC);
  for (unsigned i = 0; i < argsC; i++) {
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
  callInst = CallInst::Create(FN, Args);

  // Set some attributes to allow Polly to handle this function
  FN->setDoesNotThrow(true);
  FN->setDoesNotReturn(false);

  // TODO see ScopDetection::isValidCallInst
  //FN->setOnlyReadsMemory(true);
  //FN->setDoesNotAccessMemory(true);



  assert(callInst && "Call Instruction was NULL");

  // the new call inst
  //callInst->removeFromParent(); 
  
  return  callInst;

}		/* -----  end of function createCall  ----- */





/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  replaceViolatingInstructions
 *    Arguments:  
 *      Returns:  
 * =============================================================================
 */
void RegionSpeculation::replaceViolatingInstructions(Region &R) {
  if (!SPollyReplaceViolatingInstructions) return;

  DEBUG(dbgs() << "@\t Replace violating instructions "<< "\n");
  std::map<Instruction*,Instruction*>::iterator vIit;

  CallInst *callInst;
  
  // foreach violating instruction
  for (vIit = violatingInstructions.begin(); vIit != violatingInstructions.end();
       vIit++) {
    // create the corresponding call instruction and add it to
    // the replacementInstructions list
    DEBUG(dbgs() << "@\t\t replace " << (*(vIit->first)) << "\n");
    //DEBUG(dbgs() << " " << (**vIit)) << "\n";
  
    if (SPollyRemoveViolatingInstructions) {
      (vIit->first)->eraseFromParent();
      continue;
    } else if ((vIit->first)->getOpcode() == Instruction::PHI) {
      // Skip Phi nodes since they dominate theirself 
      continue;
    }
   
    // vIit is not a PHI instruction and we should not remove it, so we 
    // create a call instruction which will be used to replace vIit  
    callInst = createCall(vIit->first);
    
    assert(callInst && "Replacement call is NULL");

    DEBUG(dbgs() << "@\t\t with " << (*callInst) << "\n");
    
    // Save the call in the replacementInstructions list
    // #x of violatingInstructions <<==>> #x of replacementInstructions
    violatingInstructions[vIit->first] = (callInst);
    
    // Replace the violating instruction with the created call 
    //callInst->moveBefore(*vIit);
    //(*vIit)->replaceAllUsesWith(callInst);
    ReplaceInstWithInst(vIit->first, callInst);
    
    //(*vIit)->eraseFromParent(); 
    
    // Add the result of the new call to the pseudo sum 
    // else it would vanish if it is not used 
    
  
  } /* -----  end foreach violating instruction  ----- */




}		/* -----  end of function replaceViolatingInstruction ----- */






/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  scoreBasicBlock
 *    Arguments:  The BasicBlock for which a score should be computed
 *      Returns:  The computed score
 *  Description:  
 * =============================================================================
 */
int RegionSpeculation::scoreBasicBlock(BasicBlock *B) {

  // Start with an initial value which is not accurate for this block
  // but in the end all violations not contained in this block are substracted
  int blockScore = calculateScoreFromViolations(B, violations, currentRegion);

  DEBUG(dbgs() << "@\t    Computing score of the BasicBlock " 
        << B->getName() << " \n");

  // Add INSTRUCTIONVALUE per instruction in the BasicBlock
  blockScore += B->size() * INSTRUCTION_VALUE;

  ScopDetection::DetectionContext Context(*currentRegion, *(AA),
                                          false /*verifying*/);
  SD->isValidBasicBlock(*B, Context);

  // This will take all violations within this block into account
  blockScore  -= calculateScoreFromViolations(B, violations, currentRegion);

  DEBUG(dbgs() << "@\t    -- blockScore is " << blockScore << " \n");
  return blockScore;
}		/* -----  end of function scoreBasicBlock  ----- */





/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  scoreLoop
 *    Arguments:  A Region R containing a loop
 *      Returns:  A score for this Region
 *  Description:  Use the iterationCount and score from BasicBlocks as well
 *                as SubRegions to compute a score for this Region
 *
 *  -----------------------------------------
 *  |                              Region R |
 *  |                                       |
 *  |           ==========                  |
 *  |           | Header |<---|             |
 *  |           ==========    |             |
 *  |              |          |             |
 *  |         |----|          |             |
 *  |         V               |             |
 *  |     ========            |             |
 *  |     | Body |            |             |
 *  |     ========            |             |
 *  |         |               |             |
 *  |         |----|          |             |
 *  |              V          |             |
 *  |           ==========    |             |
 *  |           |        |----|             |
 *  |           ==========                  |
 *  |                                       |
 *  -----------------------------------------
 *
 * =============================================================================
 */
int RegionSpeculation::scoreLoop(Region *R) {
  int loopScore = 0, iterationCount;

  // Get the iteration count if computable or via profiling information  
  iterationCount = getLoopIterationCount(R);
  
  assert(iterationCount > 0 && "invalid iteration count");

  // The iteration count influences the score
  loopScore = (loopScore * iterationCount) / ITERATION_TRESHOLD;

  // Handle all subregions and basicBlocks within this region
  for (Region::element_iterator bb = R->element_begin(), be = R->element_end();
       bb != be; ++bb) {

    if ((*bb)->isSubRegion()) {
      DEBUG(dbgs() << "@\t-- and the subregion " << 
            (*bb)->getNodeAs<Region>()->getNameStr() << " \n");
      loopScore += scoreRegion((*bb)->getNodeAs<Region>());
    } else {
      DEBUG(dbgs() << "@\t-- and the BasicBlock " << 
            (*bb)->getNodeAs<BasicBlock>()->getName() << " \n");
      loopScore += scoreBasicBlock((*bb)->getNodeAs<BasicBlock>());
    }
  }


  DEBUG(dbgs() << "@\t  -- Loop score is " << loopScore << " \n");
  return loopScore;
}		/* -----  end of function scoreLoop  ----- */





/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  scoreConditional
 *    Arguments:  The Region R containing a contitional
 *      Returns:  A score computed for the whole Region
 *
 * -----------------------------------------    
 * |                              Region R |
 * |              =========                |  To score a conditional, first the
 * |              I entry I -- entryScore  |  entry BasicBlock is scored, and 
 * |              I-------I                |  afterwards the branch0 and br1-
 * |              I guard I                |  ernative, but only if such a block
 * |              ==|===|==                |  exitst. The branch1 or the 
 * |                |   |                  |  branch0 (but not both) could be 
 * |     |- second -|   |- first -|        |  the same as the Exit block. In 
 * |     V                        V        |  such a case no score is added.
 * | ===========             ============  |  Before we sum up all computed 
 * | I branch1 I             I branch0  I  |  scores, we use profiling data
 * | ===========             ============  |  to weight the scores computed
 * |       | br1Score   br0Scrore |        |  for the branches. The exit node
 * ------- | -------------------- | --------  Is handled by the scoreRegion.
 *         |                      |       
 *         |                      |           
 *         |      ==========      |           
 *         |----->I  exit  I<-----|           
 *                ==========                  
 *    
 *        br0Score = ((br0 * p(br0)) / (101 - p(br0)))     
 *        br0Score = ((br1  * p(br1))  / (101 - p(br1)))     
 *        where p(block) := execution probability of block
 *
 *        conditionlScore = entryScore + br1Score + br0Score
 *
 * =============================================================================
 */
int RegionSpeculation::scoreConditional(Region *R) {
  Region *tempRegion; 
  BasicBlock *branch0, *branch1, *entry, *exit;
  int conditionalScore = 0, entryScore = 0, br0Score = 0, br1Score = 0;
  int probability0, probability1;

  // Increase withinBranch to indicate that we probably not execute every Block
  withinBranch++;
  
  exit  = R->getExit();
  entry = R->getEntry(); 
  entryScore = scoreBasicBlock(entry);


  TerminatorInst *guard = entry->getTerminator();
  assert(guard->getNumSuccessors() == 2 
         && "Branch with two successors expected");

  branch0 = guard->getSuccessor(0);
  branch1  = guard->getSuccessor(1);
 
  probability0 = getExecutionProbability(branch0);
  while (branch0 != exit) {
    if ((tempRegion = RI->getRegionFor(branch0)) == R) {
      // The branch0 is a BasicBlock in the region R 
      br0Score += scoreBasicBlock(branch0);
      branch0   = branch0->getTerminator()->getSuccessor(0);
    } else {
      // The branch0 is contained in another region
      br0Score += scoreRegion(tempRegion);
      branch0   = tempRegion->getExit();
    }
  }

  // probability1 = 100 - probability0 
  probability1 = getExecutionProbability(branch1); 
  while (branch1 != exit) {
    if ((tempRegion = RI->getRegionFor(branch1)) == R) {
      // The branch1 is just one BasicBlock   
      br1Score += scoreBasicBlock(branch1);
      branch1   = branch1->getTerminator()->getSuccessor(0);
    } else {
      // The branch1 contains another region
      br1Score += scoreRegion(tempRegion);
      branch1   = tempRegion->getExit();
    }
  }

  // If commandline flags are set, orverwrite the probabilities
  if (SPollyBranchWorst) {
    if (br0Score < br1Score) {
      probability0 = BRANCHPROBABILITYHIGHT;
      probability1 = BRANCHPROBABILITYLOW;
    } else {
      probability1 = BRANCHPROBABILITYHIGHT;
      probability0 = BRANCHPROBABILITYLOW;
    }
  } else if (SPollyBranchBest) {
    if (br0Score < br1Score) {
      probability1 = BRANCHPROBABILITYHIGHT;
      probability0 = BRANCHPROBABILITYLOW;
    } else {
      probability0 = BRANCHPROBABILITYHIGHT;
      probability1 = BRANCHPROBABILITYLOW;
    }
  }

  assert(probability0 >=   0 && "probability <   0% ");
  assert(probability0 <= 100 && "probability > 100% ");
  assert(probability1 >=   0 && "probability <   0% ");
  assert(probability1 <= 100 && "probability > 100% ");

  // Score the first branch
  br0Score = (br0Score * probability0) / (101 - probability0);
  // Score the first branch
  br1Score = (br1Score * probability1) / (101 - probability1);

  conditionalScore = entryScore + br0Score + br1Score;

  // Decrease withinBranch to indicate that we left a Branch
  withinBranch--;
  
  DEBUG(dbgs() << "@\t  -- Conditional score is " << conditionalScore << " \n");
  return conditionalScore;

}		/* -----  end of function scoreConditional  ----- */





/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  scoreRegion
 *    Arguments:
 *      Returns:  
 *
 *
 * =============================================================================
 */
int RegionSpeculation::scoreRegion(Region *R) {
  RegionScoreKey RSK= std::make_pair(R->getEntry(), R->getExit());
  
  RegionScoreMap::iterator it;
  Region *tempRegion; 
  int regionScore = 0;

  // Save the currentRegion
  tempRegion    = currentRegion;
  // And set R as (temporary) new one
  currentRegion = R;
    
  DEBUG(dbgs() << "\n@\tCompute score for region "<<  R->getNameStr() << "\n");

  // Score this region as loop or conditional 
  if (regionIsLoop(R)) {
    DEBUG(dbgs() << "@\t-- which is a loop \n");
    regionScore += scoreLoop(R);
  } else {
    DEBUG(dbgs() << "@\t-- which is a conditional \n");
    regionScore += scoreConditional(R);
  }

  // Save the score and leave 
  RegionScores[RSK] = regionScore;

  // Restore the currentRegion
  currentRegion = tempRegion;
  
  DEBUG(dbgs() << "@\t-- Region score is " << regionScore << " \n");

  return regionScore;
}		/* -----  end of function scoreRegion  ----- */



/* 
 * ===  FUNCTION  ======================================================================
 *         Name:  createTestBlock
 *  Description:  
 * =====================================================================================
 */
BasicBlock *RegionSpeculation::createTestBlock() {
  BasicBlock *entry = currentRegion->getEntry();

  DEBUG(dbgs() << "\n\n\n@\t----------------123456---------------------------\n\n");


  // Collect all predecessors of entry which do not belong to the loop/region
  std::vector<BasicBlock*> entryPreds;
  for (pred_iterator itPred = pred_begin(entry),
       end = pred_end(entry); itPred != end; itPred ++) {
    if ( currentRegion->contains(*itPred) ) continue;
    entryPreds.push_back(*itPred);
  }

  // Split the entry block according to the collected predecessors 
  BasicBlock *BBAT = SplitBlockPredecessors(entry, &entryPreds[0], 
                                            entryPreds.size(),
                                            "_spolly_tests",
                                            SD);
   
  return BBAT;
}		/* -----  end of function createTestBlock  ----- */



/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  prepareRegion
 *  Description:  
 * =============================================================================
 */
void RegionSpeculation::prepareRegion( Region &R ) {
  DEBUG(dbgs() << "\n@@@@# prepareRegion " << R.getNameStr() << " \n");
  DEBUG(dbgs() << "\n@\tPrepare region "<<  R.getNameStr() << "\n");
  DEBUG(dbgs() << "@\t\t " << maxTripCounts.size() << "\n");
  
  RegionScoreKey RSK= std::make_pair(R.getEntry(), R.getExit());
  if (preparedRegions.count(RSK) || R.getExit()->getName().startswith("polly")) {
    DEBUG(dbgs() <<"@\t\t skipped region");
    return;
  } 
  preparedRegions.insert(RSK);
  
   
  // if gatherViolatingInstructions is set we are preparing the region right now
  assert (!SD->gatherViolatingInstructions &&
          "Called prepare Region during preparation");

  // We need to access the region later on to create the checks
  currentRegion = &R;
  
  // Indicate that all violating instructions should be added by calling
  // addViolatingInstruction(Instruction *I)
  SD->gatherViolatingInstructions = true;
  
  // check the region again, but this time invalid instructions are gathered
  ScopDetection::DetectionContext Context(R, *AA, false /*verifying*/);
  SD->isValidRegion(Context);

  BasicBlock *testBlock = createTestBlock();
  postPrepareRegion(testBlock);

  // replace the gathered instructions
  replaceViolatingInstructions(R);

  // After the region is prepared we do not want to gather instructions anymore
  SD->gatherViolatingInstructions = false;

  DEBUG(dbgs() << "\n@\t== Prepared region "<<  R.getNameStr() << "\n");
  
}		/* -----  end of function prepareRegion  ----- */




/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  postPrepareRegion
 *  Description:  
 * =============================================================================
 */
void RegionSpeculation::postPrepareRegion(BasicBlock *testBlock) {
  DEBUG(dbgs() << "\n@@@@# postPrepareRegion " << currentRegion << "  "
        << " TB: "  << testBlock << "  "<< testBlock->getName() 
        << " " << aliasingValues.size() << "  \n");

  ScopDetection::DetectionContext Context(*currentRegion, *AA,
                                          false /*verifying*/);
  
  if (aliasingValues.size() || containsCalls) {
    
    // insert Alias checks
    if (aliasingValues.size()) {
      insertAliasChecks((void *)&Context, testBlock);
    }
  
    if (containsCalls) {
      // This causes Polly assertions AffFunc 4 and CFG 1
      //insertInvariantChecks(testBlock);
    }
  }  

}		/* -----  end of function postPrepareRegion  ----- */



/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  speculateOnRegion
 *    Arguments:  The speculative valid Region &R
 *                The violation array (counter for each violation)
 *  Description:  This function is the entry point for the region speculation.
 *                If Pollys SCoP detections detects some SCoP which would be 
 *                valid except for the restrictions we speculate on, it calls
 *                this function.
 * =============================================================================
 */
bool RegionSpeculation::speculateOnRegion(Region &R, int *v) {
  DEBUG(dbgs() << "\n@@@@# speculateOnRegion " << R.getNameStr() << "\n");
  if (SPollyDisabled && !SPollyEnabled) return false;
  
  RegionScoreKey RSK= std::make_pair(R.getEntry(), R.getExit());
  if (RegionScores.count(RSK)) return true; 

  DEBUG(dbgs() << "\n@\tSpeculate on region "<<  R.getNameStr() << "\n");

  // Clear the list of violating and replacement instructions
  maxTripCounts.clear();
  violatingInstructions.clear();
  aliasingValues.clear();
  loadInstructions.clear();
  storeInstructions.clear();
  containsCalls = false;
  

  
  violations = v;

  int i;
  // revert the violation count 
  for (i = 0; i < VIOLATION_COUNT; i++) {
    DEBUG(dbgs() << "@i: " << i << "  v[i]: " << violations[i] << "\n");
    violations[i] = -violations[i];
  } 
  
  int score = scoreRegion(&R);

  // TODO change output file according to the current function
  if (SPollyDumpCandidates) {
    std::ofstream outfile (getFileName(&R).c_str(), std::ios_base::app);
    outfile << func->getParent() << "\t\t" <<  R.getNameStr() << ":\t\t" << score << "\n";
    outfile.close();
  }
  
  // Sanity check 
  for (i = 0; i < VIOLATION_COUNT; i++) {
    DEBUG(dbgs() << "@i: " << i << "  v[i]: " << violations[i] << "\n");
    assert(violations[i] == 0 
           && "All violations should be found in subRegions and BasicBlocks.");
  }
  
  

  if (SPollyJustScore) return false;

  //return false;
  return true;

  //return score > SPECULATIVETRESHOLD;
}		/* -----  end of function speculateOnRegion  ----- */


RegionSpeculation::RegionSpeculation(ScopDetection *sd) {
  SD = sd;
  DEBUG(dbgs() << "00000000000123456789 \n");
}
