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

#include "polly/ScopInfo.h"
#include "polly/ScopDetection.h"
#include "polly/LinkAllPasses.h"
#include "polly/Support/ScopHelper.h"
#include "polly/Support/RegionSpeculationHelper.h"
#include "polly/Support/SCEVValidator.h"

#include "llvm/Module.h"
#include "llvm/Target/TargetData.h"
#include "llvm/Analysis/Interval.h"
#include "llvm/LLVMContext.h"

#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/DenseMap.h"

#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/RegionIterator.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#define DEBUG_TYPE "region-speculation"
#include "llvm/Support/Debug.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/CommandLine.h"

#define FunctionForRegion(R) (R->getEntry()->getParent())

using namespace llvm;
using namespace polly;


#if 0

#define VIOLATION_COUNT 4
static int violationCosts[VIOLATION_COUNT] = { 2, 1, 2, 2 };


// How much is each instruction "worth"
#define INSTRUCTION_VALUE 10
#define ITERATION_TRESHOLD 10
#define ITERATIONCOUNTCONSTANT 20

#define SPECULATIVETRESHOLD -500

// Probabilities is spolly-branch-{best,worst} is set
#define BRANCHPROBABILITYHIGHT  99
#define BRANCHPROBABILITYLOW   100 - BRANCHPROBABILITYHIGHT


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
   *         Name:  regionIsLoop
   *    Arguments:  A Region pointer R
   *      Returns:  true iff R describes a loop 
   * ===========================================================================
   */
  bool regionIsLoop(Region *R, LoopInfo *LI) {
    BasicBlock *entry = R->getEntry();
    BasicBlock *exit  = R->getExit();

    return (LI->getLoopDepth(entry) - LI->getLoopDepth(exit));
  }		  /* -----  end of function regionIsLoop  ----- */

  
  
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
 *         Name:  registerMemoryInstruction
 *  Description:  
 * =====================================================================================
 */
void RegionSpeculation::registerMemoryInstruction(Instruction *I, Value *BV,
                                                  const SCEV *AccessFunction) {
  assert((isa<LoadInst>(I) || isa<StoreInst>(I)) 
         && " Instruction was neither load nor store");
  
  (dbgs() << "@\t\t\t Register " << I->getName() << " " << I << "   " 
          << BV->getName() << " " << BV << " AF:" << AccessFunction 
          << "  " << *AccessFunction << "\n" );

  if (isa<LoadInst>(I)) {
    // TODO map contains
    if (storeInstructions.count(BV)) {
      // This 
    } else {
      loadInstructions.insert(BV);
    }
  } else if (isa<StoreInst>(I)) {

    loadInstructions.erase(BV);
    storeInstructions.insert(BV);

  } else {
    assert( 0 && " Reached non store and non load instruction case "); 
  }
  
  accessFunctions[BV].insert(AccessFunction); 

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
  Loop *loop = SD->LI->getLoopFor(R->getEntry());
  int64_t count = ITERATIONCOUNTCONSTANT;

  SCEV const *tripCount = SE->getBackedgeTakenCount(loop);
  assert(tripCount && "Could not get the SCEV value for the iteration count");

  DEBUG(dbgs() << "@\t TripCount: ");
  tripCount->print(dbgs());
  DEBUG(dbgs() << "\n");


  // get constant iteration count if available
  if (SCEVConstant const *c = dyn_cast<SCEVConstant>(tripCount)) {
    count = c->getValue()->getSExtValue();
    DEBUG(dbgs() << "    -- Constant trip count " << count << "\n");
  }

  return count;
}		/* -----  end of function getLoopIterationCount  ----- */




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

  (dbgs() << "@\t  == Base value " << BaseValue << " " << *BaseValue << "\n");
  (dbgs() << "@\t  == Instruction " << I << " " << *I << "\n");

  aliasingValues[BaseValue] = 
        std::make_pair(I, I->getMetadata(LLVMContext::MD_tbaa));
}		/* -----  end of function collectAliasSets  ----- */




/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  insertAliasCheck
 *    Arguments:  
 * =============================================================================
 */
Value *RegionSpeculation::insertAliasCheck(BasicBlock *BBAT, 
                                           std::pair<Value*, Value*> &v0,
                                           std::pair<Value*, Value*> &v1,
                                           Value *currentResult) {

  // The builder for the alias test basic block 
  IRBuilder<> builder(BBAT, --(BBAT->end())); 
  
  Value *min0 = v0.first, *max0 = v0.second;
  Value *min1 = v1.first, *max1 = v1.second;

  Value *result0 = builder.CreateICmpSGT(min0, max1,
                                         min0->getNameStr() + "_g_" 
                                         + max1->getNameStr());
  DEBUG(dbgs() << "@\t\t - result0: " << *result0 << "\n");
  Value *result1 = builder.CreateICmpSGT(min1, max0,
                                         min1->getNameStr() + "_g_" 
                                         + max0->getNameStr());
  DEBUG(dbgs() << "@\t\t - result1: " << *result1 << "\n");
  
  Value *result  = builder.CreateOr(result0, result1, result0->getNameStr()
                                                      + "_v_" 
                                                      + result1->getNameStr());
  DEBUG(dbgs() << "@\t\t - result: " << *result << "\n");

  if (currentResult) { 
    result = builder.CreateAnd(result, currentResult, 
                result->getName() + "_A_" + currentResult->getName());
  }

  return result;
   
}		/* -----  end of function insertAliasCheck  ----- */




/* 
 * ===  FUNCTION  ======================================================================
 *         Name:  scevToValue
 *  Description:  
 * =====================================================================================
 */
static std::map<const SCEV*, Value*> scevToValueMap; 
Value *RegionSpeculation::scevToValue(const SCEV *scev, IRBuilder<> &builder) {
  assert(scev && "SCEV was 0");
  std::map<const SCEV*, Value*>::iterator v = scevToValueMap.find(scev); 
  if (v != scevToValueMap.end()) {
    return v->second;
  }
  
  //dbgs() << "SCEV TO VALUE "<< *scev << "\n";
  //assert(!scev->isZero() && "Zero is a useless offset for alias checking 1");

  if (const SCEVConstant *C = dyn_cast<SCEVConstant>(scev)) {
    
    Value *val = builder.CreateSExtOrBitCast(C->getValue(), 
                                    builder.getInt64Ty(), "const"); 
    //dbgs() << "ConstValue " << *val << "\n";
    scevToValueMap[scev] = val;
    return val;

  } else if (const SCEVCastExpr *Cast = dyn_cast<SCEVCastExpr>(scev)) {
    
    assert(isa<SCEVSignExtendExpr>(Cast) 
           && "Only sign extended casts are supported");
    Value *val = scevToValue(Cast->getOperand(), builder);
    //dbgs() << "SignExtend of " << *val << " to " << *Cast->getType() << "\n";
    Value *sext= builder.CreateSExtOrBitCast(val, Cast->getType(), "scev_sext");
    //dbgs() << " == " << *sext << "\n";
    scevToValueMap[scev] = sext;
    return sext;

  } else if (const SCEVUnknown *U = dyn_cast<SCEVUnknown>(scev)) {

    Type *type;
    if (U->isSizeOf(type)) {
      //dbgs() << "Sizeof " << *type << "\n";
      Value *val = builder.getInt64(TD->getTypeStoreSize(type));
      scevToValueMap[scev] = val;
      return val; 
    } else {
      Value *val = U->getValue();
      if (U->getType()->isPointerTy()) {
        val = builder.CreatePtrToInt(val, 
                                     builder.getInt64Ty(), 
                                     val->getName()+"_64");
      } else { 
        val = builder.CreateSExtOrBitCast(val, builder.getInt64Ty(), 
                                          val->getName()+"_64"); 
      }

      scevToValueMap[scev] = val;
      //dbgs() << "UnknownValue " << *val << "\n";
      return val;
    }

  } else if (const SCEVAddRecExpr *R = dyn_cast<SCEVAddRecExpr>(scev)) {
    assert(R->getNumOperands() == 2 
           && "Found add rev expr with more than two operands");

    Value *step  = scevToValue(R->getStepRecurrence(*SE), builder);
    const Loop *loop = R->getLoop();
    //dbgs() << "LOOP " << *loop << "\n";
    Value *loopCount = builder.CreateSExtOrBitCast(
                            scevToValue(SE->getBackedgeTakenCount(loop), builder),
                            builder.getInt64Ty(), "loop_count");
    //dbgs() << "LOOP COUNT " << *loopCount << "\n";
    //Value *maxLoopCount = builder.CreateAdd(loopCount,
                                    //builder.getInt64(1),
                                    //"max_loop_count");
    //dbgs() << "MAX LOOP COUNT " << *maxLoopCount << "\n";
    //step = builder.CreateMul(step, maxLoopCount, "scev_rec_step");
    step = builder.CreateMul(step, loopCount, "scev_rec_step");

    if (R->getStart()->isZero()) {
      //dbgs() << "AddRec " << *step << "\n";
      scevToValueMap[scev] = step;
      return step; 
    } else {
      Value *start = scevToValue(R->getStart(), builder);
      Value *add = builder.CreateAdd(start, step, "scev_rec_base");
      //dbgs() << "AddRec " << *add << "\n";
      scevToValueMap[scev] = add;
      return add;
    }

  } else if (const SCEVAddExpr *A = dyn_cast<SCEVAddExpr>(scev)) {
    
    SCEVNAryExpr::op_iterator it = A->op_begin(), end = A->op_end();
    Value *val = scevToValue(*(it++), builder);
    for (; it != end; it++ ) {
      val = builder.CreateAdd(val, scevToValue(*it, builder), "scev_add");
    }
    
    scevToValueMap[scev] = val;
    //dbgs() << "Add " << *val << "\n";
    return val;

  } else if (const SCEVMulExpr *M = dyn_cast<SCEVMulExpr>(scev)) {
    
    SCEVNAryExpr::op_iterator it = M->op_begin(), end = M->op_end();
    Value *val = scevToValue(*(it++), builder);
    for (; it != end; it++ ) {
      //dbgs() << "  ### " << **it << "\n";
      val = builder.CreateMul(val, scevToValue(*it, builder), "scev_mul");
    }
    
    scevToValueMap[scev] = val;
    //dbgs() << "Mul " << *val << "\n";
    return val;

  } else if (const SCEVSMaxExpr *S = dyn_cast<SCEVSMaxExpr>(scev)) {
    assert(S->getNumOperands() == 2 
           && "Found SMax expr with more than two operands");

    // Zero values can be ignored e.g. (0 smax %n)
    if (S->getOperand(0)->isZero()) {
      Value *val = scevToValue(S->getOperand(1), builder);
      scevToValueMap[scev] = val;
      return val;
    } else if (S->getOperand(1)->isZero()) {
      Value *val = scevToValue(S->getOperand(0), builder);
      scevToValueMap[scev] = val;
      return val;
    }

    Value *v0 = scevToValue(S->getOperand(0), builder);
    Value *v1 = scevToValue(S->getOperand(1), builder);

    Value *cmp = builder.CreateICmpSGT(v0, v1, "scev_smax_cmp");
    Value *sel = builder.CreateSelect(cmp, v0, v1, "scev_smax_sel");
     
    //dbgs() << "SMax " << *sel << "\n";
    scevToValueMap[scev] = sel;
    return sel;

  } else {
    dbgs() << "UNKOWN SCEV";
    scev->print(dbgs());
    assert(0 && "unknown scev value");
  }

}		/* -----  end of function scevToValue  ----- */



// Use the less equal comparison since we want to discard equal expressions
#define PRED_LT ICmpInst::ICMP_SLE
#define PRED_GT ICmpInst::ICMP_SGT
#define IS_LESS(s0, s1) SE->isKnownPredicate(PRED_LT, s0, s1)
#define IS_GREATER(s0, s1) SE->isKnownPredicate(PRED_GT, s0, s1)

/* 
 * ===  FUNCTION  ======================================================================
 *         Name:  createMinMaxAccessPair
 *  Description:  
 * =====================================================================================
 */
void RegionSpeculation::createMinMaxAccessPair(Value *baseValue,
                                               IRBuilder<> &builder,
                                               std::pair<Value*, Value*> &p) {
  assert(accessFunctions[baseValue].size()
         && "No access function for given base value");


  // List containing the possible minima and maxima (as scev values) 
  std::list<const SCEV*> minAccesses; 
  std::list<const SCEV*> maxAccesses; 
  std::list<const SCEV*>::iterator mit, Mit, mend, Mend;
  mend = minAccesses.end(); Mend = maxAccesses.end();

  std::set<const SCEV*>::iterator it, end;
  it  = accessFunctions[baseValue].begin();
  end = accessFunctions[baseValue].end();
  dbgs() << "@\t\t AccessFunctions for baseValue " << *baseValue 
         << " " << SE << "\n";
  for (; it != end; it++) {
    bool possibleMin = true, possibleMax = true;
    const SCEV *scev = *it;
    dbgs() << "@\t\t\t scev:" << scev << "   "  << *scev <<   "\n";
    if (const SCEVUnknown *U = dyn_cast<SCEVUnknown>(scev)) {
      Type *t;
      dbgs() << "@\t\t\t\t sizeof:" << U->isSizeOf(t) << "\n";
    }
    // Zero accesses can be ignored
    if (scev->isZero()) 
      continue;

    // Only negative (or zero) access values can be minimal accesses
    if (SE->isKnownNonPositive(scev))
      possibleMax = false;
    // Only positive (or zero) access values can be maximal accesses
    if (SE->isKnownNonNegative(scev))
      possibleMin = false;
 
    // Test all possible minima
    if (possibleMin) {
      for (mit = minAccesses.begin(); mit != mend; mit++) {
        if (IS_LESS(*mit, scev)) possibleMin = false;
        if (IS_GREATER(*mit, scev)) mit = minAccesses.erase(mit);
      }
      if (possibleMin) 
        minAccesses.push_back(scev);
    }

    // Test all possible maxima
    if (possibleMax) {
      for (mit = maxAccesses.begin(); mit != Mend; mit++) {
        if (IS_LESS(scev, *mit)) possibleMax = false;
        if (IS_GREATER(scev, *mit)) mit = maxAccesses.erase(mit);
      }
      if (possibleMax) 
        maxAccesses.push_back(scev);
    }
  }

  // Compute the minima and maxima during runtime. 
  //  -- iterate over all possibilities
  //  -- compute their values
  //  -- select the maxima/minima
  Value *baseValueAsInt64 = 0;
  const SCEV* baseValueSCEV = 0;

  // First try to find the value corresponding to the baseValue
  // in the scevToValueMap
  if (SE->isSCEVable(baseValue->getType())) {
    baseValueSCEV = SE->getSCEV(baseValue);
    std::map<const SCEV*, Value*>::iterator v = scevToValueMap.find(baseValueSCEV);
    if (v != scevToValueMap.end()) {
      baseValueAsInt64 = v->second;
    }
  } 

  if (!baseValueAsInt64) {
    if (baseValue->getType()->isPointerTy()) {
      baseValueAsInt64 = builder.CreatePtrToInt(baseValue, builder.getInt64Ty(),
                                                baseValue->getName() + "_64");
    } else {
      baseValueAsInt64 = builder.CreateSExtOrBitCast(baseValue, builder.getInt64Ty(),
                                                     baseValue->getName() + "_64");
    }
    // Save the extended baseValue for later use
    if (baseValueSCEV) 
      scevToValueMap[baseValueSCEV] = baseValueAsInt64;
  }
  
  dbgs() << "baseValueAsInt64 " << *baseValueAsInt64 << "\n";

  Value *val, *cmp;
  Value *currentMin, *currentMax;

  // Create the first minimal and maximal access
  mit = minAccesses.begin();
  Mit = maxAccesses.begin();
  

  // Compute the minimal access
  if (mit != mend) {
    currentMin = scevToValue(*(mit++), builder);
    dbgs() << "initial min "<< *currentMin <<  "\n";
    
    for (; mit != mend; mit++) {
      val = scevToValue(*mit, builder);
      cmp = builder.CreateICmpSLT(currentMin, val);
      currentMin = builder.CreateSelect(cmp, currentMin, val);
    }
    
    // Take the base value into account
    currentMin = builder.CreateAdd(currentMin, baseValueAsInt64);
    cmp = builder.CreateICmpSLT(currentMin, baseValueAsInt64, "min_check");
    currentMin = builder.CreateSelect(cmp, currentMin, baseValueAsInt64,
                                      baseValue->getName() + "min");
  } else {
    currentMin = baseValueAsInt64;
  } 

  // Compute the maximal access
  if (Mit != Mend) {
    currentMax = scevToValue(*(Mit++), builder);
    dbgs() << "initial max " << *currentMax << "\n";

    for (; Mit != Mend; Mit++) {
      val = scevToValue(*Mit, builder);
      cmp = builder.CreateICmpSGT(currentMax, val);
      currentMax = builder.CreateSelect(cmp, currentMax, val);
    }

    // Take the base value into account
    currentMax = builder.CreateAdd(currentMax, baseValueAsInt64);
    cmp = builder.CreateICmpSGT(currentMax, baseValueAsInt64, "max_check");
    currentMax = builder.CreateSelect(cmp, currentMax, baseValueAsInt64,
                                      baseValue->getName() + "max");
  } else {
    currentMax = baseValueAsInt64;
  } 

  dbgs() << "final min/max "<< *currentMin << " | " << *currentMax << "\n";
  // return the results 
  p.first  = currentMin;
  p.second = currentMax;
   
}		/* -----  end of function createMinMaxAccessPair  ----- */



/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  insertAliasChecks
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
void RegionSpeculation::insertAliasChecks(BasicBlock *BBAT, BasicBlock *entry) {
  dbgs() << "InsertAliasChecks in block " << BBAT->getName() << "\n\n";
  AliasSetTracker &AST = SD->detectionContext->AST;
  dbgs() << "InsertAliasChecks in block " << BBAT->getName() << "\n\n";
  
  assert(aliasingValues.size() 
         && "No aliasing values, thus no need to insert a check"); 

  assert(DT && "No dominatorTree available");
  
  dbgs() << "Entry is " << entry->getName() << "\n\n";

  // An iterator over the aliasing values
  std::map<Value*, std::pair<Instruction*, MDNode*> >::iterator avit;
  std::set<Value*> aliasingVals;
  // Insert aliasing pointers to the set of aliasing ints if they can be 
  // derived outside the loop. The set stores no pointers, instead the casted
  // integer values.
  for (avit = aliasingValues.begin(); avit != aliasingValues.end(); avit++) {
    Value *baseValue  = avit->first; 
    Instruction *inst = avit->second.first;
    MDNode *metadata  = avit->second.second;
  
    // Remove base values which are created by violating instructions, such as:
    // A[i][k] where A[i] is the base value, but not usable for any test
    if (violatingInstructions.count((Instruction *) baseValue)) {
      (dbgs() << "@\t\t == remove base value (violating instruction!) \n");
      continue;
    }

    (dbgs() << "@\t  -- Base value is " << *baseValue << "\n" );
    (dbgs() << "@\t  -- orig instruction is " << inst << "\n" );
    
    // Get the alias set
    AliasSet &AS = 
      AST.getAliasSetForPointer(baseValue, AliasAnalysis::UnknownSize,
                                metadata);
    // Which should not be empty (else the base value should not be in the 
    // aliasingValues set
    assert(!AS.empty() && " alias set is empty ");
     
    // Iterate over all values in in the alias set 
    for (AliasSet::iterator aliasSetIt = AS.begin(), aliasSetEnd = AS.end();
         aliasSetIt != aliasSetEnd; aliasSetIt++) {
      Value *aliasSetValue = aliasSetIt->getValue();

      // And check if they are not violating (see above)
      if (Instruction *I = dyn_cast<Instruction>(aliasSetValue)) {
        if (DT->dominates(entry, I->getParent())) {
          (dbgs() 
                << "@\t instruction is dominated by the check basic block\n"
                << "@\t\t --- " << *I << "\n");
          // This instruction/pointer can not be tested because it is not loop 
          // invariant
          continue;
        }
      } 
      
      assert(accessFunctions[aliasSetValue].size() 
             && "All aliasing values should have at least one access functions");

      // The value aliasSetValue is loop indipendant so we can use it for the 
      // alias tests
      (dbgs() << "@\t\t Insert aliasingVals: " << *aliasSetValue  <<"\n"); 
      aliasingVals.insert(aliasSetValue);
    }
  }
  
  aliasingValues.clear();
 
  if (aliasingVals.size() < 2) {
    (dbgs() << "@\t There are not enough pointers to compare \n");
    return;
  }

  // Old Values created from SCEVs cannot be used again, so a clean map is needed
  scevToValueMap.clear();

  // The builder for the alias test basic block 
  IRBuilder<> builder(BBAT, --(BBAT->end())); 
  
  // For each aliasing base value this list will contain the base value and
  // the access point from this base value such that the interval
  // [base value , access point] becomes maximal
  // e.g for (i = 0; i < n; i++) A[i] = B[i*3+2];
  // will result in:
  //    [(A, A+n), (B, B*n+2)]
  // TODO scevToValue will produce wrong maxima for 
  // e.g for (i = n - 1; i >= 0; i--) A[i] = B[i*3+2];
  std::list<std::pair<Value*, Value*> > aliasingInts;

  for (std::set<Value *>::iterator aliasingValue = aliasingVals.begin(); 
       aliasingValue != aliasingVals.end(); aliasingValue++){
      
    std::pair<Value*, Value*> p(0,0);
    createMinMaxAccessPair(*aliasingValue, builder, p);
    assert(p.first && p.second && "MinMax pair contains 0 values");
    dbgs() << "@\t\t\t\t P: " << *p.first << " | " << *p.second << "\n";
    aliasingInts.push_back(p);

  }

  // All pointers to check are in the map aliasingInts
  Value *result = 0;
  for (std::list<std::pair<Value*, Value*> >::iterator avIt = aliasingInts.begin(),
       avEnd = aliasingInts.end(); avIt != avEnd; avIt++){
    // Iterate over all coming values to check each against another
    for (std::list<std::pair<Value*, Value*> >::iterator oaIt(avIt);
         ++oaIt != avEnd;) {
      dbgs() << "@\t\t\t\t avit: " << *(*avIt).first << " | " << *(*avIt).second << "\n";
      dbgs() << "@\t\t\t\t oait: " << *(*oaIt).first << " | " << *(*oaIt).second << "\n";
      result = insertAliasCheck(BBAT, *avIt, *oaIt, result);
    }  
  }

  // After the code generation this terminator of BBAT can be changed to a
  // conditional branch to the new (speculative) parallelized version or to
  // the old non parallelized version 
  // TODO
  TerminatorInst *oldTerm = BBAT->getTerminator();

  BranchInst::Create(oldTerm->getSuccessor(0), entry,
                     result, BBAT);
  oldTerm->eraseFromParent();

  (dbgs() << "\n\n\n-----------------------------------------------\n\n");

}		/* -----  end of function insertAliasChecks  ----- */





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
  (dbgs() << "@\t Add violating instruction " << viol << " "<< *I << "\n");

  // Save the instruction in the list of violating ones
  violatingInstructions.insert(I);

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
  //RegionScoreKey RSK = std::make_pair(R->getEntry(), R->getExit());
  RegionScoreKey RSK = R;
  
  RegionScoreMap::iterator it;
  Region *tempRegion; 
  int regionScore = 0;

  // Save the currentRegion
  tempRegion    = currentRegion;
  // And set R as (temporary) new one
  currentRegion = R;
    
  DEBUG(dbgs() << "\n@\tCompute score for region "<<  R->getNameStr() << "\n");

  // Score this region as loop or conditional 
  if (regionIsLoop(R, SD->LI)) {
    DEBUG(dbgs() << "@\t-- which is a loop \n");
    regionScore += scoreLoop(R);
  } else {
    DEBUG(dbgs() << "@\t-- which is a conditional \n");
    regionScore += scoreConditional(R);
  }

  Function *func = R->getEntry()->getParent(); 
  // Save the score and leave 
  RegionScores[func][RSK] = regionScore;

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
 *         Name:  processRegion
 *  Description:  
 * =============================================================================
 */
void RegionSpeculation::processRegion( Region *R ) {
  (dbgs() << "\n@@@@# processRegion " << R->getNameStr() << " in " 
          << R->getEntry()->getParent()->getNameStr() << " \n");
  (dbgs() << "\n@\tPrepare region "<<  R->getNameStr() << "\n");
  
  // Clear the list of violating and replacement instructions
  loadInstructions.clear();
  storeInstructions.clear();
  violatingInstructionsMap.clear();
  violatingInstructions.clear();

  containsCalls = false;

  //RegionScoreKey RSK= std::make_pair(R->>getEntry(), R->getExit());
  RegionScoreKey RSK = R;
  
  if (preparedRegions.count(RSK) || R->getExit()->getName().startswith("polly")) {
    (dbgs() <<"@\t\t skipped region");
    (dbgs() << "\n\n-------------------------------------------------\n\n\n");
    return;
  } 
  preparedRegions.insert(RSK);
  
   
  // if gatherViolatingInstructions is set we are preparing the region right now
  assert (!SD->gatherViolatingInstructions &&
          "Called prepare Region during preparation");

  // We need to access the region later on to create the checks
  currentRegion = R;
  
  // Indicate that all violating instructions should be added by calling
  // addViolatingInstruction(Instruction *I)
  SD->gatherViolatingInstructions = true;
  
  // check the region again, but this time invalid instructions are gathered
  ScopDetection::DetectionContext Context(*R, *AA, false /*verifying*/);
  SD->isValidRegion(Context);

  // If the region should be prepared all violating instructions are replaced
  // else only information abaout this region are gathered
  if (SPollyPrepareRegions)
    replaceViolatingInstructions();

  // After the region is prepared we do not want to gather instructions anymore
  SD->gatherViolatingInstructions = false;

  (dbgs() << "\n@\t== Prepared region "<<  R->getNameStr() << "\n");
  
}		/* -----  end of function processRegion  ----- */



/* 
 * ===  FUNCTION  ==============================================================
 *         Name:   
 *  Description:  
 * =============================================================================
 */
bool RegionSpeculation::checksAvailable() {
  return (aliasingValues.size() || containsCalls);
}

/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  insertChecks 
 *  Description:  
 * =============================================================================
 */
void RegionSpeculation::insertChecks(BasicBlock *testBlock,
                                     BasicBlock *invariantProfilingBlock,
                                     BasicBlock *entry) {
  (dbgs() << "@$$$\n@$$$\n@$$$\n InsertChecks: " << aliasingValues.size() << "\n");
  // insert Alias checks
  if (aliasingValues.size()) {
    insertAliasChecks(testBlock, entry);
  }

  if (containsCalls && invariantProfilingBlock) {
    // This causes Polly assertions AffFunc 4 and CFG 1
    insertInvariantChecks(testBlock, invariantProfilingBlock);
  }

  (dbgs() << "@$$$\n@$$$\n@$$$\n");
}

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



/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  score 
 *    Arguments:  TODO old... The speculative valid Region &R
 *                The violation array (counter for each violation)
 *  Description:  This function is the entry point for the region speculation.
 *                If Pollys SCoP detections detects some SCoP which would be 
 *                valid except for the restrictions we speculate on, it calls
 *                this function.
 * =============================================================================
 */
int RegionSpeculation::scoreRegion(Region &R, int *v) {
  (dbgs() << "\n@@@@# scoreRegion " << R.getNameStr() <<" \n"); 
  if (SPollyDisabled) return false;
  
  Function *func = R.getEntry()->getParent(); 
  //RegionScoreKey RSK = std::make_pair(R.getEntry(), R.getExit());
  RegionScoreKey RSK = &R;
  if (RegionScores[func].count(RSK)) {
    return RegionScores[func][RSK];
  } 

  (dbgs() << "\n@\tSpeculate on region "<<  R.getNameStr() << "\n");
 
 
  violations = v;

  int i;
  // revert the violation count 
  for (i = 0; i < VIOLATION_COUNT; i++) {
    (dbgs() << "@i: " << i << "  v[i]: " << violations[i] << "\n");
    violations[i] = -violations[i];
  } 
  
  int score = scoreRegion(&R);

  // TODO change output file according to the current function
  if (SPollyDumpCandidates) {
    std::ofstream outfile (getFileName(&R).c_str(), std::ios_base::app);
    outfile << R.getEntry()->getParent()->getParent()->getModuleIdentifier() 
            << "\t\t" <<  R.getNameStr() << ":\t\t" << score << "\n";
    outfile.close();
  }
  
  // Sanity check 
  for (i = 0; i < VIOLATION_COUNT; i++) {
    (dbgs() << "@i: " << i << "  v[i]: " << violations[i] << "\n");
    assert(violations[i] == 0 
           && "All violations should be found in subRegions and BasicBlocks.");
  }
  
  return score;
}		/* -----  end of function speculateOnRegion  ----- */

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
    
    typedef RegionSpeculation::Violation Violation;
    typedef const Region * CRegionT;

    /// @brief The speculative valid region which is represented
    CRegionT R;

    /// @brief The scoreSCEV represents the score of the region
    const SCEV *ScoreSCEV;
    
    /// @brief A map of all memory accesses contained in this region
    //@{
    typedef DenseMap<const Instruction *, const SCEV *> MemoryAccessSet;
    typedef MemoryAccessSet::const_iterator MemoryAccess;
    MemoryAccessSet MemoryAccesses;
    //@}

    /// @brief A map of all violating contained in this region
    //@{
    typedef DenseMap<const Instruction *, Violation> ViolatingInstructionSet;
    typedef ViolatingInstructionSet::const_iterator ViolatingInstruction;
    ViolatingInstructionSet ViolatingInstructions;
    //@}

    public:
      /// @brief Default Constructor
      SPollyInfo(CRegionT R) : 
         R(R) {};
 
      /// @brief The default Destructor
      ~SPollyInfo() {};
 
      /// @brief Return the underlying speculative valid region
      CRegionT getRegion() const { return R; }
      
      /// @brief Create the ScoreSCEV representing the score of this region
      /// 
      /// The SCEV representing the score is parameterized. 
      /// It is build from information known during compile time and Unknown 
      /// values are added for information only known at runtime. 
      /// These information will be replaced by the @getScore function, thus 
      /// @getScore will create an integer value based on the created ScoreSCEV
      void createScoreSCEV(SCEVCreator * const Creator) {
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
      void registerMemoryAccess(const Instruction * const I,
                               const SCEV * const scev) {
        assert(I && scev && R->contains(I) && "Bad memory access");
        MemoryAccesses.insert(std::make_pair(I, scev));
      }
      

      /// @brief Register a violating instruction for this region
      void registerViolatingInstruction(const Instruction * const I,
                                        const Violation V) {
        assert(I && R->contains(I) && "Bad violating instruction");
        ViolatingInstructions.insert(std::make_pair(I, V));
      }
    
    
      /// @brief Pretty print all contained information 
      void print(raw_ostream &OS) {
        OS << "\n SPollyInfo for region " << R->getNameStr() << "\n";
        OS.indent(4) << " #MemoryAccesses: " << MemoryAccesses.size() << "\n";

        for (MemoryAccess it = MA_begin(),end = MA_end(); it != end; it++){
          OS.indent(8) << *(it->first) << "\t\t" << *(it->second) << "\n\n";
        }

        OS.indent(4) << " ScoreSCEV: " << *ScoreSCEV << "\n\n";
        
        OS.indent(4) << " #ViolatingInstructions: " 
                     << ViolatingInstructions.size() << "\n";
        for (ViolatingInstruction it = VI_begin(),end = VI_end();
             it != end; it++){
          OS.indent(8) << *(it->first) << "\t\t" << (it->second) << "\n";
        }


      }
     


  }; // end class SPollyInfo
} // end namespace polly


/// @brief Register a violating instruction for the current region 
void RegionSpeculation::registerViolatingInstruction(const Instruction* const I,
                                                     Violation V) { 
  assert(TemporaryRegion && "No TemporaryRegion to insert access");
  assert(TemporaryRegion->getRegion()->contains(I)
         && "Access is not contained in TemporaryRegion");

  TemporaryRegion->registerViolatingInstruction(I, V);
}


/// @brief Register a memory access for the current region (TemporaryRegion)
void RegionSpeculation::registerMemoryAccess(const Instruction * const I,
                                             const SCEV * const scev) {
  assert(TemporaryRegion && "No TemporaryRegion to insert access");
  assert(TemporaryRegion->getRegion()->contains(I)
         && "Access is not contained in TemporaryRegion");

  TemporaryRegion->registerMemoryAccess(I, scev);
}


/// @brief Store the associated SPollyInfo object for the given region
/// 
/// The SPollyInfo object from TemporaryRegion will be added
/// to the SpeculativeValidRegions map.
void RegionSpeculation::storeTemporaryRegion(CRegionT R) {
  (dbgs() << "*\t Store TemporaryRegion " << R->getNameStr() 
          << " in " << FunctionForRegion(R)->getNameStr() << "\n");


  assert(R == TemporaryRegion->getRegion()
         && "Region does not match TemporaryRegion");
  assert(!SpeculativeValidRegions.count(R)
         && "Region is already contained in SpeculativeValidRegions");
  

  // Finalize the TemporaryRegion
  TemporaryRegion->createScoreSCEV(Creator);

  SpeculativeValidRegions[R] = TemporaryRegion;
  
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
  

  assert(R == TemporaryRegion->getRegion()
         && "Cannot forget an unknown temporary region");
  assert(!SpeculativeValidRegions.count(R)
         && "Region cannot be temporary and speculative valid");
  
  delete TemporaryRegion;
  TemporaryRegion = 0;
}


/// @brief Create a new SPollyInfo object for the given region
/// 
/// The new created object is associated with the given region and stored as
/// TemporaryRegion
void RegionSpeculation::newTemporaryRegion(CRegionT R) {
  (dbgs() << "*\t New TemporaryRegion " << R->getNameStr() 
          << " in " << FunctionForRegion(R)->getNameStr() << "\n");

  assert(!TemporaryRegion && "There is already a TemporaryRegion");
  assert((!SpeculativeValidRegions.count(R)) 
         && "Region cannot be temporary and speculative valid");
 
  // Create a SpollyInfo object with the Region *R and the internal ScalarEvolution 
  TemporaryRegion = new SPollyInfo(R);
}


/// @brief Initialize the RegionSpeculation for a new ScopDetection run
/// 
/// Save the given analyses passes and init a new temporary map to match
/// violating instructions to speculative valid regions
void RegionSpeculation::initScopDetectionRun(
                          AliasAnalysis *aa, ScalarEvolution *se, 
                          LoopInfo *li, RegionInfo *ri, 
                          DominatorTree *dt, TargetData *td) {
  (dbgs() << "*\t Init ScopDetection run \n");

  // Save the given analyses
  assert(aa && se && li && ri && dt && td && "Analyses are not valid");
  AA = aa; SE = se; LI = li; RI = ri; DT = dt; TD = td; 

  // All TemporaryRegions should be saved or deleted 
  assert(!TemporaryRegion
         && "TemporaryRegion was not 0 during initialization");

  assert(!Creator && "SCEVCreator was already initialized");
  Creator = new SCEVCreator(SE, SPI_SE, LI, Profiler);
  
}

/// @brief Finalize the ScopDetection run 
/// 
///  - Forget the given analyses
void RegionSpeculation::finalizeScopDetectionRun() {
  (dbgs() << "*\t Finalyze ScopDetection run \n");
  
  // Forget the given analyses
  AA = 0; SE = 0; LI = 0; RI = 0; DT = 0; TD = 0;
  
  assert(Creator && "SCEVCreator was 0");

  delete Creator;
  Creator = 0;

  // All TemporaryRegions should be saved or deleted 
  assert(!TemporaryRegion
         && "TemporaryRegion was not 0 during finalization");
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
