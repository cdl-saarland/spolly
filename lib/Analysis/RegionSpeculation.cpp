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

#define DEBUG_TYPE "spolly-detect"
#include "llvm/Support/Debug.h"

// Use the analysis results of the ScopDetection
#define AA SD->AA
#define RI SD->RI
#define LI SD->LI
#define SE SD->SE

#define VIOLATION_COUNT 4
static int violationCosts[VIOLATION_COUNT] = { 1, 1, 10, 1 };

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
static int violPerc = -1;
static int getViolationProbability(Region *R) {
  if (violPerc == -1) {
    if (SPollyViolationProbabilityHigh)
     violPerc = 10000;
    else if (SPollyViolationProbabilityLow)
     violPerc = 1;
    else
     violPerc = 20;
  } 

  // FIXME add profiling information here

  return violPerc;
}		/* -----  end of function getViolationProbability  ----- */





/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  getExecutionProbability
 *  Description:  
 * =============================================================================
 */
static int getExecutionProbability(BasicBlock *B) {
  int exPerc;

  // Test whether we are within a branch or not
  if (withinBranch) {
    exPerc = 50;
  } else {
    exPerc = 100;
  }
  
  // FIXME use profiling information here
   
  return exPerc;
}		/* -----  end of function getExecutionProbability  ----- */



/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  calculateScoreFromViolations
 *  Description:  
 * =============================================================================
 */
static inline int calculateScoreFromViolations(int *v, Region *R) {
  int score = 0;
  for (int i = 0; i < VIOLATION_COUNT; i++) {
    score += v[i] * violationCosts[i];
  }
  
  score *= getViolationProbability(R);

  return score;
}		/* -----  end of function calculateScoreFromViolations  ----- */




/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  getLoopIterationCount 
 *     Argument:  Region *R
 *  Description:  Return the iteration Count of the Region R or 
 *                ITERATIONCOUNTCONSTANT if not available 
 * =============================================================================
 */
int RegionSpeculation::getLoopIterationCount(Region *R) {
  Loop *loop = LI->getLoopFor(R->getEntry());
  
  
  unsigned iterationCount = loop->getSmallConstantTripCount();
  
  DEBUG(dbgs() << "@\t    -- Loop " << R->getNameStr() << " has iteration count " 
               << iterationCount << "\n");
  DEBUG(dbgs() << "@\t   ------ " << SE->hasLoopInvariantBackedgeTakenCount(loop)
               << "   " << SE->getBackedgeTakenCount(loop)  
               << "\n");

  if (iterationCount == 0) {
    // FIXME test if profiling information is available
    return ITERATIONCOUNTCONSTANT;
  } else {
    return iterationCount;
  }
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
 *         Name:  addViolatingInstruction 
 *    Arguments:  A violating Instruction I
 *  Description:  Add the Instruction I to the list of all violating
 *                instructions. If this Region should be executed speculatively
 *                the replaceViolatingInstructions call will replace it with 
 *                a unique function call
 * =============================================================================
 */
void RegionSpeculation::addViolatingInstruction(Instruction *I) {
  DEBUG(dbgs() << "@\t Add violating instruction " << I << " "<< *I << "\n");

  // Save the instruction in the list of violating ones
  violatingInstructions.push_back(I);

  // The corresponding call is created as needed
}		/* -----  end of function addViolatingInstruction  ----- */






/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  insertPseudoInstructionsPre
 *  Description:  
 * =============================================================================
 */
Value *RegionSpeculation::insertPseudoInstructionsPre(Region &R) {

  DEBUG(dbgs() << "@\tInsertPseudoSum in block "
        << R.getEntry()->getNameStr() << "\n");

  LLVMContext &context = getGlobalContext();
  Type *int32 = Type::getInt32Ty(context);

  IRBuilder<> builder(R.getEntry());
  Value *pseudoSum = builder.Insert(Constant::getNullValue(int32));
  
  return pseudoSum;
}		/* -----  end of function insertPseudoInstructionsPre  ----- */






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

  DEBUG(dbgs() << "\n\n" << *I << "\n\n");
  // The IRBuilder for the basic block with the violating instruction
  //IRBuilder<> builder(context);
  //Module *M = builder.GetInsertBlock()->getParent()->getParent();
  Module *M = I->getParent()->getParent()->getParent();
  
  DEBUG(dbgs() << "\n\n" << *I << "\n\n");
  DEBUG(dbgs() << *I->getType() << "\t" << I->getNumOperands() << "\n"
        << *I->getOperand(0));
  
  unsigned argsC = I->getNumOperands();

  // Remove the called function operand from call instructions
  if (I->getOpcode() == Instruction::Call) {
    argsC -= 1;
  }
  
  DEBUG(dbgs() << "\n\n" << *I << "\n\n");

  std::vector<Type *> argsT(argsC);
  std::vector<Value *> argsV(argsC);
  for (unsigned i = 0; i < argsC; i++) {
    argsV[i] = I->getOperand(i);
    argsT[i] = I->getOperand(i)->getType();
  }
  
  DEBUG(dbgs() << "\n\n" << *I << "\n\n");
  // Create the function which has the same return type as the instruction
  // and uses the same operands as the instruction (as arguments)
  FT = FunctionType::get(I->getType(), argsT, false);
  FN = Function::Create(FT, Function::ExternalLinkage,
                        "spolly_call", M);

  DEBUG(dbgs() << "\n\n" << *I << "\n\n");
  ArrayRef<Value*> Args(argsV);
  //callInst = builder.CreateCall(FN, Args); 
  callInst = CallInst::Create(FN, Args);

  // Set some attributes to allow Polly to handle this function
  FN->setDoesNotThrow(true);
  FN->setDoesNotReturn(false);

  // TODO see ScopDetection::isValidCallInst
  //FN->setOnlyReadsMemory(true);
  //FN->setDoesNotAccessMemory(true);


  DEBUG(dbgs() << "\n\n" << *I << "\n\n");

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
  DEBUG(dbgs() << "@\t Replace violating instructions "<< "\n");
  std::list<Instruction*>::iterator vIit;

  CallInst *callInst;
  
  // foreach violating instruction
  for (vIit = violatingInstructions.begin(); vIit != violatingInstructions.end();
       vIit++) {
    // create the corresponding call instruction and add it to
    // the replacementInstructions list
    DEBUG(dbgs() << "@\t\t replace " << (**vIit) << "\n");
    //DEBUG(dbgs() << " " << (**vIit)) << "\n";
  
    if (SPollyRemoveViolatingInstructions) {
      (*vIit)->eraseFromParent(); 
    } else {
      callInst = createCall(*vIit);
    }
    
    assert(callInst && "Replacement call is NULL");

    DEBUG(dbgs() << "@\t\t with " << (*callInst) << "\n");
    
    // Save the call in the replacementInstructions list
    // #x of violatingInstructions <<==>> #x of replacementInstructions
    replacementInstructions.push_back(callInst);
    
    // Replace the violating instruction with the created call 
    //callInst->moveBefore(*vIit);
    //(*vIit)->replaceAllUsesWith(callInst);
    ReplaceInstWithInst((*vIit), callInst);
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
  int blockScore = calculateScoreFromViolations(violations, currentRegion);

  DEBUG(dbgs() << "@\t    Computing score of the BasicBlock " 
        << B->getName() << " \n");

  // Add INSTRUCTIONVALUE per instruction in the BasicBlock
  blockScore += B->size() * INSTRUCTION_VALUE;

  ScopDetection::DetectionContext Context(*currentRegion, *(AA),
                                          false /*verifying*/);
  SD->isValidBasicBlock(*B, Context);

  // This will take all violations within this block into account
  blockScore -= calculateScoreFromViolations(violations, currentRegion);

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
 * ===  FUNCTION  ==============================================================
 *         Name:  prepareRegion
 *  Description:  
 * =============================================================================
 */
void RegionSpeculation::prepareRegion( Region &R ) {
  DEBUG(dbgs() << "\n@\tPrepare region "<<  R.getNameStr() << "\n");

  // if gatherViolatingInstructions is set we are preparing the region right now
  assert (!SD->gatherViolatingInstructions &&
          "Called prepare Region during preparation");

  // Indicate that all violating instructions should be added by calling
  // addViolatingInstruction(Instruction *I)
  SD->gatherViolatingInstructions = true;
  
  // Clear the list of violating and replacement instructions
  violatingInstructions.clear();
  replacementInstructions.clear();

  // check the region again, but this time invalid instructions are gathered
  ScopDetection::DetectionContext Context(R, *AA, false /*verifying*/);
  SD->isValidRegion(Context);

  // replace the gathered instructions
  replaceViolatingInstructions(R);

  // After the region is prepared we do not want to gather instructions anymore
  SD->gatherViolatingInstructions = false;

  DEBUG(dbgs() << "\n@\t== Prepared region "<<  R.getNameStr() << "\n");
  
}		/* -----  end of function prepareRegion  ----- */




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
  DEBUG(dbgs() << "\n@\tSpeculate on region "<<  R.getNameStr() << "\n");

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
    outfile << func << R.getNameStr() << ":\t\t" << score << "\n";
    outfile.close();
  }
  
  // Sanity check 
  for (i = 0; i < VIOLATION_COUNT; i++) {
    DEBUG(dbgs() << "@i: " << i << "  v[i]: " << violations[i] << "\n");
    //assert(violations[i] == 0 
           //&& "All violations should be found in subRegions and BasicBlocks.");
  }

  // TODO remove me
  prepareRegion(R);
  //return false;
  return true;

  //return score > SPECULATIVETRESHOLD;
}		/* -----  end of function speculateOnRegion  ----- */



