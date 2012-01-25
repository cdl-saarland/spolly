//===--- RegionSpeculation.h - Create Speculative Information -----*- C++ -*-===//
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
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/RegionIterator.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Assembly/Writer.h"

#define DEBUG_TYPE "spolly-detect"
#include "llvm/Support/Debug.h"

// Use the analysis results of the ScopDetection
#define AA SD->AA
#define RI SD->RI
#define LI SD->LI

#define VIOLATION_COUNT 4
static int violationCosts[VIOLATION_COUNT] = { 1, 1, 1, 1 };

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
SPollyDumpCandidates("spolly-dump",
       cl::desc("Dump all speculative candidates"),
       cl::Hidden,
       cl::value_desc("Dump all speculative candidates"),
       cl::init(false));

static cl::opt<bool>
SPollyBranchWorst("spolly-branch-worst",
       cl::desc(""),
       cl::Hidden,
       cl::value_desc(""),
       cl::init(false));

static cl::opt<bool>
SPollyBranchBest("spolly-branch-best",
       cl::desc(""),
       cl::Hidden,
       cl::value_desc(""),
       cl::init(false));


static cl::opt<bool>
SPollyViolationProbabilityHigh("spolly-violation-high",
       cl::desc(""),
       cl::Hidden,
       cl::value_desc(""),
       cl::init(false));

static cl::opt<bool>
SPollyViolationProbabilityLow("spolly-violation-low",
       cl::desc("TODO"),
       cl::Hidden,
       cl::value_desc("TODO"),
       cl::init(false));


/* 
 * ===  FUNCTION  ======================================================================
 *         Name:  getFileName 
 *  Description:  
 * =====================================================================================
 */
static std::string getFileName(Region *R) {
  std::string FunctionName =
    R->getEntry()->getParent()->getName();
  std::string FileName = "spolly_" + FunctionName + ".score";
  return FileName;
}




/* 
 * ===  FUNCTION  ======================================================================
 *         Name:  getViolationProbability
 *  Description:  
 * =====================================================================================
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

  return violPerc;
}		/* -----  end of function getViolationProbability  ----- */





/* 
 * ===  FUNCTION  ======================================================================
 *         Name:  getExecutionProbability
 *  Description:  
 * =====================================================================================
 */
static int getExecutionProbability(BasicBlock *B) {
  int exPerc = 50;

  // TODO 
  // use profiling information here
   
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
static inline int getLoopIterationCount(Region *R) {
  Loop *loop = LI->getLoopFor(R->getEntry());
  unsigned iterationCount = loop->getSmallConstantTripCount()
  
  if (iterationCount == 0) {
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
  
  assume(iterationCount > 0 && "invalid iteration count");

    
  // Test if it is worth to speculativelly parallelize this loop since 
  if (iterationCount < ITERATION_TRESHOLD) {
    // The loopCount was under the treshold, so stop speculating
    return - (1 << 20);
  }

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

  // Use the iteration count if available and high enough to influence 
  if (iterationCount > 0) 
    loopScore *= iterationCount;

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
 * | I branch1 I             I br0quent I  |  scores, we use profiling data
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
      branch0 = branch0->getTerminator()->getSuccessor(0);
    } else {
      // The branch0 is contained in another region
      br0Score += scoreRegion(tempRegion);
      branch0 = tempRegion->getExit();
    }
  }

  // probability1 = 100 - probability0 
  probability1 = getExecutionProbability(branch1); 
  while (branch1 != exit) {
    if ((tempRegion = RI->getRegionFor(branch1)) == R) {
      // The branch1 is just one BasicBlock   
      br1Score   += scoreBasicBlock(branch1);
      branch1 = branch1->getTerminator()->getSuccessor(0);
    } else {
      // The branch1 contains another region
      br1Score   += scoreRegion(tempRegion);
      branch1 = tempRegion->getExit();
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

  DEBUG(dbgs() << "@\t  -- Conditional score is " << conditionalScore << " \n");
  return conditionalScore;

}		/* -----  end of function scoreConditional  ----- */





/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  scoreRegion
 *    Arguments:
 *      Returns:  
 *
 *  -----------------------------------------
 *  |                                       |
 *  |                                       |
 *  |                                       |
 *  |                                       |
 *  |                                       |
 *  |                                       |
 *  |                                       |
 *  -----------------------------------------
 *
 * =============================================================================
 */
int RegionSpeculation::scoreRegion(Region *R) {
  RegionScoreKey RSK= std::make_pair(R->getEntry(), R->getExit());
  RegionScoreMap::iterator it;
  Region *tempRegion; 
  int regionScore = 0, exitScore = 0;

  tempRegion    = currentRegion;
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

  currentRegion = tempRegion;
  
  DEBUG(dbgs() << "@\t-- Region score is " << regionScore << " \n");

  return regionScore;
}		/* -----  end of function scoreRegion  ----- */





/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  speculateOnRegion
 *  Description:  
 * =============================================================================
 */
bool RegionSpeculation::speculateOnRegion(Region &R, int *v) {
  int i;

  violations = v;

  // revert the violation count 
  for (i = 0; i < VIOLATION_COUNT; i++) {
    DEBUG(dbgs() << "@i: " << i << "  v[i]: " << violations[i] << "\n");
    violations[i] = -violations[i];
  } 
  
  int score = scoreRegion(&R);

  // TODO change output file according to the current function
  if (SPollyDumpCandidates) {
    std::ofstream outfile (getFileName(&R).c_str(), std::ios_base::app);
    outfile << R.getNameStr() << ":\t\t" << score << "\n";
    outfile.close();
  }
  
  // Sanity check 
  for (i = 0; i < VIOLATION_COUNT; i++) {
    DEBUG(dbgs() << "@i: " << i << "  v[i]: " << violations[i] << "\n");
    //assert(violations[i] == 0 
           //&& "All violations should be found in subRegions and BasicBlocks.");
  }

  return score > SPECULATIVETRESHOLD;
}		/* -----  end of function speculateOnRegion  ----- */



