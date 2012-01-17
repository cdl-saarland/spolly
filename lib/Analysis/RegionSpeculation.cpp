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
static int violationCosts[VIOLATION_COUNT] = { 2, 2, 2, 2 };

// How much is each instruction "worth"
#define INSTRUCTION_VALUE 4
#define ITERATION_TRESHOLD 10

using namespace llvm;
using namespace polly;

static cl::opt<bool>
SPollyDumpCandidates("spolly-dump",
       cl::desc("Dump all speculative candidates"),
       cl::Hidden,
       cl::value_desc("Dump all speculative candidates"),
       cl::init(false));

static cl::opt<bool>
SPollyProbabilityOnbranch0("spolly-prob-br0",
       cl::desc(""),
       cl::Hidden,
       cl::value_desc(""),
       cl::init(false));

static cl::opt<bool>
SPollyProbabilityOnbranch1("spolly-prob-br1",
       cl::desc(""),
       cl::Hidden,
       cl::value_desc(""),
       cl::init(false));


static cl::opt<bool>
SPollyViolationProbabilityHigh("spolly-viol-high",
       cl::desc(""),
       cl::Hidden,
       cl::value_desc(""),
       cl::init(false));

static cl::opt<bool>
SPollyViolationProbabilityLow("spolly-viol-low",
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
static int exPerc = -1;
static int getExecutionProbability(BasicBlock *B) {
  if (exPerc == -1) {
    if (SPollyProbabilityOnbranch0)
      exPerc = 10;
    else if (SPollyProbabilityOnbranch1)
      exPerc = 90;
    else
      exPerc = 50;
  } 

  return (exPerc = 100 - exPerc);
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
 *  Description:  
 * =============================================================================
 */
static inline int getLoopIterationCount(Region *R) {
  // -1 to indicate no information available 
  return 20;
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
 *    Arguments:
 *      Returns:  
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
 *    Arguments:
 *      Returns:  
 *  Description: 
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
  // 
  if (iterationCount > 0) {
    
    // Test if it is worth to speculativelly parallelize this loop since 
    if (iterationCount < ITERATION_TRESHOLD) {
      // The loopCount was under the treshold, so stop speculating
      return - (1 << 20);
    }
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
 *    Arguments:
 *      Returns:  
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
  int probability;
  
  exit  = R->getExit();
  entry = R->getEntry(); 
  entryScore = scoreBasicBlock(entry);


  TerminatorInst *guard = entry->getTerminator();
  assert(guard->getNumSuccessors() == 2 
         && "Branch with two successors expected");

  branch0 = guard->getSuccessor(0);
  branch1  = guard->getSuccessor(1);
 
  probability = getExecutionProbability(branch0);
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
  br0Score = (br0Score * probability) / (101 - probability);

  // probability = 100 - probability 
  probability = getExecutionProbability(branch1); 
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
  br1Score = (br1Score * probability) / (101 - probability);

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

  // Handle all subregions and basicBlocks within this region
  //for (Region::element_iterator bb = R->element_begin(), be = R->element_end();
       //bb != be; ++bb) {

    //if ((*bb)->isSubRegion()) {
      //DEBUG(dbgs() << "@\t-- and the subregion " << 
            //(*bb)->getNodeAs<Region>()->getNameStr() << " \n");
      //regionScore += scoreRegion((*bb)->getNodeAs<Region>());
    //} else {
      //DEBUG(dbgs() << "@\t-- and the BasicBlock " << 
            //(*bb)->getNodeAs<BasicBlock>()->getName() << " \n");
      //score += scoreBasicBlock((*bb)->getNodeAs<BasicBlock>());
    //}

  //}
 
  // Score the exit block of the region 
  //exitScore = scoreBasicBlock(R->getExit());
  
  //regionScore += exitScore;

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

  return score > 200;
}		/* -----  end of function speculateOnRegion  ----- */



