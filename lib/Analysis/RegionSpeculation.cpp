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
static int violationCosts[VIOLATION_COUNT] = { 10, 10, 10, 10 };

#define INSTRUCTION_VALUE 2


using namespace llvm;
using namespace polly;

static cl::opt<bool>
SPollyDumpCandidates("spolly-dump",
       cl::desc("Dump all speculative candidates"),
       cl::Hidden,
       cl::value_desc("Dump all speculative candidates"),
       cl::init(false));




/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  calculateScoreFromViolations
 *  Description:  
 * =============================================================================
 */
static inline int calculateScoreFromViolations(int *v) {
  int score = 0;
  for (int i = 0; i < VIOLATION_COUNT; i++) {
    score += v[i] * violationCosts[i];
  }
  return score;
}		/* -----  end of function calculateScoreFromViolations  ----- */





/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  regionIsLoop
 *  Description:  
 * =============================================================================
 */
bool RegionSpeculation::regionIsLoop(Region *R) {
  RegionScoreKey RSK= std::make_pair(R->getEntry(), R->getExit());

  return (LI->getLoopDepth(RSK.first) - LI->getLoopDepth(RSK.second));
}		/* -----  end of function regionIsLoop  ----- */





/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  scoreBasicBlock
 *  Description:  
 * =============================================================================
 */
int RegionSpeculation::scoreBasicBlock(BasicBlock *B) {

  // Start with an initial value which is not accurate for this block
  // but in the end all violations not contained in this block are substracted
  int blockScore = calculateScoreFromViolations(violations);

  DEBUG(dbgs() << "@\t    Computing score of the BasicBlock " 
        << B->getName() << " \n");

  // Add INSTRUCTIONVALUE per instruction in the BasicBlock
  blockScore += B->size() * INSTRUCTION_VALUE;

  ScopDetection::DetectionContext Context(*currentRegion, *(AA),
                                          false /*verifying*/);
  SD->isValidBasicBlock(*B, Context);

  // This will take all violations within this block into account
  blockScore -= calculateScoreFromViolations(violations);

  DEBUG(dbgs() << "@\t    -- blockScore is " << blockScore << " \n");
  return blockScore;
}		/* -----  end of function scoreBasicBlock  ----- */





/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  scoreLoop
 *  Description:  
 * =============================================================================
 */
int RegionSpeculation::scoreLoop(Loop *L) {
  int score = 0;



  DEBUG(dbgs() << "@\t  -- Loop score is " << score << " \n");
  return score;
}		/* -----  end of function scoreLoop  ----- */





/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  scoreConditional
 *  Description:  
 * =============================================================================
 */
int RegionSpeculation::scoreConditional(Region *R) {
  Region *tempRegion; 
  BasicBlock *consequent, *alternative, *guard;
  int conditionalScore = 0, guardScore = 0, consScore = 0, altScore = 0;
  
  guard = R->getEntry(); 
  guardScore = scoreBasicBlock(guard);

  TerminatorInst *branch = guard->getTerminator();

  assert(branch->getNumSuccessors() == 2 
         && "Branch with two successors expected");

  consequent  = branch->getSuccessor(0);
  alternative = branch->getSuccessor(1);
 
  // TODO check if there is a real consequence and alternative 
  if (true) {
/*-----------------------------------------------------------------------------
 *             ---------
 *             | guard |
 *             ---------
 *               |   |
 *      |-- no --|   |-- yes --|
 *      |                      V 
 *      |                  -------------
 *     ???                 | consquent | << This block exists
 *      |                  -------------
 *      |                      |
 *      |      ---------       |
 *      |----->|       |<------|
 *             ---------
 *-----------------------------------------------------------------------------*/
    if ((tempRegion = RI->getRegionFor(consequent)) == R) {
      // The consequent is just one BasicBlock   
      consScore = scoreBasicBlock(consequent);
    } else {
      // The consequent contains another region
      consScore = scoreRegion(tempRegion);
    }
  }

  // TODO check if there is a real consequence and alternative 
  if (true) {
/*-----------------------------------------------------------------------------
 *             ---------
 *             | guard |
 *             ---------
 *               |   |
 *      |-- no --|   |-- yes -------------------|
 *      V                                       | 
 * ---------------                              |
 * | alternative | << This block exists        ???
 * ---------------                              |
 *      |                                       |
 *      |      ---------                        |
 *      |----->|       |<-----------------------|
 *             ---------
 *-----------------------------------------------------------------------------*/
    if ((tempRegion = RI->getRegionFor(alternative)) == R) {
      // The alternative is just one BasicBlock   
      altScore = scoreBasicBlock(alternative);
    } else {
      // The alternative contains another region
      altScore = scoreRegion(tempRegion);
    }
  }


  DEBUG(dbgs() << "@\t  -- Conditional score is " << conditionalScore << " \n");
  return conditionalScore;

}		/* -----  end of function scoreConditional  ----- */





/* 
 * ===  FUNCTION  ==============================================================
 *         Name:  scoreRegion
 *  Description:  
 * =============================================================================
 */
int RegionSpeculation::scoreRegion(Region *R) {
  RegionScoreKey RSK= std::make_pair(R->getEntry(), R->getExit());
  RegionScoreMap::iterator it;
  Region *tempRegion; 
  int i, regionScore = 0, exitScore = 0;

  tempRegion    = currentRegion;
  currentRegion = R;
    
  DEBUG(dbgs() << "\n@\tCompute score for region "<<  R->getNameStr() << "\n");

    
  // Score this region as loop or conditional 
  if (regionIsLoop(R)) {
    DEBUG(dbgs() << "@\t-- which is a loop \n");
    regionScore += scoreLoop(LI->getLoopFor(RSK.first));
  } else {
    DEBUG(dbgs() << "@\t-- which is a conditional \n");
    regionScore += scoreConditional(R);
  }

  // Handle all subregions and basicBlocks within this region
  for (Region::element_iterator bb = R->element_begin(), be = R->element_end();
       bb != be; ++bb) {

    if ((*bb)->isSubRegion()) {
      DEBUG(dbgs() << "@\t-- and the subregion " << 
            (*bb)->getNodeAs<Region>()->getNameStr() << " \n");
      regionScore += scoreRegion((*bb)->getNodeAs<Region>());
    } else {
      //DEBUG(dbgs() << "@\t-- and the BasicBlock " << 
            //(*bb)->getNodeAs<BasicBlock>()->getName() << " \n");
      //score += scoreBasicBlock((*bb)->getNodeAs<BasicBlock>());
    }

  }
 
  // Score the exit block of the region 
  exitScore = scoreBasicBlock(R->getExit());
  

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
    std::ofstream outfile ("speculativeRegions", std::ios_base::app);
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



