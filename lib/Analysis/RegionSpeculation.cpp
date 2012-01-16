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

using namespace llvm;
using namespace polly;

static cl::opt<bool>
SPollyDumpCandidates("spolly-dump",
       cl::desc("Dump all speculative candidates"),
       cl::Hidden,
       cl::value_desc("Dump all speculative candidates"),
       cl::init(false));


bool RegionSpeculation::regionIsLoop(Region *R) {
  RegionScoreKey RSK= std::make_pair(R->getEntry(), R->getExit());

  return (LI->getLoopDepth(RSK.first) - LI->getLoopDepth(RSK.second));
}

int RegionSpeculation::scoreBasicBlock(BasicBlock *B, int *&violations) {
  return 0;
}

int RegionSpeculation::scoreLoop(Region *R, int *&violations) {
  return 0;
}

int RegionSpeculation::scoreConditional(Region *R, int *&violations) {
  Region *tempRegion; 
  BasicBlock *consequent, *alternative;
  int consScore, altScore;
  

#if 0
  ScopDetection::DetectionContext Context(*R, *(AA), false /*verifying*/);
  if ((tempRegion = RI->getRegionFor(consequent)) == R) {
    // The consequent is just one BasicBlock   
    DEBUG(dbgs() << "  @@@@@@@@@@@  " <<
          SD->isValidBasicBlock(consequent, Context) 
          << "\n");

  } else {
    // The consequent contains another region

  }
#endif

  return 0;

}


int RegionSpeculation::scoreRegion(Region *R, int *&violations) {
  RegionScoreKey RSK= std::make_pair(R->getEntry(), R->getExit());
  RegionScoreMap::iterator it;
  int i, score = 0;
    
  DEBUG(dbgs() << "\n\nCompute score of "<<  R->getNameStr() << "\n");


  // TODO update parent Region if in RegionScores
  //if ((it = RegionScores.find(RSK)) != RegionScores.end()) {
  //} 
    
    
  // Score this region as loop or conditional 
  if (regionIsLoop(R)) {
    DEBUG(dbgs() << "\t-- which is a loop \n");
    score += scoreLoop(R, violations);
  } else {
    DEBUG(dbgs() << "\t-- which is a conditional \n");
    score += scoreConditional(R, violations);
  }

  // Handle all subregions and basicBlocks within this region
  for (Region::element_iterator bb = R->element_begin(), be = R->element_end();
       bb != be; ++bb) {
    if ((*bb)->isSubRegion()) {
      DEBUG(dbgs() <<  (*bb)->getNodeAs<Region>()->getNameStr() << "\n");
      if (!regionIsLoop((*bb)->getNodeAs<Region>()))
        score += scoreRegion((*bb)->getNodeAs<Region>(), violations);

    } else {
      DEBUG(dbgs() <<  (*bb)->getNodeAs<BasicBlock>()->getName() << "  (" << 
           ((*bb)->getNodeAs<BasicBlock>()->size()) << ")\n");
      score += scoreBasicBlock((*bb)->getNodeAs<BasicBlock>(), violations);
    }
  }
  
 
  // Sanity check 
  for (i = 1; i < VIOLATION_COUNT; i++) {
    assert(violations[i] == 0 
           && "All violations should be found in subRegions and BasicBlocks.");
  }


  // Save the score and leave 
  RegionScores[RSK] = score;

  return score;
}

bool RegionSpeculation::speculateOnRegion(Region &R, int *violations) {
  
  int score = scoreRegion(&R, violations);

  // TODO change output file according to the current function
  if (SPollyDumpCandidates) {
    std::ofstream outfile ("speculativeRegions", std::ios_base::app);
    outfile << R.getNameStr() << ":\t\t" << score << "\n";
    outfile.close();
  }
  
  return score > 200;
}


