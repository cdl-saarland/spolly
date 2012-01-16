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

#ifndef POLLY_REGION_SPECULATION_H
#define POLLY_REGION_SPECULATION_H

#include "llvm/Support/CommandLine.h"

#include <map>

using namespace llvm;

namespace llvm {
  class BasicBlock;
  class Region;
  class Function;
}

namespace polly {
  
class ScopDetection;

//===----------------------------------------------------------------------===//
/// @brief Speculate on SCoPs
class RegionSpeculation {

  ScopDetection *SD;
  Function *func;

  bool regionIsLoop(Region *R);

  int scoreBasicBlock(BasicBlock *B, int *&violations);

  int scoreLoop(Region *R, int *&violations);

  int scoreConditional(Region *R, int *&violations);

  int scoreRegion(Region *R, int *&violations);
  
  typedef std::pair<BasicBlock*, BasicBlock*> RegionScoreKey;
  typedef std::map<RegionScoreKey, int> RegionScoreMap;
  RegionScoreMap RegionScores;

public:
  RegionSpeculation(ScopDetection *SD) : SD(SD) {};

  bool speculateOnRegion(Region &R, int *violations);

  void setFunction(Function &F) { func = &F; };

};

} //end namespace polly


#endif
