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
#include <list>

using namespace llvm;

namespace llvm {
  class Loop;
  class BasicBlock;
  class Region;
  class Instruction;
  class CallInst;
  class Function;
  class Value;
}

namespace polly {
  
class ScopDetection;

//===----------------------------------------------------------------------===//
/// @brief Speculate on SCoPs
class RegionSpeculation {

  ScopDetection *SD;
  Function *func;

  std::list<Instruction*> violatingInstructions; 
  std::list<Instruction*> replacementInstructions; 

  int* violations;
  Region *currentRegion;

  bool regionIsLoop(Region *R);

  int scoreBasicBlock(BasicBlock *B);

  int scoreLoop(Region *R);

  int scoreConditional(Region *R);

  int scoreRegion(Region *R);

  int getLoopIterationCount(Region *R);
  
  void replaceViolatingInstructions(Region &R);

  Value *insertPseudoInstructionsPre(Region &R);

  CallInst *createCall(Instruction *I);

  typedef std::pair<BasicBlock*, BasicBlock*> RegionScoreKey;
  typedef std::map<RegionScoreKey, int> RegionScoreMap;
  RegionScoreMap RegionScores;

public:
  RegionSpeculation(ScopDetection *SD) : SD(SD) {};

  void prepareRegion( Region &R );
  
  bool speculateOnRegion(Region &R, int *violations);

  void setFunction(Function &F) { func = &F; };

  void addViolatingInstruction(Instruction *I);

};

} //end namespace polly


#endif
