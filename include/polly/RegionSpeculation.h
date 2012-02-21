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
#include <set>

#define VIOLATION_COUNT 4

using namespace llvm;

namespace llvm {
  class Loop;
  class BasicBlock;
  class Region;
  class Instruction;
  class CallInst;
  class Function;
  class Value;
  class AliasSet;
  class SCEV;
}

namespace polly {
  
class ScopDetection;

//===----------------------------------------------------------------------===//
/// @brief Speculate on SCoPs
class RegionSpeculation {

  ScopDetection *SD;
  Function *func;
 

  std::set<Value*> loadInstructions;
  std::set<Value*> storeInstructions;
  void insertInvariantChecks(BasicBlock *BBAT);

  std::map<Instruction*, Instruction*> violatingInstructions; 
  std::map<Value*, Instruction*> aliasingValues;

  int getExecutionProbability(BasicBlock *B);

  int getViolationProbability(BasicBlock *B, Region *R);

  void collectAliasSets(Instruction *I);

  int calculateScoreFromViolations(BasicBlock *B, int *v, Region *R);

  int* violations;
  Region *currentRegion;

  bool regionIsLoop(Region *R);

  int scoreBasicBlock(BasicBlock *B);

  int scoreLoop(Region *R);

  int scoreConditional(Region *R);

  int scoreRegion(Region *R);

  void insertTripCount(SCEV const *tripCount);
  Value *scevToValue(SCEV const *scev);
  int64_t getLoopIterationCount(Region *R);
  std::list<SCEV const *> maxTripCounts;
  
  void replaceViolatingInstructions(Region &R);

  BasicBlock *createTestBlock();

  void insertAliasChecks(void* Context, BasicBlock* BBAT);
  Value *insertAliasCheck(BasicBlock *BBAT, Value *v1, Value *v2, Value* res);

  void insertFunctionCheck(Instruction *I);

  void insertRollbackCall(Instruction *I);

  Value *insertPseudoInstructionsPre(Region &R);

  bool containsCalls;
  CallInst *createCall(Instruction *I);

  typedef std::pair<BasicBlock*, BasicBlock*> RegionScoreKey;
  typedef std::map<RegionScoreKey, int> RegionScoreMap;
  RegionScoreMap RegionScores;
  std::set<RegionScoreKey> preparedRegions;

  std::map<BasicBlock*, int> ExecutionProbability;

  typedef std::map<Region*, int> ViolationProbabilityMap;
  ViolationProbabilityMap ViolationProbability;

  
public:

  enum Violations {
    
    VIOLATION_PHI,
    VIOLATION_ALIAS,
    VIOLATION_FUNCCALL,
    VIOLATION_AFFFUNC

  };


  void registerMemoryInstruction(Instruction *I, Value *BV);

  RegionSpeculation(ScopDetection *SD);

  void prepareRegion( Region &R );
  
  bool speculateOnRegion(Region &R, int *violations);

  void setFunction(Function &F) { func = &F; };

  void addViolatingInstruction(Instruction *I, unsigned violation);

  void postPrepareRegion(BasicBlock *testBlock);

};

} //end namespace polly


#endif
