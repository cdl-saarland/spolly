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

#include "sambamba/Profiler.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/IRBuilder.h"

#include "llvm/Analysis/AliasSetTracker.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"

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
  class AliasAnalysis;
  class ScalarEvolution; 
  class LoopInfo;
  class RegionInfo;
  class DominatorTree;
  class TargetData;
  class SCEV;
}

namespace polly {
  
extern bool RegionSpeculationPrepareRegion;

class ScopStmt;
class ScopDetection;
class SPollyInfo;
class SCEVCreator;

//===----------------------------------------------------------------------===//
/// @brief Speculate on SCoPs
class RegionSpeculation { 

  typedef const Region * CRegionT;

  // Some typedef as in the ScopDetection pass
  typedef std::map<CRegionT, std::string> InvalidRegionMap;
  typedef std::set<CRegionT> RegionSet;

  typedef std::map<CRegionT, SPollyInfo*> SPollyRegionMap;
  /// @brief The set containing all speculative valid regions 
  SPollyRegionMap SpeculativeValidRegions;

  /// @brief A temporary SPollyInfo object for the current region
  /// 
  /// Information gathered during the analysis are saved and the object is 
  /// deleted or stored afterwards
  SPollyInfo *TemporaryRegion;
  
  /// @brief This ScalarEvolution is used to create and evaluate region scores
  ///
  /// It is created once and all SPollyInfo objects are using it
  ScalarEvolution * const SPI_SE;

  /// @brief The Profiler object
  ///
  /// During runtime it is used to create SCEV placeholders and during compile 
  /// time these placeholders are evaluated by this object
  // TODO              const
  sambamba::Profiler *       Profiler;

  /// @brief Analysis passes used.
  //@{
  ScalarEvolution* SE;
  LoopInfo *LI;
  RegionInfo *RI;
  AliasAnalysis *AA;
  TargetData *TD;
  DominatorTree *DT;
  //@}
  
  /// @brief TODO 
  class SCEVCreator * Creator;

  std::set<Value*> loadInstructions;
  std::set<Value*> storeInstructions;
  void insertInvariantChecks(BasicBlock *testBlock, BasicBlock *profilingBlock);

  std::map<Value*, std::set<const SCEV*> > accessFunctions;
  std::map<Instruction*, Instruction*> accessStatements;
  std::set<Instruction*> violatingInstructions; 
  std::map<Value*, std::pair<Instruction*, MDNode*> > aliasingValues;

  int getExecutionProbability(BasicBlock *B);

  int getViolationProbability(BasicBlock *B, Region *R);

  void collectAliasSets(Instruction *I);

  int calculateScoreFromViolations(BasicBlock *B, int *v, Region *R);

  int scoreBasicBlock(BasicBlock *B);

  int scoreLoop(Region *R);

  int scoreConditional(Region *R);

  void createMinMaxAccessPair(Value *baseValue,
                              IRBuilder<> &builder,
                              std::pair<Value*, Value*> &p);
  Value *scevToValue(SCEV const *scev, IRBuilder<> &builder);
  
  int64_t getLoopIterationCount(Region *R);
  
  void replaceViolatingInstructions();

  BasicBlock *createTestBlock();

  Value *insertAliasCheck(BasicBlock *BBAT,
                          std::pair<Value*, Value*> &v0,
                          std::pair<Value*, Value*> &v1,
                          Value *currentResult);

  void insertAliasChecks(BasicBlock* BBAT, BasicBlock *entry);

  void insertFunctionCheck(Instruction *I);

  void insertRollbackCall(Instruction *I);

  Value *insertPseudoInstructionsPre(Region &R);

  bool containsCalls;
  CallInst *createCall(Instruction *I);

  //typedef std::pair<BasicBlock*, BasicBlock*> RegionScoreKey;
  typedef Region* RegionScoreKey;
  typedef std::map<RegionScoreKey, int> RegionScoreMap;
  typedef std::map<Function*, RegionScoreMap> FunctionRegionScoreMap;
  FunctionRegionScoreMap RegionScores;
  std::set<RegionScoreKey> preparedRegions;

  std::map<BasicBlock*, int> ExecutionProbability;

  typedef std::map<Region*, int> ViolationProbabilityMap;
  ViolationProbabilityMap ViolationProbability;

  
public:

  /// @brief Different violation causes for instructions
  //@{
  enum Violation {
    Alias,               // Aliasing instruction
    AffineFunction,      // Non affine access function
    FunctionCall         // 
  };
  //@}


  /// @brief The default constructor
  /// 
  /// - Create the SPollyInfo ScalarEvolution object
  RegionSpeculation() : 
    TemporaryRegion(0), SPI_SE(new ScalarEvolution()), 
    Creator(0) {
    Profiler = new sambamba::Profiler(SPI_SE);
  } 


  std::map<Instruction*, unsigned> violatingInstructionsMap; 

  RegionScoreMap *getRegionScores(Function *func) {
    if (RegionScores.count(func)) 
      return &RegionScores[func];
    else 
      return NULL;
  }

  bool checksAvailable();
  void insertChecks(BasicBlock *aliasingTestBlock,
                    BasicBlock *invariantTestBlock,
                    BasicBlock *entry);
  
  void replaceScopStatements(ScopStmt *Statement);

  void registerMemoryInstruction(Instruction *I, Value *BV, 
                                 const SCEV* AccessFunction);

  
  void processRegion( Region *R );
  
  int scoreRegion(Region &R, int *violations);

  void addViolatingInstruction(Instruction *I, unsigned violation);

  void postPrepareRegion(BasicBlock *testBlock, Region *region);


  /// @brief Register a memory access for the current region (TemporaryRegion)
  void registerViolatingInstruction(const Instruction * const I,
                                    Violation V);

  /// @brief Register a memory access for the current region (TemporaryRegion)
  void registerMemoryAccess(const Instruction * const I,
                            const SCEV * const scev);
  
  /// @brief Store the associated SPollyInfo object for the given region
  /// 
  /// The SPollyInfo object for the region (should be TemporaryRegion)
  /// is added to SpeculativeValidRegions 
  void storeTemporaryRegion(CRegionT R);

  /// @brief Delete the associated SPollyInfo object for the given region
  void forgetTemporaryRegion(CRegionT R);

  /// @brief Create a new SPollyInfo object for the given region
  /// 
  /// The new created object is associated with the given region and store it 
  /// as TemporaryRegion
  void newTemporaryRegion(CRegionT R);

  /// @brief Initialize the RegionSpeculation for a new ScopDetection run
  /// 
  /// Save the given analyses passes 
  void initScopDetectionRun(AliasAnalysis *AA, ScalarEvolution *SE, 
                            LoopInfo *LI, RegionInfo *RI, 
                            DominatorTree *DT, TargetData *TD);

  /// @brief Finalize the ScopDetection run 
  /// 
  ///  - Forget the given analysis
  void finalizeScopDetectionRun();

  /// @brief Verify the communication between ScopDetection and RegionSpeculation 
  ///
  /// This is called after by the veryify function of the ScopDetection pass
  /// and should only be used in DEBUG mode
  void verifyRS(const RegionSet &ValidRegions, 
                const RegionSet &SpeculativeValidRegions,
                const InvalidRegionMap &InvalidRegions) const ;
  

};

} //end namespace polly


#endif
