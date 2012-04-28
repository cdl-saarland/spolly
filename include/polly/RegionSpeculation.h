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

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/Statistic.h"

#include "llvm/Transforms/Utils/ValueMapper.h"

#include "llvm/Analysis/AliasSetTracker.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/IRBuilder.h"

#include <map>
#include <set>

using namespace llvm;

namespace sambamba {
  class Profiler2;
}

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
  class FunctionPassManager;
}

namespace polly {
  
extern bool SPollyExtractRegions;
extern bool SPOLLY_CHUNKS;

class ScopStmt;
class ScopDetection;
class SPollyInfo;

//===----------------------------------------------------------------------===//
/// @brief Speculate on SCoPs
class RegionSpeculation { 

  /// @brief Allow SPollyInfo objects to acces the analyses
  friend class SPollyInfo;

  /// @brief Some typedef as in the ScopDetection pass
  //@{
  typedef const Region * CRegionT;
  typedef std::map<CRegionT, std::string> InvalidRegionMap;
  typedef std::set<CRegionT> RegionSet;
public:
  typedef std::pair<BasicBlock*, BasicBlock*> RegionMapKey;
private:
  typedef DenseMap<RegionMapKey, SPollyInfo*> SPollyRegionMap;
  //@}
  
  /// @brief The set containing all speculative valid regions 
  SPollyRegionMap SpeculativeValidRegions;

  /// @brief A temporary SPollyInfo object for the current region
  /// 
  /// Information gathered during the analysis are saved and the object is 
  /// deleted or stored afterwards
  SPollyInfo *TemporaryRegion;
  
  FunctionPassManager *fpm;

  /// @brief Analysis passes used.
  //@{
  ScopDetection *SD;
  ScalarEvolution* SE;
  LoopInfo *LI;
  RegionInfo *RI;
  AliasAnalysis *AA;
  TargetData *TD;
  DominatorTree *DT;
  //@}
  
public:

  /// @brief Different violation causes for instructions
  //@{
  enum Violation {
    Alias,               // Aliasing instruction
    AffineFunction,      // Non affine access function
    LoopCount,
    FunctionCall         // 
  };
  //@}

  /// @brief The default constructor
  RegionSpeculation();
  
  /// @brief
  ~RegionSpeculation();

  void releaseMemory(); 

  /// @brief
  //@{
  typedef SPollyRegionMap::iterator iterator;
  typedef SPollyRegionMap::const_iterator const_iterator;
  iterator begin() { return SpeculativeValidRegions.begin(); }
  iterator end() { return SpeculativeValidRegions.end(); }
  
  const_iterator begin() const { return SpeculativeValidRegions.begin(); }
  const_iterator end() const { return SpeculativeValidRegions.end(); }

  unsigned size() const { return SpeculativeValidRegions.size(); }
  //@}
  
  /// @brief Access functions for SPollyInfo objects
  //@{
  //typedef std::pair<Function *, ValueToValueMapTy *> FunctionPair;
  Function *getOriginalVersion(RegionMapKey &RMK);
  Function *getProfilingVersion(RegionMapKey &RMK);
  BasicBlock *getParallelSplitBlock(RegionMapKey &RMK); 
  Function *getParallelVersion(RegionMapKey &RMK, Module *dstModule, 
                               bool useOriginal = false, unsigned forks = 16);
  std::string getNameStr(RegionMapKey &RMK);
  bool checksAreSound(RegionMapKey &RMK);
  int64_t getScore(RegionMapKey &RMK);
  void changeCalledVersion(RegionMapKey &RMK, Function *Version); 

  void removeRegion(RegionMapKey &RMK);

  Function *getOriginalVersion(SPollyInfo *SPI);
  Function *getProfilingVersion(SPollyInfo *SPI);
  Function *getParallelVersion(SPollyInfo *SPI, Module *dstModule,
                               bool useOriginal = false, unsigned forks = 16);
  BasicBlock *getParallelSplitBlock(SPollyInfo *SPI);
  std::string getNameStr(SPollyInfo *SPI);
  bool checksAreSound(SPollyInfo *SPI);
  int64_t getScore(SPollyInfo *SPI);

  std::vector<Value *> &getAliasGroupFor(Value *v);

  void changeCalledVersion(SPollyInfo *SPI, Function *Version); 
  //@}

  /// @brief Register a memory access for the current region (TemporaryRegion)
  bool registerViolatingInstruction(const Instruction * const I,
                                    Violation V);
  
  /// @brief Register a 
  void registerLoopCount(const Loop *L);

  /// @brief Register a memory access for the current region (TemporaryRegion)
  bool registerMemoryAccess(const Instruction * const I,
                            const SCEV * const scev,
                            const Value * const V);
  
  /// @brief Store the associated SPollyInfo object for the given region
  ///
  /// @param R
  ///     The current analysed Region
  /// 
  /// The SPollyInfo object for the region (should be TemporaryRegion)
  /// is added to SpeculativeValidRegions 
  void storeTemporaryRegion(CRegionT R, AliasSetTracker &AST);

  /// @brief Delete the associated SPollyInfo object for the given region
  ///
  /// @param R
  ///     The current analysed Region
  void forgetTemporaryRegion(CRegionT R);

  /// @brief Create a new SPollyInfo object for the given region
  /// 
  /// @param R
  ///     The current analysed Region
  /// 
  /// The new created object is associated with the given region and store it 
  /// as TemporaryRegion
  void newTemporaryRegion(CRegionT R);

  /// @brief Initialize the RegionSpeculation for a new ScopDetection run
  /// 
  /// Save the given analyses passes 
  void initScopDetectionRun(Function &function,
                            AliasAnalysis *AA, ScalarEvolution *SE, 
                            LoopInfo *LI, RegionInfo *RI, 
                            DominatorTree *DT, TargetData *TD,
                            ScopDetection *SD);

  /// @brief Finalize the ScopDetection run 
  /// 
  ///  - Forget the given analysis
  void finalizeScopDetectionRun();

  /// @brief
  ScalarEvolution *getSE() { return SE; }

  /// @brief Verify the communication between ScopDetection and RegionSpeculation 
  ///
  /// This is called after by the veryify function of the ScopDetection pass
  /// and should only be used in DEBUG mode
  void verifyRS(const RegionSet &ValidRegions, 
                const RegionSet &SpeculativeValidRegions,
                const InvalidRegionMap &InvalidRegions) const ;

  
  /// @brief
  void print();
  
};

class StatisticPrinter : public FunctionPass {

public:
  static char ID;
  StatisticPrinter();

  virtual void getAnalysisUsage(AnalysisUsage &AU) const;
  virtual bool runOnFunction(Function &F);
  virtual bool doInitialization(Module &M);
  virtual bool doFinalization(Module &M);
};

Pass *createStatisticPrinterPass();

} //end namespace polly

namespace llvm {
  class PassRegistry;
  void initializeStatisticPrinterPass(llvm::PassRegistry&);
}


#endif
