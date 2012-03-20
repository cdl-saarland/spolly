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

#include "llvm/Transforms/Utils/ValueMapper.h"

#include "llvm/Analysis/AliasSetTracker.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/IRBuilder.h"

#include <map>
#include <set>

#define VIOLATION_COUNT 4

using namespace llvm;

namespace sambamba {
  class Profiler;
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
}

namespace polly {
  
extern bool RegionSpeculationPrepareRegion;

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
  typedef std::pair<BasicBlock*, BasicBlock*> RegionMapKey;
  typedef DenseMap<RegionMapKey, SPollyInfo*> SPollyRegionMap;
  //@}
  
  /// @brief The set containing all speculative valid regions 
  SPollyRegionMap SpeculativeValidRegions;

  /// @brief A temporary SPollyInfo object for the current region
  /// 
  /// Information gathered during the analysis are saved and the object is 
  /// deleted or stored afterwards
  SPollyInfo *TemporaryRegion;
  
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
    FunctionCall         // 
  };
  //@}

  /// @brief The default constructor
  /// 
  /// - Create the SPollyInfo ScalarEvolution object
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
  typedef std::pair<Function *, ValueToValueMapTy *> FunctionPair;
  Function* getOriginalVersion(RegionMapKey &RMK);
  FunctionPair getProfilingVersion(RegionMapKey &RMK, sambamba::Profiler *profiler);
  FunctionPair getParallelVersion(RegionMapKey &RMK, Module *dstModule);
  bool checksAreSound(RegionMapKey &RMK);
  int getScore(RegionMapKey &RMK);

  Function* getOriginalVersion(SPollyInfo *SPI);
  FunctionPair getProfilingVersion(SPollyInfo *SPI, sambamba::Profiler *profiler);
  FunctionPair getParallelVersion(SPollyInfo *SPI, Module *dstModule);
  bool checksAreSound(SPollyInfo *SPI);
  int getScore(SPollyInfo *SPI);

  
  // Not implemented
  void applyChangesToFunction(Function *F, ValueToValueMapTy &VMap);
  //@}

  /// @brief Register a memory access for the current region (TemporaryRegion)
  void registerViolatingInstruction(const Instruction * const I,
                                    Violation V);

  /// @brief Register a memory access for the current region (TemporaryRegion)
  void registerMemoryAccess(const Instruction * const I,
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

  /// @brief TODO
  bool speculateOnRegion(const Region *R);

  /// @brief
  //void updateRegionPointer(RegionInfo *RI);

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

} //end namespace polly


#endif
