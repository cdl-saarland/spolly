//===------ polly/CodeGeneration.h - The Polly code generator *- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//===----------------------------------------------------------------------===//

#ifndef POLLY_CODEGENERATION_H
#define POLLY_CODEGENERATION_H

#include "llvm/Pass.h"
#include "llvm/Support/IRBuilder.h"

#include "polly/Config/config.h"
#include "polly/ScopPass.h"
#include "polly/ScopInfo.h"

#include <vector>
#include <string>
#include <cstdlib>

namespace llvm {
  class Region;
  class DominatorTree;
  class ScalarEvolution;
  class TargetData;
  class RegionInfo;
  class BasicBlock;
  class PassRegistry;
  void initializeCodeGenerationPass(llvm::PassRegistry&);
}

using namespace llvm;

namespace polly {
  class Scop;
  class ScopDetection;

  extern char &IndependentBlocksID;
  extern bool EnablePollyVector;

  class CodeGeneration : public ScopPass {
    Region *region;
    Scop *S;
    DominatorTree *DT;
    ScalarEvolution *SE;
    ScopDetection *SD;
    TargetData *TD;
    RegionInfo *RI;

    std::vector<std::string> parallelLoops;

    public:
    static char ID;

    CodeGeneration() : ScopPass(ID) {}

    // Adding prototypes required if OpenMP is enabled.
    void addOpenMPDefinitions(IRBuilder<> &Builder);
  
    BasicBlock *splitEdgeAdvanced(Region *region);

    BasicBlock *addSplitAndStartBlock(IRBuilder<> *builder);
  
    void mergeControlFlow(BasicBlock *splitBlock, IRBuilder<> *builder);

    bool runOnScop(Scop &scop);

    virtual void printScop(raw_ostream &OS) const;
    virtual void getAnalysisUsage(AnalysisUsage &AU) const;
    virtual bool doInitialization(Region *, RGPassManager &RGM);
    virtual bool doFinalization();
  };
  
  Pass *createCodeGenerationPass();
}


#endif

