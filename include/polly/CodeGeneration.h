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

namespace polly {
  extern bool EnablePollyVector;
  extern bool EnablePollyOpenMP;
  extern unsigned  PollyForks;
  extern bool EnablePollyForkJoin;
  extern bool EnablePollyForkJoinInline;
}

#endif
