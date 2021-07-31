/*
 Copyright 2021 Alain Dargelas

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

 http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
 */

/*
 * File:   PreprocessHarness.cpp
 * Author: alain
 *
 * Created on June 1, 2021, 8:37 PM
 */
#include "SourceCompile/PreprocessHarness.h"

#if (defined(_MSC_VER) || defined(__MINGW32__) || defined(__CYGWIN__))
#include <process.h>  // Has to be included before <thread>
#endif

#if defined(_MSC_VER)
#include <direct.h>
#else
#include <sys/param.h>
#include <unistd.h>
#endif

#include <math.h>
#include <stdint.h>
#include <string.h>
#include <sys/stat.h>

#include <cstdlib>
#include <fstream>
#include <iostream>
#include <mutex>
#include <thread>
#include <vector>

#include "API/PythonAPI.h"
#include "CommandLine/CommandLineParser.h"
#include "DesignCompile/CompileDesign.h"
#include "ErrorReporting/ErrorContainer.h"
#include "Library/ParseLibraryDef.h"
#include "Package/Precompiled.h"
#include "SourceCompile/AnalyzeFile.h"
#include "SourceCompile/CheckCompile.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/SymbolTable.h"
#include "Utils/ContainerUtils.h"
#include "Utils/FileUtils.h"
#include "Utils/StringUtils.h"
#include "Utils/Timer.h"
#include "antlr4-runtime.h"

namespace SURELOG {

std::string PreprocessHarness::preprocess(std::string_view content) {
  std::string result;
  PreprocessFile::SpecialInstructions instructions(
      PreprocessFile::SpecialInstructions::DontMute,
      PreprocessFile::SpecialInstructions::DontMark,
      PreprocessFile::SpecialInstructions::DontFilter,
      PreprocessFile::SpecialInstructions::CheckLoop,
      PreprocessFile::SpecialInstructions::ComplainUndefinedMacro);
  // TODO: all these objects leak.
  CompilationUnit* unit = new CompilationUnit(false);
  SymbolTable* symbols = new SymbolTable();
  ErrorContainer* errors = new ErrorContainer(symbols);
  CommandLineParser* clp = new CommandLineParser(errors, symbols, false, false);
  Library* lib = new Library("work", symbols);
  Compiler* compiler = new Compiler(clp, errors, symbols);
  CompileSourceFile* csf =
      new CompileSourceFile(0, clp, errors, compiler, symbols, unit, lib);
  PreprocessFile* pp = new PreprocessFile(0, nullptr, 0, csf, instructions,
                                          unit, lib, content, nullptr, 0, 0);

  if (!pp->preprocess()) {
    result = "ERROR_PP";
  }
  bool fatalErrors = errors->hasFatalErrors();
  if (fatalErrors) {
    result = "ERROR_PP";
  }
  errors->printMessages();
  if (result.empty()) result = pp->getPreProcessedFileContent();
  delete unit;
  delete symbols;
  delete errors;
  delete clp;
  delete lib;
  delete compiler;
  delete csf;
  delete pp;
  return result;
}

}  // namespace SURELOG
