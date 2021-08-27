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

PreprocessHarness::PreprocessHarness() : m_errors(&m_symbols) {}

std::string PreprocessHarness::preprocess(std::string_view content) {
  std::string result;
  PreprocessFile::SpecialInstructions instructions(
      PreprocessFile::SpecialInstructions::DontMute,
      PreprocessFile::SpecialInstructions::DontMark,
      PreprocessFile::SpecialInstructions::DontFilter,
      PreprocessFile::SpecialInstructions::CheckLoop,
      PreprocessFile::SpecialInstructions::ComplainUndefinedMacro);
  CompilationUnit unit(false);
  CommandLineParser clp(&m_errors, &m_symbols, false, false);
  Library lib("work", &m_symbols);
  Compiler compiler(&clp, &m_errors, &m_symbols);
  CompileSourceFile csf(0, &clp, &m_errors, &compiler, &m_symbols, &unit, &lib);
  PreprocessFile pp(0, nullptr, 0, &csf, instructions, &unit, &lib, content,
                    nullptr, 0, 0);

  if (!pp.preprocess()) {
    result = "ERROR_PP";
  }
  if (m_errors.hasFatalErrors()) {
    result = "ERROR_PP";
  }
  m_errors.printMessages();
  if (result.empty()) result = pp.getPreProcessedFileContent();
  return result;
}

}  // namespace SURELOG
