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
 * File:   ParserHarness.cpp
 * Author: alain
 *
 * Created on June 05, 2021, 90:03 AM
 */
#include "SourceCompile/ParserHarness.h"

#include <cstdlib>
#include <iostream>

#include "Cache/ParseCache.h"
#include "CommandLine/CommandLineParser.h"
#include "ErrorReporting/ErrorContainer.h"
#include "Package/Precompiled.h"
#include "SourceCompile/AntlrParserErrorListener.h"
#include "SourceCompile/AntlrParserHandler.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/Compiler.h"
#include "SourceCompile/ParseFile.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/SV3_1aTreeShapeListener.h"
#include "SourceCompile/SymbolTable.h"
#include "Utils/FileUtils.h"
#include "Utils/ParseUtils.h"
#include "Utils/StringUtils.h"
#include "Utils/Timer.h"
#include "antlr4-runtime.h"
#include "atn/ParserATNSimulator.h"
#include "parser/SV3_1aLexer.h"
#include "parser/SV3_1aParser.h"
#include "parser/SV3_1aParserBaseListener.h"

namespace SURELOG {

FileContent* ParserHarness::parse(const std::string& content) {
  CompilationUnit* unit = new CompilationUnit(false);
  SymbolTable* symbols = new SymbolTable();
  ErrorContainer* errors = new ErrorContainer(symbols);
  CommandLineParser* clp = new CommandLineParser(errors, symbols, false, false);
  Library* lib = new Library("work", symbols);
  Compiler* compiler = new Compiler(clp, errors, symbols);
  CompileSourceFile* csf =
      new CompileSourceFile(0, clp, errors, compiler, symbols, unit, lib);
  ParseFile* pf = new ParseFile(content, csf, unit, lib);
  FileContent* fC = new FileContent(0, lib, symbols, errors, nullptr, 0);
  pf->setFileContent(fC);
  if (!pf->parse()) {
    return nullptr;
  }
  // Do not delete, necessary to inspact the FileContent
  // delete unit;
  // delete symbols;
  // delete errors;
  delete clp;
  // delete lib;
  delete compiler;
  delete csf;
  delete pf;
  return fC;
}

}  // namespace SURELOG
