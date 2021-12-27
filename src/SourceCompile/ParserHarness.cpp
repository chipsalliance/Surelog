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
#include "ErrorReporting/Error.h"
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

struct ParserHarness::Holder {
  std::unique_ptr<CompilationUnit> unit;
  std::unique_ptr<SymbolTable> symbols;
  std::unique_ptr<ErrorContainer> errors;
  std::unique_ptr<CommandLineParser> clp;
  std::unique_ptr<Library> lib;
  std::unique_ptr<Compiler> compiler;
  std::unique_ptr<CompileSourceFile> csf;
  std::unique_ptr<ParseFile> pf;
};

std::unique_ptr<FileContent> ParserHarness::parse(const std::string& content) {
  delete m_h;
  m_h = new Holder();

  m_h->unit = std::make_unique<CompilationUnit>(false);
  m_h->symbols = std::make_unique<SymbolTable>();
  m_h->errors = std::make_unique<ErrorContainer>(m_h->symbols.get());
  m_h->clp = std::make_unique<CommandLineParser>(
      m_h->errors.get(), m_h->symbols.get(), false, false);
  m_h->clp->setCacheAllowed(false);
  m_h->lib = std::make_unique<Library>("work", m_h->symbols.get());
  m_h->compiler = std::make_unique<Compiler>(m_h->clp.get(), m_h->errors.get(),
                                             m_h->symbols.get());
  m_h->csf = std::make_unique<CompileSourceFile>(
      0, m_h->clp.get(), m_h->errors.get(), m_h->compiler.get(),
      m_h->symbols.get(), m_h->unit.get(), m_h->lib.get());
  m_h->pf.reset(
      new ParseFile(content, m_h->csf.get(), m_h->unit.get(), m_h->lib.get()));
  std::unique_ptr<FileContent> file_content_result(new FileContent(
      0, m_h->lib.get(), m_h->symbols.get(), m_h->errors.get(), nullptr, 0));
  m_h->pf->setFileContent(file_content_result.get());
  if (!m_h->pf->parse()) file_content_result.reset(nullptr);
  return file_content_result;
}

FileContent* ParserHarness::parse(const std::string& content,
                                  Compiler* compiler,
                                  const std::string fileName) {
  CompilationUnit* unit = new CompilationUnit(false);
  SymbolTable* symbols = compiler->getSymbolTable();
  ErrorContainer* errors = compiler->getErrorContainer();
  CommandLineParser* clp = compiler->getCommandLineParser();
  Library* lib = new Library("work", symbols);
  CompileSourceFile* csf =
      new CompileSourceFile(0, clp, errors, compiler, symbols, unit, lib);
  ParseFile* pf = new ParseFile(content, csf, unit, lib);
  NodeId fileId = 0;
  if (!fileName.empty()) {
    fileId = symbols->registerSymbol(fileName);
  }
  FileContent* file_content_result =
      new FileContent(fileId, lib, symbols, errors, nullptr, 0);
  pf->setFileContent(file_content_result);
  if (!pf->parse()) file_content_result = nullptr;
  return file_content_result;
}

ParserHarness::~ParserHarness() { delete m_h; }

}  // namespace SURELOG
