/*
 Copyright 2019 Alain Dargelas

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
 * File:   CompileSourceFile.cpp
 * Author: alain
 *
 * Created on February 20, 2017, 9:54 PM
 */
#include "Surelog/SourceCompile/CompileSourceFile.h"

#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>

#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <iostream>

#include "Surelog/API/PythonAPI.h"
#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/ErrorReporting/ErrorContainer.h"
#include "Surelog/Package/Precompiled.h"
#include "Surelog/SourceCompile/AntlrParserHandler.h"
#include "Surelog/SourceCompile/CompilationUnit.h"
#include "Surelog/SourceCompile/Compiler.h"
#include "Surelog/SourceCompile/ParseFile.h"
#include "Surelog/SourceCompile/PreprocessFile.h"
#include "Surelog/SourceCompile/PythonListen.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/Utils/FileUtils.h"
#include "Surelog/Utils/StringUtils.h"
#include "antlr4-runtime.h"
#include "parser/SV3_1aLexer.h"
#include "parser/SV3_1aParser.h"

using namespace antlr4;

namespace SURELOG {
namespace fs = std::filesystem;

CompileSourceFile::CompileSourceFile(SymbolId fileId, CommandLineParser* clp,
                                     ErrorContainer* errors, Compiler* compiler,
                                     SymbolTable* symbols,
                                     CompilationUnit* compilationUnit,
                                     Library* library, const std::string& text)
    : m_fileId(fileId),
      m_commandLineParser(clp),
      m_errors(errors),
      m_compiler(compiler),
      m_symbolTable(symbols),
      m_compilationUnit(compilationUnit),
      m_action(Preprocess),
      m_ppResultFileId(0),
      m_library(library),
      m_text(text) {}

CompileSourceFile::CompileSourceFile(CompileSourceFile* parent,
                                     SymbolId ppResultFileId,
                                     unsigned int lineOffset)
    : m_fileId(parent->m_fileId),
      m_commandLineParser(parent->m_commandLineParser),
      m_errors(parent->m_errors),
      m_compiler(parent->m_compiler),
      m_pp(parent->m_pp),
      m_compilationUnit(parent->m_compilationUnit),
      m_action(Parse),
      m_ppResultFileId(ppResultFileId),
#ifdef SURELOG_WITH_PYTHON
      m_interpState(parent->m_interpState),
#endif
      m_fileAnalyzer(parent->m_fileAnalyzer),
      m_library(parent->m_library) {
  m_parser =
      new ParseFile(this, parent->m_parser, m_ppResultFileId, lineOffset);
}

bool CompileSourceFile::compile(Action action) {
  m_action = action;
  fs::path fileName = m_symbolTable->getSymbol(m_fileId);
  if (m_commandLineParser->verbose()) {
    SymbolId fileId = m_fileId;
    Location loc(fileId);
    ErrorDefinition::ErrorType type =
        ErrorDefinition::PP_PROCESSING_SOURCE_FILE;
    switch (m_action) {
      case Preprocess:
      case PostPreprocess:
        type = ErrorDefinition::PP_PROCESSING_SOURCE_FILE;
        break;
      case Parse:
        type = ErrorDefinition::PA_PROCESSING_SOURCE_FILE;
        break;
      case PythonAPI:
        type = ErrorDefinition::PY_PROCESSING_SOURCE_FILE;
        break;
    }
    if (action != PostPreprocess) {
      Error err(type, loc);
      m_errors->printMessage(m_errors->addError(err, true));
    }
  }

  switch (m_action) {
    case Preprocess:
      return preprocess_();
    case PostPreprocess:
      return postPreprocess_();
    case Parse:
      return parse_();
    case PythonAPI: {
      return pythonAPI_();
    }
  }
  return true;
}

CompileSourceFile::CompileSourceFile(const CompileSourceFile& orig) {}

CompileSourceFile::~CompileSourceFile() {
  std::vector<PreprocessFile*>::iterator itr;
  for (itr = m_ppIncludeVec.begin(); itr != m_ppIncludeVec.end(); itr++) {
    delete *itr;
  }

  delete m_parser;
#ifdef SURELOG_WITH_PYTHON
  delete m_pythonListener;
#endif
  std::map<SymbolId, PreprocessFile::AntlrParserHandler*>::iterator itr2;
  for (itr2 = m_antlrPpMap.begin(); itr2 != m_antlrPpMap.end(); itr2++) {
    delete (*itr2).second;
  }
}

unsigned int CompileSourceFile::getJobSize(Action action) {
  switch (action) {
    case Preprocess:
    case PostPreprocess: {
      fs::path fileName = getSymbolTable()->getSymbol(m_fileId);
      return FileUtils::fileSize(fileName);
    }
    case Parse: {
      fs::path fileName = getSymbolTable()->getSymbol(m_ppResultFileId);
      return FileUtils::fileSize(fileName);
    }
    case PythonAPI: {
      fs::path fileName = getSymbolTable()->getSymbol(m_ppResultFileId);
      return FileUtils::fileSize(fileName);
    }
  };
  return 0;
}

bool CompileSourceFile::pythonAPI_() {
#ifdef SURELOG_WITH_PYTHON
  if (getCommandLineParser()->pythonListener()) {
    m_pythonListener = new PythonListen(m_parser, this);
    if (!m_pythonListener->listen()) {
      return false;
    }
    bool fatalErrors = m_errors->hasFatalErrors();
    if (fatalErrors) {
      return false;
    }
  }

  if (getCommandLineParser()->pythonEvalScriptPerFile()) {
    PythonAPI::evalScriptPerFile(
        getCommandLineParser()->getSymbolTable().getSymbol(
            getCommandLineParser()->pythonEvalScriptPerFileId()),
        m_errors, m_parser->getFileContent(), m_interpState);
  }
  return true;
#else
  return false;
#endif
}

bool CompileSourceFile::initParser() {
  if (m_parser == nullptr)
    m_parser = new ParseFile(m_fileId, this, m_compilationUnit, m_library,
                             m_ppResultFileId,
                             getCommandLineParser()->pythonListener());
  return true;
}

bool CompileSourceFile::parse_() {
  initParser();
  if (!m_parser->parse()) {
    return false;
  }
  bool fatalErrors = m_errors->hasFatalErrors();
  if (fatalErrors) {
    return false;
  }
  return true;
}

bool CompileSourceFile::preprocess_() {
  Precompiled* prec = Precompiled::getSingleton();
  fs::path root = getSymbolTable()->getSymbol(m_fileId);
  root = FileUtils::basename(root);

  PreprocessFile::SpecialInstructions instructions(
      PreprocessFile::SpecialInstructions::DontMute,
      PreprocessFile::SpecialInstructions::DontMark,
      m_commandLineParser->filterFileLine()
          ? PreprocessFile::SpecialInstructions::Filter
          : PreprocessFile::SpecialInstructions::DontFilter,
      PreprocessFile::SpecialInstructions::CheckLoop,
      PreprocessFile::SpecialInstructions::ComplainUndefinedMacro);
  if (m_text.empty()) {
    m_pp = new PreprocessFile(m_fileId, this, instructions, m_compilationUnit,
                              m_library);
  } else {
    m_pp =
        new PreprocessFile(0, nullptr, 0, this, instructions, m_compilationUnit,
                           m_library, m_text, nullptr, 0, 0);
  }
  registerPP(m_pp);

  if (!m_pp->preprocess()) {
    return false;
  }
  bool fatalErrors = m_errors->hasFatalErrors();
  if (fatalErrors) {
    return false;
  }

  if (m_commandLineParser->getDebugIncludeFileInfo())
    std::cout << m_pp->reportIncludeInfo();

  if ((!m_commandLineParser->createCache()) && prec->isFilePrecompiled(root))
    return true;

  m_pp->saveCache();
  return true;
}

bool CompileSourceFile::postPreprocess_() {
  SymbolTable* symbolTable = getCompiler()->getSymbolTable();
  if (m_commandLineParser->parseOnly()) {
    m_ppResultFileId =
        m_symbolTable->registerSymbol(symbolTable->getSymbol(m_fileId));
    return true;
  }
  std::string m_pp_result = m_pp->getPreProcessedFileContent();
  if (!m_text.empty()) {
    m_parser = new ParseFile(m_pp_result, this, m_compilationUnit,
                             m_library);  // unit test
  }
  if (m_commandLineParser->writePpOutput() ||
      (m_commandLineParser->writePpOutputFileId() != 0)) {
    const fs::path directory =
        symbolTable->getSymbol(m_commandLineParser->getFullCompileDir());
    fs::path fullFileName = symbolTable->getSymbol(m_fileId);
    fs::path baseFileName = FileUtils::basename(fullFileName);
    fs::path filePath = FileUtils::getPathName(fullFileName);
    fs::path hashedPath = FileUtils::hashPath(filePath);
    fs::path fileName = hashedPath / baseFileName;

    const fs::path writePpOutputFileName =
        symbolTable->getSymbol(m_commandLineParser->writePpOutputFileId());
    std::string libName = m_library->getName();
    fs::path ppFileName = m_commandLineParser->writePpOutput()
                              ? directory / libName / fileName
                              : writePpOutputFileName;
    fs::path dirPpFile = FileUtils::getPathName(ppFileName);
    SymbolId ppOutId = symbolTable->registerSymbol(ppFileName.string());
    m_ppResultFileId = m_symbolTable->registerSymbol(ppFileName.string());
    SymbolId ppDirId = symbolTable->registerSymbol(dirPpFile.string());
    if (m_commandLineParser->lowMem()) {
      return true;
    }
    if (!FileUtils::mkDirs(dirPpFile)) {
      Location loc(ppDirId);
      Error err(ErrorDefinition::PP_CANNOT_CREATE_DIRECTORY, loc);
      m_errors->addError(err);
      return false;
    }
    if ((!m_pp->usingCachedVersion()) || (!FileUtils::fileExists(ppFileName))) {
      std::ofstream ofs;
      ofs.open(ppFileName);
      if (ofs.good()) {
        ofs << m_pp_result;
        ofs.close();
      } else {
        Location loc(ppOutId);
        Error err(ErrorDefinition::PP_OPEN_FILE_FOR_WRITE, loc);
        m_errors->addError(err);
        return false;
      }
    }
  }
  return true;
}

void CompileSourceFile::registerAntlrPpHandlerForId(
    SymbolId id, PreprocessFile::AntlrParserHandler* pp) {
  std::map<SymbolId, PreprocessFile::AntlrParserHandler*>::iterator itr =
      m_antlrPpMap.find(id);
  if (itr != m_antlrPpMap.end()) {
    delete (*itr).second;
    m_antlrPpMap.erase(itr);
    m_antlrPpMap.insert(std::make_pair(id, pp));
    return;
  }
  m_antlrPpMap.insert(std::make_pair(id, pp));
}

PreprocessFile::AntlrParserHandler* CompileSourceFile::getAntlrPpHandlerForId(
    SymbolId id) {
  std::map<SymbolId, PreprocessFile::AntlrParserHandler*>::iterator itr =
      m_antlrPpMap.find(id);
  if (itr != m_antlrPpMap.end()) {
    PreprocessFile::AntlrParserHandler* ptr = (*itr).second;
    return ptr;
  }
  return nullptr;
}

void CompileSourceFile::setSymbolTable(SymbolTable* symbols) {
  m_symbolTable = symbols;
}

#ifdef SURELOG_WITH_PYTHON
void CompileSourceFile::setPythonInterp(PyThreadState* interpState) {
  m_interpState = interpState;
  m_errors->setPythonInterp(interpState);
}

void CompileSourceFile::shutdownPythonInterp() {
  m_errors->setPythonInterp(nullptr);
  PythonAPI::shutdown(m_interpState);
  m_interpState = nullptr;
}
#endif
}  // namespace SURELOG
