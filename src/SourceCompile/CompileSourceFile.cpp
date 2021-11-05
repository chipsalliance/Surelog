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
#include "SourceCompile/CompileSourceFile.h"

#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>

#include <cstdlib>
#include <fstream>
#include <iostream>

#include "API/PythonAPI.h"
#include "CommandLine/CommandLineParser.h"
#include "ErrorReporting/ErrorContainer.h"
#include "Package/Precompiled.h"
#include "SourceCompile/AntlrParserHandler.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/Compiler.h"
#include "SourceCompile/ParseFile.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/PythonListen.h"
#include "SourceCompile/SymbolTable.h"
#include "Utils/FileUtils.h"
#include "Utils/StringUtils.h"
#include "antlr4-runtime.h"
#include "parser/SV3_1aLexer.h"
#include "parser/SV3_1aParser.h"

using namespace antlr4;
using namespace SURELOG;

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
  std::string_view fileName = m_symbolTable->getSymbol(m_fileId);
  if (m_commandLineParser->verbose()) {
    SymbolId fileId = m_fileId;
    if (fileName.rfind("/bin/sv/builtin.sv") != std::string_view::npos) {
      fileId = m_symbolTable->registerSymbol("builtin.sv");
    }
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
      if (fileName.rfind("/bin/sv/builtin.sv") == std::string_view::npos) {
        return pythonAPI_();
      }
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
      std::string_view fileName = getSymbolTable()->getSymbol(m_fileId);
      return FileUtils::fileSize(fileName);
    }
    case Parse: {
      std::string_view fileName = getSymbolTable()->getSymbol(m_ppResultFileId);
      return FileUtils::fileSize(fileName);
    }
    case PythonAPI: {
      std::string_view fileName = getSymbolTable()->getSymbol(m_ppResultFileId);
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
  if (m_parser == NULL)
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
  std::string root = FileUtils::basename(getSymbolTable()->getSymbol(m_fileId));

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
  if (m_text.size()) {
    m_parser = new ParseFile(m_pp_result, this, m_compilationUnit,
                             m_library);  // unit test
  }
  if (m_commandLineParser->writePpOutput() ||
      (m_commandLineParser->writePpOutputFileId() != 0)) {
    const std::string_view directory =
        symbolTable->getSymbol(m_commandLineParser->getFullCompileDir());
    const std::string_view fullFileName = symbolTable->getSymbol(m_fileId);
    std::string baseFileName = FileUtils::basename(fullFileName);
    std::string filePath = FileUtils::getPathName(fullFileName);
    std::string hashedPath = FileUtils::hashPath(filePath);
    std::string fileName = hashedPath + baseFileName;

    const std::string_view writePpOutputFileName =
        symbolTable->getSymbol(m_commandLineParser->writePpOutputFileId());
    std::string libName = m_library->getName() + "/";
    std::string ppFileName =
        m_commandLineParser->writePpOutput()
            ? std::string(directory).append(libName).append(fileName)
            : std::string(writePpOutputFileName);
    std::string dirPpFile = FileUtils::getPathName(ppFileName);
    SymbolId ppOutId = symbolTable->registerSymbol(ppFileName);
    m_ppResultFileId = m_symbolTable->registerSymbol(ppFileName);
    SymbolId ppDirId = symbolTable->registerSymbol(dirPpFile);
    if (m_commandLineParser->lowMem()) {
      return true;
    }
    if (!FileUtils::mkDir(dirPpFile)) {
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
  return NULL;
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
  m_errors->setPythonInterp(NULL);
  PythonAPI::shutdown(m_interpState);
  m_interpState = NULL;
}
#endif
