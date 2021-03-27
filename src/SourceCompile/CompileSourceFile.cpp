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
#include "CommandLine/CommandLineParser.h"
#include "ErrorReporting/ErrorContainer.h"
#include "SourceCompile/SymbolTable.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompilationUnit.h"

#include "antlr4-runtime.h"
using namespace antlr4;
#include "parser/SV3_1aLexer.h"
#include "parser/SV3_1aParser.h"

#include "SourceCompile/AntlrParserHandler.h"

#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/Compiler.h"
#include "Utils/StringUtils.h"
#include "Utils/FileUtils.h"
#include <cstdlib>
#include <iostream>
#include <fstream>
#include <sys/types.h>
#include <sys/stat.h>
using namespace std;
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/ParseFile.h"
#include "API/PythonAPI.h"
#include "SourceCompile/PythonListen.h"
#include "Package/Precompiled.h"

using namespace SURELOG;

CompileSourceFile::CompileSourceFile(SymbolId fileId, CommandLineParser* clp,
                                     ErrorContainer* errors, Compiler* compiler,
                                     SymbolTable* symbols,
                                     CompilationUnit* compilationUnit,
                                     Library* library)
    : m_fileId(fileId),
      m_commandLineParser(clp),
      m_errors(errors),
      m_compiler(compiler),
      m_pp(NULL),
      m_symbolTable(symbols),
      m_parser(NULL),
      m_compilationUnit(compilationUnit),
      m_action(Preprocess),
      m_ppResultFileId(0),
      m_interpState(NULL),
      m_pythonListener(NULL),
      m_fileAnalyzer(NULL),
      m_library(library) {}

CompileSourceFile::CompileSourceFile(CompileSourceFile* parent,
                                     SymbolId ppResultFileId,
                                     unsigned int lineOffset)
    : m_fileId(parent->m_fileId),
      m_commandLineParser(parent->m_commandLineParser),
      m_errors(parent->m_errors),
      m_compiler(parent->m_compiler),
      m_pp(parent->m_pp),
      m_symbolTable(NULL),
      m_parser(NULL),
      m_compilationUnit(parent->m_compilationUnit),
      m_action(Parse),
      m_ppResultFileId(ppResultFileId),
      m_interpState(parent->m_interpState),
      m_pythonListener(NULL),
      m_fileAnalyzer(parent->m_fileAnalyzer),
      m_library(parent->m_library) {
  m_parser =
      new ParseFile(this, parent->m_parser, m_ppResultFileId, lineOffset);
}

bool CompileSourceFile::compile(Action action) {
  m_action = action;
  std::string fileName = m_symbolTable->getSymbol(m_fileId);
  if (m_commandLineParser->verbose()) {
    SymbolId fileId = m_fileId;
    if (strstr(fileName.c_str(), "/bin/sv/builtin.sv")) {
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
      if (!strstr(fileName.c_str(), "/bin/sv/builtin.sv")) {
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

  if (m_parser) delete m_parser;

  if (m_pythonListener) delete m_pythonListener;

  std::map<SymbolId, PreprocessFile::AntlrParserHandler*>::iterator itr2;
  for (itr2 = m_antlrPpMap.begin(); itr2 != m_antlrPpMap.end(); itr2++) {
    delete (*itr2).second;
  }
}

unsigned int CompileSourceFile::getJobSize(Action action) {
  switch (action) {
    case Preprocess:
    case PostPreprocess: {
      std::string fileName = getSymbolTable()->getSymbol(m_fileId);
      return FileUtils::fileSize(fileName);
    }
    case Parse: {
      std::string fileName = getSymbolTable()->getSymbol(m_ppResultFileId);
      return FileUtils::fileSize(fileName);
    }
    case PythonAPI: {
      std::string fileName = getSymbolTable()->getSymbol(m_ppResultFileId);
      return FileUtils::fileSize(fileName);
    }
  };
  return 0;
}

bool CompileSourceFile::pythonAPI_() {
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
  std::string root = getSymbolTable()->getSymbol(m_fileId);
  root = FileUtils::basename(root);

  PreprocessFile::SpecialInstructions instructions(
      PreprocessFile::SpecialInstructions::DontMute,
      PreprocessFile::SpecialInstructions::DontMark,
      m_commandLineParser->filterFileLine()
          ? PreprocessFile::SpecialInstructions::Filter
          : PreprocessFile::SpecialInstructions::DontFilter,
      PreprocessFile::SpecialInstructions::CheckLoop,
      PreprocessFile::SpecialInstructions::ComplainUndefinedMacro);
  m_pp = new PreprocessFile(m_fileId, this, instructions, m_compilationUnit,
                            m_library);
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
    m_ppResultFileId = m_symbolTable->registerSymbol(symbolTable->getSymbol(m_fileId));
    return true;
  }
  std::string m_pp_result = m_pp->getPreProcessedFileContent();
  if (m_commandLineParser->writePpOutput() ||
      (m_commandLineParser->writePpOutputFileId() != 0)) {
    const std::string& directory =
        symbolTable->getSymbol(m_commandLineParser->getFullCompileDir());
    std::string fileName = FileUtils::makeRelativePath(symbolTable->getSymbol(m_fileId));
    const std::string& writePpOutputFileName =
        symbolTable->getSymbol(m_commandLineParser->writePpOutputFileId());
    std::string libName = m_library->getName() + "/";
    string ppFileName = m_commandLineParser->writePpOutput()
                            ? directory + libName + fileName
                            : writePpOutputFileName;
    std::string dirPpFile = FileUtils::getPathName(ppFileName);
    SymbolId ppOutId = symbolTable->registerSymbol(ppFileName);
    m_ppResultFileId = m_symbolTable->registerSymbol(ppFileName);
    SymbolId ppDirId = symbolTable->registerSymbol(dirPpFile);

    if (FileUtils::mkDir(dirPpFile.c_str()) != 0) {
      Location loc(ppDirId);
      Error err(ErrorDefinition::PP_CANNOT_CREATE_DIRECTORY, loc);
      m_errors->addError(err);
      return false;
    }
    if ((!m_pp->usingCachedVersion()) || (!FileUtils::fileExists(ppFileName))) {
      ofstream ofs;
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

void CompileSourceFile::setPythonInterp(PyThreadState* interpState) {
  m_interpState = interpState;
  m_errors->setPythonInterp(interpState);
}

void CompileSourceFile::shutdownPythonInterp() {
  m_errors->setPythonInterp(NULL);
  PythonAPI::shutdown(m_interpState);
  m_interpState = NULL;
}
