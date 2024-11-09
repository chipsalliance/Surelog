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

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/ErrorReporting/ErrorContainer.h"
#include "Surelog/Library/Library.h"
#include "Surelog/Package/Precompiled.h"
#include "Surelog/SourceCompile/AnalyzeFile.h"
#include "Surelog/SourceCompile/Compiler.h"
#include "Surelog/SourceCompile/ParseFile.h"
#include "Surelog/SourceCompile/SymbolTable.h"

#ifdef SURELOG_WITH_PYTHON
#include <Python.h>

#include <string_view>

#include "Surelog/API/PythonAPI.h"
#include "Surelog/SourceCompile/PythonListen.h"
#endif

#include <iostream>

namespace SURELOG {

CompileSourceFile::CompileSourceFile(PathId fileId, CommandLineParser* clp,
                                     ErrorContainer* errors, Compiler* compiler,
                                     SymbolTable* symbols,
                                     CompilationUnit* compilationUnit,
                                     Library* library, std::string_view text)
    : m_fileId(fileId),
      m_commandLineParser(clp),
      m_errors(errors),
      m_compiler(compiler),
      m_symbolTable(symbols),
      m_compilationUnit(compilationUnit),
      m_action(Preprocess),
      m_library(library),
      m_text(text) {}

CompileSourceFile::CompileSourceFile(CompileSourceFile* parent,
                                     PathId ppResultFileId, uint32_t lineOffset)
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
  if (m_commandLineParser->verbose()) {
    Location loc(m_fileId);
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
  for (auto& entry : m_antlrPpMacroMap) {
    delete entry.second;
  }
  for (auto& entry : m_antlrPpFileMap) {
    delete entry.second;
  }
  m_antlrPpMacroMap.clear();
  m_antlrPpFileMap.clear();
  delete m_fileAnalyzer;
}

uint64_t CompileSourceFile::getJobSize(Action action) const {
  FileSystem* const fileSystem = FileSystem::getInstance();
  std::streamsize size = 0;
  switch (action) {
    case Preprocess:
    case PostPreprocess: {
      if (fileSystem->filesize(m_fileId, &size)) {
        return size;
      }
    } break;
    case Parse:
    case PythonAPI: {
      if (fileSystem->filesize(m_ppResultFileId, &size)) {
        return size;
      }
    } break;
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
        FileSystem::getInstance()->toPath(
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
    m_pp = new PreprocessFile(BadSymbolId, this, instructions,
                              m_compilationUnit, m_library,
                              /* includer */ nullptr, /* includerLine */ 0,
                              m_text, nullptr, 0, BadPathId);
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
    std::cerr << m_pp->reportIncludeInfo();

  Precompiled* prec = Precompiled::getSingleton();
  if ((!m_commandLineParser->createCache()) &&
      prec->isFilePrecompiled(m_fileId, getSymbolTable()))
    return true;

  m_pp->saveCache();
  return true;
}

bool CompileSourceFile::postPreprocess_() {
  FileSystem* const fileSystem = FileSystem::getInstance();
  if (m_commandLineParser->parseOnly()) {
    m_ppResultFileId = fileSystem->copy(m_fileId, m_symbolTable);
    return true;
  }
  std::string m_pp_result = m_pp->getPreProcessedFileContent();
  if (!m_text.empty()) {
    m_parser = new ParseFile(m_pp_result, this, m_compilationUnit,
                             m_library);  // unit test
  }
  if (!(m_commandLineParser->writePpOutput() ||
        m_commandLineParser->writePpOutputFileId())) {
    return true;
  }

  m_ppResultFileId = m_commandLineParser->writePpOutputFileId();
  if (!m_ppResultFileId) {
    const std::string_view libraryName = m_library->getName();
    m_ppResultFileId = fileSystem->getPpOutputFile(
        m_commandLineParser->fileunit(), m_fileId, libraryName, m_symbolTable);
  }

  if (m_commandLineParser->lowMem() || m_commandLineParser->link()) {
    return true;
  }

  const PathId ppResultDirId =
      fileSystem->getParent(m_ppResultFileId, m_symbolTable);
  if (!fileSystem->mkdirs(ppResultDirId)) {
    Location loc(ppResultDirId);
    Error err(ErrorDefinition::PP_CANNOT_CREATE_DIRECTORY, loc);
    m_errors->addError(err);
    return false;
  }
  if (!m_pp->usingCachedVersion() || !fileSystem->exists(m_ppResultFileId)) {
    if (!fileSystem->writeContent(m_ppResultFileId, m_pp_result, true)) {
      Location loc(m_ppResultFileId);
      Error err(ErrorDefinition::PP_OPEN_FILE_FOR_WRITE, loc);
      m_errors->addError(err);
      return false;
    }
  }
  return true;
}

void CompileSourceFile::registerAntlrPpHandlerForId(
    SymbolId id, PreprocessFile::AntlrParserHandler* pp) {
  auto itr = m_antlrPpMacroMap.find(id);
  if (itr != m_antlrPpMacroMap.end()) {
    delete (*itr).second;
    m_antlrPpMacroMap.erase(itr);
  }
  m_antlrPpMacroMap.emplace(id, pp);
}

void CompileSourceFile::registerAntlrPpHandlerForId(
    PathId id, PreprocessFile::AntlrParserHandler* pp) {
  auto itr = m_antlrPpFileMap.find(id);
  if (itr != m_antlrPpFileMap.end()) {
    delete (*itr).second;
    m_antlrPpFileMap.erase(itr);
  }
  m_antlrPpFileMap.emplace(id, pp);
}

PreprocessFile::AntlrParserHandler* CompileSourceFile::getAntlrPpHandlerForId(
    SymbolId id) {
  auto itr = m_antlrPpMacroMap.find(id);
  if (itr != m_antlrPpMacroMap.end()) {
    PreprocessFile::AntlrParserHandler* ptr = (*itr).second;
    return ptr;
  }
  return nullptr;
}

PreprocessFile::AntlrParserHandler* CompileSourceFile::getAntlrPpHandlerForId(
    PathId id) {
  auto itr = m_antlrPpFileMap.find(id);
  if (itr != m_antlrPpFileMap.end()) {
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
