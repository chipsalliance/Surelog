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
#include "Surelog/Common/Containers.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/PathId.h"
#include "Surelog/Common/Session.h"
#include "Surelog/Common/SymbolId.h"
#include "Surelog/ErrorReporting/Error.h"
#include "Surelog/ErrorReporting/ErrorContainer.h"
#include "Surelog/ErrorReporting/ErrorDefinition.h"
#include "Surelog/ErrorReporting/Location.h"
#include "Surelog/Library/Library.h"
#include "Surelog/Package/Precompiled.h"
#include "Surelog/SourceCompile/AnalyzeFile.h"
#include "Surelog/SourceCompile/Compiler.h"
#include "Surelog/SourceCompile/ParseFile.h"
#include "Surelog/SourceCompile/SymbolTable.h"

#ifdef SURELOG_WITH_PYTHON
#include <Python.h>

#include <cstdint>
#include <string_view>
#include <vector>

#include "Surelog/API/PythonAPI.h"
#include "Surelog/SourceCompile/PythonListen.h"
#endif

#include <iostream>

namespace SURELOG {

CompileSourceFile::CompileSourceFile(Session* session, PathId fileId,
                                     Compiler* compiler,
                                     CompilationUnit* compilationUnit,
                                     Library* library, std::string_view text)
    : m_session(session),
      m_fileId(fileId),
      m_compiler(compiler),
      m_compilationUnit(compilationUnit),
      m_action(Action::Preprocess),
      m_library(library),
      m_text(text) {}

CompileSourceFile::CompileSourceFile(Session* session,
                                     CompileSourceFile* parent,
                                     PathId ppResultFileId, uint32_t lineOffset)
    : m_session(session),
      m_fileId(parent->m_fileId),
      m_compiler(parent->m_compiler),
      m_pp(parent->m_pp),
      m_compilationUnit(parent->m_compilationUnit),
      m_action(Action::Parse),
      m_ppResultFileId(ppResultFileId),
#ifdef SURELOG_WITH_PYTHON
      m_interpState(parent->m_interpState),
#endif
      m_fileAnalyzer(parent->m_fileAnalyzer),
      m_library(parent->m_library) {
  m_parser = new ParseFile(m_session, this, parent->m_parser, m_ppResultFileId,
                           lineOffset);
}

bool CompileSourceFile::compile(Action action) {
  ErrorContainer* const errors = m_session->getErrorContainer();
  CommandLineParser* const clp = m_session->getCommandLineParser();
  m_action = action;
  if (clp->verbose()) {
    Location loc(m_fileId);
    ErrorDefinition::ErrorType type =
        ErrorDefinition::PP_PROCESSING_SOURCE_FILE;
    switch (m_action) {
      case Action::Preprocess:
      case Action::PostPreprocess:
        type = ErrorDefinition::PP_PROCESSING_SOURCE_FILE;
        break;
      case Action::Parse:
        type = ErrorDefinition::PA_PROCESSING_SOURCE_FILE;
        break;
      case Action::PythonAPI:
        type = ErrorDefinition::PY_PROCESSING_SOURCE_FILE;
        break;
    }
    if (action != Action::PostPreprocess) {
      Error err(type, loc);
      errors->printMessage(errors->addError(err, true));
    }
  }

  switch (m_action) {
    case Action::Preprocess:
      return preprocess_();
    case Action::PostPreprocess:
      return postPreprocess_();
    case Action::Parse:
      return parse_();
    case Action::PythonAPI: {
      return pythonAPI_();
    }
  }
  return true;
}

CompileSourceFile::CompileSourceFile(const CompileSourceFile& orig)
    : m_session(orig.m_session) {}

CompileSourceFile::~CompileSourceFile() {
  DeleteSequenceContainerPointersAndClear(&m_ppIncludeVec);
  delete m_parser;

#ifdef SURELOG_WITH_PYTHON
  delete m_pythonListener;
#endif

  DeleteAssociativeContainerValuePointersAndClear(&m_antlrPpMacroMap);
  DeleteAssociativeContainerValuePointersAndClear(&m_antlrPpFileMap);
  delete m_fileAnalyzer;
}

uint64_t CompileSourceFile::getJobSize(Action action) const {
  FileSystem* const fileSystem = m_session->getFileSystem();
  std::streamsize size = 0;
  switch (action) {
    case Action::Preprocess:
    case Action::PostPreprocess: {
      if (fileSystem->filesize(m_fileId, &size)) {
        return size;
      }
    } break;
    case Action::Parse:
    case Action::PythonAPI: {
      if (fileSystem->filesize(m_ppResultFileId, &size)) {
        return size;
      }
    } break;
  };
  return 0;
}

bool CompileSourceFile::pythonAPI_() {
#ifdef SURELOG_WITH_PYTHON
  if (m_session->pythonListener()) {
    m_pythonListener = new PythonListen(m_parser, this);
    if (!m_pythonListener->listen()) {
      return false;
    }
    bool fatalErrors = m_errors->hasFatalErrors();
    if (fatalErrors) {
      return false;
    }
  }

  if (m_session->pythonEvalScriptPerFile()) {
    PythonAPI::evalScriptPerFile(m_session->getFileSystem()->toPath(
                                     m_session->pythonEvalScriptPerFileId()),
                                 m_errors, m_parser->getFileContent(),
                                 m_interpState);
  }
  return true;
#else
  return false;
#endif
}

bool CompileSourceFile::initParser() {
  if (m_parser == nullptr) {
    CommandLineParser* const clp = m_session->getCommandLineParser();
    m_parser =
        new ParseFile(m_session, m_fileId, this, m_compilationUnit, m_library,
                      m_ppResultFileId, clp->pythonListener());
    return true;
  }
  return false;
}

bool CompileSourceFile::parse_() {
  initParser();
  if (!m_parser->parse()) {
    return false;
  }
  bool fatalErrors = m_session->getErrorContainer()->hasFatalErrors();
  if (fatalErrors) {
    return false;
  }
  return true;
}

bool CompileSourceFile::preprocess_() {
  ErrorContainer* const errors = m_session->getErrorContainer();
  CommandLineParser* const clp = m_session->getCommandLineParser();
  PreprocessFile::SpecialInstructions instructions(
      PreprocessFile::SpecialInstructions::DontMute,
      PreprocessFile::SpecialInstructions::DontMark,
      clp->filterFileLine() ? PreprocessFile::SpecialInstructions::Filter
                            : PreprocessFile::SpecialInstructions::DontFilter,
      PreprocessFile::SpecialInstructions::CheckLoop,
      PreprocessFile::SpecialInstructions::ComplainUndefinedMacro);
  if (m_text.empty()) {
    m_pp = new PreprocessFile(m_session, m_fileId, this, instructions,
                              m_compilationUnit, m_library);
  } else {
    m_pp = new PreprocessFile(m_session, BadSymbolId, this, instructions,
                              m_compilationUnit, m_library,
                              /* includer */ nullptr, /* includerLine */ 0,
                              m_text, nullptr, m_fileId, BadPathId, 0);
  }
  registerPP(m_pp);

  if (!m_pp->preprocess()) {
    return false;
  }
  bool fatalErrors = errors->hasFatalErrors();
  if (fatalErrors) {
    return false;
  }

  if (clp->getDebugIncludeFileInfo()) m_pp->reportIncludeInfo(std::cerr);

  Precompiled* prec = m_session->getPrecompiled();
  if ((!clp->createCache()) && prec->isFilePrecompiled(m_fileId)) return true;

  m_pp->saveCache();
  return true;
}

bool CompileSourceFile::postPreprocess_() {
  SymbolTable* const symbols = m_session->getSymbolTable();
  FileSystem* const fileSystem = m_session->getFileSystem();
  ErrorContainer* const errors = m_session->getErrorContainer();
  CommandLineParser* const clp = m_session->getCommandLineParser();
  if (clp->parseOnly()) {
    m_ppResultFileId = fileSystem->copy(m_fileId, symbols);
    return true;
  }
  const auto& pp_result = m_pp->getPreProcessedFileContent();
  const std::string& m_pp_result = std::get<0>(pp_result);
  if (!m_text.empty()) {
    m_parser = new ParseFile(m_session, m_pp_result, this, m_compilationUnit,
                             m_library);  // unit test
  }
  if (!(clp->writePpOutput() || clp->writePpOutputFileId())) {
    return true;
  }

  m_ppResultFileId = clp->writePpOutputFileId();
  if (!m_ppResultFileId) {
    const std::string_view libraryName = m_library->getName();
    m_ppResultFileId = fileSystem->getPpOutputFile(clp->fileUnit(), m_fileId,
                                                   libraryName, symbols);
  }

  if (clp->lowMem() || clp->link()) {
    return true;
  }

  const PathId ppResultDirId = fileSystem->getParent(m_ppResultFileId, symbols);
  if (!fileSystem->mkdirs(ppResultDirId)) {
    errors->addError(ErrorDefinition::PP_CANNOT_CREATE_DIRECTORY,
                     Location(ppResultDirId));
    return false;
  }
  if (!m_pp->usingCachedVersion() || !fileSystem->exists(m_ppResultFileId)) {
    if (!fileSystem->writeContent(m_ppResultFileId, m_pp_result, true)) {
      errors->addError(ErrorDefinition::PP_OPEN_FILE_FOR_WRITE,
                       Location(m_ppResultFileId));
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
