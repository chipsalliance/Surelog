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
 * File:   Session.cpp
 * Author: hs
 *
 * Created on April 1, 2024, 0:00 AM
 */

#include <Surelog/CommandLine/CommandLineParser.h>
#include <Surelog/Common/PlatformFileSystem.h>
#include <Surelog/Common/Session.h>
#include <Surelog/ErrorReporting/ErrorContainer.h>
#include <Surelog/ErrorReporting/LogListener.h>
#include <Surelog/Package/Precompiled.h>
#include <Surelog/SourceCompile/SymbolTable.h>

#include <filesystem>

namespace fs = std::filesystem;

namespace SURELOG {
Session::Session(FileSystem *fileSystem, SymbolTable *symbolTable,
                 LogListener *logListener, ErrorContainer *errorContainer,
                 CommandLineParser *commandLineParser, Precompiled *precompiled)
    : m_fileSystem(fileSystem == nullptr
                       ? new PlatformFileSystem(fs::current_path())
                       : fileSystem),
      m_symbolTable(symbolTable == nullptr ? new SymbolTable : symbolTable),
      m_logListener(logListener == nullptr ? new LogListener(this)
                                           : logListener),
      m_precompiled(precompiled == nullptr ? new Precompiled(this)
                                           : precompiled),
      m_errorContainer(errorContainer == nullptr ? new ErrorContainer(this)
                                                 : errorContainer),
      m_commandLineParser(commandLineParser == nullptr
                              ? new CommandLineParser(this)
                              : commandLineParser),
      m_ownsFileSystem(fileSystem == nullptr),
      m_ownsSymbolTable(symbolTable == nullptr),
      m_ownsLogListener(logListener == nullptr),
      m_ownsPrecompiled(precompiled == nullptr),
      m_ownsErrorContainer(errorContainer == nullptr),
      m_ownsCommandLineParser(commandLineParser == nullptr) {}

Session::Session()
    : Session(nullptr, nullptr, nullptr, nullptr, nullptr, nullptr) {}

Session::Session(Session *session)
    : Session(session->m_fileSystem, session->m_symbolTable,
              session->m_logListener, session->m_errorContainer,
              session->m_commandLineParser, session->m_precompiled) {}

Session::~Session() {
  if (m_ownsFileSystem) delete m_fileSystem;
  if (m_ownsSymbolTable) delete m_symbolTable;
  if (m_ownsLogListener) delete m_logListener;
  if (m_ownsPrecompiled) delete m_precompiled;
  if (m_ownsErrorContainer) delete m_errorContainer;
  if (m_ownsCommandLineParser) delete m_commandLineParser;
}

bool Session::parseCommandLine(int32_t argc, const char **argv,
                               bool diffCompMode, bool fileUnit) {
  return m_commandLineParser->parse(argc, argv, diffCompMode, fileUnit);
}

}  // namespace SURELOG
