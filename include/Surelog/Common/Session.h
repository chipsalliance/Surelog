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
 * File:   Session.h
 * Author: hs
 *
 * Created on April 1, 2024, 0:00 AM
 */

#ifndef SURELOG_SESSION_H
#define SURELOG_SESSION_H
#pragma once

#include <cstdint>

namespace SURELOG {
class CommandLineParser;
class ErrorContainer;
class FileSystem;
class LogListener;
class Precompiled;
class SymbolTable;

class Session final {
 public:
  Session();
  Session(FileSystem* fileSystem, SymbolTable* symbolTable,
          LogListener* logListener, ErrorContainer* errorContainer,
          CommandLineParser* commandLineParser, Precompiled* precompiled);
  explicit Session(Session* session);
  ~Session();

  bool parseCommandLine(int32_t argc, const char** argv, bool diffCompMode,
                        bool fileUnit);

  ErrorContainer* getErrorContainer() { return m_errorContainer; }
  const ErrorContainer* getErrorContainer() const { return m_errorContainer; }

  FileSystem* getFileSystem() { return m_fileSystem; }
  const FileSystem* getFileSystem() const { return m_fileSystem; }

  SymbolTable* getSymbolTable() { return m_symbolTable; }
  const SymbolTable* getSymbolTable() const { return m_symbolTable; }

  LogListener* getLogListener() { return m_logListener; }
  const LogListener* getLogListener() const { return m_logListener; }

  Precompiled* getPrecompiled() { return m_precompiled; }
  const Precompiled* getPrecompiled() const { return m_precompiled; }

  CommandLineParser* getCommandLineParser() { return m_commandLineParser; }
  const CommandLineParser* getCommandLineParser() const {
    return m_commandLineParser;
  }

 private:
  FileSystem* const m_fileSystem = nullptr;
  SymbolTable* const m_symbolTable = nullptr;
  LogListener* const m_logListener = nullptr;
  Precompiled* const m_precompiled = nullptr;
  ErrorContainer* const m_errorContainer = nullptr;
  CommandLineParser* const m_commandLineParser = nullptr;

  const bool m_ownsFileSystem = false;
  const bool m_ownsSymbolTable = false;
  const bool m_ownsLogListener = false;
  const bool m_ownsPrecompiled = false;
  const bool m_ownsErrorContainer = false;
  const bool m_ownsCommandLineParser = false;
};
};  // namespace SURELOG

#endif  // SURELOG_SESSION_H
