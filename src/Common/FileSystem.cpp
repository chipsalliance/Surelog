/*
 Copyright 2022 chipsalliance

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
 * File:   FileSystem.cpp
 * Author: hs
 *
 * Created on June 1, 2022, 3:00 AM
 */

#include <Surelog/Common/FileSystem.h>
#include <Surelog/Common/PathId.h>
#include <Surelog/SourceCompile/SymbolTable.h>

#if defined(_MSC_VER)
#define NOMINMAX
#include <Windows.h>
#else
#include <sys/param.h>
#include <unistd.h>
#endif

namespace SURELOG {
FileSystem *FileSystem::sInstance = nullptr;

FileSystem *FileSystem::getInstance() {
  if (sInstance == nullptr) {
    sInstance = new FileSystem(std::filesystem::current_path());
  }
  return sInstance;
}

FileSystem *FileSystem::setInstance(FileSystem *const fileSystem) {
  FileSystem *const instance = sInstance;
  sInstance = fileSystem;
  return instance;
}

FileSystem::FileSystem(const std::filesystem::path &cwd) : m_cwd(cwd) {}

FileSystem::~FileSystem() {
  if (sInstance == this) setInstance(nullptr);
}

PathId FileSystem::toPathId(const std::filesystem::path &path,
                            SymbolTable *const symbolTable) {
  if (path.empty()) return BadPathId;

  auto [symbolId, symbol] = symbolTable->add(path.string());
  return PathId(symbolTable, (RawSymbolId)symbolId, symbol);
}

const std::string &FileSystem::toSymbol(PathId id) {
  return id ? id.getSymbolTable()->getSymbol((SymbolId)id)
            : SymbolTable::getBadSymbol();
}

std::filesystem::path FileSystem::toPath(PathId id) {
  if (!id) return std::filesystem::path();

  const std::string &symbol = toSymbol(id);
  return (symbol == BadRawSymbol) ? std::filesystem::path()
                                  : std::filesystem::path(symbol);
}

const std::filesystem::path &FileSystem::getCwd() { return m_cwd; }

PathId FileSystem::getCwd(SymbolTable *const symbolTable) {
  return toPathId(m_cwd, symbolTable);
}

PathId FileSystem::copy(PathId id, SymbolTable *const toSymbolTable) {
  if (!id) return BadPathId;

  const std::string &symbol = toSymbol(id);
  return (symbol == BadRawSymbol) ? BadPathId : toPathId(symbol, toSymbolTable);
}
}  // namespace SURELOG
