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

#ifndef SURELOG_FILESYSTEM_H
#define SURELOG_FILESYSTEM_H
#pragma once

#include <cstdint>
#include <filesystem>
#include <string_view>

namespace SURELOG {
class PathId;
class SymbolId;
class SymbolTable;

class FileSystem {
 public:
  static FileSystem *getInstance();
  static FileSystem *setInstance(FileSystem *const fileSystem);

 public:
  virtual PathId toPathId(const std::filesystem::path &path,
                          SymbolTable *const symbolTable);
  virtual const std::string &toSymbol(PathId id);
  virtual std::filesystem::path toPath(PathId id);

  virtual const std::filesystem::path &getCwd();
  virtual PathId getCwd(SymbolTable *const symbolTable);

  virtual PathId copy(PathId id, SymbolTable *const toSymbolTable);

  virtual ~FileSystem();

 protected:
  const std::filesystem::path m_cwd;

 private:
  static FileSystem *sInstance;

 protected:
  FileSystem(const std::filesystem::path &cwd);

 private:
  FileSystem(const FileSystem &rhs) = delete;
  FileSystem &operator=(const FileSystem &rhs) = delete;
};
}  // namespace SURELOG

#endif  // SURELOG_FILESYSTEM_H
