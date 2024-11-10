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
 * File:   PlatformFileSystem.h
 * Author: hs
 *
 * Created on October 8, 2022, 3:00 AM
 */

#ifndef SURELOG_PLATFORMFILESYSTEM_H
#define SURELOG_PLATFORMFILESYSTEM_H
#pragma once

#include <Surelog/Common/FileSystem.h>

#include <cstdint>
#include <functional>
#include <memory>
#include <mutex>
#include <set>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace SURELOG {
class SymbolTable;

/**
 * class PlatformFileSystem
 *
 * Native platform specific file system implementation.
 *
 * Note, thie is final class from Surelogs perspective, but
 * to make it simpler for users to override and change, keeping
 * it overridable.
 */
class PlatformFileSystem /*final*/ : public FileSystem {
 public:
  struct Configuration final {
    std::filesystem::path m_sourceDir;
    std::filesystem::path m_cacheDir;
  };
  using Configurations = std::vector<Configuration>;

  struct Mapping final {
    std::string m_what;
    std::string m_with;
  };
  using Mappings = std::vector<Mapping>;

 public:
  PathId toPathId(std::string_view path, SymbolTable *symbolTable) override;
  std::filesystem::path toPlatformAbsPath(PathId id) override;
  std::filesystem::path toPlatformRelPath(PathId id) override;

  std::pair<std::filesystem::path, std::filesystem::path> toSplitPlatformPath(
      PathId id) override;

  std::string getWorkingDir() override;
  std::set<std::string> getWorkingDirs() override;

  using FileSystem::openInput;
  std::istream &openInput(PathId fileId, std::ios_base::openmode mode) override;
  bool close(std::istream &strm) override;

  using FileSystem::openOutput;
  std::ostream &openOutput(PathId fileId,
                           std::ios_base::openmode mode) override;
  bool close(std::ostream &strm) override;

  using FileSystem::saveContent;
  bool saveContent(PathId fileId, const char *content, std::streamsize length,
                   bool useTemp) override;

  bool addMapping(std::string_view what, std::string_view with) override;
  std::string remap(std::string_view what) override;

  bool addWorkingDirectoryCacheEntry(std::string_view prefix,
                                     std::string_view suffix) override;

  PathId getProgramFile(std::string_view hint,
                        SymbolTable *symbolTable) override;

  PathId getWorkingDir(std::string_view dir, SymbolTable *symbolTable) override;
  PathId getOutputDir(std::string_view dir, SymbolTable *symbolTable) override;
  PathId getPrecompiledDir(PathId programId, SymbolTable *symbolTable) override;

  using FileSystem::getLogFile;
  PathId getLogFile(bool isUnitCompilation, std::string_view filename,
                    SymbolTable *symbolTable) override;

  PathId getCacheDir(bool isUnitCompilation, std::string_view dirname,
                     SymbolTable *symbolTable) override;

  PathId getCompileDir(bool isUnitCompilation,
                       SymbolTable *symbolTable) override;

  using FileSystem::getPpOutputFile;
  PathId getPpOutputFile(bool isUnitCompilation, PathId sourceFileId,
                         std::string_view libraryName,
                         SymbolTable *symbolTable) override;

  using FileSystem::getPpCacheFile;
  PathId getPpCacheFile(bool isUnitCompilation, PathId sourceFileId,
                        std::string_view libraryName, bool isPrecompiled,
                        SymbolTable *symbolTable) override;

  using FileSystem::getParseCacheFile;
  PathId getParseCacheFile(bool isUnitCompilation, PathId ppFileId,
                           std::string_view libraryName, bool isPrecompiled,
                           SymbolTable *symbolTable) override;

  using FileSystem::getPythonCacheFile;
  PathId getPythonCacheFile(bool isUnitCompilation, PathId sourceFileId,
                            std::string_view libraryName,
                            SymbolTable *symbolTable) override;

  PathId getPpMultiprocessingDir(bool isUnitCompilation,
                                 SymbolTable *symbolTable) override;
  PathId getParserMultiprocessingDir(bool isUnitCompilation,
                                     SymbolTable *symbolTable) override;

  PathId getChunkFile(PathId ppFileId, int32_t chunkIndex,
                      SymbolTable *symbolTable) override;

  PathId getCheckerDir(bool isUnitCompilation,
                       SymbolTable *symbolTable) override;
  PathId getCheckerFile(PathId uhdmFileId, SymbolTable *symbolTable) override;
  PathId getCheckerHtmlFile(PathId uhdmFileId,
                            SymbolTable *symbolTable) override;
  PathId getCheckerHtmlFile(PathId uhdmFileId, int32_t index,
                            SymbolTable *symbolTable) override;

  bool rename(PathId whatId, PathId toId) override;
  bool remove(PathId fileId) override;
  bool mkdir(PathId dirId) override;
  bool rmdir(PathId dirId) override;
  bool mkdirs(PathId dirId) override;
  bool rmtree(PathId dirId) override;
  bool exists(PathId id) override;
  bool exists(PathId dirId, std::string_view descendant) override;
  bool isDirectory(PathId id) override;
  bool isRegularFile(PathId id) override;
  bool filesize(PathId fileId, std::streamsize *result) override;
  std::filesystem::file_time_type modtime(
      PathId fileId, std::filesystem::file_time_type defaultOnFail) override;

  PathId locate(std::string_view name, const PathIdVector &directories,
                SymbolTable *symbolTable) override;

  PathIdVector &collect(PathId dirId, SymbolTable *symbolTable,
                        PathIdVector &container) override;
  PathIdVector &collect(PathId dirId, std::string_view extension,
                        SymbolTable *symbolTable,
                        PathIdVector &container) override;
  PathIdVector &matching(PathId dirId, std::string_view pattern,
                         SymbolTable *symbolTable,
                         PathIdVector &container) override;
  PathIdVector &matching(PathId dirId, const std::regex &pattern,
                         SymbolTable *symbolTable,
                         PathIdVector &container) override;

  PathId getChild(PathId id, std::string_view name,
                  SymbolTable *symbolTable) override;
  PathId getSibling(PathId id, std::string_view name,
                    SymbolTable *symbolTable) override;
  PathId getParent(PathId id, SymbolTable *symbolTable) override;
  std::pair<SymbolId, std::string_view> getLeaf(
      PathId id, SymbolTable *symbolTable) override;
  std::pair<SymbolId, std::string_view> getType(
      PathId id, SymbolTable *symbolTable) override;

  void printConfiguration(std::ostream &out) override;

  explicit PlatformFileSystem(const std::filesystem::path &workingDir);
  ~PlatformFileSystem() override;

 protected:
  // Internal helpers
  void addConfiguration(const std::filesystem::path &sourceDir);
  std::filesystem::path getPrecompiledDir(SymbolTable *symbolTable);

  virtual std::istream &openInput(const std::filesystem::path &filepath,
                                  std::ios_base::openmode mode);
  virtual std::ostream &openOutput(const std::filesystem::path &filepath,
                                   std::ios_base::openmode mode);

  // ref: https://stackoverflow.com/a/18940595
  template <class T>
  struct Comparer final {
    using is_transparent = std::true_type;
    // helper does some magic in order to reduce the number of
    // pairs of types we need to know how to compare: it turns
    // everything into a pointer, and then uses `std::less<T*>`
    // to do the comparison:
    struct Helper final {
      T *ptr = nullptr;
      Helper() : ptr(nullptr) {}
      Helper(Helper const &) = default;
      Helper(T *p) : ptr(p) {}  // NOLINT
      template <class U>
      Helper(std::shared_ptr<U> const &sp) : ptr(sp.get()) {}  // NOLINT
      template <class U, class... Ts>
      Helper(std::unique_ptr<U, Ts...> const &up) : ptr(up.get()) {}  // NOLINT
      // && optional: enforces rvalue use only
      bool operator<(const Helper &o) const {
        return std::less<T *>()(ptr, o.ptr);
      }
    };
    // Without helper, we would need 2^n different overloads, where
    // n is the number of types we want to support (so, 8 with
    // raw pointers, unique pointers, and shared pointers). That
    // seems silly.
    // && helps enforce rvalue use only
    bool operator()(Helper const &&lhs, Helper const &&rhs) const {
      return lhs < rhs;
    }
  };

  using InputStreams =
      std::set<std::unique_ptr<std::istream>, Comparer<std::istream>>;
  using OutputStreams =
      std::set<std::unique_ptr<std::ostream>, Comparer<std::ostream>>;

  const std::filesystem::path m_workingDir;

  std::mutex m_inputStreamsMutex;
  std::mutex m_outputStreamsMutex;
  InputStreams m_inputStreams;
  OutputStreams m_outputStreams;

  Configurations m_configurations;
  Mappings m_mappings;
  std::filesystem::path m_outputDir;

 public:
  PlatformFileSystem(const PlatformFileSystem &rhs) = delete;
  PlatformFileSystem &operator=(const PlatformFileSystem &rhs) = delete;
};
}  // namespace SURELOG

#endif  // SURELOG_PLATFORMFILESYSTEM_H
