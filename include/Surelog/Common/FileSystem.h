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

#include <Surelog/Common/PathId.h>

#include <cstdint>
#include <filesystem>
#include <istream>
#include <memory>
#include <mutex>
#include <ostream>
#include <set>
#include <sstream>
#include <string_view>

namespace SURELOG {
class PathId;
class SymbolId;
class SymbolTable;

/**
 * class FileSystem
 *
 * Implements a thin layer between Surelog & the native file system.
 * The same interface can also be used to bypass the entire file system
 * and implement a custom home-grown one. All interactions between the
 * FileSystem and Surelog use PathId (in conjunctin with SymbolTable).
 *
 * A sub-classed implementation of the FileSystem can be used to
 * implement support for UNC paths, compressed tarballs of source and
 * cache files, and a virtual file system (i.e. no writes to disk). A
 * example of such are implemented in FileSystem_test.cpp for reference.
 *
 * A few words on convention:
 *
 * Stream convention:
 *   Read/Write is used in context to text streams
 *   and Load/Save in context to binary streams.
 *
 * toPath vs. toSymbol:
 *   toPath returns a std::filesystem::path representation of the PathId.
 *     The path itself can be non-existant. in certain cases, however
 *     it does have to exist because it is t be used by external processes
 *     like CMake or a system call to batch script.
 *   toSymbol returns a printable representation of the PathId. This doesn't
 *     necessarily have to be a path (in FileSystem implementation it is but
 *     doesn't have to be. What the symbol represent is up to the
 *     interpretation of the FileSystem implementation itself.
 *
 */
class FileSystem {
 public:
  static constexpr std::string_view kCacheDirName = "cache";
  static constexpr std::string_view kAllCompileDirName = "slpp_all";
  static constexpr std::string_view kUnitCompileDirName = "slpp_unit";
  static constexpr std::string_view kLogFileName = "surelog.log";
  static constexpr std::string_view kPrecompiledDirName = "pkg";
  static constexpr std::string_view kMultiprocessingPpDirName = "mp_preprocess";
  static constexpr std::string_view kMultiprocessingParserDirName = "mp_parser";
  static constexpr std::string_view kCheckerDirName = "checker";
  static constexpr std::string_view kPreprocessLibraryDirName = "lib";
  static constexpr std::string_view kPreprocessCacheDirName = kCacheDirName;
  static constexpr std::string_view kParserCacheDirName = kCacheDirName;
  static constexpr std::string_view kPythonCacheDirName = kCacheDirName;

 public:
  struct Configuration {
    std::filesystem::path m_sourceDir;
    std::filesystem::path m_cacheDir;
  };
  typedef std::vector<Configuration> Configurations;

 public:
  static FileSystem *getInstance();
  static FileSystem *setInstance(FileSystem *fileSystem);

  // Returns the executing binary's path by querying the OS
  static std::filesystem::path getProgramPath();

  // Normalizes the input path
  //   Standardizes the directory separator based on platform
  //   No trailing slash regardless of whether the path exists or not
  //   Shortens the path by removing any '.' and '..'
  static std::filesystem::path normalize(const std::filesystem::path &p);
  static bool is_subpath(const std::filesystem::path &parent,
                         const std::filesystem::path &child);

 public:
  // Convert a native filesystem path to PathId
  virtual PathId toPathId(std::string_view path, SymbolTable *symbolTable);
  // Returns the string/printable representation of the input id
  virtual std::string_view toSymbol(PathId id);
  // Returns either the absolute or relative native filesystem path
  // based on how the FileSystem is configured.
  virtual std::filesystem::path toPath(PathId id);

  // Returns the current working directory as either the native filesystem
  // path or as a PathId registered in the input SymbolTable.
  virtual const std::filesystem::path &getWorkingDir();
  virtual PathId getWorkingDir(SymbolTable *symbolTable);

  // Open/Close an input stream represented by the input PathId.
  // openForRead defaults the ios_base::openmode to ios_base::text
  // openForLoad defaults the ios_base::openmode to ios_base::binary
  virtual std::istream &openInput(PathId fileId, std::ios_base::openmode mode);
  std::istream &openForRead(PathId fileId);
  std::istream &openForLoad(PathId fileId);
  virtual bool close(std::istream &strm);

  // Open/Close an output stream represented by the input PathId.
  // openForWrite defaults the ios_base::openmode to ios_base::text
  // openForSave defaults the ios_base::openmode to ios_base::binary
  virtual std::ostream &openOutput(PathId fileId, std::ios_base::openmode mode);
  std::ostream &openForWrite(PathId fileId);
  std::ostream &openForSave(PathId fileId);
  virtual bool close(std::ostream &strm);

  // Read/Write content i.e. blob of text as string from file represented by
  // input PathId. onlyIfModified defaults to true if using the overloaded
  // variation.
  virtual bool readContent(PathId fileId, std::string &content);
  virtual bool writeContent(PathId fileId, std::string_view content,
                            bool onlyIfModified);
  bool writeContent(PathId fileId, std::string_view content);

  // Read/Write lines of text from file represented by input PathId.
  // onlyIfModified defaults to true if using the overloaded variation.
  virtual bool readLines(PathId fileId, std::vector<std::string> &lines);
  virtual bool writeLines(PathId fileId, const std::vector<std::string> &lines,
                          bool onlyIfModified);
  bool writeLines(PathId fileId, const std::vector<std::string> &lines);

  // Read specific line of text from file represented by input PathId.
  // Note that the first line in the file is at index 1 (i.e. 1 based indexing)
  virtual bool readLine(PathId fileId, int32_t index, std::string &content);

  // Load/Save content i.e. blob from file represented by input PathId.
  // useTemp defaults to false if using the overloaded variations.
  virtual bool loadContent(PathId fileId, std::vector<char> &data);
  virtual bool saveContent(PathId fileId, const char *content,
                           std::streamsize length, bool useTemp);
  bool saveContent(PathId fileId, const char *content, std::streamsize length);
  bool saveContent(PathId fileId, const std::vector<char> &data, bool useTemp);
  bool saveContent(PathId fileId, const std::vector<char> &data);

  virtual PathId getProgramFile(std::string_view hint,
                                SymbolTable *symbolTable);

  virtual PathId getWorkingDir(std::string_view dir, SymbolTable *symbolTable);
  virtual PathId getOutputDir(std::string_view dir, SymbolTable *symbolTable);
  virtual PathId getPrecompiledDir(PathId programId, SymbolTable *symbolTable);

  virtual PathId getLogFile(bool isUnitCompilation, SymbolTable *symbolTable);
  virtual PathId getLogFile(bool isUnitCompilation, std::string_view filename,
                            SymbolTable *symbolTable);

  virtual PathId getCacheDir(bool isUnitCompilation, SymbolTable *symbolTable);
  virtual PathId getCacheDir(bool isUnitCompilation, std::string_view dirname,
                             SymbolTable *symbolTable);

  virtual PathId getCompileDir(bool isUnitCompilation,
                               SymbolTable *symbolTable);

  virtual PathId getPpOutputFile(bool isUnitCompilation, PathId sourceFileId,
                                 std::string_view libraryName,
                                 SymbolTable *symbolTable);
  virtual PathId getPpOutputFile(bool isUnitCompilation, PathId sourceFileId,
                                 SymbolId libraryNameId,
                                 SymbolTable *symbolTable);

  virtual PathId getPpCacheFile(bool isUnitCompilation, PathId sourceFileId,
                                std::string_view libraryName,
                                bool isPrecompiled, SymbolTable *symbolTable);
  virtual PathId getPpCacheFile(bool isUnitCompilation, PathId sourceFileId,
                                SymbolId libraryNameId, bool isPrecompiled,
                                SymbolTable *symbolTable);

  virtual PathId getParseCacheFile(bool isUnitCompilation, PathId ppFileId,
                                   std::string_view libraryName,
                                   bool isPrecompiled,
                                   SymbolTable *symbolTable);
  virtual PathId getParseCacheFile(bool isUnitCompilation, PathId ppFileId,
                                   SymbolId libraryNameId, bool isPrecompiled,
                                   SymbolTable *symbolTable);

  virtual PathId getPythonCacheFile(bool isUnitCompilation, PathId sourceFileId,
                                    std::string_view libraryName,
                                    SymbolTable *symbolTable);
  virtual PathId getPythonCacheFile(bool isUnitCompilation, PathId sourceFileId,
                                    SymbolId libraryNameId,
                                    SymbolTable *symbolTable);

  virtual PathId getPpMultiprocessingDir(bool isUnitCompilation,
                                         SymbolTable *symbolTable);
  virtual PathId getParserMultiprocessingDir(bool isUnitCompilation,
                                             SymbolTable *symbolTable);

  virtual PathId getChunkFile(PathId ppFileId, int32_t chunkIndex,
                              SymbolTable *symbolTable);

  virtual PathId getCheckerDir(bool isUnitCompilation,
                               SymbolTable *symbolTable);
  virtual PathId getCheckerFile(PathId uhdmFileId, SymbolTable *symbolTable);
  virtual PathId getCheckerHtmlFile(PathId uhdmFileId,
                                    SymbolTable *symbolTable);
  virtual PathId getCheckerHtmlFile(PathId uhdmFileId, int32_t index,
                                    SymbolTable *symbolTable);

  // Rename directory/file represented by 'whatId' to 'toId'
  virtual bool rename(PathId whatId, PathId toId);

  // Remove the file represented by 'fileId'. Note this cannot be used
  // for removing directories.
  virtual bool remove(PathId fileId);

  // Make a new directory represented by the input 'dirId'. The parent of the
  // input 'dirId' should already exist.
  virtual bool mkdir(PathId dirId);

  // Remove the directory represented by the input 'dirId'. The directory has
  // to be empty. For non-empty directories, use rmtree.
  virtual bool rmdir(PathId dirId);

  // Make a new directory and all its subsequent non-existent parents.
  virtual bool mkdirs(PathId dirId);

  // Remove the direcoty represented by input 'dirId' and all
  // subdirectories & files under it.
  virtual bool rmtree(PathId dirId);

  // Returns true if the input PathId is a pre-existing native filesystem path.
  virtual bool exists(PathId id);

  // Returns true if descendant exists under the directory
  // represented by the input PathId.
  virtual bool exists(PathId dirId, std::string_view descendant);

  // Returns true if the input id represents a directory.
  virtual bool isDirectory(PathId id);

  // Returns true if the input id represents a file.
  virtual bool isRegularFile(PathId id);

  // Returns the length of the file represented by the input id.
  virtual bool filesize(PathId fileId, std::streamsize *result);

  // Returns the 'last modified time' for the input fileId, or the default
  // if the file was not found or the operation failed.
  virtual std::filesystem::file_time_type modtime(
      PathId fileId, std::filesystem::file_time_type defaultOnFail);
  std::filesystem::file_time_type modtime(PathId fileId);

  // Find the first directory in input 'directories' that contain
  // directory/file named 'name'.
  // If found, return the PathId representing that directory/file
  // and otherwise BadPathId
  virtual PathId locate(std::string_view name, const PathIdVector &directories,
                        SymbolTable *symbolTable);

  // Returns a list of all files under the input 'dirId'.
  virtual PathIdVector &collect(PathId dirId, SymbolTable *symbolTable,
                                PathIdVector &container);
  // Returns a list of all files under the input 'dirId',
  // filtered by 'extension'.
  virtual PathIdVector &collect(PathId dirId, std::string_view extension,
                                SymbolTable *symbolTable,
                                PathIdVector &container);
  // Returns all files under the input 'dirId' that matches the input 'pattern'
  virtual PathIdVector &matching(PathId dirId, std::string_view pattern,
                                 SymbolTable *symbolTable,
                                 PathIdVector &container);

  // Returns child, sibling, parent, leaf and type of filesystem path
  virtual PathId getChild(PathId id, std::string_view name,
                          SymbolTable *symbolTable);
  virtual PathId getSibling(PathId id, std::string_view name,
                            SymbolTable *symbolTable);
  virtual PathId getParent(PathId id, SymbolTable *symbolTable);
  virtual std::pair<SymbolId, std::string_view> getLeaf(
      PathId id, SymbolTable *symbolTable);
  virtual std::pair<SymbolId, std::string_view> getType(
      PathId id, SymbolTable *symbolTable);

  // Returns a copy of the input id registered with the input SymbolTable.
  virtual PathId copy(PathId id, SymbolTable *toSymbolTable);

  // Returns all accumulated working directories (including
  // the externally registered ones)
  virtual std::set<std::filesystem::path> getWorkingDirs();

  // For debugging: Print internal configuration
  virtual void printConfiguration(std::ostream &out);

  virtual ~FileSystem();

 protected:
  // Internal helpers
  std::filesystem::path toRelPath(PathId id);
  void addConfiguration(const std::filesystem::path &dir);

  virtual std::istream &openInput(const std::filesystem::path &filepath,
                                  std::ios_base::openmode mode);
  virtual std::ostream &openOutput(const std::filesystem::path &filepath,
                                   std::ios_base::openmode mode);

  // ref: https://stackoverflow.com/a/18940595
  template <class T>
  struct Comparer final {
    typedef std::true_type is_transparent;
    // helper does some magic in order to reduce the number of
    // pairs of types we need to know how to compare: it turns
    // everything into a pointer, and then uses `std::less<T*>`
    // to do the comparison:
    struct Helper final {
      T *ptr = nullptr;
      Helper() : ptr(nullptr) {}
      Helper(Helper const &) = default;
      Helper(T *p) : ptr(p) {}
      template <class U>
      Helper(std::shared_ptr<U> const &sp) : ptr(sp.get()) {}
      template <class U, class... Ts>
      Helper(std::unique_ptr<U, Ts...> const &up) : ptr(up.get()) {}
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

  typedef std::set<std::unique_ptr<std::istream>, Comparer<std::istream>>
      InputStreams;
  typedef std::set<std::unique_ptr<std::ostream>, Comparer<std::ostream>>
      OutputStreams;

  const std::filesystem::path m_workingDir;

  std::mutex m_inputStreamsMutex;
  std::mutex m_outputStreamsMutex;
  InputStreams m_inputStreams;
  OutputStreams m_outputStreams;

  Configurations m_configurations;
  std::filesystem::path m_outputDir;

  std::istringstream m_nullInputStream;
  std::ostringstream m_nullOutputStream;

 private:
  static FileSystem *sInstance;

 protected:
  explicit FileSystem(const std::filesystem::path &workingDir);

 private:
  FileSystem(const FileSystem &rhs) = delete;
  FileSystem &operator=(const FileSystem &rhs) = delete;
};
}  // namespace SURELOG

#endif  // SURELOG_FILESYSTEM_H
