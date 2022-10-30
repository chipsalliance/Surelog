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
 * File:   FileSystem.h
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
#include <ostream>
#include <sstream>
#include <string>
#include <string_view>

namespace SURELOG {
class PathId;
class SymbolId;
class SymbolTable;

/**
 * class FileSystem
 *
 * Abstract interface between Surelog & file system access. The interface can
 * be used to bypass the platform/OS specific file system entirely by
 * implementing a custom home-grown one. All interactions between the
 * FileSystem and Surelog use PathId (in conjunction with SymbolTable) for
 * communication.
 *
 * A sub-classed implementation of the FileSystem can be used to
 * implement support for UNC paths, compressed tarballs of source and
 * cache files, and a virtual file system (i.e. no read/writes to disk). A
 * example of such an implementation is in PlatformFileSystem_test.cpp
 * for reference.
 *
 * A few words on convention:
 *
 * Stream convention:
 *   Read/Write is used in context to text streams
 *   and Load/Save in context to binary streams.
 *
 * toPath vs. toPlatformPath:
 *   toPath returns a printable representation of the PathId. This doesn't
 *     necessarily have to be a resolve-able path. What the string represent
 *     is up to the interpretation of the FileSystem implementation itself.
 * 
 *   toPlatformPath returns a std::filesystem::path representation of PathId.
 *     The path itself can be non-existant, in certain cases, however
 *     it does have to exist because it is to be used by external processes
 *     like CMake or a system call to batch script. In short, the return path
 *     needs to be resolve-able by the OS.
 *
 *   NOTE:
 *     toPath(id) == toPath(toPathId(toPath(id))) but
 *     toPlatformPath(id) <> toPlatformPath(toPathId(toPlatformPath(id)))
 * 
 *     i.e. string representation can be converted to id (and vice-versa)
 *     using toPathId & toPath but the same is not necessarily guaranteed
 *     between toPathId & toPlatformPath (primarily because of potential
 *     normalization).
 *
 * Mappings:
 *   Mappings are basically replacement symbols to use in place of the
 *   original. These are/can be used to retarget PathId to point to a
 *   different target.
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
  virtual PathId toPathId(std::string_view path, SymbolTable *symbolTable) = 0;
  // Returns the string/printable representation of the input id
  virtual std::string_view toPath(PathId id);
  // Returns platform specific path i.e. a path that can be mapped on disk
  // and can be used for, say, system commands.
  virtual std::filesystem::path toPlatformPath(PathId id) = 0;

  // Returns the current working directory as either the native filesystem
  // path or as a PathId registered in the input SymbolTable.
  virtual std::string getWorkingDir() = 0;
  virtual PathId getWorkingDir(SymbolTable *symbolTable);
  // Returns all accumulated working directories (including
  // the externally registered ones)
  virtual std::set<std::string> getWorkingDirs() = 0;

  // Open/Close an input stream represented by the input PathId.
  // openForRead defaults the ios_base::openmode to ios_base::text
  // openForLoad defaults the ios_base::openmode to ios_base::binary
  virtual std::istream &openInput(PathId fileId, std::ios_base::openmode mode) = 0;
  std::istream &openForRead(PathId fileId);
  std::istream &openForLoad(PathId fileId);
  virtual bool close(std::istream &strm) = 0;

  // Open/Close an output stream represented by the input PathId.
  // openForWrite defaults the ios_base::openmode to ios_base::text
  // openForSave defaults the ios_base::openmode to ios_base::binary
  virtual std::ostream &openOutput(PathId fileId, std::ios_base::openmode mode) = 0;
  std::ostream &openForWrite(PathId fileId);
  std::ostream &openForSave(PathId fileId);
  virtual bool close(std::ostream &strm) = 0;

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
                           std::streamsize length, bool useTemp) = 0;
  bool saveContent(PathId fileId, const char *content, std::streamsize length);
  bool saveContent(PathId fileId, const std::vector<char> &data, bool useTemp);
  bool saveContent(PathId fileId, const std::vector<char> &data);

  // Register a path remapping entry and call to remap a path
  // These can be used to make caches portable and to reconnect sources
  // after relocation.
  virtual bool addMapping(std::string_view what, std::string_view with) = 0;
  virtual std::string remap(std::string_view what) = 0;

  // Path computation APIs for different contexts
  virtual PathId getProgramFile(std::string_view hint,
                                SymbolTable *symbolTable) = 0;

  virtual PathId getWorkingDir(std::string_view dir, SymbolTable *symbolTable) = 0;
  virtual PathId getOutputDir(std::string_view dir, SymbolTable *symbolTable) = 0;
  virtual PathId getPrecompiledDir(PathId programId, SymbolTable *symbolTable) = 0;

  virtual PathId getLogFile(bool isUnitCompilation, std::string_view filename,
                            SymbolTable *symbolTable) = 0;
  PathId getLogFile(bool isUnitCompilation, SymbolTable *symbolTable);

  virtual PathId getCacheDir(bool isUnitCompilation, std::string_view dirname,
                             SymbolTable *symbolTable) = 0;
  PathId getCacheDir(bool isUnitCompilation, SymbolTable *symbolTable);

  virtual PathId getCompileDir(bool isUnitCompilation,
                               SymbolTable *symbolTable) = 0;

  virtual PathId getPpOutputFile(bool isUnitCompilation, PathId sourceFileId,
                                 std::string_view libraryName,
                                 SymbolTable *symbolTable) = 0;
  PathId getPpOutputFile(bool isUnitCompilation, PathId sourceFileId,
                                 SymbolId libraryNameId,
                                 SymbolTable *symbolTable);

  virtual PathId getPpCacheFile(bool isUnitCompilation, PathId sourceFileId,
                                std::string_view libraryName,
                                bool isPrecompiled, SymbolTable *symbolTable) = 0;
  PathId getPpCacheFile(bool isUnitCompilation, PathId sourceFileId,
                                SymbolId libraryNameId, bool isPrecompiled,
                                SymbolTable *symbolTable);

  virtual PathId getParseCacheFile(bool isUnitCompilation, PathId ppFileId,
                                   std::string_view libraryName,
                                   bool isPrecompiled,
                                   SymbolTable *symbolTable) = 0;
  PathId getParseCacheFile(bool isUnitCompilation, PathId ppFileId,
                                   SymbolId libraryNameId, bool isPrecompiled,
                                   SymbolTable *symbolTable);

  virtual PathId getPythonCacheFile(bool isUnitCompilation, PathId sourceFileId,
                                    std::string_view libraryName,
                                    SymbolTable *symbolTable) = 0;
  virtual PathId getPythonCacheFile(bool isUnitCompilation, PathId sourceFileId,
                                    SymbolId libraryNameId,
                                    SymbolTable *symbolTable);

  virtual PathId getPpMultiprocessingDir(bool isUnitCompilation,
                                         SymbolTable *symbolTable) = 0;
  virtual PathId getParserMultiprocessingDir(bool isUnitCompilation,
                                             SymbolTable *symbolTable) = 0;

  virtual PathId getChunkFile(PathId ppFileId, int32_t chunkIndex,
                              SymbolTable *symbolTable) = 0;

  virtual PathId getCheckerDir(bool isUnitCompilation,
                               SymbolTable *symbolTable) = 0;
  virtual PathId getCheckerFile(PathId uhdmFileId, SymbolTable *symbolTable) = 0;
  virtual PathId getCheckerHtmlFile(PathId uhdmFileId,
                                    SymbolTable *symbolTable) = 0;
  virtual PathId getCheckerHtmlFile(PathId uhdmFileId, int32_t index,
                                    SymbolTable *symbolTable) = 0;

  // Rename directory/file represented by 'whatId' to 'toId'
  virtual bool rename(PathId whatId, PathId toId) = 0;

  // Remove the file represented by 'fileId'. Note this cannot be used
  // for removing directories.
  virtual bool remove(PathId fileId) = 0;

  // Make a new directory represented by the input 'dirId'. The parent of the
  // input 'dirId' should already exist.
  virtual bool mkdir(PathId dirId) = 0;

  // Remove the directory represented by the input 'dirId'. The directory has
  // to be empty. For non-empty directories, use rmtree.
  virtual bool rmdir(PathId dirId) = 0;

  // Make a new directory and all its subsequent non-existent parents.
  virtual bool mkdirs(PathId dirId) = 0;

  // Remove the direcoty represented by input 'dirId' and all
  // subdirectories & files under it.
  virtual bool rmtree(PathId dirId) = 0;

  // Returns true if the input PathId is a pre-existing native filesystem path.
  virtual bool exists(PathId id) = 0;

  // Returns true if descendant exists under the directory
  // represented by the input PathId.
  virtual bool exists(PathId dirId, std::string_view descendant) = 0;

  // Returns true if the input id represents a directory.
  virtual bool isDirectory(PathId id) = 0;

  // Returns true if the input id represents a file.
  virtual bool isRegularFile(PathId id) = 0;

  // Returns the length of the file represented by the input id.
  virtual bool filesize(PathId fileId, std::streamsize *result) = 0;

  // Returns the 'last modified time' for the input fileId, or the default
  // if the file was not found or the operation failed.
  virtual std::filesystem::file_time_type modtime(
      PathId fileId, std::filesystem::file_time_type defaultOnFail) = 0;
  std::filesystem::file_time_type modtime(PathId fileId);

  // Find the first directory in input 'directories' that contain
  // directory/file named 'name'.
  // If found, return the PathId representing that directory/file
  // and otherwise BadPathId
  virtual PathId locate(std::string_view name, const PathIdVector &directories,
                        SymbolTable *symbolTable) = 0;

  // Returns a list of all files under the input 'dirId'.
  virtual PathIdVector &collect(PathId dirId, SymbolTable *symbolTable,
                                PathIdVector &container) = 0;
  // Returns a list of all files under the input 'dirId',
  // filtered by 'extension'.
  virtual PathIdVector &collect(PathId dirId, std::string_view extension,
                                SymbolTable *symbolTable,
                                PathIdVector &container) = 0;
  // Returns all files under the input 'dirId' that matches the input 'pattern'
  virtual PathIdVector &matching(PathId dirId, std::string_view pattern,
                                 SymbolTable *symbolTable,
                                 PathIdVector &container) = 0;

  // Returns child, sibling, parent, leaf and type of filesystem path
  virtual PathId getChild(PathId id, std::string_view name,
                          SymbolTable *symbolTable) = 0;
  virtual PathId getSibling(PathId id, std::string_view name,
                            SymbolTable *symbolTable) = 0;
  virtual PathId getParent(PathId id, SymbolTable *symbolTable) = 0;
  virtual std::pair<SymbolId, std::string_view> getLeaf(
      PathId id, SymbolTable *symbolTable) = 0;
  virtual std::pair<SymbolId, std::string_view> getType(
      PathId id, SymbolTable *symbolTable) = 0;

  // Returns a copy of the input id registered with the input SymbolTable.
  virtual PathId copy(PathId id, SymbolTable *toSymbolTable);

  // For debugging: Print internal configuration
  virtual void printConfiguration(std::ostream &out) = 0;

  virtual ~FileSystem() = default;

 protected:
  std::istringstream m_nullInputStream;
  std::ostringstream m_nullOutputStream;

 private:
  static FileSystem *sInstance;

 protected:
  FileSystem() = default;

 private:
  FileSystem(const FileSystem &rhs) = delete;
  FileSystem &operator=(const FileSystem &rhs) = delete;
};
}  // namespace SURELOG

#endif  // SURELOG_FILESYSTEM_H
