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
  static FileSystem *getInstance();
  static FileSystem *setInstance(FileSystem *fileSystem);

 public:
  // Convert a native filesystem path to PathId
  virtual PathId toPathId(const std::filesystem::path &path,
                          SymbolTable *symbolTable);
  // Returns the string/printable representation of the input id
  virtual std::string_view toSymbol(PathId id);

  // Returns the absolute/relative native filesystem path
  // representation for the input id
  virtual std::filesystem::path toAbsPath(PathId id);
  virtual std::filesystem::path toRelPath(PathId id);

  // Returns either the absolute or relative native filesystem path
  // based on how the FileSystem is configured.
  virtual std::filesystem::path toPath(PathId id);

  // Returns the current working directory as either the native filesystem
  // path or as a PathId registered in the input SymbolTable.
  virtual const std::filesystem::path &getCwd();
  virtual PathId getCwd(SymbolTable *symbolTable);

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

  // Returns a copy of the input id registered with the input SymbolTable.
  virtual PathId copy(PathId id, SymbolTable *toSymbolTable);

  virtual ~FileSystem();

 protected:
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

  const std::filesystem::path m_cwd;
  bool m_useAbsPaths = true;

  std::mutex m_inputStreamsMutex;
  std::mutex m_outputStreamsMutex;
  InputStreams m_inputStreams;
  OutputStreams m_outputStreams;

  std::istringstream m_nullInputStream;
  std::ostringstream m_nullOutputStream;

 private:
  static FileSystem *sInstance;

 protected:
  explicit FileSystem(const std::filesystem::path &cwd);

 private:
  FileSystem(const FileSystem &rhs) = delete;
  FileSystem &operator=(const FileSystem &rhs) = delete;
};
}  // namespace SURELOG

#endif  // SURELOG_FILESYSTEM_H
