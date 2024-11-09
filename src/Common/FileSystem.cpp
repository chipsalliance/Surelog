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

#include "Surelog/Common/FileSystem.h"

#include "Surelog/SourceCompile/SymbolTable.h"

#if defined(_WIN32)
#define NOMINMAX
#include <Windows.h>

#include <string>
#include <string_view>
#elif defined(__APPLE__)
#include <mach-o/dyld.h>
#include <sys/param.h>
#include <unistd.h>
#else
#include <limits.h>
#include <unistd.h>
#endif

namespace SURELOG {
FileSystem *FileSystem::sInstance = nullptr;

FileSystem *FileSystem::getInstance() { return sInstance; }

FileSystem *FileSystem::setInstance(FileSystem *fileSystem) {
  FileSystem *const instance = sInstance;
  sInstance = fileSystem;
  return instance;
}

std::filesystem::path FileSystem::getProgramPath() {
#if defined(_WIN32)
  char result[MAX_PATH + 1] = {'\0'};
  auto count = GetModuleFileNameA(NULL, result, MAX_PATH);
#elif defined(__APPLE__)
  char result[MAXPATHLEN + 1] = {'\0'};
  uint32_t count = MAXPATHLEN;
  if (_NSGetExecutablePath(result, &count) != 0) {
    count = readlink("/proc/self/exe", result, MAXPATHLEN);
  }
#else
  char result[PATH_MAX + 1] = {'\0'};
  ssize_t count = readlink("/proc/self/exe", result, PATH_MAX);
#endif
  return (count > 0) ? std::filesystem::path(result) : std::filesystem::path();
}

std::filesystem::path FileSystem::normalize(const std::filesystem::path &p) {
  std::filesystem::path norm = p.lexically_normal();
  // Remove the trailing slash, if any!
  if (norm != norm.root_path()) {
    std::string s = norm.string();
    while ((s.back() == '\\') || (s.back() == '/')) s.pop_back();
    norm = s;
  }
  return norm;
}

bool FileSystem::is_subpath(const std::filesystem::path &parent,
                            const std::filesystem::path &child) {
  std::filesystem::path np = normalize(parent);
  std::filesystem::path nc = normalize(child);

  if (np.root_path() == nc.root_path()) {
    std::filesystem::path c = nc;
    while ((np != c) && (c != nc.root_path())) {
      c = c.parent_path();
    }
    return np == c;
  }
  return false;
}

std::string_view FileSystem::toPath(PathId id) {
  static constexpr std::string_view kEmpty;
  if (!id) return kEmpty;

  const std::string_view symbol = id.getSymbolTable()->getSymbol((SymbolId)id);
  return (symbol == SymbolTable::getBadSymbol()) ? kEmpty : symbol;
}

PathId FileSystem::getWorkingDir(SymbolTable *symbolTable) {
  return toPathId(getWorkingDir(), symbolTable);
}

std::istream &FileSystem::openForRead(PathId fileId) {
  return openInput(fileId, std::ios_base::in);
}

std::istream &FileSystem::openForLoad(PathId fileId) {
  return openInput(fileId, std::ios_base::in | std::ios_base::binary);
}

std::ostream &FileSystem::openForWrite(PathId fileId) {
  return openOutput(fileId, std::ios_base::out);
}

std::ostream &FileSystem::openForSave(PathId fileId) {
  return openOutput(fileId, std::ios_base::out | std::ios_base::binary);
}

bool FileSystem::readContent(PathId fileId, std::string &content) {
  if (!fileId) return false;

  bool result = false;
  std::streamsize length = 0;
  if (filesize(fileId, &length)) {
    std::istream &strm = openForRead(fileId);
    if (strm.good()) {
      content.resize(length);

      std::streamsize offset = 0;
      while (!strm.eof() && (offset < length)) {
        strm.read(content.data() + offset, length - offset);
        offset += strm.gcount();
      }
      // Can't compare the offset to length for identifying success
      // Based on platform, filesize returns number of bytes when
      // the file is loaded in binary mode. But when reading the file
      // as text (as here is the case), the underlying stream automatically
      // strips '\r' (at least in the case of Windows) and thus the number
      // of actual bytes loaded are less than the number of bytes on disk.
      if (offset != length) content.resize(offset);
      result = (offset == length) || strm.eof();
    }
    close(strm);
  }
  return result;
}

bool FileSystem::writeContent(PathId fileId, std::string_view content,
                              bool onlyIfModified) {
  if (!fileId) return false;

  if (onlyIfModified && exists(fileId)) {
    std::string currentContent;
    if (readContent(fileId, currentContent) && (currentContent == content)) {
      return true;
    }
  }

  bool result = false;
  std::ostream &strm = openForWrite(fileId);
  if (strm.good()) {
    strm << content;
    strm.flush();
    result = strm.good();
  }
  close(strm);
  return result;
}

bool FileSystem::writeContent(PathId fileId, std::string_view content) {
  return writeContent(fileId, content, true);
}

bool FileSystem::readLines(PathId fileId, std::vector<std::string> &lines) {
  if (!fileId) return false;

  bool result = false;
  std::istream &strm = openForRead(fileId);
  if (strm.good()) {
    std::string line;
    while (!strm.eof() && std::getline(strm, line)) {
      while (!line.empty() &&
             ((line.back() == '\r') || (line.back() == '\n'))) {
        line.pop_back();
      }
      lines.emplace_back(line);
    }
    result = strm.eof();
  }
  close(strm);
  return result;
}

bool FileSystem::writeLines(PathId fileId,
                            const std::vector<std::string> &lines,
                            bool onlyIfModified /* = true */) {
  if (!fileId) return false;

  if (onlyIfModified && exists(fileId)) {
    std::vector<std::string> currentLines;
    if ((readLines(fileId, currentLines)) &&
        (lines.size() == currentLines.size())) {
      bool diffs = false;
      for (size_t i = 0, n = lines.size(); i < n; ++i) {
        if (lines[i] != currentLines[i]) {
          diffs = true;
          break;
        }
      }
      if (!diffs) return true;
    }
  }

  bool result = false;
  std::ostream &strm = openForWrite(fileId);
  if (strm.good()) {
    for (const std::string &line : lines) {
      strm << line << std::endl;
    }
    strm.flush();
    result = strm.good();
  }
  close(strm);
  return result;
}

bool FileSystem::writeLines(PathId fileId,
                            const std::vector<std::string> &lines) {
  return writeLines(fileId, lines, true);
}

bool FileSystem::readLine(PathId fileId, int32_t index, std::string &content) {
  if (!fileId) return false;
  if (index < 1) return false;  // Note: index starts at 1.

  bool result = false;
  std::istream &strm = openForRead(fileId);
  if (strm.good()) {
    std::string line;
    while ((index > 0) && strm.good() && std::getline(strm, line)) {
      --index;
    }

    if ((result = (index == 0))) {
      while (!line.empty() &&
             ((line.back() == '\r') || (line.back() == '\n'))) {
        line.pop_back();
      }
      content = line;
    }
  }
  close(strm);
  return result;
}

bool FileSystem::loadContent(PathId fileId, std::vector<char> &content) {
  if (!fileId) return false;

  bool result = false;
  std::streamsize length = 0;
  if (filesize(fileId, &length)) {
    std::istream &strm = openForLoad(fileId);
    if (strm.good()) {
      content.resize(length);

      std::streamsize offset = 0;
      while (!strm.eof() && (offset < length)) {
        strm.read(content.data() + offset, length - offset);
        offset += strm.gcount();
      }
      result = offset == length;
    }
    close(strm);
  }
  return result;
}

bool FileSystem::saveContent(PathId fileId, const char *content,
                             std::streamsize length) {
  return saveContent(fileId, content, length, false);
}

bool FileSystem::saveContent(PathId fileId, const std::vector<char> &content,
                             bool useTemp) {
  return saveContent(fileId, content.data(), content.size(), useTemp);
}

bool FileSystem::saveContent(PathId fileId, const std::vector<char> &data) {
  return saveContent(fileId, data, false);
}

PathId FileSystem::getLogFile(bool isUnitCompilation,
                              SymbolTable *symbolTable) {
  return getLogFile(isUnitCompilation, kLogFileName, symbolTable);
}

PathId FileSystem::getCacheDir(bool isUnitCompilation,
                               SymbolTable *symbolTable) {
  return getCacheDir(isUnitCompilation, kCacheDirName, symbolTable);
}

PathId FileSystem::getPpOutputFile(bool isUnitCompilation, PathId sourceFileId,
                                   SymbolId libraryNameId,
                                   SymbolTable *symbolTable) {
  if (!sourceFileId || !libraryNameId) return BadPathId;

  const std::string_view libraryName = symbolTable->getSymbol(libraryNameId);
  if (libraryName == BadRawSymbol) return BadPathId;

  return getPpOutputFile(isUnitCompilation, sourceFileId, libraryName,
                         symbolTable);
}

PathId FileSystem::getPpCacheFile(bool isUnitCompilation, PathId sourceFileId,
                                  SymbolId libraryNameId, bool isPrecompiled,
                                  SymbolTable *symbolTable) {
  if (!sourceFileId || !libraryNameId) return BadPathId;

  const std::string_view libraryName = symbolTable->getSymbol(libraryNameId);
  if (libraryName == BadRawSymbol) return BadPathId;

  return getPpCacheFile(isUnitCompilation, sourceFileId, libraryName,
                        isPrecompiled, symbolTable);
}

PathId FileSystem::getParseCacheFile(bool isUnitCompilation, PathId ppFileId,
                                     SymbolId libraryNameId, bool isPrecompiled,
                                     SymbolTable *symbolTable) {
  if (!ppFileId || !libraryNameId) return BadPathId;

  const std::string_view libraryName = symbolTable->getSymbol(libraryNameId);
  if (libraryName == BadRawSymbol) return BadPathId;

  return getParseCacheFile(isUnitCompilation, ppFileId, libraryName,
                           isPrecompiled, symbolTable);
}

PathId FileSystem::getPythonCacheFile(bool isUnitCompilation,
                                      PathId sourceFileId,
                                      SymbolId libraryNameId,
                                      SymbolTable *symbolTable) {
  if (!sourceFileId || !libraryNameId) return BadPathId;

  const std::string_view libraryName = symbolTable->getSymbol(libraryNameId);
  if (libraryName == BadRawSymbol) return BadPathId;

  return getPythonCacheFile(isUnitCompilation, sourceFileId, libraryName,
                            symbolTable);
}

std::filesystem::file_time_type FileSystem::modtime(PathId fileId) {
  return modtime(fileId, std::filesystem::file_time_type::min());
}

PathId FileSystem::copy(PathId id, SymbolTable *toSymbolTable) {
  if (!id) return BadPathId;
  if (id.getSymbolTable() == toSymbolTable) return id;

  const std::string_view symbol1 = toPath(id);
  if (symbol1 == BadRawSymbol) return BadPathId;

  auto [symbolId, symbol2] = toSymbolTable->add(symbol1);
  return PathId(toSymbolTable, (RawSymbolId)symbolId, symbol2);
}
}  // namespace SURELOG
