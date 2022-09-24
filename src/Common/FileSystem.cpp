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

#include <fstream>

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

FileSystem *FileSystem::setInstance(FileSystem *fileSystem) {
  FileSystem *const instance = sInstance;
  sInstance = fileSystem;
  return instance;
}

FileSystem::FileSystem(const std::filesystem::path &cwd)
    : m_cwd(cwd), m_useAbsPaths(true) {}

FileSystem::~FileSystem() {
  {
    std::scoped_lock<std::mutex> lock(m_inputStreamsMutex);

    while (!m_inputStreams.empty()) {
      close(*m_inputStreams.begin()->get());
    }
  }
  {
    std::scoped_lock<std::mutex> lock(m_outputStreamsMutex);

    while (!m_outputStreams.empty()) {
      close(*m_outputStreams.begin()->get());
    }
  }

  if (sInstance == this) setInstance(nullptr);
}

PathId FileSystem::toPathId(const std::filesystem::path &path,
                            SymbolTable *symbolTable) {
  if (path.empty()) return BadPathId;

  auto [symbolId, symbol] = symbolTable->add(path.string());
  return PathId(symbolTable, (RawSymbolId)symbolId, symbol);
}

std::string_view FileSystem::toSymbol(PathId id) {
  return id ? id.getSymbolTable()->getSymbol((SymbolId)id)
            : SymbolTable::getBadSymbol();
}

std::filesystem::path FileSystem::toPath(PathId id) {
  if (!id) return std::filesystem::path();

  std::string_view symbol = toSymbol(id);
  return (symbol == BadRawSymbol) ? std::filesystem::path()
                                  : std::filesystem::path(symbol);

  // TODO(HS): Imeplement me!
  // return m_useAbsPaths ? toAbsPath(id) ? toRelPath(id);
}

std::filesystem::path FileSystem::toAbsPath(PathId id) {
  // TODO(HS): Imeplement me!
  return toPath(id);
}

std::filesystem::path FileSystem::toRelPath(PathId id) {
  // TODO(HS): Imeplement me!
  return toPath(id);
}

const std::filesystem::path &FileSystem::getCwd() { return m_cwd; }

PathId FileSystem::getCwd(SymbolTable *symbolTable) {
  return toPathId(m_cwd, symbolTable);
}

std::istream &FileSystem::openInput(const std::filesystem::path &filepath,
                                    std::ios_base::openmode mode) {
  std::scoped_lock<std::mutex> lock(m_inputStreamsMutex);
  std::pair<InputStreams::iterator, bool> it =
      m_inputStreams.emplace(new std::ifstream);

  std::ifstream &strm = *static_cast<std::ifstream *>(it.first->get());
  strm.open(filepath, mode);
  return strm;
}

std::ostream &FileSystem::openOutput(const std::filesystem::path &filepath,
                                     std::ios_base::openmode mode) {
  std::scoped_lock<std::mutex> lock(m_outputStreamsMutex);
  std::pair<OutputStreams::iterator, bool> it =
      m_outputStreams.emplace(new std::ofstream);

  std::ofstream &strm = *static_cast<std::ofstream *>(it.first->get());
  strm.open(filepath, mode);
  return strm;
}

std::istream &FileSystem::openInput(PathId fileId,
                                    std::ios_base::openmode mode) {
  const std::filesystem::path filepath = toAbsPath(fileId);
  return filepath.empty() ? m_nullInputStream : openInput(filepath, mode);
}

std::istream &FileSystem::openForRead(PathId fileId) {
  return openInput(fileId, std::ios_base::in);
}

std::istream &FileSystem::openForLoad(PathId fileId) {
  return openInput(fileId, std::ios_base::in | std::ios_base::binary);
}

bool FileSystem::close(std::istream &strm) {
  std::scoped_lock<std::mutex> lock(m_inputStreamsMutex);

  InputStreams::const_iterator it = m_inputStreams.find(&strm);
  if (it != m_inputStreams.end()) {
    m_inputStreams.erase(it);
    return true;
  }
  return false;
}

std::ostream &FileSystem::openOutput(PathId fileId,
                                     std::ios_base::openmode mode) {
  const std::filesystem::path filepath = toAbsPath(fileId);
  return filepath.empty() ? m_nullOutputStream : openOutput(filepath, mode);
}

std::ostream &FileSystem::openForWrite(PathId fileId) {
  return openOutput(fileId, std::ios_base::out);
}

std::ostream &FileSystem::openForSave(PathId fileId) {
  return openOutput(fileId, std::ios_base::out | std::ios_base::binary);
}

bool FileSystem::close(std::ostream &strm) {
  std::scoped_lock<std::mutex> lock(m_outputStreamsMutex);

  OutputStreams::const_iterator it = m_outputStreams.find(&strm);
  if (it != m_outputStreams.end()) {
    m_outputStreams.erase(it);
    return true;
  }
  return false;
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
                             std::streamsize length, bool useTemp) {
  if (!fileId) return false;

  const std::filesystem::path filepath = toAbsPath(fileId);
  if (filepath.empty()) return false;

  bool result = false;

  std::filesystem::path filepath2Write = filepath;
  if (useTemp) filepath2Write += ".tmp";

  std::ostream &strm =
      openOutput(filepath2Write, std::ios_base::out | std::ios_base::binary);
  if (strm.good()) {
    if (length > 0) {
      strm.write(content, length);
    }
    result = strm.good();
  }
  close(strm);

  if (useTemp) {
    std::error_code ec;
    if (result) {
      std::filesystem::rename(filepath2Write, filepath, ec);
      result = !ec;
    } else {
      std::filesystem::remove(filepath2Write, ec);
    }
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

bool FileSystem::exists(PathId id) {
  if (!id) return false;

  const std::filesystem::path filepath = toAbsPath(id);

  std::error_code ec;
  return !filepath.empty() && std::filesystem::exists(filepath, ec) && !ec;
}

bool FileSystem::exists(PathId dirId, std::string_view descendant) {
  if (!dirId || descendant.empty()) return false;

  const std::filesystem::path filepath = toAbsPath(dirId) / descendant;

  std::error_code ec;
  return !filepath.empty() && std::filesystem::exists(filepath, ec) && !ec;
}

bool FileSystem::isDirectory(PathId id) {
  if (!id) return false;

  const std::filesystem::path dirpath = toAbsPath(id);

  std::error_code ec;
  return !dirpath.empty() && std::filesystem::exists(dirpath, ec) && !ec &&
         std::filesystem::is_directory(dirpath, ec) && !ec;
}

bool FileSystem::isRegularFile(PathId id) {
  if (!id) return false;

  const std::filesystem::path filepath = toAbsPath(id);

  std::error_code ec;
  return !filepath.empty() && std::filesystem::exists(filepath, ec) && !ec &&
         std::filesystem::is_regular_file(filepath, ec) && !ec;
}

bool FileSystem::filesize(PathId fileId, std::streamsize *result) {
  if (!fileId) return false;

  const std::filesystem::path filepath = toAbsPath(fileId);
  if (filepath.empty()) return false;

  std::error_code ec;
  std::streamsize length = std::filesystem::file_size(filepath, ec);
  if (!ec) {
    if (result != nullptr) {
      *result = length;
    }
    return true;
  }
  return false;
}

PathId FileSystem::copy(PathId id, SymbolTable *toSymbolTable) {
  if (!id) return BadPathId;

  std::string_view symbol = toSymbol(id);
  return (symbol == BadRawSymbol) ? BadPathId : toPathId(symbol, toSymbolTable);
}
}  // namespace SURELOG
