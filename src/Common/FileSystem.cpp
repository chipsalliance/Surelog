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
#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/Utils/StringUtils.h>

#include <fstream>
#include <regex>

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

std::filesystem::path FileSystem::normalize(const std::filesystem::path &p,
                                            std::error_code &ec) {
  // NOTES & SHORTCOMINGS:
  // * Though this implementation enforces an absolute path requirement, for
  //   the sake of completeness, the input path is made absolute if it was
  //   relative. Note that std::filesystem::weakly_canonical works only if the
  //   path is rooted i.e. some portion of the prefix path actually exist.
  //
  // * std::filesystem::weakly_canonical has to be called multiple times
  //   since some implementations can get tripped over with multiple 'walk up'
  //   in the path. For instance, paths like "dir/subdir/../../dir" doesn't
  //   work the same across platforms.
  //
  // * There is also an issue of trailing slash - for paths that do exist, the
  //   result of std::filesystem::weakly_canonical appends a trailing slash for
  //   directories. For non-existent paths, there is no trailing slash. This
  //   can cause paths to mismatch.
  //
  // * Most importantly, the implementation doesn't account for case
  //   sensitivity. For case insensitive platforms, like Windows, two paths of
  //   different casing will resolve to the same file/directory but are still
  //   wouldn't be considered equal i.e. as strings.
  //
  // * Few reference links:
  //   https://stackoverflow.com/questions/72678527/version-of-stdfilesystemequivalent-for-non-existing-files

  std::filesystem::path p1 =
      p.is_absolute() ? p : std::filesystem::current_path() / p;
  std::filesystem::path p2 = std::filesystem::weakly_canonical(p1, ec);
  while ((p1 != p2) && !ec) {
    p1 = p2;
    p2 = std::filesystem::weakly_canonical(p2, ec);
  }

  if (!ec) {
    // Remove the trailing slash, if any.
    std::string s = p2.string();
    if (p2 != p2.root_path()) {
      while (!s.empty() && ((s.back() == '\\') || (s.back() == '/'))) {
        s.pop_back();
      }
    }

    return s;
  }

  return std::filesystem::path();
}

PathId FileSystem::toPathId(const std::filesystem::path &path,
                            SymbolTable *symbolTable) {
  if (path.empty()) return BadPathId;

  std::filesystem::path fullpath = path.lexically_normal();

  auto [symbolId, symbol] = symbolTable->add(fullpath.string());
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

bool FileSystem::rename(PathId whatId, PathId toId) {
  if (!whatId || !toId) return false;

  const std::filesystem::path what = toAbsPath(whatId);
  const std::filesystem::path to = toAbsPath(toId);

  if (what.empty() || to.empty()) return false;

  std::error_code ec;
  std::filesystem::rename(what, to, ec);
  return !ec;
}

bool FileSystem::remove(PathId fileId) {
  if (!fileId) return false;

  const std::filesystem::path file = toAbsPath(fileId);
  if (file.empty()) return false;

  std::error_code ec;
  if (!std::filesystem::exists(file) && !ec) {
    return true;
  }

  if (!std::filesystem::remove(file, ec) && ec) {
    return false;
  }

  return !std::filesystem::exists(file, ec) && !ec;
}

bool FileSystem::mkdir(PathId dirId) {
  if (!dirId) return false;

  const std::filesystem::path dir = toAbsPath(dirId);
  if (dir.empty()) return false;

  std::error_code ec;
  if ((std::filesystem::exists(dir, ec) && !ec) &&
      (std::filesystem::is_directory(dir, ec) && !ec)) {
    return true;
  }

  if (!std::filesystem::create_directory(dir, ec) || ec) {
    return false;
  }

  return std::filesystem::is_directory(dir, ec) && !ec;
}

bool FileSystem::rmdir(PathId dirId) {
  if (!dirId) return false;

  const std::filesystem::path dir = toAbsPath(dirId);
  if (dir.empty()) return false;

  std::error_code ec;
  if ((!std::filesystem::exists(dir, ec) && !ec) ||
      (!std::filesystem::is_directory(dir, ec) && !ec)) {
    return true;
  }

  if (!std::filesystem::remove(dir, ec) || ec) {
    return false;
  }

  return !std::filesystem::exists(dir, ec) && !ec;
}

bool FileSystem::mkdirs(PathId dirId) {
  if (!dirId) return false;

  const std::filesystem::path dir = toAbsPath(dirId);
  if (dir.empty()) return false;

  std::error_code ec;
  if ((std::filesystem::exists(dir, ec) && !ec) &&
      (std::filesystem::is_directory(dir, ec) && !ec)) {
    return true;
  }

  // CAUTION: There is a known bug in VC compiler where a trailing
  // slash in the path will cause a false return from a call to
  // fs::create_directories.
  // if (!std::filesystem::create_directories(dir, ec) || ec) {
  std::filesystem::create_directories(dir, ec);
  if (ec) return false;

  return std::filesystem::is_directory(dir, ec) && !ec;
}

bool FileSystem::rmtree(PathId dirId) {
  if (!dirId) return false;

  const std::filesystem::path dir = toAbsPath(dirId);
  if (dir.empty()) return false;

  std::error_code ec;
  if ((!std::filesystem::exists(dir, ec) && !ec) ||
      (!std::filesystem::is_directory(dir, ec) && !ec)) {
    return true;
  }

  if (!std::filesystem::remove_all(dir, ec) || ec) {
    return false;
  }

  return !std::filesystem::exists(dir, ec) && !ec;
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

std::filesystem::file_time_type FileSystem::modtime(
    PathId fileId, std::filesystem::file_time_type defaultOnFail) {
  if (!fileId) return defaultOnFail;

  const std::filesystem::path filepath = toAbsPath(fileId);
  if (filepath.empty()) return defaultOnFail;

  std::error_code ec;
  if (!std::filesystem::exists(filepath) || ec) {
    return defaultOnFail;
  }

  std::filesystem::file_time_type lmt =
      std::filesystem::last_write_time(filepath, ec);
  return ec ? defaultOnFail : lmt;
}

std::filesystem::file_time_type FileSystem::modtime(PathId fileId) {
  return modtime(fileId, std::filesystem::file_time_type::min());
}

PathId FileSystem::locate(std::string_view name,
                          const PathIdVector &directories,
                          SymbolTable *symbolTable) {
  if (name.empty()) return BadPathId;

  std::error_code ec;
  for (const PathId &dirId : directories) {
    if (dirId) {
      const std::filesystem::path filepath = toAbsPath(dirId) / name;
      if (!filepath.empty() && std::filesystem::exists(filepath, ec) && !ec) {
        return toPathId(filepath, symbolTable);
      }
    }
  }

  return BadPathId;
}

PathIdVector &FileSystem::collect(PathId dirId, std::string_view extension,
                                  SymbolTable *symbolTable,
                                  PathIdVector &container) {
  if (!dirId) return container;

  const std::filesystem::path dirpath = toAbsPath(dirId);
  if (dirpath.empty()) return container;

  std::error_code ec;
  if (std::filesystem::is_directory(dirpath, ec) && !ec) {
    for (const std::filesystem::directory_entry &entry :
         std::filesystem::directory_iterator(dirpath)) {
      const std::filesystem::path &filepath = entry.path();
      if (extension.empty() || (filepath.extension() == extension)) {
        if (std::filesystem::is_regular_file(filepath, ec) && !ec) {
          container.emplace_back(toPathId(filepath, symbolTable));
        }
      }
    }
  }

  return container;
}

PathIdVector &FileSystem::collect(PathId dirId, SymbolTable *symbolTable,
                                  PathIdVector &container) {
  return dirId ? collect(dirId, "", symbolTable, container) : container;
}

PathIdVector &FileSystem::matching(PathId dirId, std::string_view pattern,
                                   SymbolTable *symbolTable,
                                   PathIdVector &container) {
  if (!dirId) return container;

  // ?   single character wildcard (matches any single character)
  // *   multiple character wildcard (matches any number of characters in a
  // directory/file name)
  // ... hierarchical wildcard (matches any number of hierarchical directories)
  // ..  specifies the parent directory
  // .   specifies the directory containing the lib.map
  // Paths that end in / shall include all files in the specified directory.
  // Identical to / * Paths that do not begin with / are relative to the
  // directory in which the current lib.map file is located.

  std::error_code ec;
  std::filesystem::path prefix = toAbsPath(dirId);
  if (prefix.empty()) return container;

  std::filesystem::path suffix;
  for (const std::filesystem::path &part : std::filesystem::path(pattern)) {
    if (part == ".") {
      continue;
    } else if (!suffix.empty()) {
      suffix /= part;
    } else if (part.string().find_first_of(".?*") == std::string::npos) {
      prefix /= part;
    } else {
      suffix /= part;
    }
  }

  if (suffix.empty()) {
    return collect(toPathId(prefix, symbolTable), symbolTable, container);
  }

  prefix = std::filesystem::weakly_canonical(prefix, ec);
  if (ec) return container;

  const std::string separator(1, std::filesystem::path::preferred_separator);
  const std::string escaped = "\\" + separator;

  std::string regexp = suffix.string();
  regexp = StringUtils::replaceAll(regexp, separator,
                                   escaped);  // escape separators
  regexp = StringUtils::replaceAll(regexp, StrCat("...", escaped),
                                   StrCat(R"([a-zA-Z0-9_\-.)", escaped, R"(]+)",
                                          escaped));  // separator allowed
  regexp = StringUtils::replaceAll(
      regexp, StrCat("..", escaped),
      StrCat(R"([a-zA-Z0-9_\-.]+)", escaped, R"([a-zA-Z0-9_\-.]+)",
             escaped));  // separator NOT allowed
  regexp = StringUtils::replaceAll(regexp, ".", "\\.");  // escape it
  regexp = StringUtils::replaceAll(regexp, "?",
                                   R"([a-zA-Z0-9_\-\.])");  // at most one
  regexp = StringUtils::replaceAll(
      regexp, "*", StrCat("[^", escaped, "]*"));  // free for all

  const std::regex regex(regexp);
  const std::filesystem::directory_options options =
      std::filesystem::directory_options::skip_permission_denied |
      std::filesystem::directory_options::follow_directory_symlink;

  for (const std::filesystem::directory_entry &entry :
       std::filesystem::recursive_directory_iterator(prefix, options)) {
    const std::filesystem::path &absolute = entry.path();
    if (std::filesystem::is_regular_file(absolute, ec) && !ec) {
      const std::string relative =
          std::filesystem::relative(absolute, prefix, ec).string();
      std::smatch match;
      if (!ec && std::regex_match(relative, match, regex)) {
        if (std::filesystem::is_regular_file(absolute, ec) && !ec) {
          container.emplace_back(toPathId(absolute, symbolTable));
        }
      }
    }
  }

  return container;
}

PathId FileSystem::copy(PathId id, SymbolTable *toSymbolTable) {
  if (!id) return BadPathId;
  if (id.getSymbolTable() == toSymbolTable) return id;

  const std::string_view symbol1 = toSymbol(id);
  if (symbol1 == BadRawSymbol) return BadPathId;

  auto [symbolId, symbol2] = toSymbolTable->add(symbol1);
  return PathId(toSymbolTable, (RawSymbolId)symbolId, symbol2);
}

PathId FileSystem::getChild(PathId id, std::string_view name,
                            SymbolTable *symbolTable) {
  if (!id) return BadPathId;

  std::filesystem::path filepath = toAbsPath(id);
  if (filepath.empty()) return BadPathId;

  return toPathId(filepath / name, symbolTable);
}

PathId FileSystem::getSibling(PathId id, std::string_view name,
                              SymbolTable *symbolTable) {
  if (!id) return BadPathId;

  std::filesystem::path filepath = toAbsPath(id);
  if (filepath.empty()) return BadPathId;

  return filepath.has_parent_path()
             ? toPathId(filepath.parent_path() / name, symbolTable)
             : toPathId(name, symbolTable);
}

PathId FileSystem::getParent(PathId id, SymbolTable *symbolTable) {
  if (!id) return BadPathId;

  std::filesystem::path filepath = toAbsPath(id);
  if (filepath.empty()) return BadPathId;

  return filepath.has_parent_path()
             ? toPathId(filepath.parent_path(), symbolTable)
             : toPathId(".", symbolTable);
}

std::pair<SymbolId, std::string_view> FileSystem::getLeaf(
    PathId id, SymbolTable *symbolTable) {
  if (!id) return {BadSymbolId, BadRawSymbol};

  const std::filesystem::path filepath = toAbsPath(id);
  if (!filepath.has_filename()) {
    return {BadSymbolId, BadRawSymbol};
  }

  return symbolTable->add(filepath.filename().string());
}

std::pair<SymbolId, std::string_view> FileSystem::getType(
    PathId id, SymbolTable *symbolTable) {
  if (!id) return {BadSymbolId, BadRawSymbol};

  const std::filesystem::path filepath = toAbsPath(id);
  if (!filepath.has_extension()) {
    return {BadSymbolId, BadRawSymbol};
  }

  return symbolTable->add(filepath.extension().string());
}
}  // namespace SURELOG
