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
 * File:   FileUtils.cpp
 * Author: alain
 *
 * Created on March 16, 2017, 11:02 PM
 */
#include "Utils/FileUtils.h"

#include <errno.h>
#include <limits.h> /* PATH_MAX */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

#include <algorithm>
#include <fstream>
#include <iostream>
#include <regex>
#include <sstream>
#include <string>

#include "SourceCompile/SymbolTable.h"
#include "Utils/StringUtils.h"

namespace SURELOG {
namespace fs = std::filesystem;

bool FileUtils::fileExists(const fs::path& name) {
  std::error_code ec;
  return fs::exists(name, ec);
}

uint64_t FileUtils::fileSize(const fs::path& name) {
  std::error_code ec;
  return fs::file_size(name, ec);
}

bool FileUtils::fileIsDirectory(const fs::path& name) {
  return fs::is_directory(name);
}

bool FileUtils::fileIsRegular(const fs::path& name) {
  return fs::is_regular_file(name);
}

SymbolId FileUtils::locateFile(SymbolId file, SymbolTable* symbols,
                               const std::vector<SymbolId>& paths) {
  const fs::path fileName = symbols->getSymbol(file);
  if (fileExists(fileName)) {
    return file;
  }
  for (auto id : paths) {
    const fs::path path = symbols->getSymbol(id);
    fs::path filePath = path / fileName;
    if (fileExists(filePath)) {
      return symbols->registerSymbol(filePath.string());
    }
  }
  return SymbolTable::getBadId();
}

bool FileUtils::mkDirs(const fs::path& path) {
  // CAUTION: There is a known bug in VC compiler where a trailing
  // slash in the path will cause a false return from a call to
  // fs::create_directories.
  std::error_code err;
  fs::create_directories(path, err);
  return fs::is_directory(path);
}

bool FileUtils::rmDirRecursively(const fs::path& path) {
  static constexpr uintmax_t kErrorCondition = static_cast<std::uintmax_t>(-1);
  std::error_code err;
  return fs::remove_all(path, err) != kErrorCondition;
}

fs::path FileUtils::getFullPath(const fs::path& path) {
  std::error_code ec;
  fs::path fullPath = fs::canonical(path, ec);
  return ec ? path : fullPath;
}

bool FileUtils::getFullPath(const fs::path& path, fs::path* result) {
  std::error_code ec;
  fs::path fullPath = fs::canonical(path, ec);
  bool found = (!ec && fileIsRegular(fullPath));
  if (result != nullptr) {
    *result = found ? fullPath : path;
  }
  return found;
}

std::vector<SymbolId> FileUtils::collectFiles(SymbolId dirPath, SymbolId ext,
                                              SymbolTable* symbols) {
  return collectFiles(symbols->getSymbol(dirPath), symbols->getSymbol(ext),
                      symbols);
}

std::vector<SymbolId> FileUtils::collectFiles(const fs::path& dirPath,
                                              const fs::path& ext,
                                              SymbolTable* symbols) {
  std::vector<SymbolId> result;
  if (fileIsDirectory(dirPath)) {
    for (fs::directory_entry entry : fs::directory_iterator(dirPath)) {
      const fs::path& filepath = entry.path();
      if (filepath.extension() == ext) {
        result.push_back(symbols->registerSymbol(filepath.string()));
      }
    }
  }
  return result;
}

std::vector<SymbolId> FileUtils::collectFiles(const fs::path& pathSpec,
                                              SymbolTable* symbols) {
  // ?   single character wildcard (matches any single character)
  // *   multiple character wildcard (matches any number of characters in a
  // directory/file name)
  // ... hierarchical wildcard (matches any number of hierarchical directories)
  // ..  specifies the parent directory
  // .   specifies the directory containing the lib.map
  // Paths that end in / shall include all files in the specified directory.
  // Identical to / * Paths that do not begin with / are relative to the
  // directory in which the current lib.map file is located.

  std::vector<SymbolId> result;

  std::error_code ec;
  fs::path path(pathSpec);
  if (!path.is_absolute()) {
    path = fs::current_path(ec) / path;
    if (ec) return result;
  }
  path.make_preferred();

  fs::path prefix;
  fs::path suffix;
  for (const fs::path& subpath : path) {
    const std::string substr = subpath.string();
    if (substr == ".")
      continue;
    else if (!suffix.empty())
      suffix /= subpath;
    else if (substr.find_first_of(".?*") == std::string::npos)
      prefix /= subpath;
    else
      suffix /= subpath;
  }

  prefix = fs::canonical(prefix, ec);
  if (ec) return result;
  if (suffix.empty()) suffix /= "*";

  const std::string separator(1, fs::path::preferred_separator);
  const std::string escaped = "\\" + separator;
  std::string regexp = suffix.string();
  regexp =
      StringUtils::replaceAll(regexp, separator, escaped);  // escape separators
  regexp = StringUtils::replaceAll(
      regexp, "..." + escaped,
      R"([a-zA-Z0-9_\-.)" + escaped + R"(]+)" + escaped);  // separator allowed
  regexp = StringUtils::replaceAll(regexp, ".." + escaped,
                                   R"([a-zA-Z0-9_\-.]+)" + escaped +
                                       R"([a-zA-Z0-9_\-.]+)" +
                                       escaped);  // separator NOT allowed
  regexp = StringUtils::replaceAll(regexp, ".", "\\.");  // escape it
  regexp = StringUtils::replaceAll(regexp, "?",
                                   R"([a-zA-Z0-9_\-\.])");  // at most one
  regexp = StringUtils::replaceAll(regexp, "*",
                                   "[^" + escaped + "]*");  // free for all

  const std::regex regex(regexp);
  const fs::directory_options options =
      fs::directory_options::skip_permission_denied |
      fs::directory_options::follow_directory_symlink;

  for (const fs::directory_entry& entry :
       fs::recursive_directory_iterator(prefix, options)) {
    if (fs::is_regular_file(entry.path())) {
      const std::string relative =
          entry.path().string().substr(prefix.string().length() + 1);
      std::smatch match;
      if (!ec && std::regex_match(relative, match, regex)) {
        result.push_back(symbols->registerSymbol(entry.path().string()));
      }
    }
  }

  return result;
}

std::string FileUtils::getFileContent(const fs::path& filename) {
  std::ifstream in(filename, std::ios::in | std::ios::binary);
  if (in) {
    std::string result;
    result.assign(std::istreambuf_iterator<char>(in),
                  std::istreambuf_iterator<char>());
    return result;
  }
  return "FAILED_TO_LOAD_CONTENT";
}

fs::path FileUtils::getPathName(const fs::path& path) {
  return path.has_parent_path() ? path.parent_path() : "";
}

fs::path FileUtils::basename(const fs::path& path) { return path.filename(); }

fs::path FileUtils::getPreferredPath(const fs::path& path) {
  return fs::path(path).make_preferred();
}

std::string FileUtils::hashPath(const fs::path& path) {
  const std::string separator(1, fs::path::preferred_separator);
  std::string hashedpath;
  std::size_t val = std::hash<std::string>{}(path.string());
  std::string last_dir = path.string();
  if (!last_dir.empty()) last_dir.erase(last_dir.end() - 1);
  auto it1 = std::find_if(last_dir.rbegin(), last_dir.rend(),
                          [](char ch) { return (ch == '/' || ch == '\\'); });
  if (it1 != last_dir.rend()) last_dir.erase(last_dir.begin(), it1.base());

  hashedpath = last_dir + "_" + std::to_string(val) + separator;
  return hashedpath;
}

fs::path FileUtils::makeRelativePath(const fs::path& in_path) {
  const std::string separator(1, fs::path::preferred_separator);
  // Standardize it so we can avoid special cases and wildcards!
  std::string path = getPreferredPath(in_path).string();
  // Handle Windows specific absolute paths
  if (in_path.is_absolute() && (path.length() > 1) && (path[1] == ':'))
    path[1] = '$';
  // Swap "..\" (or "../") for "__\" (or "__/")
  path = StringUtils::replaceAll(path, ".." + separator, "__" + separator);
  // Swap "\.\" (or "/./") for "\" (or "/")
  path = StringUtils::replaceAll(path, separator + "." + separator, separator);
  if (path[0] != '.') {
    if (path[0] != fs::path::preferred_separator) path = separator + path;
    path = "." + path;
  }
  return path;
}
}  // namespace SURELOG
