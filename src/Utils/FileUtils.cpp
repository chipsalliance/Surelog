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

#include "SourceCompile/SymbolTable.h"
#include "Utils/FileUtils.h"
#include "Utils/StringUtils.h"
#include <sys/stat.h>
#include <string.h>
#include <limits.h> /* PATH_MAX */
#include <errno.h>
#include <stdlib.h>
#include <iostream>
#include <algorithm>
#include <string>
#include <stdio.h>
#include <regex>
#include <fstream>
#include <sstream>

#if defined(_MSC_VER)
  #include <direct.h>
  #define PATH_MAX _MAX_PATH
#else
  #include <dirent.h>
  #include <unistd.h>
#endif

#if (__cplusplus >= 201703L) && __has_include(<filesystem>)
  #include <filesystem>
  namespace fs = std::filesystem;
#else
  #include <experimental/filesystem>
  namespace fs = std::experimental::filesystem;
#endif

using namespace SURELOG;

bool FileUtils::fileExists(const std::string& name) {
  std::error_code ec;
  return fs::exists(name, ec);
}

unsigned long FileUtils::fileSize(const std::string& name) {
  std::error_code ec;
  return fs::file_size(name, ec);
}

bool FileUtils::fileIsDirectory(const std::string& name) {
  return fs::is_directory(name);
}

bool FileUtils::fileIsRegular(const std::string& name) {
  return fs::is_regular_file(name);
}

SymbolId FileUtils::locateFile(SymbolId file, SymbolTable* symbols,
                               const std::vector<SymbolId>& paths) {
  const std::string& fileName = symbols->getSymbol(file);
  if (fileExists(fileName)) {
    return file;
  }
  for (auto id : paths) {
    const std::string& path = symbols->getSymbol(id);
    std::string filePath;
    if (path.size() && (path[path.size() - 1] == '/'))
      filePath = path + fileName;
    else
      filePath = path + "/" + fileName;
    if (fileExists(filePath)) {
      return symbols->registerSymbol(filePath);
    }
  }
  return symbols->getBadId();
}

int FileUtils::mkDir(const char* path) {
  // CAUTION: There is a known bug in VC compiler where a trailing
  // slash in the path will cause a false return from a call to
  // fs::create_directories.
  const std::string dirpath(path);
  fs::create_directories(dirpath);
  return fs::is_directory(dirpath) ? 0 : -1;
}

int FileUtils::rmDir(const char* path) {
  const std::string dirpath(path);
  return fs::remove_all(dirpath);
}

std::string FileUtils::getFullPath(const std::string& path) {
  std::error_code ec;
  fs::path fullPath = fs::canonical(path, ec);
  return ec ? path : fullPath.string();
}

bool FileUtils::getFullPath(const std::string& path, std::string* result) {
  std::error_code ec;
  fs::path fullPath = fs::canonical(path, ec);
  bool found = (!ec && fileIsRegular(fullPath.string()));
  if (result != nullptr) {
    *result = found ? fullPath.string() : path;
  }
  return found;
}

static bool has_suffix(const std::string& s, const std::string& suffix) {
  return (s.size() >= suffix.size()) &&
         equal(suffix.rbegin(), suffix.rend(), s.rbegin());
}

std::vector<SymbolId> FileUtils::collectFiles(SymbolId dirPath, SymbolId ext,
                                              SymbolTable* symbols) {
  return collectFiles(symbols->getSymbol(dirPath), symbols->getSymbol(ext),
                      symbols);
}

std::vector<SymbolId> FileUtils::collectFiles(const std::string& dirPath,
                                              const std::string& ext,
                                              SymbolTable* symbols) {
  std::vector<SymbolId> result;
  if (fileIsDirectory(dirPath)) {
    for (fs::directory_entry entry : fs::directory_iterator(dirPath)) {
      const std::string filepath = entry.path().string();
      if (has_suffix(filepath, ext)) {
        result.push_back(symbols->registerSymbol(filepath));
      }
    }
  }
  return result;
}

std::vector<SymbolId> FileUtils::collectFiles(const std::string& pathSpec,
                                              SymbolTable* const symbols) {
  // ?   single character wildcard (matches any single character)
  // *   multiple character wildcard (matches any number of characters in a
  // directory/file name)
  // ... hierarchical wildcard (matches any number of hierarchical directories)
  // ..  specifies the parent directory
  // .   specifies the directory containing the lib.map
  // Paths that end in / shall include all files in the specified directory.
  // Identical to / * Paths that do not begin with / are relative to the directory
  // in which the current lib.map file is located.

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
  for (const fs::path &subpath : path)
  {
    const std::string substr = subpath.string();
    if (substr.compare(".") == 0)
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
  regexp = StringUtils::replaceAll(regexp, separator, escaped); // escape separators
  regexp = StringUtils::replaceAll(regexp, "..." + escaped,
      R"([a-zA-Z0-9_\-.)" + escaped + R"(]+)" + escaped);  // separator allowed
  regexp = StringUtils::replaceAll(regexp, ".." + escaped,
      R"([a-zA-Z0-9_\-.]+)" + escaped + R"([a-zA-Z0-9_\-.]+)" + escaped);  // separator NOT allowed
  regexp = StringUtils::replaceAll(regexp, ".", "\\.");  // escape it
  regexp = StringUtils::replaceAll(regexp, "?", R"([a-zA-Z0-9_\-\.])"); // at most one
  regexp = StringUtils::replaceAll(regexp, "*", "[^" + escaped + "]*"); // free for all

  const std::regex regex(regexp);
  const fs::directory_options options =
      fs::directory_options::skip_permission_denied |
      fs::directory_options::follow_directory_symlink;

  for (fs::directory_entry entry :
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

std::string FileUtils::getFileContent(const std::string& filename) {
  std::ifstream in(filename, std::ios::in | std::ios::binary);
  if (in) {
    std::string result;
    result.assign(std::istreambuf_iterator<char>(in),
                  std::istreambuf_iterator<char>());
    return result;
  }
  return "FAILED_TO_LOAD_CONTENT";
}

std::string FileUtils::getPathName(const std::string& path) {
  fs::path fs_path(path);
  return fs_path.has_parent_path() ? (fs::path(path).parent_path() += fs::path::preferred_separator).string() : "";
}

std::string FileUtils::basename(const std::string& str) {
  return fs::path(str).filename().string();
}

std::string FileUtils::getPreferredPath(const std::string& path) {
  return fs::path(path).make_preferred().string();
}

std::string FileUtils::makeRelativePath(const std::string& in_path) {
  const std::string separator(1, fs::path::preferred_separator);
  // Standardize it so we can avoid special cases and wildcards!
  fs::path p(in_path);
  std::string path = p.make_preferred().string();
  // Handle Windows specific absolute paths
  if (p.is_absolute() && (path.length() > 1) && (path[1] == ':')) path[1] = '$';
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
