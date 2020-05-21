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

#if (defined(_MSC_VER) || defined(__MINGW32__) || defined(__CYGWIN__))
  #include <direct.h>
  #define PATH_MAX _MAX_PATH
  // Supress the warning for the time being until we upgrade to C++17
  #define _SILENCE_EXPERIMENTAL_FILESYSTEM_DEPRECATION_WARNING
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

FileUtils::FileUtils() {}

FileUtils::FileUtils(const FileUtils& orig) {}

FileUtils::~FileUtils() {}

bool FileUtils::fileExists(const std::string name) {
  struct stat buffer;
  return (stat(name.c_str(), &buffer) == 0);
}

unsigned long FileUtils::fileSize(const std::string name) {
  struct stat buf;
  stat(name.c_str(), &buf);
  off_t size = buf.st_size;
  return size;
}

bool FileUtils::fileIsDirectory(const std::string name) {
  return fs::is_directory(name);
}

bool FileUtils::fileIsRegular(const std::string name) {
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

std::string FileUtils::getPathName(const std::string path) {
  return (fs::path(path).parent_path() += fs::path::preferred_separator).string();
}

std::string FileUtils::getFullPath(const std::string path) {
  std::error_code ec;
  fs::path fullPath = fs::canonical(path, ec);
  return ec ? path : fullPath.string();
}

bool FileUtils::getFullPath(const std::string path, std::string* const result) {
  std::error_code ec;
  fs::path fullPath = fs::canonical(path, ec);
  if (!ec && fileIsRegular(fullPath.string())) {
    if (result != nullptr) *result = fullPath.string();
    return true;
  }
  return false;
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

std::vector<SymbolId> FileUtils::collectFiles(const std::string dirPath,
                                              const std::string ext,
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

std::vector<SymbolId> FileUtils::collectFilesRegexp(const std::string dirPath,
                                                    const std::string regexp,
                                                    SymbolTable* symbols) {
  std::vector<SymbolId> result;
  if (!fileIsDirectory(dirPath)) {
    return result;
  }

  std::string newregexp;
  for (unsigned int i = 0; i < regexp.size(); i++) {
    if (regexp[i] == '.') {
      newregexp += "\\";
    }
    if (regexp[i] == '*') {
      newregexp += "[a-zA-Z0-9_-]*\\.*[a-zA-Z0-9_]*";
      continue;
    }
    if (regexp[i] == '?') {
      newregexp += "[a-zA-Z0-9_-]+";
      continue;
    }
    newregexp += regexp[i];
  }

  std::regex base_regex(newregexp);
  std::smatch base_match;

  for (fs::directory_entry entry : fs::directory_iterator(dirPath)) {
    std::string value = entry.path().string();
    if (std::regex_match(value, base_match, base_regex)) {
      result.push_back(symbols->registerSymbol(value));
    }
  }

  return result;
}

void FileUtils::collectFiles(const std::string dirPath,
                             std::vector<std::string>& dirs, unsigned int level,
                             SymbolTable* symbols,
                             std::vector<SymbolId>& files) {
  char currentDir[4096];
  if (!getcwd(currentDir, 4096)) return;

  if (chdir(dirPath.c_str()) != 0) return;
  char dir[4096];
  if (!getcwd(dir, 4096)) return;

  std::string regexp = dirs[level];
  std::vector<SymbolId> ids = collectFilesRegexp("./", regexp, symbols);
  for (auto id : ids) {
    std::string file = "./" + symbols->getSymbol(id);
    if (fileIsDirectory(file)) {
      if ((level + 1) < dirs.size()) {
        collectFiles(file, dirs, level + 1, symbols, files);
      }
    } else {
      std::string filePath = dir + std::string("/") + symbols->getSymbol(id);
      files.push_back(symbols->registerSymbol(filePath));
    }
  }

  if (chdir(currentDir) != 0) return;
}

std::vector<SymbolId> FileUtils::collectFiles(std::string pathSpec,
                                              SymbolTable* symbols) {
  std::vector<SymbolId> result;
  char currentDir[4096];
  if (!getcwd(currentDir, 4096)) return result;

  /*
  ?   single character wildcard (matches any single character)
  *   multiple character wildcard (matches any number of characters in a
  directory/file name)
  ... hierarchical wildcard (matches any number of hierarchical directories)
  ..  specifies the parent directory
  .   specifies the directory containing the lib.map
  Paths that end in / shall include all files in the specified directory.
  Identical to / * Paths that do not begin with / are relative to the directory
  in which the current lib.map file is located.
  */
  if (pathSpec[pathSpec.size() - 1] == '/') {
    pathSpec += "*";
  }

  std::vector<std::string> dirs;
  StringUtils::tokenize(pathSpec, "/", dirs);

  if (pathSpec[0] == '/') {
    // Absolute path
    if (chdir("/") != 0) return result;
  }

  char dir[4096];
  if (!getcwd(dir, 4096)) return result;
  std::vector<SymbolId> subs = collectFilesRegexp("./", dirs[0], symbols);
  for (auto id : subs) {
    std::string file = "./" + symbols->getSymbol(id);
    if (fileIsDirectory(file))
      collectFiles(file, dirs, 1, symbols, result);
    else {
      std::string filePath = dir + std::string("/") + symbols->getSymbol(id);
      result.push_back(symbols->registerSymbol(filePath));
    }
  }

  if (chdir(currentDir) != 0) return result;
  return result;
}

std::string FileUtils::getFileContent(const std::string filename) {
  std::ifstream in(filename, std::ios::in | std::ios::binary);
  if (in) {
    std::ostringstream contents;
    contents << in.rdbuf();
    in.close();
    return (contents.str());
  }
  return "FAILED_TO_LOAD_CONTENT";
}

std::string FileUtils::fileName(std::string str) {
  char c = '/';
  auto it1 = std::find_if(str.rbegin(), str.rend(),
                          [c](char ch) { return (ch == c); });
  if (it1 != str.rend()) 
    str.erase(str.begin(), it1.base());
  return str;
}

