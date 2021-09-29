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
 * File:   FileUtils.h
 * Author: alain
 *
 * Created on March 16, 2017, 11:02 PM
 */

#ifndef FILEUTILS_H
#define FILEUTILS_H

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

namespace SURELOG {

typedef uint64_t SymbolId;
class SymbolTable;

class FileUtils final {
 public:
  static bool fileExists(std::string_view name);
  static bool fileIsRegular(std::string_view name);
  static bool fileIsDirectory(std::string_view name);

  // Find file whose name is available in the SymbolTable either in
  // the current directory or under each of the paths.
  // If found, return the symbolID representing that file.
  static SymbolId locateFile(SymbolId file, SymbolTable* symbols,
                             const std::vector<SymbolId>& paths);
  static bool mkDir(std::string_view path);
  static bool rmDirRecursively(std::string_view path);
  static std::string getFullPath(std::string_view path);
  static bool getFullPath(std::string_view path, std::string* result);
  static std::string getPathName(std::string_view path);
  static std::string basename(std::string_view str);
  static uint64_t fileSize(std::string_view name);
  static std::string hashPath(const std::string& path);
  static std::vector<SymbolId> collectFiles(std::string_view dirPath,
                                            std::string_view extension,
                                            SymbolTable* symbols);
  static std::vector<SymbolId> collectFiles(SymbolId dirPath,
                                            SymbolId extension,
                                            SymbolTable* symbols);
  static std::vector<SymbolId> collectFiles(std::string_view pathSpec,
                                            SymbolTable* symbols);
  static std::string getFileContent(const std::string& name);
  static std::string getPreferredPath(std::string_view path);
  static std::string makeRelativePath(std::string_view path);

 private:
  FileUtils() = delete;
  FileUtils(const FileUtils& orig) = delete;
  ~FileUtils() = delete;
};

};  // namespace SURELOG

#endif /* FILEUTILS_H */
