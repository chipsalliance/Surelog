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
#include <filesystem>
#include <string>
#include <string_view>
#include <vector>

namespace fs = std::filesystem;

namespace SURELOG {

typedef uint64_t SymbolId;
class SymbolTable;

class FileUtils final {
 public:
  static bool fileExists(const fs::path& name);
  static bool fileIsRegular(const fs::path& name);
  static bool fileIsDirectory(const fs::path& name);

  // Find file whose name is available in the SymbolTable either in
  // the current directory or under each of the paths.
  // If found, return the symbolID representing that file.
  static SymbolId locateFile(SymbolId file, SymbolTable* symbols,
                             const std::vector<SymbolId>& paths);
  static bool mkDirs(const fs::path& path);
  static bool rmDirRecursively(const fs::path& path);
  static fs::path getFullPath(const fs::path& path);
  static bool getFullPath(const fs::path& path, fs::path* result);
  static fs::path getPathName(const fs::path& path);
  static fs::path basename(const fs::path& str);
  static uint64_t fileSize(const fs::path& name);
  static std::string hashPath(const fs::path& path);
  static std::vector<SymbolId> collectFiles(const fs::path& dirPath,
                                            const fs::path& extension,
                                            SymbolTable* symbols);
  static std::vector<SymbolId> collectFiles(SymbolId dirPath,
                                            SymbolId extension,
                                            SymbolTable* symbols);
  static std::vector<SymbolId> collectFiles(const fs::path& pathSpec,
                                            SymbolTable* symbols);
  static std::string getFileContent(const fs::path& name);
  static fs::path makeRelativePath(const fs::path& path);
  static fs::path getPreferredPath(const fs::path& path);

 private:
  FileUtils() = delete;
  FileUtils(const FileUtils& orig) = delete;
  ~FileUtils() = delete;
};

};  // namespace SURELOG

#endif /* FILEUTILS_H */
