/*
 Copyright 2021 The Surelog Team.

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

#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/Utils/FileUtils.h>
#include <gtest/gtest.h>

#include <filesystem>
#include <fstream>
#include <string>
#include <vector>

namespace SURELOG {

namespace fs = std::filesystem;

namespace {
TEST(FileUtilsTest, BasicFileOperations) {
  const std::string dirtest = testing::TempDir() + "/file-exist-dir";
  const std::string basename = "file-exists-test.txt";
  const std::string filename = dirtest + "/" + basename;
  const std::string dummy_data = "This file contains some bytes";

  EXPECT_TRUE(FileUtils::rmDirRecursively(dirtest));
  EXPECT_TRUE(FileUtils::rmDirRecursively(dirtest));  // not there: no error

  EXPECT_FALSE(FileUtils::fileIsDirectory(dirtest));

  EXPECT_TRUE(FileUtils::mkDirs(dirtest));

  EXPECT_TRUE(FileUtils::fileIsDirectory(dirtest));
  EXPECT_FALSE(FileUtils::fileIsRegular(dirtest));

  EXPECT_FALSE(FileUtils::fileExists(filename));

  {
    std::ofstream testfile(filename);
    testfile.write(dummy_data.data(), dummy_data.size());
    testfile.close();
  }
  EXPECT_TRUE(FileUtils::fileExists(filename));
  EXPECT_FALSE(FileUtils::fileIsDirectory(filename));
  EXPECT_TRUE(FileUtils::fileIsRegular(filename));

  EXPECT_EQ(FileUtils::fileSize(filename), dummy_data.size());

  const std::string content = FileUtils::getFileContent(filename);
  EXPECT_EQ(content, dummy_data);

  FileUtils::rmDirRecursively(dirtest);

  EXPECT_EQ(FileUtils::basename(filename), basename);
}

TEST(FileUtilsTest, LocateFile) {
  SymbolTable sym;
  const std::string search_file = "search-file.txt";

  const fs::path basedir = fs::path(testing::TempDir()) / "locate-file-test";
  const fs::path path1 = basedir / "dir1-no-slash";
  const fs::path path2 = basedir / "dir2-with-slash/";
  const fs::path actual_dir = basedir / "actual-dir";

  FileUtils::mkDirs(path1);
  FileUtils::mkDirs(actual_dir);

  std::vector<SymbolId> paths = {
      sym.registerSymbol(path1.string()),
      sym.registerSymbol(path2.string()),
      sym.registerSymbol(actual_dir.string()),
  };

  SymbolId search_file_id = sym.registerSymbol(search_file);

  // At this point, the file does not exist yet.
  SymbolId non_exist = FileUtils::locateFile(search_file_id, &sym, paths);
  EXPECT_EQ(non_exist, SymbolTable::getBadId());

  const fs::path actual_loc = actual_dir / search_file;
  std::ofstream(actual_loc).close();

  SymbolId now_exists = FileUtils::locateFile(search_file_id, &sym, paths);
  EXPECT_NE(now_exists, SymbolTable::getBadId());
  EXPECT_EQ(sym.getSymbol(now_exists), actual_loc);

  SymbolId already_found = FileUtils::locateFile(now_exists, &sym, paths);
  EXPECT_EQ(already_found, now_exists);

  FileUtils::rmDirRecursively(basedir);
}

TEST(FileUtilsTest, GetPathName) {
  EXPECT_EQ(FileUtils::getPathName(""), "");
  EXPECT_EQ(FileUtils::getPathName("/r/dir/file.txt"), fs::path("/r/dir"));
}

// Still missing
// FileUtils::getFullPath
// FileUtils::collectFiles() <- important, a lot of untested logic there.
// FileUtils::hashPath()
// FileUtils::getPrefferedPath()
}  // namespace
}  // namespace SURELOG
