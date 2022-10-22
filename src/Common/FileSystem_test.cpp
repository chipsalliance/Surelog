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
 * File:   FileSystem_test.cpp
 * Author: hs
 *
 * Created on June 1, 2022, 3:00 AM
 */

#include <Surelog/Common/FileSystem.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/Utils/StringUtils.h>
#include <gtest/gtest.h>

#include <chrono>
#include <filesystem>
#include <fstream>
#include <map>
#include <string>
#include <vector>

namespace SURELOG {

namespace fs = std::filesystem;

namespace {
class TestFileSystem : public FileSystem {
 public:
  TestFileSystem() : FileSystem(fs::current_path()) {}
};

std::string getUniqueTempFileName() {
  return std::to_string(
      std::chrono::steady_clock::now().time_since_epoch().count());
}

TEST(FileSystemTest, ReadWriteOperations) {
  const fs::path testdir = testing::TempDir();
  const fs::path filename = getUniqueTempFileName();
  const fs::path filepath = testdir / filename;
  const std::string_view line1 = "Line1: This file contains some bytes.";
  const std::string_view line2 = "Line2: This file contains more bytes.";
  const std::string_view line3 = "Line3: This is the last line.";

  TestFileSystem fileSystem;
  SymbolTable symbolTable;

  PathId fileId = fileSystem.toPathId(filepath, &symbolTable);

  EXPECT_FALSE(fileSystem.exists(fileId));
  EXPECT_FALSE(fileSystem.isDirectory(fileId));
  EXPECT_FALSE(fileSystem.isRegularFile(fileId));

  std::string content;
  EXPECT_FALSE(fileSystem.readContent(fileId, content));

  std::vector<std::string> lines;
  EXPECT_FALSE(fileSystem.readLines(fileId, lines));

  lines.emplace_back(line1);
  lines.emplace_back(line2);
  lines.emplace_back(line3);
  EXPECT_TRUE(fileSystem.writeLines(fileId, lines));

  EXPECT_TRUE(fileSystem.exists(fileId));
  EXPECT_FALSE(fileSystem.isDirectory(fileId));
  EXPECT_TRUE(fileSystem.isRegularFile(fileId));

  std::string actualContent;
  EXPECT_TRUE(fileSystem.readContent(fileId, actualContent));

  const std::string expectedContent =
      StrCat(line1, "\n", line2, "\n", line3, "\n");
  EXPECT_EQ(actualContent, expectedContent);

  std::vector<std::string> actualLines;
  EXPECT_TRUE(fileSystem.readLines(fileId, actualLines));

  const std::vector<std::string>& expectedLines = lines;
  EXPECT_EQ(actualLines, expectedLines);

  for (size_t i = 0, n = expectedLines.size(); i < n; ++i) {
    content.clear();
    EXPECT_TRUE(fileSystem.readLine(fileId, i + 1, content));
    EXPECT_EQ(content, expectedLines[i]);
  }
  content.clear();
  EXPECT_FALSE(fileSystem.readLine(fileId, expectedLines.size() + 1, content));
}

TEST(FileSystemTest, LoadSaveOperations) {
  const fs::path testdir = testing::TempDir();
  const fs::path filename = getUniqueTempFileName();
  const fs::path filepath = testdir / filename;
  const std::string_view lines =
      "Line1: This file contains some bytes.\n"
      "Line2: This file contains more bytes.\n"
      "Line3: This is the last line.";

  TestFileSystem fileSystem;
  SymbolTable symbolTable;

  PathId fileId = fileSystem.toPathId(filepath, &symbolTable);

  EXPECT_FALSE(fileSystem.exists(fileId));
  EXPECT_FALSE(fileSystem.isDirectory(fileId));
  EXPECT_FALSE(fileSystem.isRegularFile(fileId));

  std::vector<char> content;
  EXPECT_FALSE(fileSystem.loadContent(fileId, content));

  content.reserve(lines.length());
  std::copy(lines.begin(), lines.end(), std::back_inserter(content));
  EXPECT_TRUE(fileSystem.saveContent(fileId, content));

  EXPECT_TRUE(fileSystem.exists(fileId));
  EXPECT_FALSE(fileSystem.isDirectory(fileId));
  EXPECT_TRUE(fileSystem.isRegularFile(fileId));

  std::vector<char> actualContent;
  EXPECT_TRUE(fileSystem.loadContent(fileId, actualContent));

  const std::vector<char>& expectedContent = content;
  EXPECT_EQ(actualContent, expectedContent);
}

TEST(FileSystemTest, BasicFileOperations) {
  const fs::path testdir = testing::TempDir();
  const fs::path dirtest = testdir / "file-exist-dir";
  const std::string_view filename = "file-exists-test.txt";
  const fs::path filepath = dirtest / filename;
  const std::string_view dummy_data = "This file contains some bytes";

  TestFileSystem fileSystem;
  SymbolTable symbolTable;
  const PathId dirId = fileSystem.toPathId(dirtest, &symbolTable);
  const PathId fileId = fileSystem.toPathId(filepath, &symbolTable);

  EXPECT_FALSE(fileSystem.exists(dirId));
  EXPECT_TRUE(fileSystem.rmtree(dirId));  // not there: no error
  EXPECT_FALSE(fileSystem.isDirectory(dirId));

  EXPECT_TRUE(fileSystem.mkdirs(dirId));
  EXPECT_TRUE(fileSystem.isDirectory(dirId));
  EXPECT_FALSE(fileSystem.isRegularFile(dirId));

  EXPECT_FALSE(fileSystem.exists(fileId));
  EXPECT_TRUE(fileSystem.writeContent(fileId, dummy_data));
  EXPECT_TRUE(fileSystem.exists(fileId));
  EXPECT_FALSE(fileSystem.isDirectory(fileId));
  EXPECT_TRUE(fileSystem.isRegularFile(fileId));

  std::streamsize size = 0;
  EXPECT_TRUE(fileSystem.filesize(fileId, &size));
  EXPECT_EQ(size, dummy_data.size());

  std::string content;
  EXPECT_TRUE(fileSystem.readContent(fileId, content));
  EXPECT_EQ(content, dummy_data);

  EXPECT_FALSE(fileSystem.remove(dirId));  // Non-empty dir
  EXPECT_TRUE(fileSystem.rmtree(dirId));
  EXPECT_FALSE(fileSystem.exists(dirId));
}

TEST(FileSystemTest, LocateFile) {
  const std::string search_file = "search-file.txt";

  const fs::path testdir = FileSystem::normalize(testing::TempDir());
  const fs::path basedir = testdir / "locate-file-test";
  const fs::path path1 = basedir / "dir1";
  const fs::path path2 = basedir / "dir2";
  const fs::path actual_dir_1 = basedir / "actual-dir-1";
  const fs::path actual_dir_2 = basedir / "actual-dir-2";

  std::error_code ec;
  TestFileSystem fileSystem;
  SymbolTable symbolTable;

  const PathId pathId1 = fileSystem.toPathId(path1, &symbolTable);
  const PathId pathId2 = fileSystem.toPathId(path2, &symbolTable);
  const PathId dirId1 = fileSystem.toPathId(actual_dir_1, &symbolTable);
  const PathId dirId2 = fileSystem.toPathId(actual_dir_2, &symbolTable);

  EXPECT_TRUE(fileSystem.mkdirs(pathId1));
  EXPECT_TRUE(fileSystem.mkdirs(dirId1));
  EXPECT_TRUE(fileSystem.mkdirs(dirId2));

  const std::vector<PathId> directories{
      pathId1,
      pathId2,
      dirId1,
      dirId2,
  };

  // At this point, the file does not exist yet.
  const PathId not_exists =
      fileSystem.locate(search_file, directories, &symbolTable);
  EXPECT_EQ(not_exists, BadPathId);

  const fs::path actual_loc_1 =
      FileSystem::normalize(actual_dir_1 / search_file);
  std::ofstream(actual_loc_1).close();

  PathId now_exists = fileSystem.locate(search_file, directories, &symbolTable);
  EXPECT_NE(now_exists, BadPathId);
  EXPECT_EQ(fileSystem.toPath(now_exists), actual_loc_1);

  PathId already_found =
      fileSystem.locate(search_file, directories, &symbolTable);
  EXPECT_EQ(already_found, now_exists);

  const fs::path actual_loc_2 = actual_dir_2 / search_file;
  std::ofstream(actual_loc_2).close();

  PathId now_exists_1 =
      fileSystem.locate(search_file, directories, &symbolTable);
  EXPECT_NE(now_exists_1, BadPathId);
  EXPECT_EQ(fileSystem.toPath(now_exists_1), actual_loc_1);

  EXPECT_TRUE(fileSystem.remove(now_exists_1));
  EXPECT_FALSE(fileSystem.exists(now_exists_1));

  PathId now_exists_2 =
      fileSystem.locate(search_file, directories, &symbolTable);
  EXPECT_NE(now_exists_2, BadPathId);
  EXPECT_EQ(fileSystem.toPath(now_exists_2), actual_loc_2);

  EXPECT_TRUE(fileSystem.rmtree(fileSystem.toPathId(basedir, &symbolTable)));
}
}  // namespace
}  // namespace SURELOG
