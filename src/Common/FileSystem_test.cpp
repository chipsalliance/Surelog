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
}  // namespace
}  // namespace SURELOG
