/*
 Copyright 2021 Alain Dargelas

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

#include "Surelog/Common/PathId.h"

#include <gtest/gtest.h>

#include <filesystem>
#include <memory>

#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/PlatformFileSystem.h"
#include "Surelog/SourceCompile/SymbolTable.h"

namespace SURELOG {

namespace fs = std::filesystem;

namespace {
class TestFileSystem : public PlatformFileSystem {
 public:
  explicit TestFileSystem(const fs::path &wd) : PlatformFileSystem(wd) {
    FileSystem::setInstance(this);
  }
  TestFileSystem() : TestFileSystem(fs::current_path()) {}
};

TEST(PathId, constructors) {
  const fs::path testdir = testing::TempDir();

  std::unique_ptr<SymbolTable> symbolTableA(new SymbolTable);
  std::unique_ptr<SymbolTable> symbolTableB(new SymbolTable);
  std::unique_ptr<FileSystem> fileSystem(new TestFileSystem);

  PathId pathId1a =
      fileSystem->toPathId((testdir / "path1").string(), symbolTableA.get());
  PathId pathId2a =
      fileSystem->toPathId((testdir / "path2").string(), symbolTableA.get());

  PathId pathId1b =
      fileSystem->toPathId((testdir / "path1").string(), symbolTableB.get());
  PathId pathId2b =
      fileSystem->toPathId((testdir / "path2").string(), symbolTableB.get());

  EXPECT_EQ(pathId1a.getSymbolTable(), pathId2a.getSymbolTable());
  EXPECT_EQ(pathId1b.getSymbolTable(), pathId2b.getSymbolTable());
  EXPECT_NE(pathId1a.getSymbolTable(), pathId1b.getSymbolTable());

  PathId pathId3a(pathId1a);
  EXPECT_EQ(pathId1a, pathId3a);
  EXPECT_EQ(pathId1a.getSymbolTable(), pathId3a.getSymbolTable());
}

TEST(PathId, assignment_operator) {
  const fs::path testdir = testing::TempDir();

  std::unique_ptr<SymbolTable> symbolTableA(new SymbolTable);
  std::unique_ptr<FileSystem> fileSystem(new TestFileSystem);

  PathId pathId1 =
      fileSystem->toPathId((testdir / "path1").string(), symbolTableA.get());

  PathId pathId2 = pathId1;
  EXPECT_EQ(pathId1, pathId2);
  EXPECT_EQ(pathId1.getSymbolTable(), pathId2.getSymbolTable());
}

TEST(PathId, comparison_operators) {
  const fs::path testdir = testing::TempDir();

  std::unique_ptr<SymbolTable> symbolTableA(new SymbolTable);
  std::unique_ptr<FileSystem> fileSystem(new TestFileSystem);

  PathId pathId1 =
      fileSystem->toPathId((testdir / "path1").string(), symbolTableA.get());
  PathId pathId2 =
      fileSystem->toPathId((testdir / "path2").string(), symbolTableA.get());

  PathId pathId4, pathId5;
  EXPECT_EQ(pathId4, pathId4);  // Both empty self
  EXPECT_EQ(pathId1, pathId1);  // Against non-empty self
  EXPECT_EQ(pathId4, pathId5);  // Two distinct empty
  EXPECT_NE(pathId1, pathId4);  // Empty against not
  EXPECT_NE(pathId1, pathId2);  // Two distinct non-empty

  std::unique_ptr<SymbolTable> symbolTableB(new SymbolTable);
  PathId pathId6 =
      fileSystem->toPathId((testdir / "path1").string(), symbolTableB.get());
  EXPECT_NE(pathId1.getSymbolTable(), pathId6.getSymbolTable());
  EXPECT_EQ(pathId1, pathId6);  // Same stored in distinct SymbolTables
}

}  // namespace
}  // namespace SURELOG
