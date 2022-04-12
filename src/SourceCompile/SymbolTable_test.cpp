/*
 Copyright 2020 The Surelog Team.

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
#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

namespace SURELOG {
using testing::ElementsAre;

namespace {
TEST(SymbolTableTest, SymbolTableAccess) {
  SymbolTable table;

  const SymbolId foo_id = table.registerSymbol("foo");
  EXPECT_NE(foo_id, SymbolTable::getBadId());

  const SymbolId bar_id = table.registerSymbol("bar");
  EXPECT_NE(foo_id, bar_id);

  // Attempting to register the same symbol will result in original ID.
  EXPECT_EQ(table.registerSymbol("foo"), foo_id);
  EXPECT_EQ(table.registerSymbol("bar"), bar_id);

  // Retrieve symbol-ID by text string
  EXPECT_EQ(table.getId("foo"), foo_id);
  EXPECT_EQ(table.getId("bar"), bar_id);
  EXPECT_EQ(table.getId("baz"), SymbolTable::getBadId());  // no-exist

  // Retrieve text symbol by ID
  EXPECT_EQ(table.getSymbol(foo_id), "foo");
  EXPECT_EQ(table.getSymbol(bar_id), "bar");
  EXPECT_EQ(table.getSymbol(42), SymbolTable::getBadSymbol());  // no-exist

  // For now, symbols returned in getSymbols() always contain bad symbol as
  // first element (though this is an implementation detail and might change).
  EXPECT_THAT(table.getSymbols(),
              ElementsAre(SymbolTable::getBadSymbol(), "foo", "bar"));
}

TEST(SymbolTableTest, SymbolStringsAreStable) {
  SymbolTable table;

  const SymbolId foo_id = table.registerSymbol("foo");

  // Deliberately using .data() here so that API change to getSymbol() returning
  // std::string_view later will keep this test source-code compatible.
  const char *before_data = table.getSymbol(foo_id).data();

  // We want to make sure that even after reallocing the underlying
  // data structure, the symbol reference does not change. Let's enforce
  // some reallocs by creating a bunch of symbols.
  for (int i = 0; i < 100000; ++i) {
    table.registerSymbol("bar" + std::to_string(i));
  }

  const char *after_data = table.getSymbol(foo_id).data();

  EXPECT_EQ(before_data, after_data);
}

// Copying a symbol table also not allocate new strings, but just point
// to the already existing ones.
// Note, we shouldn't really have a copy constructor, but while it is there,
// let's also test that things work as expected.
TEST(SymbolTableTest, SymbolStringsAreStableAfterTableCopy) {
  SymbolTable table;

  const SymbolId foo_id = table.registerSymbol("foo");

  const char *before_data = table.getSymbol(foo_id).data();

  {
    SymbolTable table_copy(table);  // NOLINT
    const char *after_data = table.getSymbol(foo_id).data();
    EXPECT_EQ(before_data, after_data);
  }
}
}  // namespace
}  // namespace SURELOG
