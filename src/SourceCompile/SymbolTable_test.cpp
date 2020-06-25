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

#include "SourceCompile/SymbolTable.h"

#include <vector>
#include <string>
#include <string_view>

#include "gtest/gtest.h"
#include "gmock/gmock.h"

using testing::ElementsAre;

namespace SURELOG {
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

}  // namespace
}  // namespace SURELOG
