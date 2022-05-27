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
  EXPECT_NE(foo_id, BadSymbolId);

  const SymbolId bar_id = table.registerSymbol("bar");
  EXPECT_NE(foo_id, bar_id);

  // Attempting to register the same symbol will result in original ID.
  EXPECT_EQ(table.registerSymbol("foo"), foo_id);
  EXPECT_EQ(table.registerSymbol("bar"), bar_id);

  // Retrieve symbol-ID by text string
  EXPECT_EQ(table.getId("foo"), foo_id);
  EXPECT_EQ(table.getId("bar"), bar_id);
  EXPECT_EQ(table.getId("baz"), BadSymbolId);  // no-exist

  // Retrieve text symbol by ID
  EXPECT_EQ(table.getSymbol(foo_id), "foo");
  EXPECT_EQ(table.getSymbol(bar_id), "bar");
  EXPECT_EQ(table.getSymbol(SymbolId(42, BadRawSymbol)),
            SymbolTable::getBadSymbol());  // no-exist

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
  const void *before_data = table.getSymbol(foo_id).data();

  // We want to make sure that even after reallocing the underlying
  // data structure, the symbol reference does not change. Let's enforce
  // some reallocs by creating a bunch of symbols.
  for (int i = 0; i < 100000; ++i) {
    table.registerSymbol("bar" + std::to_string(i));
  }

  const void *after_data = table.getSymbol(foo_id).data();

  EXPECT_EQ(before_data, after_data);
}

// Copying a symbol table also not allocate new strings, but just point
// to the already existing ones.
// Note, we shouldn't really have a copy constructor, but while it is there,
// let's also test that things work as expected.
TEST(SymbolTableTest, SymbolStringsAreStableAfterTableCopy) {
  SymbolTable table;

  const SymbolId foo_id = table.registerSymbol("foo");

  const void *before_data = table.getSymbol(foo_id).data();

  {
    std::unique_ptr<SymbolTable> table_copy(table.CreateSnapshot());
    const void *after_data = table_copy->getSymbol(foo_id).data();
    EXPECT_EQ(before_data, after_data);
  }
}

TEST(SymbolTableTest, SequenceOfStackedSymbolTablesPreserved) {
  // Testing the semantics of stacked symbol tables with copy constructors.
  SymbolTable parent;
  const SymbolId foo_id = parent.registerSymbol("foo");
  const SymbolId bar_id = parent.registerSymbol("bar");
  EXPECT_TRUE(SymbolIdLessThanComparer()(foo_id, bar_id));
  EXPECT_EQ(bar_id, SymbolId(2, "bar"));

  std::unique_ptr<SymbolTable> child(parent.CreateSnapshot());
  const SymbolId baz_id = child->registerSymbol("baz");
  EXPECT_TRUE(SymbolIdLessThanComparer()(bar_id, baz_id));
  const SymbolId quux_id = child->registerSymbol("quux");
  EXPECT_TRUE(SymbolIdLessThanComparer()(baz_id, quux_id));
  EXPECT_EQ(quux_id, SymbolId(4, "quux"));

  std::unique_ptr<SymbolTable> grandchild(child->CreateSnapshot());
  const SymbolId foobar_id = grandchild->registerSymbol("foobar");
  EXPECT_TRUE(SymbolIdLessThanComparer()(quux_id, foobar_id));
  const SymbolId flip_id = grandchild->registerSymbol("flip");
  EXPECT_TRUE(SymbolIdLessThanComparer()(foobar_id, flip_id));
  EXPECT_EQ(flip_id, SymbolId(6, "flip"));

  // Attempting to re-register symbols will return the existing id.
  EXPECT_EQ(foo_id, grandchild->registerSymbol("foo"));
  EXPECT_EQ(baz_id, grandchild->registerSymbol("baz"));
  EXPECT_EQ(foobar_id, grandchild->registerSymbol("foobar"));

  struct {
    SymbolTable *testsym;
    std::vector<std::string_view> expected_symbols;
  } kTests[] = {
      {&parent, {"@@BAD_SYMBOL@@", "foo", "bar"}},
      {child.get(), {"@@BAD_SYMBOL@@", "foo", "bar", "baz", "quux"}},
      {grandchild.get(),
       {"@@BAD_SYMBOL@@", "foo", "bar", "baz", "quux", "foobar", "flip"}},
  };

  for (const auto &testcase : kTests) {
    SymbolTable &testsym = *testcase.testsym;
    std::vector<std::string_view> all_symbols = testsym.getSymbols();
    EXPECT_EQ(all_symbols, testcase.expected_symbols);

    for (size_t i = 0; i < all_symbols.size(); ++i) {
      const std::string_view symbol = all_symbols[i];
      EXPECT_EQ(symbol, testsym.getSymbol(SymbolId(i, BadRawSymbol))) << i;
      EXPECT_EQ(testsym.getId(symbol), SymbolId(i, symbol));
      EXPECT_EQ(testsym.registerSymbol(symbol),
                SymbolId(i, symbol));  // re-register attempt.
    }

    // Request value out of range will return bad symbol.
    EXPECT_EQ(SymbolTable::getBadSymbol(),
              testsym.getSymbol(SymbolId(all_symbols.size(), BadRawSymbol)));
  }

  // A new symbol introduced in the parent should not be visible
  // in any child that had been snapshotted before that time.
  const SymbolId hello_id = parent.registerSymbol("hello");  // new in parent
  EXPECT_EQ(child->getId("hello"), BadSymbolId);             // not in child
  EXPECT_EQ(grandchild->getId("hello"), BadSymbolId);

  // We can register our own version of the same name in the child and get
  // a local id.
  const SymbolId hello_child_id = child->registerSymbol("hello");
  EXPECT_NE(hello_id, hello_child_id);
  EXPECT_EQ(child->getId("hello"), hello_child_id);
  EXPECT_EQ(child->getSymbol(hello_child_id), "hello");

  const SymbolId hello_grandchild_id = grandchild->registerSymbol("hello");
  EXPECT_NE(hello_id, hello_grandchild_id);
  EXPECT_NE(hello_child_id, hello_grandchild_id);
  EXPECT_EQ(grandchild->getId("hello"), hello_grandchild_id);
  EXPECT_EQ(grandchild->getSymbol(hello_grandchild_id), "hello");

  // Likewise, looking at 'all symbols', parent symbols only should be
  // included up to the point the snapshot happened.
  std::vector<std::string_view> expected_parent{"@@BAD_SYMBOL@@", "foo", "bar",
                                                "hello"};
  EXPECT_EQ(parent.getSymbols(), expected_parent);

  std::vector<std::string_view> expected_child{
      "@@BAD_SYMBOL@@", "foo", "bar", "baz", "quux", "hello"};
  EXPECT_EQ(child->getSymbols(), expected_child);

  std::vector<std::string_view> expected_grandchild{
      "@@BAD_SYMBOL@@", "foo", "bar", "baz", "quux", "foobar", "flip", "hello"};
  EXPECT_EQ(grandchild->getSymbols(), expected_grandchild);
}
}  // namespace
}  // namespace SURELOG
