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

#include <Surelog/Design/FileContent.h>
#include <Surelog/Expression/ExprBuilder.h>
#include <Surelog/SourceCompile/ParserHarness.h>
#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <memory>
#include <string>
#include <string_view>
#include <vector>

namespace SURELOG {

using ::testing::ElementsAre;

namespace {
TEST(ExprBuilderTest, BasicValueOp) {
  {
    LValue v0, v1, v2;
    v1.set((int64_t)1);
    v2.set((int64_t)0);
    v0.bitwAnd(&v1, &v2);
    EXPECT_EQ(v0.getValueL(), 0);
  }

  {
    LValue v0, v1, v2;
    v1.set((int64_t)1);
    v2.set((int64_t)0);
    v0.bitwOr(&v1, &v2);
    EXPECT_EQ(v0.getValueL(), 1);
  }
  {
    LValue v0, v1;
    v1.set((int64_t)1);
    v0.u_not(&v1);
    EXPECT_EQ(v0.getValueL(), 0);
  }
  {
    LValue v0, v1, v2;
    v1.set((int64_t)-1);
    v2.set((int64_t)1);
    v0.plus(&v1, &v2);
    EXPECT_EQ(v0.getValueL(), 0);
  }
  {
    LValue v0, v1, v2;
    v1.set((int64_t)-10);
    v2.set((int64_t)9);
    v0.plus(&v1, &v2);
    EXPECT_EQ(v0.getValueL(), -1);
    EXPECT_EQ(v0.uhdmValue(), "INT:-1");
  }
  {
    ValueFactory factory;
    std::unique_ptr<Value> v0(factory.newStValue());
    v0->set("BLAH");
    EXPECT_EQ(v0->uhdmValue(), "STRING:BLAH");
  }
}
TEST(ExprBuilderTest, BuildFrom) {
  {
    ExprBuilder builder;
    std::unique_ptr<Value> v1(builder.fromVpiValue("HEX:A", 4));
    std::unique_ptr<Value> v2(builder.fromVpiValue("INT:10", 0));
    std::unique_ptr<Value> v3(builder.fromString("2'b11"));
    std::unique_ptr<Value> v4(builder.fromString("4'hFF_FF"));
    std::unique_ptr<Value> v5(builder.fromString("-0.6"));
    std::unique_ptr<Value> v6(builder.fromVpiValue("UINT:11", 0));
    LValue v0;
    v0.equiv(v1.get(), v2.get());
    EXPECT_EQ(v1->uhdmValue(), "HEX:A");
    EXPECT_EQ(v0.getValueL(), 1);
    EXPECT_EQ(v3->getValueL(), 3);
    EXPECT_EQ(v4->uhdmValue(), "HEX:FFFF");
    EXPECT_EQ(v5->getValueD(), -0.6);
    EXPECT_EQ(v6->uhdmValue(), "UINT:11");
  }
}
TEST(ExprBuilderTest, ExprFromParseTree1) {
  ExprBuilder builder;
  ParserHarness harness;
  // Cannot use parameters assignments in next expression, there is no
  // elaboration performed here!
  auto fC = harness.parse(
      "module top();"
      "parameter p1 = 5 + 5;"
      "parameter p2 = 2 * 5;"
      "parameter p3 = -2 * -5;"
      "endmodule");
  NodeId root = fC->getRootNode();
  std::vector<NodeId> assigns = fC->sl_collect_all(root, slParam_assignment);
  for (NodeId param_assign : assigns) {
    NodeId param = fC->Child(param_assign);
    NodeId rhs = fC->Sibling(param);
    std::unique_ptr<Value> val(builder.evalExpr(fC.get(), rhs));
    EXPECT_EQ(val->isValid(), true);
    EXPECT_EQ(val->getValueUL(), 10);
  }
}
TEST(ExprBuilderTest, ExprFromParseTree2) {
  ExprBuilder builder;
  ParserHarness harness;
  // Cannot use parameters assignments in next expression, there is no
  // elaboration performed here!
  auto fC = harness.parse(
      "module top();"
      "parameter p1 = 1 << 4;"
      "parameter p2 = (1 << 8) >> 4;"
      "parameter p3 = (16 * 4) / 4;"
      "parameter p4 = 32 - 16;"
      "endmodule");
  NodeId root = fC->getRootNode();
  std::vector<NodeId> assigns = fC->sl_collect_all(root, slParam_assignment);
  for (NodeId param_assign : assigns) {
    NodeId param = fC->Child(param_assign);
    NodeId rhs = fC->Sibling(param);
    std::unique_ptr<Value> val(builder.evalExpr(fC.get(), rhs));
    EXPECT_EQ(val->isValid(), true);
    EXPECT_EQ(val->getValueUL(), 16);
  }
}
}  // namespace
}  // namespace SURELOG
