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

#include <string>
#include <string_view>
#include <vector>

#include "DesignCompile/CompileHelper.h"
#include "DesignCompile/CompilerHarness.h"
#include "SourceCompile/ParserHarness.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"

using ::testing::ElementsAre;

namespace SURELOG {
namespace {
TEST(CompileExpression, ExprFromParseTree1) {
  CompileHelper helper;
  ParserHarness pharness;
  CompilerHarness charness;
  CompileDesign* compileDesign = charness.getCompileDesign();
  // Cannot use parameters assignments in next expression, there is no
  // elaboration performed here!
  FileContent* fC = pharness.parse(
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
    UHDM::expr* exp = (UHDM::expr*)helper.compileExpression(
        nullptr, fC, rhs, compileDesign, nullptr, nullptr, true, true);
    EXPECT_EQ(exp->UhdmType(), UHDM::uhdmconstant);
    bool invalidValue = false;
    EXPECT_EQ(helper.get_value(invalidValue, exp), 16);
  }
}
}  // namespace
}  // namespace SURELOG
