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
#include <tuple>

#include "DesignCompile/CompileHelper.h"
#include "DesignCompile/CompilerHarness.h"
#include "SourceCompile/PreprocessHarness.h"
#include "DesignCompile/ElaboratorHarness.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"

using ::testing::ElementsAre;

namespace SURELOG {
namespace {
TEST(Elaboration, ExprFromPpTree) {
  CompileHelper helper;
  PreprocessHarness ppharness;
  ElaboratorHarness eharness;

  // Preprocess
  const std::string text = ppharness.preprocess(
      "`define A {1'b1, 2'b10}\n"
      "\n"
      "`define B '{1'b1, 2'b10}\n"
      "\n"
      "module top();\n"
      "parameter p1 = `A;\n"
      "parameter p2 = `B;\n"
      "endmodule\n");

  // Parse, Compile, Elaborate    
  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  std::tie(design, fC, compileDesign) = eharness.elaborate(text);

  // Get handles
  auto insts = design->getTopLevelModuleInstances();
  ModuleInstance* top = nullptr;
  DesignComponent* component = nullptr;
  if (insts.size()) {
    top = insts.at(0);
    component = top->getDefinition();
  }
  NodeId root = fC->getRootNode();
  EXPECT_NE(top, nullptr);

  std::vector<NodeId> assigns = fC->sl_collect_all(root, slParam_assignment);
  EXPECT_EQ(assigns.size(), 2);
  for (NodeId param_assign : assigns) {
    NodeId param = fC->Child(param_assign);
    const std::string& name = fC->SymName(param);
    NodeId rhs = fC->Sibling(param);
    // Not reduced
    UHDM::expr* exp1 = (UHDM::expr*)helper.compileExpression(
        component, fC, rhs, compileDesign, nullptr, top, false, true);
    EXPECT_EQ(exp1->UhdmType(), UHDM::uhdmoperation);
    // Reduced
    UHDM::expr* exp2 = (UHDM::expr*)helper.compileExpression(
        component, fC, rhs, compileDesign, nullptr, top, true, true);
    if (name == "p1") {
      EXPECT_EQ(exp2->UhdmType(), UHDM::uhdmconstant);
      bool invalidValue = false;
      EXPECT_EQ(helper.get_value(invalidValue, exp2), 6);
    }
  }
}
TEST(Elaboration, ExprFromText) {
  CompileHelper helper;
  ElaboratorHarness eharness;

  // Parse, Compile, Elaborate
  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  std::tie(design, fC, compileDesign) = eharness.elaborate(
      "module top();"
      "parameter p1 = 1 << 4;"
      "parameter p2 = (p1 >> 2) << 2;"
      "parameter p3 = (p2 * 2) / 2;"
      "endmodule");

  // Get handles
  auto insts = design->getTopLevelModuleInstances();
  ModuleInstance* top = nullptr;
  DesignComponent* component = nullptr;
  if (insts.size()) {
    top = insts.at(0);
    component = top->getDefinition();
  }
  NodeId root = fC->getRootNode();
  EXPECT_NE(top, nullptr);

  std::vector<NodeId> assigns = fC->sl_collect_all(root, slParam_assignment);
  EXPECT_EQ(assigns.size(), 3);
  for (NodeId param_assign : assigns) {
    NodeId param = fC->Child(param_assign);
    NodeId rhs = fC->Sibling(param);
    // Reduced
    UHDM::expr* exp = (UHDM::expr*)helper.compileExpression(
        component, fC, rhs, compileDesign, nullptr, top, true, true);
    EXPECT_EQ(exp->UhdmType(), UHDM::uhdmconstant);
    bool invalidValue = false;
    EXPECT_EQ(helper.get_value(invalidValue, exp), 16);
  }
}
}  // namespace
}  // namespace SURELOG
