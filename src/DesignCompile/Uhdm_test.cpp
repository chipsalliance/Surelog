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

#include <Surelog/Design/Design.h>
#include <Surelog/DesignCompile/CompileDesign.h>
#include <Surelog/DesignCompile/CompileHelper.h>
#include <Surelog/DesignCompile/ElaboratorHarness.h>
#include <Surelog/SourceCompile/Compiler.h>
#include <gmock/gmock.h>
#include <gtest/gtest.h>

// UHDM
#include <uhdm/design.h>
#include <uhdm/uhdm.h>

namespace SURELOG {

using ::testing::ElementsAre;

namespace {

TEST(Uhdm, PortType) {
  CompileHelper helper;
  ElaboratorHarness eharness;

  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  // Preprocess, Parse, Compile, Elaborate, Create UHDM model
  std::tie(design, fC, compileDesign) = eharness.elaborate(R"(
  module dut1(logic a, logic b);
  endmodule
  module dut2(input logic c, logic d);
  endmodule
  module dut3(output logic e, logic f);
  endmodule
  )");
  auto insts = design->getTopLevelModuleInstances();
  EXPECT_EQ(insts.size(), 3);
  Compiler* compiler = compileDesign->getCompiler();
  vpiHandle hdesign = compiler->getUhdmDesign();
  UHDM::design* udesign = UhdmDesignFromVpiHandle(hdesign);
  for (auto topMod : *udesign->TopModules()) {
    const std::string& instName = topMod->VpiName();
    EXPECT_EQ(topMod->Ports()->size(), 2);
    for (auto port : *topMod->Ports()) {
      if (instName == "UnitTest@dut1") {
        EXPECT_EQ(port->VpiDirection(), vpiInout);
      } else if (instName == "UnitTest@dut2") {
        EXPECT_EQ(port->VpiDirection(), vpiInput);
      } else if (instName == "UnitTest@dut3") {
        EXPECT_EQ(port->VpiDirection(), vpiOutput);
      } else {
        FAIL();
      }
    }
  }
}
TEST(Uhdm, Unsigned) {
  CompileHelper helper;
  ElaboratorHarness eharness;

  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  // Preprocess, Parse, Compile, Elaborate, Create UHDM model
  std::tie(design, fC, compileDesign) = eharness.elaborate(R"(
  module top();
    parameter logic [7:0] A = unsigned'(4); // A = 4
    parameter logic [7:0] B = $unsigned(-4); // B = 8'b11111100
    parameter logic [7:0] C = $unsigned(-4'sd4);// C = 8'b00001100
    parameter logic signed [7:0] D =  signed'(4'b1100); // D = -4
    parameter logic signed [7:0] E =  $signed(4'b1100); // E = -4
    parameter logic signed [7:0] F =  signed'(-4'sd4); // D = -4
  endmodule
  )");
  auto insts = design->getTopLevelModuleInstances();
  EXPECT_EQ(insts.size(), 1);
  Compiler* compiler = compileDesign->getCompiler();
  vpiHandle hdesign = compiler->getUhdmDesign();
  UHDM::design* udesign = UhdmDesignFromVpiHandle(hdesign);
  for (auto topMod : *udesign->TopModules()) {
    EXPECT_EQ(topMod->Param_assigns()->size(), 6);
    for (auto passign : *topMod->Param_assigns()) {
      UHDM::parameter* p = (UHDM::parameter*)passign->Lhs();
      const std::string_view pname = p->VpiName();
      UHDM::constant* value = (UHDM::constant*)passign->Rhs();
      if (pname == "A") {
        EXPECT_EQ(value->VpiValue(), "UINT:4");
      } else if (pname == "B") {
        EXPECT_EQ(value->VpiValue(), "UINT:252");
      } else if (pname == "C") {
        EXPECT_EQ(value->VpiValue(), "UINT:12");
      } else if (pname == "D") {
        EXPECT_EQ(value->VpiValue(), "INT:-4");
      } else if (pname == "E") {
        EXPECT_EQ(value->VpiValue(), "INT:-4");
      } else if (pname == "F") {
        EXPECT_EQ(value->VpiValue(), "INT:-4");
      } else {
        FAIL();
      }
    }
  }
}
}  // namespace
}  // namespace SURELOG
