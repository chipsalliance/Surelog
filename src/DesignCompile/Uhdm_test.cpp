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
#include <tuple>
#include <vector>

#include "DesignCompile/CompileHelper.h"
#include "DesignCompile/ElaboratorHarness.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"

// UHDM
#include <uhdm/design.h>
#include <uhdm/module.h>
#include <uhdm/port.h>

using ::testing::ElementsAre;

namespace SURELOG {
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

}  // namespace
}  // namespace SURELOG
