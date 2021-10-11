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

using ::testing::ElementsAre;

namespace SURELOG {
namespace {

TEST(Elaboration, ExprFromPpTree) {
  CompileHelper helper;
  ElaboratorHarness eharness;

  // Preprocess, Parse, Compile, Elaborate
  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  std::tie(design, fC, compileDesign) = eharness.elaborate(
      "`define A {1'b1, 2'b10}\n"
      "\n"
      "`define B '{1'b1, 2'b10}\n"
      "\n"
      "module top();\n"
      "parameter p1 = `A;\n"
      "parameter p2 = `B;\n"
      "endmodule\n");

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
    const std::string_view name = fC->SymName(param);
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

  // Preprocess, Parse, Compile, Elaborate
  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  std::tie(design, fC, compileDesign) = eharness.elaborate(
      "module top();\n"
      "parameter p1 = 1 << 4;\n"
      "parameter p2 = (p1 >> 2) << 2;\n"
      "parameter p3 = (p2 * 2) / 2;\n"
      "endmodule\n");

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

TEST(Elaboration, ExprUsePackage) {
  CompileHelper helper;
  ElaboratorHarness eharness;

  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  // Preprocess, Parse, Compile, Elaborate
  std::tie(design, fC, compileDesign) = eharness.elaborate(R"(
  `define FOO 4
  package pkg;
    parameter p0 = `FOO;
  endpackage
  module top();
    parameter p1 = 1 << pkg::p0;
    parameter p2 = (p1 >> 2) << 2;
    parameter p3 = (p2 * 2) / 2;
  endmodule)");

  // Get handles
  auto insts = design->getTopLevelModuleInstances();
  ModuleInstance* top = nullptr;
  DesignComponent* component = nullptr;
  if (insts.size()) {
    top = insts.at(0);
    component = top->getDefinition();
  }
  EXPECT_NE(top, nullptr);
  NodeId root = fC->getRootNode();
  NodeId moduleRoot = fC->sl_collect(root, slModule_declaration);
  EXPECT_NE(moduleRoot, 0);

  std::vector<NodeId> assigns =
      fC->sl_collect_all(moduleRoot, slParam_assignment);
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

TEST(Elaboration, DollarBits) {
  CompileHelper helper;
  ElaboratorHarness eharness;

  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  // Preprocess, Parse, Compile, Elaborate
  std::tie(design, fC, compileDesign) = eharness.elaborate(R"(
  package pkg;
    typedef struct packed {
      logic[7:0] x;
      logic      z;
    } struct_t;
  endpackage : pkg
  module dut #(parameter int Width = 1) ();
  endmodule
  module top (input pkg::struct_t in);
    localparam int SyncWidth = $bits({in,in.x});
    dut #(.Width($bits({in.x}))) dut1();
    dut #(.Width($bits({in}))) dut2();
    dut #(.Width($bits(in))) dut3();
    dut #(.Width($bits({in,in.x}))) dut4();
  endmodule // top)");
  auto insts = design->getTopLevelModuleInstances();
  ModuleInstance* top = nullptr;
  if (insts.size()) {
    top = insts.at(0);
  }
  EXPECT_NE(top, nullptr);
  Compiler* compiler = compileDesign->getCompiler();
  vpiHandle hdesign = compiler->getUhdmDesign();
  UHDM::design* udesign = UhdmDesignFromVpiHandle(hdesign);
  for (auto topMod : *udesign->TopModules()) {
    for (auto passign : *topMod->Param_assigns()) {
      UHDM::expr* rhs = (UHDM::expr*)passign->Rhs();
      bool invalidValue = false;
      EXPECT_EQ(helper.get_value(invalidValue, rhs), 17);
    }
    for (auto sub : *topMod->Modules()) {
      const std::string_view instName = sub->VpiName();
      for (auto passign : *sub->Param_assigns()) {
        UHDM::expr* rhs = (UHDM::expr*)passign->Rhs();
        bool invalidValue = false;
        uint64_t val = helper.get_value(invalidValue, rhs);
        if (instName == "dut1") {
          EXPECT_EQ(val, 8);
        } else if (instName == "dut2") {
          EXPECT_EQ(val, 9);
        } else if (instName == "dut3") {
          EXPECT_EQ(val, 9);
        } else if (instName == "dut4") {
          EXPECT_EQ(val, 17);
        }
      }
    }
  }
}

TEST(Elaboration, DollarBitsHier) {
  CompileHelper helper;
  ElaboratorHarness eharness;
  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  // Preprocess, Parse, Compile, Elaborate
  std::tie(design, fC, compileDesign) = eharness.elaborate(R"(
  package my_pkg;
    typedef struct packed {
      logic [1:0] rxblvl;
      logic [15:0] nco;
    } uart_reg2hw_ctrl_reg_t;
    typedef struct  packed {
      uart_reg2hw_ctrl_reg_t ctrl;
    } uart_reg2hw_t;
  endpackage // my_pkg
  module top;
    my_pkg::uart_reg2hw_t reg2hw;
    parameter o = $bits(reg2hw.ctrl.nco);
  endmodule)");
  Compiler* compiler = compileDesign->getCompiler();
  vpiHandle hdesign = compiler->getUhdmDesign();
  UHDM::design* udesign = UhdmDesignFromVpiHandle(hdesign);
  for (auto topMod : *udesign->TopModules()) {
    for (auto passign : *topMod->Param_assigns()) {
      UHDM::expr* rhs = (UHDM::expr*)passign->Rhs();
      bool invalidValue = false;
      EXPECT_EQ(helper.get_value(invalidValue, rhs), 16);
    }
  }
}

TEST(Elaboration, ConcatHexa) {
  CompileHelper helper;
  ElaboratorHarness eharness;
  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  // Preprocess, Parse, Compile, Elaborate
  std::tie(design, fC, compileDesign) = eharness.elaborate(R"(
  module dut();
    localparam logic [31:0] JT = {
      4'h0,     
      16'h4F54, 
      11'h426,  
      1'b1      
    };
  endmodule)");
  Compiler* compiler = compileDesign->getCompiler();
  vpiHandle hdesign = compiler->getUhdmDesign();
  UHDM::design* udesign = UhdmDesignFromVpiHandle(hdesign);
  for (auto topMod : *udesign->TopModules()) {
    for (auto passign : *topMod->Param_assigns()) {
      UHDM::expr* rhs = (UHDM::expr*)passign->Rhs();
      bool invalidValue = false;
      EXPECT_EQ(helper.get_value(invalidValue, rhs), 83183693);
    }
  }
}

TEST(Elaboration, ParamSubstituteWhenConstant) {
  CompileHelper helper;
  ElaboratorHarness eharness;
  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  // Preprocess, Parse, Compile, Elaborate
  std::tie(design, fC, compileDesign) = eharness.elaborate(R"(
  package aes_pkg;
    parameter logic [7:0][3:0] X = 32'habcd;
  endpackage 
  module aes_cipher_core;
    import aes_pkg::*;
    parameter logic [7:0][3:0] P = X;
  endmodule )");
  Compiler* compiler = compileDesign->getCompiler();
  vpiHandle hdesign = compiler->getUhdmDesign();
  UHDM::design* udesign = UhdmDesignFromVpiHandle(hdesign);
  for (auto topMod : *udesign->TopModules()) {
    for (auto passign : *topMod->Param_assigns()) {
      UHDM::expr* rhs = (UHDM::expr*)passign->Rhs();
      bool invalidValue = false;
      EXPECT_EQ(rhs->UhdmType(), UHDM::uhdmconstant);
      EXPECT_EQ(helper.get_value(invalidValue, rhs), 43981);
    }
  }
}

TEST(Elaboration, ParamSubstituteComplex) {
  CompileHelper helper;
  ElaboratorHarness eharness;
  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  // Preprocess, Parse, Compile, Elaborate
  std::tie(design, fC, compileDesign) = eharness.elaborate(R"(
module top();

typedef logic [0:4]       fmt_logic_t;  
  
typedef struct packed {
    int unsigned Width;
    logic        EnableVectors;
    logic        EnableNanBox;
    fmt_logic_t  FpFmtMask;
    fmt_logic_t IntFmtMask;
  } fpu_features_t;

localparam fpu_features_t RV64D_Xsflt = '{
    Width:         64,
    EnableVectors: 1'b1,
    EnableNanBox:  1'b1,
    FpFmtMask:     5'b11111,
    IntFmtMask:    4'b1111
  };
 localparam XLEN = 64;

localparam IS_XLEN64  = (XLEN == 32) ? 1'b0 : 1'b1;
localparam bit RVF = IS_XLEN64; 
localparam bit RVD = IS_XLEN64;
localparam bit XF16    = 1'b0; 
localparam bit XF16ALT = 1'b0; 
localparam bit XF8     = 1'b0; 
localparam bit XFVEC   = 1'b0;

localparam fpu_features_t FPU_FEATURES = '{
      Width:         64,
      EnableVectors: XFVEC,
      EnableNanBox:  1'b1,
      FpFmtMask:     {RVF, RVD, XF16, XF8, XF16ALT},
      IntFmtMask:    {XFVEC && XF8, XFVEC && (XF16 || XF16ALT), 1'b1, 1'b1}
    };
 parameter fpu_features_t   Features       = FPU_FEATURES;
 parameter fmt_logic_t      FpFmtMask     = Features.FpFmtMask;
 
localparam DEBUGME = FpFmtMask[0];

endmodule

)");
  Compiler* compiler = compileDesign->getCompiler();
  vpiHandle hdesign = compiler->getUhdmDesign();
  UHDM::design* udesign = UhdmDesignFromVpiHandle(hdesign);
  for (auto topMod : *udesign->TopModules()) {
    for (auto passign : *topMod->Param_assigns()) {
      if (passign->Lhs()->VpiName() == "DEBUGME") {
        UHDM::expr* rhs = (UHDM::expr*)passign->Rhs();
        bool invalidValue = false;
        EXPECT_EQ(rhs->UhdmType(), UHDM::uhdmconstant);
        EXPECT_EQ(helper.get_value(invalidValue, rhs), 1);
      }
    }
  }
}

}  // namespace
}  // namespace SURELOG
