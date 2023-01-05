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
#include <Surelog/Design/FileContent.h>
#include <Surelog/Design/ModuleInstance.h>
#include <Surelog/DesignCompile/CompileDesign.h>
#include <Surelog/DesignCompile/CompileHelper.h>
#include <Surelog/DesignCompile/ElaboratorHarness.h>
#include <Surelog/SourceCompile/Compiler.h>
#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <tuple>
#include <vector>

// UHDM
#include <uhdm/ExprEval.h>
#include <uhdm/cont_assign.h>
#include <uhdm/design.h>
#include <uhdm/expr.h>
#include <uhdm/gen_scope.h>
#include <uhdm/gen_scope_array.h>
#include <uhdm/int_typespec.h>
#include <uhdm/module_inst.h>
#include <uhdm/param_assign.h>
#include <uhdm/variables.h>
#include <uhdm/vpi_user.h>

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
  if (!insts.empty()) {
    top = insts.at(0);
    component = top->getDefinition();
  }
  NodeId root = fC->getRootNode();
  EXPECT_NE(top, nullptr);

  std::vector<NodeId> assigns =
      fC->sl_collect_all(root, VObjectType::slParam_assignment);
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
      UHDM::ExprEval eval;
      EXPECT_EQ(eval.get_value(invalidValue, exp2), 6);
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
  if (!insts.empty()) {
    top = insts.at(0);
    component = top->getDefinition();
  }
  NodeId root = fC->getRootNode();
  EXPECT_NE(top, nullptr);

  std::vector<NodeId> assigns =
      fC->sl_collect_all(root, VObjectType::slParam_assignment);
  EXPECT_EQ(assigns.size(), 3);
  for (NodeId param_assign : assigns) {
    NodeId param = fC->Child(param_assign);
    NodeId rhs = fC->Sibling(param);
    // Reduced
    UHDM::expr* exp = (UHDM::expr*)helper.compileExpression(
        component, fC, rhs, compileDesign, nullptr, top, true, true);
    EXPECT_EQ(exp->UhdmType(), UHDM::uhdmconstant);
    bool invalidValue = false;
    UHDM::ExprEval eval;
    EXPECT_EQ(eval.get_value(invalidValue, exp), 16);
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
  if (!insts.empty()) {
    top = insts.at(0);
    component = top->getDefinition();
  }
  EXPECT_NE(top, nullptr);
  NodeId root = fC->getRootNode();
  NodeId moduleRoot = fC->sl_collect(root, VObjectType::slModule_declaration);
  EXPECT_TRUE(moduleRoot);

  std::vector<NodeId> assigns =
      fC->sl_collect_all(moduleRoot, VObjectType::slParam_assignment);
  EXPECT_EQ(assigns.size(), 3);
  for (NodeId param_assign : assigns) {
    NodeId param = fC->Child(param_assign);
    NodeId rhs = fC->Sibling(param);
    // Reduced
    UHDM::expr* exp = (UHDM::expr*)helper.compileExpression(
        component, fC, rhs, compileDesign, nullptr, top, true, true);
    EXPECT_EQ(exp->UhdmType(), UHDM::uhdmconstant);
    bool invalidValue = false;
    UHDM::ExprEval eval;
    EXPECT_EQ(eval.get_value(invalidValue, exp), 16);
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
  if (!insts.empty()) {
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
      UHDM::ExprEval eval;
      EXPECT_EQ(eval.get_value(invalidValue, rhs), 17);
    }
    for (auto sub : *topMod->Modules()) {
      const std::string_view instName = sub->VpiName();
      for (auto passign : *sub->Param_assigns()) {
        UHDM::expr* rhs = (UHDM::expr*)passign->Rhs();
        bool invalidValue = false;
        UHDM::ExprEval eval;
        uint64_t val = eval.get_value(invalidValue, rhs);
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
      UHDM::ExprEval eval;
      EXPECT_EQ(eval.get_value(invalidValue, rhs), 16);
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
      UHDM::ExprEval eval;
      EXPECT_EQ(eval.get_value(invalidValue, rhs), 83183693);
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
      UHDM::ExprEval eval;
      EXPECT_EQ(eval.get_value(invalidValue, rhs), 43981);
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
        UHDM::ExprEval eval;
        EXPECT_EQ(eval.get_value(invalidValue, rhs), 1);
      }
    }
  }
}

TEST(Elaboration, SignedBinConstParam) {
  CompileHelper helper;
  ElaboratorHarness eharness;

  // Preprocess, Parse, Compile, Elaborate
  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  std::tie(design, fC, compileDesign) = eharness.elaborate(R"(
module top();
  parameter [1:0] p1 =  1'sb1;
  parameter [1:0] p2 =  2'sb10;
  parameter int p3 =  2'sb10;
  parameter int p4 =  3'sb101;
endmodule
  )");
  Compiler* compiler = compileDesign->getCompiler();
  vpiHandle hdesign = compiler->getUhdmDesign();
  UHDM::design* udesign = UhdmDesignFromVpiHandle(hdesign);
  for (auto topMod : *udesign->TopModules()) {
    for (auto passign : *topMod->Param_assigns()) {
      UHDM::expr* rhs = (UHDM::expr*)passign->Rhs();
      bool invalidValue = false;
      EXPECT_EQ(rhs->UhdmType(), UHDM::uhdmconstant);
      UHDM::ExprEval eval;
      int64_t val = eval.get_value(invalidValue, rhs);
      const std::string_view name = passign->Lhs()->VpiName();
      if (name == "p1") {
        EXPECT_EQ(val, 3);
      } else if (name == "p2") {
        EXPECT_EQ(val, 2);
      } else if (name == "p3") {
        EXPECT_EQ(val, -2);
      } else if (name == "p4") {
        EXPECT_EQ(val, -3);
      }
    }
  }
}

TEST(Elaboration, SignedBinConstAssign) {
  CompileHelper helper;
  ElaboratorHarness eharness;

  // Preprocess, Parse, Compile, Elaborate
  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  std::tie(design, fC, compileDesign) = eharness.elaborate(R"(
module top(output [3:0] x);
  reg [1:0] p1 =  1'sb1;
  reg [1:0] p2 =  2'sb10;
  int p3 =  2'sb10;
  assign x = '1;
endmodule
  )");
  Compiler* compiler = compileDesign->getCompiler();
  vpiHandle hdesign = compiler->getUhdmDesign();
  UHDM::design* udesign = UhdmDesignFromVpiHandle(hdesign);
  for (auto topMod : *udesign->TopModules()) {
    for (auto cassign : *topMod->Cont_assigns()) {
      UHDM::expr* rhs = (UHDM::expr*)cassign->Rhs();
      bool invalidValue = false;
      EXPECT_EQ(rhs->UhdmType(), UHDM::uhdmconstant);
      UHDM::ExprEval eval;
      int64_t val = eval.get_value(invalidValue, rhs);
      const std::string_view name = cassign->Lhs()->VpiName();
      if (name == "p1") {
        // Val is 1, but it has a signed typespec (Meaning negative bin number)
        EXPECT_EQ(val, 3);
        const UHDM::typespec* tps = rhs->Typespec();
        UHDM::int_typespec* itps = (UHDM::int_typespec*)tps;
        EXPECT_EQ(itps->VpiSigned(), true);
      } else if (name == "p2") {
        EXPECT_EQ(val, 2);
      } else if (name == "x") {
        EXPECT_EQ(val, 15);
      }
    }
    for (auto var : *topMod->Variables()) {
      UHDM::expr* rhs = (UHDM::expr*)var->Expr();
      bool invalidValue = false;
      EXPECT_EQ(rhs->UhdmType(), UHDM::uhdmconstant);
      UHDM::ExprEval eval;
      int64_t val = eval.get_value(invalidValue, rhs);
      const std::string_view name = var->VpiName();
      if (name == "p3") {
        EXPECT_EQ(val, -2);
      }
    }
  }
}

TEST(Elaboration, WordSizeFuncArg) {
  CompileHelper helper;
  ElaboratorHarness eharness;

  // Preprocess, Parse, Compile, Elaborate
  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  std::tie(design, fC, compileDesign) = eharness.elaborate(R"(
module top(output logic [31:0] o);
  typedef logic [31:0] word;   
   
  function automatic word element_sum(input word [1:0] w);
    return w[0] + w[1];
  endfunction
  parameter p = element_sum({32'h1234, 32'h5678}); 
endmodule
  )");
  Compiler* compiler = compileDesign->getCompiler();
  vpiHandle hdesign = compiler->getUhdmDesign();
  UHDM::design* udesign = UhdmDesignFromVpiHandle(hdesign);
  for (auto topMod : *udesign->TopModules()) {
    for (auto passign : *topMod->Param_assigns()) {
      UHDM::expr* rhs = (UHDM::expr*)passign->Rhs();
      bool invalidValue = false;
      EXPECT_EQ(rhs->UhdmType(), UHDM::uhdmconstant);
      UHDM::ExprEval eval;
      int64_t val = eval.get_value(invalidValue, rhs);
      EXPECT_EQ(val, 26796);
    }
  }
}

TEST(Elaboration, FuncNoArg) {
  CompileHelper helper;
  ElaboratorHarness eharness;

  // Preprocess, Parse, Compile, Elaborate
  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  std::tie(design, fC, compileDesign) = eharness.elaborate(R"(
module top(output int o);
   parameter int X [1:0] = '{0, 1};

   function automatic int theta();
      return X[0];
   endfunction : theta

   parameter p = theta();
endmodule
  )");
  Compiler* compiler = compileDesign->getCompiler();
  vpiHandle hdesign = compiler->getUhdmDesign();
  UHDM::design* udesign = UhdmDesignFromVpiHandle(hdesign);
  for (auto topMod : *udesign->TopModules()) {
    for (auto passign : *topMod->Param_assigns()) {
      UHDM::expr* rhs = (UHDM::expr*)passign->Rhs();
      bool invalidValue = false;
      const std::string_view name = passign->Lhs()->VpiName();
      if (name == "p") {
        EXPECT_EQ(rhs->UhdmType(), UHDM::uhdmconstant);
        UHDM::ExprEval eval;
        int64_t val = eval.get_value(invalidValue, rhs);
        EXPECT_EQ(val, 1);
      }
    }
  }
}

TEST(Elaboration, FuncReturn) {
  CompileHelper helper;
  ElaboratorHarness eharness;

  // Preprocess, Parse, Compile, Elaborate
  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  std::tie(design, fC, compileDesign) = eharness.elaborate(R"(
module top(output logic o);
   function automatic logic theta();
      for (int x = 0 ; x < 5 ; x++) begin
         logic a;
         a = 1'b1;
         return a;
      end
      return 1'b0;
   endfunction : theta

   parameter p = theta();
endmodule : top

  )");
  Compiler* compiler = compileDesign->getCompiler();
  vpiHandle hdesign = compiler->getUhdmDesign();
  UHDM::design* udesign = UhdmDesignFromVpiHandle(hdesign);
  for (auto topMod : *udesign->TopModules()) {
    for (auto passign : *topMod->Param_assigns()) {
      UHDM::expr* rhs = (UHDM::expr*)passign->Rhs();
      bool invalidValue = false;
      const std::string_view name = passign->Lhs()->VpiName();
      if (name == "p") {
        EXPECT_EQ(rhs->UhdmType(), UHDM::uhdmconstant);
        UHDM::ExprEval eval;
        int64_t val = eval.get_value(invalidValue, rhs);
        EXPECT_EQ(val, 1);
      }
    }
  }
}

TEST(Elaboration, StructValToLogic) {
  CompileHelper helper;
  ElaboratorHarness eharness;

  // Preprocess, Parse, Compile, Elaborate
  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  std::tie(design, fC, compileDesign) = eharness.elaborate(R"(
module top();

   typedef struct packed {
      logic [1:0] a;
      logic [2:0] b;
      logic [1:0] c;
   } struct_t;

   typedef enum logic [1:0] {
      ENUM_ITEM = 2'b11
   } enum_t;

   parameter struct_t CTRL_RESET = '{
      a: ENUM_ITEM,
      b: '0,
      c: ENUM_ITEM
   };

   parameter  logic [6:0] RESVAL = CTRL_RESET;

endmodule
  )");
  Compiler* compiler = compileDesign->getCompiler();
  vpiHandle hdesign = compiler->getUhdmDesign();
  UHDM::design* udesign = UhdmDesignFromVpiHandle(hdesign);
  for (auto topMod : *udesign->TopModules()) {
    for (auto passign : *topMod->Param_assigns()) {
      UHDM::expr* rhs = (UHDM::expr*)passign->Rhs();
      bool invalidValue = false;
      const std::string_view name = passign->Lhs()->VpiName();
      if (name == "RESVAL") {
        UHDM::ExprEval eval;
        int64_t val = eval.get_value(invalidValue, rhs);
        EXPECT_EQ(val, 99);
      }
    }
  }
}

TEST(Elaboration, DefaultValLogic) {
  CompileHelper helper;
  ElaboratorHarness eharness;

  // Preprocess, Parse, Compile, Elaborate
  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  std::tie(design, fC, compileDesign) = eharness.elaborate(R"(
module top();
  parameter logic[7:0] P = '{default: 1};
endmodule
  )");
  Compiler* compiler = compileDesign->getCompiler();
  vpiHandle hdesign = compiler->getUhdmDesign();
  UHDM::design* udesign = UhdmDesignFromVpiHandle(hdesign);
  for (auto topMod : *udesign->TopModules()) {
    for (auto passign : *topMod->Param_assigns()) {
      UHDM::expr* rhs = (UHDM::expr*)passign->Rhs();
      bool invalidValue = false;
      const std::string_view name = passign->Lhs()->VpiName();
      if (name == "P") {
        UHDM::ExprEval eval;
        int64_t val = eval.get_value(invalidValue, rhs);
        EXPECT_EQ(val, 255);
      }
    }
  }
}

TEST(Elaboration, AssignmentBitOrder) {
  CompileHelper helper;
  ElaboratorHarness eharness;

  // Preprocess, Parse, Compile, Elaborate
  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  std::tie(design, fC, compileDesign) = eharness.elaborate(R"(
module dut();
   parameter logic [0:4] A = 0;
endmodule 

module top();
   typedef struct packed {
      logic [1:0] a;
      logic [2:0] b;
   } struct_1;
 
   parameter struct_1 X = '{a: 2'b10, b: 3'b110};

   dut #(.A(X)) u_dut();
endmodule

  )");
  Compiler* compiler = compileDesign->getCompiler();
  vpiHandle hdesign = compiler->getUhdmDesign();
  UHDM::design* udesign = UhdmDesignFromVpiHandle(hdesign);
  for (auto topMod : *udesign->TopModules()) {
    for (auto inst : *topMod->Modules()) {
      for (auto passign : *inst->Param_assigns()) {
        UHDM::expr* rhs = (UHDM::expr*)passign->Rhs();
        bool invalidValue = false;
        const std::string_view name = passign->Lhs()->VpiName();
        if (name == "A") {
          UHDM::ExprEval eval;
          int64_t val = eval.get_value(invalidValue, rhs);
          EXPECT_EQ(val, 22);
        }
      }
    }
  }
}

TEST(Elaboration, EnumConstElab) {
  CompileHelper helper;
  ElaboratorHarness eharness;

  // Preprocess, Parse, Compile, Elaborate
  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  std::tie(design, fC, compileDesign) = eharness.elaborate(R"(
module prim_subreg;
   parameter logic [4:0] RESVAL = '0;
endmodule // prim_subreg

module prim_subreg_shadow;
   typedef struct packed {
      logic [2:0] a;
      logic [1:0] b;
   } struct_t;

   typedef enum logic [2:0] {
      ENUM_ITEM = 3'b000
   } enum_t;

   parameter struct_t RESVAL = '{
      a: ENUM_ITEM,
      b: '1
   };

   prim_subreg #(
      .RESVAL(RESVAL)
   ) staged_reg ();
endmodule // prim_subreg_shadow

module top;
   typedef struct packed {
      logic [1:0] a;
      logic [2:0] b;
   } struct_t;

   typedef enum logic [1:0] {
      ENUM_ITEM = 2'b11
   } enum_t;

   parameter struct_t CTRL_RESET = '{
      a: ENUM_ITEM,
      b: '0
   };

   prim_subreg_shadow #(
      .RESVAL(CTRL_RESET)
   ) u_ctrl_reg_shadowed ();
endmodule // top
  )");
  Compiler* compiler = compileDesign->getCompiler();
  vpiHandle hdesign = compiler->getUhdmDesign();
  UHDM::design* udesign = UhdmDesignFromVpiHandle(hdesign);
  for (auto topMod : *udesign->TopModules()) {
    for (auto inst : *topMod->Modules()) {
      for (auto inst2 : *inst->Modules()) {
        for (auto passign : *inst2->Param_assigns()) {
          UHDM::expr* rhs = (UHDM::expr*)passign->Rhs();
          bool invalidValue = false;
          const std::string_view name = passign->Lhs()->VpiName();
          if (name == "RESVAL") {
            UHDM::ExprEval eval;
            int64_t val = eval.get_value(invalidValue, rhs);
            EXPECT_EQ(val, 24);
          }
        }
      }
    }
  }
}

TEST(Elaboration, ParamNoDefault) {
  CompileHelper helper;
  ElaboratorHarness eharness;

  // Preprocess, Parse, Compile, Elaborate
  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  std::tie(design, fC, compileDesign) = eharness.elaborate(R"(
module dut();
parameter logic [4:0] A = 0;
endmodule // dut

module top();
 typedef struct packed {
    logic [1:0] a;
 } struct_1;
    
 parameter struct_1 X = '{a: '1};
 
 dut #(.A(X)) u_dut();
endmodule
  )");
  Compiler* compiler = compileDesign->getCompiler();
  vpiHandle hdesign = compiler->getUhdmDesign();
  UHDM::design* udesign = UhdmDesignFromVpiHandle(hdesign);
  for (auto topMod : *udesign->TopModules()) {
    for (auto inst : *topMod->Modules()) {
      for (auto passign : *inst->Param_assigns()) {
        UHDM::expr* rhs = (UHDM::expr*)passign->Rhs();
        bool invalidValue = false;
        const std::string_view name = passign->Lhs()->VpiName();
        if (name == "A") {
          UHDM::ExprEval eval;
          int64_t val = eval.get_value(invalidValue, rhs);
          EXPECT_EQ(val, 3);
        }
      }
    }
  }
}

TEST(Elaboration, ParamOverloading) {
  CompileHelper helper;
  ElaboratorHarness eharness;

  // Preprocess, Parse, Compile, Elaborate
  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  std::tie(design, fC, compileDesign) = eharness.elaborate(R"(
module prim_subreg;
   parameter logic [4:0] RESVAL = '0;
   int a = int'(RESVAL);
endmodule // prim_subreg

module prim_subreg_shadow;
   typedef struct packed {
      logic [2:0] a;
      logic [1:0] b;
   } struct_ab;

   parameter struct_ab RESVAL = '{
      a: '0,
      b: '1
   };

   prim_subreg #(
      .RESVAL(RESVAL)
   ) staged_reg();
   
endmodule // prim_subreg_shadow

module top;
   typedef struct packed {
      logic [1:0] a;
      logic [2:0] b;
   } struct_ab;
   parameter v1 = 1;
   parameter v2 = 0;
   
   parameter struct_ab CTRL_RESET = '{
    //  a: '1,
    //  b: '0
    v1, v2
   };

   prim_subreg_shadow #(
      .RESVAL(CTRL_RESET)
   ) u_ctrl_reg_shadowed();
endmodule // top
  )");
  Compiler* compiler = compileDesign->getCompiler();
  vpiHandle hdesign = compiler->getUhdmDesign();
  UHDM::design* udesign = UhdmDesignFromVpiHandle(hdesign);
  for (auto topMod : *udesign->TopModules()) {
    for (auto inst : *topMod->Modules()) {
      for (auto inst2 : *inst->Modules()) {
        for (auto passign : *inst2->Param_assigns()) {
          UHDM::expr* rhs = (UHDM::expr*)passign->Rhs();
          bool invalidValue = false;
          const std::string_view name = passign->Lhs()->VpiName();
          if (name == "RESVAL") {
            UHDM::ExprEval eval;
            int64_t val = eval.get_value(invalidValue, rhs);
            EXPECT_EQ(val, 8);
          }
        }
      }
    }
  }
}

TEST(Elaboration, BitSelect) {
  CompileHelper helper;
  ElaboratorHarness eharness;

  // Preprocess, Parse, Compile, Elaborate
  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  std::tie(design, fC, compileDesign) = eharness.elaborate(R"(
package my_pkg;
   function automatic logic [7:0] sbox4_8bit(logic [7:0] state_in);
      return state_in;
   endfunction : sbox4_8bit

   function automatic logic [15:0] sbox4_16bit(logic [15:0] state_in);
      logic [15:0] state_out;
      state_out[0 : 7] = sbox4_8bit(state_in[0 +: 8]);
      state_out[8 : 15] = sbox4_8bit(state_in[0 +: 8]);
      state_out[2] = 1'b0;
      state_out[14] = 1'b1;
      return state_out;
   endfunction : sbox4_16bit
endpackage // my_pkg

module top(output logic [15:0] o);
   assign o = my_pkg::sbox4_16bit(16'hAB0F);
endmodule // top
  )");
  Compiler* compiler = compileDesign->getCompiler();
  vpiHandle hdesign = compiler->getUhdmDesign();
  UHDM::design* udesign = UhdmDesignFromVpiHandle(hdesign);
  for (auto topMod : *udesign->TopModules()) {
    for (auto cassign : *topMod->Cont_assigns()) {
      UHDM::expr* rhs = (UHDM::expr*)cassign->Rhs();
      bool invalidValue = false;
      const std::string_view name = cassign->Lhs()->VpiName();
      if (name == "o") {
        UHDM::ExprEval eval;
        int64_t val = eval.get_value(invalidValue, rhs);
        EXPECT_EQ(val, 0b0100111100001011);
      }
    }
  }
}

TEST(Elaboration, PartSelect) {
  CompileHelper helper;
  ElaboratorHarness eharness;

  // Preprocess, Parse, Compile, Elaborate
  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  std::tie(design, fC, compileDesign) = eharness.elaborate(R"(
package my_pkg;
   function automatic logic [7:0] sbox4_8bit(logic [7:0] state_in);
      return state_in;
   endfunction : sbox4_8bit

   function automatic logic [15:0] sbox4_16bit(logic [15:0] state_in);
      logic [15:0] state_out;
      state_out[0 : 7] = sbox4_8bit(state_in[0 +: 8]);
      state_out[8 : 15] = 8'hAB;
      return state_out;
   endfunction : sbox4_16bit
endpackage // my_pkg

module top(output logic [15:0] o);
   assign o = my_pkg::sbox4_16bit(16'hAB0F);
endmodule // top
  )");
  Compiler* compiler = compileDesign->getCompiler();
  vpiHandle hdesign = compiler->getUhdmDesign();
  UHDM::design* udesign = UhdmDesignFromVpiHandle(hdesign);
  for (auto topMod : *udesign->TopModules()) {
    for (auto cassign : *topMod->Cont_assigns()) {
      UHDM::expr* rhs = (UHDM::expr*)cassign->Rhs();
      bool invalidValue = false;
      const std::string_view name = cassign->Lhs()->VpiName();
      if (name == "o") {
        UHDM::ExprEval eval;
        int64_t val = eval.get_value(invalidValue, rhs);
        EXPECT_EQ(val, 0b1010101100001111);
      }
    }
  }
}

TEST(Elaboration, IndexedPartSelect) {
  CompileHelper helper;
  ElaboratorHarness eharness;

  // Preprocess, Parse, Compile, Elaborate
  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  std::tie(design, fC, compileDesign) = eharness.elaborate(R"(
package my_pkg;
   function automatic logic [7:0] sbox4_8bit(logic [7:0] state_in);
      return state_in;
   endfunction : sbox4_8bit

   function automatic logic [15:0] sbox4_16bit(logic [15:0] state_in);
      logic [15:0] state_out;
      state_out[0 +: 8] = sbox4_8bit(state_in[0 +: 8]);
      state_out[8 +: 8] = 8'hAB;
      return state_out;
   endfunction : sbox4_16bit
endpackage // my_pkg

module top(output logic [15:0] o);
   assign o = my_pkg::sbox4_16bit(16'hAB0F);
endmodule // top
  )");
  Compiler* compiler = compileDesign->getCompiler();
  vpiHandle hdesign = compiler->getUhdmDesign();
  UHDM::design* udesign = UhdmDesignFromVpiHandle(hdesign);
  for (auto topMod : *udesign->TopModules()) {
    for (auto cassign : *topMod->Cont_assigns()) {
      UHDM::expr* rhs = (UHDM::expr*)cassign->Rhs();
      bool invalidValue = false;
      const std::string_view name = cassign->Lhs()->VpiName();
      if (name == "o") {
        UHDM::ExprEval eval;
        int64_t val = eval.get_value(invalidValue, rhs);
        EXPECT_EQ(val, 0b1010101100001111);
      }
    }
  }
}

TEST(Elaboration, ConcatPartSelect) {
  CompileHelper helper;
  ElaboratorHarness eharness;

  // Preprocess, Parse, Compile, Elaborate
  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  std::tie(design, fC, compileDesign) = eharness.elaborate(R"(
package my_pkg;
   function automatic logic [7:0] sbox4_8bit(logic [7:0] state_in);
      return state_in;
   endfunction : sbox4_8bit

   function automatic logic [15:0] sbox4_16bit(logic [15:0] state_in);
      logic [15:0] state_out;
      {state_out[15 : 8], state_out[7 : 0]} = {sbox4_8bit(state_in[0 +: 8]), sbox4_8bit(state_in[0 +: 8])};
      state_out[2] = 1'b0;
      state_out[14] = 1'b1;
      return state_out;
   endfunction : sbox4_16bit
endpackage // my_pkg

module top(output logic [15:0] o);
   assign o = my_pkg::sbox4_16bit(16'hAB0F);
  initial $display("o: %b", o);
endmodule // top
  )");
  Compiler* compiler = compileDesign->getCompiler();
  vpiHandle hdesign = compiler->getUhdmDesign();
  UHDM::design* udesign = UhdmDesignFromVpiHandle(hdesign);
  for (auto topMod : *udesign->TopModules()) {
    for (auto cassign : *topMod->Cont_assigns()) {
      UHDM::expr* rhs = (UHDM::expr*)cassign->Rhs();
      bool invalidValue = false;
      const std::string_view name = cassign->Lhs()->VpiName();
      if (name == "o") {
        UHDM::ExprEval eval;
        int64_t val = eval.get_value(invalidValue, rhs);
        EXPECT_EQ(val, 0b0100111100001011);
      }
    }
  }
}

TEST(Elaboration, StringMath1) {
  CompileHelper helper;
  ElaboratorHarness eharness;

  // Preprocess, Parse, Compile, Elaborate
  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  std::tie(design, fC, compileDesign) = eharness.elaborate(R"(
module Example();
  parameter OUTPUT = "FOO";
  function automatic [23:0] flip;
    input [23:0] inp;
    flip = ~inp;
  endfunction
  parameter DEBUG = flip(flip(OUTPUT[15:8]));
endmodule
  )");
  Compiler* compiler = compileDesign->getCompiler();
  vpiHandle hdesign = compiler->getUhdmDesign();
  UHDM::design* udesign = UhdmDesignFromVpiHandle(hdesign);
  for (auto topMod : *udesign->TopModules()) {
    for (auto passign : *topMod->Param_assigns()) {
      UHDM::expr* rhs = (UHDM::expr*)passign->Rhs();
      bool invalidValue = false;
      const std::string_view name = passign->Lhs()->VpiName();
      if (name == "DEBUG") {
        UHDM::ExprEval eval;
        int64_t val = eval.get_value(invalidValue, rhs);
        EXPECT_EQ(val, 79);
      }
    }
  }
}

TEST(Elaboration, StringMath2) {
  CompileHelper helper;
  ElaboratorHarness eharness;

  // Preprocess, Parse, Compile, Elaborate
  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  std::tie(design, fC, compileDesign) = eharness.elaborate(R"(
module dut2 #(parameter num_out_p="inv") ();
  parameter int P = num_out_p + 0;
endmodule
  )");
  Compiler* compiler = compileDesign->getCompiler();
  vpiHandle hdesign = compiler->getUhdmDesign();
  UHDM::design* udesign = UhdmDesignFromVpiHandle(hdesign);
  for (auto topMod : *udesign->TopModules()) {
    for (auto passign : *topMod->Param_assigns()) {
      UHDM::expr* rhs = (UHDM::expr*)passign->Rhs();
      bool invalidValue = false;
      const std::string_view name = passign->Lhs()->VpiName();
      if (name == "P") {
        UHDM::ExprEval eval;
        int64_t val = eval.get_value(invalidValue, rhs);
        EXPECT_EQ(val, 6909558);
      }
    }
  }
}

TEST(Elaboration, CaseStatement) {
  CompileHelper helper;
  ElaboratorHarness eharness;

  // Preprocess, Parse, Compile, Elaborate
  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  std::tie(design, fC, compileDesign) = eharness.elaborate(R"(
module GOOD();
endmodule

module top();
  parameter bit unsigned x_1b0 = 1'b0;
  parameter bit signed x_1sb0 = 1'sb0;
  parameter bit signed x_1sb1 = 1'sb1;
  parameter logic signed [1:0] x_2sb11 = 2'sb11;

  case (x_2sb11)
    x_1sb1: GOOD u2();
    default: BAD u3();
  endcase

  // Mix signed and unsigned
  case (x_2sb11)
    x_1b0:  BAD u1();
    x_1sb1: BAD u2();
    default: GOOD u3();
  endcase

  case (x_2sb11)
    x_1sb0:  BAD u1();
    x_1sb1: GOOD u2();
    default: BAD u3();
  endcase

endmodule
  )");
  Compiler* compiler = compileDesign->getCompiler();
  vpiHandle hdesign = compiler->getUhdmDesign();
  UHDM::design* udesign = UhdmDesignFromVpiHandle(hdesign);
  for (auto topMod : *udesign->TopModules()) {
    for (auto gen_array : *topMod->Gen_scope_arrays()) {
      for (auto gen_scope : *gen_array->Gen_scopes()) {
        for (auto mod : *gen_scope->Modules()) {
          EXPECT_EQ(mod->VpiDefName(), "UnitTest@GOOD");
        }
      }
    }
  }
}

TEST(Elaboration, DollarBitsArrayVar) {
  CompileHelper helper;
  ElaboratorHarness eharness;

  // Preprocess, Parse, Compile, Elaborate
  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  std::tie(design, fC, compileDesign) = eharness.elaborate(R"(
module top(output int o);
   parameter P = 1;
   logic [7:P] key [2];
   assign o = $bits(key);
endmodule
  )");
  Compiler* compiler = compileDesign->getCompiler();
  vpiHandle hdesign = compiler->getUhdmDesign();
  UHDM::design* udesign = UhdmDesignFromVpiHandle(hdesign);
  for (auto topMod : *udesign->TopModules()) {
    for (auto cassign : *topMod->Cont_assigns()) {
      UHDM::expr* rhs = (UHDM::expr*)cassign->Rhs();
      bool invalidValue = false;
      const std::string_view name = cassign->Lhs()->VpiName();
      if (name == "o") {
        UHDM::ExprEval eval;
        int64_t val = eval.get_value(invalidValue, rhs);
        EXPECT_EQ(val, 14);
      }
    }
  }
}

TEST(Elaboration, FuncImplicitSignedReturn) {
  CompileHelper helper;
  ElaboratorHarness eharness;

  // Preprocess, Parse, Compile, Elaborate
  Design* design;
  FileContent* fC;
  CompileDesign* compileDesign;
  std::tie(design, fC, compileDesign) = eharness.elaborate(R"(
module top (o);
	output int o;
	function automatic signed get1;
            get1 = 1'b1;
	endfunction
	assign o = get1();
endmodule
  )");
  Compiler* compiler = compileDesign->getCompiler();
  vpiHandle hdesign = compiler->getUhdmDesign();
  UHDM::design* udesign = UhdmDesignFromVpiHandle(hdesign);
  for (auto topMod : *udesign->TopModules()) {
    for (auto cassign : *topMod->Cont_assigns()) {
      UHDM::expr* rhs = (UHDM::expr*)cassign->Rhs();
      bool invalidValue = false;
      const std::string_view name = cassign->Lhs()->VpiName();
      if (name == "o") {
        UHDM::ExprEval eval;
        int64_t val = eval.get_value(invalidValue, rhs);
        EXPECT_EQ(val, -1);
      }
    }
  }
}

}  // namespace
}  // namespace SURELOG
