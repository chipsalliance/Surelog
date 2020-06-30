///////////////////////////////////////////////////////////////////////////////
//     Copyright (c) 1995/2018 Xilinx, Inc.
// 
//    Licensed under the Apache License, Version 2.0 (the "License");
//    you may not use this file except in compliance with the License.
//    You may obtain a copy of the License at
// 
//        http://www.apache.org/licenses/LICENSE-2.0
// 
//    Unless required by applicable law or agreed to in writing, software
//    distributed under the License is distributed on an "AS IS" BASIS,
//    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//    See the License for the specific language governing permissions and
//    limitations under the License.
///////////////////////////////////////////////////////////////////////////////
//   ____  ____
//  /   /\/   / 
// /___/  \  /     Vendor      : Xilinx 
// \   \   \/      Version     : 2019.2
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        General Clock Control Buffer
// /___/   /\      Filename    : BUFGCTRL.v
// \   \  /  \ 
//  \___\/\___\                    
//                                 
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps 

`celldefine

module BUFGCTRL #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",  
`endif
  parameter CE_TYPE_CE0 = "SYNC",
  parameter CE_TYPE_CE1 = "SYNC",
  parameter integer INIT_OUT = 0,
  parameter [0:0] IS_CE0_INVERTED = 1'b0,
  parameter [0:0] IS_CE1_INVERTED = 1'b0,
  parameter [0:0] IS_I0_INVERTED = 1'b0,
  parameter [0:0] IS_I1_INVERTED = 1'b0,
  parameter [0:0] IS_IGNORE0_INVERTED = 1'b0,
  parameter [0:0] IS_IGNORE1_INVERTED = 1'b0,
  parameter [0:0] IS_S0_INVERTED = 1'b0,
  parameter [0:0] IS_S1_INVERTED = 1'b0,
  parameter PRESELECT_I0 = "FALSE",
  parameter PRESELECT_I1 = "FALSE",
  parameter SIM_DEVICE = "ULTRASCALE",
  parameter STARTUP_SYNC = "FALSE"
)(
  output O,

  input CE0,
  input CE1,
  input I0,
  input I1,
  input IGNORE0,
  input IGNORE1,
  input S0,
  input S1
);
  
// define constants
  localparam MODULE_NAME = "BUFGCTRL";

// Parameter encodings and registers
  localparam CE_TYPE_CE0_HARDSYNC = 1;
  localparam CE_TYPE_CE0_SYNC = 0;
  localparam CE_TYPE_CE1_HARDSYNC = 1;
  localparam CE_TYPE_CE1_SYNC = 0;
  localparam PRESELECT_I0_FALSE = 0;
  localparam PRESELECT_I0_TRUE = 1;
  localparam PRESELECT_I1_FALSE = 0;
  localparam PRESELECT_I1_TRUE = 1;
  localparam SIM_DEVICE_7SERIES = 1;
  localparam SIM_DEVICE_ULTRASCALE = 0;
  localparam SIM_DEVICE_ULTRASCALE_PLUS = 2;
  localparam SIM_DEVICE_VERSAL_AI_CORE = 4;
  localparam SIM_DEVICE_VERSAL_AI_CORE_ES1 = 5;
  localparam SIM_DEVICE_VERSAL_AI_CORE_ES2 = 6;
  localparam SIM_DEVICE_VERSAL_AI_EDGE = 7;
  localparam SIM_DEVICE_VERSAL_AI_EDGE_ES1 = 8;
  localparam SIM_DEVICE_VERSAL_AI_EDGE_ES2 = 9;
  localparam SIM_DEVICE_VERSAL_AI_RF = 10;
  localparam SIM_DEVICE_VERSAL_AI_RF_ES1 = 11;
  localparam SIM_DEVICE_VERSAL_AI_RF_ES2 = 12;
  localparam SIM_DEVICE_VERSAL_HBM = 15;
  localparam SIM_DEVICE_VERSAL_HBM_ES1 = 16;
  localparam SIM_DEVICE_VERSAL_HBM_ES2 = 17;
  localparam SIM_DEVICE_VERSAL_PREMIUM = 18;
  localparam SIM_DEVICE_VERSAL_PREMIUM_ES1 = 19;
  localparam SIM_DEVICE_VERSAL_PREMIUM_ES2 = 20;
  localparam SIM_DEVICE_VERSAL_PRIME = 21;
  localparam SIM_DEVICE_VERSAL_PRIME_ES1 = 22;
  localparam SIM_DEVICE_VERSAL_PRIME_ES2 = 23;
  localparam STARTUP_SYNC_FALSE = 0;
  localparam STARTUP_SYNC_TRUE = 1;

  reg trig_attr;
// include dynamic registers - XILINX test only
`ifdef XIL_DR
  `include "BUFGCTRL_dr.v"
`else
  reg [64:1] CE_TYPE_CE0_REG = CE_TYPE_CE0;
  reg [64:1] CE_TYPE_CE1_REG = CE_TYPE_CE1;
  reg [31:0] INIT_OUT_REG = INIT_OUT;
  reg [0:0] IS_CE0_INVERTED_REG = IS_CE0_INVERTED;
  reg [0:0] IS_CE1_INVERTED_REG = IS_CE1_INVERTED;
  reg [0:0] IS_I0_INVERTED_REG = IS_I0_INVERTED;
  reg [0:0] IS_I1_INVERTED_REG = IS_I1_INVERTED;
  reg [0:0] IS_IGNORE0_INVERTED_REG = IS_IGNORE0_INVERTED;
  reg [0:0] IS_IGNORE1_INVERTED_REG = IS_IGNORE1_INVERTED;
  reg [0:0] IS_S0_INVERTED_REG = IS_S0_INVERTED;
  reg [0:0] IS_S1_INVERTED_REG = IS_S1_INVERTED;
  reg [40:1] PRESELECT_I0_REG = PRESELECT_I0;
  reg [40:1] PRESELECT_I1_REG = PRESELECT_I1;
  reg [144:1] SIM_DEVICE_REG = SIM_DEVICE;
  reg [40:1] STARTUP_SYNC_REG = STARTUP_SYNC;
`endif

`ifdef XIL_XECLIB
  wire CE_TYPE_CE0_BIN;
  wire CE_TYPE_CE1_BIN;
  wire INIT_OUT_BIN;
  wire PRESELECT_I0_BIN;
  wire PRESELECT_I1_BIN;
  wire [4:0] SIM_DEVICE_BIN;
  wire STARTUP_SYNC_BIN;
`else
  reg CE_TYPE_CE0_BIN;
  reg CE_TYPE_CE1_BIN;
  reg INIT_OUT_BIN;
  reg PRESELECT_I0_BIN;
  reg PRESELECT_I1_BIN;
  reg [4:0] SIM_DEVICE_BIN;
  reg STARTUP_SYNC_BIN;
`endif

`ifdef XIL_XECLIB
  reg glblGSR = 1'b0;
  reg glblGRESTORE = 1'b0;
`else
  tri0 glblGSR = glbl.GSR;
  tri0 glblGRESTORE = glbl.GRESTORE;
`endif

  wire CE0_in;
  wire CE1_in;
  wire I0_in;
  wire I1_in;
  wire IGNORE0_in;
  wire IGNORE1_in;
  wire S0_in;
  wire S1_in;

`ifdef XIL_TIMING
  wire CE0_delay;
  wire CE1_delay;
  wire I0_delay;
  wire I1_delay;
  wire S0_delay;
  wire S1_delay;
`endif

`ifdef XIL_TIMING
  assign CE0_in = (CE0 !== 1'bz) && (CE0_delay ^ IS_CE0_INVERTED_REG); // rv 0
  assign CE1_in = (CE1 !== 1'bz) && (CE1_delay ^ IS_CE1_INVERTED_REG); // rv 0
  assign I0_in = I0_delay ^ IS_I0_INVERTED_REG;
  assign I1_in = I1_delay ^ IS_I1_INVERTED_REG;
  assign S0_in = (S0 !== 1'bz) && (S0_delay ^ IS_S0_INVERTED_REG); // rv 0
  assign S1_in = (S1 !== 1'bz) && (S1_delay ^ IS_S1_INVERTED_REG); // rv 0
`else
  assign CE0_in = (CE0 !== 1'bz) && (CE0 ^ IS_CE0_INVERTED_REG); // rv 0
  assign CE1_in = (CE1 !== 1'bz) && (CE1 ^ IS_CE1_INVERTED_REG); // rv 0
  assign I0_in = I0 ^ IS_I0_INVERTED_REG;
  assign I1_in = I1 ^ IS_I1_INVERTED_REG;
  assign S0_in = (S0 !== 1'bz) && (S0 ^ IS_S0_INVERTED_REG); // rv 0
  assign S1_in = (S1 !== 1'bz) && (S1 ^ IS_S1_INVERTED_REG); // rv 0
`endif

  assign IGNORE0_in = (IGNORE0 !== 1'bz) && (IGNORE0 ^ IS_IGNORE0_INVERTED_REG); // rv 0
  assign IGNORE1_in = (IGNORE1 !== 1'bz) && (IGNORE1 ^ IS_IGNORE1_INVERTED_REG); // rv 0

`ifndef XIL_XECLIB
  reg attr_test;
  reg attr_err;
  
  initial begin
    trig_attr = 1'b0;
  `ifdef XIL_ATTR_TEST
    attr_test = 1'b1;
  `else
    attr_test = 1'b0;
  `endif
    attr_err = 1'b0;
    #1;
    trig_attr = ~trig_attr;
  end
`endif

`ifdef XIL_XECLIB
  assign CE_TYPE_CE0_BIN =
      (CE_TYPE_CE0_REG == "SYNC") ? CE_TYPE_CE0_SYNC :
      (CE_TYPE_CE0_REG == "HARDSYNC") ? CE_TYPE_CE0_HARDSYNC :
       CE_TYPE_CE0_SYNC;
  
  assign CE_TYPE_CE1_BIN =
      (CE_TYPE_CE1_REG == "SYNC") ? CE_TYPE_CE1_SYNC :
      (CE_TYPE_CE1_REG == "HARDSYNC") ? CE_TYPE_CE1_HARDSYNC :
       CE_TYPE_CE1_SYNC;
  
  assign INIT_OUT_BIN = INIT_OUT_REG[0];

  assign PRESELECT_I0_BIN =
    (PRESELECT_I0_REG == "FALSE") ? PRESELECT_I0_FALSE :
    (PRESELECT_I0_REG == "TRUE")  ? PRESELECT_I0_TRUE  :
    PRESELECT_I0_FALSE;

  assign PRESELECT_I1_BIN =
    (PRESELECT_I1_REG == "FALSE") ? PRESELECT_I1_FALSE :
    (PRESELECT_I1_REG == "TRUE")  ? PRESELECT_I1_TRUE  :
    PRESELECT_I1_FALSE;

  assign SIM_DEVICE_BIN =
      (SIM_DEVICE_REG == "ULTRASCALE") ? SIM_DEVICE_ULTRASCALE :
      (SIM_DEVICE_REG == "7SERIES") ? SIM_DEVICE_7SERIES :
      (SIM_DEVICE_REG == "ULTRASCALE_PLUS") ? SIM_DEVICE_ULTRASCALE_PLUS :
      (SIM_DEVICE_REG == "VERSAL_AI_CORE") ? SIM_DEVICE_VERSAL_AI_CORE :
      (SIM_DEVICE_REG == "VERSAL_AI_CORE_ES1") ? SIM_DEVICE_VERSAL_AI_CORE_ES1 :
      (SIM_DEVICE_REG == "VERSAL_AI_CORE_ES2") ? SIM_DEVICE_VERSAL_AI_CORE_ES2 :
      (SIM_DEVICE_REG == "VERSAL_AI_EDGE") ? SIM_DEVICE_VERSAL_AI_EDGE :
      (SIM_DEVICE_REG == "VERSAL_AI_EDGE_ES1") ? SIM_DEVICE_VERSAL_AI_EDGE_ES1 :
      (SIM_DEVICE_REG == "VERSAL_AI_EDGE_ES2") ? SIM_DEVICE_VERSAL_AI_EDGE_ES2 :
      (SIM_DEVICE_REG == "VERSAL_AI_RF") ? SIM_DEVICE_VERSAL_AI_RF :
      (SIM_DEVICE_REG == "VERSAL_AI_RF_ES1") ? SIM_DEVICE_VERSAL_AI_RF_ES1 :
      (SIM_DEVICE_REG == "VERSAL_AI_RF_ES2") ? SIM_DEVICE_VERSAL_AI_RF_ES2 :
      (SIM_DEVICE_REG == "VERSAL_HBM") ? SIM_DEVICE_VERSAL_HBM :
      (SIM_DEVICE_REG == "VERSAL_HBM_ES1") ? SIM_DEVICE_VERSAL_HBM_ES1 :
      (SIM_DEVICE_REG == "VERSAL_HBM_ES2") ? SIM_DEVICE_VERSAL_HBM_ES2 :
      (SIM_DEVICE_REG == "VERSAL_PREMIUM") ? SIM_DEVICE_VERSAL_PREMIUM :
      (SIM_DEVICE_REG == "VERSAL_PREMIUM_ES1") ? SIM_DEVICE_VERSAL_PREMIUM_ES1 :
      (SIM_DEVICE_REG == "VERSAL_PREMIUM_ES2") ? SIM_DEVICE_VERSAL_PREMIUM_ES2 :
      (SIM_DEVICE_REG == "VERSAL_PRIME") ? SIM_DEVICE_VERSAL_PRIME :
      (SIM_DEVICE_REG == "VERSAL_PRIME_ES1") ? SIM_DEVICE_VERSAL_PRIME_ES1 :
      (SIM_DEVICE_REG == "VERSAL_PRIME_ES2") ? SIM_DEVICE_VERSAL_PRIME_ES2 :
       SIM_DEVICE_ULTRASCALE;
  
  assign STARTUP_SYNC_BIN =
      (STARTUP_SYNC_REG == "FALSE") ? STARTUP_SYNC_FALSE :
      (STARTUP_SYNC_REG == "TRUE") ? STARTUP_SYNC_TRUE :
       STARTUP_SYNC_FALSE;
  
`else
  always @ (trig_attr) begin
  #1;
  CE_TYPE_CE0_BIN =
      (CE_TYPE_CE0_REG == "SYNC") ? CE_TYPE_CE0_SYNC :
      (CE_TYPE_CE0_REG == "HARDSYNC") ? CE_TYPE_CE0_HARDSYNC :
       CE_TYPE_CE0_SYNC;
  
  CE_TYPE_CE1_BIN =
      (CE_TYPE_CE1_REG == "SYNC") ? CE_TYPE_CE1_SYNC :
      (CE_TYPE_CE1_REG == "HARDSYNC") ? CE_TYPE_CE1_HARDSYNC :
       CE_TYPE_CE1_SYNC;
  
  INIT_OUT_BIN = INIT_OUT_REG[0];
  
  PRESELECT_I0_BIN =
      (PRESELECT_I0_REG == "FALSE") ? PRESELECT_I0_FALSE :
      (PRESELECT_I0_REG == "TRUE")  ? PRESELECT_I0_TRUE  :
       PRESELECT_I0_FALSE;

  PRESELECT_I1_BIN =
      (PRESELECT_I1_REG == "FALSE") ? PRESELECT_I1_FALSE :
      (PRESELECT_I1_REG == "TRUE")  ? PRESELECT_I1_TRUE  :
       PRESELECT_I1_FALSE;

  SIM_DEVICE_BIN =
      (SIM_DEVICE_REG == "ULTRASCALE") ? SIM_DEVICE_ULTRASCALE :
      (SIM_DEVICE_REG == "7SERIES") ? SIM_DEVICE_7SERIES :
      (SIM_DEVICE_REG == "ULTRASCALE_PLUS") ? SIM_DEVICE_ULTRASCALE_PLUS :
      (SIM_DEVICE_REG == "VERSAL_AI_CORE") ? SIM_DEVICE_VERSAL_AI_CORE :
      (SIM_DEVICE_REG == "VERSAL_AI_CORE_ES1") ? SIM_DEVICE_VERSAL_AI_CORE_ES1 :
      (SIM_DEVICE_REG == "VERSAL_AI_CORE_ES2") ? SIM_DEVICE_VERSAL_AI_CORE_ES2 :
      (SIM_DEVICE_REG == "VERSAL_AI_EDGE") ? SIM_DEVICE_VERSAL_AI_EDGE :
      (SIM_DEVICE_REG == "VERSAL_AI_EDGE_ES1") ? SIM_DEVICE_VERSAL_AI_EDGE_ES1 :
      (SIM_DEVICE_REG == "VERSAL_AI_EDGE_ES2") ? SIM_DEVICE_VERSAL_AI_EDGE_ES2 :
      (SIM_DEVICE_REG == "VERSAL_AI_RF") ? SIM_DEVICE_VERSAL_AI_RF :
      (SIM_DEVICE_REG == "VERSAL_AI_RF_ES1") ? SIM_DEVICE_VERSAL_AI_RF_ES1 :
      (SIM_DEVICE_REG == "VERSAL_AI_RF_ES2") ? SIM_DEVICE_VERSAL_AI_RF_ES2 :
      (SIM_DEVICE_REG == "VERSAL_HBM") ? SIM_DEVICE_VERSAL_HBM :
      (SIM_DEVICE_REG == "VERSAL_HBM_ES1") ? SIM_DEVICE_VERSAL_HBM_ES1 :
      (SIM_DEVICE_REG == "VERSAL_HBM_ES2") ? SIM_DEVICE_VERSAL_HBM_ES2 :
      (SIM_DEVICE_REG == "VERSAL_PREMIUM") ? SIM_DEVICE_VERSAL_PREMIUM :
      (SIM_DEVICE_REG == "VERSAL_PREMIUM_ES1") ? SIM_DEVICE_VERSAL_PREMIUM_ES1 :
      (SIM_DEVICE_REG == "VERSAL_PREMIUM_ES2") ? SIM_DEVICE_VERSAL_PREMIUM_ES2 :
      (SIM_DEVICE_REG == "VERSAL_PRIME") ? SIM_DEVICE_VERSAL_PRIME :
      (SIM_DEVICE_REG == "VERSAL_PRIME_ES1") ? SIM_DEVICE_VERSAL_PRIME_ES1 :
      (SIM_DEVICE_REG == "VERSAL_PRIME_ES2") ? SIM_DEVICE_VERSAL_PRIME_ES2 :
       SIM_DEVICE_ULTRASCALE;
  
  STARTUP_SYNC_BIN =
      (STARTUP_SYNC_REG == "FALSE") ? STARTUP_SYNC_FALSE :
      (STARTUP_SYNC_REG == "TRUE") ? STARTUP_SYNC_TRUE :
       STARTUP_SYNC_FALSE;
  
  end
`endif

`ifndef XIL_XECLIB
  always @ (trig_attr) begin
    #1;
    if ((attr_test == 1'b1) ||
        ((CE_TYPE_CE0_REG != "SYNC") &&
         (CE_TYPE_CE0_REG != "HARDSYNC"))) begin
      $display("Error: [Unisim %s-101] CE_TYPE_CE0 attribute is set to %s.  Legal values for this attribute are SYNC or HARDSYNC. Instance: %m", MODULE_NAME, CE_TYPE_CE0_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((CE_TYPE_CE1_REG != "SYNC") &&
         (CE_TYPE_CE1_REG != "HARDSYNC"))) begin
      $display("Error: [Unisim %s-102] CE_TYPE_CE1 attribute is set to %s.  Legal values for this attribute are SYNC or HARDSYNC. Instance: %m", MODULE_NAME, CE_TYPE_CE1_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((INIT_OUT_REG != 0) &&
         (INIT_OUT_REG != 1))) begin
      $display("Error: [Unisim %s-104] INIT_OUT attribute is set to %d.  Legal values for this attribute are 0 or 1. Instance: %m", MODULE_NAME, INIT_OUT_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((PRESELECT_I0_REG != "FALSE") &&
         (PRESELECT_I0_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-113] PRESELECT_I0 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PRESELECT_I0_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((PRESELECT_I1_REG != "FALSE") &&
         (PRESELECT_I1_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-114] PRESELECT_I1 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PRESELECT_I1_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((SIM_DEVICE_REG != "ULTRASCALE") &&
         (SIM_DEVICE_REG != "7SERIES") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS") &&
         (SIM_DEVICE_REG != "VERSAL_AI_CORE") &&
         (SIM_DEVICE_REG != "VERSAL_AI_CORE_ES1") &&
         (SIM_DEVICE_REG != "VERSAL_AI_CORE_ES2") &&
         (SIM_DEVICE_REG != "VERSAL_AI_EDGE") &&
         (SIM_DEVICE_REG != "VERSAL_AI_EDGE_ES1") &&
         (SIM_DEVICE_REG != "VERSAL_AI_EDGE_ES2") &&
         (SIM_DEVICE_REG != "VERSAL_AI_RF") &&
         (SIM_DEVICE_REG != "VERSAL_AI_RF_ES1") &&
         (SIM_DEVICE_REG != "VERSAL_AI_RF_ES2") &&
         (SIM_DEVICE_REG != "VERSAL_HBM") &&
         (SIM_DEVICE_REG != "VERSAL_HBM_ES1") &&
         (SIM_DEVICE_REG != "VERSAL_HBM_ES2") &&
         (SIM_DEVICE_REG != "VERSAL_PREMIUM") &&
         (SIM_DEVICE_REG != "VERSAL_PREMIUM_ES1") &&
         (SIM_DEVICE_REG != "VERSAL_PREMIUM_ES2") &&
         (SIM_DEVICE_REG != "VERSAL_PRIME") &&
         (SIM_DEVICE_REG != "VERSAL_PRIME_ES1") &&
         (SIM_DEVICE_REG != "VERSAL_PRIME_ES2"))) begin
      $display("Error: [Unisim %s-115] SIM_DEVICE attribute is set to %s.  Legal values for this attribute are ULTRASCALE, 7SERIES, ULTRASCALE_PLUS, VERSAL_AI_CORE, VERSAL_AI_CORE_ES1, VERSAL_AI_CORE_ES2, VERSAL_AI_EDGE, VERSAL_AI_EDGE_ES1, VERSAL_AI_EDGE_ES2, VERSAL_AI_RF, VERSAL_AI_RF_ES1, VERSAL_AI_RF_ES2, VERSAL_HBM, VERSAL_HBM_ES1, VERSAL_HBM_ES2, VERSAL_PREMIUM, VERSAL_PREMIUM_ES1, VERSAL_PREMIUM_ES2, VERSAL_PRIME, VERSAL_PRIME_ES1 or VERSAL_PRIME_ES2. Instance: %m", MODULE_NAME, SIM_DEVICE_REG);
      attr_err = 1'b1;
   end

    if ((attr_test == 1'b1) ||
        ((STARTUP_SYNC_REG != "FALSE") &&
         (STARTUP_SYNC_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-116] STARTUP_SYNC attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, STARTUP_SYNC_REG);
      attr_err = 1'b1;
    end
    
  if (attr_err == 1'b1) #1 $finish;
  end
`endif

`ifdef XIL_TIMING
  reg notifier;
`endif

// begin behavioral model

  reg O_out;


`ifndef XIL_XECLIB
  always @ (trig_attr) begin
    #1;

// *** both preselects can not be 1 simultaneously.
    if ((PRESELECT_I0_REG == "TRUE") && (PRESELECT_I1_REG == "TRUE")) begin
      $display("Error : [Unisim %s-1] The attributes PRESELECT_I0 and PRESELECT_I1 should not be set to TRUE simultaneously. Instance: %m", MODULE_NAME);
      attr_err = 1'b1;
    end

  if (attr_err == 1'b1) #1 $finish;
  end

  always @ (trig_attr) begin
    #1;
    if (((SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_CORE      ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_CORE_ES1  ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_CORE_ES2  ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_EDGE      ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_EDGE_ES1  ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_EDGE_ES2  ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_RF        ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_RF_ES1    ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_RF_ES2    ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_HBM          ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_HBM_ES1      ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_HBM_ES2      ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_PREMIUM      ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_PREMIUM_ES1  ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_PREMIUM_ES2  ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_PRIME        ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_PRIME_ES1    ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_PRIME_ES2    )) &&
        (STARTUP_SYNC_BIN == STARTUP_SYNC_TRUE)) begin
        $display("Warning: [Unisim %s-200] SIM_DEVICE attribute is set to %s and STARTUP_SYNC is set to %s. STARTUP_SYNC functionality is not supported for this DEVICE. Instance: %m", MODULE_NAME, SIM_DEVICE_REG, STARTUP_SYNC_REG);
        STARTUP_SYNC_BIN = STARTUP_SYNC_FALSE; //force correct
      end

    if (((SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_CORE      ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_CORE_ES1  ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_CORE_ES2  ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_EDGE      ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_EDGE_ES1  ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_EDGE_ES2  ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_RF        ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_RF_ES1    ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_RF_ES2    ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_HBM          ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_HBM_ES1      ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_HBM_ES2      ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_PREMIUM      ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_PREMIUM_ES1  ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_PREMIUM_ES2  ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_PRIME        ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_PRIME_ES1    ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_PRIME_ES2    )) &&
        (CE_TYPE_CE0_BIN == CE_TYPE_CE0_HARDSYNC || CE_TYPE_CE1_BIN==CE_TYPE_CE1_HARDSYNC)) begin
        $display("Warning: [Unisim %s-201] SIM_DEVICE attribute is set to %s; CE_TYPE_CE0 is set to %s and CE_TYPE_CE1 is set to %s. HARDSYNC functionality is not supported for this DEVICE. Instance: %m", MODULE_NAME, SIM_DEVICE_REG, CE_TYPE_CE0_REG, CE_TYPE_CE1_REG);
        CE_TYPE_CE0_BIN = CE_TYPE_CE0_SYNC; //force correct
        CE_TYPE_CE1_BIN = CE_TYPE_CE1_SYNC;
      end
  end //always

`endif


  reg [2:0] gwe0_sync;
  reg [2:0] gwe1_sync;
  wire      gwe_sync;
  wire      gwe;
  wire      gwe_muxed_sync;
  reg [2:0] CE0_sync;
  reg [2:0] CE1_sync;
  wire      ce0_muxed_sync;
  wire      ce1_muxed_sync;
  reg       CE0_in_dly;
  reg       CE1_in_dly;
  wire      I0_optinv;
  wire      I1_optinv;
  wire      d00;   
  wire      d01;   
  wire      d10;   
  wire      d11;
  reg       qb00;   
  reg       qb01;   
  reg       qb10;   
  reg       qb11;
  wire      cb00;   
  wire      cb01;   
  wire      cb10;   
  wire      cb11;
  reg       state0;
  reg       state1;

  initial begin
    CE0_sync   = 3'b000;
    CE1_sync   = 3'b000;
    gwe0_sync  = 3'b000;
    gwe1_sync  = 3'b000;
    O_out     = 1'b0;

    #2;
    qb00       = (PRESELECT_I0_BIN==PRESELECT_I0_TRUE)? 1'b1:1'b0;
    qb01       = (PRESELECT_I0_BIN==PRESELECT_I0_TRUE)? 1'b1:1'b0;
    qb10       = (PRESELECT_I1_BIN==PRESELECT_I1_TRUE)? 1'b1:1'b0;
    qb11       = (PRESELECT_I1_BIN==PRESELECT_I1_TRUE)? 1'b1:1'b0;
    //don't put anything after here
  end

  assign gwe = ~glblGSR;

  assign I0_optinv = INIT_OUT_BIN ^ I0_in;
  assign I1_optinv = INIT_OUT_BIN ^ I1_in;

  always @ (negedge I0_optinv or posedge glblGRESTORE) begin
    if(glblGRESTORE)
      gwe0_sync <= 3'd0;
    else 
      gwe0_sync <= {gwe0_sync[1:0], gwe};
    end

  always @ (negedge I1_optinv or posedge glblGRESTORE) begin 
    if(glblGRESTORE)
      gwe1_sync <= 3'd0;
    else 
      gwe1_sync <= {gwe1_sync[1:0], gwe};
  end

  assign gwe_sync = ((PRESELECT_I0_BIN==PRESELECT_I0_TRUE ) ? gwe0_sync[2] :
                     (PRESELECT_I1_BIN==PRESELECT_I1_TRUE ) ? gwe1_sync[2] : 
                     (gwe0_sync[2] | gwe1_sync[2]));
  assign gwe_muxed_sync = (STARTUP_SYNC_BIN==STARTUP_SYNC_TRUE) ? gwe_sync : gwe;

  always @(*) CE0_in_dly    = #1 CE0_in;
  always @(*) CE1_in_dly    = #1 CE1_in;
  
  always @ (posedge I0_optinv or posedge glblGRESTORE) 
    if(glblGRESTORE)
      CE0_sync <= 3'd0;
    else 
      CE0_sync <= {CE0_sync[1:0], CE0_in_dly};

  always @ (posedge I1_optinv or posedge glblGRESTORE) 
    if(glblGRESTORE)
      CE1_sync <= 3'd0;
    else 
      CE1_sync <= {CE1_sync[1:0], CE1_in_dly};


  assign ce0_muxed_sync = (CE_TYPE_CE0_BIN==CE_TYPE_CE0_HARDSYNC) ? CE0_sync[2] : CE0_in;
  assign ce1_muxed_sync = (CE_TYPE_CE1_BIN==CE_TYPE_CE1_HARDSYNC) ? CE1_sync[2] : CE1_in;

  assign d00 = ~(state1 & S0_in);
  assign d01 = ~(qb00 & ce0_muxed_sync);
  assign d10 = ~(state0 & S1_in);
  assign d11 = ~(qb10 & ce1_muxed_sync);

  assign cb00 = ~( (~gwe_muxed_sync) | (~IGNORE0_in) & (~I0_optinv) );
  assign cb01 = ~( (~gwe_muxed_sync) | (~IGNORE0_in) & ( I0_optinv) );
  assign cb10 = ~( (~gwe_muxed_sync) | (~IGNORE1_in) & (~I1_optinv) );
  assign cb11 = ~( (~gwe_muxed_sync) | (~IGNORE1_in) & ( I1_optinv) );
 
  always@(*) begin
    if (glblGRESTORE && ~PRESELECT_I0_BIN)
      qb00 <= 1'b0;
    else if (glblGRESTORE && PRESELECT_I0_BIN)
      qb00 <= 1'b1;
    else if(cb00)
      qb00 <= #1 ~d00;
    end

  always@(*) begin
    if (glblGRESTORE && ~PRESELECT_I0_BIN)
      qb01 <= 1'b0;
    else if (glblGRESTORE && PRESELECT_I0_BIN)
      qb01 <= 1'b1;
    else if(cb01)
      qb01 <= #1 ~d01;
  end

  always @(*) begin
    if (glblGRESTORE && ~PRESELECT_I1_BIN)
      qb10 <= 1'b0;
    else if (glblGRESTORE && PRESELECT_I1_BIN)
      qb10 <= 1'b1;
    else if(cb10)
      qb10 <= #1 ~d10;
    end

  always@(*) begin
    if (glblGRESTORE && ~PRESELECT_I1_BIN)
      qb11 <= 1'b0;
    else if (glblGRESTORE && PRESELECT_I1_BIN)
      qb11 <= 1'b1;
    else if(cb11)
      qb11 <= #1 ~d11;
  end
  
  always@(*) begin
    state0 =  ~(qb01|(~gwe_muxed_sync));
    state1 =  ~(qb11|(~gwe_muxed_sync));
  end

  always @(*) begin
    case ({state1,state0})
      2'b00   : O_out = 1'b0;
      2'b01   : O_out = I1_in;
      2'b10   : O_out = I0_in;
      2'b11   : O_out = INIT_OUT_BIN;
      default : O_out = 1'bx;  
    endcase
  end

  assign O = O_out;

// end behavioral model

`ifndef XIL_XECLIB
`ifdef XIL_TIMING

  wire i0_en_n;
  wire i0_en_p;
  wire i1_en_n;
  wire i1_en_p;

  assign i0_en_n = IS_I0_INVERTED_REG;
  assign i0_en_p = ~IS_I0_INVERTED_REG;
  assign i1_en_n = IS_I1_INVERTED_REG;
  assign i1_en_p = ~IS_I1_INVERTED_REG;

`endif

// I0/I1 are clocks but do not clock anything in this model. do not need the 100 ps.
// specify absorbs a potential glitch in functional simuation when S0/S1 switch
// that needs to remain to match rtl.
// IO paths are combinatorial through muxes and not registers
`ifdef XIL_TIMING
  specify
    (CE0 => O) = (0:0:0, 0:0:0);
    (CE1 => O) = (0:0:0, 0:0:0);
    (I0 => O) = (0:0:0, 0:0:0);
    (I1 => O) = (0:0:0, 0:0:0);
    $period (negedge I0, 0:0:0, notifier);
    $period (negedge I1, 0:0:0, notifier);
    $period (posedge I0, 0:0:0, notifier);
    $period (posedge I1, 0:0:0, notifier);
    $setuphold (negedge I0, negedge CE0, 0:0:0, 0:0:0, notifier,i0_en_n,i0_en_n, I0_delay, CE0_delay);
    $setuphold (negedge I0, negedge S0, 0:0:0, 0:0:0, notifier,i0_en_n,i0_en_n, I0_delay, S0_delay);
    $setuphold (negedge I0, posedge CE0, 0:0:0, 0:0:0, notifier,i0_en_n,i0_en_n, I0_delay, CE0_delay);
    $setuphold (negedge I0, posedge S0, 0:0:0, 0:0:0, notifier,i0_en_n,i0_en_n, I0_delay, S0_delay);
    $setuphold (negedge I1, negedge CE1, 0:0:0, 0:0:0, notifier,i1_en_n,i1_en_n, I1_delay, CE1_delay);
    $setuphold (negedge I1, negedge S1, 0:0:0, 0:0:0, notifier,i1_en_n,i1_en_n, I1_delay, S1_delay);
    $setuphold (negedge I1, posedge CE1, 0:0:0, 0:0:0, notifier,i1_en_n,i1_en_n, I1_delay, CE1_delay);
    $setuphold (negedge I1, posedge S1, 0:0:0, 0:0:0, notifier,i1_en_n,i1_en_n, I1_delay, S1_delay);
    $setuphold (posedge I0, negedge CE0, 0:0:0, 0:0:0, notifier,i0_en_p,i0_en_p, I0_delay, CE0_delay);
    $setuphold (posedge I0, negedge S0, 0:0:0, 0:0:0, notifier,i0_en_p,i0_en_p, I0_delay, S0_delay);
    $setuphold (posedge I0, posedge CE0, 0:0:0, 0:0:0, notifier,i0_en_p,i0_en_p, I0_delay, CE0_delay);
    $setuphold (posedge I0, posedge S0, 0:0:0, 0:0:0, notifier,i0_en_p,i0_en_p, I0_delay, S0_delay);
    $setuphold (posedge I1, negedge CE1, 0:0:0, 0:0:0, notifier,i1_en_p,i1_en_p, I1_delay, CE1_delay);
    $setuphold (posedge I1, negedge S1, 0:0:0, 0:0:0, notifier,i1_en_p,i1_en_p, I1_delay, S1_delay);
    $setuphold (posedge I1, posedge CE1, 0:0:0, 0:0:0, notifier,i1_en_p,i1_en_p, I1_delay, CE1_delay);
    $setuphold (posedge I1, posedge S1, 0:0:0, 0:0:0, notifier,i1_en_p,i1_en_p, I1_delay, S1_delay);
    specparam PATHPULSE$ = 0;
  endspecify
`endif
`endif

endmodule

`endcelldefine
