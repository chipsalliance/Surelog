///////////////////////////////////////////////////////////////////////////////
//     Copyright (c) 1995/2017 Xilinx, Inc.
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
// \   \   \/      Version     : 2018.1
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        HBM_SNGLBLI_INTF_APB
// /___/   /\      Filename    : HBM_SNGLBLI_INTF_APB.v
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

module HBM_SNGLBLI_INTF_APB #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter CLK_SEL = "FALSE",
  parameter [0:0] IS_PCLK_INVERTED = 1'b0,
  parameter [0:0] IS_PRESET_N_INVERTED = 1'b0,
  parameter MC_ENABLE = "FALSE",
  parameter PHY_ENABLE = "FALSE",
  parameter PHY_PCLK_INVERT = "FALSE",
  parameter SWITCH_ENABLE = "FALSE"
)(
  output CATTRIP_PIPE,
  output [31:0] PRDATA_PIPE,
  output PREADY_PIPE,
  output PSLVERR_PIPE,
  output [2:0] TEMP_PIPE,

  input [21:0] PADDR,
  input PCLK,
  input PENABLE,
  input PRESET_N,
  input PSEL,
  input [31:0] PWDATA,
  input PWRITE
);

// define constants
  localparam MODULE_NAME = "HBM_SNGLBLI_INTF_APB";
  
// Parameter encodings and registers
  localparam CLK_SEL_FALSE = 0;
  localparam CLK_SEL_TRUE = 1;
  localparam MC_ENABLE_FALSE = 0;
  localparam MC_ENABLE_TRUE = 1;
  localparam PHY_ENABLE_FALSE = 0;
  localparam PHY_ENABLE_TRUE = 1;
  localparam SWITCH_ENABLE_FALSE = 0;
  localparam SWITCH_ENABLE_TRUE = 1;

  reg trig_attr;
// include dynamic registers - XILINX test only
`ifdef XIL_DR
  `include "HBM_SNGLBLI_INTF_APB_dr.v"
`else
  localparam [40:1] CLK_SEL_REG = CLK_SEL;
  localparam [0:0] IS_PCLK_INVERTED_REG = IS_PCLK_INVERTED;
  localparam [0:0] IS_PRESET_N_INVERTED_REG = IS_PRESET_N_INVERTED;
  localparam [40:1] MC_ENABLE_REG = MC_ENABLE;
  localparam [40:1] PHY_ENABLE_REG = PHY_ENABLE;
  localparam [40:1] PHY_PCLK_INVERT_REG = PHY_PCLK_INVERT;
  localparam [40:1] SWITCH_ENABLE_REG = SWITCH_ENABLE;
`endif

`ifdef XIL_XECLIB
  wire CLK_SEL_BIN;
  wire MC_ENABLE_BIN;
  wire PHY_ENABLE_BIN;
  wire SWITCH_ENABLE_BIN;
`else
  reg CLK_SEL_BIN;
  reg MC_ENABLE_BIN;
  reg PHY_ENABLE_BIN;
  reg SWITCH_ENABLE_BIN;
`endif

  reg attr_test;
  reg attr_err;
  tri0 glblGSR = glbl.GSR;

  wire PCLK_in;
  wire PENABLE_in;
  wire PRESET_N_in;
  wire PSEL_in;
  wire PWRITE_in;
  wire [21:0] PADDR_in;
  wire [31:0] PWDATA_in;

`ifdef XIL_TIMING
  wire PCLK_delay;
  wire PENABLE_delay;
  wire PRESET_N_delay;
  wire PSEL_delay;
  wire PWRITE_delay;
  wire [21:0] PADDR_delay;
  wire [31:0] PWDATA_delay;
`endif

`ifdef XIL_TIMING
  assign PADDR_in = PADDR_delay;
  assign PCLK_in = PCLK_delay;
  assign PENABLE_in = PENABLE_delay;
  assign PRESET_N_in = PRESET_N_delay;
  assign PSEL_in = PSEL_delay;
  assign PWDATA_in = PWDATA_delay;
  assign PWRITE_in = PWRITE_delay;
`else
  assign PADDR_in = PADDR;
  assign PCLK_in = PCLK;
  assign PENABLE_in = PENABLE;
  assign PRESET_N_in = PRESET_N;
  assign PSEL_in = PSEL;
  assign PWDATA_in = PWDATA;
  assign PWRITE_in = PWRITE;
`endif

`ifndef XIL_XECLIB
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
  assign CLK_SEL_BIN =
      (CLK_SEL_REG == "FALSE") ? CLK_SEL_FALSE :
      (CLK_SEL_REG == "TRUE") ? CLK_SEL_TRUE :
       CLK_SEL_FALSE;
  
  assign MC_ENABLE_BIN =
      (MC_ENABLE_REG == "FALSE") ? MC_ENABLE_FALSE :
      (MC_ENABLE_REG == "TRUE") ? MC_ENABLE_TRUE :
       MC_ENABLE_FALSE;
  
  assign PHY_ENABLE_BIN =
      (PHY_ENABLE_REG == "FALSE") ? PHY_ENABLE_FALSE :
      (PHY_ENABLE_REG == "TRUE") ? PHY_ENABLE_TRUE :
       PHY_ENABLE_FALSE;
  
  assign SWITCH_ENABLE_BIN =
      (SWITCH_ENABLE_REG == "FALSE") ? SWITCH_ENABLE_FALSE :
      (SWITCH_ENABLE_REG == "TRUE") ? SWITCH_ENABLE_TRUE :
       SWITCH_ENABLE_FALSE;
  
`else
  always @ (trig_attr) begin
  #1;
  CLK_SEL_BIN =
      (CLK_SEL_REG == "FALSE") ? CLK_SEL_FALSE :
      (CLK_SEL_REG == "TRUE") ? CLK_SEL_TRUE :
       CLK_SEL_FALSE;
  
  MC_ENABLE_BIN =
      (MC_ENABLE_REG == "FALSE") ? MC_ENABLE_FALSE :
      (MC_ENABLE_REG == "TRUE") ? MC_ENABLE_TRUE :
       MC_ENABLE_FALSE;
  
  PHY_ENABLE_BIN =
      (PHY_ENABLE_REG == "FALSE") ? PHY_ENABLE_FALSE :
      (PHY_ENABLE_REG == "TRUE") ? PHY_ENABLE_TRUE :
       PHY_ENABLE_FALSE;
  
  SWITCH_ENABLE_BIN =
      (SWITCH_ENABLE_REG == "FALSE") ? SWITCH_ENABLE_FALSE :
      (SWITCH_ENABLE_REG == "TRUE") ? SWITCH_ENABLE_TRUE :
       SWITCH_ENABLE_FALSE;
  
  end
`endif

`ifndef XIL_TIMING
  initial begin
    $display("Error: [Unisim %s-100] SIMPRIM primitive is not intended for direct instantiation in RTL or functional netlists. This primitive is only available in the SIMPRIM library for implemented netlists, please ensure you are pointing to the correct library. Instance %m", MODULE_NAME);
    #1 $finish;
  end
`endif

`ifndef XIL_XECLIB
always @ (trig_attr) begin
  #1;
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_REG != "FALSE") &&
       (CLK_SEL_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-101] CLK_SEL attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((MC_ENABLE_REG != "FALSE") &&
       (MC_ENABLE_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-104] MC_ENABLE attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, MC_ENABLE_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_REG != "FALSE") &&
       (PHY_ENABLE_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-105] PHY_ENABLE attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_PCLK_INVERT_REG != "FALSE") &&
       (PHY_PCLK_INVERT_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-106] PHY_PCLK_INVERT attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_PCLK_INVERT_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((SWITCH_ENABLE_REG != "FALSE") &&
       (SWITCH_ENABLE_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-107] SWITCH_ENABLE attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, SWITCH_ENABLE_REG);
    attr_err = 1'b1;
  end
  
  if (attr_err == 1'b1) #1 $finish;
end
`endif

`ifdef XIL_TIMING
  reg notifier;
`endif

// begin behavioral model

// end behavioral model

`ifndef XIL_XECLIB
  specify
    (PCLK => CATTRIP_PIPE) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[0]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[10]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[11]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[12]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[13]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[14]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[15]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[16]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[17]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[18]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[19]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[1]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[20]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[21]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[22]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[23]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[24]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[25]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[26]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[27]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[28]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[29]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[2]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[30]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[31]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[3]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[4]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[5]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[6]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[7]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[8]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[9]) = (100:100:100, 100:100:100);
    (PCLK => PREADY_PIPE) = (100:100:100, 100:100:100);
    (PCLK => PSLVERR_PIPE) = (100:100:100, 100:100:100);
    (PCLK => TEMP_PIPE[0]) = (100:100:100, 100:100:100);
    (PCLK => TEMP_PIPE[1]) = (100:100:100, 100:100:100);
    (PCLK => TEMP_PIPE[2]) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (CATTRIP_PIPE +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[0] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[10] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[11] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[12] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[13] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[14] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[15] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[16] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[17] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[18] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[19] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[1] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[20] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[21] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[22] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[23] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[24] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[25] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[26] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[27] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[28] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[29] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[2] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[30] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[31] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[3] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[4] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[5] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[6] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[7] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[8] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[9] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PREADY_PIPE +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PSLVERR_PIPE +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (TEMP_PIPE[0] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (TEMP_PIPE[1] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (TEMP_PIPE[2] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (CATTRIP_PIPE +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[0] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[10] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[11] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[12] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[13] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[14] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[15] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[16] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[17] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[18] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[19] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[1] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[20] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[21] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[22] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[23] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[24] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[25] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[26] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[27] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[28] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[29] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[2] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[30] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[31] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[3] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[4] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[5] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[6] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[7] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[8] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[9] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PREADY_PIPE +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PSLVERR_PIPE +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (TEMP_PIPE[0] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (TEMP_PIPE[1] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (TEMP_PIPE[2] +: 1)) = (100:100:100, 100:100:100);
`ifdef XIL_TIMING
    $recrem (negedge PRESET_N, negedge PCLK, 0:0:0, 0:0:0, notifier, , , PRESET_N_delay, PCLK_delay);
    $recrem (negedge PRESET_N, posedge PCLK, 0:0:0, 0:0:0, notifier, , , PRESET_N_delay, PCLK_delay);
    $recrem (posedge PRESET_N, negedge PCLK, 0:0:0, 0:0:0, notifier, , , PRESET_N_delay, PCLK_delay);
    $recrem (posedge PRESET_N, posedge PCLK, 0:0:0, 0:0:0, notifier, , , PRESET_N_delay, PCLK_delay);
    $setuphold (negedge PCLK, negedge PADDR[0], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[0]);
    $setuphold (negedge PCLK, negedge PADDR[10], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[10]);
    $setuphold (negedge PCLK, negedge PADDR[11], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[11]);
    $setuphold (negedge PCLK, negedge PADDR[12], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[12]);
    $setuphold (negedge PCLK, negedge PADDR[13], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[13]);
    $setuphold (negedge PCLK, negedge PADDR[14], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[14]);
    $setuphold (negedge PCLK, negedge PADDR[15], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[15]);
    $setuphold (negedge PCLK, negedge PADDR[16], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[16]);
    $setuphold (negedge PCLK, negedge PADDR[17], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[17]);
    $setuphold (negedge PCLK, negedge PADDR[18], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[18]);
    $setuphold (negedge PCLK, negedge PADDR[19], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[19]);
    $setuphold (negedge PCLK, negedge PADDR[1], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[1]);
    $setuphold (negedge PCLK, negedge PADDR[20], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[20]);
    $setuphold (negedge PCLK, negedge PADDR[21], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[21]);
    $setuphold (negedge PCLK, negedge PADDR[2], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[2]);
    $setuphold (negedge PCLK, negedge PADDR[3], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[3]);
    $setuphold (negedge PCLK, negedge PADDR[4], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[4]);
    $setuphold (negedge PCLK, negedge PADDR[5], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[5]);
    $setuphold (negedge PCLK, negedge PADDR[6], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[6]);
    $setuphold (negedge PCLK, negedge PADDR[7], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[7]);
    $setuphold (negedge PCLK, negedge PADDR[8], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[8]);
    $setuphold (negedge PCLK, negedge PADDR[9], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[9]);
    $setuphold (negedge PCLK, negedge PENABLE, 0:0:0, 0:0:0, notifier, , , PCLK_delay, PENABLE_delay);
    $setuphold (negedge PCLK, negedge PSEL, 0:0:0, 0:0:0, notifier, , , PCLK_delay, PSEL_delay);
    $setuphold (negedge PCLK, negedge PWDATA[0], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[0]);
    $setuphold (negedge PCLK, negedge PWDATA[10], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[10]);
    $setuphold (negedge PCLK, negedge PWDATA[11], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[11]);
    $setuphold (negedge PCLK, negedge PWDATA[12], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[12]);
    $setuphold (negedge PCLK, negedge PWDATA[13], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[13]);
    $setuphold (negedge PCLK, negedge PWDATA[14], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[14]);
    $setuphold (negedge PCLK, negedge PWDATA[15], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[15]);
    $setuphold (negedge PCLK, negedge PWDATA[16], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[16]);
    $setuphold (negedge PCLK, negedge PWDATA[17], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[17]);
    $setuphold (negedge PCLK, negedge PWDATA[18], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[18]);
    $setuphold (negedge PCLK, negedge PWDATA[19], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[19]);
    $setuphold (negedge PCLK, negedge PWDATA[1], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[1]);
    $setuphold (negedge PCLK, negedge PWDATA[20], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[20]);
    $setuphold (negedge PCLK, negedge PWDATA[21], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[21]);
    $setuphold (negedge PCLK, negedge PWDATA[22], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[22]);
    $setuphold (negedge PCLK, negedge PWDATA[23], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[23]);
    $setuphold (negedge PCLK, negedge PWDATA[24], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[24]);
    $setuphold (negedge PCLK, negedge PWDATA[25], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[25]);
    $setuphold (negedge PCLK, negedge PWDATA[26], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[26]);
    $setuphold (negedge PCLK, negedge PWDATA[27], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[27]);
    $setuphold (negedge PCLK, negedge PWDATA[28], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[28]);
    $setuphold (negedge PCLK, negedge PWDATA[29], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[29]);
    $setuphold (negedge PCLK, negedge PWDATA[2], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[2]);
    $setuphold (negedge PCLK, negedge PWDATA[30], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[30]);
    $setuphold (negedge PCLK, negedge PWDATA[31], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[31]);
    $setuphold (negedge PCLK, negedge PWDATA[3], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[3]);
    $setuphold (negedge PCLK, negedge PWDATA[4], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[4]);
    $setuphold (negedge PCLK, negedge PWDATA[5], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[5]);
    $setuphold (negedge PCLK, negedge PWDATA[6], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[6]);
    $setuphold (negedge PCLK, negedge PWDATA[7], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[7]);
    $setuphold (negedge PCLK, negedge PWDATA[8], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[8]);
    $setuphold (negedge PCLK, negedge PWDATA[9], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[9]);
    $setuphold (negedge PCLK, negedge PWRITE, 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWRITE_delay);
    $setuphold (negedge PCLK, posedge PADDR[0], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[0]);
    $setuphold (negedge PCLK, posedge PADDR[10], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[10]);
    $setuphold (negedge PCLK, posedge PADDR[11], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[11]);
    $setuphold (negedge PCLK, posedge PADDR[12], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[12]);
    $setuphold (negedge PCLK, posedge PADDR[13], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[13]);
    $setuphold (negedge PCLK, posedge PADDR[14], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[14]);
    $setuphold (negedge PCLK, posedge PADDR[15], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[15]);
    $setuphold (negedge PCLK, posedge PADDR[16], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[16]);
    $setuphold (negedge PCLK, posedge PADDR[17], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[17]);
    $setuphold (negedge PCLK, posedge PADDR[18], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[18]);
    $setuphold (negedge PCLK, posedge PADDR[19], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[19]);
    $setuphold (negedge PCLK, posedge PADDR[1], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[1]);
    $setuphold (negedge PCLK, posedge PADDR[20], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[20]);
    $setuphold (negedge PCLK, posedge PADDR[21], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[21]);
    $setuphold (negedge PCLK, posedge PADDR[2], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[2]);
    $setuphold (negedge PCLK, posedge PADDR[3], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[3]);
    $setuphold (negedge PCLK, posedge PADDR[4], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[4]);
    $setuphold (negedge PCLK, posedge PADDR[5], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[5]);
    $setuphold (negedge PCLK, posedge PADDR[6], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[6]);
    $setuphold (negedge PCLK, posedge PADDR[7], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[7]);
    $setuphold (negedge PCLK, posedge PADDR[8], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[8]);
    $setuphold (negedge PCLK, posedge PADDR[9], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[9]);
    $setuphold (negedge PCLK, posedge PENABLE, 0:0:0, 0:0:0, notifier, , , PCLK_delay, PENABLE_delay);
    $setuphold (negedge PCLK, posedge PSEL, 0:0:0, 0:0:0, notifier, , , PCLK_delay, PSEL_delay);
    $setuphold (negedge PCLK, posedge PWDATA[0], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[0]);
    $setuphold (negedge PCLK, posedge PWDATA[10], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[10]);
    $setuphold (negedge PCLK, posedge PWDATA[11], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[11]);
    $setuphold (negedge PCLK, posedge PWDATA[12], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[12]);
    $setuphold (negedge PCLK, posedge PWDATA[13], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[13]);
    $setuphold (negedge PCLK, posedge PWDATA[14], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[14]);
    $setuphold (negedge PCLK, posedge PWDATA[15], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[15]);
    $setuphold (negedge PCLK, posedge PWDATA[16], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[16]);
    $setuphold (negedge PCLK, posedge PWDATA[17], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[17]);
    $setuphold (negedge PCLK, posedge PWDATA[18], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[18]);
    $setuphold (negedge PCLK, posedge PWDATA[19], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[19]);
    $setuphold (negedge PCLK, posedge PWDATA[1], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[1]);
    $setuphold (negedge PCLK, posedge PWDATA[20], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[20]);
    $setuphold (negedge PCLK, posedge PWDATA[21], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[21]);
    $setuphold (negedge PCLK, posedge PWDATA[22], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[22]);
    $setuphold (negedge PCLK, posedge PWDATA[23], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[23]);
    $setuphold (negedge PCLK, posedge PWDATA[24], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[24]);
    $setuphold (negedge PCLK, posedge PWDATA[25], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[25]);
    $setuphold (negedge PCLK, posedge PWDATA[26], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[26]);
    $setuphold (negedge PCLK, posedge PWDATA[27], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[27]);
    $setuphold (negedge PCLK, posedge PWDATA[28], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[28]);
    $setuphold (negedge PCLK, posedge PWDATA[29], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[29]);
    $setuphold (negedge PCLK, posedge PWDATA[2], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[2]);
    $setuphold (negedge PCLK, posedge PWDATA[30], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[30]);
    $setuphold (negedge PCLK, posedge PWDATA[31], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[31]);
    $setuphold (negedge PCLK, posedge PWDATA[3], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[3]);
    $setuphold (negedge PCLK, posedge PWDATA[4], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[4]);
    $setuphold (negedge PCLK, posedge PWDATA[5], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[5]);
    $setuphold (negedge PCLK, posedge PWDATA[6], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[6]);
    $setuphold (negedge PCLK, posedge PWDATA[7], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[7]);
    $setuphold (negedge PCLK, posedge PWDATA[8], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[8]);
    $setuphold (negedge PCLK, posedge PWDATA[9], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[9]);
    $setuphold (negedge PCLK, posedge PWRITE, 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWRITE_delay);
    $setuphold (posedge PCLK, negedge PADDR[0], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[0]);
    $setuphold (posedge PCLK, negedge PADDR[10], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[10]);
    $setuphold (posedge PCLK, negedge PADDR[11], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[11]);
    $setuphold (posedge PCLK, negedge PADDR[12], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[12]);
    $setuphold (posedge PCLK, negedge PADDR[13], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[13]);
    $setuphold (posedge PCLK, negedge PADDR[14], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[14]);
    $setuphold (posedge PCLK, negedge PADDR[15], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[15]);
    $setuphold (posedge PCLK, negedge PADDR[16], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[16]);
    $setuphold (posedge PCLK, negedge PADDR[17], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[17]);
    $setuphold (posedge PCLK, negedge PADDR[18], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[18]);
    $setuphold (posedge PCLK, negedge PADDR[19], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[19]);
    $setuphold (posedge PCLK, negedge PADDR[1], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[1]);
    $setuphold (posedge PCLK, negedge PADDR[20], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[20]);
    $setuphold (posedge PCLK, negedge PADDR[21], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[21]);
    $setuphold (posedge PCLK, negedge PADDR[2], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[2]);
    $setuphold (posedge PCLK, negedge PADDR[3], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[3]);
    $setuphold (posedge PCLK, negedge PADDR[4], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[4]);
    $setuphold (posedge PCLK, negedge PADDR[5], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[5]);
    $setuphold (posedge PCLK, negedge PADDR[6], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[6]);
    $setuphold (posedge PCLK, negedge PADDR[7], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[7]);
    $setuphold (posedge PCLK, negedge PADDR[8], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[8]);
    $setuphold (posedge PCLK, negedge PADDR[9], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[9]);
    $setuphold (posedge PCLK, negedge PENABLE, 0:0:0, 0:0:0, notifier, , , PCLK_delay, PENABLE_delay);
    $setuphold (posedge PCLK, negedge PSEL, 0:0:0, 0:0:0, notifier, , , PCLK_delay, PSEL_delay);
    $setuphold (posedge PCLK, negedge PWDATA[0], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[0]);
    $setuphold (posedge PCLK, negedge PWDATA[10], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[10]);
    $setuphold (posedge PCLK, negedge PWDATA[11], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[11]);
    $setuphold (posedge PCLK, negedge PWDATA[12], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[12]);
    $setuphold (posedge PCLK, negedge PWDATA[13], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[13]);
    $setuphold (posedge PCLK, negedge PWDATA[14], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[14]);
    $setuphold (posedge PCLK, negedge PWDATA[15], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[15]);
    $setuphold (posedge PCLK, negedge PWDATA[16], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[16]);
    $setuphold (posedge PCLK, negedge PWDATA[17], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[17]);
    $setuphold (posedge PCLK, negedge PWDATA[18], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[18]);
    $setuphold (posedge PCLK, negedge PWDATA[19], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[19]);
    $setuphold (posedge PCLK, negedge PWDATA[1], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[1]);
    $setuphold (posedge PCLK, negedge PWDATA[20], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[20]);
    $setuphold (posedge PCLK, negedge PWDATA[21], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[21]);
    $setuphold (posedge PCLK, negedge PWDATA[22], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[22]);
    $setuphold (posedge PCLK, negedge PWDATA[23], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[23]);
    $setuphold (posedge PCLK, negedge PWDATA[24], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[24]);
    $setuphold (posedge PCLK, negedge PWDATA[25], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[25]);
    $setuphold (posedge PCLK, negedge PWDATA[26], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[26]);
    $setuphold (posedge PCLK, negedge PWDATA[27], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[27]);
    $setuphold (posedge PCLK, negedge PWDATA[28], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[28]);
    $setuphold (posedge PCLK, negedge PWDATA[29], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[29]);
    $setuphold (posedge PCLK, negedge PWDATA[2], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[2]);
    $setuphold (posedge PCLK, negedge PWDATA[30], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[30]);
    $setuphold (posedge PCLK, negedge PWDATA[31], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[31]);
    $setuphold (posedge PCLK, negedge PWDATA[3], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[3]);
    $setuphold (posedge PCLK, negedge PWDATA[4], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[4]);
    $setuphold (posedge PCLK, negedge PWDATA[5], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[5]);
    $setuphold (posedge PCLK, negedge PWDATA[6], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[6]);
    $setuphold (posedge PCLK, negedge PWDATA[7], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[7]);
    $setuphold (posedge PCLK, negedge PWDATA[8], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[8]);
    $setuphold (posedge PCLK, negedge PWDATA[9], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[9]);
    $setuphold (posedge PCLK, negedge PWRITE, 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWRITE_delay);
    $setuphold (posedge PCLK, posedge PADDR[0], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[0]);
    $setuphold (posedge PCLK, posedge PADDR[10], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[10]);
    $setuphold (posedge PCLK, posedge PADDR[11], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[11]);
    $setuphold (posedge PCLK, posedge PADDR[12], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[12]);
    $setuphold (posedge PCLK, posedge PADDR[13], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[13]);
    $setuphold (posedge PCLK, posedge PADDR[14], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[14]);
    $setuphold (posedge PCLK, posedge PADDR[15], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[15]);
    $setuphold (posedge PCLK, posedge PADDR[16], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[16]);
    $setuphold (posedge PCLK, posedge PADDR[17], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[17]);
    $setuphold (posedge PCLK, posedge PADDR[18], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[18]);
    $setuphold (posedge PCLK, posedge PADDR[19], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[19]);
    $setuphold (posedge PCLK, posedge PADDR[1], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[1]);
    $setuphold (posedge PCLK, posedge PADDR[20], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[20]);
    $setuphold (posedge PCLK, posedge PADDR[21], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[21]);
    $setuphold (posedge PCLK, posedge PADDR[2], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[2]);
    $setuphold (posedge PCLK, posedge PADDR[3], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[3]);
    $setuphold (posedge PCLK, posedge PADDR[4], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[4]);
    $setuphold (posedge PCLK, posedge PADDR[5], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[5]);
    $setuphold (posedge PCLK, posedge PADDR[6], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[6]);
    $setuphold (posedge PCLK, posedge PADDR[7], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[7]);
    $setuphold (posedge PCLK, posedge PADDR[8], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[8]);
    $setuphold (posedge PCLK, posedge PADDR[9], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PADDR_delay[9]);
    $setuphold (posedge PCLK, posedge PENABLE, 0:0:0, 0:0:0, notifier, , , PCLK_delay, PENABLE_delay);
    $setuphold (posedge PCLK, posedge PSEL, 0:0:0, 0:0:0, notifier, , , PCLK_delay, PSEL_delay);
    $setuphold (posedge PCLK, posedge PWDATA[0], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[0]);
    $setuphold (posedge PCLK, posedge PWDATA[10], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[10]);
    $setuphold (posedge PCLK, posedge PWDATA[11], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[11]);
    $setuphold (posedge PCLK, posedge PWDATA[12], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[12]);
    $setuphold (posedge PCLK, posedge PWDATA[13], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[13]);
    $setuphold (posedge PCLK, posedge PWDATA[14], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[14]);
    $setuphold (posedge PCLK, posedge PWDATA[15], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[15]);
    $setuphold (posedge PCLK, posedge PWDATA[16], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[16]);
    $setuphold (posedge PCLK, posedge PWDATA[17], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[17]);
    $setuphold (posedge PCLK, posedge PWDATA[18], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[18]);
    $setuphold (posedge PCLK, posedge PWDATA[19], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[19]);
    $setuphold (posedge PCLK, posedge PWDATA[1], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[1]);
    $setuphold (posedge PCLK, posedge PWDATA[20], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[20]);
    $setuphold (posedge PCLK, posedge PWDATA[21], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[21]);
    $setuphold (posedge PCLK, posedge PWDATA[22], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[22]);
    $setuphold (posedge PCLK, posedge PWDATA[23], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[23]);
    $setuphold (posedge PCLK, posedge PWDATA[24], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[24]);
    $setuphold (posedge PCLK, posedge PWDATA[25], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[25]);
    $setuphold (posedge PCLK, posedge PWDATA[26], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[26]);
    $setuphold (posedge PCLK, posedge PWDATA[27], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[27]);
    $setuphold (posedge PCLK, posedge PWDATA[28], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[28]);
    $setuphold (posedge PCLK, posedge PWDATA[29], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[29]);
    $setuphold (posedge PCLK, posedge PWDATA[2], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[2]);
    $setuphold (posedge PCLK, posedge PWDATA[30], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[30]);
    $setuphold (posedge PCLK, posedge PWDATA[31], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[31]);
    $setuphold (posedge PCLK, posedge PWDATA[3], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[3]);
    $setuphold (posedge PCLK, posedge PWDATA[4], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[4]);
    $setuphold (posedge PCLK, posedge PWDATA[5], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[5]);
    $setuphold (posedge PCLK, posedge PWDATA[6], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[6]);
    $setuphold (posedge PCLK, posedge PWDATA[7], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[7]);
    $setuphold (posedge PCLK, posedge PWDATA[8], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[8]);
    $setuphold (posedge PCLK, posedge PWDATA[9], 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWDATA_delay[9]);
    $setuphold (posedge PCLK, posedge PWRITE, 0:0:0, 0:0:0, notifier, , , PCLK_delay, PWRITE_delay);
`endif
    specparam PATHPULSE$ = 0;
  endspecify
`endif
endmodule

`endcelldefine
