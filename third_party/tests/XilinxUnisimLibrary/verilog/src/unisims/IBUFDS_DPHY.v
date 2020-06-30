///////////////////////////////////////////////////////////////////////////////
//     Copyright (c) 1995/2015 Xilinx, Inc.
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
// \   \   \/      Version     : 2015.4
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        _no_description_
// /___/   /\      Filename    : IBUFDS_DPHY.v
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

module IBUFDS_DPHY #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter DIFF_TERM = "TRUE",
  parameter IOSTANDARD = "DEFAULT",
  parameter SIM_DEVICE = "ULTRASCALE_PLUS"
)(
  output HSRX_O,
  output LPRX_O_N,
  output LPRX_O_P,

  input HSRX_DISABLE,
  input I,
  input IB,
  input LPRX_DISABLE
);
  
// define constants
  localparam MODULE_NAME = "IBUFDS_DPHY";

// Parameter encodings and registers
  localparam DIFF_TERM_FALSE = 1;
  localparam DIFF_TERM_TRUE = 0;
  localparam IOSTANDARD_DEFAULT = 0;

  reg trig_attr = 1'b0;
// include dynamic registers - XILINX test only
`ifdef XIL_DR
  `include "IBUFDS_DPHY_dr.v"
`else
  localparam [40:1] DIFF_TERM_REG = DIFF_TERM;
  localparam [56:1] IOSTANDARD_REG = IOSTANDARD;
`endif

  wire DIFF_TERM_BIN;
  wire IOSTANDARD_BIN;

`ifdef XIL_ATTR_TEST
  reg attr_test = 1'b1;
`else
  reg attr_test = 1'b0;
`endif
  reg attr_err = 1'b0;
  tri0 glblGSR = glbl.GSR;

  wire HSRX_O_out;
  wire LPRX_O_N_out;
  wire LPRX_O_P_out;

  wire HSRX_DISABLE_in;
  wire IB_in;
  wire I_in;
  wire LPRX_DISABLE_in;

  assign HSRX_O = HSRX_O_out;
  assign LPRX_O_N = LPRX_O_N_out;
  assign LPRX_O_P = LPRX_O_P_out;

  assign HSRX_DISABLE_in = HSRX_DISABLE;
  assign IB_in = IB;
  assign I_in = I;
  assign LPRX_DISABLE_in = LPRX_DISABLE;

  assign DIFF_TERM_BIN =
    (DIFF_TERM_REG == "FALSE") ? DIFF_TERM_FALSE :
    (DIFF_TERM_REG == "TRUE")  ? DIFF_TERM_TRUE  :
     DIFF_TERM_TRUE;

  assign IOSTANDARD_BIN =
    (IOSTANDARD_REG == "DEFAULT") ? IOSTANDARD_DEFAULT :
     IOSTANDARD_DEFAULT;

  initial begin
    #1;
    trig_attr = ~trig_attr;
  end

  always @ (trig_attr) begin
    #1;
    if ((attr_test == 1'b1) ||
        ((DIFF_TERM_REG != "TRUE") &&
         (DIFF_TERM_REG != "FALSE"))) begin
      $display("Error: [Unisim %s-101] DIFF_TERM attribute is set to %s.  Legal values for this attribute are TRUE or FALSE. Instance: %m", MODULE_NAME, DIFF_TERM_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((SIM_DEVICE != "ULTRASCALE_PLUS") &&
         (SIM_DEVICE != "ULTRASCALE_PLUS_ES1") &&
         (SIM_DEVICE != "ULTRASCALE_PLUS_ES2") &&
         (SIM_DEVICE != "VERSAL_AI_CORE") &&
         (SIM_DEVICE != "VERSAL_AI_CORE_ES1") &&
         (SIM_DEVICE != "VERSAL_AI_CORE_ES2") &&
         (SIM_DEVICE != "VERSAL_AI_EDGE") &&
         (SIM_DEVICE != "VERSAL_AI_EDGE_ES1") &&
         (SIM_DEVICE != "VERSAL_AI_EDGE_ES2") &&
         (SIM_DEVICE != "VERSAL_AI_RF") &&
         (SIM_DEVICE != "VERSAL_AI_RF_ES1") &&
         (SIM_DEVICE != "VERSAL_AI_RF_ES2") &&
         (SIM_DEVICE != "VERSAL_HBM") &&
         (SIM_DEVICE != "VERSAL_HBM_ES1") &&
         (SIM_DEVICE != "VERSAL_HBM_ES2") &&
         (SIM_DEVICE != "VERSAL_PREMIUM") &&
         (SIM_DEVICE != "VERSAL_PREMIUM_ES1") &&
         (SIM_DEVICE != "VERSAL_PREMIUM_ES2") &&
         (SIM_DEVICE != "VERSAL_PRIME") &&
         (SIM_DEVICE != "VERSAL_PRIME_ES1") &&
         (SIM_DEVICE != "VERSAL_PRIME_ES2"))) begin
      $display("Error: [Unisim %s-102] SIM_DEVICE attribute is set to %s.  Legal values for this attribute are ULTRASCALE_PLUS, ULTRASCALE_PLUS_ES1, ULTRASCALE_PLUS_ES2, VERSAL_AI_CORE, VERSAL_AI_CORE_ES1, VERSAL_AI_CORE_ES2, VERSAL_AI_EDGE, VERSAL_AI_EDGE_ES1, VERSAL_AI_EDGE_ES2, VERSAL_AI_RF, VERSAL_AI_RF_ES1, VERSAL_AI_RF_ES2, VERSAL_HBM, VERSAL_HBM_ES1, VERSAL_HBM_ES2, VERSAL_PREMIUM, VERSAL_PREMIUM_ES1, VERSAL_PREMIUM_ES2, VERSAL_PRIME, VERSAL_PRIME_ES1 or VERSAL_PRIME_ES2. Instance: %m", MODULE_NAME, SIM_DEVICE);
      attr_err = 1'b1;
    end

// no check
//    if ((attr_test == 1'b1) ||
//        ((IOSTANDARD_REG != "DEFAULT"))) begin
//      $display("Error: [Unisim %s-102] IOSTANDARD attribute is set to %s.  Legal values for this attribute are DEFAULT. Instance: %m", MODULE_NAME, IOSTANDARD_REG);
//      attr_err = 1'b1;
//    end

    if (attr_err == 1'b1) #1 $finish;
  end

  reg o_out;
  wire [1:0] lp_out;
  wire sim_mode;
  wire lp_mode;
  wire lp_rx_disable;
  wire hs_mode;
  wire hs_out;
  reg [3*8:1] strP,strN;  
  
  always @(*)
     begin
        $sformat(strP, "%v", I);
        $sformat(strN, "%v", IB);
     end

  assign lp_mode = (strP[24:17] == "S") & (strN[24:17] == "S");  // For LP strength type Strong
  //assign sim_mode = (SIM_DEVICE == "ULTRASCALE_PLUS" || SIM_DEVICE== "ULTRASCALE_PLUS_ES1" || SIM_DEVICE== "ULTRASCALE_PLUS_ES2") ? 1'b0 : 1'b0;
  assign sim_mode = 1'b0;
  assign #1 lp_out[0] = lp_mode === 1'b1 ? I_in : 1'b0;
  assign #1 lp_out[1] = lp_mode === 1'b1 ? IB_in : 1'b0;
  
  assign HSRX_O_out = (HSRX_DISABLE_in === 1'b0) ? o_out : (HSRX_DISABLE_in === 1'bx || HSRX_DISABLE_in === 1'bz) ? 1'bx : 1'b0;
  
  assign LPRX_O_N_out = (LPRX_DISABLE_in === 1'b0) ? lp_out[1] : (LPRX_DISABLE_in === 1'bx || LPRX_DISABLE_in === 1'bz) ? 1'bx : sim_mode; 
  assign LPRX_O_P_out = (LPRX_DISABLE_in === 1'b0) ? lp_out[0] : (LPRX_DISABLE_in === 1'bx || LPRX_DISABLE_in === 1'bz) ? 1'bx : sim_mode; 

  always @ (I_in or IB_in) begin
    if (I_in == 1'b1 && IB_in == 1'b0)
      o_out <= 1'b1;
    else if (I_in == 1'b0 && IB_in == 1'b1)
      o_out <= 1'b0;
    else if ((I_in === 1'bx) || (IB_in === 1'bx) || I_in === 1'bz || IB_in === 1'bz )
      o_out <= 1'bx;
  end

endmodule

`endcelldefine
