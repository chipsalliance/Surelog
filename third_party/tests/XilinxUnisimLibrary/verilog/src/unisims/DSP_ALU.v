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
// \   \   \/      Version     : 2018.3
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        DSP_ALU
// /___/   /\      Filename    : DSP_ALU.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//  07/15/12 - Migrate from E1.
//  12/10/12 - Add dynamic registers
//  04/22/13 - 713695 - Zero mult result on USE_SIMD
//  04/22/13 - 713617 - CARRYCASCOUT behaviour
//  04/23/13 - 714772 - remove sensitivity to negedge GSR
//  05/07/13 - 716896 - ALUMODE/OPMODE_INV_REG mis sized
//  05/07/13 - x_mac_cascd missing for sensitivity list.
//  10/22/14 - 808642 - Added #1 to $finish
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps

`celldefine

module DSP_ALU #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter integer ALUMODEREG = 1,
  parameter integer CARRYINREG = 1,
  parameter integer CARRYINSELREG = 1,
  parameter [3:0] IS_ALUMODE_INVERTED = 4'b0000,
  parameter [0:0] IS_CARRYIN_INVERTED = 1'b0,
  parameter [0:0] IS_CLK_INVERTED = 1'b0,
  parameter [8:0] IS_OPMODE_INVERTED = 9'b000000000,
  parameter [0:0] IS_RSTALLCARRYIN_INVERTED = 1'b0,
  parameter [0:0] IS_RSTALUMODE_INVERTED = 1'b0,
  parameter [0:0] IS_RSTCTRL_INVERTED = 1'b0,
  parameter integer MREG = 1,
  parameter integer OPMODEREG = 1,
  parameter [47:0] RND = 48'h000000000000,
  parameter USE_SIMD = "ONE48",
  parameter USE_WIDEXOR = "FALSE",
  parameter XORSIMD = "XOR24_48_96"
)(
  output ALUMODE10,
  output [47:0] ALU_OUT,
  output [3:0] COUT,
  output MULTSIGN_ALU,
  output [7:0] XOR_MX,

  input [3:0] ALUMODE,
  input AMULT26,
  input [29:0] A_ALU,
  input BMULT17,
  input [17:0] B_ALU,
  input CARRYCASCIN,
  input CARRYIN,
  input [2:0] CARRYINSEL,
  input CCOUT,
  input CEALUMODE,
  input CECARRYIN,
  input CECTRL,
  input CEM,
  input CLK,
  input [47:0] C_DATA,
  input MULTSIGNIN,
  input [8:0] OPMODE,
  input [47:0] PCIN,
  input [47:0] P_FDBK,
  input P_FDBK_47,
  input RSTALLCARRYIN,
  input RSTALUMODE,
  input RSTCTRL,
  input [44:0] U_DATA,
  input [44:0] V_DATA
);
  
// define constants
  localparam MODULE_NAME = "DSP_ALU";

// Parameter encodings and registers
  localparam USE_SIMD_FOUR12 = 1;
  localparam USE_SIMD_ONE48 = 0;
  localparam USE_SIMD_TWO24 = 2;
  localparam USE_WIDEXOR_FALSE = 0;
  localparam USE_WIDEXOR_TRUE = 1;
  localparam XORSIMD_XOR12 = 1;
  localparam XORSIMD_XOR24_48_96 = 0;

  reg trig_attr;
// include dynamic registers - XILINX test only
`ifdef XIL_DR
  `include "DSP_ALU_dr.v"
`else
  reg [31:0] ALUMODEREG_REG = ALUMODEREG;
  reg [31:0] CARRYINREG_REG = CARRYINREG;
  reg [31:0] CARRYINSELREG_REG = CARRYINSELREG;
  reg [3:0] IS_ALUMODE_INVERTED_REG = IS_ALUMODE_INVERTED;
  reg [0:0] IS_CARRYIN_INVERTED_REG = IS_CARRYIN_INVERTED;
  reg [0:0] IS_CLK_INVERTED_REG = IS_CLK_INVERTED;
  reg [8:0] IS_OPMODE_INVERTED_REG = IS_OPMODE_INVERTED;
  reg [0:0] IS_RSTALLCARRYIN_INVERTED_REG = IS_RSTALLCARRYIN_INVERTED;
  reg [0:0] IS_RSTALUMODE_INVERTED_REG = IS_RSTALUMODE_INVERTED;
  reg [0:0] IS_RSTCTRL_INVERTED_REG = IS_RSTCTRL_INVERTED;
  reg [31:0] MREG_REG = MREG;
  reg [31:0] OPMODEREG_REG = OPMODEREG;
  reg [47:0] RND_REG = RND;
  reg [48:1] USE_SIMD_REG = USE_SIMD;
  reg [40:1] USE_WIDEXOR_REG = USE_WIDEXOR;
  reg [88:1] XORSIMD_REG = XORSIMD;
`endif

`ifdef XIL_XECLIB
  wire ALUMODEREG_BIN;
  wire CARRYINREG_BIN;
  wire CARRYINSELREG_BIN;
  wire MREG_BIN;
  wire OPMODEREG_BIN;
  wire [1:0] USE_SIMD_BIN;
  wire USE_WIDEXOR_BIN;
  wire XORSIMD_BIN;
`else
  reg ALUMODEREG_BIN;
  reg CARRYINREG_BIN;
  reg CARRYINSELREG_BIN;
  reg MREG_BIN;
  reg OPMODEREG_BIN;
  reg [1:0] USE_SIMD_BIN;
  reg USE_WIDEXOR_BIN;
  reg XORSIMD_BIN;
`endif

`ifdef XIL_XECLIB
  reg glblGSR = 1'b0;
`else
  tri0 glblGSR = glbl.GSR;
`endif

  wire AMULT26_in;
  wire BMULT17_in;
  wire CARRYCASCIN_in;
  wire CARRYIN_in;
  wire CCOUT_in;
  wire CEALUMODE_in;
  wire CECARRYIN_in;
  wire CECTRL_in;
  wire CEM_in;
  wire CLK_in;
  wire MULTSIGNIN_in;
  wire P_FDBK_47_in;
  wire RSTALLCARRYIN_in;
  wire RSTALUMODE_in;
  wire RSTCTRL_in;
  wire [17:0] B_ALU_in;
  wire [29:0] A_ALU_in;
  wire [2:0] CARRYINSEL_in;
  wire [3:0] ALUMODE_in;
  wire [44:0] U_DATA_in;
  wire [44:0] V_DATA_in;
  wire [47:0] C_DATA_in;
  wire [47:0] PCIN_in;
  wire [47:0] P_FDBK_in;
  wire [8:0] OPMODE_in;

`ifdef XIL_TIMING
  wire AMULT26_delay;
  wire BMULT17_delay;
  wire CARRYIN_delay;
  wire CEALUMODE_delay;
  wire CECARRYIN_delay;
  wire CECTRL_delay;
  wire CEM_delay;
  wire CLK_delay;
  wire RSTALLCARRYIN_delay;
  wire RSTALUMODE_delay;
  wire RSTCTRL_delay;
  wire [2:0] CARRYINSEL_delay;
  wire [3:0] ALUMODE_delay;
  wire [8:0] OPMODE_delay;
`endif
  
`ifdef XIL_TIMING
  assign ALUMODE_in[0] = (ALUMODE[0] !== 1'bz) && (ALUMODE_delay[0] ^ IS_ALUMODE_INVERTED_REG[0]); // rv 0
  assign ALUMODE_in[1] = (ALUMODE[1] !== 1'bz) && (ALUMODE_delay[1] ^ IS_ALUMODE_INVERTED_REG[1]); // rv 0
  assign ALUMODE_in[2] = (ALUMODE[2] !== 1'bz) && (ALUMODE_delay[2] ^ IS_ALUMODE_INVERTED_REG[2]); // rv 0
  assign ALUMODE_in[3] = (ALUMODE[3] !== 1'bz) && (ALUMODE_delay[3] ^ IS_ALUMODE_INVERTED_REG[3]); // rv 0
  assign AMULT26_in = AMULT26_delay;
  assign BMULT17_in = BMULT17_delay;
  assign CARRYINSEL_in[0] = (CARRYINSEL[0] !== 1'bz) && CARRYINSEL_delay[0]; // rv 0
  assign CARRYINSEL_in[1] = (CARRYINSEL[1] !== 1'bz) && CARRYINSEL_delay[1]; // rv 0
  assign CARRYINSEL_in[2] = (CARRYINSEL[2] !== 1'bz) && CARRYINSEL_delay[2]; // rv 0
  assign CARRYIN_in = (CARRYIN !== 1'bz) && (CARRYIN_delay ^ IS_CARRYIN_INVERTED_REG); // rv 0
  assign CEALUMODE_in = (CEALUMODE !== 1'bz) && CEALUMODE_delay; // rv 0
  assign CECARRYIN_in = (CECARRYIN !== 1'bz) && CECARRYIN_delay; // rv 0
  assign CECTRL_in = (CECTRL !== 1'bz) && CECTRL_delay; // rv 0
  assign CEM_in = (CEM !== 1'bz) && CEM_delay; // rv 0
  assign CLK_in = (CLK !== 1'bz) && (CLK_delay ^ IS_CLK_INVERTED_REG); // rv 0
  assign OPMODE_in[0] = (OPMODE[0] !== 1'bz) && (OPMODE_delay[0] ^ IS_OPMODE_INVERTED_REG[0]); // rv 0
  assign OPMODE_in[1] = (OPMODE[1] !== 1'bz) && (OPMODE_delay[1] ^ IS_OPMODE_INVERTED_REG[1]); // rv 0
  assign OPMODE_in[2] = (OPMODE[2] !== 1'bz) && (OPMODE_delay[2] ^ IS_OPMODE_INVERTED_REG[2]); // rv 0
  assign OPMODE_in[3] = (OPMODE[3] !== 1'bz) && (OPMODE_delay[3] ^ IS_OPMODE_INVERTED_REG[3]); // rv 0
  assign OPMODE_in[4] = (OPMODE[4] !== 1'bz) && (OPMODE_delay[4] ^ IS_OPMODE_INVERTED_REG[4]); // rv 0
  assign OPMODE_in[5] = (OPMODE[5] !== 1'bz) && (OPMODE_delay[5] ^ IS_OPMODE_INVERTED_REG[5]); // rv 0
  assign OPMODE_in[6] = (OPMODE[6] !== 1'bz) && (OPMODE_delay[6] ^ IS_OPMODE_INVERTED_REG[6]); // rv 0
  assign OPMODE_in[7] = (OPMODE[7] !== 1'bz) && (OPMODE_delay[7] ^ IS_OPMODE_INVERTED_REG[7]); // rv 0
  assign OPMODE_in[8] = (OPMODE[8] !== 1'bz) && (OPMODE_delay[8] ^ IS_OPMODE_INVERTED_REG[8]); // rv 0
  assign RSTALLCARRYIN_in = (RSTALLCARRYIN !== 1'bz) && (RSTALLCARRYIN_delay ^ IS_RSTALLCARRYIN_INVERTED_REG); // rv 0
  assign RSTALUMODE_in = (RSTALUMODE !== 1'bz) && (RSTALUMODE_delay ^ IS_RSTALUMODE_INVERTED_REG); // rv 0
  assign RSTCTRL_in = (RSTCTRL !== 1'bz) && (RSTCTRL_delay ^ IS_RSTCTRL_INVERTED_REG); // rv 0
`else
  assign ALUMODE_in[0] = (ALUMODE[0] !== 1'bz) && (ALUMODE[0] ^ IS_ALUMODE_INVERTED_REG[0]); // rv 0
  assign ALUMODE_in[1] = (ALUMODE[1] !== 1'bz) && (ALUMODE[1] ^ IS_ALUMODE_INVERTED_REG[1]); // rv 0
  assign ALUMODE_in[2] = (ALUMODE[2] !== 1'bz) && (ALUMODE[2] ^ IS_ALUMODE_INVERTED_REG[2]); // rv 0
  assign ALUMODE_in[3] = (ALUMODE[3] !== 1'bz) && (ALUMODE[3] ^ IS_ALUMODE_INVERTED_REG[3]); // rv 0
  assign AMULT26_in = AMULT26;
  assign BMULT17_in = BMULT17;
  assign CARRYINSEL_in[0] = (CARRYINSEL[0] !== 1'bz) && CARRYINSEL[0]; // rv 0
  assign CARRYINSEL_in[1] = (CARRYINSEL[1] !== 1'bz) && CARRYINSEL[1]; // rv 0
  assign CARRYINSEL_in[2] = (CARRYINSEL[2] !== 1'bz) && CARRYINSEL[2]; // rv 0
  assign CARRYIN_in = (CARRYIN !== 1'bz) && (CARRYIN ^ IS_CARRYIN_INVERTED_REG); // rv 0
  assign CEALUMODE_in = (CEALUMODE !== 1'bz) && CEALUMODE; // rv 0
  assign CECARRYIN_in = (CECARRYIN !== 1'bz) && CECARRYIN; // rv 0
  assign CECTRL_in = (CECTRL !== 1'bz) && CECTRL; // rv 0
  assign CEM_in = (CEM !== 1'bz) && CEM; // rv 0
  assign CLK_in = (CLK !== 1'bz) && (CLK ^ IS_CLK_INVERTED_REG); // rv 0
  assign OPMODE_in[0] = (OPMODE[0] !== 1'bz) && (OPMODE[0] ^ IS_OPMODE_INVERTED_REG[0]); // rv 0
  assign OPMODE_in[1] = (OPMODE[1] !== 1'bz) && (OPMODE[1] ^ IS_OPMODE_INVERTED_REG[1]); // rv 0
  assign OPMODE_in[2] = (OPMODE[2] !== 1'bz) && (OPMODE[2] ^ IS_OPMODE_INVERTED_REG[2]); // rv 0
  assign OPMODE_in[3] = (OPMODE[3] !== 1'bz) && (OPMODE[3] ^ IS_OPMODE_INVERTED_REG[3]); // rv 0
  assign OPMODE_in[4] = (OPMODE[4] !== 1'bz) && (OPMODE[4] ^ IS_OPMODE_INVERTED_REG[4]); // rv 0
  assign OPMODE_in[5] = (OPMODE[5] !== 1'bz) && (OPMODE[5] ^ IS_OPMODE_INVERTED_REG[5]); // rv 0
  assign OPMODE_in[6] = (OPMODE[6] !== 1'bz) && (OPMODE[6] ^ IS_OPMODE_INVERTED_REG[6]); // rv 0
  assign OPMODE_in[7] = (OPMODE[7] !== 1'bz) && (OPMODE[7] ^ IS_OPMODE_INVERTED_REG[7]); // rv 0
  assign OPMODE_in[8] = (OPMODE[8] !== 1'bz) && (OPMODE[8] ^ IS_OPMODE_INVERTED_REG[8]); // rv 0
  assign RSTALLCARRYIN_in = (RSTALLCARRYIN !== 1'bz) && (RSTALLCARRYIN ^ IS_RSTALLCARRYIN_INVERTED_REG); // rv 0
  assign RSTALUMODE_in = (RSTALUMODE !== 1'bz) && (RSTALUMODE ^ IS_RSTALUMODE_INVERTED_REG); // rv 0
  assign RSTCTRL_in = (RSTCTRL !== 1'bz) && (RSTCTRL ^ IS_RSTCTRL_INVERTED_REG); // rv 0
`endif

  assign A_ALU_in = A_ALU;
  assign B_ALU_in = B_ALU;
  assign CARRYCASCIN_in = CARRYCASCIN;
  assign CCOUT_in = CCOUT;
  assign C_DATA_in = C_DATA;
  assign MULTSIGNIN_in = MULTSIGNIN;
  assign PCIN_in = PCIN;
  assign P_FDBK_47_in = P_FDBK_47;
  assign P_FDBK_in = P_FDBK;
  assign U_DATA_in = (USE_SIMD_BIN == USE_SIMD_ONE48) ? U_DATA : 45'h100000000000;
  assign V_DATA_in = (USE_SIMD_BIN == USE_SIMD_ONE48) ? V_DATA : 45'h100000000000;

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
  assign ALUMODEREG_BIN = ALUMODEREG_REG[0];

  assign CARRYINREG_BIN = CARRYINREG_REG[0];

  assign CARRYINSELREG_BIN = CARRYINSELREG_REG[0];

  assign MREG_BIN = MREG_REG[0];

  assign OPMODEREG_BIN = OPMODEREG_REG[0];

  assign USE_SIMD_BIN =
    (USE_SIMD_REG == "ONE48") ? USE_SIMD_ONE48 :
    (USE_SIMD_REG == "FOUR12") ? USE_SIMD_FOUR12 :
    (USE_SIMD_REG == "TWO24") ? USE_SIMD_TWO24 :
     USE_SIMD_ONE48;

  assign USE_WIDEXOR_BIN =
    (USE_WIDEXOR_REG == "FALSE") ? USE_WIDEXOR_FALSE :
    (USE_WIDEXOR_REG == "TRUE") ? USE_WIDEXOR_TRUE :
     USE_WIDEXOR_FALSE;

  assign XORSIMD_BIN =
    (XORSIMD_REG == "XOR24_48_96") ? XORSIMD_XOR24_48_96 :
    (XORSIMD_REG == "XOR12") ? XORSIMD_XOR12 :
     XORSIMD_XOR24_48_96;

`else
always @(trig_attr) begin
#1;
  ALUMODEREG_BIN = ALUMODEREG_REG[0];

  CARRYINREG_BIN = CARRYINREG_REG[0];

  CARRYINSELREG_BIN = CARRYINSELREG_REG[0];

  MREG_BIN = MREG_REG[0];

  OPMODEREG_BIN = OPMODEREG_REG[0];

  USE_SIMD_BIN =
    (USE_SIMD_REG == "ONE48") ? USE_SIMD_ONE48 :
    (USE_SIMD_REG == "FOUR12") ? USE_SIMD_FOUR12 :
    (USE_SIMD_REG == "TWO24") ? USE_SIMD_TWO24 :
     USE_SIMD_ONE48;

  USE_WIDEXOR_BIN =
    (USE_WIDEXOR_REG == "FALSE") ? USE_WIDEXOR_FALSE :
    (USE_WIDEXOR_REG == "TRUE") ? USE_WIDEXOR_TRUE :
     USE_WIDEXOR_FALSE;

  XORSIMD_BIN =
    (XORSIMD_REG == "XOR24_48_96") ? XORSIMD_XOR24_48_96 :
    (XORSIMD_REG == "XOR12") ? XORSIMD_XOR12 :
     XORSIMD_XOR24_48_96;

end
`endif

`ifndef XIL_TIMING
  initial begin
    $display("Error: [Unisim %s-100] SIMPRIM primitive is not intended for direct instantiation in RTL or functional netlists. This primitive is only available in the SIMPRIM library for implemented netlists, please ensure you are pointing to the correct library. Instance %m", MODULE_NAME);
    #1 $finish;
  end
`endif

`ifndef XIL_XECLIB
  always @(trig_attr) begin
  #1;
    if ((attr_test == 1'b1) ||
        ((ALUMODEREG_REG != 1) &&
         (ALUMODEREG_REG != 0))) begin
      $display("Error: [Unisim %s-101] ALUMODEREG attribute is set to %d.  Legal values for this attribute are 1 or 0. Instance: %m", MODULE_NAME, ALUMODEREG_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((CARRYINREG_REG != 1) &&
         (CARRYINREG_REG != 0))) begin
      $display("Error: [Unisim %s-102] CARRYINREG attribute is set to %d.  Legal values for this attribute are 1 or 0. Instance: %m", MODULE_NAME, CARRYINREG_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((CARRYINSELREG_REG != 1) &&
         (CARRYINSELREG_REG != 0))) begin
      $display("Error: [Unisim %s-103] CARRYINSELREG attribute is set to %d.  Legal values for this attribute are 1 or 0. Instance: %m", MODULE_NAME, CARRYINSELREG_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((MREG_REG != 1) &&
         (MREG_REG != 0))) begin
      $display("Error: [Unisim %s-111] MREG attribute is set to %d.  Legal values for this attribute are 1 or 0. Instance: %m", MODULE_NAME, MREG_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((OPMODEREG_REG != 1) &&
         (OPMODEREG_REG != 0))) begin
      $display("Error: [Unisim %s-112] OPMODEREG attribute is set to %d.  Legal values for this attribute are 1 or 0. Instance: %m", MODULE_NAME, OPMODEREG_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((USE_SIMD_REG != "ONE48") &&
         (USE_SIMD_REG != "FOUR12") &&
         (USE_SIMD_REG != "TWO24"))) begin
      $display("Error: [Unisim %s-114] USE_SIMD attribute is set to %s.  Legal values for this attribute are ONE48, FOUR12 or TWO24. Instance: %m", MODULE_NAME, USE_SIMD_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((USE_WIDEXOR_REG != "FALSE") &&
         (USE_WIDEXOR_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-115] USE_WIDEXOR attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, USE_WIDEXOR_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((XORSIMD_REG != "XOR24_48_96") &&
         (XORSIMD_REG != "XOR12"))) begin
      $display("Error: [Unisim %s-116] XORSIMD attribute is set to %s.  Legal values for this attribute are XOR24_48_96 or XOR12. Instance: %m", MODULE_NAME, XORSIMD_REG);
      attr_err = 1'b1;
    end

    if (attr_err == 1'b1) #1 $finish;
  end
`endif

`ifdef XIL_TIMING
  reg notifier;
`endif

// begin behavioral model

  localparam MAX_ALU_FULL   = 48;
  localparam MAX_CARRYOUT   = 4;
  reg cci_drc_msg;
  reg cis_drc_msg;


  wire CARRYIN_mux;
  reg CARRYIN_reg;
  reg [3:0] ALUMODE_reg;
  reg [2:0] CARRYINSEL_mux;
  reg [2:0] CARRYINSEL_reg;
  reg [8:0] OPMODE_mux;
  reg [8:0] OPMODE_reg;

  wire [47:0] x_mac_cascd;
  
  reg [47:0] wmux;
  reg [47:0] xmux;
  reg [47:0] ymux;
  reg [47:0] zmux;
  wire [47:0] z_optinv;
  
  wire cin;
  reg cin_b;
  wire rst_carryin_g;
  reg qmultcarryin;

  wire c_mult;
  wire ce_m_g;
  wire d_carryin_int;
  wire dr_carryin_int;
  wire multcarryin_data;

  reg invalid_opmode;
  reg opmode_valid_flag_dal; // used in OPMODE DRC
  reg ping_opmode_drc_check;

  wire [MAX_ALU_FULL-1:0] co;
  wire [MAX_ALU_FULL-1:0] s;
  wire [MAX_ALU_FULL-1:0] comux;
  wire [MAX_ALU_FULL-1:0] comux_w;
  wire [MAX_ALU_FULL-1:0] comux4simd;
  wire [MAX_ALU_FULL-1:0] smux;
  wire [MAX_ALU_FULL-1:0] smux_w;
  wire [MAX_ALU_FULL:0] a_int;
  wire [12:0] s0;
  wire cout0;
  wire intc1;
  wire co12_lsb;
  wire [12:0] s1;
  wire cout1;
  wire intc2;
  wire co24_lsb;
  wire [12:0] s2;
  wire cout2;
  wire intc3;
  wire co36_lsb;
  wire [13:0] s3;
  wire cout3;
  wire cout4;
  wire xor_12a;
  wire xor_12b;
  wire xor_12c;
  wire xor_12d;
  wire xor_12e;
  wire xor_12f;
  wire xor_12g;
  wire xor_12h;
  wire xor_24a;
  wire xor_24b;
  wire xor_24c;
  wire xor_24d;
  wire xor_48a;
  wire xor_48b;
  wire xor_96;
  wire cout_0;
  wire cout_1;
  wire cout_2;
  wire cout_3;
  wire mult_or_logic;

  reg [3:0] ALUMODE_DATA;

// initialize regs
`ifndef XIL_XECLIB
initial begin
  cci_drc_msg = 1'b0;
  cis_drc_msg = 1'b0;
  CARRYIN_reg = 1'b0;
  ALUMODE_reg = 4'b0;
  CARRYINSEL_mux = 3'b0;
  CARRYINSEL_reg = 3'b0;
  OPMODE_mux = 9'b0;
  OPMODE_reg = 9'b0;
  wmux = 48'b0;
  xmux = 48'b0;
  ymux = 48'b0;
  zmux = 48'b0;
  cin_b = 1'b0;
  qmultcarryin = 1'b0;
  invalid_opmode = 1'b1;
  opmode_valid_flag_dal = 1'b1;
  ping_opmode_drc_check = 1'b0;
end
`endif

//*** W mux NB
  always @(OPMODE_mux[8:7] or P_FDBK_in or RND_REG or C_DATA_in)
     case (OPMODE_mux[8:7])
          2'b00 : wmux = 48'b0;
          2'b01 : wmux = P_FDBK_in;
          2'b10 : wmux = RND_REG;
          2'b11 : wmux = C_DATA_in;
        default : wmux = {48{1'bx}};
    endcase

// To support MAC-cascade add multsignin to bit 1 of X
  assign x_mac_cascd = (OPMODE_mux[6:4] == 3'b100) ? {{46{1'b0}},MULTSIGNIN_in,1'b0} : {48{1'b0}};

//*** X mux NB
  always @(U_DATA_in or P_FDBK_in or A_ALU_in or B_ALU_in or OPMODE_mux[1:0] or x_mac_cascd)
	  case (OPMODE_mux[1:0])
          2'b00 : xmux = x_mac_cascd;
          2'b01 : xmux = {{3{U_DATA_in[44]}}, U_DATA_in};
          2'b10 : xmux = P_FDBK_in;
          2'b11 : xmux = {A_ALU_in, B_ALU_in};
        default : xmux = {48{1'bx}};
	  endcase

//*** Y mux NB
  always @(OPMODE_mux[3:2] or V_DATA_in or C_DATA_in)
	  case (OPMODE_mux[3:2])
          2'b00 : ymux = 48'b0;
          2'b01 : ymux = {{3{1'b0}}, V_DATA_in};
          2'b10 : ymux = {48{1'b1}};
          2'b11 : ymux = C_DATA_in;
        default : ymux = {48{1'bx}};
     endcase

//*** Z mux NB
  always @(OPMODE_mux[6:4] or PCIN_in or P_FDBK_in or C_DATA_in or P_FDBK_47_in)
	  casex (OPMODE_mux[6:4])
         3'b000 : zmux = 48'b0;
         3'b001 : zmux = PCIN_in;
         3'b010 : zmux = P_FDBK_in;
         3'b011 : zmux = C_DATA_in;
         3'b100 : zmux = P_FDBK_in;
         3'b101 : zmux = {{9{PCIN_in[47]}},  {8{PCIN_in[47]}},   PCIN_in[47:17]};
         3'b11x : zmux = {{9{P_FDBK_47_in}}, {8{P_FDBK_in[47]}}, P_FDBK_in[47:17]};
        default : zmux = {48{1'bx}};
     endcase

//*********************************************************
//*** CARRYINSEL and OPMODE with 1 level of register
//*********************************************************
    always @(posedge CLK_in) begin
	   if (RSTCTRL_in || glblGSR) begin
         OPMODE_reg <= 9'b0;
	   end  
	   else if (CECTRL_in) begin
         OPMODE_reg <= OPMODE_in;
	   end
    end

    always @(posedge CLK_in) begin
	   if (RSTCTRL_in || glblGSR) begin
         CARRYINSEL_reg <= 3'b0;
	   end  
	   else if (CECTRL_in) begin
         CARRYINSEL_reg <= CARRYINSEL_in;
	   end
    end

    always @(*) CARRYINSEL_mux = (CARRYINSELREG_BIN == 1'b1) ?  CARRYINSEL_reg : CARRYINSEL_in;

    always @(*) begin
      if (OPMODEREG_BIN == 1'b1) OPMODE_mux = OPMODE_reg;
      else OPMODE_mux = OPMODE_in;
    end

    always @(CARRYINSEL_mux or CARRYCASCIN_in or MULTSIGNIN_in or OPMODE_mux) begin
      if (CARRYINSEL_mux == 3'b010) begin 
        if (!((MULTSIGNIN_in === 1'bx) || (cci_drc_msg == 1'b1) ||
             ((OPMODE_mux == 9'b001001000) && !(MULTSIGNIN_in === 1'bx)) ||
             ((MULTSIGNIN_in == 1'b0) && (CARRYCASCIN_in == 1'b0)))) begin
	       $display("DRC warning : [Unisim %s-7] CARRYCASCIN can only be used in the current %s if the previous %s is performing a two input ADD or SUBRTACT operation or the current %s is configured in the MAC extend opmode 7'b1001000 at %.3f ns. Instance %m\n", MODULE_NAME, MODULE_NAME, MODULE_NAME, MODULE_NAME, $time/1000.0);
// CR 619940 -- Enhanced DRC warning
          $display("The simulation model does not know the placement of the %s slices used, so it cannot fully confirm the above warning. It is necessary to view the placement of the %s slices and ensure that these warnings are not being breached\n", MODULE_NAME, MODULE_NAME);
          cci_drc_msg = 1'b1;
        end  
        if (!((MULTSIGNIN_in === 1'bx) || (OPMODE_mux[3:0] != 4'b0101))) begin
          $display("DRC warning : [Unisim %s-10] CARRYINSEL is set to 010 with OPMODE set to multiplication (xxx0101). This is an illegal mode and may show deviation between simulation results and hardware behavior. %s instance %m at %.3f ns.", MODULE_NAME, MODULE_NAME, $time/1000.0);
        end
        if (!((MULTSIGNIN_in === 1'bx) || (cis_drc_msg == 1'b1) ||
             (OPMODEREG_BIN == 1'b1))) begin
          $display("DRC warning : [Unisim %s-11] CARRYINSEL is set to 010 with OPMODEREG set to 0. This causes unknown values after reset occurs. It is suggested to use OPMODEREG = 1 when cascading large adders. %s instance %m at %.3f ns.", MODULE_NAME, MODULE_NAME, $time/1000.0);
          cis_drc_msg = 1'b1;
        end
      end  
    end 

//*********************************************************
//*** ALUMODE with 1 level of register
//*********************************************************
    always @(posedge CLK_in) begin
	    if (RSTALUMODE_in || glblGSR)
          ALUMODE_reg <= 4'b0;
	    else if (CEALUMODE_in)
          ALUMODE_reg <= ALUMODE_in;
       end

    always @(*) ALUMODE_DATA = (ALUMODEREG_BIN == 1'b1) ? ALUMODE_reg : ALUMODE_in;

//------------------------------------------------------------------
//*** DRC for OPMODE
//------------------------------------------------------------------

// needs PREG from output block
// ~2000 lines code - skip for now - copy/rework from DSP48E1.

//--####################################################################
//--#####                         ALU                              #####
//--####################################################################

// ADDSUB block - first stage of ALU develops sums and carries for Final Adder
// Invert Z for subtract operation using alumode<0>
  assign z_optinv = {48{ALUMODE_DATA[0]}} ^ zmux;

// Add W, X, Y, Z carry-save style; basically full adder logic below
  assign co = ((xmux & ymux)|(z_optinv & ymux)|(xmux & z_optinv));
// s has a fan-out of 2 (1) FA with W (2) second leg of XOR tree
  assign s  = (z_optinv^xmux^ymux);

// Mux S and CO to do 2 operands logic operations
// S = produce XOR/XNOR, NOT functions
// CO = produce AND/NAND, OR/NOR functions
  assign comux = ALUMODE_DATA[2] ? 0  : co;
  assign smux =  ALUMODE_DATA[3] ? co : s;

// Carry mux to handle SIMD mode 
// SIMD must be used here since addition of W requires carry propogation
  assign comux4simd = {
              comux[47:36],
              comux[35]&&(USE_SIMD_BIN != USE_SIMD_FOUR12),
              comux[34:24],
              comux[23]&&(USE_SIMD_BIN == USE_SIMD_ONE48),
              comux[22:12],
              comux[11]&&(USE_SIMD_BIN != USE_SIMD_FOUR12),
              comux[10:0]
            };

// FA to combine W-mux with s and co
// comux must be shifted to properly reflect carry operation
  assign smux_w  =   smux ^ {comux4simd[46:0],1'b0} ^ wmux;
  assign comux_w = ((smux & {comux4simd[46:0],1'b0}) |
                    (wmux & {comux4simd[46:0],1'b0}) |
                    (smux & wmux));

// alumode10 indicates a subtraction, used to correct carryout polarity
  assign ALUMODE10 = (ALUMODE_DATA[0] & ALUMODE_DATA[1]);

// prepare data for Final Adder
// a[0] is in fact the cin bit, adder inputs: a[48:1], b[47:0], cin= a[0]
  assign a_int = {comux_w, cin};
//  assign b_int = smux_w;

// FINAL ADDER - second stage develops final sums and carries 
  assign s0        = a_int[11:0] + smux_w[11:0];
  // invert if alumode10
  assign cout0     = ALUMODE10     ^ (a_int[12] ^ s0[12] ^ comux[11]);
  // internal carry is zero'd out on mc_simd == 1
  assign intc1     = (USE_SIMD_BIN != USE_SIMD_FOUR12) && s0[12];
  // next lsb is zero'd out on mc_simd == 1
  assign co12_lsb  = (USE_SIMD_BIN != USE_SIMD_FOUR12) && a_int[12];
  //
  assign s1        = {a_int[23:13],co12_lsb} + smux_w[23:12] + intc1;
  assign cout1     = ALUMODE10     ^ (a_int[24] ^ s1[12] ^ comux[23]);
  assign intc2     = (USE_SIMD_BIN == USE_SIMD_ONE48) && s1[12];
  assign co24_lsb  = (USE_SIMD_BIN == USE_SIMD_ONE48) && a_int[24];
  //
  assign s2        = {a_int[35:25],co24_lsb} + smux_w[35:24] + intc2;
  assign cout2     = ALUMODE10     ^ (a_int[36] ^ s2[12] ^ comux[35]);
  assign intc3     = (USE_SIMD_BIN != USE_SIMD_FOUR12) && s2[12];
  assign co36_lsb  = (USE_SIMD_BIN != USE_SIMD_FOUR12) && a_int[36];
  //
  assign s3        = {a_int[48:37],co36_lsb} + {comux4simd[47],smux_w[47:36]} + intc3;
  assign cout3     = ALUMODE10     ^ s3[12];

// Not gated with alumode10 since used to propogate carry in wide multiply
  assign cout4     = s3[13];

// Wide XOR
  assign xor_12a = USE_WIDEXOR_BIN ? ^s[5:0] : 0;
  assign xor_12b = USE_WIDEXOR_BIN ? ^s[11:6] : 0;
  assign xor_12c = USE_WIDEXOR_BIN ? ^s[17:12] : 0;
  assign xor_12d = USE_WIDEXOR_BIN ? ^s[23:18] : 0;
  assign xor_12e = USE_WIDEXOR_BIN ? ^s[29:24] : 0;
  assign xor_12f = USE_WIDEXOR_BIN ? ^s[35:30] : 0;
  assign xor_12g = USE_WIDEXOR_BIN ? ^s[41:36] : 0;
  assign xor_12h = USE_WIDEXOR_BIN ? ^s[47:42] : 0;

  assign xor_24a = xor_12a ^ xor_12b;
  assign xor_24b = xor_12c ^ xor_12d;
  assign xor_24c = xor_12e ^ xor_12f;
  assign xor_24d = xor_12g ^ xor_12h;

  assign xor_48a = xor_24a ^ xor_24b;
  assign xor_48b = xor_24c ^ xor_24d;

  assign xor_96 = xor_48a ^ xor_48b;

//  "X" carryout for multiply and logic operations
  assign mult_or_logic = ((OPMODE_mux[3:0] == 4'b0101) ||
                          (ALUMODE_DATA[3:2] != 2'b00));
// allow carrycascout to not X in output atom
//  assign cout_3 = mult_or_logic ? 1'bx : cout3;
  assign cout_3 =                        cout3;
  assign cout_2 = mult_or_logic ? 1'bx : cout2;
  assign cout_1 = mult_or_logic ? 1'bx : cout1;
  assign cout_0 = mult_or_logic ? 1'bx : cout0;
// drive signals to Output Atom
  assign COUT[3] =                                     cout_3;
  assign COUT[2] = (USE_SIMD_BIN == USE_SIMD_FOUR12) ? cout_2 : 1'bx;
  assign COUT[1] = (USE_SIMD_BIN != USE_SIMD_ONE48 ) ? cout_1 : 1'bx;
  assign COUT[0] = (USE_SIMD_BIN == USE_SIMD_FOUR12) ? cout_0 : 1'bx;
  assign MULTSIGN_ALU     = s3[13];
  assign #1 ALU_OUT = {48{ALUMODE_DATA[1]}} ^ {s3[11:0],s2[11:0],s1[11:0],s0[11:0]}; // break 0 delay feedback
  assign XOR_MX[0] = XORSIMD_BIN ? xor_12a : xor_24a;
  assign XOR_MX[1] = XORSIMD_BIN ? xor_12b : xor_48a;
  assign XOR_MX[2] = XORSIMD_BIN ? xor_12c : xor_24b;
  assign XOR_MX[3] = XORSIMD_BIN ? xor_12d : xor_96;
  assign XOR_MX[4] = XORSIMD_BIN ? xor_12e : xor_24c;
  assign XOR_MX[5] = XORSIMD_BIN ? xor_12f : xor_48b;
  assign XOR_MX[6] = XORSIMD_BIN ? xor_12g : xor_24d;
  assign XOR_MX[7] = xor_12h;


//--########################### END ALU ################################
 
    
//*** CarryIn Mux and Register

//-------  input 0
    always @(posedge CLK_in) begin
	    if (RSTALLCARRYIN_in || glblGSR)
          CARRYIN_reg <= 1'b0;
	    else if (CECARRYIN_in)
          CARRYIN_reg <= CARRYIN_in;
       end

       assign CARRYIN_mux = (CARRYINREG_BIN == 1'b1) ? CARRYIN_reg : CARRYIN_in;

// INTERNAL CARRYIN REGISTER
  assign c_mult = !(AMULT26_in^BMULT17_in);
  assign ce_m_g   = CEM_in & ~glblGSR; // & gwe
  assign rst_carryin_g = RSTALLCARRYIN_in & ~glblGSR; // & gwe
  assign d_carryin_int  = ce_m_g ? c_mult : qmultcarryin;

// rstallcarryin is injected through data path
  assign dr_carryin_int = rst_carryin_g ? 0 : d_carryin_int;

  always @(posedge CLK_in) begin
    if (glblGSR)
       qmultcarryin <= 1'b0;
    else
       qmultcarryin <= dr_carryin_int;
  end

  // bypass register mux
  assign multcarryin_data = (MREG_BIN == 1'b1) ? qmultcarryin : c_mult;

//NB
  always @(CARRYINSEL_mux or CARRYIN_mux or PCIN_in[47] or CARRYCASCIN_in or CCOUT_in or P_FDBK_in[47] or multcarryin_data) begin
	case (CARRYINSEL_mux)
     3'b000  : cin_b = ~CARRYIN_mux;
     3'b001  : cin_b = PCIN_in[47];
     3'b010  : cin_b = ~CARRYCASCIN_in;
     3'b011  : cin_b = ~PCIN_in[47];
     3'b100  : cin_b = ~CCOUT_in;
     3'b101  : cin_b = P_FDBK_in[47];
     3'b110  : cin_b = ~multcarryin_data;
     3'b111  : cin_b = ~P_FDBK_in[47];
     default : cin_b = 1'bx;
	endcase
   end
// disable carryin when performing logic operation
   assign cin = (ALUMODE_DATA[3] || ALUMODE_DATA[2]) ? 1'b0 : ~cin_b;

// end behavioral model

`ifndef XIL_XECLIB
`ifdef XIL_TIMING
  wire clk_en_n;
  wire clk_en_p;

  assign clk_en_n = IS_CLK_INVERTED_REG;
  assign clk_en_p = ~IS_CLK_INVERTED_REG;

`endif
  specify
    (ALUMODE *> ALUMODE10) = (0:0:0, 0:0:0);
    (ALUMODE *> ALU_OUT) = (0:0:0, 0:0:0);
    (ALUMODE *> COUT) = (0:0:0, 0:0:0);
    (ALUMODE *> MULTSIGN_ALU) = (0:0:0, 0:0:0);
    (ALUMODE *> XOR_MX) = (0:0:0, 0:0:0);
    (AMULT26 *> ALU_OUT) = (0:0:0, 0:0:0);
    (AMULT26 *> COUT) = (0:0:0, 0:0:0);
    (AMULT26 => MULTSIGN_ALU) = (0:0:0, 0:0:0);
    (A_ALU *> ALU_OUT) = (0:0:0, 0:0:0);
    (A_ALU *> COUT) = (0:0:0, 0:0:0);
    (A_ALU *> MULTSIGN_ALU) = (0:0:0, 0:0:0);
    (A_ALU *> XOR_MX) = (0:0:0, 0:0:0);
    (BMULT17 *> ALU_OUT) = (0:0:0, 0:0:0);
    (BMULT17 *> COUT) = (0:0:0, 0:0:0);
    (BMULT17 => MULTSIGN_ALU) = (0:0:0, 0:0:0);
    (B_ALU *> ALU_OUT) = (0:0:0, 0:0:0);
    (B_ALU *> COUT) = (0:0:0, 0:0:0);
    (B_ALU *> MULTSIGN_ALU) = (0:0:0, 0:0:0);
    (B_ALU *> XOR_MX) = (0:0:0, 0:0:0);
    (CARRYCASCIN *> ALU_OUT) = (0:0:0, 0:0:0);
    (CARRYCASCIN *> COUT) = (0:0:0, 0:0:0);
    (CARRYCASCIN => MULTSIGN_ALU) = (0:0:0, 0:0:0);
    (CARRYIN *> ALU_OUT) = (0:0:0, 0:0:0);
    (CARRYIN *> COUT) = (0:0:0, 0:0:0);
    (CARRYIN => MULTSIGN_ALU) = (0:0:0, 0:0:0);
    (CARRYINSEL *> ALU_OUT) = (0:0:0, 0:0:0);
    (CARRYINSEL *> COUT) = (0:0:0, 0:0:0);
    (CARRYINSEL *> MULTSIGN_ALU) = (0:0:0, 0:0:0);
    (CCOUT *> ALU_OUT) = (0:0:0, 0:0:0);
    (CCOUT *> COUT) = (0:0:0, 0:0:0);
    (CCOUT => MULTSIGN_ALU) = (0:0:0, 0:0:0);
    (CLK *> ALU_OUT) = (0:0:0, 0:0:0);
    (CLK *> COUT) = (0:0:0, 0:0:0);
    (CLK *> XOR_MX) = (0:0:0, 0:0:0);
    (CLK => ALUMODE10) = (0:0:0, 0:0:0);
    (CLK => MULTSIGN_ALU) = (0:0:0, 0:0:0);
    (C_DATA *> ALU_OUT) = (0:0:0, 0:0:0);
    (C_DATA *> COUT) = (0:0:0, 0:0:0);
    (C_DATA *> MULTSIGN_ALU) = (0:0:0, 0:0:0);
    (C_DATA *> XOR_MX) = (0:0:0, 0:0:0);
    (MULTSIGNIN *> ALU_OUT) = (0:0:0, 0:0:0);
    (MULTSIGNIN *> COUT) = (0:0:0, 0:0:0);
    (MULTSIGNIN => MULTSIGN_ALU) = (0:0:0, 0:0:0);
    (OPMODE *> ALU_OUT) = (0:0:0, 0:0:0);
    (OPMODE *> COUT) = (0:0:0, 0:0:0);
    (OPMODE *> MULTSIGN_ALU) = (0:0:0, 0:0:0);
    (OPMODE *> XOR_MX) = (0:0:0, 0:0:0);
    (PCIN *> ALU_OUT) = (0:0:0, 0:0:0);
    (PCIN *> COUT) = (0:0:0, 0:0:0);
    (PCIN *> MULTSIGN_ALU) = (0:0:0, 0:0:0);
    (PCIN *> XOR_MX) = (0:0:0, 0:0:0);
    (P_FDBK *> ALU_OUT) = (0:0:0, 0:0:0);
    (P_FDBK *> COUT) = (0:0:0, 0:0:0);
    (P_FDBK *> MULTSIGN_ALU) = (0:0:0, 0:0:0);
    (P_FDBK *> XOR_MX) = (0:0:0, 0:0:0);
    (P_FDBK_47 *> ALU_OUT) = (0:0:0, 0:0:0);
    (P_FDBK_47 *> COUT) = (0:0:0, 0:0:0);
    (P_FDBK_47 *> XOR_MX) = (0:0:0, 0:0:0);
    (P_FDBK_47 => MULTSIGN_ALU) = (0:0:0, 0:0:0);
    (U_DATA *> ALU_OUT) = (0:0:0, 0:0:0);
    (U_DATA *> COUT) = (0:0:0, 0:0:0);
    (U_DATA *> MULTSIGN_ALU) = (0:0:0, 0:0:0);
    (V_DATA *> ALU_OUT) = (0:0:0, 0:0:0);
    (V_DATA *> COUT) = (0:0:0, 0:0:0);
    (V_DATA *> MULTSIGN_ALU) = (0:0:0, 0:0:0);
`ifdef XIL_TIMING
    $setuphold (negedge CLK, negedge ALUMODE, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, ALUMODE_delay);
    $setuphold (negedge CLK, negedge AMULT26, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, AMULT26_delay);
    $setuphold (negedge CLK, negedge BMULT17, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, BMULT17_delay);
    $setuphold (negedge CLK, negedge CARRYIN, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CARRYIN_delay);
    $setuphold (negedge CLK, negedge CARRYINSEL, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CARRYINSEL_delay);
    $setuphold (negedge CLK, negedge CEALUMODE, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CEALUMODE_delay);
    $setuphold (negedge CLK, negedge CECARRYIN, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CECARRYIN_delay);
    $setuphold (negedge CLK, negedge CECTRL, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CECTRL_delay);
    $setuphold (negedge CLK, negedge CEM, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CEM_delay);
    $setuphold (negedge CLK, negedge OPMODE, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, OPMODE_delay);
    $setuphold (negedge CLK, negedge RSTALLCARRYIN, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, RSTALLCARRYIN_delay);
    $setuphold (negedge CLK, negedge RSTALUMODE, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, RSTALUMODE_delay);
    $setuphold (negedge CLK, negedge RSTCTRL, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, RSTCTRL_delay);
    $setuphold (negedge CLK, posedge ALUMODE, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, ALUMODE_delay);
    $setuphold (negedge CLK, posedge AMULT26, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, AMULT26_delay);
    $setuphold (negedge CLK, posedge BMULT17, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, BMULT17_delay);
    $setuphold (negedge CLK, posedge CARRYIN, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CARRYIN_delay);
    $setuphold (negedge CLK, posedge CARRYINSEL, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CARRYINSEL_delay);
    $setuphold (negedge CLK, posedge CEALUMODE, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CEALUMODE_delay);
    $setuphold (negedge CLK, posedge CECARRYIN, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CECARRYIN_delay);
    $setuphold (negedge CLK, posedge CECTRL, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CECTRL_delay);
    $setuphold (negedge CLK, posedge CEM, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CEM_delay);
    $setuphold (negedge CLK, posedge OPMODE, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, OPMODE_delay);
    $setuphold (negedge CLK, posedge RSTALLCARRYIN, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, RSTALLCARRYIN_delay);
    $setuphold (negedge CLK, posedge RSTALUMODE, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, RSTALUMODE_delay);
    $setuphold (negedge CLK, posedge RSTCTRL, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, RSTCTRL_delay);
    $setuphold (posedge CLK, negedge ALUMODE, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, ALUMODE_delay);
    $setuphold (posedge CLK, negedge AMULT26, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, AMULT26_delay);
    $setuphold (posedge CLK, negedge BMULT17, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, BMULT17_delay);
    $setuphold (posedge CLK, negedge CARRYIN, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CARRYIN_delay);
    $setuphold (posedge CLK, negedge CARRYINSEL, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CARRYINSEL_delay);
    $setuphold (posedge CLK, negedge CEALUMODE, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CEALUMODE_delay);
    $setuphold (posedge CLK, negedge CECARRYIN, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CECARRYIN_delay);
    $setuphold (posedge CLK, negedge CECTRL, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CECTRL_delay);
    $setuphold (posedge CLK, negedge CEM, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CEM_delay);
    $setuphold (posedge CLK, negedge OPMODE, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, OPMODE_delay);
    $setuphold (posedge CLK, negedge RSTALLCARRYIN, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, RSTALLCARRYIN_delay);
    $setuphold (posedge CLK, negedge RSTALUMODE, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, RSTALUMODE_delay);
    $setuphold (posedge CLK, negedge RSTCTRL, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, RSTCTRL_delay);
    $setuphold (posedge CLK, posedge ALUMODE, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, ALUMODE_delay);
    $setuphold (posedge CLK, posedge AMULT26, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, AMULT26_delay);
    $setuphold (posedge CLK, posedge BMULT17, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, BMULT17_delay);
    $setuphold (posedge CLK, posedge CARRYIN, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CARRYIN_delay);
    $setuphold (posedge CLK, posedge CARRYINSEL, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CARRYINSEL_delay);
    $setuphold (posedge CLK, posedge CEALUMODE, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CEALUMODE_delay);
    $setuphold (posedge CLK, posedge CECARRYIN, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CECARRYIN_delay);
    $setuphold (posedge CLK, posedge CECTRL, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CECTRL_delay);
    $setuphold (posedge CLK, posedge CEM, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CEM_delay);
    $setuphold (posedge CLK, posedge OPMODE, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, OPMODE_delay);
    $setuphold (posedge CLK, posedge RSTALLCARRYIN, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, RSTALLCARRYIN_delay);
    $setuphold (posedge CLK, posedge RSTALUMODE, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, RSTALUMODE_delay);
    $setuphold (posedge CLK, posedge RSTCTRL, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, RSTCTRL_delay);
`endif
    specparam PATHPULSE$ = 0;
  endspecify
`endif
endmodule

`endcelldefine
