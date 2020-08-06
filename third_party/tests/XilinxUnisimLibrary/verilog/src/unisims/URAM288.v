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
//  /   /                        288K-bit High-Density Memory Building Block
// /___/   /\      Filename    : URAM288.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//  10/31/2014 - Initial functional version
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps

`celldefine

module URAM288 #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter integer AUTO_SLEEP_LATENCY = 8,
  parameter integer AVG_CONS_INACTIVE_CYCLES = 10,
  parameter BWE_MODE_A = "PARITY_INTERLEAVED",
  parameter BWE_MODE_B = "PARITY_INTERLEAVED",
  parameter CASCADE_ORDER_A = "NONE",
  parameter CASCADE_ORDER_B = "NONE",
  parameter EN_AUTO_SLEEP_MODE = "FALSE",
  parameter EN_ECC_RD_A = "FALSE",
  parameter EN_ECC_RD_B = "FALSE",
  parameter EN_ECC_WR_A = "FALSE",
  parameter EN_ECC_WR_B = "FALSE",
  parameter IREG_PRE_A = "FALSE",
  parameter IREG_PRE_B = "FALSE",
  parameter [0:0] IS_CLK_INVERTED = 1'b0,
  parameter [0:0] IS_EN_A_INVERTED = 1'b0,
  parameter [0:0] IS_EN_B_INVERTED = 1'b0,
  parameter [0:0] IS_RDB_WR_A_INVERTED = 1'b0,
  parameter [0:0] IS_RDB_WR_B_INVERTED = 1'b0,
  parameter [0:0] IS_RST_A_INVERTED = 1'b0,
  parameter [0:0] IS_RST_B_INVERTED = 1'b0,
  parameter MATRIX_ID = "NONE",
  parameter integer NUM_UNIQUE_SELF_ADDR_A = 1,
  parameter integer NUM_UNIQUE_SELF_ADDR_B = 1,
  parameter integer NUM_URAM_IN_MATRIX = 1,
  parameter OREG_A = "FALSE",
  parameter OREG_B = "FALSE",
  parameter OREG_ECC_A = "FALSE",
  parameter OREG_ECC_B = "FALSE",
  parameter REG_CAS_A = "FALSE",
  parameter REG_CAS_B = "FALSE",
  parameter RST_MODE_A = "SYNC",
  parameter RST_MODE_B = "SYNC",
  parameter [10:0] SELF_ADDR_A = 11'h000,
  parameter [10:0] SELF_ADDR_B = 11'h000,
  parameter [10:0] SELF_MASK_A = 11'h7FF,
  parameter [10:0] SELF_MASK_B = 11'h7FF,
  parameter USE_EXT_CE_A = "FALSE",
  parameter USE_EXT_CE_B = "FALSE"
)(
  output [22:0] CAS_OUT_ADDR_A,
  output [22:0] CAS_OUT_ADDR_B,
  output [8:0] CAS_OUT_BWE_A,
  output [8:0] CAS_OUT_BWE_B,
  output CAS_OUT_DBITERR_A,
  output CAS_OUT_DBITERR_B,
  output [71:0] CAS_OUT_DIN_A,
  output [71:0] CAS_OUT_DIN_B,
  output [71:0] CAS_OUT_DOUT_A,
  output [71:0] CAS_OUT_DOUT_B,
  output CAS_OUT_EN_A,
  output CAS_OUT_EN_B,
  output CAS_OUT_RDACCESS_A,
  output CAS_OUT_RDACCESS_B,
  output CAS_OUT_RDB_WR_A,
  output CAS_OUT_RDB_WR_B,
  output CAS_OUT_SBITERR_A,
  output CAS_OUT_SBITERR_B,
  output DBITERR_A,
  output DBITERR_B,
  output [71:0] DOUT_A,
  output [71:0] DOUT_B,
  output RDACCESS_A,
  output RDACCESS_B,
  output SBITERR_A,
  output SBITERR_B,

  input [22:0] ADDR_A,
  input [22:0] ADDR_B,
  input [8:0] BWE_A,
  input [8:0] BWE_B,
  input [22:0] CAS_IN_ADDR_A,
  input [22:0] CAS_IN_ADDR_B,
  input [8:0] CAS_IN_BWE_A,
  input [8:0] CAS_IN_BWE_B,
  input CAS_IN_DBITERR_A,
  input CAS_IN_DBITERR_B,
  input [71:0] CAS_IN_DIN_A,
  input [71:0] CAS_IN_DIN_B,
  input [71:0] CAS_IN_DOUT_A,
  input [71:0] CAS_IN_DOUT_B,
  input CAS_IN_EN_A,
  input CAS_IN_EN_B,
  input CAS_IN_RDACCESS_A,
  input CAS_IN_RDACCESS_B,
  input CAS_IN_RDB_WR_A,
  input CAS_IN_RDB_WR_B,
  input CAS_IN_SBITERR_A,
  input CAS_IN_SBITERR_B,
  input CLK,
  input [71:0] DIN_A,
  input [71:0] DIN_B,
  input EN_A,
  input EN_B,
  input INJECT_DBITERR_A,
  input INJECT_DBITERR_B,
  input INJECT_SBITERR_A,
  input INJECT_SBITERR_B,
  input OREG_CE_A,
  input OREG_CE_B,
  input OREG_ECC_CE_A,
  input OREG_ECC_CE_B,
  input RDB_WR_A,
  input RDB_WR_B,
  input RST_A,
  input RST_B,
  input SLEEP
);
  
// define constants
  localparam MODULE_NAME = "URAM288";

// Parameter encodings and registers
  localparam BWE_MODE_A_PARITY_INDEPENDENT = 1;
  localparam BWE_MODE_A_PARITY_INTERLEAVED = 0;
  localparam BWE_MODE_B_PARITY_INDEPENDENT = 1;
  localparam BWE_MODE_B_PARITY_INTERLEAVED = 0;
  localparam CASCADE_ORDER_A_FIRST = 1;
  localparam CASCADE_ORDER_A_LAST = 2;
  localparam CASCADE_ORDER_A_MIDDLE = 3;
  localparam CASCADE_ORDER_A_NONE = 0;
  localparam CASCADE_ORDER_B_FIRST = 1;
  localparam CASCADE_ORDER_B_LAST = 2;
  localparam CASCADE_ORDER_B_MIDDLE = 3;
  localparam CASCADE_ORDER_B_NONE = 0;
  localparam EN_AUTO_SLEEP_MODE_FALSE = 0;
  localparam EN_AUTO_SLEEP_MODE_TRUE = 1;
  localparam EN_ECC_RD_A_FALSE = 0;
  localparam EN_ECC_RD_A_TRUE = 1;
  localparam EN_ECC_RD_B_FALSE = 0;
  localparam EN_ECC_RD_B_TRUE = 1;
  localparam EN_ECC_WR_A_FALSE = 0;
  localparam EN_ECC_WR_A_TRUE = 1;
  localparam EN_ECC_WR_B_FALSE = 0;
  localparam EN_ECC_WR_B_TRUE = 1;
  localparam IREG_PRE_A_FALSE = 0;
  localparam IREG_PRE_A_TRUE = 1;
  localparam IREG_PRE_B_FALSE = 0;
  localparam IREG_PRE_B_TRUE = 1;
  localparam OREG_A_FALSE = 0;
  localparam OREG_A_TRUE = 1;
  localparam OREG_B_FALSE = 0;
  localparam OREG_B_TRUE = 1;
  localparam OREG_ECC_A_FALSE = 0;
  localparam OREG_ECC_A_TRUE = 1;
  localparam OREG_ECC_B_FALSE = 0;
  localparam OREG_ECC_B_TRUE = 1;
  localparam REG_CAS_A_FALSE = 0;
  localparam REG_CAS_A_TRUE = 1;
  localparam REG_CAS_B_FALSE = 0;
  localparam REG_CAS_B_TRUE = 1;
  localparam RST_MODE_A_ASYNC = 1;
  localparam RST_MODE_A_SYNC = 0;
  localparam RST_MODE_B_ASYNC = 1;
  localparam RST_MODE_B_SYNC = 0;
  localparam USE_EXT_CE_A_FALSE = 0;
  localparam USE_EXT_CE_A_TRUE = 1;
  localparam USE_EXT_CE_B_FALSE = 0;
  localparam USE_EXT_CE_B_TRUE = 1;

  reg trig_attr;
// include dynamic registers - XILINX test only
`ifdef XIL_DR
  `include "URAM288_dr.v"
`else
  reg [31:0] AUTO_SLEEP_LATENCY_REG = AUTO_SLEEP_LATENCY;
  reg [31:0] AVG_CONS_INACTIVE_CYCLES_REG = AVG_CONS_INACTIVE_CYCLES;
  reg [144:1] BWE_MODE_A_REG = BWE_MODE_A;
  reg [144:1] BWE_MODE_B_REG = BWE_MODE_B;
  reg [48:1] CASCADE_ORDER_A_REG = CASCADE_ORDER_A;
  reg [48:1] CASCADE_ORDER_B_REG = CASCADE_ORDER_B;
  reg [40:1] EN_AUTO_SLEEP_MODE_REG = EN_AUTO_SLEEP_MODE;
  reg [40:1] EN_ECC_RD_A_REG = EN_ECC_RD_A;
  reg [40:1] EN_ECC_RD_B_REG = EN_ECC_RD_B;
  reg [40:1] EN_ECC_WR_A_REG = EN_ECC_WR_A;
  reg [40:1] EN_ECC_WR_B_REG = EN_ECC_WR_B;
  reg [40:1] IREG_PRE_A_REG = IREG_PRE_A;
  reg [40:1] IREG_PRE_B_REG = IREG_PRE_B;
  reg [0:0] IS_CLK_INVERTED_REG = IS_CLK_INVERTED;
  reg [0:0] IS_EN_A_INVERTED_REG = IS_EN_A_INVERTED;
  reg [0:0] IS_EN_B_INVERTED_REG = IS_EN_B_INVERTED;
  reg [0:0] IS_RDB_WR_A_INVERTED_REG = IS_RDB_WR_A_INVERTED;
  reg [0:0] IS_RDB_WR_B_INVERTED_REG = IS_RDB_WR_B_INVERTED;
  reg [0:0] IS_RST_A_INVERTED_REG = IS_RST_A_INVERTED;
  reg [0:0] IS_RST_B_INVERTED_REG = IS_RST_B_INVERTED;
  reg [32:1] MATRIX_ID_REG = MATRIX_ID;
  reg [31:0] NUM_UNIQUE_SELF_ADDR_A_REG = NUM_UNIQUE_SELF_ADDR_A;
  reg [31:0] NUM_UNIQUE_SELF_ADDR_B_REG = NUM_UNIQUE_SELF_ADDR_B;
  reg [31:0] NUM_URAM_IN_MATRIX_REG = NUM_URAM_IN_MATRIX;
  reg [40:1] OREG_A_REG = OREG_A;
  reg [40:1] OREG_B_REG = OREG_B;
  reg [40:1] OREG_ECC_A_REG = OREG_ECC_A;
  reg [40:1] OREG_ECC_B_REG = OREG_ECC_B;
  reg [40:1] REG_CAS_A_REG = REG_CAS_A;
  reg [40:1] REG_CAS_B_REG = REG_CAS_B;
  reg [40:1] RST_MODE_A_REG = RST_MODE_A;
  reg [40:1] RST_MODE_B_REG = RST_MODE_B;
  reg [10:0] SELF_ADDR_A_REG = SELF_ADDR_A;
  reg [10:0] SELF_ADDR_B_REG = SELF_ADDR_B;
  reg [10:0] SELF_MASK_A_REG = SELF_MASK_A;
  reg [10:0] SELF_MASK_B_REG = SELF_MASK_B;
  reg [40:1] USE_EXT_CE_A_REG = USE_EXT_CE_A;
  reg [40:1] USE_EXT_CE_B_REG = USE_EXT_CE_B;
`endif

`ifdef XIL_XECLIB
  wire [3:0] AUTO_SLEEP_LATENCY_BIN;
  wire [16:0] AVG_CONS_INACTIVE_CYCLES_BIN;
  wire BWE_MODE_A_BIN;
  wire BWE_MODE_B_BIN;
  wire [1:0] CASCADE_ORDER_A_BIN;
  wire [1:0] CASCADE_ORDER_B_BIN;
  wire EN_AUTO_SLEEP_MODE_BIN;
  wire EN_ECC_RD_A_BIN;
  wire EN_ECC_RD_B_BIN;
  wire EN_ECC_WR_A_BIN;
  wire EN_ECC_WR_B_BIN;
  wire IREG_PRE_A_BIN;
  wire IREG_PRE_B_BIN;
  wire [11:0] NUM_UNIQUE_SELF_ADDR_A_BIN;
  wire [11:0] NUM_UNIQUE_SELF_ADDR_B_BIN;
  wire [11:0] NUM_URAM_IN_MATRIX_BIN;
  wire OREG_A_BIN;
  wire OREG_B_BIN;
  wire OREG_ECC_A_BIN;
  wire OREG_ECC_B_BIN;
  wire REG_CAS_A_BIN;
  wire REG_CAS_B_BIN;
  wire RST_MODE_A_BIN;
  wire RST_MODE_B_BIN;
  wire USE_EXT_CE_A_BIN;
  wire USE_EXT_CE_B_BIN;
`else
  reg [3:0] AUTO_SLEEP_LATENCY_BIN;
  reg [16:0] AVG_CONS_INACTIVE_CYCLES_BIN;
  reg BWE_MODE_A_BIN;
  reg BWE_MODE_B_BIN;
  reg [1:0] CASCADE_ORDER_A_BIN;
  reg [1:0] CASCADE_ORDER_B_BIN;
  reg EN_AUTO_SLEEP_MODE_BIN;
  reg EN_ECC_RD_A_BIN;
  reg EN_ECC_RD_B_BIN;
  reg EN_ECC_WR_A_BIN;
  reg EN_ECC_WR_B_BIN;
  reg IREG_PRE_A_BIN;
  reg IREG_PRE_B_BIN;
  reg [11:0] NUM_UNIQUE_SELF_ADDR_A_BIN;
  reg [11:0] NUM_UNIQUE_SELF_ADDR_B_BIN;
  reg [11:0] NUM_URAM_IN_MATRIX_BIN;
  reg OREG_A_BIN;
  reg OREG_B_BIN;
  reg OREG_ECC_A_BIN;
  reg OREG_ECC_B_BIN;
  reg REG_CAS_A_BIN;
  reg REG_CAS_B_BIN;
  reg RST_MODE_A_BIN;
  reg RST_MODE_B_BIN;
  reg USE_EXT_CE_A_BIN;
  reg USE_EXT_CE_B_BIN;
`endif

`ifdef XIL_XECLIB
  reg glblGSR = 1'b0;
`else
  tri0 glblGSR = glbl.GSR;
`endif

  wire CAS_IN_DBITERR_A_in;
  wire CAS_IN_DBITERR_B_in;
  wire CAS_IN_EN_A_in;
  wire CAS_IN_EN_B_in;
  wire CAS_IN_RDACCESS_A_in;
  wire CAS_IN_RDACCESS_B_in;
  wire CAS_IN_RDB_WR_A_in;
  wire CAS_IN_RDB_WR_B_in;
  wire CAS_IN_SBITERR_A_in;
  wire CAS_IN_SBITERR_B_in;
  wire CLK_in;
  wire EN_A_in;
  wire EN_B_in;
  wire INJECT_DBITERR_A_in;
  wire INJECT_DBITERR_B_in;
  wire INJECT_SBITERR_A_in;
  wire INJECT_SBITERR_B_in;
  wire OREG_CE_A_in;
  wire OREG_CE_B_in;
  wire OREG_ECC_CE_A_in;
  wire OREG_ECC_CE_B_in;
  wire RDB_WR_A_in;
  wire RDB_WR_B_in;
  wire RST_A_in;
  wire RST_B_in;
  wire SLEEP_in;
  wire [22:0] ADDR_A_in;
  wire [22:0] ADDR_B_in;
  wire [22:0] CAS_IN_ADDR_A_in;
  wire [22:0] CAS_IN_ADDR_B_in;
  wire [71:0] CAS_IN_DIN_A_in;
  wire [71:0] CAS_IN_DIN_B_in;
  wire [71:0] CAS_IN_DOUT_A_in;
  wire [71:0] CAS_IN_DOUT_B_in;
  wire [71:0] DIN_A_in;
  wire [71:0] DIN_B_in;
  wire [8:0] BWE_A_in;
  wire [8:0] BWE_B_in;
  wire [8:0] CAS_IN_BWE_A_in;
  wire [8:0] CAS_IN_BWE_B_in;

`ifdef XIL_TIMING
  wire CAS_IN_DBITERR_A_delay;
  wire CAS_IN_DBITERR_B_delay;
  wire CAS_IN_EN_A_delay;
  wire CAS_IN_EN_B_delay;
  wire CAS_IN_RDACCESS_A_delay;
  wire CAS_IN_RDACCESS_B_delay;
  wire CAS_IN_RDB_WR_A_delay;
  wire CAS_IN_RDB_WR_B_delay;
  wire CAS_IN_SBITERR_A_delay;
  wire CAS_IN_SBITERR_B_delay;
  wire CLK_delay;
  wire EN_A_delay;
  wire EN_B_delay;
  wire INJECT_DBITERR_A_delay;
  wire INJECT_DBITERR_B_delay;
  wire INJECT_SBITERR_A_delay;
  wire INJECT_SBITERR_B_delay;
  wire OREG_CE_A_delay;
  wire OREG_CE_B_delay;
  wire OREG_ECC_CE_A_delay;
  wire OREG_ECC_CE_B_delay;
  wire RDB_WR_A_delay;
  wire RDB_WR_B_delay;
  wire RST_A_delay;
  wire RST_B_delay;
  wire SLEEP_delay;
  wire [22:0] ADDR_A_delay;
  wire [22:0] ADDR_B_delay;
  wire [22:0] CAS_IN_ADDR_A_delay;
  wire [22:0] CAS_IN_ADDR_B_delay;
  wire [71:0] CAS_IN_DIN_A_delay;
  wire [71:0] CAS_IN_DIN_B_delay;
  wire [71:0] CAS_IN_DOUT_A_delay;
  wire [71:0] CAS_IN_DOUT_B_delay;
  wire [71:0] DIN_A_delay;
  wire [71:0] DIN_B_delay;
  wire [8:0] BWE_A_delay;
  wire [8:0] BWE_B_delay;
  wire [8:0] CAS_IN_BWE_A_delay;
  wire [8:0] CAS_IN_BWE_B_delay;
`endif

`ifdef XIL_TIMING
  assign ADDR_A_in = ADDR_A_delay;
  assign ADDR_B_in = ADDR_B_delay;
  assign BWE_A_in = BWE_A_delay;
  assign BWE_B_in = BWE_B_delay;
  assign CAS_IN_ADDR_A_in[0] = (CAS_IN_ADDR_A[0] !== 1'bz) && CAS_IN_ADDR_A_delay[0]; // rv 0
  assign CAS_IN_ADDR_A_in[10] = (CAS_IN_ADDR_A[10] !== 1'bz) && CAS_IN_ADDR_A_delay[10]; // rv 0
  assign CAS_IN_ADDR_A_in[11] = (CAS_IN_ADDR_A[11] !== 1'bz) && CAS_IN_ADDR_A_delay[11]; // rv 0
  assign CAS_IN_ADDR_A_in[12] = (CAS_IN_ADDR_A[12] !== 1'bz) && CAS_IN_ADDR_A_delay[12]; // rv 0
  assign CAS_IN_ADDR_A_in[13] = (CAS_IN_ADDR_A[13] !== 1'bz) && CAS_IN_ADDR_A_delay[13]; // rv 0
  assign CAS_IN_ADDR_A_in[14] = (CAS_IN_ADDR_A[14] !== 1'bz) && CAS_IN_ADDR_A_delay[14]; // rv 0
  assign CAS_IN_ADDR_A_in[15] = (CAS_IN_ADDR_A[15] !== 1'bz) && CAS_IN_ADDR_A_delay[15]; // rv 0
  assign CAS_IN_ADDR_A_in[16] = (CAS_IN_ADDR_A[16] !== 1'bz) && CAS_IN_ADDR_A_delay[16]; // rv 0
  assign CAS_IN_ADDR_A_in[17] = (CAS_IN_ADDR_A[17] !== 1'bz) && CAS_IN_ADDR_A_delay[17]; // rv 0
  assign CAS_IN_ADDR_A_in[18] = (CAS_IN_ADDR_A[18] !== 1'bz) && CAS_IN_ADDR_A_delay[18]; // rv 0
  assign CAS_IN_ADDR_A_in[19] = (CAS_IN_ADDR_A[19] !== 1'bz) && CAS_IN_ADDR_A_delay[19]; // rv 0
  assign CAS_IN_ADDR_A_in[1] = (CAS_IN_ADDR_A[1] !== 1'bz) && CAS_IN_ADDR_A_delay[1]; // rv 0
  assign CAS_IN_ADDR_A_in[20] = (CAS_IN_ADDR_A[20] !== 1'bz) && CAS_IN_ADDR_A_delay[20]; // rv 0
  assign CAS_IN_ADDR_A_in[21] = (CAS_IN_ADDR_A[21] !== 1'bz) && CAS_IN_ADDR_A_delay[21]; // rv 0
  assign CAS_IN_ADDR_A_in[22] = (CAS_IN_ADDR_A[22] !== 1'bz) && CAS_IN_ADDR_A_delay[22]; // rv 0
  assign CAS_IN_ADDR_A_in[2] = (CAS_IN_ADDR_A[2] !== 1'bz) && CAS_IN_ADDR_A_delay[2]; // rv 0
  assign CAS_IN_ADDR_A_in[3] = (CAS_IN_ADDR_A[3] !== 1'bz) && CAS_IN_ADDR_A_delay[3]; // rv 0
  assign CAS_IN_ADDR_A_in[4] = (CAS_IN_ADDR_A[4] !== 1'bz) && CAS_IN_ADDR_A_delay[4]; // rv 0
  assign CAS_IN_ADDR_A_in[5] = (CAS_IN_ADDR_A[5] !== 1'bz) && CAS_IN_ADDR_A_delay[5]; // rv 0
  assign CAS_IN_ADDR_A_in[6] = (CAS_IN_ADDR_A[6] !== 1'bz) && CAS_IN_ADDR_A_delay[6]; // rv 0
  assign CAS_IN_ADDR_A_in[7] = (CAS_IN_ADDR_A[7] !== 1'bz) && CAS_IN_ADDR_A_delay[7]; // rv 0
  assign CAS_IN_ADDR_A_in[8] = (CAS_IN_ADDR_A[8] !== 1'bz) && CAS_IN_ADDR_A_delay[8]; // rv 0
  assign CAS_IN_ADDR_A_in[9] = (CAS_IN_ADDR_A[9] !== 1'bz) && CAS_IN_ADDR_A_delay[9]; // rv 0
  assign CAS_IN_ADDR_B_in[0] = (CAS_IN_ADDR_B[0] !== 1'bz) && CAS_IN_ADDR_B_delay[0]; // rv 0
  assign CAS_IN_ADDR_B_in[10] = (CAS_IN_ADDR_B[10] !== 1'bz) && CAS_IN_ADDR_B_delay[10]; // rv 0
  assign CAS_IN_ADDR_B_in[11] = (CAS_IN_ADDR_B[11] !== 1'bz) && CAS_IN_ADDR_B_delay[11]; // rv 0
  assign CAS_IN_ADDR_B_in[12] = (CAS_IN_ADDR_B[12] !== 1'bz) && CAS_IN_ADDR_B_delay[12]; // rv 0
  assign CAS_IN_ADDR_B_in[13] = (CAS_IN_ADDR_B[13] !== 1'bz) && CAS_IN_ADDR_B_delay[13]; // rv 0
  assign CAS_IN_ADDR_B_in[14] = (CAS_IN_ADDR_B[14] !== 1'bz) && CAS_IN_ADDR_B_delay[14]; // rv 0
  assign CAS_IN_ADDR_B_in[15] = (CAS_IN_ADDR_B[15] !== 1'bz) && CAS_IN_ADDR_B_delay[15]; // rv 0
  assign CAS_IN_ADDR_B_in[16] = (CAS_IN_ADDR_B[16] !== 1'bz) && CAS_IN_ADDR_B_delay[16]; // rv 0
  assign CAS_IN_ADDR_B_in[17] = (CAS_IN_ADDR_B[17] !== 1'bz) && CAS_IN_ADDR_B_delay[17]; // rv 0
  assign CAS_IN_ADDR_B_in[18] = (CAS_IN_ADDR_B[18] !== 1'bz) && CAS_IN_ADDR_B_delay[18]; // rv 0
  assign CAS_IN_ADDR_B_in[19] = (CAS_IN_ADDR_B[19] !== 1'bz) && CAS_IN_ADDR_B_delay[19]; // rv 0
  assign CAS_IN_ADDR_B_in[1] = (CAS_IN_ADDR_B[1] !== 1'bz) && CAS_IN_ADDR_B_delay[1]; // rv 0
  assign CAS_IN_ADDR_B_in[20] = (CAS_IN_ADDR_B[20] !== 1'bz) && CAS_IN_ADDR_B_delay[20]; // rv 0
  assign CAS_IN_ADDR_B_in[21] = (CAS_IN_ADDR_B[21] !== 1'bz) && CAS_IN_ADDR_B_delay[21]; // rv 0
  assign CAS_IN_ADDR_B_in[22] = (CAS_IN_ADDR_B[22] !== 1'bz) && CAS_IN_ADDR_B_delay[22]; // rv 0
  assign CAS_IN_ADDR_B_in[2] = (CAS_IN_ADDR_B[2] !== 1'bz) && CAS_IN_ADDR_B_delay[2]; // rv 0
  assign CAS_IN_ADDR_B_in[3] = (CAS_IN_ADDR_B[3] !== 1'bz) && CAS_IN_ADDR_B_delay[3]; // rv 0
  assign CAS_IN_ADDR_B_in[4] = (CAS_IN_ADDR_B[4] !== 1'bz) && CAS_IN_ADDR_B_delay[4]; // rv 0
  assign CAS_IN_ADDR_B_in[5] = (CAS_IN_ADDR_B[5] !== 1'bz) && CAS_IN_ADDR_B_delay[5]; // rv 0
  assign CAS_IN_ADDR_B_in[6] = (CAS_IN_ADDR_B[6] !== 1'bz) && CAS_IN_ADDR_B_delay[6]; // rv 0
  assign CAS_IN_ADDR_B_in[7] = (CAS_IN_ADDR_B[7] !== 1'bz) && CAS_IN_ADDR_B_delay[7]; // rv 0
  assign CAS_IN_ADDR_B_in[8] = (CAS_IN_ADDR_B[8] !== 1'bz) && CAS_IN_ADDR_B_delay[8]; // rv 0
  assign CAS_IN_ADDR_B_in[9] = (CAS_IN_ADDR_B[9] !== 1'bz) && CAS_IN_ADDR_B_delay[9]; // rv 0
  assign CAS_IN_BWE_A_in[0] = (CAS_IN_BWE_A[0] !== 1'bz) && CAS_IN_BWE_A_delay[0]; // rv 0
  assign CAS_IN_BWE_A_in[1] = (CAS_IN_BWE_A[1] !== 1'bz) && CAS_IN_BWE_A_delay[1]; // rv 0
  assign CAS_IN_BWE_A_in[2] = (CAS_IN_BWE_A[2] !== 1'bz) && CAS_IN_BWE_A_delay[2]; // rv 0
  assign CAS_IN_BWE_A_in[3] = (CAS_IN_BWE_A[3] !== 1'bz) && CAS_IN_BWE_A_delay[3]; // rv 0
  assign CAS_IN_BWE_A_in[4] = (CAS_IN_BWE_A[4] !== 1'bz) && CAS_IN_BWE_A_delay[4]; // rv 0
  assign CAS_IN_BWE_A_in[5] = (CAS_IN_BWE_A[5] !== 1'bz) && CAS_IN_BWE_A_delay[5]; // rv 0
  assign CAS_IN_BWE_A_in[6] = (CAS_IN_BWE_A[6] !== 1'bz) && CAS_IN_BWE_A_delay[6]; // rv 0
  assign CAS_IN_BWE_A_in[7] = (CAS_IN_BWE_A[7] !== 1'bz) && CAS_IN_BWE_A_delay[7]; // rv 0
  assign CAS_IN_BWE_A_in[8] = (CAS_IN_BWE_A[8] !== 1'bz) && CAS_IN_BWE_A_delay[8]; // rv 0
  assign CAS_IN_BWE_B_in[0] = (CAS_IN_BWE_B[0] !== 1'bz) && CAS_IN_BWE_B_delay[0]; // rv 0
  assign CAS_IN_BWE_B_in[1] = (CAS_IN_BWE_B[1] !== 1'bz) && CAS_IN_BWE_B_delay[1]; // rv 0
  assign CAS_IN_BWE_B_in[2] = (CAS_IN_BWE_B[2] !== 1'bz) && CAS_IN_BWE_B_delay[2]; // rv 0
  assign CAS_IN_BWE_B_in[3] = (CAS_IN_BWE_B[3] !== 1'bz) && CAS_IN_BWE_B_delay[3]; // rv 0
  assign CAS_IN_BWE_B_in[4] = (CAS_IN_BWE_B[4] !== 1'bz) && CAS_IN_BWE_B_delay[4]; // rv 0
  assign CAS_IN_BWE_B_in[5] = (CAS_IN_BWE_B[5] !== 1'bz) && CAS_IN_BWE_B_delay[5]; // rv 0
  assign CAS_IN_BWE_B_in[6] = (CAS_IN_BWE_B[6] !== 1'bz) && CAS_IN_BWE_B_delay[6]; // rv 0
  assign CAS_IN_BWE_B_in[7] = (CAS_IN_BWE_B[7] !== 1'bz) && CAS_IN_BWE_B_delay[7]; // rv 0
  assign CAS_IN_BWE_B_in[8] = (CAS_IN_BWE_B[8] !== 1'bz) && CAS_IN_BWE_B_delay[8]; // rv 0
  assign CAS_IN_DBITERR_A_in = (CAS_IN_DBITERR_A !== 1'bz) && CAS_IN_DBITERR_A_delay; // rv 0
  assign CAS_IN_DBITERR_B_in = (CAS_IN_DBITERR_B !== 1'bz) && CAS_IN_DBITERR_B_delay; // rv 0
  assign CAS_IN_DIN_A_in[0] = (CAS_IN_DIN_A[0] !== 1'bz) && CAS_IN_DIN_A_delay[0]; // rv 0
  assign CAS_IN_DIN_A_in[10] = (CAS_IN_DIN_A[10] !== 1'bz) && CAS_IN_DIN_A_delay[10]; // rv 0
  assign CAS_IN_DIN_A_in[11] = (CAS_IN_DIN_A[11] !== 1'bz) && CAS_IN_DIN_A_delay[11]; // rv 0
  assign CAS_IN_DIN_A_in[12] = (CAS_IN_DIN_A[12] !== 1'bz) && CAS_IN_DIN_A_delay[12]; // rv 0
  assign CAS_IN_DIN_A_in[13] = (CAS_IN_DIN_A[13] !== 1'bz) && CAS_IN_DIN_A_delay[13]; // rv 0
  assign CAS_IN_DIN_A_in[14] = (CAS_IN_DIN_A[14] !== 1'bz) && CAS_IN_DIN_A_delay[14]; // rv 0
  assign CAS_IN_DIN_A_in[15] = (CAS_IN_DIN_A[15] !== 1'bz) && CAS_IN_DIN_A_delay[15]; // rv 0
  assign CAS_IN_DIN_A_in[16] = (CAS_IN_DIN_A[16] !== 1'bz) && CAS_IN_DIN_A_delay[16]; // rv 0
  assign CAS_IN_DIN_A_in[17] = (CAS_IN_DIN_A[17] !== 1'bz) && CAS_IN_DIN_A_delay[17]; // rv 0
  assign CAS_IN_DIN_A_in[18] = (CAS_IN_DIN_A[18] !== 1'bz) && CAS_IN_DIN_A_delay[18]; // rv 0
  assign CAS_IN_DIN_A_in[19] = (CAS_IN_DIN_A[19] !== 1'bz) && CAS_IN_DIN_A_delay[19]; // rv 0
  assign CAS_IN_DIN_A_in[1] = (CAS_IN_DIN_A[1] !== 1'bz) && CAS_IN_DIN_A_delay[1]; // rv 0
  assign CAS_IN_DIN_A_in[20] = (CAS_IN_DIN_A[20] !== 1'bz) && CAS_IN_DIN_A_delay[20]; // rv 0
  assign CAS_IN_DIN_A_in[21] = (CAS_IN_DIN_A[21] !== 1'bz) && CAS_IN_DIN_A_delay[21]; // rv 0
  assign CAS_IN_DIN_A_in[22] = (CAS_IN_DIN_A[22] !== 1'bz) && CAS_IN_DIN_A_delay[22]; // rv 0
  assign CAS_IN_DIN_A_in[23] = (CAS_IN_DIN_A[23] !== 1'bz) && CAS_IN_DIN_A_delay[23]; // rv 0
  assign CAS_IN_DIN_A_in[24] = (CAS_IN_DIN_A[24] !== 1'bz) && CAS_IN_DIN_A_delay[24]; // rv 0
  assign CAS_IN_DIN_A_in[25] = (CAS_IN_DIN_A[25] !== 1'bz) && CAS_IN_DIN_A_delay[25]; // rv 0
  assign CAS_IN_DIN_A_in[26] = (CAS_IN_DIN_A[26] !== 1'bz) && CAS_IN_DIN_A_delay[26]; // rv 0
  assign CAS_IN_DIN_A_in[27] = (CAS_IN_DIN_A[27] !== 1'bz) && CAS_IN_DIN_A_delay[27]; // rv 0
  assign CAS_IN_DIN_A_in[28] = (CAS_IN_DIN_A[28] !== 1'bz) && CAS_IN_DIN_A_delay[28]; // rv 0
  assign CAS_IN_DIN_A_in[29] = (CAS_IN_DIN_A[29] !== 1'bz) && CAS_IN_DIN_A_delay[29]; // rv 0
  assign CAS_IN_DIN_A_in[2] = (CAS_IN_DIN_A[2] !== 1'bz) && CAS_IN_DIN_A_delay[2]; // rv 0
  assign CAS_IN_DIN_A_in[30] = (CAS_IN_DIN_A[30] !== 1'bz) && CAS_IN_DIN_A_delay[30]; // rv 0
  assign CAS_IN_DIN_A_in[31] = (CAS_IN_DIN_A[31] !== 1'bz) && CAS_IN_DIN_A_delay[31]; // rv 0
  assign CAS_IN_DIN_A_in[32] = (CAS_IN_DIN_A[32] !== 1'bz) && CAS_IN_DIN_A_delay[32]; // rv 0
  assign CAS_IN_DIN_A_in[33] = (CAS_IN_DIN_A[33] !== 1'bz) && CAS_IN_DIN_A_delay[33]; // rv 0
  assign CAS_IN_DIN_A_in[34] = (CAS_IN_DIN_A[34] !== 1'bz) && CAS_IN_DIN_A_delay[34]; // rv 0
  assign CAS_IN_DIN_A_in[35] = (CAS_IN_DIN_A[35] !== 1'bz) && CAS_IN_DIN_A_delay[35]; // rv 0
  assign CAS_IN_DIN_A_in[36] = (CAS_IN_DIN_A[36] !== 1'bz) && CAS_IN_DIN_A_delay[36]; // rv 0
  assign CAS_IN_DIN_A_in[37] = (CAS_IN_DIN_A[37] !== 1'bz) && CAS_IN_DIN_A_delay[37]; // rv 0
  assign CAS_IN_DIN_A_in[38] = (CAS_IN_DIN_A[38] !== 1'bz) && CAS_IN_DIN_A_delay[38]; // rv 0
  assign CAS_IN_DIN_A_in[39] = (CAS_IN_DIN_A[39] !== 1'bz) && CAS_IN_DIN_A_delay[39]; // rv 0
  assign CAS_IN_DIN_A_in[3] = (CAS_IN_DIN_A[3] !== 1'bz) && CAS_IN_DIN_A_delay[3]; // rv 0
  assign CAS_IN_DIN_A_in[40] = (CAS_IN_DIN_A[40] !== 1'bz) && CAS_IN_DIN_A_delay[40]; // rv 0
  assign CAS_IN_DIN_A_in[41] = (CAS_IN_DIN_A[41] !== 1'bz) && CAS_IN_DIN_A_delay[41]; // rv 0
  assign CAS_IN_DIN_A_in[42] = (CAS_IN_DIN_A[42] !== 1'bz) && CAS_IN_DIN_A_delay[42]; // rv 0
  assign CAS_IN_DIN_A_in[43] = (CAS_IN_DIN_A[43] !== 1'bz) && CAS_IN_DIN_A_delay[43]; // rv 0
  assign CAS_IN_DIN_A_in[44] = (CAS_IN_DIN_A[44] !== 1'bz) && CAS_IN_DIN_A_delay[44]; // rv 0
  assign CAS_IN_DIN_A_in[45] = (CAS_IN_DIN_A[45] !== 1'bz) && CAS_IN_DIN_A_delay[45]; // rv 0
  assign CAS_IN_DIN_A_in[46] = (CAS_IN_DIN_A[46] !== 1'bz) && CAS_IN_DIN_A_delay[46]; // rv 0
  assign CAS_IN_DIN_A_in[47] = (CAS_IN_DIN_A[47] !== 1'bz) && CAS_IN_DIN_A_delay[47]; // rv 0
  assign CAS_IN_DIN_A_in[48] = (CAS_IN_DIN_A[48] !== 1'bz) && CAS_IN_DIN_A_delay[48]; // rv 0
  assign CAS_IN_DIN_A_in[49] = (CAS_IN_DIN_A[49] !== 1'bz) && CAS_IN_DIN_A_delay[49]; // rv 0
  assign CAS_IN_DIN_A_in[4] = (CAS_IN_DIN_A[4] !== 1'bz) && CAS_IN_DIN_A_delay[4]; // rv 0
  assign CAS_IN_DIN_A_in[50] = (CAS_IN_DIN_A[50] !== 1'bz) && CAS_IN_DIN_A_delay[50]; // rv 0
  assign CAS_IN_DIN_A_in[51] = (CAS_IN_DIN_A[51] !== 1'bz) && CAS_IN_DIN_A_delay[51]; // rv 0
  assign CAS_IN_DIN_A_in[52] = (CAS_IN_DIN_A[52] !== 1'bz) && CAS_IN_DIN_A_delay[52]; // rv 0
  assign CAS_IN_DIN_A_in[53] = (CAS_IN_DIN_A[53] !== 1'bz) && CAS_IN_DIN_A_delay[53]; // rv 0
  assign CAS_IN_DIN_A_in[54] = (CAS_IN_DIN_A[54] !== 1'bz) && CAS_IN_DIN_A_delay[54]; // rv 0
  assign CAS_IN_DIN_A_in[55] = (CAS_IN_DIN_A[55] !== 1'bz) && CAS_IN_DIN_A_delay[55]; // rv 0
  assign CAS_IN_DIN_A_in[56] = (CAS_IN_DIN_A[56] !== 1'bz) && CAS_IN_DIN_A_delay[56]; // rv 0
  assign CAS_IN_DIN_A_in[57] = (CAS_IN_DIN_A[57] !== 1'bz) && CAS_IN_DIN_A_delay[57]; // rv 0
  assign CAS_IN_DIN_A_in[58] = (CAS_IN_DIN_A[58] !== 1'bz) && CAS_IN_DIN_A_delay[58]; // rv 0
  assign CAS_IN_DIN_A_in[59] = (CAS_IN_DIN_A[59] !== 1'bz) && CAS_IN_DIN_A_delay[59]; // rv 0
  assign CAS_IN_DIN_A_in[5] = (CAS_IN_DIN_A[5] !== 1'bz) && CAS_IN_DIN_A_delay[5]; // rv 0
  assign CAS_IN_DIN_A_in[60] = (CAS_IN_DIN_A[60] !== 1'bz) && CAS_IN_DIN_A_delay[60]; // rv 0
  assign CAS_IN_DIN_A_in[61] = (CAS_IN_DIN_A[61] !== 1'bz) && CAS_IN_DIN_A_delay[61]; // rv 0
  assign CAS_IN_DIN_A_in[62] = (CAS_IN_DIN_A[62] !== 1'bz) && CAS_IN_DIN_A_delay[62]; // rv 0
  assign CAS_IN_DIN_A_in[63] = (CAS_IN_DIN_A[63] !== 1'bz) && CAS_IN_DIN_A_delay[63]; // rv 0
  assign CAS_IN_DIN_A_in[64] = (CAS_IN_DIN_A[64] !== 1'bz) && CAS_IN_DIN_A_delay[64]; // rv 0
  assign CAS_IN_DIN_A_in[65] = (CAS_IN_DIN_A[65] !== 1'bz) && CAS_IN_DIN_A_delay[65]; // rv 0
  assign CAS_IN_DIN_A_in[66] = (CAS_IN_DIN_A[66] !== 1'bz) && CAS_IN_DIN_A_delay[66]; // rv 0
  assign CAS_IN_DIN_A_in[67] = (CAS_IN_DIN_A[67] !== 1'bz) && CAS_IN_DIN_A_delay[67]; // rv 0
  assign CAS_IN_DIN_A_in[68] = (CAS_IN_DIN_A[68] !== 1'bz) && CAS_IN_DIN_A_delay[68]; // rv 0
  assign CAS_IN_DIN_A_in[69] = (CAS_IN_DIN_A[69] !== 1'bz) && CAS_IN_DIN_A_delay[69]; // rv 0
  assign CAS_IN_DIN_A_in[6] = (CAS_IN_DIN_A[6] !== 1'bz) && CAS_IN_DIN_A_delay[6]; // rv 0
  assign CAS_IN_DIN_A_in[70] = (CAS_IN_DIN_A[70] !== 1'bz) && CAS_IN_DIN_A_delay[70]; // rv 0
  assign CAS_IN_DIN_A_in[71] = (CAS_IN_DIN_A[71] !== 1'bz) && CAS_IN_DIN_A_delay[71]; // rv 0
  assign CAS_IN_DIN_A_in[7] = (CAS_IN_DIN_A[7] !== 1'bz) && CAS_IN_DIN_A_delay[7]; // rv 0
  assign CAS_IN_DIN_A_in[8] = (CAS_IN_DIN_A[8] !== 1'bz) && CAS_IN_DIN_A_delay[8]; // rv 0
  assign CAS_IN_DIN_A_in[9] = (CAS_IN_DIN_A[9] !== 1'bz) && CAS_IN_DIN_A_delay[9]; // rv 0
  assign CAS_IN_DIN_B_in[0] = (CAS_IN_DIN_B[0] !== 1'bz) && CAS_IN_DIN_B_delay[0]; // rv 0
  assign CAS_IN_DIN_B_in[10] = (CAS_IN_DIN_B[10] !== 1'bz) && CAS_IN_DIN_B_delay[10]; // rv 0
  assign CAS_IN_DIN_B_in[11] = (CAS_IN_DIN_B[11] !== 1'bz) && CAS_IN_DIN_B_delay[11]; // rv 0
  assign CAS_IN_DIN_B_in[12] = (CAS_IN_DIN_B[12] !== 1'bz) && CAS_IN_DIN_B_delay[12]; // rv 0
  assign CAS_IN_DIN_B_in[13] = (CAS_IN_DIN_B[13] !== 1'bz) && CAS_IN_DIN_B_delay[13]; // rv 0
  assign CAS_IN_DIN_B_in[14] = (CAS_IN_DIN_B[14] !== 1'bz) && CAS_IN_DIN_B_delay[14]; // rv 0
  assign CAS_IN_DIN_B_in[15] = (CAS_IN_DIN_B[15] !== 1'bz) && CAS_IN_DIN_B_delay[15]; // rv 0
  assign CAS_IN_DIN_B_in[16] = (CAS_IN_DIN_B[16] !== 1'bz) && CAS_IN_DIN_B_delay[16]; // rv 0
  assign CAS_IN_DIN_B_in[17] = (CAS_IN_DIN_B[17] !== 1'bz) && CAS_IN_DIN_B_delay[17]; // rv 0
  assign CAS_IN_DIN_B_in[18] = (CAS_IN_DIN_B[18] !== 1'bz) && CAS_IN_DIN_B_delay[18]; // rv 0
  assign CAS_IN_DIN_B_in[19] = (CAS_IN_DIN_B[19] !== 1'bz) && CAS_IN_DIN_B_delay[19]; // rv 0
  assign CAS_IN_DIN_B_in[1] = (CAS_IN_DIN_B[1] !== 1'bz) && CAS_IN_DIN_B_delay[1]; // rv 0
  assign CAS_IN_DIN_B_in[20] = (CAS_IN_DIN_B[20] !== 1'bz) && CAS_IN_DIN_B_delay[20]; // rv 0
  assign CAS_IN_DIN_B_in[21] = (CAS_IN_DIN_B[21] !== 1'bz) && CAS_IN_DIN_B_delay[21]; // rv 0
  assign CAS_IN_DIN_B_in[22] = (CAS_IN_DIN_B[22] !== 1'bz) && CAS_IN_DIN_B_delay[22]; // rv 0
  assign CAS_IN_DIN_B_in[23] = (CAS_IN_DIN_B[23] !== 1'bz) && CAS_IN_DIN_B_delay[23]; // rv 0
  assign CAS_IN_DIN_B_in[24] = (CAS_IN_DIN_B[24] !== 1'bz) && CAS_IN_DIN_B_delay[24]; // rv 0
  assign CAS_IN_DIN_B_in[25] = (CAS_IN_DIN_B[25] !== 1'bz) && CAS_IN_DIN_B_delay[25]; // rv 0
  assign CAS_IN_DIN_B_in[26] = (CAS_IN_DIN_B[26] !== 1'bz) && CAS_IN_DIN_B_delay[26]; // rv 0
  assign CAS_IN_DIN_B_in[27] = (CAS_IN_DIN_B[27] !== 1'bz) && CAS_IN_DIN_B_delay[27]; // rv 0
  assign CAS_IN_DIN_B_in[28] = (CAS_IN_DIN_B[28] !== 1'bz) && CAS_IN_DIN_B_delay[28]; // rv 0
  assign CAS_IN_DIN_B_in[29] = (CAS_IN_DIN_B[29] !== 1'bz) && CAS_IN_DIN_B_delay[29]; // rv 0
  assign CAS_IN_DIN_B_in[2] = (CAS_IN_DIN_B[2] !== 1'bz) && CAS_IN_DIN_B_delay[2]; // rv 0
  assign CAS_IN_DIN_B_in[30] = (CAS_IN_DIN_B[30] !== 1'bz) && CAS_IN_DIN_B_delay[30]; // rv 0
  assign CAS_IN_DIN_B_in[31] = (CAS_IN_DIN_B[31] !== 1'bz) && CAS_IN_DIN_B_delay[31]; // rv 0
  assign CAS_IN_DIN_B_in[32] = (CAS_IN_DIN_B[32] !== 1'bz) && CAS_IN_DIN_B_delay[32]; // rv 0
  assign CAS_IN_DIN_B_in[33] = (CAS_IN_DIN_B[33] !== 1'bz) && CAS_IN_DIN_B_delay[33]; // rv 0
  assign CAS_IN_DIN_B_in[34] = (CAS_IN_DIN_B[34] !== 1'bz) && CAS_IN_DIN_B_delay[34]; // rv 0
  assign CAS_IN_DIN_B_in[35] = (CAS_IN_DIN_B[35] !== 1'bz) && CAS_IN_DIN_B_delay[35]; // rv 0
  assign CAS_IN_DIN_B_in[36] = (CAS_IN_DIN_B[36] !== 1'bz) && CAS_IN_DIN_B_delay[36]; // rv 0
  assign CAS_IN_DIN_B_in[37] = (CAS_IN_DIN_B[37] !== 1'bz) && CAS_IN_DIN_B_delay[37]; // rv 0
  assign CAS_IN_DIN_B_in[38] = (CAS_IN_DIN_B[38] !== 1'bz) && CAS_IN_DIN_B_delay[38]; // rv 0
  assign CAS_IN_DIN_B_in[39] = (CAS_IN_DIN_B[39] !== 1'bz) && CAS_IN_DIN_B_delay[39]; // rv 0
  assign CAS_IN_DIN_B_in[3] = (CAS_IN_DIN_B[3] !== 1'bz) && CAS_IN_DIN_B_delay[3]; // rv 0
  assign CAS_IN_DIN_B_in[40] = (CAS_IN_DIN_B[40] !== 1'bz) && CAS_IN_DIN_B_delay[40]; // rv 0
  assign CAS_IN_DIN_B_in[41] = (CAS_IN_DIN_B[41] !== 1'bz) && CAS_IN_DIN_B_delay[41]; // rv 0
  assign CAS_IN_DIN_B_in[42] = (CAS_IN_DIN_B[42] !== 1'bz) && CAS_IN_DIN_B_delay[42]; // rv 0
  assign CAS_IN_DIN_B_in[43] = (CAS_IN_DIN_B[43] !== 1'bz) && CAS_IN_DIN_B_delay[43]; // rv 0
  assign CAS_IN_DIN_B_in[44] = (CAS_IN_DIN_B[44] !== 1'bz) && CAS_IN_DIN_B_delay[44]; // rv 0
  assign CAS_IN_DIN_B_in[45] = (CAS_IN_DIN_B[45] !== 1'bz) && CAS_IN_DIN_B_delay[45]; // rv 0
  assign CAS_IN_DIN_B_in[46] = (CAS_IN_DIN_B[46] !== 1'bz) && CAS_IN_DIN_B_delay[46]; // rv 0
  assign CAS_IN_DIN_B_in[47] = (CAS_IN_DIN_B[47] !== 1'bz) && CAS_IN_DIN_B_delay[47]; // rv 0
  assign CAS_IN_DIN_B_in[48] = (CAS_IN_DIN_B[48] !== 1'bz) && CAS_IN_DIN_B_delay[48]; // rv 0
  assign CAS_IN_DIN_B_in[49] = (CAS_IN_DIN_B[49] !== 1'bz) && CAS_IN_DIN_B_delay[49]; // rv 0
  assign CAS_IN_DIN_B_in[4] = (CAS_IN_DIN_B[4] !== 1'bz) && CAS_IN_DIN_B_delay[4]; // rv 0
  assign CAS_IN_DIN_B_in[50] = (CAS_IN_DIN_B[50] !== 1'bz) && CAS_IN_DIN_B_delay[50]; // rv 0
  assign CAS_IN_DIN_B_in[51] = (CAS_IN_DIN_B[51] !== 1'bz) && CAS_IN_DIN_B_delay[51]; // rv 0
  assign CAS_IN_DIN_B_in[52] = (CAS_IN_DIN_B[52] !== 1'bz) && CAS_IN_DIN_B_delay[52]; // rv 0
  assign CAS_IN_DIN_B_in[53] = (CAS_IN_DIN_B[53] !== 1'bz) && CAS_IN_DIN_B_delay[53]; // rv 0
  assign CAS_IN_DIN_B_in[54] = (CAS_IN_DIN_B[54] !== 1'bz) && CAS_IN_DIN_B_delay[54]; // rv 0
  assign CAS_IN_DIN_B_in[55] = (CAS_IN_DIN_B[55] !== 1'bz) && CAS_IN_DIN_B_delay[55]; // rv 0
  assign CAS_IN_DIN_B_in[56] = (CAS_IN_DIN_B[56] !== 1'bz) && CAS_IN_DIN_B_delay[56]; // rv 0
  assign CAS_IN_DIN_B_in[57] = (CAS_IN_DIN_B[57] !== 1'bz) && CAS_IN_DIN_B_delay[57]; // rv 0
  assign CAS_IN_DIN_B_in[58] = (CAS_IN_DIN_B[58] !== 1'bz) && CAS_IN_DIN_B_delay[58]; // rv 0
  assign CAS_IN_DIN_B_in[59] = (CAS_IN_DIN_B[59] !== 1'bz) && CAS_IN_DIN_B_delay[59]; // rv 0
  assign CAS_IN_DIN_B_in[5] = (CAS_IN_DIN_B[5] !== 1'bz) && CAS_IN_DIN_B_delay[5]; // rv 0
  assign CAS_IN_DIN_B_in[60] = (CAS_IN_DIN_B[60] !== 1'bz) && CAS_IN_DIN_B_delay[60]; // rv 0
  assign CAS_IN_DIN_B_in[61] = (CAS_IN_DIN_B[61] !== 1'bz) && CAS_IN_DIN_B_delay[61]; // rv 0
  assign CAS_IN_DIN_B_in[62] = (CAS_IN_DIN_B[62] !== 1'bz) && CAS_IN_DIN_B_delay[62]; // rv 0
  assign CAS_IN_DIN_B_in[63] = (CAS_IN_DIN_B[63] !== 1'bz) && CAS_IN_DIN_B_delay[63]; // rv 0
  assign CAS_IN_DIN_B_in[64] = (CAS_IN_DIN_B[64] !== 1'bz) && CAS_IN_DIN_B_delay[64]; // rv 0
  assign CAS_IN_DIN_B_in[65] = (CAS_IN_DIN_B[65] !== 1'bz) && CAS_IN_DIN_B_delay[65]; // rv 0
  assign CAS_IN_DIN_B_in[66] = (CAS_IN_DIN_B[66] !== 1'bz) && CAS_IN_DIN_B_delay[66]; // rv 0
  assign CAS_IN_DIN_B_in[67] = (CAS_IN_DIN_B[67] !== 1'bz) && CAS_IN_DIN_B_delay[67]; // rv 0
  assign CAS_IN_DIN_B_in[68] = (CAS_IN_DIN_B[68] !== 1'bz) && CAS_IN_DIN_B_delay[68]; // rv 0
  assign CAS_IN_DIN_B_in[69] = (CAS_IN_DIN_B[69] !== 1'bz) && CAS_IN_DIN_B_delay[69]; // rv 0
  assign CAS_IN_DIN_B_in[6] = (CAS_IN_DIN_B[6] !== 1'bz) && CAS_IN_DIN_B_delay[6]; // rv 0
  assign CAS_IN_DIN_B_in[70] = (CAS_IN_DIN_B[70] !== 1'bz) && CAS_IN_DIN_B_delay[70]; // rv 0
  assign CAS_IN_DIN_B_in[71] = (CAS_IN_DIN_B[71] !== 1'bz) && CAS_IN_DIN_B_delay[71]; // rv 0
  assign CAS_IN_DIN_B_in[7] = (CAS_IN_DIN_B[7] !== 1'bz) && CAS_IN_DIN_B_delay[7]; // rv 0
  assign CAS_IN_DIN_B_in[8] = (CAS_IN_DIN_B[8] !== 1'bz) && CAS_IN_DIN_B_delay[8]; // rv 0
  assign CAS_IN_DIN_B_in[9] = (CAS_IN_DIN_B[9] !== 1'bz) && CAS_IN_DIN_B_delay[9]; // rv 0
  assign CAS_IN_DOUT_A_in[0] = (CAS_IN_DOUT_A[0] !== 1'bz) && CAS_IN_DOUT_A_delay[0]; // rv 0
  assign CAS_IN_DOUT_A_in[10] = (CAS_IN_DOUT_A[10] !== 1'bz) && CAS_IN_DOUT_A_delay[10]; // rv 0
  assign CAS_IN_DOUT_A_in[11] = (CAS_IN_DOUT_A[11] !== 1'bz) && CAS_IN_DOUT_A_delay[11]; // rv 0
  assign CAS_IN_DOUT_A_in[12] = (CAS_IN_DOUT_A[12] !== 1'bz) && CAS_IN_DOUT_A_delay[12]; // rv 0
  assign CAS_IN_DOUT_A_in[13] = (CAS_IN_DOUT_A[13] !== 1'bz) && CAS_IN_DOUT_A_delay[13]; // rv 0
  assign CAS_IN_DOUT_A_in[14] = (CAS_IN_DOUT_A[14] !== 1'bz) && CAS_IN_DOUT_A_delay[14]; // rv 0
  assign CAS_IN_DOUT_A_in[15] = (CAS_IN_DOUT_A[15] !== 1'bz) && CAS_IN_DOUT_A_delay[15]; // rv 0
  assign CAS_IN_DOUT_A_in[16] = (CAS_IN_DOUT_A[16] !== 1'bz) && CAS_IN_DOUT_A_delay[16]; // rv 0
  assign CAS_IN_DOUT_A_in[17] = (CAS_IN_DOUT_A[17] !== 1'bz) && CAS_IN_DOUT_A_delay[17]; // rv 0
  assign CAS_IN_DOUT_A_in[18] = (CAS_IN_DOUT_A[18] !== 1'bz) && CAS_IN_DOUT_A_delay[18]; // rv 0
  assign CAS_IN_DOUT_A_in[19] = (CAS_IN_DOUT_A[19] !== 1'bz) && CAS_IN_DOUT_A_delay[19]; // rv 0
  assign CAS_IN_DOUT_A_in[1] = (CAS_IN_DOUT_A[1] !== 1'bz) && CAS_IN_DOUT_A_delay[1]; // rv 0
  assign CAS_IN_DOUT_A_in[20] = (CAS_IN_DOUT_A[20] !== 1'bz) && CAS_IN_DOUT_A_delay[20]; // rv 0
  assign CAS_IN_DOUT_A_in[21] = (CAS_IN_DOUT_A[21] !== 1'bz) && CAS_IN_DOUT_A_delay[21]; // rv 0
  assign CAS_IN_DOUT_A_in[22] = (CAS_IN_DOUT_A[22] !== 1'bz) && CAS_IN_DOUT_A_delay[22]; // rv 0
  assign CAS_IN_DOUT_A_in[23] = (CAS_IN_DOUT_A[23] !== 1'bz) && CAS_IN_DOUT_A_delay[23]; // rv 0
  assign CAS_IN_DOUT_A_in[24] = (CAS_IN_DOUT_A[24] !== 1'bz) && CAS_IN_DOUT_A_delay[24]; // rv 0
  assign CAS_IN_DOUT_A_in[25] = (CAS_IN_DOUT_A[25] !== 1'bz) && CAS_IN_DOUT_A_delay[25]; // rv 0
  assign CAS_IN_DOUT_A_in[26] = (CAS_IN_DOUT_A[26] !== 1'bz) && CAS_IN_DOUT_A_delay[26]; // rv 0
  assign CAS_IN_DOUT_A_in[27] = (CAS_IN_DOUT_A[27] !== 1'bz) && CAS_IN_DOUT_A_delay[27]; // rv 0
  assign CAS_IN_DOUT_A_in[28] = (CAS_IN_DOUT_A[28] !== 1'bz) && CAS_IN_DOUT_A_delay[28]; // rv 0
  assign CAS_IN_DOUT_A_in[29] = (CAS_IN_DOUT_A[29] !== 1'bz) && CAS_IN_DOUT_A_delay[29]; // rv 0
  assign CAS_IN_DOUT_A_in[2] = (CAS_IN_DOUT_A[2] !== 1'bz) && CAS_IN_DOUT_A_delay[2]; // rv 0
  assign CAS_IN_DOUT_A_in[30] = (CAS_IN_DOUT_A[30] !== 1'bz) && CAS_IN_DOUT_A_delay[30]; // rv 0
  assign CAS_IN_DOUT_A_in[31] = (CAS_IN_DOUT_A[31] !== 1'bz) && CAS_IN_DOUT_A_delay[31]; // rv 0
  assign CAS_IN_DOUT_A_in[32] = (CAS_IN_DOUT_A[32] !== 1'bz) && CAS_IN_DOUT_A_delay[32]; // rv 0
  assign CAS_IN_DOUT_A_in[33] = (CAS_IN_DOUT_A[33] !== 1'bz) && CAS_IN_DOUT_A_delay[33]; // rv 0
  assign CAS_IN_DOUT_A_in[34] = (CAS_IN_DOUT_A[34] !== 1'bz) && CAS_IN_DOUT_A_delay[34]; // rv 0
  assign CAS_IN_DOUT_A_in[35] = (CAS_IN_DOUT_A[35] !== 1'bz) && CAS_IN_DOUT_A_delay[35]; // rv 0
  assign CAS_IN_DOUT_A_in[36] = (CAS_IN_DOUT_A[36] !== 1'bz) && CAS_IN_DOUT_A_delay[36]; // rv 0
  assign CAS_IN_DOUT_A_in[37] = (CAS_IN_DOUT_A[37] !== 1'bz) && CAS_IN_DOUT_A_delay[37]; // rv 0
  assign CAS_IN_DOUT_A_in[38] = (CAS_IN_DOUT_A[38] !== 1'bz) && CAS_IN_DOUT_A_delay[38]; // rv 0
  assign CAS_IN_DOUT_A_in[39] = (CAS_IN_DOUT_A[39] !== 1'bz) && CAS_IN_DOUT_A_delay[39]; // rv 0
  assign CAS_IN_DOUT_A_in[3] = (CAS_IN_DOUT_A[3] !== 1'bz) && CAS_IN_DOUT_A_delay[3]; // rv 0
  assign CAS_IN_DOUT_A_in[40] = (CAS_IN_DOUT_A[40] !== 1'bz) && CAS_IN_DOUT_A_delay[40]; // rv 0
  assign CAS_IN_DOUT_A_in[41] = (CAS_IN_DOUT_A[41] !== 1'bz) && CAS_IN_DOUT_A_delay[41]; // rv 0
  assign CAS_IN_DOUT_A_in[42] = (CAS_IN_DOUT_A[42] !== 1'bz) && CAS_IN_DOUT_A_delay[42]; // rv 0
  assign CAS_IN_DOUT_A_in[43] = (CAS_IN_DOUT_A[43] !== 1'bz) && CAS_IN_DOUT_A_delay[43]; // rv 0
  assign CAS_IN_DOUT_A_in[44] = (CAS_IN_DOUT_A[44] !== 1'bz) && CAS_IN_DOUT_A_delay[44]; // rv 0
  assign CAS_IN_DOUT_A_in[45] = (CAS_IN_DOUT_A[45] !== 1'bz) && CAS_IN_DOUT_A_delay[45]; // rv 0
  assign CAS_IN_DOUT_A_in[46] = (CAS_IN_DOUT_A[46] !== 1'bz) && CAS_IN_DOUT_A_delay[46]; // rv 0
  assign CAS_IN_DOUT_A_in[47] = (CAS_IN_DOUT_A[47] !== 1'bz) && CAS_IN_DOUT_A_delay[47]; // rv 0
  assign CAS_IN_DOUT_A_in[48] = (CAS_IN_DOUT_A[48] !== 1'bz) && CAS_IN_DOUT_A_delay[48]; // rv 0
  assign CAS_IN_DOUT_A_in[49] = (CAS_IN_DOUT_A[49] !== 1'bz) && CAS_IN_DOUT_A_delay[49]; // rv 0
  assign CAS_IN_DOUT_A_in[4] = (CAS_IN_DOUT_A[4] !== 1'bz) && CAS_IN_DOUT_A_delay[4]; // rv 0
  assign CAS_IN_DOUT_A_in[50] = (CAS_IN_DOUT_A[50] !== 1'bz) && CAS_IN_DOUT_A_delay[50]; // rv 0
  assign CAS_IN_DOUT_A_in[51] = (CAS_IN_DOUT_A[51] !== 1'bz) && CAS_IN_DOUT_A_delay[51]; // rv 0
  assign CAS_IN_DOUT_A_in[52] = (CAS_IN_DOUT_A[52] !== 1'bz) && CAS_IN_DOUT_A_delay[52]; // rv 0
  assign CAS_IN_DOUT_A_in[53] = (CAS_IN_DOUT_A[53] !== 1'bz) && CAS_IN_DOUT_A_delay[53]; // rv 0
  assign CAS_IN_DOUT_A_in[54] = (CAS_IN_DOUT_A[54] !== 1'bz) && CAS_IN_DOUT_A_delay[54]; // rv 0
  assign CAS_IN_DOUT_A_in[55] = (CAS_IN_DOUT_A[55] !== 1'bz) && CAS_IN_DOUT_A_delay[55]; // rv 0
  assign CAS_IN_DOUT_A_in[56] = (CAS_IN_DOUT_A[56] !== 1'bz) && CAS_IN_DOUT_A_delay[56]; // rv 0
  assign CAS_IN_DOUT_A_in[57] = (CAS_IN_DOUT_A[57] !== 1'bz) && CAS_IN_DOUT_A_delay[57]; // rv 0
  assign CAS_IN_DOUT_A_in[58] = (CAS_IN_DOUT_A[58] !== 1'bz) && CAS_IN_DOUT_A_delay[58]; // rv 0
  assign CAS_IN_DOUT_A_in[59] = (CAS_IN_DOUT_A[59] !== 1'bz) && CAS_IN_DOUT_A_delay[59]; // rv 0
  assign CAS_IN_DOUT_A_in[5] = (CAS_IN_DOUT_A[5] !== 1'bz) && CAS_IN_DOUT_A_delay[5]; // rv 0
  assign CAS_IN_DOUT_A_in[60] = (CAS_IN_DOUT_A[60] !== 1'bz) && CAS_IN_DOUT_A_delay[60]; // rv 0
  assign CAS_IN_DOUT_A_in[61] = (CAS_IN_DOUT_A[61] !== 1'bz) && CAS_IN_DOUT_A_delay[61]; // rv 0
  assign CAS_IN_DOUT_A_in[62] = (CAS_IN_DOUT_A[62] !== 1'bz) && CAS_IN_DOUT_A_delay[62]; // rv 0
  assign CAS_IN_DOUT_A_in[63] = (CAS_IN_DOUT_A[63] !== 1'bz) && CAS_IN_DOUT_A_delay[63]; // rv 0
  assign CAS_IN_DOUT_A_in[64] = (CAS_IN_DOUT_A[64] !== 1'bz) && CAS_IN_DOUT_A_delay[64]; // rv 0
  assign CAS_IN_DOUT_A_in[65] = (CAS_IN_DOUT_A[65] !== 1'bz) && CAS_IN_DOUT_A_delay[65]; // rv 0
  assign CAS_IN_DOUT_A_in[66] = (CAS_IN_DOUT_A[66] !== 1'bz) && CAS_IN_DOUT_A_delay[66]; // rv 0
  assign CAS_IN_DOUT_A_in[67] = (CAS_IN_DOUT_A[67] !== 1'bz) && CAS_IN_DOUT_A_delay[67]; // rv 0
  assign CAS_IN_DOUT_A_in[68] = (CAS_IN_DOUT_A[68] !== 1'bz) && CAS_IN_DOUT_A_delay[68]; // rv 0
  assign CAS_IN_DOUT_A_in[69] = (CAS_IN_DOUT_A[69] !== 1'bz) && CAS_IN_DOUT_A_delay[69]; // rv 0
  assign CAS_IN_DOUT_A_in[6] = (CAS_IN_DOUT_A[6] !== 1'bz) && CAS_IN_DOUT_A_delay[6]; // rv 0
  assign CAS_IN_DOUT_A_in[70] = (CAS_IN_DOUT_A[70] !== 1'bz) && CAS_IN_DOUT_A_delay[70]; // rv 0
  assign CAS_IN_DOUT_A_in[71] = (CAS_IN_DOUT_A[71] !== 1'bz) && CAS_IN_DOUT_A_delay[71]; // rv 0
  assign CAS_IN_DOUT_A_in[7] = (CAS_IN_DOUT_A[7] !== 1'bz) && CAS_IN_DOUT_A_delay[7]; // rv 0
  assign CAS_IN_DOUT_A_in[8] = (CAS_IN_DOUT_A[8] !== 1'bz) && CAS_IN_DOUT_A_delay[8]; // rv 0
  assign CAS_IN_DOUT_A_in[9] = (CAS_IN_DOUT_A[9] !== 1'bz) && CAS_IN_DOUT_A_delay[9]; // rv 0
  assign CAS_IN_DOUT_B_in[0] = (CAS_IN_DOUT_B[0] !== 1'bz) && CAS_IN_DOUT_B_delay[0]; // rv 0
  assign CAS_IN_DOUT_B_in[10] = (CAS_IN_DOUT_B[10] !== 1'bz) && CAS_IN_DOUT_B_delay[10]; // rv 0
  assign CAS_IN_DOUT_B_in[11] = (CAS_IN_DOUT_B[11] !== 1'bz) && CAS_IN_DOUT_B_delay[11]; // rv 0
  assign CAS_IN_DOUT_B_in[12] = (CAS_IN_DOUT_B[12] !== 1'bz) && CAS_IN_DOUT_B_delay[12]; // rv 0
  assign CAS_IN_DOUT_B_in[13] = (CAS_IN_DOUT_B[13] !== 1'bz) && CAS_IN_DOUT_B_delay[13]; // rv 0
  assign CAS_IN_DOUT_B_in[14] = (CAS_IN_DOUT_B[14] !== 1'bz) && CAS_IN_DOUT_B_delay[14]; // rv 0
  assign CAS_IN_DOUT_B_in[15] = (CAS_IN_DOUT_B[15] !== 1'bz) && CAS_IN_DOUT_B_delay[15]; // rv 0
  assign CAS_IN_DOUT_B_in[16] = (CAS_IN_DOUT_B[16] !== 1'bz) && CAS_IN_DOUT_B_delay[16]; // rv 0
  assign CAS_IN_DOUT_B_in[17] = (CAS_IN_DOUT_B[17] !== 1'bz) && CAS_IN_DOUT_B_delay[17]; // rv 0
  assign CAS_IN_DOUT_B_in[18] = (CAS_IN_DOUT_B[18] !== 1'bz) && CAS_IN_DOUT_B_delay[18]; // rv 0
  assign CAS_IN_DOUT_B_in[19] = (CAS_IN_DOUT_B[19] !== 1'bz) && CAS_IN_DOUT_B_delay[19]; // rv 0
  assign CAS_IN_DOUT_B_in[1] = (CAS_IN_DOUT_B[1] !== 1'bz) && CAS_IN_DOUT_B_delay[1]; // rv 0
  assign CAS_IN_DOUT_B_in[20] = (CAS_IN_DOUT_B[20] !== 1'bz) && CAS_IN_DOUT_B_delay[20]; // rv 0
  assign CAS_IN_DOUT_B_in[21] = (CAS_IN_DOUT_B[21] !== 1'bz) && CAS_IN_DOUT_B_delay[21]; // rv 0
  assign CAS_IN_DOUT_B_in[22] = (CAS_IN_DOUT_B[22] !== 1'bz) && CAS_IN_DOUT_B_delay[22]; // rv 0
  assign CAS_IN_DOUT_B_in[23] = (CAS_IN_DOUT_B[23] !== 1'bz) && CAS_IN_DOUT_B_delay[23]; // rv 0
  assign CAS_IN_DOUT_B_in[24] = (CAS_IN_DOUT_B[24] !== 1'bz) && CAS_IN_DOUT_B_delay[24]; // rv 0
  assign CAS_IN_DOUT_B_in[25] = (CAS_IN_DOUT_B[25] !== 1'bz) && CAS_IN_DOUT_B_delay[25]; // rv 0
  assign CAS_IN_DOUT_B_in[26] = (CAS_IN_DOUT_B[26] !== 1'bz) && CAS_IN_DOUT_B_delay[26]; // rv 0
  assign CAS_IN_DOUT_B_in[27] = (CAS_IN_DOUT_B[27] !== 1'bz) && CAS_IN_DOUT_B_delay[27]; // rv 0
  assign CAS_IN_DOUT_B_in[28] = (CAS_IN_DOUT_B[28] !== 1'bz) && CAS_IN_DOUT_B_delay[28]; // rv 0
  assign CAS_IN_DOUT_B_in[29] = (CAS_IN_DOUT_B[29] !== 1'bz) && CAS_IN_DOUT_B_delay[29]; // rv 0
  assign CAS_IN_DOUT_B_in[2] = (CAS_IN_DOUT_B[2] !== 1'bz) && CAS_IN_DOUT_B_delay[2]; // rv 0
  assign CAS_IN_DOUT_B_in[30] = (CAS_IN_DOUT_B[30] !== 1'bz) && CAS_IN_DOUT_B_delay[30]; // rv 0
  assign CAS_IN_DOUT_B_in[31] = (CAS_IN_DOUT_B[31] !== 1'bz) && CAS_IN_DOUT_B_delay[31]; // rv 0
  assign CAS_IN_DOUT_B_in[32] = (CAS_IN_DOUT_B[32] !== 1'bz) && CAS_IN_DOUT_B_delay[32]; // rv 0
  assign CAS_IN_DOUT_B_in[33] = (CAS_IN_DOUT_B[33] !== 1'bz) && CAS_IN_DOUT_B_delay[33]; // rv 0
  assign CAS_IN_DOUT_B_in[34] = (CAS_IN_DOUT_B[34] !== 1'bz) && CAS_IN_DOUT_B_delay[34]; // rv 0
  assign CAS_IN_DOUT_B_in[35] = (CAS_IN_DOUT_B[35] !== 1'bz) && CAS_IN_DOUT_B_delay[35]; // rv 0
  assign CAS_IN_DOUT_B_in[36] = (CAS_IN_DOUT_B[36] !== 1'bz) && CAS_IN_DOUT_B_delay[36]; // rv 0
  assign CAS_IN_DOUT_B_in[37] = (CAS_IN_DOUT_B[37] !== 1'bz) && CAS_IN_DOUT_B_delay[37]; // rv 0
  assign CAS_IN_DOUT_B_in[38] = (CAS_IN_DOUT_B[38] !== 1'bz) && CAS_IN_DOUT_B_delay[38]; // rv 0
  assign CAS_IN_DOUT_B_in[39] = (CAS_IN_DOUT_B[39] !== 1'bz) && CAS_IN_DOUT_B_delay[39]; // rv 0
  assign CAS_IN_DOUT_B_in[3] = (CAS_IN_DOUT_B[3] !== 1'bz) && CAS_IN_DOUT_B_delay[3]; // rv 0
  assign CAS_IN_DOUT_B_in[40] = (CAS_IN_DOUT_B[40] !== 1'bz) && CAS_IN_DOUT_B_delay[40]; // rv 0
  assign CAS_IN_DOUT_B_in[41] = (CAS_IN_DOUT_B[41] !== 1'bz) && CAS_IN_DOUT_B_delay[41]; // rv 0
  assign CAS_IN_DOUT_B_in[42] = (CAS_IN_DOUT_B[42] !== 1'bz) && CAS_IN_DOUT_B_delay[42]; // rv 0
  assign CAS_IN_DOUT_B_in[43] = (CAS_IN_DOUT_B[43] !== 1'bz) && CAS_IN_DOUT_B_delay[43]; // rv 0
  assign CAS_IN_DOUT_B_in[44] = (CAS_IN_DOUT_B[44] !== 1'bz) && CAS_IN_DOUT_B_delay[44]; // rv 0
  assign CAS_IN_DOUT_B_in[45] = (CAS_IN_DOUT_B[45] !== 1'bz) && CAS_IN_DOUT_B_delay[45]; // rv 0
  assign CAS_IN_DOUT_B_in[46] = (CAS_IN_DOUT_B[46] !== 1'bz) && CAS_IN_DOUT_B_delay[46]; // rv 0
  assign CAS_IN_DOUT_B_in[47] = (CAS_IN_DOUT_B[47] !== 1'bz) && CAS_IN_DOUT_B_delay[47]; // rv 0
  assign CAS_IN_DOUT_B_in[48] = (CAS_IN_DOUT_B[48] !== 1'bz) && CAS_IN_DOUT_B_delay[48]; // rv 0
  assign CAS_IN_DOUT_B_in[49] = (CAS_IN_DOUT_B[49] !== 1'bz) && CAS_IN_DOUT_B_delay[49]; // rv 0
  assign CAS_IN_DOUT_B_in[4] = (CAS_IN_DOUT_B[4] !== 1'bz) && CAS_IN_DOUT_B_delay[4]; // rv 0
  assign CAS_IN_DOUT_B_in[50] = (CAS_IN_DOUT_B[50] !== 1'bz) && CAS_IN_DOUT_B_delay[50]; // rv 0
  assign CAS_IN_DOUT_B_in[51] = (CAS_IN_DOUT_B[51] !== 1'bz) && CAS_IN_DOUT_B_delay[51]; // rv 0
  assign CAS_IN_DOUT_B_in[52] = (CAS_IN_DOUT_B[52] !== 1'bz) && CAS_IN_DOUT_B_delay[52]; // rv 0
  assign CAS_IN_DOUT_B_in[53] = (CAS_IN_DOUT_B[53] !== 1'bz) && CAS_IN_DOUT_B_delay[53]; // rv 0
  assign CAS_IN_DOUT_B_in[54] = (CAS_IN_DOUT_B[54] !== 1'bz) && CAS_IN_DOUT_B_delay[54]; // rv 0
  assign CAS_IN_DOUT_B_in[55] = (CAS_IN_DOUT_B[55] !== 1'bz) && CAS_IN_DOUT_B_delay[55]; // rv 0
  assign CAS_IN_DOUT_B_in[56] = (CAS_IN_DOUT_B[56] !== 1'bz) && CAS_IN_DOUT_B_delay[56]; // rv 0
  assign CAS_IN_DOUT_B_in[57] = (CAS_IN_DOUT_B[57] !== 1'bz) && CAS_IN_DOUT_B_delay[57]; // rv 0
  assign CAS_IN_DOUT_B_in[58] = (CAS_IN_DOUT_B[58] !== 1'bz) && CAS_IN_DOUT_B_delay[58]; // rv 0
  assign CAS_IN_DOUT_B_in[59] = (CAS_IN_DOUT_B[59] !== 1'bz) && CAS_IN_DOUT_B_delay[59]; // rv 0
  assign CAS_IN_DOUT_B_in[5] = (CAS_IN_DOUT_B[5] !== 1'bz) && CAS_IN_DOUT_B_delay[5]; // rv 0
  assign CAS_IN_DOUT_B_in[60] = (CAS_IN_DOUT_B[60] !== 1'bz) && CAS_IN_DOUT_B_delay[60]; // rv 0
  assign CAS_IN_DOUT_B_in[61] = (CAS_IN_DOUT_B[61] !== 1'bz) && CAS_IN_DOUT_B_delay[61]; // rv 0
  assign CAS_IN_DOUT_B_in[62] = (CAS_IN_DOUT_B[62] !== 1'bz) && CAS_IN_DOUT_B_delay[62]; // rv 0
  assign CAS_IN_DOUT_B_in[63] = (CAS_IN_DOUT_B[63] !== 1'bz) && CAS_IN_DOUT_B_delay[63]; // rv 0
  assign CAS_IN_DOUT_B_in[64] = (CAS_IN_DOUT_B[64] !== 1'bz) && CAS_IN_DOUT_B_delay[64]; // rv 0
  assign CAS_IN_DOUT_B_in[65] = (CAS_IN_DOUT_B[65] !== 1'bz) && CAS_IN_DOUT_B_delay[65]; // rv 0
  assign CAS_IN_DOUT_B_in[66] = (CAS_IN_DOUT_B[66] !== 1'bz) && CAS_IN_DOUT_B_delay[66]; // rv 0
  assign CAS_IN_DOUT_B_in[67] = (CAS_IN_DOUT_B[67] !== 1'bz) && CAS_IN_DOUT_B_delay[67]; // rv 0
  assign CAS_IN_DOUT_B_in[68] = (CAS_IN_DOUT_B[68] !== 1'bz) && CAS_IN_DOUT_B_delay[68]; // rv 0
  assign CAS_IN_DOUT_B_in[69] = (CAS_IN_DOUT_B[69] !== 1'bz) && CAS_IN_DOUT_B_delay[69]; // rv 0
  assign CAS_IN_DOUT_B_in[6] = (CAS_IN_DOUT_B[6] !== 1'bz) && CAS_IN_DOUT_B_delay[6]; // rv 0
  assign CAS_IN_DOUT_B_in[70] = (CAS_IN_DOUT_B[70] !== 1'bz) && CAS_IN_DOUT_B_delay[70]; // rv 0
  assign CAS_IN_DOUT_B_in[71] = (CAS_IN_DOUT_B[71] !== 1'bz) && CAS_IN_DOUT_B_delay[71]; // rv 0
  assign CAS_IN_DOUT_B_in[7] = (CAS_IN_DOUT_B[7] !== 1'bz) && CAS_IN_DOUT_B_delay[7]; // rv 0
  assign CAS_IN_DOUT_B_in[8] = (CAS_IN_DOUT_B[8] !== 1'bz) && CAS_IN_DOUT_B_delay[8]; // rv 0
  assign CAS_IN_DOUT_B_in[9] = (CAS_IN_DOUT_B[9] !== 1'bz) && CAS_IN_DOUT_B_delay[9]; // rv 0
  assign CAS_IN_EN_A_in = (CAS_IN_EN_A !== 1'bz) && CAS_IN_EN_A_delay; // rv 0
  assign CAS_IN_EN_B_in = (CAS_IN_EN_B !== 1'bz) && CAS_IN_EN_B_delay; // rv 0
  assign CAS_IN_RDACCESS_A_in = (CAS_IN_RDACCESS_A !== 1'bz) && CAS_IN_RDACCESS_A_delay; // rv 0
  assign CAS_IN_RDACCESS_B_in = (CAS_IN_RDACCESS_B !== 1'bz) && CAS_IN_RDACCESS_B_delay; // rv 0
  assign CAS_IN_RDB_WR_A_in = (CAS_IN_RDB_WR_A !== 1'bz) && CAS_IN_RDB_WR_A_delay; // rv 0
  assign CAS_IN_RDB_WR_B_in = (CAS_IN_RDB_WR_B !== 1'bz) && CAS_IN_RDB_WR_B_delay; // rv 0
  assign CAS_IN_SBITERR_A_in = (CAS_IN_SBITERR_A !== 1'bz) && CAS_IN_SBITERR_A_delay; // rv 0
  assign CAS_IN_SBITERR_B_in = (CAS_IN_SBITERR_B !== 1'bz) && CAS_IN_SBITERR_B_delay; // rv 0
  assign CLK_in = (CLK !== 1'bz) && (CLK_delay ^ IS_CLK_INVERTED_REG); // rv 0
  assign DIN_A_in = DIN_A_delay;
  assign DIN_B_in = DIN_B_delay;
  assign EN_A_in = (EN_A !== 1'bz) && (EN_A_delay ^ IS_EN_A_INVERTED_REG); // rv 0
  assign EN_B_in = (EN_B !== 1'bz) && (EN_B_delay ^ IS_EN_B_INVERTED_REG); // rv 0
  assign INJECT_DBITERR_A_in = (INJECT_DBITERR_A !== 1'bz) && INJECT_DBITERR_A_delay; // rv 0
  assign INJECT_DBITERR_B_in = (INJECT_DBITERR_B !== 1'bz) && INJECT_DBITERR_B_delay; // rv 0
  assign INJECT_SBITERR_A_in = (INJECT_SBITERR_A !== 1'bz) && INJECT_SBITERR_A_delay; // rv 0
  assign INJECT_SBITERR_B_in = (INJECT_SBITERR_B !== 1'bz) && INJECT_SBITERR_B_delay; // rv 0
  assign OREG_CE_A_in = (OREG_CE_A === 1'bz) || OREG_CE_A_delay; // rv 1
  assign OREG_CE_B_in = (OREG_CE_B === 1'bz) || OREG_CE_B_delay; // rv 1
  assign OREG_ECC_CE_A_in = (OREG_ECC_CE_A === 1'bz) || OREG_ECC_CE_A_delay; // rv 1
  assign OREG_ECC_CE_B_in = (OREG_ECC_CE_B === 1'bz) || OREG_ECC_CE_B_delay; // rv 1
  assign RDB_WR_A_in = (RDB_WR_A !== 1'bz) && (RDB_WR_A_delay ^ IS_RDB_WR_A_INVERTED_REG); // rv 0
  assign RDB_WR_B_in = (RDB_WR_B !== 1'bz) && (RDB_WR_B_delay ^ IS_RDB_WR_B_INVERTED_REG); // rv 0
  assign RST_A_in = (RST_A !== 1'bz) && (RST_A_delay ^ IS_RST_A_INVERTED_REG); // rv 0
  assign RST_B_in = (RST_B !== 1'bz) && (RST_B_delay ^ IS_RST_B_INVERTED_REG); // rv 0
  assign SLEEP_in = (SLEEP !== 1'bz) && SLEEP_delay; // rv 0
`else
  assign ADDR_A_in = ADDR_A;
  assign ADDR_B_in = ADDR_B;
  assign BWE_A_in[0] = (BWE_A[0] === 1'bz) || BWE_A[0]; // rv 1
  assign BWE_A_in[1] = (BWE_A[1] === 1'bz) || BWE_A[1]; // rv 1
  assign BWE_A_in[2] = (BWE_A[2] === 1'bz) || BWE_A[2]; // rv 1
  assign BWE_A_in[3] = (BWE_A[3] === 1'bz) || BWE_A[3]; // rv 1
  assign BWE_A_in[4] = (BWE_A[4] === 1'bz) || BWE_A[4]; // rv 1
  assign BWE_A_in[5] = (BWE_A[5] === 1'bz) || BWE_A[5]; // rv 1
  assign BWE_A_in[6] = (BWE_A[6] === 1'bz) || BWE_A[6]; // rv 1
  assign BWE_A_in[7] = (BWE_A[7] === 1'bz) || BWE_A[7]; // rv 1
  assign BWE_A_in[8] = (BWE_A[8] === 1'bz) || BWE_A[8]; // rv 1
  assign BWE_B_in[0] = (BWE_B[0] === 1'bz) || BWE_B[0]; // rv 1
  assign BWE_B_in[1] = (BWE_B[1] === 1'bz) || BWE_B[1]; // rv 1
  assign BWE_B_in[2] = (BWE_B[2] === 1'bz) || BWE_B[2]; // rv 1
  assign BWE_B_in[3] = (BWE_B[3] === 1'bz) || BWE_B[3]; // rv 1
  assign BWE_B_in[4] = (BWE_B[4] === 1'bz) || BWE_B[4]; // rv 1
  assign BWE_B_in[5] = (BWE_B[5] === 1'bz) || BWE_B[5]; // rv 1
  assign BWE_B_in[6] = (BWE_B[6] === 1'bz) || BWE_B[6]; // rv 1
  assign BWE_B_in[7] = (BWE_B[7] === 1'bz) || BWE_B[7]; // rv 1
  assign BWE_B_in[8] = (BWE_B[8] === 1'bz) || BWE_B[8]; // rv 1
  assign CAS_IN_ADDR_A_in[0] = (CAS_IN_ADDR_A[0] !== 1'bz) && CAS_IN_ADDR_A[0]; // rv 0
  assign CAS_IN_ADDR_A_in[10] = (CAS_IN_ADDR_A[10] !== 1'bz) && CAS_IN_ADDR_A[10]; // rv 0
  assign CAS_IN_ADDR_A_in[11] = (CAS_IN_ADDR_A[11] !== 1'bz) && CAS_IN_ADDR_A[11]; // rv 0
  assign CAS_IN_ADDR_A_in[12] = (CAS_IN_ADDR_A[12] !== 1'bz) && CAS_IN_ADDR_A[12]; // rv 0
  assign CAS_IN_ADDR_A_in[13] = (CAS_IN_ADDR_A[13] !== 1'bz) && CAS_IN_ADDR_A[13]; // rv 0
  assign CAS_IN_ADDR_A_in[14] = (CAS_IN_ADDR_A[14] !== 1'bz) && CAS_IN_ADDR_A[14]; // rv 0
  assign CAS_IN_ADDR_A_in[15] = (CAS_IN_ADDR_A[15] !== 1'bz) && CAS_IN_ADDR_A[15]; // rv 0
  assign CAS_IN_ADDR_A_in[16] = (CAS_IN_ADDR_A[16] !== 1'bz) && CAS_IN_ADDR_A[16]; // rv 0
  assign CAS_IN_ADDR_A_in[17] = (CAS_IN_ADDR_A[17] !== 1'bz) && CAS_IN_ADDR_A[17]; // rv 0
  assign CAS_IN_ADDR_A_in[18] = (CAS_IN_ADDR_A[18] !== 1'bz) && CAS_IN_ADDR_A[18]; // rv 0
  assign CAS_IN_ADDR_A_in[19] = (CAS_IN_ADDR_A[19] !== 1'bz) && CAS_IN_ADDR_A[19]; // rv 0
  assign CAS_IN_ADDR_A_in[1] = (CAS_IN_ADDR_A[1] !== 1'bz) && CAS_IN_ADDR_A[1]; // rv 0
  assign CAS_IN_ADDR_A_in[20] = (CAS_IN_ADDR_A[20] !== 1'bz) && CAS_IN_ADDR_A[20]; // rv 0
  assign CAS_IN_ADDR_A_in[21] = (CAS_IN_ADDR_A[21] !== 1'bz) && CAS_IN_ADDR_A[21]; // rv 0
  assign CAS_IN_ADDR_A_in[22] = (CAS_IN_ADDR_A[22] !== 1'bz) && CAS_IN_ADDR_A[22]; // rv 0
  assign CAS_IN_ADDR_A_in[2] = (CAS_IN_ADDR_A[2] !== 1'bz) && CAS_IN_ADDR_A[2]; // rv 0
  assign CAS_IN_ADDR_A_in[3] = (CAS_IN_ADDR_A[3] !== 1'bz) && CAS_IN_ADDR_A[3]; // rv 0
  assign CAS_IN_ADDR_A_in[4] = (CAS_IN_ADDR_A[4] !== 1'bz) && CAS_IN_ADDR_A[4]; // rv 0
  assign CAS_IN_ADDR_A_in[5] = (CAS_IN_ADDR_A[5] !== 1'bz) && CAS_IN_ADDR_A[5]; // rv 0
  assign CAS_IN_ADDR_A_in[6] = (CAS_IN_ADDR_A[6] !== 1'bz) && CAS_IN_ADDR_A[6]; // rv 0
  assign CAS_IN_ADDR_A_in[7] = (CAS_IN_ADDR_A[7] !== 1'bz) && CAS_IN_ADDR_A[7]; // rv 0
  assign CAS_IN_ADDR_A_in[8] = (CAS_IN_ADDR_A[8] !== 1'bz) && CAS_IN_ADDR_A[8]; // rv 0
  assign CAS_IN_ADDR_A_in[9] = (CAS_IN_ADDR_A[9] !== 1'bz) && CAS_IN_ADDR_A[9]; // rv 0
  assign CAS_IN_ADDR_B_in[0] = (CAS_IN_ADDR_B[0] !== 1'bz) && CAS_IN_ADDR_B[0]; // rv 0
  assign CAS_IN_ADDR_B_in[10] = (CAS_IN_ADDR_B[10] !== 1'bz) && CAS_IN_ADDR_B[10]; // rv 0
  assign CAS_IN_ADDR_B_in[11] = (CAS_IN_ADDR_B[11] !== 1'bz) && CAS_IN_ADDR_B[11]; // rv 0
  assign CAS_IN_ADDR_B_in[12] = (CAS_IN_ADDR_B[12] !== 1'bz) && CAS_IN_ADDR_B[12]; // rv 0
  assign CAS_IN_ADDR_B_in[13] = (CAS_IN_ADDR_B[13] !== 1'bz) && CAS_IN_ADDR_B[13]; // rv 0
  assign CAS_IN_ADDR_B_in[14] = (CAS_IN_ADDR_B[14] !== 1'bz) && CAS_IN_ADDR_B[14]; // rv 0
  assign CAS_IN_ADDR_B_in[15] = (CAS_IN_ADDR_B[15] !== 1'bz) && CAS_IN_ADDR_B[15]; // rv 0
  assign CAS_IN_ADDR_B_in[16] = (CAS_IN_ADDR_B[16] !== 1'bz) && CAS_IN_ADDR_B[16]; // rv 0
  assign CAS_IN_ADDR_B_in[17] = (CAS_IN_ADDR_B[17] !== 1'bz) && CAS_IN_ADDR_B[17]; // rv 0
  assign CAS_IN_ADDR_B_in[18] = (CAS_IN_ADDR_B[18] !== 1'bz) && CAS_IN_ADDR_B[18]; // rv 0
  assign CAS_IN_ADDR_B_in[19] = (CAS_IN_ADDR_B[19] !== 1'bz) && CAS_IN_ADDR_B[19]; // rv 0
  assign CAS_IN_ADDR_B_in[1] = (CAS_IN_ADDR_B[1] !== 1'bz) && CAS_IN_ADDR_B[1]; // rv 0
  assign CAS_IN_ADDR_B_in[20] = (CAS_IN_ADDR_B[20] !== 1'bz) && CAS_IN_ADDR_B[20]; // rv 0
  assign CAS_IN_ADDR_B_in[21] = (CAS_IN_ADDR_B[21] !== 1'bz) && CAS_IN_ADDR_B[21]; // rv 0
  assign CAS_IN_ADDR_B_in[22] = (CAS_IN_ADDR_B[22] !== 1'bz) && CAS_IN_ADDR_B[22]; // rv 0
  assign CAS_IN_ADDR_B_in[2] = (CAS_IN_ADDR_B[2] !== 1'bz) && CAS_IN_ADDR_B[2]; // rv 0
  assign CAS_IN_ADDR_B_in[3] = (CAS_IN_ADDR_B[3] !== 1'bz) && CAS_IN_ADDR_B[3]; // rv 0
  assign CAS_IN_ADDR_B_in[4] = (CAS_IN_ADDR_B[4] !== 1'bz) && CAS_IN_ADDR_B[4]; // rv 0
  assign CAS_IN_ADDR_B_in[5] = (CAS_IN_ADDR_B[5] !== 1'bz) && CAS_IN_ADDR_B[5]; // rv 0
  assign CAS_IN_ADDR_B_in[6] = (CAS_IN_ADDR_B[6] !== 1'bz) && CAS_IN_ADDR_B[6]; // rv 0
  assign CAS_IN_ADDR_B_in[7] = (CAS_IN_ADDR_B[7] !== 1'bz) && CAS_IN_ADDR_B[7]; // rv 0
  assign CAS_IN_ADDR_B_in[8] = (CAS_IN_ADDR_B[8] !== 1'bz) && CAS_IN_ADDR_B[8]; // rv 0
  assign CAS_IN_ADDR_B_in[9] = (CAS_IN_ADDR_B[9] !== 1'bz) && CAS_IN_ADDR_B[9]; // rv 0
  assign CAS_IN_BWE_A_in[0] = (CAS_IN_BWE_A[0] !== 1'bz) && CAS_IN_BWE_A[0]; // rv 0
  assign CAS_IN_BWE_A_in[1] = (CAS_IN_BWE_A[1] !== 1'bz) && CAS_IN_BWE_A[1]; // rv 0
  assign CAS_IN_BWE_A_in[2] = (CAS_IN_BWE_A[2] !== 1'bz) && CAS_IN_BWE_A[2]; // rv 0
  assign CAS_IN_BWE_A_in[3] = (CAS_IN_BWE_A[3] !== 1'bz) && CAS_IN_BWE_A[3]; // rv 0
  assign CAS_IN_BWE_A_in[4] = (CAS_IN_BWE_A[4] !== 1'bz) && CAS_IN_BWE_A[4]; // rv 0
  assign CAS_IN_BWE_A_in[5] = (CAS_IN_BWE_A[5] !== 1'bz) && CAS_IN_BWE_A[5]; // rv 0
  assign CAS_IN_BWE_A_in[6] = (CAS_IN_BWE_A[6] !== 1'bz) && CAS_IN_BWE_A[6]; // rv 0
  assign CAS_IN_BWE_A_in[7] = (CAS_IN_BWE_A[7] !== 1'bz) && CAS_IN_BWE_A[7]; // rv 0
  assign CAS_IN_BWE_A_in[8] = (CAS_IN_BWE_A[8] !== 1'bz) && CAS_IN_BWE_A[8]; // rv 0
  assign CAS_IN_BWE_B_in[0] = (CAS_IN_BWE_B[0] !== 1'bz) && CAS_IN_BWE_B[0]; // rv 0
  assign CAS_IN_BWE_B_in[1] = (CAS_IN_BWE_B[1] !== 1'bz) && CAS_IN_BWE_B[1]; // rv 0
  assign CAS_IN_BWE_B_in[2] = (CAS_IN_BWE_B[2] !== 1'bz) && CAS_IN_BWE_B[2]; // rv 0
  assign CAS_IN_BWE_B_in[3] = (CAS_IN_BWE_B[3] !== 1'bz) && CAS_IN_BWE_B[3]; // rv 0
  assign CAS_IN_BWE_B_in[4] = (CAS_IN_BWE_B[4] !== 1'bz) && CAS_IN_BWE_B[4]; // rv 0
  assign CAS_IN_BWE_B_in[5] = (CAS_IN_BWE_B[5] !== 1'bz) && CAS_IN_BWE_B[5]; // rv 0
  assign CAS_IN_BWE_B_in[6] = (CAS_IN_BWE_B[6] !== 1'bz) && CAS_IN_BWE_B[6]; // rv 0
  assign CAS_IN_BWE_B_in[7] = (CAS_IN_BWE_B[7] !== 1'bz) && CAS_IN_BWE_B[7]; // rv 0
  assign CAS_IN_BWE_B_in[8] = (CAS_IN_BWE_B[8] !== 1'bz) && CAS_IN_BWE_B[8]; // rv 0
  assign CAS_IN_DBITERR_A_in = (CAS_IN_DBITERR_A !== 1'bz) && CAS_IN_DBITERR_A; // rv 0
  assign CAS_IN_DBITERR_B_in = (CAS_IN_DBITERR_B !== 1'bz) && CAS_IN_DBITERR_B; // rv 0
  assign CAS_IN_DIN_A_in[0] = (CAS_IN_DIN_A[0] !== 1'bz) && CAS_IN_DIN_A[0]; // rv 0
  assign CAS_IN_DIN_A_in[10] = (CAS_IN_DIN_A[10] !== 1'bz) && CAS_IN_DIN_A[10]; // rv 0
  assign CAS_IN_DIN_A_in[11] = (CAS_IN_DIN_A[11] !== 1'bz) && CAS_IN_DIN_A[11]; // rv 0
  assign CAS_IN_DIN_A_in[12] = (CAS_IN_DIN_A[12] !== 1'bz) && CAS_IN_DIN_A[12]; // rv 0
  assign CAS_IN_DIN_A_in[13] = (CAS_IN_DIN_A[13] !== 1'bz) && CAS_IN_DIN_A[13]; // rv 0
  assign CAS_IN_DIN_A_in[14] = (CAS_IN_DIN_A[14] !== 1'bz) && CAS_IN_DIN_A[14]; // rv 0
  assign CAS_IN_DIN_A_in[15] = (CAS_IN_DIN_A[15] !== 1'bz) && CAS_IN_DIN_A[15]; // rv 0
  assign CAS_IN_DIN_A_in[16] = (CAS_IN_DIN_A[16] !== 1'bz) && CAS_IN_DIN_A[16]; // rv 0
  assign CAS_IN_DIN_A_in[17] = (CAS_IN_DIN_A[17] !== 1'bz) && CAS_IN_DIN_A[17]; // rv 0
  assign CAS_IN_DIN_A_in[18] = (CAS_IN_DIN_A[18] !== 1'bz) && CAS_IN_DIN_A[18]; // rv 0
  assign CAS_IN_DIN_A_in[19] = (CAS_IN_DIN_A[19] !== 1'bz) && CAS_IN_DIN_A[19]; // rv 0
  assign CAS_IN_DIN_A_in[1] = (CAS_IN_DIN_A[1] !== 1'bz) && CAS_IN_DIN_A[1]; // rv 0
  assign CAS_IN_DIN_A_in[20] = (CAS_IN_DIN_A[20] !== 1'bz) && CAS_IN_DIN_A[20]; // rv 0
  assign CAS_IN_DIN_A_in[21] = (CAS_IN_DIN_A[21] !== 1'bz) && CAS_IN_DIN_A[21]; // rv 0
  assign CAS_IN_DIN_A_in[22] = (CAS_IN_DIN_A[22] !== 1'bz) && CAS_IN_DIN_A[22]; // rv 0
  assign CAS_IN_DIN_A_in[23] = (CAS_IN_DIN_A[23] !== 1'bz) && CAS_IN_DIN_A[23]; // rv 0
  assign CAS_IN_DIN_A_in[24] = (CAS_IN_DIN_A[24] !== 1'bz) && CAS_IN_DIN_A[24]; // rv 0
  assign CAS_IN_DIN_A_in[25] = (CAS_IN_DIN_A[25] !== 1'bz) && CAS_IN_DIN_A[25]; // rv 0
  assign CAS_IN_DIN_A_in[26] = (CAS_IN_DIN_A[26] !== 1'bz) && CAS_IN_DIN_A[26]; // rv 0
  assign CAS_IN_DIN_A_in[27] = (CAS_IN_DIN_A[27] !== 1'bz) && CAS_IN_DIN_A[27]; // rv 0
  assign CAS_IN_DIN_A_in[28] = (CAS_IN_DIN_A[28] !== 1'bz) && CAS_IN_DIN_A[28]; // rv 0
  assign CAS_IN_DIN_A_in[29] = (CAS_IN_DIN_A[29] !== 1'bz) && CAS_IN_DIN_A[29]; // rv 0
  assign CAS_IN_DIN_A_in[2] = (CAS_IN_DIN_A[2] !== 1'bz) && CAS_IN_DIN_A[2]; // rv 0
  assign CAS_IN_DIN_A_in[30] = (CAS_IN_DIN_A[30] !== 1'bz) && CAS_IN_DIN_A[30]; // rv 0
  assign CAS_IN_DIN_A_in[31] = (CAS_IN_DIN_A[31] !== 1'bz) && CAS_IN_DIN_A[31]; // rv 0
  assign CAS_IN_DIN_A_in[32] = (CAS_IN_DIN_A[32] !== 1'bz) && CAS_IN_DIN_A[32]; // rv 0
  assign CAS_IN_DIN_A_in[33] = (CAS_IN_DIN_A[33] !== 1'bz) && CAS_IN_DIN_A[33]; // rv 0
  assign CAS_IN_DIN_A_in[34] = (CAS_IN_DIN_A[34] !== 1'bz) && CAS_IN_DIN_A[34]; // rv 0
  assign CAS_IN_DIN_A_in[35] = (CAS_IN_DIN_A[35] !== 1'bz) && CAS_IN_DIN_A[35]; // rv 0
  assign CAS_IN_DIN_A_in[36] = (CAS_IN_DIN_A[36] !== 1'bz) && CAS_IN_DIN_A[36]; // rv 0
  assign CAS_IN_DIN_A_in[37] = (CAS_IN_DIN_A[37] !== 1'bz) && CAS_IN_DIN_A[37]; // rv 0
  assign CAS_IN_DIN_A_in[38] = (CAS_IN_DIN_A[38] !== 1'bz) && CAS_IN_DIN_A[38]; // rv 0
  assign CAS_IN_DIN_A_in[39] = (CAS_IN_DIN_A[39] !== 1'bz) && CAS_IN_DIN_A[39]; // rv 0
  assign CAS_IN_DIN_A_in[3] = (CAS_IN_DIN_A[3] !== 1'bz) && CAS_IN_DIN_A[3]; // rv 0
  assign CAS_IN_DIN_A_in[40] = (CAS_IN_DIN_A[40] !== 1'bz) && CAS_IN_DIN_A[40]; // rv 0
  assign CAS_IN_DIN_A_in[41] = (CAS_IN_DIN_A[41] !== 1'bz) && CAS_IN_DIN_A[41]; // rv 0
  assign CAS_IN_DIN_A_in[42] = (CAS_IN_DIN_A[42] !== 1'bz) && CAS_IN_DIN_A[42]; // rv 0
  assign CAS_IN_DIN_A_in[43] = (CAS_IN_DIN_A[43] !== 1'bz) && CAS_IN_DIN_A[43]; // rv 0
  assign CAS_IN_DIN_A_in[44] = (CAS_IN_DIN_A[44] !== 1'bz) && CAS_IN_DIN_A[44]; // rv 0
  assign CAS_IN_DIN_A_in[45] = (CAS_IN_DIN_A[45] !== 1'bz) && CAS_IN_DIN_A[45]; // rv 0
  assign CAS_IN_DIN_A_in[46] = (CAS_IN_DIN_A[46] !== 1'bz) && CAS_IN_DIN_A[46]; // rv 0
  assign CAS_IN_DIN_A_in[47] = (CAS_IN_DIN_A[47] !== 1'bz) && CAS_IN_DIN_A[47]; // rv 0
  assign CAS_IN_DIN_A_in[48] = (CAS_IN_DIN_A[48] !== 1'bz) && CAS_IN_DIN_A[48]; // rv 0
  assign CAS_IN_DIN_A_in[49] = (CAS_IN_DIN_A[49] !== 1'bz) && CAS_IN_DIN_A[49]; // rv 0
  assign CAS_IN_DIN_A_in[4] = (CAS_IN_DIN_A[4] !== 1'bz) && CAS_IN_DIN_A[4]; // rv 0
  assign CAS_IN_DIN_A_in[50] = (CAS_IN_DIN_A[50] !== 1'bz) && CAS_IN_DIN_A[50]; // rv 0
  assign CAS_IN_DIN_A_in[51] = (CAS_IN_DIN_A[51] !== 1'bz) && CAS_IN_DIN_A[51]; // rv 0
  assign CAS_IN_DIN_A_in[52] = (CAS_IN_DIN_A[52] !== 1'bz) && CAS_IN_DIN_A[52]; // rv 0
  assign CAS_IN_DIN_A_in[53] = (CAS_IN_DIN_A[53] !== 1'bz) && CAS_IN_DIN_A[53]; // rv 0
  assign CAS_IN_DIN_A_in[54] = (CAS_IN_DIN_A[54] !== 1'bz) && CAS_IN_DIN_A[54]; // rv 0
  assign CAS_IN_DIN_A_in[55] = (CAS_IN_DIN_A[55] !== 1'bz) && CAS_IN_DIN_A[55]; // rv 0
  assign CAS_IN_DIN_A_in[56] = (CAS_IN_DIN_A[56] !== 1'bz) && CAS_IN_DIN_A[56]; // rv 0
  assign CAS_IN_DIN_A_in[57] = (CAS_IN_DIN_A[57] !== 1'bz) && CAS_IN_DIN_A[57]; // rv 0
  assign CAS_IN_DIN_A_in[58] = (CAS_IN_DIN_A[58] !== 1'bz) && CAS_IN_DIN_A[58]; // rv 0
  assign CAS_IN_DIN_A_in[59] = (CAS_IN_DIN_A[59] !== 1'bz) && CAS_IN_DIN_A[59]; // rv 0
  assign CAS_IN_DIN_A_in[5] = (CAS_IN_DIN_A[5] !== 1'bz) && CAS_IN_DIN_A[5]; // rv 0
  assign CAS_IN_DIN_A_in[60] = (CAS_IN_DIN_A[60] !== 1'bz) && CAS_IN_DIN_A[60]; // rv 0
  assign CAS_IN_DIN_A_in[61] = (CAS_IN_DIN_A[61] !== 1'bz) && CAS_IN_DIN_A[61]; // rv 0
  assign CAS_IN_DIN_A_in[62] = (CAS_IN_DIN_A[62] !== 1'bz) && CAS_IN_DIN_A[62]; // rv 0
  assign CAS_IN_DIN_A_in[63] = (CAS_IN_DIN_A[63] !== 1'bz) && CAS_IN_DIN_A[63]; // rv 0
  assign CAS_IN_DIN_A_in[64] = (CAS_IN_DIN_A[64] !== 1'bz) && CAS_IN_DIN_A[64]; // rv 0
  assign CAS_IN_DIN_A_in[65] = (CAS_IN_DIN_A[65] !== 1'bz) && CAS_IN_DIN_A[65]; // rv 0
  assign CAS_IN_DIN_A_in[66] = (CAS_IN_DIN_A[66] !== 1'bz) && CAS_IN_DIN_A[66]; // rv 0
  assign CAS_IN_DIN_A_in[67] = (CAS_IN_DIN_A[67] !== 1'bz) && CAS_IN_DIN_A[67]; // rv 0
  assign CAS_IN_DIN_A_in[68] = (CAS_IN_DIN_A[68] !== 1'bz) && CAS_IN_DIN_A[68]; // rv 0
  assign CAS_IN_DIN_A_in[69] = (CAS_IN_DIN_A[69] !== 1'bz) && CAS_IN_DIN_A[69]; // rv 0
  assign CAS_IN_DIN_A_in[6] = (CAS_IN_DIN_A[6] !== 1'bz) && CAS_IN_DIN_A[6]; // rv 0
  assign CAS_IN_DIN_A_in[70] = (CAS_IN_DIN_A[70] !== 1'bz) && CAS_IN_DIN_A[70]; // rv 0
  assign CAS_IN_DIN_A_in[71] = (CAS_IN_DIN_A[71] !== 1'bz) && CAS_IN_DIN_A[71]; // rv 0
  assign CAS_IN_DIN_A_in[7] = (CAS_IN_DIN_A[7] !== 1'bz) && CAS_IN_DIN_A[7]; // rv 0
  assign CAS_IN_DIN_A_in[8] = (CAS_IN_DIN_A[8] !== 1'bz) && CAS_IN_DIN_A[8]; // rv 0
  assign CAS_IN_DIN_A_in[9] = (CAS_IN_DIN_A[9] !== 1'bz) && CAS_IN_DIN_A[9]; // rv 0
  assign CAS_IN_DIN_B_in[0] = (CAS_IN_DIN_B[0] !== 1'bz) && CAS_IN_DIN_B[0]; // rv 0
  assign CAS_IN_DIN_B_in[10] = (CAS_IN_DIN_B[10] !== 1'bz) && CAS_IN_DIN_B[10]; // rv 0
  assign CAS_IN_DIN_B_in[11] = (CAS_IN_DIN_B[11] !== 1'bz) && CAS_IN_DIN_B[11]; // rv 0
  assign CAS_IN_DIN_B_in[12] = (CAS_IN_DIN_B[12] !== 1'bz) && CAS_IN_DIN_B[12]; // rv 0
  assign CAS_IN_DIN_B_in[13] = (CAS_IN_DIN_B[13] !== 1'bz) && CAS_IN_DIN_B[13]; // rv 0
  assign CAS_IN_DIN_B_in[14] = (CAS_IN_DIN_B[14] !== 1'bz) && CAS_IN_DIN_B[14]; // rv 0
  assign CAS_IN_DIN_B_in[15] = (CAS_IN_DIN_B[15] !== 1'bz) && CAS_IN_DIN_B[15]; // rv 0
  assign CAS_IN_DIN_B_in[16] = (CAS_IN_DIN_B[16] !== 1'bz) && CAS_IN_DIN_B[16]; // rv 0
  assign CAS_IN_DIN_B_in[17] = (CAS_IN_DIN_B[17] !== 1'bz) && CAS_IN_DIN_B[17]; // rv 0
  assign CAS_IN_DIN_B_in[18] = (CAS_IN_DIN_B[18] !== 1'bz) && CAS_IN_DIN_B[18]; // rv 0
  assign CAS_IN_DIN_B_in[19] = (CAS_IN_DIN_B[19] !== 1'bz) && CAS_IN_DIN_B[19]; // rv 0
  assign CAS_IN_DIN_B_in[1] = (CAS_IN_DIN_B[1] !== 1'bz) && CAS_IN_DIN_B[1]; // rv 0
  assign CAS_IN_DIN_B_in[20] = (CAS_IN_DIN_B[20] !== 1'bz) && CAS_IN_DIN_B[20]; // rv 0
  assign CAS_IN_DIN_B_in[21] = (CAS_IN_DIN_B[21] !== 1'bz) && CAS_IN_DIN_B[21]; // rv 0
  assign CAS_IN_DIN_B_in[22] = (CAS_IN_DIN_B[22] !== 1'bz) && CAS_IN_DIN_B[22]; // rv 0
  assign CAS_IN_DIN_B_in[23] = (CAS_IN_DIN_B[23] !== 1'bz) && CAS_IN_DIN_B[23]; // rv 0
  assign CAS_IN_DIN_B_in[24] = (CAS_IN_DIN_B[24] !== 1'bz) && CAS_IN_DIN_B[24]; // rv 0
  assign CAS_IN_DIN_B_in[25] = (CAS_IN_DIN_B[25] !== 1'bz) && CAS_IN_DIN_B[25]; // rv 0
  assign CAS_IN_DIN_B_in[26] = (CAS_IN_DIN_B[26] !== 1'bz) && CAS_IN_DIN_B[26]; // rv 0
  assign CAS_IN_DIN_B_in[27] = (CAS_IN_DIN_B[27] !== 1'bz) && CAS_IN_DIN_B[27]; // rv 0
  assign CAS_IN_DIN_B_in[28] = (CAS_IN_DIN_B[28] !== 1'bz) && CAS_IN_DIN_B[28]; // rv 0
  assign CAS_IN_DIN_B_in[29] = (CAS_IN_DIN_B[29] !== 1'bz) && CAS_IN_DIN_B[29]; // rv 0
  assign CAS_IN_DIN_B_in[2] = (CAS_IN_DIN_B[2] !== 1'bz) && CAS_IN_DIN_B[2]; // rv 0
  assign CAS_IN_DIN_B_in[30] = (CAS_IN_DIN_B[30] !== 1'bz) && CAS_IN_DIN_B[30]; // rv 0
  assign CAS_IN_DIN_B_in[31] = (CAS_IN_DIN_B[31] !== 1'bz) && CAS_IN_DIN_B[31]; // rv 0
  assign CAS_IN_DIN_B_in[32] = (CAS_IN_DIN_B[32] !== 1'bz) && CAS_IN_DIN_B[32]; // rv 0
  assign CAS_IN_DIN_B_in[33] = (CAS_IN_DIN_B[33] !== 1'bz) && CAS_IN_DIN_B[33]; // rv 0
  assign CAS_IN_DIN_B_in[34] = (CAS_IN_DIN_B[34] !== 1'bz) && CAS_IN_DIN_B[34]; // rv 0
  assign CAS_IN_DIN_B_in[35] = (CAS_IN_DIN_B[35] !== 1'bz) && CAS_IN_DIN_B[35]; // rv 0
  assign CAS_IN_DIN_B_in[36] = (CAS_IN_DIN_B[36] !== 1'bz) && CAS_IN_DIN_B[36]; // rv 0
  assign CAS_IN_DIN_B_in[37] = (CAS_IN_DIN_B[37] !== 1'bz) && CAS_IN_DIN_B[37]; // rv 0
  assign CAS_IN_DIN_B_in[38] = (CAS_IN_DIN_B[38] !== 1'bz) && CAS_IN_DIN_B[38]; // rv 0
  assign CAS_IN_DIN_B_in[39] = (CAS_IN_DIN_B[39] !== 1'bz) && CAS_IN_DIN_B[39]; // rv 0
  assign CAS_IN_DIN_B_in[3] = (CAS_IN_DIN_B[3] !== 1'bz) && CAS_IN_DIN_B[3]; // rv 0
  assign CAS_IN_DIN_B_in[40] = (CAS_IN_DIN_B[40] !== 1'bz) && CAS_IN_DIN_B[40]; // rv 0
  assign CAS_IN_DIN_B_in[41] = (CAS_IN_DIN_B[41] !== 1'bz) && CAS_IN_DIN_B[41]; // rv 0
  assign CAS_IN_DIN_B_in[42] = (CAS_IN_DIN_B[42] !== 1'bz) && CAS_IN_DIN_B[42]; // rv 0
  assign CAS_IN_DIN_B_in[43] = (CAS_IN_DIN_B[43] !== 1'bz) && CAS_IN_DIN_B[43]; // rv 0
  assign CAS_IN_DIN_B_in[44] = (CAS_IN_DIN_B[44] !== 1'bz) && CAS_IN_DIN_B[44]; // rv 0
  assign CAS_IN_DIN_B_in[45] = (CAS_IN_DIN_B[45] !== 1'bz) && CAS_IN_DIN_B[45]; // rv 0
  assign CAS_IN_DIN_B_in[46] = (CAS_IN_DIN_B[46] !== 1'bz) && CAS_IN_DIN_B[46]; // rv 0
  assign CAS_IN_DIN_B_in[47] = (CAS_IN_DIN_B[47] !== 1'bz) && CAS_IN_DIN_B[47]; // rv 0
  assign CAS_IN_DIN_B_in[48] = (CAS_IN_DIN_B[48] !== 1'bz) && CAS_IN_DIN_B[48]; // rv 0
  assign CAS_IN_DIN_B_in[49] = (CAS_IN_DIN_B[49] !== 1'bz) && CAS_IN_DIN_B[49]; // rv 0
  assign CAS_IN_DIN_B_in[4] = (CAS_IN_DIN_B[4] !== 1'bz) && CAS_IN_DIN_B[4]; // rv 0
  assign CAS_IN_DIN_B_in[50] = (CAS_IN_DIN_B[50] !== 1'bz) && CAS_IN_DIN_B[50]; // rv 0
  assign CAS_IN_DIN_B_in[51] = (CAS_IN_DIN_B[51] !== 1'bz) && CAS_IN_DIN_B[51]; // rv 0
  assign CAS_IN_DIN_B_in[52] = (CAS_IN_DIN_B[52] !== 1'bz) && CAS_IN_DIN_B[52]; // rv 0
  assign CAS_IN_DIN_B_in[53] = (CAS_IN_DIN_B[53] !== 1'bz) && CAS_IN_DIN_B[53]; // rv 0
  assign CAS_IN_DIN_B_in[54] = (CAS_IN_DIN_B[54] !== 1'bz) && CAS_IN_DIN_B[54]; // rv 0
  assign CAS_IN_DIN_B_in[55] = (CAS_IN_DIN_B[55] !== 1'bz) && CAS_IN_DIN_B[55]; // rv 0
  assign CAS_IN_DIN_B_in[56] = (CAS_IN_DIN_B[56] !== 1'bz) && CAS_IN_DIN_B[56]; // rv 0
  assign CAS_IN_DIN_B_in[57] = (CAS_IN_DIN_B[57] !== 1'bz) && CAS_IN_DIN_B[57]; // rv 0
  assign CAS_IN_DIN_B_in[58] = (CAS_IN_DIN_B[58] !== 1'bz) && CAS_IN_DIN_B[58]; // rv 0
  assign CAS_IN_DIN_B_in[59] = (CAS_IN_DIN_B[59] !== 1'bz) && CAS_IN_DIN_B[59]; // rv 0
  assign CAS_IN_DIN_B_in[5] = (CAS_IN_DIN_B[5] !== 1'bz) && CAS_IN_DIN_B[5]; // rv 0
  assign CAS_IN_DIN_B_in[60] = (CAS_IN_DIN_B[60] !== 1'bz) && CAS_IN_DIN_B[60]; // rv 0
  assign CAS_IN_DIN_B_in[61] = (CAS_IN_DIN_B[61] !== 1'bz) && CAS_IN_DIN_B[61]; // rv 0
  assign CAS_IN_DIN_B_in[62] = (CAS_IN_DIN_B[62] !== 1'bz) && CAS_IN_DIN_B[62]; // rv 0
  assign CAS_IN_DIN_B_in[63] = (CAS_IN_DIN_B[63] !== 1'bz) && CAS_IN_DIN_B[63]; // rv 0
  assign CAS_IN_DIN_B_in[64] = (CAS_IN_DIN_B[64] !== 1'bz) && CAS_IN_DIN_B[64]; // rv 0
  assign CAS_IN_DIN_B_in[65] = (CAS_IN_DIN_B[65] !== 1'bz) && CAS_IN_DIN_B[65]; // rv 0
  assign CAS_IN_DIN_B_in[66] = (CAS_IN_DIN_B[66] !== 1'bz) && CAS_IN_DIN_B[66]; // rv 0
  assign CAS_IN_DIN_B_in[67] = (CAS_IN_DIN_B[67] !== 1'bz) && CAS_IN_DIN_B[67]; // rv 0
  assign CAS_IN_DIN_B_in[68] = (CAS_IN_DIN_B[68] !== 1'bz) && CAS_IN_DIN_B[68]; // rv 0
  assign CAS_IN_DIN_B_in[69] = (CAS_IN_DIN_B[69] !== 1'bz) && CAS_IN_DIN_B[69]; // rv 0
  assign CAS_IN_DIN_B_in[6] = (CAS_IN_DIN_B[6] !== 1'bz) && CAS_IN_DIN_B[6]; // rv 0
  assign CAS_IN_DIN_B_in[70] = (CAS_IN_DIN_B[70] !== 1'bz) && CAS_IN_DIN_B[70]; // rv 0
  assign CAS_IN_DIN_B_in[71] = (CAS_IN_DIN_B[71] !== 1'bz) && CAS_IN_DIN_B[71]; // rv 0
  assign CAS_IN_DIN_B_in[7] = (CAS_IN_DIN_B[7] !== 1'bz) && CAS_IN_DIN_B[7]; // rv 0
  assign CAS_IN_DIN_B_in[8] = (CAS_IN_DIN_B[8] !== 1'bz) && CAS_IN_DIN_B[8]; // rv 0
  assign CAS_IN_DIN_B_in[9] = (CAS_IN_DIN_B[9] !== 1'bz) && CAS_IN_DIN_B[9]; // rv 0
  assign CAS_IN_DOUT_A_in[0] = (CAS_IN_DOUT_A[0] !== 1'bz) && CAS_IN_DOUT_A[0]; // rv 0
  assign CAS_IN_DOUT_A_in[10] = (CAS_IN_DOUT_A[10] !== 1'bz) && CAS_IN_DOUT_A[10]; // rv 0
  assign CAS_IN_DOUT_A_in[11] = (CAS_IN_DOUT_A[11] !== 1'bz) && CAS_IN_DOUT_A[11]; // rv 0
  assign CAS_IN_DOUT_A_in[12] = (CAS_IN_DOUT_A[12] !== 1'bz) && CAS_IN_DOUT_A[12]; // rv 0
  assign CAS_IN_DOUT_A_in[13] = (CAS_IN_DOUT_A[13] !== 1'bz) && CAS_IN_DOUT_A[13]; // rv 0
  assign CAS_IN_DOUT_A_in[14] = (CAS_IN_DOUT_A[14] !== 1'bz) && CAS_IN_DOUT_A[14]; // rv 0
  assign CAS_IN_DOUT_A_in[15] = (CAS_IN_DOUT_A[15] !== 1'bz) && CAS_IN_DOUT_A[15]; // rv 0
  assign CAS_IN_DOUT_A_in[16] = (CAS_IN_DOUT_A[16] !== 1'bz) && CAS_IN_DOUT_A[16]; // rv 0
  assign CAS_IN_DOUT_A_in[17] = (CAS_IN_DOUT_A[17] !== 1'bz) && CAS_IN_DOUT_A[17]; // rv 0
  assign CAS_IN_DOUT_A_in[18] = (CAS_IN_DOUT_A[18] !== 1'bz) && CAS_IN_DOUT_A[18]; // rv 0
  assign CAS_IN_DOUT_A_in[19] = (CAS_IN_DOUT_A[19] !== 1'bz) && CAS_IN_DOUT_A[19]; // rv 0
  assign CAS_IN_DOUT_A_in[1] = (CAS_IN_DOUT_A[1] !== 1'bz) && CAS_IN_DOUT_A[1]; // rv 0
  assign CAS_IN_DOUT_A_in[20] = (CAS_IN_DOUT_A[20] !== 1'bz) && CAS_IN_DOUT_A[20]; // rv 0
  assign CAS_IN_DOUT_A_in[21] = (CAS_IN_DOUT_A[21] !== 1'bz) && CAS_IN_DOUT_A[21]; // rv 0
  assign CAS_IN_DOUT_A_in[22] = (CAS_IN_DOUT_A[22] !== 1'bz) && CAS_IN_DOUT_A[22]; // rv 0
  assign CAS_IN_DOUT_A_in[23] = (CAS_IN_DOUT_A[23] !== 1'bz) && CAS_IN_DOUT_A[23]; // rv 0
  assign CAS_IN_DOUT_A_in[24] = (CAS_IN_DOUT_A[24] !== 1'bz) && CAS_IN_DOUT_A[24]; // rv 0
  assign CAS_IN_DOUT_A_in[25] = (CAS_IN_DOUT_A[25] !== 1'bz) && CAS_IN_DOUT_A[25]; // rv 0
  assign CAS_IN_DOUT_A_in[26] = (CAS_IN_DOUT_A[26] !== 1'bz) && CAS_IN_DOUT_A[26]; // rv 0
  assign CAS_IN_DOUT_A_in[27] = (CAS_IN_DOUT_A[27] !== 1'bz) && CAS_IN_DOUT_A[27]; // rv 0
  assign CAS_IN_DOUT_A_in[28] = (CAS_IN_DOUT_A[28] !== 1'bz) && CAS_IN_DOUT_A[28]; // rv 0
  assign CAS_IN_DOUT_A_in[29] = (CAS_IN_DOUT_A[29] !== 1'bz) && CAS_IN_DOUT_A[29]; // rv 0
  assign CAS_IN_DOUT_A_in[2] = (CAS_IN_DOUT_A[2] !== 1'bz) && CAS_IN_DOUT_A[2]; // rv 0
  assign CAS_IN_DOUT_A_in[30] = (CAS_IN_DOUT_A[30] !== 1'bz) && CAS_IN_DOUT_A[30]; // rv 0
  assign CAS_IN_DOUT_A_in[31] = (CAS_IN_DOUT_A[31] !== 1'bz) && CAS_IN_DOUT_A[31]; // rv 0
  assign CAS_IN_DOUT_A_in[32] = (CAS_IN_DOUT_A[32] !== 1'bz) && CAS_IN_DOUT_A[32]; // rv 0
  assign CAS_IN_DOUT_A_in[33] = (CAS_IN_DOUT_A[33] !== 1'bz) && CAS_IN_DOUT_A[33]; // rv 0
  assign CAS_IN_DOUT_A_in[34] = (CAS_IN_DOUT_A[34] !== 1'bz) && CAS_IN_DOUT_A[34]; // rv 0
  assign CAS_IN_DOUT_A_in[35] = (CAS_IN_DOUT_A[35] !== 1'bz) && CAS_IN_DOUT_A[35]; // rv 0
  assign CAS_IN_DOUT_A_in[36] = (CAS_IN_DOUT_A[36] !== 1'bz) && CAS_IN_DOUT_A[36]; // rv 0
  assign CAS_IN_DOUT_A_in[37] = (CAS_IN_DOUT_A[37] !== 1'bz) && CAS_IN_DOUT_A[37]; // rv 0
  assign CAS_IN_DOUT_A_in[38] = (CAS_IN_DOUT_A[38] !== 1'bz) && CAS_IN_DOUT_A[38]; // rv 0
  assign CAS_IN_DOUT_A_in[39] = (CAS_IN_DOUT_A[39] !== 1'bz) && CAS_IN_DOUT_A[39]; // rv 0
  assign CAS_IN_DOUT_A_in[3] = (CAS_IN_DOUT_A[3] !== 1'bz) && CAS_IN_DOUT_A[3]; // rv 0
  assign CAS_IN_DOUT_A_in[40] = (CAS_IN_DOUT_A[40] !== 1'bz) && CAS_IN_DOUT_A[40]; // rv 0
  assign CAS_IN_DOUT_A_in[41] = (CAS_IN_DOUT_A[41] !== 1'bz) && CAS_IN_DOUT_A[41]; // rv 0
  assign CAS_IN_DOUT_A_in[42] = (CAS_IN_DOUT_A[42] !== 1'bz) && CAS_IN_DOUT_A[42]; // rv 0
  assign CAS_IN_DOUT_A_in[43] = (CAS_IN_DOUT_A[43] !== 1'bz) && CAS_IN_DOUT_A[43]; // rv 0
  assign CAS_IN_DOUT_A_in[44] = (CAS_IN_DOUT_A[44] !== 1'bz) && CAS_IN_DOUT_A[44]; // rv 0
  assign CAS_IN_DOUT_A_in[45] = (CAS_IN_DOUT_A[45] !== 1'bz) && CAS_IN_DOUT_A[45]; // rv 0
  assign CAS_IN_DOUT_A_in[46] = (CAS_IN_DOUT_A[46] !== 1'bz) && CAS_IN_DOUT_A[46]; // rv 0
  assign CAS_IN_DOUT_A_in[47] = (CAS_IN_DOUT_A[47] !== 1'bz) && CAS_IN_DOUT_A[47]; // rv 0
  assign CAS_IN_DOUT_A_in[48] = (CAS_IN_DOUT_A[48] !== 1'bz) && CAS_IN_DOUT_A[48]; // rv 0
  assign CAS_IN_DOUT_A_in[49] = (CAS_IN_DOUT_A[49] !== 1'bz) && CAS_IN_DOUT_A[49]; // rv 0
  assign CAS_IN_DOUT_A_in[4] = (CAS_IN_DOUT_A[4] !== 1'bz) && CAS_IN_DOUT_A[4]; // rv 0
  assign CAS_IN_DOUT_A_in[50] = (CAS_IN_DOUT_A[50] !== 1'bz) && CAS_IN_DOUT_A[50]; // rv 0
  assign CAS_IN_DOUT_A_in[51] = (CAS_IN_DOUT_A[51] !== 1'bz) && CAS_IN_DOUT_A[51]; // rv 0
  assign CAS_IN_DOUT_A_in[52] = (CAS_IN_DOUT_A[52] !== 1'bz) && CAS_IN_DOUT_A[52]; // rv 0
  assign CAS_IN_DOUT_A_in[53] = (CAS_IN_DOUT_A[53] !== 1'bz) && CAS_IN_DOUT_A[53]; // rv 0
  assign CAS_IN_DOUT_A_in[54] = (CAS_IN_DOUT_A[54] !== 1'bz) && CAS_IN_DOUT_A[54]; // rv 0
  assign CAS_IN_DOUT_A_in[55] = (CAS_IN_DOUT_A[55] !== 1'bz) && CAS_IN_DOUT_A[55]; // rv 0
  assign CAS_IN_DOUT_A_in[56] = (CAS_IN_DOUT_A[56] !== 1'bz) && CAS_IN_DOUT_A[56]; // rv 0
  assign CAS_IN_DOUT_A_in[57] = (CAS_IN_DOUT_A[57] !== 1'bz) && CAS_IN_DOUT_A[57]; // rv 0
  assign CAS_IN_DOUT_A_in[58] = (CAS_IN_DOUT_A[58] !== 1'bz) && CAS_IN_DOUT_A[58]; // rv 0
  assign CAS_IN_DOUT_A_in[59] = (CAS_IN_DOUT_A[59] !== 1'bz) && CAS_IN_DOUT_A[59]; // rv 0
  assign CAS_IN_DOUT_A_in[5] = (CAS_IN_DOUT_A[5] !== 1'bz) && CAS_IN_DOUT_A[5]; // rv 0
  assign CAS_IN_DOUT_A_in[60] = (CAS_IN_DOUT_A[60] !== 1'bz) && CAS_IN_DOUT_A[60]; // rv 0
  assign CAS_IN_DOUT_A_in[61] = (CAS_IN_DOUT_A[61] !== 1'bz) && CAS_IN_DOUT_A[61]; // rv 0
  assign CAS_IN_DOUT_A_in[62] = (CAS_IN_DOUT_A[62] !== 1'bz) && CAS_IN_DOUT_A[62]; // rv 0
  assign CAS_IN_DOUT_A_in[63] = (CAS_IN_DOUT_A[63] !== 1'bz) && CAS_IN_DOUT_A[63]; // rv 0
  assign CAS_IN_DOUT_A_in[64] = (CAS_IN_DOUT_A[64] !== 1'bz) && CAS_IN_DOUT_A[64]; // rv 0
  assign CAS_IN_DOUT_A_in[65] = (CAS_IN_DOUT_A[65] !== 1'bz) && CAS_IN_DOUT_A[65]; // rv 0
  assign CAS_IN_DOUT_A_in[66] = (CAS_IN_DOUT_A[66] !== 1'bz) && CAS_IN_DOUT_A[66]; // rv 0
  assign CAS_IN_DOUT_A_in[67] = (CAS_IN_DOUT_A[67] !== 1'bz) && CAS_IN_DOUT_A[67]; // rv 0
  assign CAS_IN_DOUT_A_in[68] = (CAS_IN_DOUT_A[68] !== 1'bz) && CAS_IN_DOUT_A[68]; // rv 0
  assign CAS_IN_DOUT_A_in[69] = (CAS_IN_DOUT_A[69] !== 1'bz) && CAS_IN_DOUT_A[69]; // rv 0
  assign CAS_IN_DOUT_A_in[6] = (CAS_IN_DOUT_A[6] !== 1'bz) && CAS_IN_DOUT_A[6]; // rv 0
  assign CAS_IN_DOUT_A_in[70] = (CAS_IN_DOUT_A[70] !== 1'bz) && CAS_IN_DOUT_A[70]; // rv 0
  assign CAS_IN_DOUT_A_in[71] = (CAS_IN_DOUT_A[71] !== 1'bz) && CAS_IN_DOUT_A[71]; // rv 0
  assign CAS_IN_DOUT_A_in[7] = (CAS_IN_DOUT_A[7] !== 1'bz) && CAS_IN_DOUT_A[7]; // rv 0
  assign CAS_IN_DOUT_A_in[8] = (CAS_IN_DOUT_A[8] !== 1'bz) && CAS_IN_DOUT_A[8]; // rv 0
  assign CAS_IN_DOUT_A_in[9] = (CAS_IN_DOUT_A[9] !== 1'bz) && CAS_IN_DOUT_A[9]; // rv 0
  assign CAS_IN_DOUT_B_in[0] = (CAS_IN_DOUT_B[0] !== 1'bz) && CAS_IN_DOUT_B[0]; // rv 0
  assign CAS_IN_DOUT_B_in[10] = (CAS_IN_DOUT_B[10] !== 1'bz) && CAS_IN_DOUT_B[10]; // rv 0
  assign CAS_IN_DOUT_B_in[11] = (CAS_IN_DOUT_B[11] !== 1'bz) && CAS_IN_DOUT_B[11]; // rv 0
  assign CAS_IN_DOUT_B_in[12] = (CAS_IN_DOUT_B[12] !== 1'bz) && CAS_IN_DOUT_B[12]; // rv 0
  assign CAS_IN_DOUT_B_in[13] = (CAS_IN_DOUT_B[13] !== 1'bz) && CAS_IN_DOUT_B[13]; // rv 0
  assign CAS_IN_DOUT_B_in[14] = (CAS_IN_DOUT_B[14] !== 1'bz) && CAS_IN_DOUT_B[14]; // rv 0
  assign CAS_IN_DOUT_B_in[15] = (CAS_IN_DOUT_B[15] !== 1'bz) && CAS_IN_DOUT_B[15]; // rv 0
  assign CAS_IN_DOUT_B_in[16] = (CAS_IN_DOUT_B[16] !== 1'bz) && CAS_IN_DOUT_B[16]; // rv 0
  assign CAS_IN_DOUT_B_in[17] = (CAS_IN_DOUT_B[17] !== 1'bz) && CAS_IN_DOUT_B[17]; // rv 0
  assign CAS_IN_DOUT_B_in[18] = (CAS_IN_DOUT_B[18] !== 1'bz) && CAS_IN_DOUT_B[18]; // rv 0
  assign CAS_IN_DOUT_B_in[19] = (CAS_IN_DOUT_B[19] !== 1'bz) && CAS_IN_DOUT_B[19]; // rv 0
  assign CAS_IN_DOUT_B_in[1] = (CAS_IN_DOUT_B[1] !== 1'bz) && CAS_IN_DOUT_B[1]; // rv 0
  assign CAS_IN_DOUT_B_in[20] = (CAS_IN_DOUT_B[20] !== 1'bz) && CAS_IN_DOUT_B[20]; // rv 0
  assign CAS_IN_DOUT_B_in[21] = (CAS_IN_DOUT_B[21] !== 1'bz) && CAS_IN_DOUT_B[21]; // rv 0
  assign CAS_IN_DOUT_B_in[22] = (CAS_IN_DOUT_B[22] !== 1'bz) && CAS_IN_DOUT_B[22]; // rv 0
  assign CAS_IN_DOUT_B_in[23] = (CAS_IN_DOUT_B[23] !== 1'bz) && CAS_IN_DOUT_B[23]; // rv 0
  assign CAS_IN_DOUT_B_in[24] = (CAS_IN_DOUT_B[24] !== 1'bz) && CAS_IN_DOUT_B[24]; // rv 0
  assign CAS_IN_DOUT_B_in[25] = (CAS_IN_DOUT_B[25] !== 1'bz) && CAS_IN_DOUT_B[25]; // rv 0
  assign CAS_IN_DOUT_B_in[26] = (CAS_IN_DOUT_B[26] !== 1'bz) && CAS_IN_DOUT_B[26]; // rv 0
  assign CAS_IN_DOUT_B_in[27] = (CAS_IN_DOUT_B[27] !== 1'bz) && CAS_IN_DOUT_B[27]; // rv 0
  assign CAS_IN_DOUT_B_in[28] = (CAS_IN_DOUT_B[28] !== 1'bz) && CAS_IN_DOUT_B[28]; // rv 0
  assign CAS_IN_DOUT_B_in[29] = (CAS_IN_DOUT_B[29] !== 1'bz) && CAS_IN_DOUT_B[29]; // rv 0
  assign CAS_IN_DOUT_B_in[2] = (CAS_IN_DOUT_B[2] !== 1'bz) && CAS_IN_DOUT_B[2]; // rv 0
  assign CAS_IN_DOUT_B_in[30] = (CAS_IN_DOUT_B[30] !== 1'bz) && CAS_IN_DOUT_B[30]; // rv 0
  assign CAS_IN_DOUT_B_in[31] = (CAS_IN_DOUT_B[31] !== 1'bz) && CAS_IN_DOUT_B[31]; // rv 0
  assign CAS_IN_DOUT_B_in[32] = (CAS_IN_DOUT_B[32] !== 1'bz) && CAS_IN_DOUT_B[32]; // rv 0
  assign CAS_IN_DOUT_B_in[33] = (CAS_IN_DOUT_B[33] !== 1'bz) && CAS_IN_DOUT_B[33]; // rv 0
  assign CAS_IN_DOUT_B_in[34] = (CAS_IN_DOUT_B[34] !== 1'bz) && CAS_IN_DOUT_B[34]; // rv 0
  assign CAS_IN_DOUT_B_in[35] = (CAS_IN_DOUT_B[35] !== 1'bz) && CAS_IN_DOUT_B[35]; // rv 0
  assign CAS_IN_DOUT_B_in[36] = (CAS_IN_DOUT_B[36] !== 1'bz) && CAS_IN_DOUT_B[36]; // rv 0
  assign CAS_IN_DOUT_B_in[37] = (CAS_IN_DOUT_B[37] !== 1'bz) && CAS_IN_DOUT_B[37]; // rv 0
  assign CAS_IN_DOUT_B_in[38] = (CAS_IN_DOUT_B[38] !== 1'bz) && CAS_IN_DOUT_B[38]; // rv 0
  assign CAS_IN_DOUT_B_in[39] = (CAS_IN_DOUT_B[39] !== 1'bz) && CAS_IN_DOUT_B[39]; // rv 0
  assign CAS_IN_DOUT_B_in[3] = (CAS_IN_DOUT_B[3] !== 1'bz) && CAS_IN_DOUT_B[3]; // rv 0
  assign CAS_IN_DOUT_B_in[40] = (CAS_IN_DOUT_B[40] !== 1'bz) && CAS_IN_DOUT_B[40]; // rv 0
  assign CAS_IN_DOUT_B_in[41] = (CAS_IN_DOUT_B[41] !== 1'bz) && CAS_IN_DOUT_B[41]; // rv 0
  assign CAS_IN_DOUT_B_in[42] = (CAS_IN_DOUT_B[42] !== 1'bz) && CAS_IN_DOUT_B[42]; // rv 0
  assign CAS_IN_DOUT_B_in[43] = (CAS_IN_DOUT_B[43] !== 1'bz) && CAS_IN_DOUT_B[43]; // rv 0
  assign CAS_IN_DOUT_B_in[44] = (CAS_IN_DOUT_B[44] !== 1'bz) && CAS_IN_DOUT_B[44]; // rv 0
  assign CAS_IN_DOUT_B_in[45] = (CAS_IN_DOUT_B[45] !== 1'bz) && CAS_IN_DOUT_B[45]; // rv 0
  assign CAS_IN_DOUT_B_in[46] = (CAS_IN_DOUT_B[46] !== 1'bz) && CAS_IN_DOUT_B[46]; // rv 0
  assign CAS_IN_DOUT_B_in[47] = (CAS_IN_DOUT_B[47] !== 1'bz) && CAS_IN_DOUT_B[47]; // rv 0
  assign CAS_IN_DOUT_B_in[48] = (CAS_IN_DOUT_B[48] !== 1'bz) && CAS_IN_DOUT_B[48]; // rv 0
  assign CAS_IN_DOUT_B_in[49] = (CAS_IN_DOUT_B[49] !== 1'bz) && CAS_IN_DOUT_B[49]; // rv 0
  assign CAS_IN_DOUT_B_in[4] = (CAS_IN_DOUT_B[4] !== 1'bz) && CAS_IN_DOUT_B[4]; // rv 0
  assign CAS_IN_DOUT_B_in[50] = (CAS_IN_DOUT_B[50] !== 1'bz) && CAS_IN_DOUT_B[50]; // rv 0
  assign CAS_IN_DOUT_B_in[51] = (CAS_IN_DOUT_B[51] !== 1'bz) && CAS_IN_DOUT_B[51]; // rv 0
  assign CAS_IN_DOUT_B_in[52] = (CAS_IN_DOUT_B[52] !== 1'bz) && CAS_IN_DOUT_B[52]; // rv 0
  assign CAS_IN_DOUT_B_in[53] = (CAS_IN_DOUT_B[53] !== 1'bz) && CAS_IN_DOUT_B[53]; // rv 0
  assign CAS_IN_DOUT_B_in[54] = (CAS_IN_DOUT_B[54] !== 1'bz) && CAS_IN_DOUT_B[54]; // rv 0
  assign CAS_IN_DOUT_B_in[55] = (CAS_IN_DOUT_B[55] !== 1'bz) && CAS_IN_DOUT_B[55]; // rv 0
  assign CAS_IN_DOUT_B_in[56] = (CAS_IN_DOUT_B[56] !== 1'bz) && CAS_IN_DOUT_B[56]; // rv 0
  assign CAS_IN_DOUT_B_in[57] = (CAS_IN_DOUT_B[57] !== 1'bz) && CAS_IN_DOUT_B[57]; // rv 0
  assign CAS_IN_DOUT_B_in[58] = (CAS_IN_DOUT_B[58] !== 1'bz) && CAS_IN_DOUT_B[58]; // rv 0
  assign CAS_IN_DOUT_B_in[59] = (CAS_IN_DOUT_B[59] !== 1'bz) && CAS_IN_DOUT_B[59]; // rv 0
  assign CAS_IN_DOUT_B_in[5] = (CAS_IN_DOUT_B[5] !== 1'bz) && CAS_IN_DOUT_B[5]; // rv 0
  assign CAS_IN_DOUT_B_in[60] = (CAS_IN_DOUT_B[60] !== 1'bz) && CAS_IN_DOUT_B[60]; // rv 0
  assign CAS_IN_DOUT_B_in[61] = (CAS_IN_DOUT_B[61] !== 1'bz) && CAS_IN_DOUT_B[61]; // rv 0
  assign CAS_IN_DOUT_B_in[62] = (CAS_IN_DOUT_B[62] !== 1'bz) && CAS_IN_DOUT_B[62]; // rv 0
  assign CAS_IN_DOUT_B_in[63] = (CAS_IN_DOUT_B[63] !== 1'bz) && CAS_IN_DOUT_B[63]; // rv 0
  assign CAS_IN_DOUT_B_in[64] = (CAS_IN_DOUT_B[64] !== 1'bz) && CAS_IN_DOUT_B[64]; // rv 0
  assign CAS_IN_DOUT_B_in[65] = (CAS_IN_DOUT_B[65] !== 1'bz) && CAS_IN_DOUT_B[65]; // rv 0
  assign CAS_IN_DOUT_B_in[66] = (CAS_IN_DOUT_B[66] !== 1'bz) && CAS_IN_DOUT_B[66]; // rv 0
  assign CAS_IN_DOUT_B_in[67] = (CAS_IN_DOUT_B[67] !== 1'bz) && CAS_IN_DOUT_B[67]; // rv 0
  assign CAS_IN_DOUT_B_in[68] = (CAS_IN_DOUT_B[68] !== 1'bz) && CAS_IN_DOUT_B[68]; // rv 0
  assign CAS_IN_DOUT_B_in[69] = (CAS_IN_DOUT_B[69] !== 1'bz) && CAS_IN_DOUT_B[69]; // rv 0
  assign CAS_IN_DOUT_B_in[6] = (CAS_IN_DOUT_B[6] !== 1'bz) && CAS_IN_DOUT_B[6]; // rv 0
  assign CAS_IN_DOUT_B_in[70] = (CAS_IN_DOUT_B[70] !== 1'bz) && CAS_IN_DOUT_B[70]; // rv 0
  assign CAS_IN_DOUT_B_in[71] = (CAS_IN_DOUT_B[71] !== 1'bz) && CAS_IN_DOUT_B[71]; // rv 0
  assign CAS_IN_DOUT_B_in[7] = (CAS_IN_DOUT_B[7] !== 1'bz) && CAS_IN_DOUT_B[7]; // rv 0
  assign CAS_IN_DOUT_B_in[8] = (CAS_IN_DOUT_B[8] !== 1'bz) && CAS_IN_DOUT_B[8]; // rv 0
  assign CAS_IN_DOUT_B_in[9] = (CAS_IN_DOUT_B[9] !== 1'bz) && CAS_IN_DOUT_B[9]; // rv 0
  assign CAS_IN_EN_A_in = (CAS_IN_EN_A !== 1'bz) && CAS_IN_EN_A; // rv 0
  assign CAS_IN_EN_B_in = (CAS_IN_EN_B !== 1'bz) && CAS_IN_EN_B; // rv 0
  assign CAS_IN_RDACCESS_A_in = (CAS_IN_RDACCESS_A !== 1'bz) && CAS_IN_RDACCESS_A; // rv 0
  assign CAS_IN_RDACCESS_B_in = (CAS_IN_RDACCESS_B !== 1'bz) && CAS_IN_RDACCESS_B; // rv 0
  assign CAS_IN_RDB_WR_A_in = (CAS_IN_RDB_WR_A !== 1'bz) && CAS_IN_RDB_WR_A; // rv 0
  assign CAS_IN_RDB_WR_B_in = (CAS_IN_RDB_WR_B !== 1'bz) && CAS_IN_RDB_WR_B; // rv 0
  assign CAS_IN_SBITERR_A_in = (CAS_IN_SBITERR_A !== 1'bz) && CAS_IN_SBITERR_A; // rv 0
  assign CAS_IN_SBITERR_B_in = (CAS_IN_SBITERR_B !== 1'bz) && CAS_IN_SBITERR_B; // rv 0
  assign CLK_in = (CLK !== 1'bz) && (CLK ^ IS_CLK_INVERTED_REG); // rv 0
  assign DIN_A_in = DIN_A;
  assign DIN_B_in = DIN_B;
  assign EN_A_in = (EN_A !== 1'bz) && (EN_A ^ IS_EN_A_INVERTED_REG); // rv 0
  assign EN_B_in = (EN_B !== 1'bz) && (EN_B ^ IS_EN_B_INVERTED_REG); // rv 0
  assign INJECT_DBITERR_A_in = (INJECT_DBITERR_A !== 1'bz) && INJECT_DBITERR_A; // rv 0
  assign INJECT_DBITERR_B_in = (INJECT_DBITERR_B !== 1'bz) && INJECT_DBITERR_B; // rv 0
  assign INJECT_SBITERR_A_in = (INJECT_SBITERR_A !== 1'bz) && INJECT_SBITERR_A; // rv 0
  assign INJECT_SBITERR_B_in = (INJECT_SBITERR_B !== 1'bz) && INJECT_SBITERR_B; // rv 0
  assign OREG_CE_A_in = (OREG_CE_A === 1'bz) || OREG_CE_A; // rv 1
  assign OREG_CE_B_in = (OREG_CE_B === 1'bz) || OREG_CE_B; // rv 1
  assign OREG_ECC_CE_A_in = (OREG_ECC_CE_A === 1'bz) || OREG_ECC_CE_A; // rv 1
  assign OREG_ECC_CE_B_in = (OREG_ECC_CE_B === 1'bz) || OREG_ECC_CE_B; // rv 1
  assign RDB_WR_A_in = (RDB_WR_A !== 1'bz) && (RDB_WR_A ^ IS_RDB_WR_A_INVERTED_REG); // rv 0
  assign RDB_WR_B_in = (RDB_WR_B !== 1'bz) && (RDB_WR_B ^ IS_RDB_WR_B_INVERTED_REG); // rv 0
  assign RST_A_in = (RST_A !== 1'bz) && (RST_A ^ IS_RST_A_INVERTED_REG); // rv 0
  assign RST_B_in = (RST_B !== 1'bz) && (RST_B ^ IS_RST_B_INVERTED_REG); // rv 0
  assign SLEEP_in = (SLEEP !== 1'bz) && SLEEP; // rv 0
`endif 

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
  assign AUTO_SLEEP_LATENCY_BIN = AUTO_SLEEP_LATENCY_REG[3:0];

  assign AVG_CONS_INACTIVE_CYCLES_BIN = AVG_CONS_INACTIVE_CYCLES_REG[16:0];

  assign BWE_MODE_A_BIN =
    (BWE_MODE_A_REG == "PARITY_INTERLEAVED") ? BWE_MODE_A_PARITY_INTERLEAVED :
    (BWE_MODE_A_REG == "PARITY_INDEPENDENT") ? BWE_MODE_A_PARITY_INDEPENDENT :
     BWE_MODE_A_PARITY_INTERLEAVED;

  assign BWE_MODE_B_BIN =
    (BWE_MODE_B_REG == "PARITY_INTERLEAVED") ? BWE_MODE_B_PARITY_INTERLEAVED :
    (BWE_MODE_B_REG == "PARITY_INDEPENDENT") ? BWE_MODE_B_PARITY_INDEPENDENT :
     BWE_MODE_B_PARITY_INTERLEAVED;

  assign CASCADE_ORDER_A_BIN =
    (CASCADE_ORDER_A_REG == "NONE") ? CASCADE_ORDER_A_NONE :
    (CASCADE_ORDER_A_REG == "FIRST") ? CASCADE_ORDER_A_FIRST :
    (CASCADE_ORDER_A_REG == "LAST") ? CASCADE_ORDER_A_LAST :
    (CASCADE_ORDER_A_REG == "MIDDLE") ? CASCADE_ORDER_A_MIDDLE :
     CASCADE_ORDER_A_NONE;

  assign CASCADE_ORDER_B_BIN =
    (CASCADE_ORDER_B_REG == "NONE") ? CASCADE_ORDER_B_NONE :
    (CASCADE_ORDER_B_REG == "FIRST") ? CASCADE_ORDER_B_FIRST :
    (CASCADE_ORDER_B_REG == "LAST") ? CASCADE_ORDER_B_LAST :
    (CASCADE_ORDER_B_REG == "MIDDLE") ? CASCADE_ORDER_B_MIDDLE :
     CASCADE_ORDER_B_NONE;

  assign EN_AUTO_SLEEP_MODE_BIN =
      (EN_AUTO_SLEEP_MODE_REG == "FALSE") ? EN_AUTO_SLEEP_MODE_FALSE :
      (EN_AUTO_SLEEP_MODE_REG == "TRUE") ? EN_AUTO_SLEEP_MODE_TRUE :
       EN_AUTO_SLEEP_MODE_FALSE;
  
  assign EN_ECC_RD_A_BIN =
    (EN_ECC_RD_A_REG == "FALSE") ? EN_ECC_RD_A_FALSE :
    (EN_ECC_RD_A_REG == "TRUE") ? EN_ECC_RD_A_TRUE :
     EN_ECC_RD_A_FALSE;

  assign EN_ECC_RD_B_BIN =
    (EN_ECC_RD_B_REG == "FALSE") ? EN_ECC_RD_B_FALSE :
    (EN_ECC_RD_B_REG == "TRUE") ? EN_ECC_RD_B_TRUE :
     EN_ECC_RD_B_FALSE;

  assign EN_ECC_WR_A_BIN =
    (EN_ECC_WR_A_REG == "FALSE") ? EN_ECC_WR_A_FALSE :
    (EN_ECC_WR_A_REG == "TRUE") ? EN_ECC_WR_A_TRUE :
     EN_ECC_WR_A_FALSE;

  assign EN_ECC_WR_B_BIN =
    (EN_ECC_WR_B_REG == "FALSE") ? EN_ECC_WR_B_FALSE :
    (EN_ECC_WR_B_REG == "TRUE") ? EN_ECC_WR_B_TRUE :
     EN_ECC_WR_B_FALSE;

  assign IREG_PRE_A_BIN =
    (IREG_PRE_A_REG == "FALSE") ? IREG_PRE_A_FALSE :
    (IREG_PRE_A_REG == "TRUE") ? IREG_PRE_A_TRUE :
     IREG_PRE_A_FALSE;

  assign IREG_PRE_B_BIN =
    (IREG_PRE_B_REG == "FALSE") ? IREG_PRE_B_FALSE :
    (IREG_PRE_B_REG == "TRUE") ? IREG_PRE_B_TRUE :
     IREG_PRE_B_FALSE;

  assign NUM_UNIQUE_SELF_ADDR_A_BIN = NUM_UNIQUE_SELF_ADDR_A_REG[11:0];
  
  assign NUM_UNIQUE_SELF_ADDR_B_BIN = NUM_UNIQUE_SELF_ADDR_B_REG[11:0];
  
  assign NUM_URAM_IN_MATRIX_BIN = NUM_URAM_IN_MATRIX_REG[11:0];

  assign OREG_A_BIN =
    (OREG_A_REG == "FALSE") ? OREG_A_FALSE :
    (OREG_A_REG == "TRUE") ? OREG_A_TRUE :
     OREG_A_FALSE;

  assign OREG_B_BIN =
    (OREG_B_REG == "FALSE") ? OREG_B_FALSE :
    (OREG_B_REG == "TRUE") ? OREG_B_TRUE :
     OREG_B_FALSE;

  assign OREG_ECC_A_BIN =
    (OREG_ECC_A_REG == "FALSE") ? OREG_ECC_A_FALSE :
    (OREG_ECC_A_REG == "TRUE") ? OREG_ECC_A_TRUE :
     OREG_ECC_A_FALSE;

  assign OREG_ECC_B_BIN =
    (OREG_ECC_B_REG == "FALSE") ? OREG_ECC_B_FALSE :
    (OREG_ECC_B_REG == "TRUE") ? OREG_ECC_B_TRUE :
     OREG_ECC_B_FALSE;

  assign REG_CAS_A_BIN =
    (REG_CAS_A_REG == "FALSE") ? REG_CAS_A_FALSE :
    (REG_CAS_A_REG == "TRUE") ? REG_CAS_A_TRUE :
    REG_CAS_A_FALSE;

  assign REG_CAS_B_BIN =
    (REG_CAS_B_REG == "FALSE") ? REG_CAS_B_FALSE :
    (REG_CAS_B_REG == "TRUE") ? REG_CAS_B_TRUE :
    REG_CAS_B_FALSE;

  assign RST_MODE_A_BIN =
    (RST_MODE_A_REG == "SYNC") ? RST_MODE_A_SYNC :
    (RST_MODE_A_REG == "ASYNC") ? RST_MODE_A_ASYNC :
     RST_MODE_A_SYNC;

  assign RST_MODE_B_BIN =
    (RST_MODE_B_REG == "SYNC") ? RST_MODE_B_SYNC :
    (RST_MODE_B_REG == "ASYNC") ? RST_MODE_B_ASYNC :
     RST_MODE_B_SYNC;

  assign USE_EXT_CE_A_BIN =
    (USE_EXT_CE_A_REG == "FALSE") ? USE_EXT_CE_A_FALSE :
    (USE_EXT_CE_A_REG == "TRUE") ? USE_EXT_CE_A_TRUE :
     USE_EXT_CE_A_FALSE;

  assign USE_EXT_CE_B_BIN =
    (USE_EXT_CE_B_REG == "FALSE") ? USE_EXT_CE_B_FALSE :
    (USE_EXT_CE_B_REG == "TRUE") ? USE_EXT_CE_B_TRUE :
     USE_EXT_CE_B_FALSE;

`else
  always @ (trig_attr) begin
    #1;
    AUTO_SLEEP_LATENCY_BIN = AUTO_SLEEP_LATENCY_REG[3:0];

    AVG_CONS_INACTIVE_CYCLES_BIN = AVG_CONS_INACTIVE_CYCLES_REG[16:0];

    BWE_MODE_A_BIN =
      (BWE_MODE_A_REG == "PARITY_INTERLEAVED") ? BWE_MODE_A_PARITY_INTERLEAVED :
      (BWE_MODE_A_REG == "PARITY_INDEPENDENT") ? BWE_MODE_A_PARITY_INDEPENDENT :
       BWE_MODE_A_PARITY_INTERLEAVED;

    BWE_MODE_B_BIN =
      (BWE_MODE_B_REG == "PARITY_INTERLEAVED") ? BWE_MODE_B_PARITY_INTERLEAVED :
      (BWE_MODE_B_REG == "PARITY_INDEPENDENT") ? BWE_MODE_B_PARITY_INDEPENDENT :
       BWE_MODE_B_PARITY_INTERLEAVED;

    CASCADE_ORDER_A_BIN =
       (CASCADE_ORDER_A_REG == "NONE") ? CASCADE_ORDER_A_NONE :
       (CASCADE_ORDER_A_REG == "FIRST") ? CASCADE_ORDER_A_FIRST :
       (CASCADE_ORDER_A_REG == "LAST") ? CASCADE_ORDER_A_LAST :
       (CASCADE_ORDER_A_REG == "MIDDLE") ? CASCADE_ORDER_A_MIDDLE :
        CASCADE_ORDER_A_NONE;

    CASCADE_ORDER_B_BIN =
      (CASCADE_ORDER_B_REG == "NONE") ? CASCADE_ORDER_B_NONE :
      (CASCADE_ORDER_B_REG == "FIRST") ? CASCADE_ORDER_B_FIRST :
      (CASCADE_ORDER_B_REG == "LAST") ? CASCADE_ORDER_B_LAST :
      (CASCADE_ORDER_B_REG == "MIDDLE") ? CASCADE_ORDER_B_MIDDLE :
       CASCADE_ORDER_B_NONE;

    EN_AUTO_SLEEP_MODE_BIN =
      (EN_AUTO_SLEEP_MODE_REG == "FALSE") ? EN_AUTO_SLEEP_MODE_FALSE :
      (EN_AUTO_SLEEP_MODE_REG == "TRUE") ? EN_AUTO_SLEEP_MODE_TRUE :
       EN_AUTO_SLEEP_MODE_FALSE;
  
    EN_ECC_RD_A_BIN =
      (EN_ECC_RD_A_REG == "FALSE") ? EN_ECC_RD_A_FALSE :
      (EN_ECC_RD_A_REG == "TRUE") ? EN_ECC_RD_A_TRUE :
       EN_ECC_RD_A_FALSE;

    EN_ECC_RD_B_BIN =
      (EN_ECC_RD_B_REG == "FALSE") ? EN_ECC_RD_B_FALSE :
      (EN_ECC_RD_B_REG == "TRUE") ? EN_ECC_RD_B_TRUE :
       EN_ECC_RD_B_FALSE;

    EN_ECC_WR_A_BIN =
      (EN_ECC_WR_A_REG == "FALSE") ? EN_ECC_WR_A_FALSE :
      (EN_ECC_WR_A_REG == "TRUE") ? EN_ECC_WR_A_TRUE :
       EN_ECC_WR_A_FALSE;

    EN_ECC_WR_B_BIN =
      (EN_ECC_WR_B_REG == "FALSE") ? EN_ECC_WR_B_FALSE :
      (EN_ECC_WR_B_REG == "TRUE") ? EN_ECC_WR_B_TRUE :
       EN_ECC_WR_B_FALSE;

    IREG_PRE_A_BIN =
      (IREG_PRE_A_REG == "FALSE") ? IREG_PRE_A_FALSE :
      (IREG_PRE_A_REG == "TRUE") ? IREG_PRE_A_TRUE :
       IREG_PRE_A_FALSE;

    IREG_PRE_B_BIN =
      (IREG_PRE_B_REG == "FALSE") ? IREG_PRE_B_FALSE :
      (IREG_PRE_B_REG == "TRUE") ? IREG_PRE_B_TRUE :
       IREG_PRE_B_FALSE;

  NUM_UNIQUE_SELF_ADDR_A_BIN = NUM_UNIQUE_SELF_ADDR_A_REG[11:0];
  
  NUM_UNIQUE_SELF_ADDR_B_BIN = NUM_UNIQUE_SELF_ADDR_B_REG[11:0];
  
  NUM_URAM_IN_MATRIX_BIN = NUM_URAM_IN_MATRIX_REG[11:0];

    OREG_A_BIN =
      (OREG_A_REG == "FALSE") ? OREG_A_FALSE :
      (OREG_A_REG == "TRUE") ? OREG_A_TRUE :
       OREG_A_FALSE;

    OREG_B_BIN =
      (OREG_B_REG == "FALSE") ? OREG_B_FALSE :
      (OREG_B_REG == "TRUE") ? OREG_B_TRUE :
       OREG_B_FALSE;

    OREG_ECC_A_BIN =
      (OREG_ECC_A_REG == "FALSE") ? OREG_ECC_A_FALSE :
      (OREG_ECC_A_REG == "TRUE") ? OREG_ECC_A_TRUE :
       OREG_ECC_A_FALSE;

    OREG_ECC_B_BIN =
      (OREG_ECC_B_REG == "FALSE") ? OREG_ECC_B_FALSE :
      (OREG_ECC_B_REG == "TRUE") ? OREG_ECC_B_TRUE :
       OREG_ECC_B_FALSE;

    REG_CAS_A_BIN =
      (REG_CAS_A_REG == "FALSE") ? REG_CAS_A_FALSE :
      (REG_CAS_A_REG == "TRUE") ? REG_CAS_A_TRUE :
       REG_CAS_A_FALSE;

    REG_CAS_B_BIN =
      (REG_CAS_B_REG == "FALSE") ? REG_CAS_B_FALSE :
      (REG_CAS_B_REG == "TRUE") ? REG_CAS_B_TRUE :
       REG_CAS_B_FALSE;

    RST_MODE_A_BIN =
      (RST_MODE_A_REG == "SYNC") ? RST_MODE_A_SYNC :
      (RST_MODE_A_REG == "ASYNC") ? RST_MODE_A_ASYNC :
       RST_MODE_A_SYNC;

    RST_MODE_B_BIN =
      (RST_MODE_B_REG == "SYNC") ? RST_MODE_B_SYNC :
      (RST_MODE_B_REG == "ASYNC") ? RST_MODE_B_ASYNC :
       RST_MODE_B_SYNC;

    USE_EXT_CE_A_BIN =
      (USE_EXT_CE_A_REG == "FALSE") ? USE_EXT_CE_A_FALSE :
      (USE_EXT_CE_A_REG == "TRUE") ? USE_EXT_CE_A_TRUE :
       USE_EXT_CE_A_FALSE;

    USE_EXT_CE_B_BIN =
      (USE_EXT_CE_B_REG == "FALSE") ? USE_EXT_CE_B_FALSE :
      (USE_EXT_CE_B_REG == "TRUE") ? USE_EXT_CE_B_TRUE :
       USE_EXT_CE_B_FALSE;

  end
`endif

`ifndef XIL_XECLIB
  always @ (trig_attr) begin
  #1;
    if ((attr_test == 1'b1) ||
        ((AUTO_SLEEP_LATENCY_REG != 8) &&
         (AUTO_SLEEP_LATENCY_REG != 3) &&
         (AUTO_SLEEP_LATENCY_REG != 4) &&
         (AUTO_SLEEP_LATENCY_REG != 5) &&
         (AUTO_SLEEP_LATENCY_REG != 6) &&
         (AUTO_SLEEP_LATENCY_REG != 7) &&
         (AUTO_SLEEP_LATENCY_REG != 9) &&
         (AUTO_SLEEP_LATENCY_REG != 10) &&
         (AUTO_SLEEP_LATENCY_REG != 11) &&
         (AUTO_SLEEP_LATENCY_REG != 12) &&
         (AUTO_SLEEP_LATENCY_REG != 13) &&
         (AUTO_SLEEP_LATENCY_REG != 14) &&
         (AUTO_SLEEP_LATENCY_REG != 15))) begin
      $display("Error: [Unisim %s-101] AUTO_SLEEP_LATENCY attribute is set to %d.  Legal values for this attribute are 8, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14 or 15. Instance: %m", MODULE_NAME, AUTO_SLEEP_LATENCY_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((AVG_CONS_INACTIVE_CYCLES_REG < 10) || (AVG_CONS_INACTIVE_CYCLES_REG > 100000))) begin
      $display("Error: [Unisim %s-102] AVG_CONS_INACTIVE_CYCLES attribute is set to %d.  Legal values for this attribute are 10 to 100000. Instance: %m", MODULE_NAME, AVG_CONS_INACTIVE_CYCLES_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((BWE_MODE_A_REG != "PARITY_INTERLEAVED") &&
         (BWE_MODE_A_REG != "PARITY_INDEPENDENT"))) begin
      $display("Error: [Unisim %s-103] BWE_MODE_A attribute is set to %s.  Legal values for this attribute are PARITY_INTERLEAVED or PARITY_INDEPENDENT. Instance: %m", MODULE_NAME, BWE_MODE_A_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((BWE_MODE_B_REG != "PARITY_INTERLEAVED") &&
         (BWE_MODE_B_REG != "PARITY_INDEPENDENT"))) begin
      $display("Error: [Unisim %s-104] BWE_MODE_B attribute is set to %s.  Legal values for this attribute are PARITY_INTERLEAVED or PARITY_INDEPENDENT. Instance: %m", MODULE_NAME, BWE_MODE_B_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((CASCADE_ORDER_A_REG != "NONE") &&
         (CASCADE_ORDER_A_REG != "FIRST") &&
         (CASCADE_ORDER_A_REG != "LAST") &&
         (CASCADE_ORDER_A_REG != "MIDDLE"))) begin
      $display("Error: [Unisim %s-105] CASCADE_ORDER_A attribute is set to %s.  Legal values for this attribute are NONE, FIRST, LAST or MIDDLE. Instance: %m", MODULE_NAME, CASCADE_ORDER_A_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((CASCADE_ORDER_B_REG != "NONE") &&
         (CASCADE_ORDER_B_REG != "FIRST") &&
         (CASCADE_ORDER_B_REG != "LAST") &&
         (CASCADE_ORDER_B_REG != "MIDDLE"))) begin
      $display("Error: [Unisim %s-106] CASCADE_ORDER_B attribute is set to %s.  Legal values for this attribute are NONE, FIRST, LAST or MIDDLE. Instance: %m", MODULE_NAME, CASCADE_ORDER_B_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((EN_AUTO_SLEEP_MODE_REG != "FALSE") &&
         (EN_AUTO_SLEEP_MODE_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-107] EN_AUTO_SLEEP_MODE attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, EN_AUTO_SLEEP_MODE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((EN_ECC_RD_A_REG != "FALSE") &&
         (EN_ECC_RD_A_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-108] EN_ECC_RD_A attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, EN_ECC_RD_A_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((EN_ECC_RD_B_REG != "FALSE") &&
         (EN_ECC_RD_B_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-109] EN_ECC_RD_B attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, EN_ECC_RD_B_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((EN_ECC_WR_A_REG != "FALSE") &&
         (EN_ECC_WR_A_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-110] EN_ECC_WR_A attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, EN_ECC_WR_A_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((EN_ECC_WR_B_REG != "FALSE") &&
         (EN_ECC_WR_B_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-111] EN_ECC_WR_B attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, EN_ECC_WR_B_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((IREG_PRE_A_REG != "FALSE") &&
         (IREG_PRE_A_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-112] IREG_PRE_A attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, IREG_PRE_A_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((IREG_PRE_B_REG != "FALSE") &&
         (IREG_PRE_B_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-113] IREG_PRE_B attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, IREG_PRE_B_REG);
      attr_err = 1'b1;
    end

  if ((attr_test == 1'b1) ||
      ((NUM_UNIQUE_SELF_ADDR_A_REG < 1) || (NUM_UNIQUE_SELF_ADDR_A_REG > 2048))) begin
    $display("Error: [Unisim %s-122] NUM_UNIQUE_SELF_ADDR_A attribute is set to %d.  Legal values for this attribute are 1 to 2048. Instance: %m", MODULE_NAME, NUM_UNIQUE_SELF_ADDR_A_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((NUM_UNIQUE_SELF_ADDR_B_REG < 1) || (NUM_UNIQUE_SELF_ADDR_B_REG > 2048))) begin
    $display("Error: [Unisim %s-123] NUM_UNIQUE_SELF_ADDR_B attribute is set to %d.  Legal values for this attribute are 1 to 2048. Instance: %m", MODULE_NAME, NUM_UNIQUE_SELF_ADDR_B_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((NUM_URAM_IN_MATRIX_REG < 1) || (NUM_URAM_IN_MATRIX_REG > 2048))) begin
    $display("Error: [Unisim %s-124] NUM_URAM_IN_MATRIX attribute is set to %d.  Legal values for this attribute are 1 to 2048. Instance: %m", MODULE_NAME, NUM_URAM_IN_MATRIX_REG);
    attr_err = 1'b1;
  end

    if ((attr_test == 1'b1) ||
        ((OREG_A_REG != "FALSE") &&
         (OREG_A_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-125] OREG_A attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, OREG_A_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((OREG_B_REG != "FALSE") &&
         (OREG_B_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-126] OREG_B attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, OREG_B_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((OREG_ECC_A_REG != "FALSE") &&
         (OREG_ECC_A_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-127] OREG_ECC_A attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, OREG_ECC_A_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((OREG_ECC_B_REG != "FALSE") &&
         (OREG_ECC_B_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-128] OREG_ECC_B attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, OREG_ECC_B_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((REG_CAS_A_REG != "FALSE") &&
         (REG_CAS_A_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-129] REG_CAS_A attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, REG_CAS_A_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((REG_CAS_B_REG != "FALSE") &&
         (REG_CAS_B_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-130] REG_CAS_B attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, REG_CAS_B_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((RST_MODE_A_REG != "SYNC") &&
         (RST_MODE_A_REG != "ASYNC"))) begin
      $display("Error: [Unisim %s-131] RST_MODE_A attribute is set to %s.  Legal values for this attribute are SYNC or ASYNC. Instance: %m", MODULE_NAME, RST_MODE_A_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((RST_MODE_B_REG != "SYNC") &&
         (RST_MODE_B_REG != "ASYNC"))) begin
      $display("Error: [Unisim %s-132] RST_MODE_B attribute is set to %s.  Legal values for this attribute are SYNC or ASYNC. Instance: %m", MODULE_NAME, RST_MODE_B_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((USE_EXT_CE_A_REG != "FALSE") &&
         (USE_EXT_CE_A_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-137] USE_EXT_CE_A attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, USE_EXT_CE_A_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((USE_EXT_CE_B_REG != "FALSE") &&
         (USE_EXT_CE_B_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-138] USE_EXT_CE_B attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, USE_EXT_CE_B_REG);
      attr_err = 1'b1;
    end

    if (attr_err == 1'b1) #1 $finish;
  end
`endif

`ifdef XIL_TIMING
  reg notifier;
`endif

// begin behavioral model
// define tasks, functions
  
reg cas_a_warning = 1'b0;
reg cas_b_warning = 1'b0;
task is_cas_a_zero;
integer i;
begin
  cas_a_warning = 1'b0;
  for (i=0;i<=22;i=i+1) begin
    if (CAS_IN_ADDR_A[i] !== 1'b0) begin
      cas_a_warning = 1'b1;
      $display("Warning: [Unisim %s-15] CAS_IN_ADDR_A[%2d] signal is not tied low in CASCADE mode (%s) Instance: %m", MODULE_NAME, i, CASCADE_ORDER_A_REG);
    end
  end
  for (i=0;i<=8;i=i+1) begin
    if (CAS_IN_BWE_A[i] !== 1'b0) begin
      cas_a_warning = 1'b1;
      $display("Warning: [Unisim %s-15] CAS_IN_BWE_A[%2d] signal is not tied low in CASCADE mode (%s) Instance: %m", MODULE_NAME, i, CASCADE_ORDER_A_REG);
    end
  end
  if (CAS_IN_DBITERR_A !== 1'b0) begin
    cas_a_warning = 1'b1;
    $display("Warning: [Unisim %s-15] CAS_IN_DBITERR_A signal is not tied low in CASCADE mode (%s) Instance: %m", MODULE_NAME, CASCADE_ORDER_A_REG);
  end
  for (i=0;i<=71;i=i+1) begin
    if (CAS_IN_DIN_A[i] !== 1'b0) begin
      cas_a_warning = 1'b1;
      $display("Warning: [Unisim %s-15] CAS_IN_DIN_A[%2d] signal is not tied low in CASCADE mode (%s) Instance: %m", MODULE_NAME, i, CASCADE_ORDER_A_REG);
    end
  end
  for (i=0;i<=71;i=i+1) begin
    if (CAS_IN_DOUT_A[i] !== 1'b0) begin
      cas_a_warning = 1'b1;
      $display("Warning: [Unisim %s-15] CAS_IN_DOUT_A[%2d] signal is not tied low in CASCADE mode (%s) Instance: %m", MODULE_NAME, i, CASCADE_ORDER_A_REG);
    end
  end
  if (CAS_IN_EN_A !== 1'b0) begin
    cas_a_warning = 1'b1;
    $display("Warning: [Unisim %s-15] CAS_IN_EN_A signal is not tied low in CASCADE mode (%s) Instance: %m", MODULE_NAME, CASCADE_ORDER_A_REG);
  end
  if (CAS_IN_RDACCESS_A !== 1'b0) begin
    cas_a_warning = 1'b1;
    $display("Warning: [Unisim %s-15] CAS_IN_RDACCESS_A signal is not tied low in CASCADE mode (%s) Instance: %m", MODULE_NAME, CASCADE_ORDER_A_REG);
  end
  if (CAS_IN_RDB_WR_A !== 1'b0) begin
    cas_a_warning = 1'b1;
    $display("Warning: [Unisim %s-15] CAS_IN_RDB_WR_A signal is not tied low in CASCADE mode (%s) Instance: %m", MODULE_NAME, CASCADE_ORDER_A_REG);
  end
  if (CAS_IN_SBITERR_A !== 1'b0) begin
    cas_a_warning = 1'b1;
    $display("Warning: [Unisim %s-15] CAS_IN_SBITERR_A signal is not tied low in CASCADE mode (%s) Instance: %m", MODULE_NAME, CASCADE_ORDER_A_REG);
  end
end
endtask // is_cas_a_zero

task is_cas_a_floating;
integer i;
begin
  cas_a_warning = 1'b0;
  for (i=0;i<=22;i=i+1) begin
    if (CAS_IN_ADDR_A[i] === 1'bz) begin
      cas_a_warning = 1'b1;
      $display("Warning: [Unisim %s-16] CAS_IN_ADDR_A[%2d] signal is unconnected in CASCADE mode (%s) Instance: %m", MODULE_NAME, i, CASCADE_ORDER_A_REG);
    end
  end
  for (i=0;i<=8;i=i+1) begin
    if (CAS_IN_BWE_A[i] === 1'bz) begin
      cas_a_warning = 1'b1;
      $display("Warning: [Unisim %s-16] CAS_IN_BWE_A[%2d] signal is unconnected in CASCADE mode (%s) Instance: %m", MODULE_NAME, i, CASCADE_ORDER_A_REG);
    end
  end
  if (CAS_IN_DBITERR_A === 1'bz) begin
    cas_a_warning = 1'b1;
    $display("Warning: [Unisim %s-16] CAS_IN_DBITERR_A signal is unconnected in CASCADE mode (%s) Instance: %m", MODULE_NAME, CASCADE_ORDER_A_REG);
  end
  for (i=0;i<=71;i=i+1) begin
    if (CAS_IN_DIN_A[i] === 1'bz) begin
      cas_a_warning = 1'b1;
      $display("Warning: [Unisim %s-16] CAS_IN_DIN_A[%2d] signal is unconnected in CASCADE mode (%s) Instance: %m", MODULE_NAME, i, CASCADE_ORDER_A_REG);
    end
  end
  for (i=0;i<=71;i=i+1) begin
    if (CAS_IN_DOUT_A[i] === 1'bz) begin
      cas_a_warning = 1'b1;
      $display("Warning: [Unisim %s-16] CAS_IN_DOUT_A[%2d] signal is unconnected in CASCADE mode (%s) Instance: %m", MODULE_NAME, i, CASCADE_ORDER_A_REG);
    end
  end
  if (CAS_IN_EN_A === 1'bz) begin
    cas_a_warning = 1'b1;
    $display("Warning: [Unisim %s-16] CAS_IN_EN_A signal is unconnected in CASCADE mode (%s) Instance: %m", MODULE_NAME, CASCADE_ORDER_A_REG);
  end
  if (CAS_IN_RDACCESS_A === 1'bz) begin
    cas_a_warning = 1'b1;
    $display("Warning: [Unisim %s-16] CAS_IN_RDACCESS_A signal is unconnected in CASCADE mode (%s) Instance: %m", MODULE_NAME, CASCADE_ORDER_A_REG);
  end
  if (CAS_IN_RDB_WR_A === 1'bz) begin
    cas_a_warning = 1'b1;
    $display("Warning: [Unisim %s-16] CAS_IN_RDB_WR_A signal is unconnected in CASCADE mode (%s) Instance: %m", MODULE_NAME, CASCADE_ORDER_A_REG);
  end
  if (CAS_IN_SBITERR_A === 1'bz) begin
    cas_a_warning = 1'b1;
    $display("Warning: [Unisim %s-16] CAS_IN_SBITERR_A signal is unconnected in CASCADE mode (%s) Instance: %m", MODULE_NAME, CASCADE_ORDER_A_REG);
  end
end
endtask // is_cas_a_floating

task is_cas_b_zero;
integer i;
begin
  cas_b_warning = 1'b0;
  for (i=0;i<=22;i=i+1) begin
    if (CAS_IN_ADDR_B[i] !== 1'b0) begin
      cas_b_warning = 1'b1;
      $display("Warning: [Unisim %s-17] CAS_IN_ADDR_B[%2d] signal is not tied low in CASCADE mode (%s) Instance: %m", MODULE_NAME, i, CASCADE_ORDER_B_REG);
    end
  end
  for (i=0;i<=8;i=i+1) begin
    if (CAS_IN_BWE_B[i] !== 1'b0) begin
      cas_b_warning = 1'b1;
      $display("Warning: [Unisim %s-17] CAS_IN_BWE_B[%2d] signal is not tied low in CASCADE mode (%s) Instance: %m", MODULE_NAME, i, CASCADE_ORDER_B_REG);
    end
  end
  if (CAS_IN_DBITERR_B !== 1'b0) begin
    cas_b_warning = 1'b1;
    $display("Warning: [Unisim %s-17] CAS_IN_DBITERR_B signal is not tied low in CASCADE mode (%s) Instance: %m", MODULE_NAME, CASCADE_ORDER_B_REG);
  end
  for (i=0;i<=71;i=i+1) begin
    if (CAS_IN_DIN_B[i] !== 1'b0) begin
      cas_b_warning = 1'b1;
      $display("Warning: [Unisim %s-17] CAS_IN_DIN_B[%2d] signal is not tied low in CASCADE mode (%s) Instance: %m", MODULE_NAME, i, CASCADE_ORDER_B_REG);
    end
  end
  for (i=0;i<=71;i=i+1) begin
    if (CAS_IN_DOUT_B[i] !== 1'b0) begin
      cas_a_warning = 1'b1;
      $display("Warning: [Unisim %s-17] CAS_IN_DOUT_B[%2d] signal is not tied low in CASCADE mode (%s) Instance: %m", MODULE_NAME, i, CASCADE_ORDER_B_REG);
    end
  end
  if (CAS_IN_EN_B !== 1'b0) begin
    cas_b_warning = 1'b1;
    $display("Warning: [Unisim %s-17] CAS_IN_EN_B signal is not tied low in CASCADE mode (%s) Instance: %m", MODULE_NAME, CASCADE_ORDER_B_REG);
  end
  if (CAS_IN_RDACCESS_B !== 1'b0) begin
    cas_b_warning = 1'b1;
    $display("Warning: [Unisim %s-17] CAS_IN_RDACCESS_B signal is not tied low in CASCADE mode (%s) Instance: %m", MODULE_NAME, CASCADE_ORDER_B_REG);
  end
  if (CAS_IN_RDB_WR_B !== 1'b0) begin
    cas_b_warning = 1'b1;
    $display("Warning: [Unisim %s-17] CAS_IN_RDB_WR_B signal is not tied low in CASCADE mode (%s) Instance: %m", MODULE_NAME, CASCADE_ORDER_B_REG);
  end
  if (CAS_IN_SBITERR_B !== 1'b0) begin
    cas_b_warning = 1'b1;
    $display("Warning: [Unisim %s-17] CAS_IN_SBITERR_B signal is not tied low in CASCADE mode (%s) Instance: %m", MODULE_NAME, CASCADE_ORDER_B_REG);
  end
end
endtask // is_cas_b_zero

task is_cas_b_floating;
integer i;
begin
  cas_b_warning = 1'b0;
  for (i=0;i<=22;i=i+1) begin
    if (CAS_IN_ADDR_B[i] === 1'bz) begin
      cas_b_warning = 1'b1;
      $display("Warning: [Unisim %s-18] CAS_IN_ADDR_B[%2d] signal is unconnected in CASCADE mode Instance: %m", MODULE_NAME, i);
    end
  end
  for (i=0;i<=8;i=i+1) begin
    if (CAS_IN_BWE_B[i] === 1'bz) begin
      cas_b_warning = 1'b1;
      $display("Warning: [Unisim %s-18] CAS_IN_BWE_B[%2d] signal is unconnected in CASCADE mode Instance: %m", MODULE_NAME, i);
    end
  end
  if (CAS_IN_DBITERR_B === 1'bz) begin
    cas_b_warning = 1'b1;
    $display("Warning: [Unisim %s-18] CAS_IN_DBITERR_B signal is unconnected in CASCADE mode Instance: %m", MODULE_NAME);
  end
  for (i=0;i<=71;i=i+1) begin
    if (CAS_IN_DIN_B[i] === 1'bz) begin
      cas_b_warning = 1'b1;
      $display("Warning: [Unisim %s-18] CAS_IN_DIN_B[%2d] signal is unconnected in CASCADE mode Instance: %m", MODULE_NAME, i);
    end
  end
  for (i=0;i<=71;i=i+1) begin
    if (CAS_IN_DOUT_B[i] === 1'bz) begin
      cas_b_warning = 1'b1;
      $display("Warning: [Unisim %s-18] CAS_IN_DOUT_B[%2d] signal is unconnected in CASCADE mode Instance: %m", MODULE_NAME, i);
    end
  end
  if (CAS_IN_EN_B === 1'bz) begin
    cas_b_warning = 1'b1;
    $display("Warning: [Unisim %s-18] CAS_IN_EN_B signal is unconnected in CASCADE mode Instance: %m", MODULE_NAME);
  end
  if (CAS_IN_RDACCESS_B === 1'bz) begin
    cas_b_warning = 1'b1;
    $display("Warning: [Unisim %s-18] CAS_IN_RDACCESS_B signal is unconnected in CASCADE mode Instance: %m", MODULE_NAME);
  end
  if (CAS_IN_RDB_WR_B === 1'bz) begin
    cas_b_warning = 1'b1;
    $display("Warning: [Unisim %s-18] CAS_IN_RDB_WR_B signal is unconnected in CASCADE mode Instance: %m", MODULE_NAME);
  end
  if (CAS_IN_SBITERR_B === 1'bz) begin
    cas_b_warning = 1'b1;
    $display("Warning: [Unisim %s-18] CAS_IN_SBITERR_B signal is unconnected in CASCADE mode Instance: %m", MODULE_NAME);
  end
end
endtask // is_cas_b_floating

function [7:0] fn_ecc (
   input encode,
   input [63:0] d_i,
   input [7:0] dp_i
   );
   reg ecc_7;
begin
   fn_ecc[0] = d_i[0]   ^  d_i[1]   ^  d_i[3]   ^  d_i[4]   ^  d_i[6]   ^
               d_i[8]   ^  d_i[10]  ^  d_i[11]  ^  d_i[13]  ^  d_i[15]  ^
               d_i[17]  ^  d_i[19]  ^  d_i[21]  ^  d_i[23]  ^  d_i[25]  ^
               d_i[26]  ^  d_i[28]  ^  d_i[30]  ^  d_i[32]  ^  d_i[34]  ^
               d_i[36]  ^  d_i[38]  ^  d_i[40]  ^  d_i[42]  ^  d_i[44]  ^
               d_i[46]  ^  d_i[48]  ^  d_i[50]  ^  d_i[52]  ^  d_i[54]  ^
               d_i[56]  ^  d_i[57]  ^  d_i[59]  ^  d_i[61]  ^  d_i[63];

   fn_ecc[1] = d_i[0]   ^  d_i[2]   ^  d_i[3]   ^  d_i[5]   ^  d_i[6]   ^
               d_i[9]   ^  d_i[10]  ^  d_i[12]  ^  d_i[13]  ^  d_i[16]  ^
               d_i[17]  ^  d_i[20]  ^  d_i[21]  ^  d_i[24]  ^  d_i[25]  ^
               d_i[27]  ^  d_i[28]  ^  d_i[31]  ^  d_i[32]  ^  d_i[35]  ^
               d_i[36]  ^  d_i[39]  ^  d_i[40]  ^  d_i[43]  ^  d_i[44]  ^
               d_i[47]  ^  d_i[48]  ^  d_i[51]  ^  d_i[52]  ^  d_i[55]  ^
               d_i[56]  ^  d_i[58]  ^  d_i[59]  ^  d_i[62]  ^  d_i[63];

   fn_ecc[2] = d_i[1]   ^  d_i[2]   ^  d_i[3]   ^  d_i[7]   ^  d_i[8]   ^
               d_i[9]   ^  d_i[10]  ^  d_i[14]  ^  d_i[15]  ^  d_i[16]  ^
               d_i[17]  ^  d_i[22]  ^  d_i[23]  ^  d_i[24]  ^  d_i[25]  ^
               d_i[29]  ^  d_i[30]  ^  d_i[31]  ^  d_i[32]  ^  d_i[37]  ^
               d_i[38]  ^  d_i[39]  ^  d_i[40]  ^  d_i[45]  ^  d_i[46]  ^
               d_i[47]  ^  d_i[48]  ^  d_i[53]  ^  d_i[54]  ^  d_i[55]  ^
               d_i[56]  ^  d_i[60]  ^  d_i[61]  ^  d_i[62]  ^  d_i[63];

   fn_ecc[3] = d_i[4]   ^  d_i[5]   ^  d_i[6]   ^  d_i[7]   ^  d_i[8]   ^
               d_i[9]   ^  d_i[10]  ^  d_i[18]  ^  d_i[19]  ^  d_i[20]  ^
               d_i[21]  ^  d_i[22]  ^  d_i[23]  ^  d_i[24]  ^  d_i[25]  ^
               d_i[33]  ^  d_i[34]  ^  d_i[35]  ^  d_i[36]  ^  d_i[37]  ^
               d_i[38]  ^  d_i[39]  ^  d_i[40]  ^  d_i[49]  ^  d_i[50]  ^
               d_i[51]  ^  d_i[52]  ^  d_i[53]  ^  d_i[54]  ^  d_i[55]  ^
               d_i[56];

   fn_ecc[4] = d_i[11]  ^  d_i[12]  ^  d_i[13]  ^  d_i[14]  ^  d_i[15]  ^
               d_i[16]  ^  d_i[17]  ^  d_i[18]  ^  d_i[19]  ^  d_i[20]  ^
               d_i[21]  ^  d_i[22]  ^  d_i[23]  ^  d_i[24]  ^  d_i[25]  ^
               d_i[41]  ^  d_i[42]  ^  d_i[43]  ^  d_i[44]  ^  d_i[45]  ^
               d_i[46]  ^  d_i[47]  ^  d_i[48]  ^  d_i[49]  ^  d_i[50]  ^
               d_i[51]  ^  d_i[52]  ^  d_i[53]  ^  d_i[54]  ^  d_i[55]  ^
               d_i[56];

   fn_ecc[5] = d_i[26]  ^  d_i[27]  ^  d_i[28]  ^  d_i[29]  ^  d_i[30]  ^
               d_i[31]  ^  d_i[32]  ^  d_i[33]  ^  d_i[34]  ^  d_i[35]  ^
               d_i[36]  ^  d_i[37]  ^  d_i[38]  ^  d_i[39]  ^  d_i[40]  ^
               d_i[41]  ^  d_i[42]  ^  d_i[43]  ^  d_i[44]  ^  d_i[45]  ^
               d_i[46]  ^  d_i[47]  ^  d_i[48]  ^  d_i[49]  ^  d_i[50]  ^
               d_i[51]  ^  d_i[52]  ^  d_i[53]  ^  d_i[54]  ^  d_i[55]  ^
               d_i[56];

   fn_ecc[6] = d_i[57]  ^  d_i[58]  ^  d_i[59]  ^  d_i[60]  ^  d_i[61]  ^
               d_i[62]  ^  d_i[63];

   ecc_7 = d_i[0]   ^  d_i[1]   ^  d_i[2]   ^  d_i[3]   ^ d_i[4]   ^
           d_i[5]   ^  d_i[6]   ^  d_i[7]   ^  d_i[8]   ^ d_i[9]   ^
           d_i[10]  ^  d_i[11]  ^  d_i[12]  ^  d_i[13]  ^ d_i[14]  ^
           d_i[15]  ^  d_i[16]  ^  d_i[17]  ^  d_i[18]  ^ d_i[19]  ^
           d_i[20]  ^  d_i[21]  ^  d_i[22]  ^  d_i[23]  ^ d_i[24]  ^
           d_i[25]  ^  d_i[26]  ^  d_i[27]  ^  d_i[28]  ^ d_i[29]  ^
           d_i[30]  ^  d_i[31]  ^  d_i[32]  ^  d_i[33]  ^ d_i[34]  ^
           d_i[35]  ^  d_i[36]  ^  d_i[37]  ^  d_i[38]  ^ d_i[39]  ^
           d_i[40]  ^  d_i[41]  ^  d_i[42]  ^  d_i[43]  ^ d_i[44]  ^
           d_i[45]  ^  d_i[46]  ^  d_i[47]  ^  d_i[48]  ^ d_i[49]  ^
           d_i[50]  ^  d_i[51]  ^  d_i[52]  ^  d_i[53]  ^ d_i[54]  ^
           d_i[55]  ^  d_i[56]  ^  d_i[57]  ^  d_i[58]  ^ d_i[59]  ^
           d_i[60]  ^  d_i[61]  ^  d_i[62]  ^  d_i[63];

   if (encode) begin
      fn_ecc[7] = ecc_7 ^
                  fn_ecc[0] ^ fn_ecc[1] ^ fn_ecc[2] ^ fn_ecc[3] ^
                  fn_ecc[4] ^ fn_ecc[5] ^ fn_ecc[6];
      end
   else begin
      fn_ecc[7] = ecc_7 ^
                  dp_i[0] ^ dp_i[1] ^ dp_i[2] ^ dp_i[3] ^
                  dp_i[4] ^ dp_i[5] ^ dp_i[6];
      end
end
endfunction // fn_ecc

function [71:0] fn_cor_bit (
   input [6:0] error_bit,
   input [63:0] d_i,
   input [7:0] dp_i
   );
   reg [71:0] cor_int;
begin
   cor_int = {d_i[63:57], dp_i[6], d_i[56:26], dp_i[5], d_i[25:11], dp_i[4],
              d_i[10:4], dp_i[3], d_i[3:1], dp_i[2], d_i[0], dp_i[1:0],
              dp_i[7]};
   cor_int[error_bit] = ~cor_int[error_bit];
   fn_cor_bit = {cor_int[0], cor_int[64], cor_int[32], cor_int[16],
                 cor_int[8], cor_int[4], cor_int[2:1], cor_int[71:65],
                 cor_int[63:33], cor_int[31:17], cor_int[15:9],
                 cor_int[7:5], cor_int[3]};
end
endfunction // fn_cor_bit

`ifndef XIL_XECLIB
  always @ (trig_attr) begin
  #1;
    if ((attr_test == 1'b1) ||
        ((CASCADE_ORDER_A_REG != "NONE") &&
         (USE_EXT_CE_A_REG == "TRUE"))) begin
      $display("Error: [Unisim %s-1] CASCADE_ORDER_A attribute is set to %s and USE_EXT_CE_A attribute is set to %s. EXT_CE_A can not be used in cascaded URAM applications. Instance: %m", MODULE_NAME, CASCADE_ORDER_A_REG, USE_EXT_CE_A_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((CASCADE_ORDER_B_REG != "NONE") &&
         (USE_EXT_CE_B_REG == "TRUE"))) begin
      $display("Error: [Unisim %s-2] CASCADE_ORDER_B attribute is set to %s and USE_EXT_CE_B attribute is set to %s. EXT_CE_B can not be used in cascaded URAM applications. Instance: %m", MODULE_NAME, CASCADE_ORDER_B_REG, USE_EXT_CE_B_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (CASCADE_ORDER_A_REG == "NONE") ||
        (CASCADE_ORDER_A_REG == "FIRST")) begin
       is_cas_a_zero;
       if (cas_a_warning) $display("Warning: [Unisim %s-13] CASCADE_ORDER_A attribute is set to %s and some or all of the CASCADE signals are not tied low. Simulation behavior may not match hardware under these circumstances. Please check that all CASCADE signals are properly tied off. Instance: %m", MODULE_NAME, CASCADE_ORDER_A_REG);
    end

    if ((attr_test == 1'b1) ||
        (CASCADE_ORDER_A_REG == "LAST") ||
        (CASCADE_ORDER_A_REG == "MIDDLE")) begin
       is_cas_a_floating;
       if (cas_a_warning) $display("Warning: [Unisim %s-13] CASCADE_ORDER_A attribute is set to %s and some or all of the CASCADE signals are unconnected. Simulation behavior may not match hardware under these circumstances. Please check that all CASCADE signals are properly connected. Instance: %m", MODULE_NAME, CASCADE_ORDER_A_REG);
    end

    if ((attr_test == 1'b1) ||
        (CASCADE_ORDER_B_REG == "NONE") ||
        (CASCADE_ORDER_B_REG == "FIRST")) begin
       is_cas_b_zero;
       if (cas_b_warning) $display("Warning: [Unisim %s-14] CASCADE_ORDER_B attribute is set to %s and some or all of the CASCADE signals are not tied low. Simulation behavior may not match hardware under these circumstances. Please check that all CASCADE signals are properly tied off. Instance: %m", MODULE_NAME, CASCADE_ORDER_B_REG);
    end

    if ((attr_test == 1'b1) ||
        (CASCADE_ORDER_B_REG == "LAST") ||
        (CASCADE_ORDER_B_REG == "MIDDLE")) begin
       is_cas_b_floating;
       if (cas_b_warning) $display("Warning: [Unisim %s-14] CASCADE_ORDER_B attribute is set to %s and some or all of the CASCADE signals are unconnected. Simulation behavior may not match hardware under these circumstances. Please check that all CASCADE signals are properly connected. Instance: %m", MODULE_NAME, CASCADE_ORDER_B_REG);
    end

    if ((attr_test == 1'b1) ||
       ((EN_AUTO_SLEEP_MODE_REG == "TRUE") && 
        (USE_EXT_CE_A_REG == "TRUE"))) begin
       $display("Error: [Unisim %s-19] EN_AUTO_SLEEP_MODE attribute is set to %s and USE_EXT_CE_A is set to %s. External OREG CE cannot be used when AUTO_SLEEP_MODE is enabled. Instance: %m", MODULE_NAME, EN_AUTO_SLEEP_MODE_REG, USE_EXT_CE_A_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
       ((EN_AUTO_SLEEP_MODE_REG == "TRUE") && 
        (USE_EXT_CE_B_REG == "TRUE"))) begin
       $display("Error: [Unisim %s-20] EN_AUTO_SLEEP_MODE attribute is set to %s and USE_EXT_CE_B is set to %s. External OREG CE cannot be used when AUTO_SLEEP_MODE is enabled. Instance: %m", MODULE_NAME, EN_AUTO_SLEEP_MODE_REG, USE_EXT_CE_B_REG);
      attr_err = 1'b1;
    end

    if (attr_err == 1'b1) #1 $finish;

  end
`endif

  localparam mem_width = 72;
  localparam mem_depth = 4 * 1024;
  localparam encode = 1'b1;
  localparam decode = 1'b0;
  localparam [22:0] ADDR_INIT = 23'b0;
  localparam [8:0] BWE_INIT = 9'b0;
  localparam [mem_width-1:0] D_INIT = {mem_width{1'b0}};
  localparam [mem_width-1:0] D_UNDEF = {mem_width{1'bx}};

  reg [mem_width-1 : 0 ]  mem      [0 : mem_depth-1];

  integer wa;
  reg [11:0] ram_addr_a;
  reg [11:0] ram_addr_b;
  reg ram_ce_a;
  reg ram_ce_b;
  reg DEEPSLEEP_in = 1'b0;
  reg SHUTDOWN_in = 1'b0;
  reg ram_ce_a_int=0;
  reg ram_ce_b_int=0;
  reg ram_ce_a_pre=0;
  reg ram_ce_b_pre=0;
  reg [15:1] ram_ce_a_fifo;
  reg [15:1] ram_ce_b_fifo;
  reg [71:0] ram_bwe_a;
  reg [71:0] ram_bwe_b;
  reg ram_we_a;
  reg ram_we_b;
  reg ram_we_a_event = 1'b0;
  reg ram_we_b_event = 1'b0;
  reg [71:0] ram_data_a;
  reg [71:0] ram_data_b;

// input register stages
// decisions simulate faster than assignments - wider muxes, less busses
  reg [22:0] ADDR_A_reg;
  reg [22:0] ADDR_B_reg;
  reg [8:0] BWE_A_reg;
  reg [8:0] BWE_B_reg;
  reg [71:0] DIN_A_reg;
  reg [71:0] DIN_B_reg;
  reg EN_A_reg;
  reg EN_B_reg;
  reg INJECT_DBITERR_A_reg;
  reg INJECT_DBITERR_B_reg;
  reg INJECT_SBITERR_A_reg;
  reg INJECT_SBITERR_B_reg;
  reg RDB_WR_A_reg;
  reg RDB_WR_B_reg;
  reg [22:0] ADDR_A_int;
  reg [22:0] ADDR_B_int;
  reg [8:0] BWE_A_int;
  reg [8:0] BWE_B_int;
  reg [71:0] DIN_A_int;
  reg [71:0] DIN_B_int;
  reg EN_A_int;
  reg EN_B_int;
  reg INJECT_DBITERR_A_int;
  reg INJECT_DBITERR_B_int;
  reg INJECT_SBITERR_A_int;
  reg INJECT_SBITERR_B_int;
  reg RDB_WR_A_int;
  reg RDB_WR_B_int;

  reg RST_A_async = 1'b0;
  reg RST_B_async = 1'b0;
  reg RST_A_sync = 1'b0;
  reg RST_B_sync = 1'b0;

  integer wake_count;
  wire auto_sleep;
  reg shut_down;
  reg a_sleep;
  reg auto_sleep_A;
  reg auto_sleep_B;
  wire auto_wake_up_A;
  wire auto_wake_up_B;

  reg CAS_OUT_DBITERR_A_out;
  reg CAS_OUT_DBITERR_B_out;
  reg CAS_OUT_EN_A_out;
  reg CAS_OUT_EN_B_out;
  reg CAS_OUT_RDACCESS_A_out;
  reg CAS_OUT_RDACCESS_B_out;
  reg CAS_OUT_RDB_WR_A_out;
  reg CAS_OUT_RDB_WR_B_out;
  reg CAS_OUT_SBITERR_A_out;
  reg CAS_OUT_SBITERR_B_out;
  reg DBITERR_A_out;
  reg DBITERR_B_out;
  reg RDACCESS_A_out;
  reg RDACCESS_B_out;
  reg SBITERR_A_out;
  reg SBITERR_B_out;
  reg [22:0] CAS_OUT_ADDR_A_out;
  reg [22:0] CAS_OUT_ADDR_B_out;
  reg [71:0] CAS_OUT_DIN_A_out;
  reg [71:0] CAS_OUT_DIN_B_out;
  reg [71:0] CAS_OUT_DOUT_A_out;
  reg [71:0] CAS_OUT_DOUT_B_out;
  reg [71:0] DOUT_A_out;
  reg [71:0] DOUT_B_out;
  reg [8:0] CAS_OUT_BWE_A_out;
  reg [8:0] CAS_OUT_BWE_B_out;

  assign CAS_OUT_ADDR_A = CAS_OUT_ADDR_A_out;
  assign CAS_OUT_ADDR_B = CAS_OUT_ADDR_B_out;
  assign CAS_OUT_BWE_A = CAS_OUT_BWE_A_out;
  assign CAS_OUT_BWE_B = CAS_OUT_BWE_B_out;
  assign CAS_OUT_DBITERR_A = DBITERR_A_out;
  assign CAS_OUT_DBITERR_B = DBITERR_B_out;
  assign CAS_OUT_DIN_A = CAS_OUT_DIN_A_out;
  assign CAS_OUT_DIN_B = CAS_OUT_DIN_B_out;
  assign CAS_OUT_DOUT_A = DOUT_A_out;
  assign CAS_OUT_DOUT_B = DOUT_B_out;
  assign CAS_OUT_EN_A = CAS_OUT_EN_A_out;
  assign CAS_OUT_EN_B = CAS_OUT_EN_B_out;
  assign CAS_OUT_RDACCESS_A = RDACCESS_A_out;
  assign CAS_OUT_RDACCESS_B = RDACCESS_B_out;
  assign CAS_OUT_RDB_WR_A = CAS_OUT_RDB_WR_A_out;
  assign CAS_OUT_RDB_WR_B = CAS_OUT_RDB_WR_B_out;
  assign CAS_OUT_SBITERR_A = SBITERR_A_out;
  assign CAS_OUT_SBITERR_B = SBITERR_B_out;
  assign DBITERR_A = DBITERR_A_out;
  assign DBITERR_B = DBITERR_B_out;
  assign DOUT_A = DOUT_A_out;
  assign DOUT_B = DOUT_B_out;
  assign RDACCESS_A = RDACCESS_A_out;
  assign RDACCESS_B = RDACCESS_B_out;
  assign SBITERR_A = SBITERR_A_out;
  assign SBITERR_B = SBITERR_B_out;

`ifndef XIL_XECLIB
  reg INIT_RAM = 1'b0;
  initial begin
    #100; INIT_RAM = 1'b1;
  end
`endif

`ifndef XIL_XECLIB
  reg rst_a_warn_once = 1'b0;
  reg rst_b_warn_once = 1'b0;

  always @(posedge CLK_in) begin
    if ((attr_test == 1'b1) ||
       ((EN_A_int == 1'b1) && (RDB_WR_A_int == 1'b0) && 
        ((RST_A_sync == 1'b1) || (RST_A_async == 1'b1)) &&
        (CASCADE_ORDER_A_BIN != CASCADE_ORDER_A_NONE) &&
        (REG_CAS_A_BIN == REG_CAS_A_TRUE))) begin
      if (rst_a_warn_once == 1'b0) begin
        $display("Warning: [Unisim %s-11] At time (%.3f) ns: CASCADE_ORDER_A attribute is set to %s and REG_CAS_A attribute is set to %s with RST_A and a READ command both active. In certain circumstances the implementation tools optimize the uram pipeline to achieve optimal timing. This is achieved by manipulating the REG_CAS_A attributes. This will not alter the latency of the pipeline but may result in different reset behavior pre and post implementation under these conditions. To avoid this, deassert EN_A when RST_A is active. Instance: %m", MODULE_NAME, $time/1000.0, CASCADE_ORDER_A_REG, REG_CAS_A_REG);
        rst_a_warn_once = 1'b1;
      end
    end else begin
      rst_a_warn_once = 1'b0;
    end 
  end

  always @(posedge CLK_in) begin
    if ((attr_test == 1'b1) ||
       ((EN_B_int == 1'b1) && (RDB_WR_B_int == 1'b0) && 
        ((RST_B_sync == 1'b1) || (RST_B_async == 1'b1)) &&
        (CASCADE_ORDER_B_BIN != CASCADE_ORDER_B_NONE) &&
        (REG_CAS_B_BIN == REG_CAS_B_TRUE))) begin
      if (rst_b_warn_once == 1'b0) begin
        $display("Warning: [Unisim %s-12] At time (%.3f) ns: CASCADE_ORDER_B attribute is set to %s and REG_CAS_B attribute is set to %s with RST_B and a READ command both active. In certain circumstances the implementation tools optimize the uram pipeline to achieve optimal timing. This is achieved by manipulating the REG_CAS_B attributes. This will not alter the latency of the pipeline but may result in different reset behavior pre and post implementation under these conditions. To avoid this, deassert EN_B when RST_B is active. Instance: %m", MODULE_NAME, $time/1000.0, CASCADE_ORDER_B_REG, REG_CAS_B_REG);
        rst_b_warn_once = 1'b1;
      end
    end else begin
      rst_b_warn_once = 1'b0;
    end
  end

`endif

  always @ (*) begin
    if (RST_MODE_A_BIN == RST_MODE_A_ASYNC) begin
      RST_A_async = RST_A_in;
    end
  end

  always @ (*) begin
    if (RST_MODE_B_BIN == RST_MODE_B_ASYNC) begin
      RST_B_async = RST_B_in;
    end
  end

  always @ (posedge CLK_in) begin
    if ((RST_MODE_A_BIN == RST_MODE_A_SYNC) && (RST_A_sync !== RST_A_in))
      RST_A_sync <= RST_A_in;
    if ((RST_MODE_B_BIN == RST_MODE_B_SYNC) && (RST_B_sync !== RST_B_in))
      RST_B_sync <= RST_B_in;
  end

`ifdef XIL_XECLIB
  always @ (posedge CLK_in) begin
`else
  always @ (posedge CLK_in or glblGSR) begin
`endif
    if (glblGSR || 
        (((CASCADE_ORDER_A_BIN != CASCADE_ORDER_A_NONE) &&
          (REG_CAS_A_BIN == REG_CAS_A_FALSE)) &&
         (((CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_FIRST) ||
           (CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_NONE)) &&
          (IREG_PRE_A_BIN == IREG_PRE_A_FALSE)))) begin
      ADDR_A_reg <= ADDR_INIT;
      EN_A_reg <= 1'b0;
      RDB_WR_A_reg <= 1'b0;
      BWE_A_reg <= BWE_INIT;
      DIN_A_reg <= D_INIT;
      INJECT_DBITERR_A_reg <= 1'b0;
      INJECT_SBITERR_A_reg <= 1'b0;
    end else if (((CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_MIDDLE) ||
                  (CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_LAST)) &&
                 (REG_CAS_A_BIN == REG_CAS_A_TRUE)) begin
      EN_A_reg <= CAS_IN_EN_A_in;
      if (CAS_IN_EN_A_in) begin
        ADDR_A_reg[22:12] <= CAS_IN_ADDR_A_in[22:12];
      end
      if (CAS_IN_EN_A_in || (EN_AUTO_SLEEP_MODE_BIN == EN_AUTO_SLEEP_MODE_TRUE)) begin
        ADDR_A_reg[11:0] <= CAS_IN_ADDR_A_in[11:0];
        BWE_A_reg <= CAS_IN_BWE_A_in;
        DIN_A_reg <= CAS_IN_DIN_A_in;
        RDB_WR_A_reg <= CAS_IN_RDB_WR_A_in;
      end
    end else begin
      EN_A_reg <= EN_A_in;
      if (EN_A_in) begin
        ADDR_A_reg[22:12] <= ADDR_A_in[22:12];
      end
      if (EN_A_in || (EN_AUTO_SLEEP_MODE_BIN == EN_AUTO_SLEEP_MODE_TRUE)) begin
        ADDR_A_reg[11:0] <= ADDR_A_in[11:0];
        BWE_A_reg <= BWE_A_in;
        DIN_A_reg <= DIN_A_in;
        INJECT_DBITERR_A_reg <= INJECT_DBITERR_A_in;
        INJECT_SBITERR_A_reg <= INJECT_SBITERR_A_in;
        RDB_WR_A_reg <= RDB_WR_A_in;
      end
    end
  end

  always @ (*) begin
    if (((CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_MIDDLE) ||
         (CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_LAST)) && 
        (REG_CAS_A_BIN == REG_CAS_A_FALSE)) begin
      ADDR_A_int = CAS_IN_ADDR_A_in;
    end else if ((((CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_FIRST) ||
                   (CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_NONE)) && 
                  (IREG_PRE_A_BIN == IREG_PRE_A_TRUE)) ||
                 (((CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_MIDDLE) || 
                  (CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_LAST)) && 
                  (REG_CAS_A_BIN == REG_CAS_A_TRUE))) begin
      ADDR_A_int = ADDR_A_reg;
    end else begin
      ADDR_A_int = ADDR_A_in;
    end
  end

  always @ (*) begin
    if (((CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_MIDDLE) ||
         (CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_LAST)) && 
        (REG_CAS_A_BIN == REG_CAS_A_FALSE)) begin
      BWE_A_int = CAS_IN_BWE_A_in;
    end else if ((((CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_FIRST) || 
                   (CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_NONE)) && 
                  (IREG_PRE_A_BIN == IREG_PRE_A_TRUE)) ||
                 (((CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_MIDDLE) || 
                   (CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_LAST)) && 
                  (REG_CAS_A_BIN == REG_CAS_A_TRUE))) begin
      BWE_A_int = BWE_A_reg;
    end else begin
      BWE_A_int = BWE_A_in;
    end
  end

  always @ (*) begin
    if (((CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_MIDDLE) ||
         (CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_LAST)) && 
        (REG_CAS_A_BIN == REG_CAS_A_FALSE)) begin
      DIN_A_int = CAS_IN_DIN_A_in;
    end else if ((((CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_FIRST) ||
                  (CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_NONE)) && 
                  (IREG_PRE_A_BIN == IREG_PRE_A_TRUE)) ||
                 (((CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_MIDDLE) || 
                   (CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_LAST)) && 
                  (REG_CAS_A_BIN == REG_CAS_A_TRUE))) begin
      DIN_A_int = DIN_A_reg;
    end else begin
      DIN_A_int = DIN_A_in;
    end
  end

  always @ (*) begin
    if (((CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_MIDDLE) ||
         (CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_LAST)) && 
        (REG_CAS_A_BIN == REG_CAS_A_FALSE)) begin
      EN_A_int = CAS_IN_EN_A_in;
    end else if ((((CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_FIRST) || 
                   (CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_NONE)) && 
                  (IREG_PRE_A_BIN == IREG_PRE_A_TRUE)) ||
                 (((CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_MIDDLE) || 
                   (CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_LAST)) && 
                  (REG_CAS_A_BIN == REG_CAS_A_TRUE))) begin
      EN_A_int = EN_A_reg;
    end else begin
      EN_A_int = EN_A_in;
    end
  end

  always @ (*) begin
    if (IREG_PRE_A_BIN == IREG_PRE_A_TRUE) begin
      INJECT_DBITERR_A_int = INJECT_DBITERR_A_reg;
    end else begin
      INJECT_DBITERR_A_int = INJECT_DBITERR_A_in;
    end
  end

  always @ (*) begin
    if (IREG_PRE_A_BIN == IREG_PRE_A_TRUE) begin
      INJECT_SBITERR_A_int = INJECT_SBITERR_A_reg;
    end else begin
      INJECT_SBITERR_A_int = INJECT_SBITERR_A_in;
    end
  end

  always @ (*) begin
    if (((CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_MIDDLE) ||
         (CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_LAST)) && 
        (REG_CAS_A_BIN == REG_CAS_A_FALSE)) begin
      RDB_WR_A_int = CAS_IN_RDB_WR_A_in;
    end else if ((((CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_FIRST) || 
                   (CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_NONE)) && 
                  (IREG_PRE_A_BIN == IREG_PRE_A_TRUE)) ||
                 (((CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_MIDDLE) || 
                   (CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_LAST)) && 
                  (REG_CAS_A_BIN == REG_CAS_A_TRUE))) begin
      RDB_WR_A_int = RDB_WR_A_reg;
    end else begin
      RDB_WR_A_int = RDB_WR_A_in;
    end
  end

`ifdef XIL_XECLIB
  always @ (posedge CLK_in) begin
`else
  always @ (posedge CLK_in or glblGSR) begin
`endif
    if (glblGSR || 
        (((CASCADE_ORDER_B_BIN != CASCADE_ORDER_B_NONE) &&
          (REG_CAS_B_BIN == REG_CAS_B_FALSE)) &&
         (((CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_FIRST) ||
           (CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_NONE)) &&
          (IREG_PRE_B_BIN == IREG_PRE_B_FALSE)))) begin
      ADDR_B_reg <= ADDR_INIT;
      EN_B_reg <= 1'b0;
      RDB_WR_B_reg <= 1'b0;
      BWE_B_reg <= BWE_INIT;
      DIN_B_reg <= D_INIT;
      INJECT_DBITERR_B_reg <= 1'b0;
      INJECT_SBITERR_B_reg <= 1'b0;
    end else if (((CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_MIDDLE) ||
                  (CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_LAST)) &&
                 (REG_CAS_B_BIN == REG_CAS_B_TRUE)) begin
      EN_B_reg <= CAS_IN_EN_B_in;
      if (CAS_IN_EN_B_in) begin
        ADDR_B_reg[22:12] <= CAS_IN_ADDR_B_in[22:12];
      end
      if (CAS_IN_EN_B_in || (EN_AUTO_SLEEP_MODE_BIN == EN_AUTO_SLEEP_MODE_TRUE)) begin
        ADDR_B_reg[11:0] <= CAS_IN_ADDR_B_in[11:0];
        BWE_B_reg <= CAS_IN_BWE_B_in;
        DIN_B_reg <= CAS_IN_DIN_B_in;
        RDB_WR_B_reg <= CAS_IN_RDB_WR_B_in;
      end
    end else begin
      EN_B_reg <= EN_B_in;
      if (EN_B_in) begin
        ADDR_B_reg[22:12] <= ADDR_B_in[22:12];
      end
      if (EN_B_in || (EN_AUTO_SLEEP_MODE_BIN == EN_AUTO_SLEEP_MODE_TRUE)) begin
        ADDR_B_reg[11:0] <= ADDR_B_in[11:0];
        BWE_B_reg <= BWE_B_in;
        DIN_B_reg <= DIN_B_in;
        INJECT_DBITERR_B_reg <= INJECT_DBITERR_B_in;
        INJECT_SBITERR_B_reg <= INJECT_SBITERR_B_in;
        RDB_WR_B_reg <= RDB_WR_B_in;
      end
    end
  end

  always @ (*) begin
    if (((CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_MIDDLE) ||
         (CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_LAST)) && 
        (REG_CAS_B_BIN == REG_CAS_B_FALSE)) begin
      ADDR_B_int = CAS_IN_ADDR_B_in;
    end else if ((((CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_FIRST) ||
                  (CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_NONE)) && 
                  (IREG_PRE_B_BIN == IREG_PRE_B_TRUE)) ||
                 (((CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_MIDDLE) || 
                  (CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_LAST)) && 
                  (REG_CAS_B_BIN == REG_CAS_B_TRUE))) begin
      ADDR_B_int = ADDR_B_reg;
    end else begin
      ADDR_B_int = ADDR_B_in;
    end
  end

  always @ (*) begin
    if (((CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_MIDDLE) ||
         (CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_LAST)) && 
        (REG_CAS_B_BIN == REG_CAS_B_FALSE)) begin
      BWE_B_int = CAS_IN_BWE_B_in;
    end else if ((((CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_FIRST) || 
                   (CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_NONE)) && 
                  (IREG_PRE_B_BIN == IREG_PRE_B_TRUE)) ||
                 (((CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_MIDDLE) || 
                   (CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_LAST)) && 
                  (REG_CAS_B_BIN == REG_CAS_B_TRUE))) begin
      BWE_B_int = BWE_B_reg;
    end else begin
      BWE_B_int = BWE_B_in;
    end
  end

  always @ (*) begin
    if (((CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_MIDDLE) ||
         (CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_LAST)) && 
        (REG_CAS_B_BIN == REG_CAS_B_FALSE)) begin
      DIN_B_int = CAS_IN_DIN_B_in;
    end else if ((((CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_FIRST) ||
                  (CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_NONE)) && 
                  (IREG_PRE_B_BIN == IREG_PRE_B_TRUE)) ||
                 (((CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_MIDDLE) || 
                   (CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_LAST)) && 
                  (REG_CAS_B_BIN == REG_CAS_B_TRUE))) begin
      DIN_B_int = DIN_B_reg;
    end else begin
      DIN_B_int = DIN_B_in;
    end
  end

  always @ (*) begin
    if (((CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_MIDDLE) ||
         (CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_LAST)) && 
        (REG_CAS_B_BIN == REG_CAS_B_FALSE)) begin
      EN_B_int = CAS_IN_EN_B_in;
    end else if ((((CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_FIRST) || 
                   (CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_NONE)) && 
                  (IREG_PRE_B_BIN == IREG_PRE_B_TRUE)) ||
                 (((CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_MIDDLE) || 
                   (CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_LAST)) && 
                  (REG_CAS_B_BIN == REG_CAS_B_TRUE))) begin
      EN_B_int = EN_B_reg;
    end else begin
      EN_B_int = EN_B_in;
    end
  end

  always @ (*) begin
    if (IREG_PRE_B_BIN == IREG_PRE_B_TRUE) begin
      INJECT_DBITERR_B_int = INJECT_DBITERR_B_reg;
    end else begin
      INJECT_DBITERR_B_int = INJECT_DBITERR_B_in;
    end
  end

  always @ (*) begin
    if (IREG_PRE_B_BIN == IREG_PRE_B_TRUE) begin
      INJECT_SBITERR_B_int = INJECT_SBITERR_B_reg;
    end else begin
      INJECT_SBITERR_B_int = INJECT_SBITERR_B_in;
    end
  end

  always @ (*) begin
    if (((CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_MIDDLE) ||
         (CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_LAST)) && 
        (REG_CAS_B_BIN == REG_CAS_B_FALSE)) begin
      RDB_WR_B_int = CAS_IN_RDB_WR_B_in;
    end else if ((((CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_FIRST) || 
                   (CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_NONE)) && 
                  (IREG_PRE_B_BIN == IREG_PRE_B_TRUE)) ||
                 (((CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_MIDDLE) || 
                   (CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_LAST)) && 
                  (REG_CAS_B_BIN == REG_CAS_B_TRUE))) begin
      RDB_WR_B_int = RDB_WR_B_reg;
    end else begin
      RDB_WR_B_int = RDB_WR_B_in;
    end
  end

// cascade out - input controls

  always @ (*) begin 
    if ((CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_LAST) || // no cascade out
        (CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_NONE)) begin
      CAS_OUT_ADDR_A_out = ADDR_INIT;
    end else begin
      CAS_OUT_ADDR_A_out = ADDR_A_int;
    end
  end

  always @ (*) begin 
    if ((CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_LAST) || // no cascade out
        (CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_NONE)) begin
      CAS_OUT_BWE_A_out = BWE_INIT;
    end else begin
      CAS_OUT_BWE_A_out = BWE_A_int;
    end
  end

  always @ (*) begin 
    if ((CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_LAST) || // no cascade out
        (CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_NONE)) begin
      CAS_OUT_DIN_A_out = D_INIT;
    end else begin
      CAS_OUT_DIN_A_out = DIN_A_int;
    end
  end

  always @ (*) begin 
    if ((CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_LAST) || // no cascade out
        (CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_NONE)) begin
      CAS_OUT_EN_A_out = 1'b0;
    end else begin
      CAS_OUT_EN_A_out = EN_A_int;
    end
  end

  always @ (*) begin 
    if ((CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_LAST) || // no cascade out
        (CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_NONE)) begin
      CAS_OUT_RDB_WR_A_out = 1'b0;
    end else begin
      CAS_OUT_RDB_WR_A_out = RDB_WR_A_int;
    end
  end

  always @ (*) begin 
    if ((CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_LAST) || // no cascade out
        (CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_NONE)) begin
      CAS_OUT_ADDR_B_out = ADDR_INIT;
    end else begin
      CAS_OUT_ADDR_B_out = ADDR_B_int;
    end
  end

  always @ (*) begin 
    if ((CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_LAST) || // no cascade out
        (CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_NONE)) begin
      CAS_OUT_BWE_B_out = BWE_INIT;
    end else begin
      CAS_OUT_BWE_B_out = BWE_B_int;
    end
  end

  always @ (*) begin 
    if ((CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_LAST) || // no cascade out
        (CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_NONE)) begin
      CAS_OUT_DIN_B_out = D_INIT;
    end else begin
      CAS_OUT_DIN_B_out = DIN_B_int;
    end
  end

  always @ (*) begin 
    if ((CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_LAST) || // no cascade out
        (CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_NONE)) begin
      CAS_OUT_EN_B_out = 1'b0;
    end else begin
      CAS_OUT_EN_B_out = EN_B_int;
    end
  end

  always @ (*) begin 
    if ((CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_LAST) || // no cascade out
        (CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_NONE)) begin
      CAS_OUT_RDB_WR_B_out = 1'b0;
    end else begin
      CAS_OUT_RDB_WR_B_out = RDB_WR_B_int;
    end
  end

// cascade=data out - outputs

  reg [71:0] ram_data_a_lat;
  reg [71:0] ram_data_a_out;
//  reg [71:0] ram_data_a_hold=D_INIT;
  reg [71:0] ram_data_a_reg;
  reg [71:0] ram_data_a_ecc=72'h000000000000000000;
  reg [71:0] ram_data_b_lat;
  reg [71:0] ram_data_b_out;
  reg [71:0] ram_data_b_reg;
  reg [71:0] ram_data_b_ecc=72'h000000000000000000;
  reg RDACCESS_A_lat;
//  reg RDACCESS_A_hold;
  reg RDACCESS_B_lat;
  reg RDACCESS_A_int;
  reg RDACCESS_B_int;
  reg SBITERR_A_ecc=1'b0;
  reg DBITERR_A_ecc=1'b0;
  reg SBITERR_B_ecc=1'b0;
  reg DBITERR_B_ecc=1'b0;

  reg DBITERR_A_reg;
  reg DBITERR_B_reg;
  reg [71:0] DOUT_A_reg;
  reg [71:0] DOUT_B_reg;
  reg RDACCESS_A_reg;
  reg RDACCESS_B_reg;
  reg SBITERR_A_reg;
  reg SBITERR_B_reg;

  reg RDACCESS_A_ecc_reg;
  reg RDACCESS_B_ecc_reg;

  reg CAS_IN_DBITERR_A_reg;
  reg CAS_IN_DBITERR_B_reg;
  reg [71:0] CAS_IN_DOUT_A_reg;
  reg [71:0] CAS_IN_DOUT_B_reg;
  reg CAS_IN_RDACCESS_A_reg;
  reg CAS_IN_RDACCESS_B_reg;
  reg CAS_IN_SBITERR_A_reg;
  reg CAS_IN_SBITERR_B_reg;
  reg data_A_enable = 1'b0;
  reg data_B_enable = 1'b0;

// data/cas reg
`ifdef XIL_XECLIB
  always @ (posedge CLK_in or posedge RST_A_async) begin
    if (RST_A_async || RST_A_in || glblGSR || (REG_CAS_A_BIN == REG_CAS_A_FALSE)) begin
`else
  always @ (posedge CLK_in or posedge RST_A_async or glblGSR) begin
    if (RST_A_in || glblGSR || (REG_CAS_A_BIN == REG_CAS_A_FALSE)) begin
`endif
      CAS_IN_DBITERR_A_reg <= 1'b0;
      CAS_IN_DOUT_A_reg <= D_INIT;
      CAS_IN_RDACCESS_A_reg <= 1'b0;
      CAS_IN_SBITERR_A_reg <= 1'b0;
    end else begin
       if ((CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_MIDDLE) ||
           (CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_LAST)) begin
         CAS_IN_RDACCESS_A_reg <= CAS_IN_RDACCESS_A_in;
         if (CAS_IN_RDACCESS_A_in) begin
           CAS_IN_DBITERR_A_reg <= CAS_IN_DBITERR_A_in;
           CAS_IN_DOUT_A_reg <= CAS_IN_DOUT_A_in;
           CAS_IN_SBITERR_A_reg <= CAS_IN_SBITERR_A_in;
         end
       end
    end
  end

`ifdef XIL_XECLIB
  always @ (posedge CLK_in or posedge RST_B_async) begin
    if (RST_B_async || RST_B_in || glblGSR || (REG_CAS_B_BIN == REG_CAS_B_FALSE)) begin
`else
  always @ (posedge CLK_in or posedge RST_B_async or glblGSR) begin
    if (RST_B_in || glblGSR || (REG_CAS_B_BIN == REG_CAS_B_FALSE)) begin
`endif
      CAS_IN_DBITERR_B_reg <= 1'b0;
      CAS_IN_DOUT_B_reg <= D_INIT;
      CAS_IN_RDACCESS_B_reg <= 1'b0;
      CAS_IN_SBITERR_B_reg <= 1'b0;
    end else begin
       if ((CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_MIDDLE) ||
           (CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_LAST)) begin
         CAS_IN_RDACCESS_B_reg <= CAS_IN_RDACCESS_B_in;
         if (CAS_IN_RDACCESS_B_in) begin
           CAS_IN_DBITERR_B_reg <= CAS_IN_DBITERR_B_in;
           CAS_IN_DOUT_B_reg <= CAS_IN_DOUT_B_in;
           CAS_IN_SBITERR_B_reg <= CAS_IN_SBITERR_B_in;
         end
       end
    end
  end

`ifdef XIL_XECLIB
  always @ (posedge CLK_in or posedge RST_A_async) begin
    if (RST_A_async || RST_A_in || glblGSR ||
`else
  always @ (posedge CLK_in or posedge RST_A_async or glblGSR) begin
    if (RST_A_in || glblGSR ||
`endif
        shut_down || SHUTDOWN_in) begin
      RDACCESS_A_int = 1'b0;
    end else begin
      if (OREG_ECC_A_BIN == OREG_ECC_A_TRUE) begin
        if ((USE_EXT_CE_A_BIN == USE_EXT_CE_A_FALSE) || OREG_ECC_CE_A_in) begin
          RDACCESS_A_int = RDACCESS_A_ecc_reg;
        end else begin
          RDACCESS_A_int = 1'b0;
        end
      end else if (OREG_A_BIN == OREG_A_TRUE) begin
        if ((USE_EXT_CE_A_BIN == USE_EXT_CE_A_FALSE) || OREG_CE_A_in) begin
          RDACCESS_A_int = RDACCESS_A_reg;
        end else begin
          RDACCESS_A_int = 1'b0;
        end
      end else begin
          RDACCESS_A_int = RDACCESS_A_lat;
      end
    end
  end

`ifdef XIL_XECLIB
  always @ (posedge CLK_in or posedge RST_B_async) begin
    if (RST_B_async || RST_B_in || glblGSR ||
`else
  always @ (posedge CLK_in or posedge RST_B_async or glblGSR) begin
    if (RST_B_in || glblGSR ||
`endif
        shut_down || SHUTDOWN_in) begin
      RDACCESS_B_int = 1'b0;
    end else begin
      if (OREG_ECC_B_BIN == OREG_ECC_B_TRUE) begin
        if ((USE_EXT_CE_B_BIN == USE_EXT_CE_B_FALSE) || OREG_ECC_CE_B_in) begin
          RDACCESS_B_int = RDACCESS_B_ecc_reg;
        end else begin
          RDACCESS_B_int = 1'b0;
        end
      end else if (OREG_B_BIN == OREG_B_TRUE) begin
        if ((USE_EXT_CE_B_BIN == USE_EXT_CE_B_FALSE) || OREG_CE_B_in) begin
          RDACCESS_B_int = RDACCESS_B_reg;
        end else begin
          RDACCESS_B_int = 1'b0;
        end
      end else begin
          RDACCESS_B_int = RDACCESS_B_lat;
      end
    end
  end

reg cas_out_mux_sel_a;
reg cas_out_mux_sel_b;
reg cas_out_mux_sel_a_reg;
reg cas_out_mux_sel_b_reg;

  always @ (*) begin
    if ((CAS_IN_RDACCESS_A_in && REG_CAS_A_BIN == REG_CAS_A_FALSE) ||
        (CAS_IN_RDACCESS_A_reg && REG_CAS_A_BIN == REG_CAS_A_TRUE) ||
        RDACCESS_A_int) begin
      cas_out_mux_sel_a = ~RDACCESS_A_int;
    end else begin
      cas_out_mux_sel_a = ~cas_out_mux_sel_a_reg;
    end
  end

  always @ (*) begin
    if ((CAS_IN_RDACCESS_B_in && (REG_CAS_B_BIN == REG_CAS_B_FALSE)) ||
        (CAS_IN_RDACCESS_B_reg && (REG_CAS_B_BIN == REG_CAS_B_TRUE)) ||
        RDACCESS_B_int) begin
      cas_out_mux_sel_b = ~RDACCESS_B_int;
    end else begin
      cas_out_mux_sel_b = ~cas_out_mux_sel_b_reg;
    end
  end

`ifdef XIL_XECLIB
  always @ (posedge CLK_in or posedge RST_A_async) begin
    if (RST_A_async || RST_A_in || glblGSR) begin
`else
  always @ (posedge CLK_in or posedge RST_A_async or glblGSR) begin
    if (RST_A_in || glblGSR) begin
`endif
      cas_out_mux_sel_a_reg <= 1'b0;
    end else begin
      cas_out_mux_sel_a_reg <= ~cas_out_mux_sel_a;
    end
  end

`ifdef XIL_XECLIB
  always @ (posedge CLK_in or posedge RST_B_async) begin
    if (RST_B_async || RST_B_in || glblGSR) begin
`else
  always @ (posedge CLK_in or posedge RST_B_async or glblGSR) begin
    if (RST_B_in || glblGSR) begin
`endif
      cas_out_mux_sel_b_reg <= 1'b0;
    end else begin
      cas_out_mux_sel_b_reg <= ~cas_out_mux_sel_b;
    end
  end

// data out mux
  always @ (*) begin
    if (RST_A_async || RST_A_sync || glblGSR) begin
      RDACCESS_A_out = 1'b0;
    end else if (((CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_MIDDLE) ||
                  (CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_LAST)) &&
                 cas_out_mux_sel_a) begin
      if (REG_CAS_A_BIN == REG_CAS_A_TRUE) begin
        RDACCESS_A_out = CAS_IN_RDACCESS_A_reg;
      end else begin
        RDACCESS_A_out = CAS_IN_RDACCESS_A_in;
      end
    end else begin
        RDACCESS_A_out = RDACCESS_A_int;
    end
  end

  always @ (*) begin
    if (RST_A_async || RST_A_sync || shut_down || glblGSR) begin
      DBITERR_A_out = 1'b0;
      SBITERR_A_out = 1'b0;
    end else if (((CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_MIDDLE) ||
                  (CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_LAST)) &&
                 cas_out_mux_sel_a) begin
      if (REG_CAS_A_BIN == REG_CAS_A_TRUE) begin
        DBITERR_A_out = CAS_IN_DBITERR_A_reg;
        SBITERR_A_out = CAS_IN_SBITERR_A_reg;
      end else begin
        DBITERR_A_out = CAS_IN_DBITERR_A_in;
        SBITERR_A_out = CAS_IN_SBITERR_A_in;
      end
    end else if (OREG_ECC_A_BIN == OREG_ECC_A_TRUE) begin
      DBITERR_A_out = DBITERR_A_reg;
      SBITERR_A_out = SBITERR_A_reg;
    end else if (EN_ECC_RD_A_BIN == EN_ECC_RD_A_TRUE) begin
      DBITERR_A_out = DBITERR_A_ecc;
      SBITERR_A_out = SBITERR_A_ecc;
    end
  end

`ifdef XIL_XECLIB
  always @ (posedge CLK_in or posedge RST_A_async) begin
    if (RST_A_async || RST_A_in || auto_sleep || a_sleep || shut_down || SHUTDOWN_in || glblGSR) begin
`else
  always @ (posedge CLK_in or posedge RST_A_async or glblGSR) begin
    if (RST_A_in || auto_sleep || a_sleep || shut_down || SHUTDOWN_in || glblGSR) begin
`endif
      data_A_enable <= 1'b0;
    end else if ((OREG_A_BIN == OREG_A_TRUE) && ram_ce_a && ~ram_we_a) begin
      data_A_enable <= 1'b1;
    end else if ((OREG_A_BIN == OREG_A_FALSE) && ram_ce_a_int && ~RDB_WR_A_int) begin
      data_A_enable <= 1'b1;
    end
  end

`ifdef XIL_XECLIB
  always @ (posedge CLK_in or posedge RST_B_async) begin
    if (RST_B_async || RST_B_in || auto_sleep || a_sleep || shut_down || SHUTDOWN_in || glblGSR) begin
`else
  always @ (posedge CLK_in or posedge RST_B_async or glblGSR) begin
    if (RST_B_in || auto_sleep || a_sleep || shut_down || SHUTDOWN_in || glblGSR) begin
`endif
      data_B_enable <= 1'b0;
    end else if ((OREG_B_BIN == OREG_B_TRUE) && ram_ce_b && ~ram_we_b) begin
      data_B_enable <= 1'b1;
    end else if ((OREG_B_BIN == OREG_B_FALSE) && ram_ce_b_int && ~RDB_WR_B_int) begin
      data_B_enable <= 1'b1;
    end
  end

  always @ (posedge CLK_in) begin
    if (ram_ce_a && ~ram_we_a && SLEEP_in && ~a_sleep && (OREG_A_BIN == OREG_A_TRUE)) begin
      $display("Warning: [Unisim %s-3] At time (%.3f) ns: Port A READ access at ADDR (%h) just prior to SLEEP with SLEEP asserted and OREG_A attribute set to (%s) will result in READ data getting lost. Instance: %m", MODULE_NAME, $time/1000.0, ram_addr_a, OREG_A_REG);
    end else if (ram_ce_a && ram_we_a && SLEEP_in && ~a_sleep) begin
      $display("Warning: [Unisim %s-4] At time (%.3f) ns: Port A WRITE access at ADDR (%h) just prior to SLEEP with SLEEP asserted will result in WRITE data getting ignored. Instance: %m", MODULE_NAME, $time/1000.0, ram_addr_a);
    end else if (ram_ce_a_pre && a_sleep && SLEEP_in) begin
      $display("Warning: [Unisim %s-5] At time (%.3f) ns: Port A access at ADDR (%h) during SLEEP will be ignored. Instance: %m", MODULE_NAME, $time/1000.0, ram_addr_a);
    end else if (ram_ce_a_pre && a_sleep && ~SLEEP_in) begin
      $display("Warning: [Unisim %s-6] At time (%.3f) ns: Port A access at ADDR (%h) during WAKEUP time will be ignored. Instance: %m", MODULE_NAME, $time/1000.0, ram_addr_a);
    end
  end

  always @ (posedge CLK_in) begin
    if (ram_ce_b && ~ram_we_b && SLEEP_in && ~a_sleep && (OREG_B_BIN == OREG_B_TRUE)) begin
      $display("Warning: [Unisim %s-7] At time (%.3f) ns: Port B READ access at ADDR (%h) just prior to SLEEP with SLEEP asserted and OREG_B attribute set to (%s) will result in READ data getting lost. Instance: %m", MODULE_NAME, $time/1000.0, ram_addr_b, OREG_B_REG);
    end else if (ram_ce_b && ram_we_b && SLEEP_in && ~a_sleep) begin
      $display("Warning: [Unisim %s-8] At time (%.3f) ns: Port B WRITE access at ADDR (%h) just prior to SLEEP with SLEEP asserted will result in WRITE data getting ignored. Instance: %m", MODULE_NAME, $time/1000.0, ram_addr_b);
    end else if (ram_ce_b_pre && a_sleep && SLEEP_in) begin
      $display("Warning: [Unisim %s-9] At time (%.3f) ns: Port B access at ADDR (%h) during SLEEP will be ignored. Instance: %m", MODULE_NAME, $time/1000.0, ram_addr_b);
    end else if (ram_ce_b_pre && a_sleep && ~SLEEP_in) begin
      $display("Warning: [Unisim %s-10] At time (%.3f) ns: Port B access at ADDR (%h) during WAKEUP time will be ignored. Instance: %m", MODULE_NAME, $time/1000.0, ram_addr_b);
    end
  end

  always @ (*) begin
    if (RST_A_async || RST_A_sync || glblGSR) begin
      DOUT_A_out = D_INIT;
    end else if (((CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_MIDDLE) ||
                  (CASCADE_ORDER_A_BIN == CASCADE_ORDER_A_LAST)) &&
                 cas_out_mux_sel_a) begin
      if (REG_CAS_A_BIN == REG_CAS_A_TRUE) begin
        DOUT_A_out = CAS_IN_DOUT_A_reg;
      end else begin
        DOUT_A_out = CAS_IN_DOUT_A_in;
      end
    end else if (OREG_ECC_A_BIN == OREG_ECC_A_TRUE) begin
      DOUT_A_out = DOUT_A_reg;
    end else if (EN_ECC_RD_A_BIN == EN_ECC_RD_A_TRUE) begin
      DOUT_A_out = ram_data_a_ecc;
    end else if (data_A_enable) begin
      if (OREG_A_BIN == OREG_A_TRUE) begin
        DOUT_A_out = ram_data_a_reg;
      end else begin
        DOUT_A_out = ram_data_a_lat;
      end
    end else begin
      DOUT_A_out = D_INIT;
    end
  end

  always @ (*) begin
    if (RST_B_async || RST_B_sync || glblGSR) begin
      RDACCESS_B_out = 1'b0;
    end else if (((CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_MIDDLE) ||
                  (CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_LAST)) &&
                 cas_out_mux_sel_b) begin
      if (REG_CAS_B_BIN == REG_CAS_B_TRUE) begin
        RDACCESS_B_out = CAS_IN_RDACCESS_B_reg;
      end else begin
        RDACCESS_B_out = CAS_IN_RDACCESS_B_in;
      end
    end else begin
        RDACCESS_B_out = RDACCESS_B_int;
    end
  end

  always @ (*) begin
    if (RST_B_async || RST_B_sync || shut_down || glblGSR) begin
      DBITERR_B_out = 1'b0;
      SBITERR_B_out = 1'b0;
    end else if (((CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_MIDDLE) ||
                  (CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_LAST)) &&
                 cas_out_mux_sel_b) begin
      if (REG_CAS_B_BIN == REG_CAS_B_TRUE) begin
        DBITERR_B_out = CAS_IN_DBITERR_B_reg;
        SBITERR_B_out = CAS_IN_SBITERR_B_reg;
      end else begin
        DBITERR_B_out = CAS_IN_DBITERR_B_in;
        SBITERR_B_out = CAS_IN_SBITERR_B_in;
      end
    end else if (OREG_ECC_B_BIN == OREG_ECC_B_TRUE) begin
      DBITERR_B_out = DBITERR_B_reg;
      SBITERR_B_out = SBITERR_B_reg;
    end else if (EN_ECC_RD_B_BIN == EN_ECC_RD_B_TRUE) begin
      DBITERR_B_out = DBITERR_B_ecc;
      SBITERR_B_out = SBITERR_B_ecc;
    end
  end

  always @ (*) begin
    if (RST_B_async || RST_B_sync || glblGSR) begin
      DOUT_B_out = D_INIT;
    end else if (((CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_MIDDLE) ||
                  (CASCADE_ORDER_B_BIN == CASCADE_ORDER_B_LAST)) &&
                 cas_out_mux_sel_b) begin
      if (REG_CAS_B_BIN == REG_CAS_B_TRUE) begin
        DOUT_B_out = CAS_IN_DOUT_B_reg;
      end else begin
        DOUT_B_out = CAS_IN_DOUT_B_in;
      end
    end else if (OREG_ECC_B_BIN == OREG_ECC_B_TRUE) begin
      DOUT_B_out = DOUT_B_reg;
    end else if (EN_ECC_RD_B_BIN == EN_ECC_RD_B_TRUE) begin
      DOUT_B_out = ram_data_b_ecc;
    end else if (data_B_enable) begin
      if (OREG_B_BIN == OREG_B_TRUE) begin
        DOUT_B_out = ram_data_b_reg;
      end else begin
        DOUT_B_out = ram_data_b_lat;
      end
    end else begin
      DOUT_B_out = D_INIT;
    end
  end

`ifdef XIL_XECLIB
  always @ (posedge CLK_in or posedge RST_A_async) begin
    if (RST_A_async || RST_A_in || glblGSR || (OREG_ECC_A_BIN == OREG_ECC_A_FALSE)) begin
`else
  always @ (posedge CLK_in or posedge RST_A_async or glblGSR) begin
    if (RST_A_in || glblGSR || (OREG_ECC_A_BIN == OREG_ECC_A_FALSE)) begin
`endif
      DBITERR_A_reg <= 1'b0;
      SBITERR_A_reg <= 1'b0;
    end else if ((~a_sleep && ~shut_down && data_A_enable) && 
                 (((OREG_A_BIN == OREG_A_TRUE) && (RDACCESS_A_reg || RDACCESS_A_ecc_reg)) ||
                  ((OREG_A_BIN == OREG_A_FALSE) && (RDACCESS_A_lat || RDACCESS_A_ecc_reg)))) begin
      if (EN_ECC_RD_A_BIN == EN_ECC_RD_A_TRUE) begin
        if ((USE_EXT_CE_A_BIN == USE_EXT_CE_A_FALSE) || OREG_ECC_CE_A_in) begin
          DBITERR_A_reg <= DBITERR_A_ecc;
          SBITERR_A_reg <= SBITERR_A_ecc;
        end
      end
    end
  end

`ifdef XIL_XECLIB
  always @ (posedge CLK_in or posedge RST_A_async) begin
    if (RST_A_async || RST_A_in || glblGSR || (OREG_ECC_A_BIN == OREG_ECC_A_FALSE)) begin
`else
  always @ (posedge CLK_in or posedge RST_A_async or glblGSR) begin
    if (RST_A_in || glblGSR || (OREG_ECC_A_BIN == OREG_ECC_A_FALSE)) begin
`endif
      DOUT_A_reg <= D_INIT;
      end else if (~shut_down && data_A_enable) begin
      if (USE_EXT_CE_A_BIN == USE_EXT_CE_A_TRUE) begin
        if (OREG_ECC_CE_A_in) begin
          if (EN_ECC_RD_A_BIN == EN_ECC_RD_A_TRUE) begin
            DOUT_A_reg <= ram_data_a_ecc;
          end else if (OREG_A_BIN == OREG_A_TRUE) begin
            DOUT_A_reg <= ram_data_a_reg;
          end else begin
            DOUT_A_reg <= ram_data_a_lat;
          end
        end
      end else if (((OREG_A_BIN == OREG_A_TRUE) && (RDACCESS_A_reg || RDACCESS_A_ecc_reg)) ||
                   ((OREG_A_BIN == OREG_A_FALSE) && (RDACCESS_A_lat || RDACCESS_A_ecc_reg))) begin
          if (EN_ECC_RD_A_BIN == EN_ECC_RD_A_TRUE) begin
            DOUT_A_reg <= ram_data_a_ecc;
          end else if (OREG_A_BIN == OREG_A_TRUE) begin
            DOUT_A_reg <= ram_data_a_reg;
          end else begin
            DOUT_A_reg <= ram_data_a_lat;
          end
        end
    end
  end

`ifdef XIL_XECLIB
  always @ (posedge CLK_in or posedge RST_A_async) begin
    if (RST_A_async || RST_A_in || glblGSR || (OREG_ECC_A_BIN == OREG_ECC_A_FALSE)) begin
`else
  always @ (posedge CLK_in or posedge RST_A_async or glblGSR) begin
    if (RST_A_in || glblGSR || (OREG_ECC_A_BIN == OREG_ECC_A_FALSE)) begin
`endif
      RDACCESS_A_ecc_reg <= 1'b0;
    end else begin
      if (OREG_A_BIN == OREG_A_TRUE) begin
        if ((USE_EXT_CE_A_BIN == USE_EXT_CE_A_FALSE) || OREG_CE_A_in) begin
          RDACCESS_A_ecc_reg <= RDACCESS_A_reg;
        end
      end else begin
        RDACCESS_A_ecc_reg <= RDACCESS_A_lat;
      end
    end
  end

`ifdef XIL_XECLIB
  always @ (posedge CLK_in or posedge RST_B_async) begin
    if (RST_B_async || RST_B_in || glblGSR || (OREG_ECC_B_BIN == OREG_ECC_B_FALSE)) begin
`else
  always @ (posedge CLK_in or posedge RST_B_async or glblGSR) begin
    if (RST_B_in || glblGSR || (OREG_ECC_B_BIN == OREG_ECC_B_FALSE)) begin
`endif
      DBITERR_B_reg <= 1'b0;
      SBITERR_B_reg <= 1'b0;
    end else if ((~a_sleep && ~shut_down && data_B_enable) && 
                 (((OREG_B_BIN == OREG_B_TRUE) && (RDACCESS_B_reg || RDACCESS_B_ecc_reg)) ||
                  ((OREG_B_BIN == OREG_B_FALSE) && (RDACCESS_B_lat || RDACCESS_B_ecc_reg)))) begin
      if (EN_ECC_RD_B_BIN == EN_ECC_RD_B_TRUE) begin
        if ((USE_EXT_CE_B_BIN == USE_EXT_CE_B_FALSE) || OREG_ECC_CE_B_in) begin
          DBITERR_B_reg <= DBITERR_B_ecc;
          SBITERR_B_reg <= SBITERR_B_ecc;
        end
      end
    end
  end

`ifdef XIL_XECLIB
  always @ (posedge CLK_in or posedge RST_B_async) begin
    if (RST_B_async || RST_B_in || glblGSR || (OREG_ECC_B_BIN == OREG_ECC_B_FALSE)) begin
`else
  always @ (posedge CLK_in or posedge RST_B_async or glblGSR) begin
    if (RST_B_in || glblGSR || (OREG_ECC_B_BIN == OREG_ECC_B_FALSE)) begin
`endif
      DOUT_B_reg <= D_INIT;
      end else if (~shut_down && data_B_enable) begin
        if (USE_EXT_CE_B_BIN == USE_EXT_CE_B_TRUE) begin
          if (OREG_ECC_CE_B_in) begin
            if (EN_ECC_RD_B_BIN == EN_ECC_RD_B_TRUE) begin
              DOUT_B_reg <= ram_data_b_ecc;
            end else if (OREG_B_BIN == OREG_B_TRUE) begin
              DOUT_B_reg <= ram_data_b_reg;
            end else begin
              DOUT_B_reg <= ram_data_b_lat;
            end
          end
        end else if (((OREG_B_BIN == OREG_B_TRUE) && (RDACCESS_B_reg || RDACCESS_B_ecc_reg)) ||
                     ((OREG_B_BIN == OREG_B_FALSE) && (RDACCESS_B_lat || RDACCESS_B_ecc_reg))) begin
          if (EN_ECC_RD_B_BIN == EN_ECC_RD_B_TRUE) begin
            DOUT_B_reg <= ram_data_b_ecc;
          end else if (OREG_B_BIN == OREG_B_TRUE) begin
            DOUT_B_reg <= ram_data_b_reg;
          end else begin
            DOUT_B_reg <= ram_data_b_lat;
          end
        end
    end
  end

`ifdef XIL_XECLIB
  always @ (posedge CLK_in or posedge RST_B_async) begin
    if (RST_B_async || RST_B_in || glblGSR || (OREG_ECC_B_BIN == OREG_ECC_B_FALSE)) begin
`else
  always @ (posedge CLK_in or posedge RST_B_async or glblGSR) begin
    if (RST_B_in || glblGSR || (OREG_ECC_B_BIN == OREG_ECC_B_FALSE)) begin
`endif
      RDACCESS_B_ecc_reg <= 1'b0;
    end else begin
      if (OREG_B_BIN == OREG_B_TRUE) begin
        if ((USE_EXT_CE_B_BIN == USE_EXT_CE_B_FALSE) || OREG_CE_B_in) begin
          RDACCESS_B_ecc_reg <= RDACCESS_B_reg;
        end
      end else begin
        RDACCESS_B_ecc_reg <= RDACCESS_B_lat;
      end
    end
  end

// ram oreg
`ifdef XIL_XECLIB
  always @ (posedge CLK_in or posedge RST_A_async) begin
    if (RST_A_async || RST_A_in || shut_down || a_sleep || glblGSR) begin
`else
  always @ (posedge CLK_in or posedge RST_A_async or shut_down or glblGSR) begin
    if (RST_A_in || shut_down || a_sleep || glblGSR) begin
`endif
      RDACCESS_A_reg <= 1'b0;
    end else begin
      RDACCESS_A_reg <= RDACCESS_A_lat;
    end
  end

`ifdef XIL_XECLIB
  always @ (posedge CLK_in or posedge RST_A_async) begin
    if (RST_A_async || RST_A_in || shut_down || SLEEP_in || a_sleep || glblGSR || (OREG_A_BIN == OREG_A_FALSE)) begin
`else
  always @ (posedge CLK_in or posedge RST_A_async or shut_down or glblGSR) begin
    if (RST_A_in || shut_down || SLEEP_in || a_sleep || glblGSR || (OREG_A_BIN == OREG_A_FALSE)) begin
`endif
      ram_data_a_reg <= D_INIT;
    end else if (USE_EXT_CE_A_BIN == USE_EXT_CE_A_TRUE) begin
      if (OREG_CE_A_in) begin
        ram_data_a_reg = ram_data_a_lat;
      end
    end else if (ram_ce_a_int || RDACCESS_A_reg) begin
      ram_data_a_reg = ram_data_a_lat;
    end
  end

`ifdef XIL_XECLIB
  always @ (posedge CLK_in or posedge RST_B_async) begin
    if (RST_B_async || RST_B_in || shut_down || a_sleep || glblGSR) begin
`else
  always @ (posedge CLK_in or posedge RST_B_async or shut_down or glblGSR) begin
    if (RST_B_in || shut_down || a_sleep || glblGSR) begin
`endif
      RDACCESS_B_reg <= 1'b0;
    end else begin
      RDACCESS_B_reg <= RDACCESS_B_lat;
    end
  end

`ifdef XIL_XECLIB
  always @ (posedge CLK_in or posedge RST_B_async) begin
    if (RST_B_async || RST_B_in || shut_down || SLEEP_in || a_sleep || glblGSR || (OREG_B_BIN == OREG_B_FALSE)) begin
`else
  always @ (posedge CLK_in or posedge RST_B_async or shut_down or glblGSR) begin
    if (RST_B_in || shut_down || SLEEP_in || a_sleep || glblGSR || (OREG_B_BIN == OREG_B_FALSE)) begin
`endif
      ram_data_b_reg <= D_INIT;
    end else if (USE_EXT_CE_B_BIN == USE_EXT_CE_B_TRUE) begin
      if (OREG_CE_B_in) begin
        ram_data_b_reg = ram_data_b_lat;
      end
    end else if (ram_ce_b_int || RDACCESS_B_reg) begin
      ram_data_b_reg = ram_data_b_lat;
    end
  end

  reg [15:1] ram_ce_a_fifo_in = 15'b0;
  always @ (*) begin
    ram_ce_a_fifo_in = 15'b0;
    ram_ce_a_fifo_in[AUTO_SLEEP_LATENCY_BIN] = &(~(ADDR_A_int[22:12] ^ SELF_ADDR_A_REG) | SELF_MASK_A_REG) && EN_A_int;
  end
`ifdef XIL_XECLIB
  always @ (posedge CLK_in) begin
`else
  always @ (posedge CLK_in or glblGSR) begin
`endif
    if (glblGSR || (EN_AUTO_SLEEP_MODE_BIN == EN_AUTO_SLEEP_MODE_FALSE)) begin
      ram_ce_a_fifo <= 15'b0;
    end else begin
      ram_ce_a_fifo <= {1'b0, ram_ce_a_fifo[15:2]} | ram_ce_a_fifo_in;
    end
  end

  always @ (*) begin
    if (EN_AUTO_SLEEP_MODE_BIN == EN_AUTO_SLEEP_MODE_FALSE) begin
      ram_ce_a_pre = &(~(ADDR_A_int[22:12] ^ SELF_ADDR_A_REG) | SELF_MASK_A_REG) && EN_A_int;
    end else begin
      ram_ce_a_pre = ram_ce_a_fifo[1]; 
    end
  end

  always @ (*) begin
    if (a_sleep || SLEEP_in || auto_sleep) begin
      ram_ce_a_int = 1'b0;
    end else begin
      ram_ce_a_int = ram_ce_a_pre;
    end
  end

  reg [15:1] ram_ce_b_fifo_in = 15'b0;
  always @ (*) begin
    ram_ce_b_fifo_in = 15'b0;
    ram_ce_b_fifo_in[AUTO_SLEEP_LATENCY_BIN] = &(~(ADDR_B_int[22:12] ^ SELF_ADDR_B_REG) | SELF_MASK_B_REG) && EN_B_int;
  end
`ifdef XIL_XECLIB
  always @ (posedge CLK_in) begin
`else
  always @ (posedge CLK_in or glblGSR) begin
`endif
    if (glblGSR || (EN_AUTO_SLEEP_MODE_BIN == EN_AUTO_SLEEP_MODE_FALSE)) begin
      ram_ce_b_fifo <= 15'b0;
    end else begin
      ram_ce_b_fifo <= {1'b0, ram_ce_b_fifo[15:2]} | ram_ce_b_fifo_in;
    end
  end

  always @ (*) begin
    if (EN_AUTO_SLEEP_MODE_BIN == EN_AUTO_SLEEP_MODE_FALSE) begin
      ram_ce_b_pre = &(~(ADDR_B_int[22:12] ^ SELF_ADDR_B_REG) | SELF_MASK_B_REG) && EN_B_int;
    end else begin
      ram_ce_b_pre = ram_ce_b_fifo[1]; 
    end
  end

  always @ (*) begin
    if (a_sleep || SLEEP_in || auto_sleep) begin
      ram_ce_b_int = 1'b0;
    end else begin
      ram_ce_b_int = ram_ce_b_pre;
    end
  end

`ifdef XIL_XECLIB
  always @ (posedge CLK_in) begin
`else
  always @ (posedge CLK_in or glblGSR) begin
`endif
    if (glblGSR || ~RDB_WR_A_int || a_sleep || DEEPSLEEP_in || SLEEP_in || auto_sleep || shut_down || SHUTDOWN_in) begin
      ram_bwe_a <= 72'h00;
    end else if (ram_ce_a_int) begin
      if (EN_ECC_WR_A_BIN == EN_ECC_WR_A_TRUE) begin
        ram_bwe_a <= 72'hFFFFFFFFFFFFFFFFFF;
      end else if (BWE_MODE_A_BIN == BWE_MODE_A_PARITY_INTERLEAVED) begin
        ram_bwe_a <= {BWE_A_int[7:0], 
                       {8{BWE_A_int[7]}}, {8{BWE_A_int[6]}}, {8{BWE_A_int[5]}}, {8{BWE_A_int[4]}},
                       {8{BWE_A_int[3]}}, {8{BWE_A_int[2]}}, {8{BWE_A_int[1]}}, {8{BWE_A_int[0]}}};
      end else begin
        ram_bwe_a <= {{8{BWE_A_int[8]}},
                       {8{BWE_A_int[7]}}, {8{BWE_A_int[6]}}, {8{BWE_A_int[5]}}, {8{BWE_A_int[4]}},
                       {8{BWE_A_int[3]}}, {8{BWE_A_int[2]}}, {8{BWE_A_int[1]}}, {8{BWE_A_int[0]}}};
      end
    end
  end

`ifdef XIL_XECLIB
  always @ (posedge CLK_in) begin
`else
  always @ (posedge CLK_in or glblGSR) begin
`endif
    if (glblGSR || ~RDB_WR_B_int || a_sleep || DEEPSLEEP_in || SLEEP_in || auto_sleep || shut_down || SHUTDOWN_in) begin
      ram_bwe_b <= 72'b0;
    end else if (ram_ce_b_int) begin
      if (EN_ECC_WR_B_BIN == EN_ECC_WR_B_TRUE) begin
        ram_bwe_b <= 72'hFFFFFFFFFFFFFFFFFF;
      end else if (BWE_MODE_B_BIN == BWE_MODE_B_PARITY_INTERLEAVED) begin
        ram_bwe_b <= {BWE_B_int[7:0], 
                       {8{BWE_B_int[7]}}, {8{BWE_B_int[6]}}, {8{BWE_B_int[5]}}, {8{BWE_B_int[4]}},
                       {8{BWE_B_int[3]}}, {8{BWE_B_int[2]}}, {8{BWE_B_int[1]}}, {8{BWE_B_int[0]}}};
      end else begin
        ram_bwe_b <= {{8{BWE_B_int[8]}},
                       {8{BWE_B_int[7]}}, {8{BWE_B_int[6]}}, {8{BWE_B_int[5]}}, {8{BWE_B_int[4]}},
                       {8{BWE_B_int[3]}}, {8{BWE_B_int[2]}}, {8{BWE_B_int[1]}}, {8{BWE_B_int[0]}}};
      end
    end
  end


`ifdef XIL_XECLIB
  always @ (posedge CLK_in) begin
`else
  always @ (posedge CLK_in or glblGSR) begin
`endif
    if (glblGSR || a_sleep || DEEPSLEEP_in || SLEEP_in || auto_sleep || shut_down || SHUTDOWN_in) begin
      ram_addr_a <= 12'b0;
    end else if (ram_ce_a_int) begin
      ram_addr_a <= ADDR_A_int[11:0];
    end
  end

`ifdef XIL_XECLIB
  always @ (posedge CLK_in) begin
`else
  always @ (posedge CLK_in or glblGSR) begin
`endif
    if (glblGSR || a_sleep || DEEPSLEEP_in || SLEEP_in || auto_sleep || shut_down || SHUTDOWN_in) begin
      ram_addr_b <= 12'b0;
    end else if (ram_ce_b_int) begin
      ram_addr_b <= ADDR_B_int[11:0];
    end
  end

`ifdef XIL_XECLIB
  always @ (posedge CLK_in or posedge RST_A_async) begin
    if (glblGSR || (RST_A_async || RST_A_in) || a_sleep || DEEPSLEEP_in || SLEEP_in || auto_sleep || shut_down || SHUTDOWN_in) begin
`else
  always @ (posedge CLK_in or posedge RST_A_async or glblGSR) begin
    if (glblGSR || RST_A_in || a_sleep || DEEPSLEEP_in || SLEEP_in || auto_sleep || shut_down || SHUTDOWN_in) begin
`endif
      ram_ce_a <= 1'b0;
    end else begin
      ram_ce_a <= ram_ce_a_int;
    end
  end

`ifdef XIL_XECLIB
  always @ (posedge CLK_in or posedge RST_B_async) begin
    if (glblGSR || (RST_B_async || RST_B_in) || a_sleep || DEEPSLEEP_in || SLEEP_in || auto_sleep || shut_down || SHUTDOWN_in) begin
`else
  always @ (posedge CLK_in or posedge RST_B_async or glblGSR) begin
    if (glblGSR || RST_B_in || a_sleep || DEEPSLEEP_in || SLEEP_in || auto_sleep || shut_down || SHUTDOWN_in) begin
`endif
      ram_ce_b <= 1'b0;
    end else begin
      ram_ce_b <= ram_ce_b_int;
    end
  end

`ifdef XIL_XECLIB
  always @ (posedge CLK_in) begin
`else
  always @ (posedge CLK_in or glblGSR) begin
`endif
    if (glblGSR || a_sleep || DEEPSLEEP_in || SLEEP_in || auto_sleep || shut_down || SHUTDOWN_in || ~ram_ce_a_int) begin
      ram_we_a <= 1'b0;
    end else begin
      ram_we_a <= RDB_WR_A_int;
      if (RDB_WR_A_int) ram_we_a_event <= ~ram_we_a_event;
    end
  end

`ifdef XIL_XECLIB
  always @ (posedge CLK_in) begin
`else
  always @ (posedge CLK_in or glblGSR) begin
`endif
    if (glblGSR || a_sleep || DEEPSLEEP_in || SLEEP_in || auto_sleep || shut_down || SHUTDOWN_in || ~ram_ce_b_int) begin
      ram_we_b <= 1'b0;
    end else begin
      ram_we_b <= RDB_WR_B_int;
      if (RDB_WR_B_int) ram_we_b_event <= ~ram_we_b_event;
    end
  end

`ifdef XIL_XECLIB
  always @ (posedge CLK_in) begin
`else
  always @ (posedge CLK_in or glblGSR) begin
`endif
    if (glblGSR || a_sleep || DEEPSLEEP_in || SLEEP_in || auto_sleep || shut_down || SHUTDOWN_in) begin
      ram_data_a <= D_INIT;
    end else if (RDB_WR_A_int && ram_ce_a_int) begin
      if (EN_ECC_WR_A_BIN == EN_ECC_WR_A_TRUE) begin
        ram_data_a[63:0] <= {DIN_A_int[63],
                             DIN_A_int[62] ^ (INJECT_DBITERR_A_int),
                             DIN_A_int[61:31],
                             DIN_A_int[30] ^ (INJECT_DBITERR_A_int || INJECT_SBITERR_A_int),
                             DIN_A_int[29:0]};
        ram_data_a[71:64] <= fn_ecc(encode, DIN_A_int[63:0], DIN_A_int[71:64]);
      end else if (EN_ECC_RD_A_BIN == EN_ECC_RD_A_TRUE) begin
        ram_data_a[63:0] <= {DIN_A_int[63],
                             DIN_A_int[62] ^ (INJECT_DBITERR_A_int),
                             DIN_A_int[61:31],
                             DIN_A_int[30] ^ (INJECT_DBITERR_A_int || INJECT_SBITERR_A_int),
                             DIN_A_int[29:0]};
        ram_data_a[71:64] <= DIN_A_int[71:64];
      end else begin
        ram_data_a <= DIN_A_int;
      end
    end
  end

`ifdef XIL_XECLIB
  always @ (posedge CLK_in) begin
`else
  always @ (posedge CLK_in or glblGSR) begin
`endif
    if (glblGSR || a_sleep || DEEPSLEEP_in || SLEEP_in || auto_sleep || shut_down || SHUTDOWN_in) begin
      ram_data_b <= D_INIT;
    end else if (RDB_WR_B_int && ram_ce_b_int) begin
      if (EN_ECC_WR_B_BIN == EN_ECC_WR_B_TRUE) begin
        ram_data_b[63:0] <= {DIN_B_int[63],
                             DIN_B_int[62] ^ (INJECT_DBITERR_B_int),
                             DIN_B_int[61:31],
                             DIN_B_int[30] ^ (INJECT_DBITERR_B_int || INJECT_SBITERR_B_int),
                             DIN_B_int[29:0]};
        ram_data_b[71:64] <= fn_ecc(encode, DIN_B_int[63:0], DIN_B_int[71:64]);
      end else if (EN_ECC_RD_B_BIN == EN_ECC_RD_B_TRUE) begin
        ram_data_b[63:0] <= {DIN_B_int[63],
                             DIN_B_int[62] ^ (INJECT_DBITERR_B_int),
                             DIN_B_int[61:31],
                             DIN_B_int[30] ^ (INJECT_DBITERR_B_int || INJECT_SBITERR_B_int),
                             DIN_B_int[29:0]};
        ram_data_b[71:64] <= DIN_B_int[71:64];
      end else begin
        ram_data_b <= DIN_B_int;
      end
    end
  end

// ram
  always @ (*) begin
    if ((auto_sleep || SLEEP_in || SHUTDOWN_in || DEEPSLEEP_in) ||
        (((OREG_A_BIN == OREG_A_TRUE) || (OREG_ECC_A_BIN == OREG_ECC_A_TRUE )) &&
         (a_sleep || shut_down)))begin
      RDACCESS_A_lat <= 1'b0;
    end else if ((ram_ce_a_int === 1'b1) && (RDB_WR_A_int === 1'b0)) begin
      RDACCESS_A_lat <= 1'b1;
    end else begin
      RDACCESS_A_lat <= 1'b0;
    end
  end

  always @ (*) begin
    if ((auto_sleep || SLEEP_in || SHUTDOWN_in || DEEPSLEEP_in) ||
        (((OREG_B_BIN == OREG_B_TRUE) || (OREG_ECC_B_BIN == OREG_ECC_B_TRUE )) &&
         (a_sleep || shut_down)))begin
      RDACCESS_B_lat <= 1'b0;
    end else if ((ram_ce_b_int === 1'b1) && (RDB_WR_B_int === 1'b0)) begin
      RDACCESS_B_lat <= 1'b1;
    end else begin
      RDACCESS_B_lat <= 1'b0;
    end
  end

`ifndef XIL_XECLIB
//  always @ (posedge INIT_RAM or posedge glblGSR) begin
  always @ (posedge INIT_RAM) begin
    for (wa=0;wa<mem_depth;wa=wa+1) begin
        mem[wa] <= D_INIT;
    end
  end
  always @ (posedge shut_down) begin
    for (wa=0;wa<mem_depth;wa=wa+1) begin
        mem[wa] <= D_UNDEF;
    end
  end
`endif

  always @ (*) begin
    if (RST_A_sync || RST_A_async || glblGSR || a_sleep || shut_down) begin
      ram_data_a_lat = D_INIT;
    end else if (ram_ce_a && ~ram_we_a) begin 
      ram_data_a_lat = ram_data_a_out;
    end
  end

  always @ (*) begin
    if (RST_B_sync || RST_B_async || glblGSR || a_sleep || shut_down) begin
      ram_data_b_lat = D_INIT;
    end else if (ram_ce_b && ~ram_we_b) begin 
      ram_data_b_lat = ram_data_b_out;
    end
  end

`ifdef XIL_XECLIB
  always @ (posedge RST_A_async or posedge RST_B_async or posedge CLK_in) begin
`else
  always @ (ram_we_a or ram_we_b or ram_ce_a or ram_ce_b or a_sleep or shut_down or ram_addr_a or ram_addr_b or ram_data_a or ram_data_b or ram_bwe_a or ram_bwe_b or ram_we_a_event or ram_we_b_event or posedge RST_A_async or posedge RST_B_async or posedge RST_A_sync or posedge RST_B_sync or glblGSR) begin
`endif
    if (RST_A_async || RST_A_sync || shut_down || glblGSR) begin
      ram_data_a_out = D_INIT;
    end
    if (ram_we_a && ~shut_down && ~a_sleep && ~glblGSR) begin
      mem [ram_addr_a] = (ram_data_a & ram_bwe_a) | (mem [ram_addr_a] & ~ram_bwe_a);
    end 
    if (ram_ce_a && ~ram_we_a && ~RST_A_in && ~shut_down && ~a_sleep && ~glblGSR) begin
      ram_data_a_out = mem[ram_addr_a];
    end

    if (RST_B_async || RST_B_sync || shut_down || glblGSR) begin
      ram_data_b_out = D_INIT;
    end
    if (ram_we_b && ~shut_down && ~a_sleep && ~glblGSR) begin
      mem [ram_addr_b] = (ram_data_b & ram_bwe_b) | (mem [ram_addr_b] & ~ram_bwe_b);
    end 
    if (ram_ce_b && ~ram_we_b && ~RST_B_in && ~shut_down && ~a_sleep && ~glblGSR) begin
      ram_data_b_out = mem[ram_addr_b];
    end
  end

// ecc correction
  task ecc_cor;
  output [71:0] data_cor; output sbiterr; output dbiterr;
  input [71:0] data;
  reg [7:0] synd_rd; reg [7:0] synd_ecc; reg decode;
  begin
    decode = 1'b0;
    synd_rd = fn_ecc(decode, data[63:0], data[71:64]);
    synd_ecc = synd_rd ^ data[71:64];
    sbiterr = (|synd_ecc &&  synd_ecc[7]);
    dbiterr = (|synd_ecc && ~synd_ecc[7]);
    if (sbiterr) begin
      data_cor = fn_cor_bit(synd_ecc[6:0],data[63:0],data[71:64]);
    end else begin
      data_cor = data;
    end
  end
  endtask

  always @ (*) begin
    if (a_sleep || shut_down || glblGSR || (EN_ECC_RD_A_BIN == EN_ECC_RD_A_FALSE)) begin
      ram_data_a_ecc <= D_INIT;
    end else if (EN_ECC_RD_A_BIN == EN_ECC_RD_A_TRUE) begin
      if (OREG_A_BIN == OREG_A_TRUE) begin
        ecc_cor(ram_data_a_ecc, SBITERR_A_ecc, DBITERR_A_ecc, ram_data_a_reg);
      end else begin
        ecc_cor(ram_data_a_ecc, SBITERR_A_ecc, DBITERR_A_ecc, ram_data_a_lat);
      end
    end
  end

  always @ (*) begin
    if (a_sleep || shut_down || glblGSR || (EN_ECC_RD_B_BIN == EN_ECC_RD_B_FALSE)) begin
      ram_data_b_ecc <= D_INIT;
    end else if (EN_ECC_RD_B_BIN == EN_ECC_RD_B_TRUE) begin
      if (OREG_B_BIN == OREG_B_TRUE) begin
        ecc_cor(ram_data_b_ecc, SBITERR_B_ecc, DBITERR_B_ecc, ram_data_b_reg);
      end else begin
        ecc_cor(ram_data_b_ecc, SBITERR_B_ecc, DBITERR_B_ecc, ram_data_b_lat);
      end
    end
  end

// sleep, deepsleep, shutdown
`ifdef XIL_XECLIB
  always @ (posedge CLK_in) begin
`else
  always @ (posedge CLK_in or glblGSR) begin
`endif
    if (glblGSR) begin
      wake_count <= 0;
    end else if (((wake_count > 0) && 
                  (~(auto_sleep || SLEEP_in || DEEPSLEEP_in || SHUTDOWN_in))) ||
                 (~(SHUTDOWN_in || DEEPSLEEP_in) && (wake_count > 2)) ||
                 (~SHUTDOWN_in && (wake_count > 3))) begin
      wake_count <= wake_count - 1;
    end else if (SHUTDOWN_in) begin
      wake_count <= 9;
    end else if (DEEPSLEEP_in && (wake_count <= 3)) begin
      wake_count <= 3;
    end else if (SLEEP_in && (wake_count <= 2)) begin
      wake_count <= 2;
    end else if (auto_sleep && (wake_count <= 1)) begin
      wake_count <= 1;
    end
  end

`ifdef XIL_XECLIB
  always @ (posedge CLK_in) begin
`else
  always @ (posedge CLK_in or glblGSR) begin
`endif
    if (glblGSR || (~auto_sleep && wake_count == 1)) begin
      a_sleep <= 1'b0;
    end else if (DEEPSLEEP_in || SLEEP_in || auto_sleep) begin
      a_sleep <= 1'b1;
    end
  end

`ifdef XIL_XECLIB
  always @ (posedge CLK_in) begin
`else
  always @ (posedge CLK_in or glblGSR) begin
`endif
    if (glblGSR || (wake_count == 1)) begin
      shut_down <= 1'b0;
    end else if (SHUTDOWN_in) begin
      shut_down <= 1'b1;
    end
  end

  assign auto_sleep = auto_sleep_A && auto_sleep_B && ~auto_wake_up_A && ~auto_wake_up_B; 
  assign auto_wake_up_A = ram_ce_a_fifo[3];

`ifdef XIL_XECLIB
  always @ (posedge CLK_in) begin
`else
  always @ (posedge CLK_in or glblGSR) begin
`endif
    if (glblGSR || (EN_AUTO_SLEEP_MODE_BIN == EN_AUTO_SLEEP_MODE_FALSE)) begin
      auto_sleep_A <= 1'b0;
    end else if (auto_wake_up_A &&  auto_sleep_A) begin
      auto_sleep_A <= 1'b0;
    end else if (~|ram_ce_a_fifo && ~auto_sleep_A) begin
      auto_sleep_A <= 1'b1;
    end
  end

  assign auto_wake_up_B = ram_ce_b_fifo[3];
`ifdef XIL_XECLIB
  always @ (posedge CLK_in) begin
`else
  always @ (posedge CLK_in or glblGSR) begin
`endif
    if (glblGSR || (EN_AUTO_SLEEP_MODE_BIN == EN_AUTO_SLEEP_MODE_FALSE)) begin
      auto_sleep_B <= 1'b0;
    end else if (auto_wake_up_B &&  auto_sleep_B) begin
      auto_sleep_B <= 1'b0;
    end else if (~|ram_ce_b_fifo && ~auto_sleep_B) begin
      auto_sleep_B <= 1'b1;
    end
  end

// end behavioral model

`ifndef XIL_XECLIB
`ifdef XIL_TIMING
  
  wire clk_en_n;
  wire clk_en_p;
  
  assign clk_en_n =  IS_CLK_INVERTED_REG;
  assign clk_en_p = ~IS_CLK_INVERTED_REG;

`endif

  specify
    (ADDR_A *> CAS_OUT_ADDR_A) = (0:0:0, 0:0:0);
    (ADDR_B *> CAS_OUT_ADDR_B) = (0:0:0, 0:0:0);
    (BWE_A *> CAS_OUT_BWE_A) = (0:0:0, 0:0:0);
    (BWE_B *> CAS_OUT_BWE_B) = (0:0:0, 0:0:0);
    (CAS_IN_ADDR_A *> CAS_OUT_ADDR_A) = (0:0:0, 0:0:0);
    (CAS_IN_ADDR_B *> CAS_OUT_ADDR_B) = (0:0:0, 0:0:0);
    (CAS_IN_BWE_A *> CAS_OUT_BWE_A) = (0:0:0, 0:0:0);
    (CAS_IN_BWE_B *> CAS_OUT_BWE_B) = (0:0:0, 0:0:0);
    (CAS_IN_DBITERR_A => CAS_OUT_DBITERR_A) = (0:0:0, 0:0:0);
    (CAS_IN_DBITERR_A => DBITERR_A) = (0:0:0, 0:0:0);
    (CAS_IN_DBITERR_B => CAS_OUT_DBITERR_B) = (0:0:0, 0:0:0);
    (CAS_IN_DBITERR_B => DBITERR_B) = (0:0:0, 0:0:0);
    (CAS_IN_DIN_A *> CAS_OUT_DIN_A) = (0:0:0, 0:0:0);
    (CAS_IN_DIN_B *> CAS_OUT_DIN_B) = (0:0:0, 0:0:0);
    (CAS_IN_DOUT_A *> CAS_OUT_DOUT_A) = (0:0:0, 0:0:0);
    (CAS_IN_DOUT_A *> DOUT_A) = (0:0:0, 0:0:0);
    (CAS_IN_DOUT_B *> CAS_OUT_DOUT_B) = (0:0:0, 0:0:0);
    (CAS_IN_DOUT_B *> DOUT_B) = (0:0:0, 0:0:0);
    (CAS_IN_EN_A => CAS_OUT_EN_A) = (0:0:0, 0:0:0);
    (CAS_IN_EN_B => CAS_OUT_EN_B) = (0:0:0, 0:0:0);
    (CAS_IN_RDACCESS_A *> CAS_OUT_DOUT_A) = (0:0:0, 0:0:0);
    (CAS_IN_RDACCESS_A *> DOUT_A) = (0:0:0, 0:0:0);
    (CAS_IN_RDACCESS_A => CAS_OUT_DBITERR_A) = (0:0:0, 0:0:0);
    (CAS_IN_RDACCESS_A => CAS_OUT_RDACCESS_A) = (0:0:0, 0:0:0);
    (CAS_IN_RDACCESS_A => CAS_OUT_SBITERR_A) = (0:0:0, 0:0:0);
    (CAS_IN_RDACCESS_A => DBITERR_A) = (0:0:0, 0:0:0);
    (CAS_IN_RDACCESS_A => RDACCESS_A) = (0:0:0, 0:0:0);
    (CAS_IN_RDACCESS_A => SBITERR_A) = (0:0:0, 0:0:0);
    (CAS_IN_RDACCESS_B *> CAS_OUT_DOUT_B) = (0:0:0, 0:0:0);
    (CAS_IN_RDACCESS_B *> DOUT_B) = (0:0:0, 0:0:0);
    (CAS_IN_RDACCESS_B => CAS_OUT_DBITERR_B) = (0:0:0, 0:0:0);
    (CAS_IN_RDACCESS_B => CAS_OUT_RDACCESS_B) = (0:0:0, 0:0:0);
    (CAS_IN_RDACCESS_B => CAS_OUT_SBITERR_B) = (0:0:0, 0:0:0);
    (CAS_IN_RDACCESS_B => DBITERR_B) = (0:0:0, 0:0:0);
    (CAS_IN_RDACCESS_B => RDACCESS_B) = (0:0:0, 0:0:0);
    (CAS_IN_RDACCESS_B => SBITERR_B) = (0:0:0, 0:0:0);
    (CAS_IN_RDB_WR_A => CAS_OUT_RDB_WR_A) = (0:0:0, 0:0:0);
    (CAS_IN_RDB_WR_B => CAS_OUT_RDB_WR_B) = (0:0:0, 0:0:0);
    (CAS_IN_SBITERR_A => CAS_OUT_SBITERR_A) = (0:0:0, 0:0:0);
    (CAS_IN_SBITERR_A => SBITERR_A) = (0:0:0, 0:0:0);
    (CAS_IN_SBITERR_B => CAS_OUT_SBITERR_B) = (0:0:0, 0:0:0);
    (CAS_IN_SBITERR_B => SBITERR_B) = (0:0:0, 0:0:0);
    (CLK *> CAS_OUT_ADDR_A) = (100:100:100, 100:100:100);
    (CLK *> CAS_OUT_ADDR_B) = (100:100:100, 100:100:100);
    (CLK *> CAS_OUT_BWE_A) = (100:100:100, 100:100:100);
    (CLK *> CAS_OUT_BWE_B) = (100:100:100, 100:100:100);
    (CLK *> CAS_OUT_DIN_A) = (100:100:100, 100:100:100);
    (CLK *> CAS_OUT_DIN_B) = (100:100:100, 100:100:100);
    (CLK *> CAS_OUT_DOUT_A) = (100:100:100, 100:100:100);
    (CLK *> CAS_OUT_DOUT_B) = (100:100:100, 100:100:100);
    (CLK *> DOUT_A) = (100:100:100, 100:100:100);
    (CLK *> DOUT_B) = (100:100:100, 100:100:100);
    (CLK => CAS_OUT_DBITERR_A) = (100:100:100, 100:100:100);
    (CLK => CAS_OUT_DBITERR_B) = (100:100:100, 100:100:100);
    (CLK => CAS_OUT_EN_A) = (100:100:100, 100:100:100);
    (CLK => CAS_OUT_EN_B) = (100:100:100, 100:100:100);
    (CLK => CAS_OUT_RDACCESS_A) = (100:100:100, 100:100:100);
    (CLK => CAS_OUT_RDACCESS_B) = (100:100:100, 100:100:100);
    (CLK => CAS_OUT_RDB_WR_A) = (100:100:100, 100:100:100);
    (CLK => CAS_OUT_RDB_WR_B) = (100:100:100, 100:100:100);
    (CLK => CAS_OUT_SBITERR_A) = (100:100:100, 100:100:100);
    (CLK => CAS_OUT_SBITERR_B) = (100:100:100, 100:100:100);
    (CLK => DBITERR_A) = (100:100:100, 100:100:100);
    (CLK => DBITERR_B) = (100:100:100, 100:100:100);
    (CLK => RDACCESS_A) = (100:100:100, 100:100:100);
    (CLK => RDACCESS_B) = (100:100:100, 100:100:100);
    (CLK => SBITERR_A) = (100:100:100, 100:100:100);
    (CLK => SBITERR_B) = (100:100:100, 100:100:100);
    (DIN_A *> CAS_OUT_DIN_A) = (0:0:0, 0:0:0);
    (DIN_B *> CAS_OUT_DIN_B) = (0:0:0, 0:0:0);
    (EN_A => CAS_OUT_EN_A) = (0:0:0, 0:0:0);
    (EN_B => CAS_OUT_EN_B) = (0:0:0, 0:0:0);
    (RDB_WR_A => CAS_OUT_RDB_WR_A) = (0:0:0, 0:0:0);
    (RDB_WR_B => CAS_OUT_RDB_WR_B) = (0:0:0, 0:0:0);
    (negedge RST_A *> (CAS_OUT_DOUT_A +: 0)) = (100:100:100, 100:100:100);
    (negedge RST_A *> (DOUT_A +: 0)) = (100:100:100, 100:100:100);
    (negedge RST_A => (CAS_OUT_DBITERR_A +: 0)) = (100:100:100, 100:100:100);
    (negedge RST_A => (CAS_OUT_RDACCESS_A +: 0)) = (100:100:100, 100:100:100);
    (negedge RST_A => (CAS_OUT_SBITERR_A +: 0)) = (100:100:100, 100:100:100);
    (negedge RST_A => (DBITERR_A +: 0)) = (100:100:100, 100:100:100);
    (negedge RST_A => (RDACCESS_A +: 0)) = (100:100:100, 100:100:100);
    (negedge RST_A => (SBITERR_A +: 0)) = (100:100:100, 100:100:100);
    (negedge RST_B *> (CAS_OUT_DOUT_B +: 0)) = (100:100:100, 100:100:100);
    (negedge RST_B *> (DOUT_B +: 0)) = (100:100:100, 100:100:100);
    (negedge RST_B => (CAS_OUT_DBITERR_B +: 0)) = (100:100:100, 100:100:100);
    (negedge RST_B => (CAS_OUT_RDACCESS_B +: 0)) = (100:100:100, 100:100:100);
    (negedge RST_B => (CAS_OUT_SBITERR_B +: 0)) = (100:100:100, 100:100:100);
    (negedge RST_B => (DBITERR_B +: 0)) = (100:100:100, 100:100:100);
    (negedge RST_B => (RDACCESS_B +: 0)) = (100:100:100, 100:100:100);
    (negedge RST_B => (SBITERR_B +: 0)) = (100:100:100, 100:100:100);
    (posedge RST_A *> (CAS_OUT_DOUT_A +: 0)) = (100:100:100, 100:100:100);
    (posedge RST_A *> (DOUT_A +: 0)) = (100:100:100, 100:100:100);
    (posedge RST_A => (CAS_OUT_DBITERR_A +: 0)) = (100:100:100, 100:100:100);
    (posedge RST_A => (CAS_OUT_RDACCESS_A +: 0)) = (100:100:100, 100:100:100);
    (posedge RST_A => (CAS_OUT_SBITERR_A +: 0)) = (100:100:100, 100:100:100);
    (posedge RST_A => (DBITERR_A +: 0)) = (100:100:100, 100:100:100);
    (posedge RST_A => (RDACCESS_A +: 0)) = (100:100:100, 100:100:100);
    (posedge RST_A => (SBITERR_A +: 0)) = (100:100:100, 100:100:100);
    (posedge RST_B *> (CAS_OUT_DOUT_B +: 0)) = (100:100:100, 100:100:100);
    (posedge RST_B *> (DOUT_B +: 0)) = (100:100:100, 100:100:100);
    (posedge RST_B => (CAS_OUT_DBITERR_B +: 0)) = (100:100:100, 100:100:100);
    (posedge RST_B => (CAS_OUT_RDACCESS_B +: 0)) = (100:100:100, 100:100:100);
    (posedge RST_B => (CAS_OUT_SBITERR_B +: 0)) = (100:100:100, 100:100:100);
    (posedge RST_B => (DBITERR_B +: 0)) = (100:100:100, 100:100:100);
    (posedge RST_B => (RDACCESS_B +: 0)) = (100:100:100, 100:100:100);
    (posedge RST_B => (SBITERR_B +: 0)) = (100:100:100, 100:100:100);
`ifdef XIL_TIMING
    $period (negedge CLK, 0:0:0, notifier);
    $period (posedge CLK, 0:0:0, notifier);
    $recrem (negedge RST_A, negedge CLK, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, RST_A_delay, CLK_delay);
    $recrem (negedge RST_A, posedge CLK, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, RST_A_delay, CLK_delay);
    $recrem (negedge RST_B, negedge CLK, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, RST_B_delay, CLK_delay);
    $recrem (negedge RST_B, posedge CLK, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, RST_B_delay, CLK_delay);
    $recrem (posedge RST_A, negedge CLK, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, RST_A_delay, CLK_delay);
    $recrem (posedge RST_A, posedge CLK, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, RST_A_delay, CLK_delay);
    $recrem (posedge RST_B, negedge CLK, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, RST_B_delay, CLK_delay);
    $recrem (posedge RST_B, posedge CLK, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, RST_B_delay, CLK_delay);
    $setuphold (negedge CLK, negedge ADDR_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, ADDR_A_delay);
    $setuphold (negedge CLK, negedge ADDR_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, ADDR_B_delay);
    $setuphold (negedge CLK, negedge BWE_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, BWE_A_delay);
    $setuphold (negedge CLK, negedge BWE_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, BWE_B_delay);
    $setuphold (negedge CLK, negedge CAS_IN_ADDR_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_ADDR_A_delay);
    $setuphold (negedge CLK, negedge CAS_IN_ADDR_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_ADDR_B_delay);
    $setuphold (negedge CLK, negedge CAS_IN_BWE_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_BWE_A_delay);
    $setuphold (negedge CLK, negedge CAS_IN_BWE_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_BWE_B_delay);
    $setuphold (negedge CLK, negedge CAS_IN_DBITERR_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_DBITERR_A_delay);
    $setuphold (negedge CLK, negedge CAS_IN_DBITERR_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_DBITERR_B_delay);
    $setuphold (negedge CLK, negedge CAS_IN_DIN_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_DIN_A_delay);
    $setuphold (negedge CLK, negedge CAS_IN_DIN_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_DIN_B_delay);
    $setuphold (negedge CLK, negedge CAS_IN_DOUT_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_DOUT_A_delay);
    $setuphold (negedge CLK, negedge CAS_IN_DOUT_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_DOUT_B_delay);
    $setuphold (negedge CLK, negedge CAS_IN_EN_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_EN_A_delay);
    $setuphold (negedge CLK, negedge CAS_IN_EN_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_EN_B_delay);
    $setuphold (negedge CLK, negedge CAS_IN_RDACCESS_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_RDACCESS_A_delay);
    $setuphold (negedge CLK, negedge CAS_IN_RDACCESS_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_RDACCESS_B_delay);
    $setuphold (negedge CLK, negedge CAS_IN_RDB_WR_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_RDB_WR_A_delay);
    $setuphold (negedge CLK, negedge CAS_IN_RDB_WR_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_RDB_WR_B_delay);
    $setuphold (negedge CLK, negedge CAS_IN_SBITERR_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_SBITERR_A_delay);
    $setuphold (negedge CLK, negedge CAS_IN_SBITERR_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_SBITERR_B_delay);
    $setuphold (negedge CLK, negedge DIN_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, DIN_A_delay);
    $setuphold (negedge CLK, negedge DIN_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, DIN_B_delay);
    $setuphold (negedge CLK, negedge EN_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, EN_A_delay);
    $setuphold (negedge CLK, negedge EN_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, EN_B_delay);
    $setuphold (negedge CLK, negedge INJECT_DBITERR_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, INJECT_DBITERR_A_delay);
    $setuphold (negedge CLK, negedge INJECT_DBITERR_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, INJECT_DBITERR_B_delay);
    $setuphold (negedge CLK, negedge INJECT_SBITERR_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, INJECT_SBITERR_A_delay);
    $setuphold (negedge CLK, negedge INJECT_SBITERR_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, INJECT_SBITERR_B_delay);
    $setuphold (negedge CLK, negedge OREG_CE_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, OREG_CE_A_delay);
    $setuphold (negedge CLK, negedge OREG_CE_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, OREG_CE_B_delay);
    $setuphold (negedge CLK, negedge OREG_ECC_CE_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, OREG_ECC_CE_A_delay);
    $setuphold (negedge CLK, negedge OREG_ECC_CE_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, OREG_ECC_CE_B_delay);
    $setuphold (negedge CLK, negedge RDB_WR_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, RDB_WR_A_delay);
    $setuphold (negedge CLK, negedge RDB_WR_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, RDB_WR_B_delay);
    $setuphold (negedge CLK, negedge RST_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, RST_A_delay);
    $setuphold (negedge CLK, negedge RST_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, RST_B_delay);
    $setuphold (negedge CLK, negedge SLEEP, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, SLEEP_delay);
    $setuphold (negedge CLK, posedge ADDR_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, ADDR_A_delay);
    $setuphold (negedge CLK, posedge ADDR_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, ADDR_B_delay);
    $setuphold (negedge CLK, posedge BWE_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, BWE_A_delay);
    $setuphold (negedge CLK, posedge BWE_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, BWE_B_delay);
    $setuphold (negedge CLK, posedge CAS_IN_ADDR_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_ADDR_A_delay);
    $setuphold (negedge CLK, posedge CAS_IN_ADDR_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_ADDR_B_delay);
    $setuphold (negedge CLK, posedge CAS_IN_BWE_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_BWE_A_delay);
    $setuphold (negedge CLK, posedge CAS_IN_BWE_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_BWE_B_delay);
    $setuphold (negedge CLK, posedge CAS_IN_DBITERR_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_DBITERR_A_delay);
    $setuphold (negedge CLK, posedge CAS_IN_DBITERR_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_DBITERR_B_delay);
    $setuphold (negedge CLK, posedge CAS_IN_DIN_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_DIN_A_delay);
    $setuphold (negedge CLK, posedge CAS_IN_DIN_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_DIN_B_delay);
    $setuphold (negedge CLK, posedge CAS_IN_DOUT_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_DOUT_A_delay);
    $setuphold (negedge CLK, posedge CAS_IN_DOUT_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_DOUT_B_delay);
    $setuphold (negedge CLK, posedge CAS_IN_EN_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_EN_A_delay);
    $setuphold (negedge CLK, posedge CAS_IN_EN_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_EN_B_delay);
    $setuphold (negedge CLK, posedge CAS_IN_RDACCESS_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_RDACCESS_A_delay);
    $setuphold (negedge CLK, posedge CAS_IN_RDACCESS_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_RDACCESS_B_delay);
    $setuphold (negedge CLK, posedge CAS_IN_RDB_WR_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_RDB_WR_A_delay);
    $setuphold (negedge CLK, posedge CAS_IN_RDB_WR_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_RDB_WR_B_delay);
    $setuphold (negedge CLK, posedge CAS_IN_SBITERR_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_SBITERR_A_delay);
    $setuphold (negedge CLK, posedge CAS_IN_SBITERR_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CAS_IN_SBITERR_B_delay);
    $setuphold (negedge CLK, posedge DIN_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, DIN_A_delay);
    $setuphold (negedge CLK, posedge DIN_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, DIN_B_delay);
    $setuphold (negedge CLK, posedge EN_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, EN_A_delay);
    $setuphold (negedge CLK, posedge EN_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, EN_B_delay);
    $setuphold (negedge CLK, posedge INJECT_DBITERR_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, INJECT_DBITERR_A_delay);
    $setuphold (negedge CLK, posedge INJECT_DBITERR_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, INJECT_DBITERR_B_delay);
    $setuphold (negedge CLK, posedge INJECT_SBITERR_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, INJECT_SBITERR_A_delay);
    $setuphold (negedge CLK, posedge INJECT_SBITERR_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, INJECT_SBITERR_B_delay);
    $setuphold (negedge CLK, posedge OREG_CE_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, OREG_CE_A_delay);
    $setuphold (negedge CLK, posedge OREG_CE_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, OREG_CE_B_delay);
    $setuphold (negedge CLK, posedge OREG_ECC_CE_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, OREG_ECC_CE_A_delay);
    $setuphold (negedge CLK, posedge OREG_ECC_CE_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, OREG_ECC_CE_B_delay);
    $setuphold (negedge CLK, posedge RDB_WR_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, RDB_WR_A_delay);
    $setuphold (negedge CLK, posedge RDB_WR_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, RDB_WR_B_delay);
    $setuphold (negedge CLK, posedge RST_A, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, RST_A_delay);
    $setuphold (negedge CLK, posedge RST_B, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, RST_B_delay);
    $setuphold (negedge CLK, posedge SLEEP, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, SLEEP_delay);
    $setuphold (posedge CLK, negedge ADDR_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, ADDR_A_delay);
    $setuphold (posedge CLK, negedge ADDR_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, ADDR_B_delay);
    $setuphold (posedge CLK, negedge BWE_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, BWE_A_delay);
    $setuphold (posedge CLK, negedge BWE_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, BWE_B_delay);
    $setuphold (posedge CLK, negedge CAS_IN_ADDR_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_ADDR_A_delay);
    $setuphold (posedge CLK, negedge CAS_IN_ADDR_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_ADDR_B_delay);
    $setuphold (posedge CLK, negedge CAS_IN_BWE_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_BWE_A_delay);
    $setuphold (posedge CLK, negedge CAS_IN_BWE_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_BWE_B_delay);
    $setuphold (posedge CLK, negedge CAS_IN_DBITERR_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_DBITERR_A_delay);
    $setuphold (posedge CLK, negedge CAS_IN_DBITERR_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_DBITERR_B_delay);
    $setuphold (posedge CLK, negedge CAS_IN_DIN_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_DIN_A_delay);
    $setuphold (posedge CLK, negedge CAS_IN_DIN_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_DIN_B_delay);
    $setuphold (posedge CLK, negedge CAS_IN_DOUT_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_DOUT_A_delay);
    $setuphold (posedge CLK, negedge CAS_IN_DOUT_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_DOUT_B_delay);
    $setuphold (posedge CLK, negedge CAS_IN_EN_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_EN_A_delay);
    $setuphold (posedge CLK, negedge CAS_IN_EN_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_EN_B_delay);
    $setuphold (posedge CLK, negedge CAS_IN_RDACCESS_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_RDACCESS_A_delay);
    $setuphold (posedge CLK, negedge CAS_IN_RDACCESS_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_RDACCESS_B_delay);
    $setuphold (posedge CLK, negedge CAS_IN_RDB_WR_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_RDB_WR_A_delay);
    $setuphold (posedge CLK, negedge CAS_IN_RDB_WR_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_RDB_WR_B_delay);
    $setuphold (posedge CLK, negedge CAS_IN_SBITERR_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_SBITERR_A_delay);
    $setuphold (posedge CLK, negedge CAS_IN_SBITERR_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_SBITERR_B_delay);
    $setuphold (posedge CLK, negedge DIN_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, DIN_A_delay);
    $setuphold (posedge CLK, negedge DIN_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, DIN_B_delay);
    $setuphold (posedge CLK, negedge EN_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, EN_A_delay);
    $setuphold (posedge CLK, negedge EN_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, EN_B_delay);
    $setuphold (posedge CLK, negedge INJECT_DBITERR_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, INJECT_DBITERR_A_delay);
    $setuphold (posedge CLK, negedge INJECT_DBITERR_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, INJECT_DBITERR_B_delay);
    $setuphold (posedge CLK, negedge INJECT_SBITERR_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, INJECT_SBITERR_A_delay);
    $setuphold (posedge CLK, negedge INJECT_SBITERR_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, INJECT_SBITERR_B_delay);
    $setuphold (posedge CLK, negedge OREG_CE_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, OREG_CE_A_delay);
    $setuphold (posedge CLK, negedge OREG_CE_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, OREG_CE_B_delay);
    $setuphold (posedge CLK, negedge OREG_ECC_CE_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, OREG_ECC_CE_A_delay);
    $setuphold (posedge CLK, negedge OREG_ECC_CE_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, OREG_ECC_CE_B_delay);
    $setuphold (posedge CLK, negedge RDB_WR_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, RDB_WR_A_delay);
    $setuphold (posedge CLK, negedge RDB_WR_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, RDB_WR_B_delay);
    $setuphold (posedge CLK, negedge RST_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, RST_A_delay);
    $setuphold (posedge CLK, negedge RST_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, RST_B_delay);
    $setuphold (posedge CLK, negedge SLEEP, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, SLEEP_delay);
    $setuphold (posedge CLK, posedge ADDR_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, ADDR_A_delay);
    $setuphold (posedge CLK, posedge ADDR_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, ADDR_B_delay);
    $setuphold (posedge CLK, posedge BWE_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, BWE_A_delay);
    $setuphold (posedge CLK, posedge BWE_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, BWE_B_delay);
    $setuphold (posedge CLK, posedge CAS_IN_ADDR_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_ADDR_A_delay);
    $setuphold (posedge CLK, posedge CAS_IN_ADDR_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_ADDR_B_delay);
    $setuphold (posedge CLK, posedge CAS_IN_BWE_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_BWE_A_delay);
    $setuphold (posedge CLK, posedge CAS_IN_BWE_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_BWE_B_delay);
    $setuphold (posedge CLK, posedge CAS_IN_DBITERR_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_DBITERR_A_delay);
    $setuphold (posedge CLK, posedge CAS_IN_DBITERR_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_DBITERR_B_delay);
    $setuphold (posedge CLK, posedge CAS_IN_DIN_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_DIN_A_delay);
    $setuphold (posedge CLK, posedge CAS_IN_DIN_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_DIN_B_delay);
    $setuphold (posedge CLK, posedge CAS_IN_DOUT_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_DOUT_A_delay);
    $setuphold (posedge CLK, posedge CAS_IN_DOUT_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_DOUT_B_delay);
    $setuphold (posedge CLK, posedge CAS_IN_EN_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_EN_A_delay);
    $setuphold (posedge CLK, posedge CAS_IN_EN_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_EN_B_delay);
    $setuphold (posedge CLK, posedge CAS_IN_RDACCESS_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_RDACCESS_A_delay);
    $setuphold (posedge CLK, posedge CAS_IN_RDACCESS_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_RDACCESS_B_delay);
    $setuphold (posedge CLK, posedge CAS_IN_RDB_WR_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_RDB_WR_A_delay);
    $setuphold (posedge CLK, posedge CAS_IN_RDB_WR_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_RDB_WR_B_delay);
    $setuphold (posedge CLK, posedge CAS_IN_SBITERR_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_SBITERR_A_delay);
    $setuphold (posedge CLK, posedge CAS_IN_SBITERR_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CAS_IN_SBITERR_B_delay);
    $setuphold (posedge CLK, posedge DIN_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, DIN_A_delay);
    $setuphold (posedge CLK, posedge DIN_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, DIN_B_delay);
    $setuphold (posedge CLK, posedge EN_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, EN_A_delay);
    $setuphold (posedge CLK, posedge EN_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, EN_B_delay);
    $setuphold (posedge CLK, posedge INJECT_DBITERR_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, INJECT_DBITERR_A_delay);
    $setuphold (posedge CLK, posedge INJECT_DBITERR_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, INJECT_DBITERR_B_delay);
    $setuphold (posedge CLK, posedge INJECT_SBITERR_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, INJECT_SBITERR_A_delay);
    $setuphold (posedge CLK, posedge INJECT_SBITERR_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, INJECT_SBITERR_B_delay);
    $setuphold (posedge CLK, posedge OREG_CE_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, OREG_CE_A_delay);
    $setuphold (posedge CLK, posedge OREG_CE_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, OREG_CE_B_delay);
    $setuphold (posedge CLK, posedge OREG_ECC_CE_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, OREG_ECC_CE_A_delay);
    $setuphold (posedge CLK, posedge OREG_ECC_CE_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, OREG_ECC_CE_B_delay);
    $setuphold (posedge CLK, posedge RDB_WR_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, RDB_WR_A_delay);
    $setuphold (posedge CLK, posedge RDB_WR_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, RDB_WR_B_delay);
    $setuphold (posedge CLK, posedge RST_A, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, RST_A_delay);
    $setuphold (posedge CLK, posedge RST_B, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, RST_B_delay);
    $setuphold (posedge CLK, posedge SLEEP, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, SLEEP_delay);
    $width (negedge CLK, 0:0:0, 0, notifier);
    $width (negedge RST_A, 0:0:0, 0, notifier);
    $width (negedge RST_B, 0:0:0, 0, notifier);
    $width (posedge CLK, 0:0:0, 0, notifier);
    $width (posedge RST_A, 0:0:0, 0, notifier);
    $width (posedge RST_B, 0:0:0, 0, notifier);
`endif
    specparam PATHPULSE$ = 0;
  endspecify
`endif
endmodule

`endcelldefine
