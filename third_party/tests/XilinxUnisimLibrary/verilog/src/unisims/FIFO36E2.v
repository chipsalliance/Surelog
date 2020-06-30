///////////////////////////////////////////////////////////////////////////////
//     Copyright (c) 1995/2014 Xilinx, Inc.
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
// \   \   \/      Version     : 2014.3
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        36Kb FIFO (First-In-First-Out) Block RAM Memory
// /___/   /\      Filename    : FIFO36E2.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//  11/30/2012 - intial
//  12/12/2012 - yaml update, 691724 and 691715
//  02/07/2013 - 699628 - correction to DO_PIPELINED mode
//  02/28/2013 - update to keep in sync with RAMB models
//  03/18/2013 - 707083 reads should clear FULL when RD & WR in CDC.
//  03/22/2013 - sync5 yaml update, port ordering, *RSTBUSY
//  03/25/2013 - 707652 - RST = 1 n enters RST sequence but does not hold it there.
//  03/25/2013 - 707719 - Add sync5 cascade feature
//  03/27/2013 - 708820 - FULL flag deassert during WREN ind clocks.
//    10/22/14 - Added #1 to $finish (CR 808642).
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps

`celldefine

module FIFO36E2 #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter CASCADE_ORDER = "NONE",
  parameter CLOCK_DOMAINS = "INDEPENDENT",
  parameter EN_ECC_PIPE = "FALSE",
  parameter EN_ECC_READ = "FALSE",
  parameter EN_ECC_WRITE = "FALSE",
  parameter FIRST_WORD_FALL_THROUGH = "FALSE",
  parameter [71:0] INIT = 72'h000000000000000000,
  parameter [0:0] IS_RDCLK_INVERTED = 1'b0,
  parameter [0:0] IS_RDEN_INVERTED = 1'b0,
  parameter [0:0] IS_RSTREG_INVERTED = 1'b0,
  parameter [0:0] IS_RST_INVERTED = 1'b0,
  parameter [0:0] IS_WRCLK_INVERTED = 1'b0,
  parameter [0:0] IS_WREN_INVERTED = 1'b0,
  parameter integer PROG_EMPTY_THRESH = 256,
  parameter integer PROG_FULL_THRESH = 256,
  parameter RDCOUNT_TYPE = "RAW_PNTR",
  parameter integer READ_WIDTH = 4,
  parameter REGISTER_MODE = "UNREGISTERED",
  parameter RSTREG_PRIORITY = "RSTREG",
  parameter SLEEP_ASYNC = "FALSE",
  parameter [71:0] SRVAL = 72'h000000000000000000,
  parameter WRCOUNT_TYPE = "RAW_PNTR",
  parameter integer WRITE_WIDTH = 4
)(
  output [63:0] CASDOUT,
  output [7:0] CASDOUTP,
  output CASNXTEMPTY,
  output CASPRVRDEN,
  output DBITERR,
  output [63:0] DOUT,
  output [7:0] DOUTP,
  output [7:0] ECCPARITY,
  output EMPTY,
  output FULL,
  output PROGEMPTY,
  output PROGFULL,
  output [13:0] RDCOUNT,
  output RDERR,
  output RDRSTBUSY,
  output SBITERR,
  output [13:0] WRCOUNT,
  output WRERR,
  output WRRSTBUSY,

  input [63:0] CASDIN,
  input [7:0] CASDINP,
  input CASDOMUX,
  input CASDOMUXEN,
  input CASNXTRDEN,
  input CASOREGIMUX,
  input CASOREGIMUXEN,
  input CASPRVEMPTY,
  input [63:0] DIN,
  input [7:0] DINP,
  input INJECTDBITERR,
  input INJECTSBITERR,
  input RDCLK,
  input RDEN,
  input REGCE,
  input RST,
  input RSTREG,
  input SLEEP,
  input WRCLK,
  input WREN
);
  
// define constants
  localparam MODULE_NAME = "FIFO36E2";

// Parameter encodings and registers
  localparam CASCADE_ORDER_FIRST = 1;
  localparam CASCADE_ORDER_LAST = 2;
  localparam CASCADE_ORDER_MIDDLE = 3;
  localparam CASCADE_ORDER_NONE = 0;
  localparam CASCADE_ORDER_PARALLEL = 4;
  localparam CLOCK_DOMAINS_COMMON = 1;
  localparam CLOCK_DOMAINS_INDEPENDENT = 0;
  localparam EN_ECC_PIPE_FALSE = 0;
  localparam EN_ECC_PIPE_TRUE = 1;
  localparam EN_ECC_READ_FALSE = 0;
  localparam EN_ECC_READ_TRUE = 1;
  localparam EN_ECC_WRITE_FALSE = 0;
  localparam EN_ECC_WRITE_TRUE = 1;
  localparam FIRST_WORD_FALL_THROUGH_FALSE = 0;
  localparam FIRST_WORD_FALL_THROUGH_TRUE = 1;
  localparam RDCOUNT_TYPE_EXTENDED_DATACOUNT = 1;
  localparam RDCOUNT_TYPE_RAW_PNTR = 0;
  localparam RDCOUNT_TYPE_SIMPLE_DATACOUNT = 2;
  localparam RDCOUNT_TYPE_SYNC_PNTR = 3;
  localparam READ_WIDTH_18 = 16;
  localparam READ_WIDTH_36 = 32;
  localparam READ_WIDTH_4 = 4;
  localparam READ_WIDTH_72 = 64;
  localparam READ_WIDTH_9 = 8;
  localparam REGISTER_MODE_DO_PIPELINED = 1;
  localparam REGISTER_MODE_REGISTERED = 2;
  localparam REGISTER_MODE_UNREGISTERED = 0;
  localparam RSTREG_PRIORITY_REGCE = 1;
  localparam RSTREG_PRIORITY_RSTREG = 0;
  localparam SLEEP_ASYNC_FALSE = 0;
  localparam SLEEP_ASYNC_TRUE = 1;
  localparam WRCOUNT_TYPE_EXTENDED_DATACOUNT = 1;
  localparam WRCOUNT_TYPE_RAW_PNTR = 0;
  localparam WRCOUNT_TYPE_SIMPLE_DATACOUNT = 2;
  localparam WRCOUNT_TYPE_SYNC_PNTR = 3;
  localparam WRITE_WIDTH_18 = 16;
  localparam WRITE_WIDTH_36 = 32;
  localparam WRITE_WIDTH_4 = 4;
  localparam WRITE_WIDTH_72 = 64;
  localparam WRITE_WIDTH_9 = 8;

// include dynamic registers - XILINX test only
  reg trig_attr = 1'b0;
`ifdef XIL_DR
  `include "FIFO36E2_dr.v"
`else
  localparam [64:1] CASCADE_ORDER_REG = CASCADE_ORDER;
  localparam [88:1] CLOCK_DOMAINS_REG = CLOCK_DOMAINS;
  localparam [40:1] EN_ECC_PIPE_REG = EN_ECC_PIPE;
  localparam [40:1] EN_ECC_READ_REG = EN_ECC_READ;
  localparam [40:1] EN_ECC_WRITE_REG = EN_ECC_WRITE;
  localparam [40:1] FIRST_WORD_FALL_THROUGH_REG = FIRST_WORD_FALL_THROUGH;
  localparam [71:0] INIT_REG = INIT;
  localparam [0:0] IS_RDCLK_INVERTED_REG = IS_RDCLK_INVERTED;
  localparam [0:0] IS_RDEN_INVERTED_REG = IS_RDEN_INVERTED;
  localparam [0:0] IS_RSTREG_INVERTED_REG = IS_RSTREG_INVERTED;
  localparam [0:0] IS_RST_INVERTED_REG = IS_RST_INVERTED;
  localparam [0:0] IS_WRCLK_INVERTED_REG = IS_WRCLK_INVERTED;
  localparam [0:0] IS_WREN_INVERTED_REG = IS_WREN_INVERTED;
  localparam [12:0] PROG_EMPTY_THRESH_REG = PROG_EMPTY_THRESH;
  localparam [12:0] PROG_FULL_THRESH_REG = PROG_FULL_THRESH;
  localparam [144:1] RDCOUNT_TYPE_REG = RDCOUNT_TYPE;
  localparam [6:0] READ_WIDTH_REG = READ_WIDTH;
  localparam [96:1] REGISTER_MODE_REG = REGISTER_MODE;
  localparam [48:1] RSTREG_PRIORITY_REG = RSTREG_PRIORITY;
  localparam [40:1] SLEEP_ASYNC_REG = SLEEP_ASYNC;
  localparam [71:0] SRVAL_REG = SRVAL;
  localparam [144:1] WRCOUNT_TYPE_REG = WRCOUNT_TYPE;
  localparam [6:0] WRITE_WIDTH_REG = WRITE_WIDTH;
`endif

  wire [2:0] CASCADE_ORDER_BIN;
  wire CLOCK_DOMAINS_BIN;
  wire EN_ECC_PIPE_BIN;
  wire EN_ECC_READ_BIN;
  wire EN_ECC_WRITE_BIN;
  wire FIRST_WORD_FALL_THROUGH_BIN;
  wire [71:0] INIT_BIN;
  wire IS_RDCLK_INVERTED_BIN;
  wire IS_RDEN_INVERTED_BIN;
  wire IS_RSTREG_INVERTED_BIN;
  wire IS_RST_INVERTED_BIN;
  wire IS_WRCLK_INVERTED_BIN;
  wire IS_WREN_INVERTED_BIN;
  wire [12:0] PROG_EMPTY_THRESH_BIN;
  wire [12:0] PROG_FULL_THRESH_BIN;
  wire [1:0] RDCOUNT_TYPE_BIN;
  wire [6:0] READ_WIDTH_BIN;
  wire [1:0] REGISTER_MODE_BIN;
  wire RSTREG_PRIORITY_BIN;
  wire SLEEP_ASYNC_BIN;
  wire [71:0] SRVAL_BIN;
  wire [1:0] WRCOUNT_TYPE_BIN;
  wire [6:0] WRITE_WIDTH_BIN;
  reg INIT_MEM = 0;

`ifdef XIL_ATTR_TEST
  reg attr_test = 1'b1;
`else
  reg attr_test = 1'b0;
`endif
  reg attr_err = 1'b0;
  tri0 glblGSR = glbl.GSR || INIT_MEM;

  wire CASNXTEMPTY_out;
  wire CASPRVRDEN_out;
  wire DBITERR_out;
  wire EMPTY_out;
  wire FULL_out;
  wire PROGEMPTY_out;
  wire PROGFULL_out;
  wire RDERR_out;
  wire RDRSTBUSY_out;
  wire SBITERR_out;
  wire WRERR_out;
  wire WRRSTBUSY_out;
  wire [13:0] RDCOUNT_out;
  wire [13:0] WRCOUNT_out;
  wire [63:0] CASDOUT_out;
  reg [63:0] DOUT_out;
  wire [7:0] CASDOUTP_out;
  reg [7:0] DOUTP_out;
  wire [7:0] ECCPARITY_out;

  wire CASDOMUXEN_in;
  wire CASDOMUX_in;
  wire CASNXTRDEN_in;
  wire CASOREGIMUXEN_in;
  wire CASOREGIMUX_in;
  wire CASPRVEMPTY_in;
  wire INJECTDBITERR_in;
  wire INJECTSBITERR_in;
  wire RDCLK_in;
  wire RDEN_in;
  wire REGCE_in;
  wire RSTREG_in;
  wire RST_in;
  wire RST_in_pulse;
  
  wire SLEEP_in;
  wire WRCLK_in;
  wire WREN_in;
  wire [63:0] CASDIN_in;
  reg [63:0] DIN_in;
  wire [7:0] CASDINP_in;
  reg [7:0] DINP_in;

`ifdef XIL_TIMING
  wire CASDOMUXEN_delay;
  wire CASDOMUX_delay;
  wire CASNXTRDEN_delay;
  wire CASOREGIMUXEN_delay;
  wire CASOREGIMUX_delay;
  wire CASPRVEMPTY_delay;
  wire INJECTDBITERR_delay;
  wire INJECTSBITERR_delay;
  wire RDCLK_delay;
  wire RDEN_delay;
  wire REGCE_delay;
  wire RSTREG_delay;
  wire RST_delay;
  wire SLEEP_delay;
  wire WRCLK_delay;
  wire WREN_delay;
  wire [63:0] CASDIN_delay;
  wire [63:0] DIN_delay;
  wire [7:0] CASDINP_delay;
  wire [7:0] DINP_delay;
`endif

  assign CASDOUT = CASDOUT_out;
  assign CASDOUTP = CASDOUTP_out;
  assign CASNXTEMPTY = CASNXTEMPTY_out;
  assign CASPRVRDEN = CASPRVRDEN_out;
  assign DBITERR = DBITERR_out;
  assign DOUT = DOUT_out;
  assign DOUTP = DOUTP_out;
  assign ECCPARITY = ECCPARITY_out;
  assign EMPTY = EMPTY_out;
  assign FULL = FULL_out;
  assign PROGEMPTY = PROGEMPTY_out;
  assign PROGFULL = PROGFULL_out;
  assign RDCOUNT = RDCOUNT_out;
  assign RDERR = RDERR_out;
  assign RDRSTBUSY = RDRSTBUSY_out;
  assign SBITERR = SBITERR_out;
  assign WRCOUNT = WRCOUNT_out;
  assign WRERR = WRERR_out;
  assign WRRSTBUSY = WRRSTBUSY_out;

`ifdef XIL_TIMING
  assign CASDINP_in[0] = (CASDINP[0] !== 1'bz) && CASDINP_delay[0]; // rv 0
  assign CASDINP_in[1] = (CASDINP[1] !== 1'bz) && CASDINP_delay[1]; // rv 0
  assign CASDINP_in[2] = (CASDINP[2] !== 1'bz) && CASDINP_delay[2]; // rv 0
  assign CASDINP_in[3] = (CASDINP[3] !== 1'bz) && CASDINP_delay[3]; // rv 0
  assign CASDINP_in[4] = (CASDINP[4] !== 1'bz) && CASDINP_delay[4]; // rv 0
  assign CASDINP_in[5] = (CASDINP[5] !== 1'bz) && CASDINP_delay[5]; // rv 0
  assign CASDINP_in[6] = (CASDINP[6] !== 1'bz) && CASDINP_delay[6]; // rv 0
  assign CASDINP_in[7] = (CASDINP[7] !== 1'bz) && CASDINP_delay[7]; // rv 0
  assign CASDIN_in[0] = (CASDIN[0] !== 1'bz) && CASDIN_delay[0]; // rv 0
  assign CASDIN_in[10] = (CASDIN[10] !== 1'bz) && CASDIN_delay[10]; // rv 0
  assign CASDIN_in[11] = (CASDIN[11] !== 1'bz) && CASDIN_delay[11]; // rv 0
  assign CASDIN_in[12] = (CASDIN[12] !== 1'bz) && CASDIN_delay[12]; // rv 0
  assign CASDIN_in[13] = (CASDIN[13] !== 1'bz) && CASDIN_delay[13]; // rv 0
  assign CASDIN_in[14] = (CASDIN[14] !== 1'bz) && CASDIN_delay[14]; // rv 0
  assign CASDIN_in[15] = (CASDIN[15] !== 1'bz) && CASDIN_delay[15]; // rv 0
  assign CASDIN_in[16] = (CASDIN[16] !== 1'bz) && CASDIN_delay[16]; // rv 0
  assign CASDIN_in[17] = (CASDIN[17] !== 1'bz) && CASDIN_delay[17]; // rv 0
  assign CASDIN_in[18] = (CASDIN[18] !== 1'bz) && CASDIN_delay[18]; // rv 0
  assign CASDIN_in[19] = (CASDIN[19] !== 1'bz) && CASDIN_delay[19]; // rv 0
  assign CASDIN_in[1] = (CASDIN[1] !== 1'bz) && CASDIN_delay[1]; // rv 0
  assign CASDIN_in[20] = (CASDIN[20] !== 1'bz) && CASDIN_delay[20]; // rv 0
  assign CASDIN_in[21] = (CASDIN[21] !== 1'bz) && CASDIN_delay[21]; // rv 0
  assign CASDIN_in[22] = (CASDIN[22] !== 1'bz) && CASDIN_delay[22]; // rv 0
  assign CASDIN_in[23] = (CASDIN[23] !== 1'bz) && CASDIN_delay[23]; // rv 0
  assign CASDIN_in[24] = (CASDIN[24] !== 1'bz) && CASDIN_delay[24]; // rv 0
  assign CASDIN_in[25] = (CASDIN[25] !== 1'bz) && CASDIN_delay[25]; // rv 0
  assign CASDIN_in[26] = (CASDIN[26] !== 1'bz) && CASDIN_delay[26]; // rv 0
  assign CASDIN_in[27] = (CASDIN[27] !== 1'bz) && CASDIN_delay[27]; // rv 0
  assign CASDIN_in[28] = (CASDIN[28] !== 1'bz) && CASDIN_delay[28]; // rv 0
  assign CASDIN_in[29] = (CASDIN[29] !== 1'bz) && CASDIN_delay[29]; // rv 0
  assign CASDIN_in[2] = (CASDIN[2] !== 1'bz) && CASDIN_delay[2]; // rv 0
  assign CASDIN_in[30] = (CASDIN[30] !== 1'bz) && CASDIN_delay[30]; // rv 0
  assign CASDIN_in[31] = (CASDIN[31] !== 1'bz) && CASDIN_delay[31]; // rv 0
  assign CASDIN_in[32] = (CASDIN[32] !== 1'bz) && CASDIN_delay[32]; // rv 0
  assign CASDIN_in[33] = (CASDIN[33] !== 1'bz) && CASDIN_delay[33]; // rv 0
  assign CASDIN_in[34] = (CASDIN[34] !== 1'bz) && CASDIN_delay[34]; // rv 0
  assign CASDIN_in[35] = (CASDIN[35] !== 1'bz) && CASDIN_delay[35]; // rv 0
  assign CASDIN_in[36] = (CASDIN[36] !== 1'bz) && CASDIN_delay[36]; // rv 0
  assign CASDIN_in[37] = (CASDIN[37] !== 1'bz) && CASDIN_delay[37]; // rv 0
  assign CASDIN_in[38] = (CASDIN[38] !== 1'bz) && CASDIN_delay[38]; // rv 0
  assign CASDIN_in[39] = (CASDIN[39] !== 1'bz) && CASDIN_delay[39]; // rv 0
  assign CASDIN_in[3] = (CASDIN[3] !== 1'bz) && CASDIN_delay[3]; // rv 0
  assign CASDIN_in[40] = (CASDIN[40] !== 1'bz) && CASDIN_delay[40]; // rv 0
  assign CASDIN_in[41] = (CASDIN[41] !== 1'bz) && CASDIN_delay[41]; // rv 0
  assign CASDIN_in[42] = (CASDIN[42] !== 1'bz) && CASDIN_delay[42]; // rv 0
  assign CASDIN_in[43] = (CASDIN[43] !== 1'bz) && CASDIN_delay[43]; // rv 0
  assign CASDIN_in[44] = (CASDIN[44] !== 1'bz) && CASDIN_delay[44]; // rv 0
  assign CASDIN_in[45] = (CASDIN[45] !== 1'bz) && CASDIN_delay[45]; // rv 0
  assign CASDIN_in[46] = (CASDIN[46] !== 1'bz) && CASDIN_delay[46]; // rv 0
  assign CASDIN_in[47] = (CASDIN[47] !== 1'bz) && CASDIN_delay[47]; // rv 0
  assign CASDIN_in[48] = (CASDIN[48] !== 1'bz) && CASDIN_delay[48]; // rv 0
  assign CASDIN_in[49] = (CASDIN[49] !== 1'bz) && CASDIN_delay[49]; // rv 0
  assign CASDIN_in[4] = (CASDIN[4] !== 1'bz) && CASDIN_delay[4]; // rv 0
  assign CASDIN_in[50] = (CASDIN[50] !== 1'bz) && CASDIN_delay[50]; // rv 0
  assign CASDIN_in[51] = (CASDIN[51] !== 1'bz) && CASDIN_delay[51]; // rv 0
  assign CASDIN_in[52] = (CASDIN[52] !== 1'bz) && CASDIN_delay[52]; // rv 0
  assign CASDIN_in[53] = (CASDIN[53] !== 1'bz) && CASDIN_delay[53]; // rv 0
  assign CASDIN_in[54] = (CASDIN[54] !== 1'bz) && CASDIN_delay[54]; // rv 0
  assign CASDIN_in[55] = (CASDIN[55] !== 1'bz) && CASDIN_delay[55]; // rv 0
  assign CASDIN_in[56] = (CASDIN[56] !== 1'bz) && CASDIN_delay[56]; // rv 0
  assign CASDIN_in[57] = (CASDIN[57] !== 1'bz) && CASDIN_delay[57]; // rv 0
  assign CASDIN_in[58] = (CASDIN[58] !== 1'bz) && CASDIN_delay[58]; // rv 0
  assign CASDIN_in[59] = (CASDIN[59] !== 1'bz) && CASDIN_delay[59]; // rv 0
  assign CASDIN_in[5] = (CASDIN[5] !== 1'bz) && CASDIN_delay[5]; // rv 0
  assign CASDIN_in[60] = (CASDIN[60] !== 1'bz) && CASDIN_delay[60]; // rv 0
  assign CASDIN_in[61] = (CASDIN[61] !== 1'bz) && CASDIN_delay[61]; // rv 0
  assign CASDIN_in[62] = (CASDIN[62] !== 1'bz) && CASDIN_delay[62]; // rv 0
  assign CASDIN_in[63] = (CASDIN[63] !== 1'bz) && CASDIN_delay[63]; // rv 0
  assign CASDIN_in[6] = (CASDIN[6] !== 1'bz) && CASDIN_delay[6]; // rv 0
  assign CASDIN_in[7] = (CASDIN[7] !== 1'bz) && CASDIN_delay[7]; // rv 0
  assign CASDIN_in[8] = (CASDIN[8] !== 1'bz) && CASDIN_delay[8]; // rv 0
  assign CASDIN_in[9] = (CASDIN[9] !== 1'bz) && CASDIN_delay[9]; // rv 0
  assign CASDOMUXEN_in = (CASDOMUXEN === 1'bz) || CASDOMUXEN_delay; // rv 1
  assign CASDOMUX_in = (CASDOMUX !== 1'bz) && CASDOMUX_delay; // rv 0
  assign CASNXTRDEN_in = (CASNXTRDEN !== 1'bz) && CASNXTRDEN_delay; // rv 0
  assign CASOREGIMUXEN_in = (CASOREGIMUXEN === 1'bz) || CASOREGIMUXEN_delay; // rv 1
  assign CASOREGIMUX_in = (CASOREGIMUX !== 1'bz) && CASOREGIMUX_delay; // rv 0
  assign CASPRVEMPTY_in = (CASPRVEMPTY !== 1'bz) && CASPRVEMPTY_delay; // rv 0
  always @ (*) DINP_in = DINP_delay;
  always @ (*) DIN_in = DIN_delay;
  assign INJECTDBITERR_in = (INJECTDBITERR !== 1'bz) && INJECTDBITERR_delay; // rv 0
  assign INJECTSBITERR_in = (INJECTSBITERR !== 1'bz) && INJECTSBITERR_delay; // rv 0
  assign RDCLK_in = (RDCLK !== 1'bz) && (RDCLK_delay ^ IS_RDCLK_INVERTED_BIN); // rv 0
  assign RDEN_in = (RDEN !== 1'bz) && (RDEN_delay ^ IS_RDEN_INVERTED_BIN); // rv 0
  assign REGCE_in = (REGCE === 1'bz) || REGCE_delay; // rv 1
  assign RSTREG_in = (RSTREG !== 1'bz) && (RSTREG_delay ^ IS_RSTREG_INVERTED_BIN); // rv 0
  assign RST_in = (RST !== 1'bz) && (RST_delay ^ IS_RST_INVERTED_BIN); // rv 0
  assign SLEEP_in = (SLEEP !== 1'bz) && SLEEP_delay; // rv 0
  assign WRCLK_in = (WRCLK !== 1'bz) && (WRCLK_delay ^ IS_WRCLK_INVERTED_BIN); // rv 0
  assign WREN_in = (WREN !== 1'bz) && (WREN_delay ^ IS_WREN_INVERTED_BIN); // rv 0
`else
  assign CASDINP_in[0] = (CASDINP[0] !== 1'bz) && CASDINP[0]; // rv 0
  assign CASDINP_in[1] = (CASDINP[1] !== 1'bz) && CASDINP[1]; // rv 0
  assign CASDINP_in[2] = (CASDINP[2] !== 1'bz) && CASDINP[2]; // rv 0
  assign CASDINP_in[3] = (CASDINP[3] !== 1'bz) && CASDINP[3]; // rv 0
  assign CASDINP_in[4] = (CASDINP[4] !== 1'bz) && CASDINP[4]; // rv 0
  assign CASDINP_in[5] = (CASDINP[5] !== 1'bz) && CASDINP[5]; // rv 0
  assign CASDINP_in[6] = (CASDINP[6] !== 1'bz) && CASDINP[6]; // rv 0
  assign CASDINP_in[7] = (CASDINP[7] !== 1'bz) && CASDINP[7]; // rv 0
  assign CASDIN_in[0] = (CASDIN[0] !== 1'bz) && CASDIN[0]; // rv 0
  assign CASDIN_in[10] = (CASDIN[10] !== 1'bz) && CASDIN[10]; // rv 0
  assign CASDIN_in[11] = (CASDIN[11] !== 1'bz) && CASDIN[11]; // rv 0
  assign CASDIN_in[12] = (CASDIN[12] !== 1'bz) && CASDIN[12]; // rv 0
  assign CASDIN_in[13] = (CASDIN[13] !== 1'bz) && CASDIN[13]; // rv 0
  assign CASDIN_in[14] = (CASDIN[14] !== 1'bz) && CASDIN[14]; // rv 0
  assign CASDIN_in[15] = (CASDIN[15] !== 1'bz) && CASDIN[15]; // rv 0
  assign CASDIN_in[16] = (CASDIN[16] !== 1'bz) && CASDIN[16]; // rv 0
  assign CASDIN_in[17] = (CASDIN[17] !== 1'bz) && CASDIN[17]; // rv 0
  assign CASDIN_in[18] = (CASDIN[18] !== 1'bz) && CASDIN[18]; // rv 0
  assign CASDIN_in[19] = (CASDIN[19] !== 1'bz) && CASDIN[19]; // rv 0
  assign CASDIN_in[1] = (CASDIN[1] !== 1'bz) && CASDIN[1]; // rv 0
  assign CASDIN_in[20] = (CASDIN[20] !== 1'bz) && CASDIN[20]; // rv 0
  assign CASDIN_in[21] = (CASDIN[21] !== 1'bz) && CASDIN[21]; // rv 0
  assign CASDIN_in[22] = (CASDIN[22] !== 1'bz) && CASDIN[22]; // rv 0
  assign CASDIN_in[23] = (CASDIN[23] !== 1'bz) && CASDIN[23]; // rv 0
  assign CASDIN_in[24] = (CASDIN[24] !== 1'bz) && CASDIN[24]; // rv 0
  assign CASDIN_in[25] = (CASDIN[25] !== 1'bz) && CASDIN[25]; // rv 0
  assign CASDIN_in[26] = (CASDIN[26] !== 1'bz) && CASDIN[26]; // rv 0
  assign CASDIN_in[27] = (CASDIN[27] !== 1'bz) && CASDIN[27]; // rv 0
  assign CASDIN_in[28] = (CASDIN[28] !== 1'bz) && CASDIN[28]; // rv 0
  assign CASDIN_in[29] = (CASDIN[29] !== 1'bz) && CASDIN[29]; // rv 0
  assign CASDIN_in[2] = (CASDIN[2] !== 1'bz) && CASDIN[2]; // rv 0
  assign CASDIN_in[30] = (CASDIN[30] !== 1'bz) && CASDIN[30]; // rv 0
  assign CASDIN_in[31] = (CASDIN[31] !== 1'bz) && CASDIN[31]; // rv 0
  assign CASDIN_in[32] = (CASDIN[32] !== 1'bz) && CASDIN[32]; // rv 0
  assign CASDIN_in[33] = (CASDIN[33] !== 1'bz) && CASDIN[33]; // rv 0
  assign CASDIN_in[34] = (CASDIN[34] !== 1'bz) && CASDIN[34]; // rv 0
  assign CASDIN_in[35] = (CASDIN[35] !== 1'bz) && CASDIN[35]; // rv 0
  assign CASDIN_in[36] = (CASDIN[36] !== 1'bz) && CASDIN[36]; // rv 0
  assign CASDIN_in[37] = (CASDIN[37] !== 1'bz) && CASDIN[37]; // rv 0
  assign CASDIN_in[38] = (CASDIN[38] !== 1'bz) && CASDIN[38]; // rv 0
  assign CASDIN_in[39] = (CASDIN[39] !== 1'bz) && CASDIN[39]; // rv 0
  assign CASDIN_in[3] = (CASDIN[3] !== 1'bz) && CASDIN[3]; // rv 0
  assign CASDIN_in[40] = (CASDIN[40] !== 1'bz) && CASDIN[40]; // rv 0
  assign CASDIN_in[41] = (CASDIN[41] !== 1'bz) && CASDIN[41]; // rv 0
  assign CASDIN_in[42] = (CASDIN[42] !== 1'bz) && CASDIN[42]; // rv 0
  assign CASDIN_in[43] = (CASDIN[43] !== 1'bz) && CASDIN[43]; // rv 0
  assign CASDIN_in[44] = (CASDIN[44] !== 1'bz) && CASDIN[44]; // rv 0
  assign CASDIN_in[45] = (CASDIN[45] !== 1'bz) && CASDIN[45]; // rv 0
  assign CASDIN_in[46] = (CASDIN[46] !== 1'bz) && CASDIN[46]; // rv 0
  assign CASDIN_in[47] = (CASDIN[47] !== 1'bz) && CASDIN[47]; // rv 0
  assign CASDIN_in[48] = (CASDIN[48] !== 1'bz) && CASDIN[48]; // rv 0
  assign CASDIN_in[49] = (CASDIN[49] !== 1'bz) && CASDIN[49]; // rv 0
  assign CASDIN_in[4] = (CASDIN[4] !== 1'bz) && CASDIN[4]; // rv 0
  assign CASDIN_in[50] = (CASDIN[50] !== 1'bz) && CASDIN[50]; // rv 0
  assign CASDIN_in[51] = (CASDIN[51] !== 1'bz) && CASDIN[51]; // rv 0
  assign CASDIN_in[52] = (CASDIN[52] !== 1'bz) && CASDIN[52]; // rv 0
  assign CASDIN_in[53] = (CASDIN[53] !== 1'bz) && CASDIN[53]; // rv 0
  assign CASDIN_in[54] = (CASDIN[54] !== 1'bz) && CASDIN[54]; // rv 0
  assign CASDIN_in[55] = (CASDIN[55] !== 1'bz) && CASDIN[55]; // rv 0
  assign CASDIN_in[56] = (CASDIN[56] !== 1'bz) && CASDIN[56]; // rv 0
  assign CASDIN_in[57] = (CASDIN[57] !== 1'bz) && CASDIN[57]; // rv 0
  assign CASDIN_in[58] = (CASDIN[58] !== 1'bz) && CASDIN[58]; // rv 0
  assign CASDIN_in[59] = (CASDIN[59] !== 1'bz) && CASDIN[59]; // rv 0
  assign CASDIN_in[5] = (CASDIN[5] !== 1'bz) && CASDIN[5]; // rv 0
  assign CASDIN_in[60] = (CASDIN[60] !== 1'bz) && CASDIN[60]; // rv 0
  assign CASDIN_in[61] = (CASDIN[61] !== 1'bz) && CASDIN[61]; // rv 0
  assign CASDIN_in[62] = (CASDIN[62] !== 1'bz) && CASDIN[62]; // rv 0
  assign CASDIN_in[63] = (CASDIN[63] !== 1'bz) && CASDIN[63]; // rv 0
  assign CASDIN_in[6] = (CASDIN[6] !== 1'bz) && CASDIN[6]; // rv 0
  assign CASDIN_in[7] = (CASDIN[7] !== 1'bz) && CASDIN[7]; // rv 0
  assign CASDIN_in[8] = (CASDIN[8] !== 1'bz) && CASDIN[8]; // rv 0
  assign CASDIN_in[9] = (CASDIN[9] !== 1'bz) && CASDIN[9]; // rv 0
  assign CASDOMUXEN_in = (CASDOMUXEN === 1'bz) || CASDOMUXEN; // rv 1
  assign CASDOMUX_in = (CASDOMUX !== 1'bz) && CASDOMUX; // rv 0
  assign CASNXTRDEN_in = (CASNXTRDEN !== 1'bz) && CASNXTRDEN; // rv 0
  assign CASOREGIMUXEN_in = (CASOREGIMUXEN === 1'bz) || CASOREGIMUXEN; // rv 1
  assign CASOREGIMUX_in = (CASOREGIMUX !== 1'bz) && CASOREGIMUX; // rv 0
  assign CASPRVEMPTY_in = (CASPRVEMPTY !== 1'bz) && CASPRVEMPTY; // rv 0
  always @ (*) DINP_in = DINP;
  always @ (*) DIN_in = DIN;
  assign INJECTDBITERR_in = (INJECTDBITERR !== 1'bz) && INJECTDBITERR; // rv 0
  assign INJECTSBITERR_in = (INJECTSBITERR !== 1'bz) && INJECTSBITERR; // rv 0
  assign RDCLK_in = (RDCLK !== 1'bz) && (RDCLK ^ IS_RDCLK_INVERTED_BIN); // rv 0
  assign RDEN_in = (RDEN !== 1'bz) && (RDEN ^ IS_RDEN_INVERTED_BIN); // rv 0
  assign REGCE_in = (REGCE === 1'bz) || REGCE; // rv 1
  assign RSTREG_in = (RSTREG !== 1'bz) && (RSTREG ^ IS_RSTREG_INVERTED_BIN); // rv 0
  assign RST_in = (RST !== 1'bz) && (RST ^ IS_RST_INVERTED_BIN); // rv 0
  assign SLEEP_in = (SLEEP !== 1'bz) && SLEEP; // rv 0
  assign WRCLK_in = (WRCLK !== 1'bz) && (WRCLK ^ IS_WRCLK_INVERTED_BIN); // rv 0
  assign WREN_in = (WREN !== 1'bz) && (WREN ^ IS_WREN_INVERTED_BIN); // rv 0
`endif

// internal variables, signals, busses
  localparam integer ADDR_WIDTH = 15;
  localparam integer INIT_WIDTH = 72;
  localparam integer D_WIDTH = 64;
  localparam integer DP_WIDTH = 8;

  localparam mem_width = 1;
  localparam memp_width = 1;
  localparam mem_size = 32768;
  localparam mem_depth = mem_size;
  localparam memp_depth = mem_size/8;
  localparam mem_pad = 64;
  localparam memp_pad = 8;
  localparam encode = 1'b1;
  localparam decode = 1'b0;
  integer i=0;
  integer j=0;
  integer k=0;
  integer ra=0;
  integer raa=0;
  integer raw=0;
  integer wb=0;
  integer rd_loops_a = 1;
  integer wr_loops_b = 1;
  localparam max_rd_loops = D_WIDTH;
  localparam max_wr_loops = D_WIDTH;
  integer rdcount_adj = 0;
  integer wrcount_adj = 0;
  integer wr_adj = 0;
  wire RDEN_int;
  wire RDEN_lat;
  wire WREN_int;
  wire WREN_lat;
  wire RDEN_reg;
  reg  fill_lat=0;
  reg  fill_reg=0;
  wire WREN_ecc;
  wire RDEN_ecc;
  reg  fill_ecc=0;
  wire SLEEP_A_int;
  wire SLEEP_B_int;
  reg  [1:0] SLEEP_A_reg = 2'b0;
  reg  [1:0] SLEEP_B_reg = 2'b0;
  wire RSTREG_A_int;
  wire REGCE_A_int;
  wire [7:0] DINP_int;
  reg CASDOMUXA_reg = 1'b0;
  reg CASOREGIMUXA_reg = 1'b0;
  wire INJECTDBITERR_int;
  wire INJECTSBITERR_int;
  wire prog_empty;
  reg prog_empty_cc = 1;
  reg  ram_full_c = 0;
  wire ram_empty;
  reg  ram_empty_i = 1;
  reg  ram_empty_c = 1;
  reg  o_lat_empty = 1;
  reg  o_reg_empty = 1;
  reg  o_ecc_empty = 1;
  wire [1:0] output_stages;
  reg [6:0] error_bit = 7'b0;
  reg [DP_WIDTH-1:0] eccparity_reg = 8'h00;
  wire o_stages_full;
  wire o_stages_empty;
  reg  o_stages_full_sync=0;
  reg  o_stages_full_sync1=0;
  reg  o_stages_full_sync2=0;
  reg  o_stages_full_sync3=0;
  wire prog_full;
  reg  prog_full_reg = 1'b0;
  reg  rderr_reg = 1'b0;
  reg  wrerr_reg = 1'b0;
  wire [INIT_WIDTH-1:0] INIT_A_int;
  wire [INIT_WIDTH-1:0] SRVAL_A_int;

  wire mem_wr_en_b;
  reg mem_wr_en_b_wf = 1'b0;
  wire [D_WIDTH-1:0] mem_we_b;
  wire [DP_WIDTH-1:0] memp_we_b;
  wire [D_WIDTH-1:0] mem_rm_douta;
  wire [DP_WIDTH-1:0] memp_rm_douta;
  wire mem_rd_en_a;
  wire mem_rst_a;
  reg mem_is_rst_a = 1'b0;
  reg first_read = 1'b0;
  reg rdcount_en = 1'b0;

  reg                     mem      [0 : mem_depth+mem_pad-1];
  reg  [D_WIDTH-1 : 0]  ram_rd_a;
  reg [D_WIDTH-1 : 0]  mem_wr_b;
  reg  wr_b_event = 1'b0;
  reg  [D_WIDTH-1 : 0]  mem_rd_b_rf;
  reg  [D_WIDTH-1 : 0]  mem_rd_b_wf;
  reg  [D_WIDTH-1 : 0]  mem_a_reg;
  reg [D_WIDTH-1 : 0]  mem_a_reg_mux;
  reg  [D_WIDTH-1 : 0]  mem_a_lat;
  reg  [D_WIDTH-1 : 0]  mem_a_pipe;
  reg                     memp     [0 : memp_depth+memp_pad-1];
  reg  [DP_WIDTH-1 : 0] ramp_rd_a;
  wire [DP_WIDTH-1 : 0] memp_wr_b;
  reg  [DP_WIDTH-1 : 0] memp_rd_b_rf;
  reg  [DP_WIDTH-1 : 0] memp_rd_b_wf;
  reg  [DP_WIDTH-1 : 0]  memp_a_reg;
  reg [DP_WIDTH-1 : 0]  memp_a_reg_mux;
  reg  [DP_WIDTH-1 : 0]  memp_a_lat;
  reg [DP_WIDTH-1 : 0]  memp_a_out;
  reg  [DP_WIDTH-1 : 0]  memp_a_pipe;
  wire dbit_int;
  wire sbit_int;
  reg dbit_lat = 0;
  reg sbit_lat = 0;
  reg dbit_pipe = 0;
  reg sbit_pipe = 0;
  reg dbit_reg = 0;
  reg sbit_reg = 0;
  reg dbit_ecc;
  reg sbit_ecc;
  wire [ADDR_WIDTH-1:0] wr_addr_b_mask;
  reg [ADDR_WIDTH-1:0] rd_addr_a = 0;
  reg [ADDR_WIDTH-1:0] wr_addr_b = 0;
  reg [ADDR_WIDTH-1:0] rd_addr_a_wr = 0;
  reg [ADDR_WIDTH-1:0] wr_addr_b_rd = 0;
  reg [ADDR_WIDTH-1:0] rd_addr_sync_wr = 0;
  reg [ADDR_WIDTH-1:0] rd_addr_sync_wr2 = 0;
  reg [ADDR_WIDTH-1:0] rd_addr_sync_wr1 = 0;
  reg [ADDR_WIDTH-1:0] wr_addr_sync_rd = 0;
  reg [ADDR_WIDTH-1:0] wr_addr_sync_rd2 = 0;
  reg [ADDR_WIDTH-1:0] wr_addr_sync_rd1 = 0;
  wire [ADDR_WIDTH-1:0] rd_addr_wr;
  wire [ADDR_WIDTH-1:0] next_rd_addr_wr;
  wire [ADDR_WIDTH-1:0] wr_addr_rd;
  wire [ADDR_WIDTH-1:0] next_wr_addr_rd;
  wire [ADDR_WIDTH:0] wr_simple_raw;
//  wire [ADDR_WIDTH:0] rd_simple_raw;
  wire [ADDR_WIDTH-1:0] wr_simple;
  wire [ADDR_WIDTH:0] rd_simple;
  reg [ADDR_WIDTH-1:0] rd_simple_cc = 0;
  reg  [ADDR_WIDTH-1:0] wr_simple_sync = 0;
  reg  [ADDR_WIDTH-1:0] rd_simple_sync = 0;

//reset logic variables
  reg RST_in_p1 = 1'b0;
  reg WRRST_int = 1'b0;
  reg RST_sync = 1'b0;
  reg WRRST_done = 1'b0;
  reg WRRST_done1 = 1'b0;
  reg WRRST_done2 = 1'b0;
  wire RDRST_int;
  reg RDRST_done = 1'b0;
  reg RDRST_done1 = 1'b0;
  reg RDRST_done2 = 1'b0;
  wire WRRST_done_wr;
  reg WRRST_in_sync_rd = 1'b0;
  reg WRRST_in_sync_rd1 = 1'b0;
  reg WRRSTBUSY_dly = 1'b0;
  reg WRRSTBUSY_dly1 = 1'b0;
  reg RDRSTBUSY_dly = 1'b0;
  reg RDRSTBUSY_dly1 = 1'b0;
  reg RDRSTBUSY_dly2 = 1'b0;

  reg [7:0] synd_wr;
  reg [7:0] synd_rd;
  reg [7:0] synd_ecc;

  reg sdp_mode = 1'b1;
  reg sdp_mode_wr = 1'b1;
  reg sdp_mode_rd = 1'b1;

// full/empty variables
  wire [ADDR_WIDTH-1:0] full_count;
  wire [ADDR_WIDTH-1:0] next_full_count;
  wire [ADDR_WIDTH-1:0] full_count_masked;
  wire [8:0] m_full;
  wire [8:0] m_full_raw;
  wire [5:0] n_empty;
  wire [5:0] unr_ratio;
  wire [ADDR_WIDTH+1:0] prog_full_val;
  wire [ADDR_WIDTH+1:0] prog_empty_val;

  reg ram_full_i;
  wire ram_one_from_full_i;
  wire ram_two_from_full_i;
  wire ram_one_from_full;
  wire ram_two_from_full;
  wire ram_one_read_from_not_full;

  wire [ADDR_WIDTH-1:0] empty_count;
  wire [ADDR_WIDTH-1:0] next_empty_count;
  wire ram_one_read_from_empty_i;
  wire ram_one_read_from_empty;
  wire ram_one_write_from_not_empty;
  wire ram_one_write_from_not_empty_i;

reg en_clk_sync = 1'b0;

// define tasks, functions

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

reg cas_warning = 1'b0;
task is_cas_connected;
integer i;
begin
  for (i=0;i<=63;i=i+1) begin
    if (CASDIN[i] === 1'bz) begin
      cas_warning = 1'b1;
      $display("Warning: [Unisim %s-130] CASDIN[%2d] signal is unconnected in CASCADE mode Instance: %m", MODULE_NAME, i);
    end
  end
  for (i=0;i<=7;i=i+1) begin
    if (CASDINP[i] === 1'bz) begin
      cas_warning = 1'b1;
      $display("Warning: [Unisim %s-130] CASDINP[%2d] signal is unconnected in CASCADE mode Instance: %m", MODULE_NAME, i);
    end
  end
  if (CASDOMUX === 1'bz) begin
      cas_warning = 1'b1;
      $display("Warning: [Unisim %s-130] CASDOMUX signal is unconnected in CASCADE mode Instance: %m", MODULE_NAME);
    end
  if (CASDOMUXEN === 1'bz) begin
      cas_warning = 1'b1;
      $display("Warning: [Unisim %s-130] CASDOMUXEN signal is unconnected in CASCADE mode Instance: %m", MODULE_NAME);
    end
  if (CASNXTRDEN === 1'bz) begin
      cas_warning = 1'b1;
      $display("Warning: [Unisim %s-130] CASNXTRDEN signal is unconnected in CASCADE mode Instance: %m", MODULE_NAME);
    end
  if (CASOREGIMUX === 1'bz) begin
      cas_warning = 1'b1;
      $display("Warning: [Unisim %s-130] CASOREGIMUX signal is unconnected in CASCADE mode Instance: %m", MODULE_NAME);
    end
  if (CASOREGIMUXEN === 1'bz) begin
      cas_warning = 1'b1;
      $display("Warning: [Unisim %s-130] CASOREGIMUXEN signal is unconnected in CASCADE mode Instance: %m", MODULE_NAME);
    end
end
endtask // is_cas_connected

  assign RDEN_int = ((CASCADE_ORDER_BIN == CASCADE_ORDER_FIRST) ||
                    (CASCADE_ORDER_BIN == CASCADE_ORDER_MIDDLE)) ?
                     CASNXTRDEN_in && ~SLEEP_A_int : RDEN_in;
  assign WREN_int = ((CASCADE_ORDER_BIN == CASCADE_ORDER_LAST) ||
                    (CASCADE_ORDER_BIN == CASCADE_ORDER_MIDDLE)) ?
                    ~(CASPRVEMPTY_in || FULL_out || SLEEP_B_int) : WREN_in;
  assign DINP_int = ((CASCADE_ORDER_BIN == CASCADE_ORDER_LAST) ||
                     (CASCADE_ORDER_BIN == CASCADE_ORDER_MIDDLE)) ?  CASDINP_in : DINP_in;
  assign mem_wr_en_b = WREN_int && ~FULL_out && ~WRRSTBUSY_out;
  assign mem_rd_en_a = (RDEN_int ||
                        ((fill_lat || fill_reg || fill_ecc) && ~SLEEP_A_int)) && 
                        ~ram_empty && ~RDRST_int;

  assign INJECTDBITERR_int = (EN_ECC_WRITE_BIN == EN_ECC_WRITE_FALSE) ? 1'b0 :
                            INJECTDBITERR_in;
  assign INJECTSBITERR_int = (EN_ECC_WRITE_BIN == EN_ECC_WRITE_FALSE) ? 1'b0 :
                            INJECTSBITERR_in || INJECTDBITERR_in;
  wire [35:0] bit_err_pat;
  assign bit_err_pat = INJECTDBITERR_int ? 36'h400000004 : INJECTSBITERR_int ? 36'h000000004 : 36'h0;
  always @ (*) begin
    if (INJECTDBITERR_int || INJECTSBITERR_int) begin
      if ((CASCADE_ORDER_BIN == CASCADE_ORDER_LAST) ||
          (CASCADE_ORDER_BIN == CASCADE_ORDER_MIDDLE))
         mem_wr_b = CASDIN_in ^ {bit_err_pat, 28'h0};
      else
         mem_wr_b = DIN_in ^ {bit_err_pat, 28'h0};
    end
    else begin
      if ((CASCADE_ORDER_BIN == CASCADE_ORDER_LAST) ||
          (CASCADE_ORDER_BIN == CASCADE_ORDER_MIDDLE))
         mem_wr_b = CASDIN_in;
      else
         mem_wr_b = DIN_in;
    end
  end
  assign memp_wr_b = (EN_ECC_WRITE_BIN == EN_ECC_WRITE_TRUE) ? synd_wr : DINP_int;

//victor DRC
reg sleep_is_asserted;
reg sleep_is_deasserted;
reg RDEN_p1;
reg RDEN_p2;
reg RDEN_p3;
reg RDEN_p4;
reg RDEN_p5;
reg RDEN_p6;
reg WREN_p1;
reg WREN_p2;
reg WREN_p3;
reg SLEEPA_p1;
reg SLEEPA_p2;
reg SLEEPB_p1;
reg SLEEPB_p2;

  always @(SLEEP_in) begin
     sleep_is_asserted <= 1'b0;
     sleep_is_deasserted <= 1'b0;
     if (SLEEP_in == 1'b1)
        sleep_is_asserted <= 1'b1;
     else if (SLEEP_in == 1'b0)
        sleep_is_deasserted <= 1'b1;
  end

  //victor drc #5
  always @(posedge RDCLK_in) begin
      if (sleep_is_asserted && RDEN_in) begin
            $display("Error: [Unisim %s-23] DRC : RDEN must be LOW in the clock cycle when SLEEP is going from LOW to HIGH. Instance: %m", MODULE_NAME);
      end
  end
  always @(posedge WRCLK_in) begin
      if (sleep_is_asserted && WREN_in) begin
            $display("Error: [Unisim %s-23] DRC : WREN must be LOW in the clock cycle when SLEEP is going from LOW to HIGH. Instance: %m", MODULE_NAME);
      end
  end

  always @(posedge RDCLK_in) begin
      if (glblGSR) begin
         RDEN_p1 <= 1'b0;
         RDEN_p2 <= 1'b0;
         RDEN_p3 <= 1'b0;
         RDEN_p4 <= 1'b0;
         RDEN_p5 <= 1'b0;
         RDEN_p6 <= 1'b0;
      end 
      else begin
         RDEN_p1 <= RDEN_in;
         RDEN_p2 <= RDEN_p1;
         RDEN_p3 <= RDEN_p2;
         RDEN_p4 <= RDEN_p3;
         RDEN_p5 <= RDEN_p4;
         RDEN_p6 <= RDEN_p5;
      end
  end
  always @(posedge WRCLK_in) begin
      if (glblGSR) begin
         WREN_p1 <= 1'b0;
         WREN_p2 <= 1'b0;
         WREN_p3 <= 1'b0;
      end
      else begin
         WREN_p1 <= WREN_in;
         WREN_p2 <= WREN_p1;
         WREN_p3 <= WREN_p2;
      end
  end

  always @(posedge RDCLK_in or posedge WRCLK_in) begin
      if (FIRST_WORD_FALL_THROUGH_REG == "FALSE") begin 
         if (sleep_is_asserted && RDEN_p1)
                     $display("Error: [Unisim %s-23] DRC : When FWFT = FALSE, RDEN must be LOW at least one RDCLK cycle before SLEEP is going from LOW to HIGH. Instance: %m", MODULE_NAME);
         if (sleep_is_asserted && WREN_p1)
                     $display("Error: [Unisim %s-23] DRC : When FWFT = FALSE, WREN must be LOW at least one WRCLK cycle before SLEEP is going from LOW to HIGH. Instance: %m", MODULE_NAME);
      end
  end

  always @(posedge RDCLK_in or posedge WRCLK_in) begin
      if ((FIRST_WORD_FALL_THROUGH_REG == "TRUE") && (CLOCK_DOMAINS_REG == "COMMON")) begin 
         if (sleep_is_asserted && RDEN_p1)
                     $display("Error: [Unisim %s-23] DRC : When FWFT = FALSE, RDEN must be LOW at least one cycle before SLEEP is going from LOW to HIGH. Instance: %m", MODULE_NAME);
         if (sleep_is_asserted && WREN_p3)
                     $display("Error: [Unisim %s-23] DRC : When FWFT = FALSE, WREN must be LOW at least three cycle before SLEEP is going from LOW to HIGH. Instance: %m", MODULE_NAME);
      end
  end

  always @(posedge RDCLK_in or posedge WRCLK_in) begin
      if ((FIRST_WORD_FALL_THROUGH_REG == "TRUE") && (CLOCK_DOMAINS_REG == "INDEPENDENT")) begin 
         if (sleep_is_asserted && RDEN_p1)
                     $display("Error: [Unisim %s-23] DRC : When FWFT = FALSE, RDEN must be LOW at least one cycle before SLEEP is going from LOW to HIGH. Instance: %m", MODULE_NAME);
         if (sleep_is_asserted && WREN_p3 && RDEN_p6)
                     $display("Error: [Unisim %s-23] DRC : When FWFT = FALSE, WREN must be LOW at least one WRCLK plus six RDCLK cycles before SLEEP is going from LOW to HIGH. Instance: %m", MODULE_NAME);
      end
  end

  //victor drc #6
  always @(posedge RDCLK_in) begin
      if (glblGSR) begin
         SLEEPA_p1 <= 1'b0;
         SLEEPA_p2 <= 1'b0;
      end
      else begin
         SLEEPA_p1 <= SLEEP_in;
         SLEEPA_p2 <= SLEEPA_p1;
      end
  end
  always @(posedge WRCLK_in) begin
      if (glblGSR) begin
         SLEEPB_p1 <= 1'b0;
         SLEEPB_p2 <= 1'b0;
      end
      else begin
         SLEEPB_p1 <= SLEEP_in;
         SLEEPB_p2 <= SLEEPB_p1;
      end
  end
  always @(RDEN_in) begin
      if (RDEN_in && SLEEPA_p2)
         $display("Error: [Unisim %s-23] DRC : RDEN can be asserted at least 2 cycles RDCLK after SLEEP signal has been de-asserted. Instance: %m", MODULE_NAME);
  end
  always @(WREN_in) begin
      if (WREN_in && SLEEPB_p2)
         $display("Error: [Unisim %s-23] DRC : WREN can be asserted at least 2 cycles WRCLK after SLEEP signal has been de-asserted. Instance: %m", MODULE_NAME);
  end

  assign CASCADE_ORDER_BIN =
    (CASCADE_ORDER_REG == "NONE") ? CASCADE_ORDER_NONE :
    (CASCADE_ORDER_REG == "FIRST") ? CASCADE_ORDER_FIRST :
    (CASCADE_ORDER_REG == "LAST") ? CASCADE_ORDER_LAST :
    (CASCADE_ORDER_REG == "MIDDLE") ? CASCADE_ORDER_MIDDLE :
    (CASCADE_ORDER_REG == "PARALLEL") ? CASCADE_ORDER_PARALLEL :
     CASCADE_ORDER_NONE;

  assign CLOCK_DOMAINS_BIN =
    (CLOCK_DOMAINS_REG == "INDEPENDENT") ? CLOCK_DOMAINS_INDEPENDENT :
    (CLOCK_DOMAINS_REG == "COMMON") ? CLOCK_DOMAINS_COMMON :
     CLOCK_DOMAINS_INDEPENDENT;

  assign EN_ECC_PIPE_BIN =
    (EN_ECC_PIPE_REG == "FALSE") ? EN_ECC_PIPE_FALSE :
    (EN_ECC_PIPE_REG == "TRUE") ? EN_ECC_PIPE_TRUE :
     EN_ECC_PIPE_FALSE;

  assign EN_ECC_READ_BIN =
    (EN_ECC_READ_REG == "FALSE") ? EN_ECC_READ_FALSE :
    (EN_ECC_READ_REG == "TRUE") ? EN_ECC_READ_TRUE :
     EN_ECC_READ_FALSE;

  assign EN_ECC_WRITE_BIN =
    (EN_ECC_WRITE_REG == "FALSE") ? EN_ECC_WRITE_FALSE :
    (EN_ECC_WRITE_REG == "TRUE") ? EN_ECC_WRITE_TRUE :
     EN_ECC_WRITE_FALSE;

  assign FIRST_WORD_FALL_THROUGH_BIN =
    (FIRST_WORD_FALL_THROUGH_REG == "FALSE") ? FIRST_WORD_FALL_THROUGH_FALSE :
    (FIRST_WORD_FALL_THROUGH_REG == "TRUE") ? FIRST_WORD_FALL_THROUGH_TRUE :
     FIRST_WORD_FALL_THROUGH_FALSE;

  assign INIT_BIN = INIT_REG;

  assign IS_RDCLK_INVERTED_BIN = IS_RDCLK_INVERTED_REG;

  assign IS_RDEN_INVERTED_BIN = IS_RDEN_INVERTED_REG;

  assign IS_RSTREG_INVERTED_BIN = IS_RSTREG_INVERTED_REG;

  assign IS_RST_INVERTED_BIN = IS_RST_INVERTED_REG;

  assign IS_WRCLK_INVERTED_BIN = IS_WRCLK_INVERTED_REG;

  assign IS_WREN_INVERTED_BIN = IS_WREN_INVERTED_REG;

  assign PROG_EMPTY_THRESH_BIN = PROG_EMPTY_THRESH_REG;

  assign PROG_FULL_THRESH_BIN = PROG_FULL_THRESH_REG;

  assign RDCOUNT_TYPE_BIN =
    (RDCOUNT_TYPE_REG == "RAW_PNTR") ? RDCOUNT_TYPE_RAW_PNTR :
    (RDCOUNT_TYPE_REG == "EXTENDED_DATACOUNT") ? RDCOUNT_TYPE_EXTENDED_DATACOUNT :
    (RDCOUNT_TYPE_REG == "SIMPLE_DATACOUNT") ? RDCOUNT_TYPE_SIMPLE_DATACOUNT :
    (RDCOUNT_TYPE_REG == "SYNC_PNTR") ? RDCOUNT_TYPE_SYNC_PNTR :
     RDCOUNT_TYPE_RAW_PNTR;

  assign READ_WIDTH_BIN =
    (READ_WIDTH_REG == 4) ? READ_WIDTH_4 :
    (READ_WIDTH_REG == 9) ? READ_WIDTH_9 :
    (READ_WIDTH_REG == 18) ? READ_WIDTH_18 :
    (READ_WIDTH_REG == 36) ? READ_WIDTH_36 :
    (READ_WIDTH_REG == 72) ? READ_WIDTH_72 :
     READ_WIDTH_4;

  assign REGISTER_MODE_BIN =
    (REGISTER_MODE_REG == "UNREGISTERED") ? REGISTER_MODE_UNREGISTERED :
    (REGISTER_MODE_REG == "DO_PIPELINED") ? REGISTER_MODE_DO_PIPELINED :
    (REGISTER_MODE_REG == "REGISTERED") ? REGISTER_MODE_REGISTERED :
     REGISTER_MODE_UNREGISTERED;

  assign RSTREG_PRIORITY_BIN =
    (RSTREG_PRIORITY_REG == "RSTREG") ? RSTREG_PRIORITY_RSTREG :
    (RSTREG_PRIORITY_REG == "REGCE") ? RSTREG_PRIORITY_REGCE :
     RSTREG_PRIORITY_RSTREG;

  assign SLEEP_ASYNC_BIN =
    (SLEEP_ASYNC_REG == "FALSE") ? SLEEP_ASYNC_FALSE :
    (SLEEP_ASYNC_REG == "TRUE") ? SLEEP_ASYNC_TRUE :
     SLEEP_ASYNC_FALSE;

  assign SRVAL_BIN = SRVAL_REG;

  assign WRCOUNT_TYPE_BIN =
    (WRCOUNT_TYPE_REG == "RAW_PNTR") ? WRCOUNT_TYPE_RAW_PNTR :
    (WRCOUNT_TYPE_REG == "EXTENDED_DATACOUNT") ? WRCOUNT_TYPE_EXTENDED_DATACOUNT :
    (WRCOUNT_TYPE_REG == "SIMPLE_DATACOUNT") ? WRCOUNT_TYPE_SIMPLE_DATACOUNT :
    (WRCOUNT_TYPE_REG == "SYNC_PNTR") ? WRCOUNT_TYPE_SYNC_PNTR :
     WRCOUNT_TYPE_RAW_PNTR;

  assign WRITE_WIDTH_BIN =
    (WRITE_WIDTH_REG == 4) ? WRITE_WIDTH_4 :
    (WRITE_WIDTH_REG == 9) ? WRITE_WIDTH_9 :
    (WRITE_WIDTH_REG == 18) ? WRITE_WIDTH_18 :
    (WRITE_WIDTH_REG == 36) ? WRITE_WIDTH_36 :
    (WRITE_WIDTH_REG == 72) ? WRITE_WIDTH_72 :
     WRITE_WIDTH_4;

  initial begin
    #1;
    trig_attr = 1'b1;
    #100;
    trig_attr = 1'b0;
  end

  always @ (posedge trig_attr) begin
    INIT_MEM  <= #100 1'b1;
    INIT_MEM  <= #200 1'b0;

    if ((attr_test == 1'b1) ||
        ((CASCADE_ORDER_REG != "NONE") &&
         (CASCADE_ORDER_REG != "FIRST") &&
         (CASCADE_ORDER_REG != "LAST") &&
         (CASCADE_ORDER_REG != "MIDDLE") &&
         (CASCADE_ORDER_REG != "PARALLEL"))) begin
      $display("Error: [Unisim %s-101] CASCADE_ORDER attribute is set to %s.  Legal values for this attribute are NONE, FIRST, LAST, MIDDLE or PARALLEL. Instance: %m", MODULE_NAME, CASCADE_ORDER_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((CLOCK_DOMAINS_REG != "INDEPENDENT") &&
         (CLOCK_DOMAINS_REG != "COMMON"))) begin
      $display("Error: [Unisim %s-103] CLOCK_DOMAINS attribute is set to %s.  Legal values for this attribute are INDEPENDENT or COMMON. Instance: %m", MODULE_NAME, CLOCK_DOMAINS_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((EN_ECC_PIPE_REG != "FALSE") &&
         (EN_ECC_PIPE_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-108] EN_ECC_PIPE attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, EN_ECC_PIPE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((EN_ECC_READ_REG != "FALSE") &&
         (EN_ECC_READ_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-109] EN_ECC_READ attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, EN_ECC_READ_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((EN_ECC_WRITE_REG != "FALSE") &&
         (EN_ECC_WRITE_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-110] EN_ECC_WRITE attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, EN_ECC_WRITE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((FIRST_WORD_FALL_THROUGH_REG != "FALSE") &&
         (FIRST_WORD_FALL_THROUGH_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-106] FIRST_WORD_FALL_THROUGH attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, FIRST_WORD_FALL_THROUGH_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((PROG_EMPTY_THRESH_REG < 1) || (PROG_EMPTY_THRESH_REG > 8191))) begin
      $display("Error: [Unisim %s-114] PROG_EMPTY_THRESH attribute is set to %d.  Legal values for this attribute are 1 to 8191. Instance: %m", MODULE_NAME, PROG_EMPTY_THRESH_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((PROG_FULL_THRESH_REG < 1) || (PROG_FULL_THRESH_REG > 8191))) begin
      $display("Error: [Unisim %s-115] PROG_FULL_THRESH attribute is set to %d.  Legal values for this attribute are 1 to 8191. Instance: %m", MODULE_NAME, PROG_FULL_THRESH_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((RDCOUNT_TYPE_REG != "RAW_PNTR") &&
         (RDCOUNT_TYPE_REG != "EXTENDED_DATACOUNT") &&
         (RDCOUNT_TYPE_REG != "SIMPLE_DATACOUNT") &&
         (RDCOUNT_TYPE_REG != "SYNC_PNTR"))) begin
      $display("Error: [Unisim %s-116] RDCOUNT_TYPE attribute is set to %s.  Legal values for this attribute are RAW_PNTR, EXTENDED_DATACOUNT, SIMPLE_DATACOUNT or SYNC_PNTR. Instance: %m", MODULE_NAME, RDCOUNT_TYPE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((READ_WIDTH_REG != 4) &&
         (READ_WIDTH_REG != 9) &&
         (READ_WIDTH_REG != 18) &&
         (READ_WIDTH_REG != 36) &&
         (READ_WIDTH_REG != 72))) begin
      $display("Error: [Unisim %s-117] READ_WIDTH attribute is set to %d.  Legal values for this attribute are 4, 9, 18, 36 or 72. Instance: %m", MODULE_NAME, READ_WIDTH_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((REGISTER_MODE_REG != "UNREGISTERED") &&
         (REGISTER_MODE_REG != "DO_PIPELINED") &&
         (REGISTER_MODE_REG != "REGISTERED"))) begin
      $display("Error: [Unisim %s-118] REGISTER_MODE attribute is set to %s.  Legal values for this attribute are UNREGISTERED, DO_PIPELINED or REGISTERED. Instance: %m", MODULE_NAME, REGISTER_MODE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((RSTREG_PRIORITY_REG != "RSTREG") &&
         (RSTREG_PRIORITY_REG != "REGCE"))) begin
      $display("Error: [Unisim %s-119] RSTREG_PRIORITY attribute is set to %s.  Legal values for this attribute are RSTREG or REGCE. Instance: %m", MODULE_NAME, RSTREG_PRIORITY_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((SLEEP_ASYNC_REG != "FALSE") &&
         (SLEEP_ASYNC_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-273] SLEEP_ASYNC attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, SLEEP_ASYNC_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((WRCOUNT_TYPE_REG != "RAW_PNTR") &&
         (WRCOUNT_TYPE_REG != "EXTENDED_DATACOUNT") &&
         (WRCOUNT_TYPE_REG != "SIMPLE_DATACOUNT") &&
         (WRCOUNT_TYPE_REG != "SYNC_PNTR"))) begin
      $display("Error: [Unisim %s-122] WRCOUNT_TYPE attribute is set to %s.  Legal values for this attribute are RAW_PNTR, EXTENDED_DATACOUNT, SIMPLE_DATACOUNT or SYNC_PNTR. Instance: %m", MODULE_NAME, WRCOUNT_TYPE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((WRITE_WIDTH_REG != 4) &&
         (WRITE_WIDTH_REG != 9) &&
         (WRITE_WIDTH_REG != 18) &&
         (WRITE_WIDTH_REG != 36) &&
         (WRITE_WIDTH_REG != 72))) begin
      $display("Error: [Unisim %s-123] WRITE_WIDTH attribute is set to %d.  Legal values for this attribute are 4, 9, 18, 36 or 72. Instance: %m", MODULE_NAME, WRITE_WIDTH_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (PROG_EMPTY_THRESH_REG < 1) ||
        (PROG_EMPTY_THRESH_REG >= mem_depth/READ_WIDTH_BIN)) begin
      $display("Error: [Unisim %s-124] PROG_EMPTY_THRESH is set to %d. When READ_WIDTH is set to %d PROG_EMPTY_THRESH must be greater than 0 and less than %d. Instance: %m", MODULE_NAME, PROG_EMPTY_THRESH_REG, READ_WIDTH_REG, mem_depth/READ_WIDTH_BIN);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (PROG_FULL_THRESH_REG < 1) ||
        (PROG_FULL_THRESH_REG >= mem_depth/WRITE_WIDTH_BIN)) begin
      $display("Error: [Unisim %s-125] PROG_FULL_THRESH is set to %d. When WRITE_WIDTH is set to %d PROG_FULL_THRESH must be greater than 0 and less than %d. Instance: %m", MODULE_NAME, PROG_FULL_THRESH_REG, WRITE_WIDTH_REG, mem_depth/WRITE_WIDTH_BIN);
      attr_err = 1'b1;
    end

    if ((CASCADE_ORDER_REG == "LAST") ||
        (CASCADE_ORDER_REG == "MIDDLE") ||
        (CASCADE_ORDER_REG == "PARALLEL")) begin
       is_cas_connected;
       if (cas_warning) $display("Warning: [Unisim %s-126] CASCADE_ORDER attribute is set to %s and some or all of the CASCADE signals are unconnected. Simulation behavior may not match hardware under these circumstances. Please check that all CASCADE signals are properly connected. Instance: %m", MODULE_NAME, CASCADE_ORDER_REG);
    end

    if (attr_err == 1'b1) #100 $finish;
  end

  initial begin
    INIT_MEM  <= #100 1'b1;
    INIT_MEM  <= #200 1'b0;
  end

  assign output_stages =
         ((EN_ECC_PIPE_BIN == EN_ECC_PIPE_TRUE) &&
          (REGISTER_MODE_BIN == REGISTER_MODE_REGISTERED) &&
          (FIRST_WORD_FALL_THROUGH_BIN == FIRST_WORD_FALL_THROUGH_TRUE)) ? 2'b11 :
         ((EN_ECC_PIPE_BIN != EN_ECC_PIPE_TRUE) &&
          (REGISTER_MODE_BIN != REGISTER_MODE_REGISTERED) &&
          (FIRST_WORD_FALL_THROUGH_BIN != FIRST_WORD_FALL_THROUGH_TRUE)) ? 2'b00 :
         ((EN_ECC_PIPE_BIN == EN_ECC_PIPE_TRUE) ^
          (REGISTER_MODE_BIN == REGISTER_MODE_REGISTERED) ^
          (FIRST_WORD_FALL_THROUGH_BIN == FIRST_WORD_FALL_THROUGH_TRUE)) ? 2'b01 : 2'b10;

  assign wr_addr_b_mask =
    (WRITE_WIDTH_REG == 4) ?  {{ADDR_WIDTH-6{1'b1}}, 6'h3c} :
    (WRITE_WIDTH_REG == 9) ?  {{ADDR_WIDTH-6{1'b1}}, 6'h38} :
    (WRITE_WIDTH_REG == 18) ? {{ADDR_WIDTH-6{1'b1}}, 6'h30} :
    (WRITE_WIDTH_REG == 36) ? {{ADDR_WIDTH-6{1'b1}}, 6'h20} :
    (WRITE_WIDTH_REG == 72) ? {{ADDR_WIDTH-6{1'b1}}, 6'h00} :
    {{ADDR_WIDTH-6{1'b1}}, 6'h3f};

  always @(READ_WIDTH_BIN) rd_loops_a <= READ_WIDTH_BIN;
  always @(WRITE_WIDTH_BIN) wr_loops_b <= WRITE_WIDTH_BIN;

    always @ (posedge RDCLK_in) begin
      if (glblGSR) begin
          SLEEP_A_reg <= 2'b0;
      end
      else begin
          SLEEP_A_reg <= {SLEEP_A_reg[0], SLEEP_in};
      end
    end

    always @ (posedge WRCLK_in) begin
      if (glblGSR) begin
          SLEEP_B_reg <= 2'b0;
      end
      else begin
          SLEEP_B_reg <= {SLEEP_B_reg[0], SLEEP_in};
      end
    end

    assign SLEEP_A_int = SLEEP_A_reg[1] || SLEEP_A_reg[0] || SLEEP_in;
    assign SLEEP_B_int = SLEEP_B_reg[1] || SLEEP_B_reg[0] || SLEEP_in;

   assign REGCE_A_int = (REGISTER_MODE_BIN != REGISTER_MODE_DO_PIPELINED) ? RDEN_reg :
                         REGCE_in;
   assign RSTREG_A_int = (REGISTER_MODE_BIN != REGISTER_MODE_DO_PIPELINED) ? RDRST_int :
                         (RSTREG_PRIORITY_BIN == RSTREG_PRIORITY_RSTREG) ? RSTREG_in  :
                         (RSTREG_in && REGCE_in);
   assign RDEN_lat = RDEN_int || ((fill_reg || fill_ecc || fill_lat) && ~SLEEP_A_int);
   assign WREN_lat = mem_rd_en_a;
   assign RDEN_ecc = (RDEN_int || fill_reg) && (EN_ECC_PIPE_BIN == EN_ECC_PIPE_TRUE);
   assign WREN_ecc = (RDEN_int || fill_reg || fill_ecc) && ~o_lat_empty &&
                       (EN_ECC_PIPE_BIN == EN_ECC_PIPE_TRUE) && first_read;
   assign RDEN_reg = RDEN_int || fill_reg ;
  always @ (*) begin
    if (((CASCADE_ORDER_BIN == CASCADE_ORDER_LAST) ||
        (CASCADE_ORDER_BIN == CASCADE_ORDER_PARALLEL) ||
        (CASCADE_ORDER_BIN == CASCADE_ORDER_MIDDLE)) && CASDOMUXA_reg)
      DOUT_out = CASDIN_in;
    else if ((REGISTER_MODE_BIN == REGISTER_MODE_REGISTERED) ||
             (REGISTER_MODE_BIN == REGISTER_MODE_DO_PIPELINED))
      DOUT_out = mem_a_reg ^ mem_rm_douta;
    else if (EN_ECC_PIPE_BIN == EN_ECC_PIPE_TRUE)
      DOUT_out = mem_a_pipe ^ mem_rm_douta;
    else
      DOUT_out = mem_a_lat ^ mem_rm_douta;
  end
  always @ (*) begin
    if (((CASCADE_ORDER_BIN == CASCADE_ORDER_LAST) ||
        (CASCADE_ORDER_BIN == CASCADE_ORDER_PARALLEL) ||
        (CASCADE_ORDER_BIN == CASCADE_ORDER_MIDDLE)) && CASDOMUXA_reg)
      DOUTP_out = CASDINP_in;
    else if ((REGISTER_MODE_BIN == REGISTER_MODE_REGISTERED) ||
             (REGISTER_MODE_BIN == REGISTER_MODE_DO_PIPELINED))
      DOUTP_out = memp_a_reg ^ memp_rm_douta;
    else if (EN_ECC_PIPE_BIN == EN_ECC_PIPE_TRUE)
      DOUTP_out = memp_a_pipe ^ memp_rm_douta;
    else
      DOUTP_out = memp_a_lat ^ memp_rm_douta;
  end
   assign ECCPARITY_out = eccparity_reg;
   always @ (*) begin
     if (EN_ECC_PIPE_BIN == EN_ECC_PIPE_TRUE) dbit_ecc =  dbit_pipe;
     else dbit_ecc = dbit_lat;
   end
   always @ (*) begin
     if (EN_ECC_PIPE_BIN == EN_ECC_PIPE_TRUE) sbit_ecc =  sbit_pipe;
     else sbit_ecc = sbit_lat;
   end
   assign DBITERR_out = ((REGISTER_MODE_BIN == REGISTER_MODE_REGISTERED) ||
             (REGISTER_MODE_BIN == REGISTER_MODE_DO_PIPELINED)) ? dbit_reg : dbit_ecc;
   assign SBITERR_out = ((REGISTER_MODE_BIN == REGISTER_MODE_REGISTERED) ||
             (REGISTER_MODE_BIN == REGISTER_MODE_DO_PIPELINED)) ? sbit_reg : sbit_ecc;
   assign INIT_A_int =
    (READ_WIDTH_BIN <= READ_WIDTH_9)  ? {{8{INIT_BIN[8]}},     {8{INIT_BIN[7:0]}}} :
    (READ_WIDTH_BIN == READ_WIDTH_18) ? {{4{INIT_BIN[17:16]}}, {4{INIT_BIN[15:0]}}} :
    (READ_WIDTH_BIN == READ_WIDTH_36) ? {{2{INIT_BIN[35:32]}}, {2{INIT_BIN[31:0]}}} :
     INIT_BIN;

   assign SRVAL_A_int =
    (READ_WIDTH_BIN <= READ_WIDTH_9)  ? {{8{SRVAL_BIN[8]}},     {8{SRVAL_BIN[7:0]}}} :
    (READ_WIDTH_BIN == READ_WIDTH_18) ? {{4{SRVAL_BIN[17:16]}}, {4{SRVAL_BIN[15:0]}}} :
    (READ_WIDTH_BIN == READ_WIDTH_36) ? {{2{SRVAL_BIN[35:32]}}, {2{SRVAL_BIN[31:0]}}} :
     SRVAL_BIN;


   assign rd_addr_wr = (CLOCK_DOMAINS_BIN == CLOCK_DOMAINS_COMMON) ? rd_addr_a : rd_addr_sync_wr;
   assign wr_addr_rd = (CLOCK_DOMAINS_BIN == CLOCK_DOMAINS_COMMON) ? wr_addr_b : wr_addr_sync_rd;
// in clock domains common what is important is the result of the next clock edge.
   assign next_rd_addr_wr = (mem_rd_en_a == 1'b1) ? rd_addr_a + rd_loops_a : rd_addr_a;
   assign next_wr_addr_rd = (mem_wr_en_b == 1'b1) ? wr_addr_b + wr_loops_b : wr_addr_b;

   assign o_stages_empty =
         (output_stages==2'b00) ? ram_empty :
         (output_stages==2'b01) ? o_lat_empty :
         (output_stages==2'b11) ? o_reg_empty : //3 FWFT + ECC + REG
        ((output_stages==2'b10) && (EN_ECC_PIPE_BIN == EN_ECC_PIPE_FALSE)) ?
          o_reg_empty : // 2 FWFT + REG
          o_ecc_empty ; // 2 FWFT + ECC // 2 REG + ECC
   assign o_stages_full = (CLOCK_DOMAINS_BIN == CLOCK_DOMAINS_COMMON) ? ~o_stages_empty : o_stages_full_sync;

// cascade out
   assign CASDOUT_out = ((CASCADE_ORDER_BIN == CASCADE_ORDER_FIRST) ||
                             (CASCADE_ORDER_BIN == CASCADE_ORDER_PARALLEL) ||
                             (CASCADE_ORDER_BIN == CASCADE_ORDER_MIDDLE)) ?
                             DOUT_out : {D_WIDTH-1{1'b0}};
   assign CASDOUTP_out = ((CASCADE_ORDER_BIN == CASCADE_ORDER_FIRST) ||
                             (CASCADE_ORDER_BIN == CASCADE_ORDER_PARALLEL) ||
                             (CASCADE_ORDER_BIN == CASCADE_ORDER_MIDDLE)) ?
                             DOUTP_out : {DP_WIDTH-1{1'b0}};
   assign CASNXTEMPTY_out = ((CASCADE_ORDER_BIN == CASCADE_ORDER_FIRST) ||
                             (CASCADE_ORDER_BIN == CASCADE_ORDER_MIDDLE)) ?
                             EMPTY_out || SLEEP_A_int : 1'b0;
   assign CASPRVRDEN_out = ((CASCADE_ORDER_BIN == CASCADE_ORDER_LAST) ||
                             (CASCADE_ORDER_BIN == CASCADE_ORDER_MIDDLE)) ?
                             ~(CASPRVEMPTY_in || FULL_out || SLEEP_B_int) : 1'b0;

// start model internals

// integers / constants
  always begin
     if (rd_loops_a>=wr_loops_b) wr_adj = rd_loops_a/wr_loops_b;
     else wr_adj = 1;
     @(wr_loops_b or rd_loops_a);
  end

  always begin
     if (((wr_loops_b>=rd_loops_a) && (output_stages==0)) ||
         ((wr_loops_b>=output_stages*rd_loops_a) && (output_stages>0)))
          wrcount_adj = 1;
     else if ((output_stages>1) ||
              (FIRST_WORD_FALL_THROUGH_BIN == FIRST_WORD_FALL_THROUGH_TRUE))
          wrcount_adj = output_stages*wr_adj;
     else
          wrcount_adj = 0;
     if (RDCOUNT_TYPE_BIN == RDCOUNT_TYPE_SIMPLE_DATACOUNT)
       rdcount_adj = 0;
     else if (RDCOUNT_TYPE_BIN == RDCOUNT_TYPE_EXTENDED_DATACOUNT)
       rdcount_adj = output_stages;
     @(wr_adj or output_stages or wr_loops_b or rd_loops_a or FIRST_WORD_FALL_THROUGH_BIN or RDCOUNT_TYPE_BIN);
  end

// reset logic
   assign RDRSTBUSY_out = RDRST_int;
   assign WRRSTBUSY_out = WRRST_int || WRRSTBUSY_dly;
   assign mem_rst_a = RDRST_int;


//vc capture a reset event, does not matter how long the user keep it asserted
   always @ (posedge WRCLK_in) begin
      RST_in_p1 <= RST_in;
   end

   assign RST_in_pulse = RST_in & ~RST_in_p1;



// RST_in sampled by WRCLK cleared by WR done
//vc RST_sync is not used
   always @ (posedge WRCLK_in) begin
      if (RST_in && ~RST_sync) begin
         RST_sync <= 1'b1;
         end
      else if (WRRST_done) begin
         RST_sync <= 1'b0;
         end
      end

   assign WRRST_done_wr = (CLOCK_DOMAINS_BIN == CLOCK_DOMAINS_COMMON) ? WRRST_int : WRRST_done;
   always @ (posedge WRCLK_in) begin
    //vc old method would repeat reset sequence
    //if (RST_in && ~WRRSTBUSY_out) begin
      if (RST_in_pulse && ~WRRSTBUSY_out) begin
         WRRST_int <= #1 1'b1;
         end
      else if (WRRST_done_wr) begin
         WRRST_int <= #1 1'b0;
         end
      end

// WRRST_int sampled by RDCLK twice => RDRST_int in CDI
   assign RDRST_int = (CLOCK_DOMAINS_BIN==CLOCK_DOMAINS_COMMON) ? WRRST_int: WRRST_in_sync_rd;
   always @ (posedge RDCLK_in) begin
      if (glblGSR) begin
         WRRST_in_sync_rd1 <= 1'b0;
         WRRST_in_sync_rd  <= 1'b0;
         end
      else begin
         WRRST_in_sync_rd1 <= #1 WRRST_int;
         WRRST_in_sync_rd  <= #1 WRRST_in_sync_rd1;
         end
      end

// 3 rdclks to be done RD side
   always @ (posedge RDCLK_in) begin
      if (glblGSR || ~RDRST_int || (CLOCK_DOMAINS_BIN==CLOCK_DOMAINS_COMMON)) begin
         RDRST_done2 <= 1'b0;
         RDRST_done1 <= 1'b0;
         RDRST_done  <= 1'b0;
         end
      else begin
         RDRST_done2 <= RDRST_int;
         RDRST_done1 <= RDRST_done2;
         RDRST_done  <= RDRST_done1;
         end
      end

// 3 wrclks to be done WR side after RDRST_done
   always @ (posedge WRCLK_in) begin
      if (glblGSR || WRRST_done || (CLOCK_DOMAINS_BIN == CLOCK_DOMAINS_COMMON)) begin
         WRRST_done2 <= 1'b0;
         WRRST_done1 <= 1'b0;
         WRRST_done  <= 1'b0;
      end
      else if (WRRST_int) begin
         WRRST_done2 <= RDRST_done;
         WRRST_done1 <= WRRST_done2;
         WRRST_done  <= WRRST_done1;
      end
   end

// bug fix - 3 rd 2 wr. rtl verified
   always @ (posedge RDCLK_in) begin
      if (glblGSR || (CLOCK_DOMAINS_BIN==CLOCK_DOMAINS_COMMON)) begin
         RDRSTBUSY_dly2 <= 1'b0;
         RDRSTBUSY_dly1 <= 1'b0;
         RDRSTBUSY_dly  <= 1'b0;
         end
      else begin
         RDRSTBUSY_dly2 <= RDRST_int;
         RDRSTBUSY_dly1 <= RDRSTBUSY_dly2;
         RDRSTBUSY_dly  <= RDRSTBUSY_dly1;
         end
      end

   always @ (posedge WRCLK_in) begin
      if (glblGSR || (CLOCK_DOMAINS_BIN == CLOCK_DOMAINS_COMMON)) begin
         WRRSTBUSY_dly1 <= 1'b0;
         WRRSTBUSY_dly  <= 1'b0;
      end
      else begin
         WRRSTBUSY_dly1 <= RDRSTBUSY_dly;
         WRRSTBUSY_dly  <= WRRSTBUSY_dly1;
      end
   end

// cascade control
   always @ (posedge RDCLK_in) begin
      if (glblGSR) CASDOMUXA_reg <= 1'b0;
      else CASDOMUXA_reg <= CASDOMUX_in; // EN tied to 1 in FIFO
      end

   always @ (posedge RDCLK_in) begin
      if (glblGSR) CASOREGIMUXA_reg <= 1'b0;
      else CASOREGIMUXA_reg <= CASOREGIMUX_in; // EN tied to 1 in FIFO
      end

// output register
   always @ (*) begin
     if  (((CASCADE_ORDER_BIN == CASCADE_ORDER_LAST) ||
           (CASCADE_ORDER_BIN == CASCADE_ORDER_PARALLEL) ||
           (CASCADE_ORDER_BIN == CASCADE_ORDER_MIDDLE)) &&
          CASOREGIMUXA_reg) mem_a_reg_mux = CASDIN_in;
     else if (EN_ECC_PIPE_BIN == EN_ECC_PIPE_TRUE) mem_a_reg_mux =  mem_a_pipe;
     else mem_a_reg_mux = mem_a_lat;
   end
   always @ (*) begin
     if  (((CASCADE_ORDER_BIN == CASCADE_ORDER_LAST) ||
           (CASCADE_ORDER_BIN == CASCADE_ORDER_PARALLEL) ||
           (CASCADE_ORDER_BIN == CASCADE_ORDER_MIDDLE)) &&
          CASOREGIMUXA_reg) memp_a_reg_mux = CASDINP_in;
     else if (EN_ECC_PIPE_BIN == EN_ECC_PIPE_TRUE) memp_a_reg_mux =  memp_a_pipe;
     else memp_a_reg_mux = memp_a_lat;
   end

   always @ (posedge RDCLK_in or posedge INIT_MEM or glblGSR) begin
      if (glblGSR || INIT_MEM) begin
         {memp_a_reg, mem_a_reg} <= #100 INIT_A_int;
         end
      else if (RSTREG_A_int) begin
         {memp_a_reg, mem_a_reg} <= #100 SRVAL_A_int;
         end
      else if (REGCE_A_int) begin
         mem_a_reg <= #100 mem_a_reg_mux;
         memp_a_reg <= #100 memp_a_reg_mux;
         end
      end

// bit err reg
   always @ (posedge RDCLK_in or glblGSR) begin
      if (glblGSR || mem_rst_a) begin
         dbit_reg <= 1'b0;
         sbit_reg <= 1'b0;
         end
      else if (REGCE_A_int) begin
         dbit_reg <= dbit_ecc;
         sbit_reg <= sbit_ecc;
         end
      end

// ecc pipe register
   always @ (posedge RDCLK_in or posedge INIT_MEM or glblGSR) begin
      if (glblGSR || INIT_MEM) begin
         {memp_a_pipe, mem_a_pipe} <= #100 INIT_A_int;
         dbit_pipe <= #100 1'b0;
         sbit_pipe <= #100 1'b0;
         end
      else if (mem_rst_a) begin
         {memp_a_pipe, mem_a_pipe} <= #100 SRVAL_A_int;
         dbit_pipe <= #100 1'b0;
         sbit_pipe <= #100 1'b0;
         end
      else if (WREN_ecc) begin
         mem_a_pipe <= #100 mem_a_lat;
         memp_a_pipe <= #100 memp_a_lat;
         dbit_pipe <= #100 dbit_lat;
         sbit_pipe <= #100 sbit_lat;
         end
      end

   wire fifo_cc_count;
   assign fifo_cc_count = (WRITE_WIDTH_BIN==READ_WIDTH_BIN) && (CLOCK_DOMAINS_BIN==CLOCK_DOMAINS_COMMON);

// RDCOUNT sync to RDCLK
//   assign rd_simple_raw = {1'b1, wr_addr_rd}-{1'b0, rd_addr_a};
   assign rd_simple = {1'b1, wr_addr_rd}-{1'b0, rd_addr_a};
//   assign rd_simple = rd_simple_raw[ADDR_WIDTH-1:0];
   assign RDCOUNT_out =
     (RDCOUNT_TYPE_BIN == RDCOUNT_TYPE_RAW_PNTR) ? (rd_addr_a/(rd_loops_a)) :
     (RDCOUNT_TYPE_BIN == RDCOUNT_TYPE_SYNC_PNTR) ? (rd_addr_wr/(rd_loops_a)) :
     (RDCOUNT_TYPE_BIN == RDCOUNT_TYPE_SIMPLE_DATACOUNT) ? rd_simple_sync :
     (RDCOUNT_TYPE_BIN == RDCOUNT_TYPE_EXTENDED_DATACOUNT) && ~fifo_cc_count ? rd_simple_sync :
     (RDCOUNT_TYPE_BIN == RDCOUNT_TYPE_EXTENDED_DATACOUNT) && fifo_cc_count ? rd_simple_cc :
     (rd_addr_a/rd_loops_a);

   always @ (posedge RDCLK_in or glblGSR) begin
      if (glblGSR || RDRST_int)
         rd_simple_cc <= 0;
      else if (fifo_cc_count)
         if ((RDEN_int && ~EMPTY_out) && ~mem_wr_en_b)
           rd_simple_cc <= rd_simple_cc - 1;
         else if ((~RDEN_int || EMPTY_out) && mem_wr_en_b)
           rd_simple_cc <= rd_simple_cc + 1;
      end

   always @ (posedge RDCLK_in or glblGSR) begin
      if (glblGSR || RDRST_int)
         rd_simple_sync <= 0;
      else if (rdcount_en)
         if (rd_simple[ADDR_WIDTH-1:0] == {ADDR_WIDTH-1{1'b0}})
            rd_simple_sync <= {FULL_out, rd_simple[ADDR_WIDTH-2:0]}/rd_loops_a + rdcount_adj;
         else
            rd_simple_sync <= rd_simple[ADDR_WIDTH-1:0]/rd_loops_a + rdcount_adj;
      end

// WRCOUNT sync to WRCLK
   assign wr_simple_raw = {1'b1, wr_addr_b}-{1'b0,rd_addr_wr};
   assign wr_simple = wr_simple_raw[ADDR_WIDTH-1:0];
   assign WRCOUNT_out =
     (WRCOUNT_TYPE_BIN == WRCOUNT_TYPE_RAW_PNTR) ? wr_addr_b/wr_loops_b :
     (WRCOUNT_TYPE_BIN == WRCOUNT_TYPE_SYNC_PNTR) ? wr_addr_rd/wr_loops_b :
     (WRCOUNT_TYPE_BIN == WRCOUNT_TYPE_SIMPLE_DATACOUNT) ? wr_simple_sync :
     (WRCOUNT_TYPE_BIN == WRCOUNT_TYPE_EXTENDED_DATACOUNT) ? wr_simple_sync :
     wr_addr_b/wr_loops_b;

   always @ (posedge WRCLK_in or glblGSR) begin
      if (glblGSR || WRRSTBUSY_out)
         wr_simple_sync <= 0;
      else if (WRCOUNT_TYPE_BIN == WRCOUNT_TYPE_SIMPLE_DATACOUNT)
         wr_simple_sync <= wr_simple/wr_loops_b;
      else if (WRCOUNT_TYPE_BIN == WRCOUNT_TYPE_EXTENDED_DATACOUNT)
          wr_simple_sync <= (wr_simple/wr_loops_b) + wrcount_adj;
      end

// with any output stage or FWFT fill the ouptut latch
// when ram not empty and o_latch empty
   always @ (posedge RDCLK_in or glblGSR) begin
      if (glblGSR || RDRST_int) begin
         o_lat_empty <= 1;
         end
      else if (RDEN_lat) begin
         o_lat_empty <= ram_empty;
      end
      else if (WREN_lat == 1) begin
         o_lat_empty <= 0;
         end
      end

   always @ (negedge RDCLK_in or glblGSR) begin
      if (glblGSR || RDRST_int || SLEEP_A_int) begin
         fill_lat  <= 0;
         end
      else if (o_lat_empty == 1) begin
         if (output_stages>0) begin
            fill_lat  <= ~ram_empty;
         end
      end
      else begin
         fill_lat  <= 0;
         end
      end

// FWFT and
// REGISTERED not ECC_PIPE fill the ouptut register when o_latch not empty.
// REGISTERED and ECC_PIPE fill the ouptut register when o_ecc not empty.
// Empty on external read and prev stage also empty
   always @ (posedge RDCLK_in or glblGSR) begin
      if (glblGSR || RDRST_int) begin
          o_reg_empty <= 1;
         end
      else if ((o_lat_empty == 0) && RDEN_reg &&
               (EN_ECC_PIPE_BIN == EN_ECC_PIPE_FALSE)) begin
          o_reg_empty <= 0;
         end
      else if ((o_ecc_empty == 0) && RDEN_reg &&
               (EN_ECC_PIPE_BIN == EN_ECC_PIPE_TRUE)) begin
          o_reg_empty <= 0;
         end
      else if ((o_lat_empty == 1) && RDEN_reg &&
               (EN_ECC_PIPE_BIN == EN_ECC_PIPE_FALSE)) begin
          o_reg_empty <= 1;
         end
      else if ((o_ecc_empty == 1) && RDEN_reg &&
               (EN_ECC_PIPE_BIN == EN_ECC_PIPE_TRUE)) begin
          o_reg_empty <= 1;
         end
      end

   always @ (negedge RDCLK_in or glblGSR) begin
      if (glblGSR || RDRST_int || SLEEP_A_int) begin
          fill_reg <= 0;
          end
      else if ((o_lat_empty == 0) && (o_reg_empty == 1) &&
               (EN_ECC_PIPE_BIN == EN_ECC_PIPE_FALSE) &&
               (output_stages==2)) begin
          fill_reg <= 1;
          end
      else if ((o_ecc_empty == 0) && (o_reg_empty == 1) &&
               (output_stages==3)) begin
          fill_reg <= first_read;
          end
      else begin
          fill_reg <= 0;
          end
      end

   always @ (posedge RDCLK_in or glblGSR) begin
      if (glblGSR || RDRST_int) begin
          o_ecc_empty <= 1;
         end
      else if (RDEN_ecc || WREN_ecc) begin
          o_ecc_empty <= o_lat_empty;
         end
      end

   always @ (negedge RDCLK_in or glblGSR) begin
      if (glblGSR || RDRST_int || SLEEP_A_int) begin
          fill_ecc <= 0;
      end
      else if ((o_lat_empty == 0) && (o_ecc_empty == 1) && first_read &&
               ((EN_ECC_PIPE_BIN == EN_ECC_PIPE_TRUE) &&
                 ((REGISTER_MODE_BIN == REGISTER_MODE_REGISTERED) ||
                  (FIRST_WORD_FALL_THROUGH_BIN == FIRST_WORD_FALL_THROUGH_TRUE)))) begin
          fill_ecc <= 1;
      end
      else begin
          fill_ecc <= 0;
      end
   end

// read engine
   always @ (rd_addr_a or mem_rd_en_a or mem_rst_a or wr_b_event or INIT_MEM) begin
      if ((mem_rd_en_a || INIT_MEM) && ~mem_rst_a) begin
         for (raa=0;raa<rd_loops_a;raa=raa+1) begin
           ram_rd_a[raa] = mem [rd_addr_a+raa];
         end
         if (rd_loops_a >= 8) begin
           for (raa=0;raa<rd_loops_a/8;raa=raa+1) begin
             ramp_rd_a[raa] = memp [(rd_addr_a/8)+raa];
           end
         end
      end
   end

   assign RDERR_out = rderr_reg;
   always @ (posedge RDCLK_in or glblGSR) begin
      if (glblGSR)
         rderr_reg <= 1'b0;
      else if (RDEN_int && (EMPTY_out || RDRST_int))
         rderr_reg <= 1'b1;
      else
         rderr_reg <= 1'b0;
   end

   always @(posedge RDCLK_in or posedge INIT_MEM or posedge glblGSR) begin
      if (glblGSR || INIT_MEM) begin
         mem_is_rst_a <= 1'b0;
         for (ra=0;ra<rd_loops_a;ra=ra+1) begin
            mem_a_lat[ra] <= #100 INIT_A_int >> ra;
            if (ra<rd_loops_a/8) begin
               memp_a_lat[ra] <= #100 INIT_A_int >> (D_WIDTH+ra);
            end
         end
         first_read <= 1'b0;
         rdcount_en <= 1'b0;
      end
      else if (SLEEP_A_int && mem_rd_en_a) begin
         $display("Error: [Unisim %s-23] DRC : READ on port A attempted while in SLEEP mode at time %.3f ns. Instance: %m.", MODULE_NAME, $time/1000.0);
         mem_is_rst_a <= 1'b0;
         for (ra=0;ra<rd_loops_a;ra=ra+1) begin
            mem_a_lat[ra] <= #100 1'bx;
            if (ra<rd_loops_a/8) begin
               memp_a_lat[ra] <= #100 1'bx;
            end
         end
      end
      else if (mem_rst_a) begin
         if (~mem_is_rst_a) begin
           mem_is_rst_a <= 1'b1;
           for (ra=0;ra<rd_loops_a;ra=ra+1) begin
             mem_a_lat[ra] <= #100 SRVAL_A_int >> ra;
             if (ra<rd_loops_a/8) begin
               memp_a_lat[ra]  <= #100 SRVAL_A_int >> (D_WIDTH+ra);
             end
           end
         end
      end
      else if (WREN_lat) begin
        mem_is_rst_a <= 1'b0;
        if ((EN_ECC_READ_BIN == EN_ECC_READ_TRUE) && sbit_int) begin
          {memp_a_lat, mem_a_lat} <= #100 fn_cor_bit(synd_ecc[6:0], ram_rd_a, ramp_rd_a);
        end
        else begin
          mem_a_lat   <= #100 ram_rd_a;
          memp_a_lat  <= #100 ramp_rd_a;
        end
         first_read <= 1'b1;
         rdcount_en <= 1'b1;
      end
      else if (RDEN_int) begin
         rdcount_en <= 1'b1;
      end
   end

   always @ (posedge RDCLK_in or glblGSR) begin
      if (glblGSR || RDRST_int) begin
         rd_addr_a <= {ADDR_WIDTH-1{1'b0}};
         rd_addr_a_wr <= {ADDR_WIDTH-1{1'b0}};
         wr_addr_sync_rd2 <= {ADDR_WIDTH-1{1'b0}};
         wr_addr_sync_rd1 <= {ADDR_WIDTH-1{1'b0}};
         wr_addr_sync_rd  <= {ADDR_WIDTH-1{1'b0}};
         end
      else begin
         if (mem_rd_en_a) begin
            rd_addr_a <= rd_addr_a + rd_loops_a;
            end
         rd_addr_a_wr <= rd_addr_a;
         wr_addr_sync_rd2 <= wr_addr_b_rd;
         wr_addr_sync_rd1 <= wr_addr_sync_rd2;
         wr_addr_sync_rd  <= wr_addr_sync_rd1;
         end
      end

// write engine
   always @ (posedge WRCLK_in or posedge INIT_MEM) begin
     if (INIT_MEM == 1'b1) begin
// initialize memory
       for (i=0;i<mem_depth;i=i+1) begin
         mem [i] <= 1'b0;
       end
// initialize memory p
       for (i=0;i<memp_depth;i=i+1) begin
         memp [i] <= 1'b0;
       end
     end
     else if (mem_wr_en_b && ~glblGSR) begin
       if (SLEEP_B_int) begin
         $display("Error: [Unisim %s-26] DRC : WRITE on port B attempted while in SLEEP mode at time %.3f ns. Instance: %m.", MODULE_NAME, $time/1000.0);
       end
       else begin
         for (wb=0;wb<wr_loops_b;wb=wb+1) begin
           mem [wr_addr_b+wb] <= mem_wr_b[wb];
         end
         if (WRITE_WIDTH_BIN > WRITE_WIDTH_4) begin
           for (wb=0;wb<wr_loops_b/8;wb=wb+1) begin
             memp [(wr_addr_b/8)+wb] <= memp_wr_b[wb];
           end
         end
         wr_b_event <= ~wr_b_event;
       end
     end
   end

  assign mem_rm_douta = {D_WIDTH{1'b0}};
  assign memp_rm_douta = {DP_WIDTH{1'b0}};
//  assign mem_we_b = {{D_WIDTH{1'b1}}};
//  assign memp_we_b = (WRITE_WIDTH_BIN > WRITE_WIDTH_4) ? {{DP_WIDTH{1'b1}}} : {{DP_WIDTH{1'b0}}};
   assign WRERR_out = wrerr_reg;
   always @ (posedge WRCLK_in or glblGSR) begin
      if (glblGSR)
         wrerr_reg <= 1'b0;
      else if (WREN_int && (FULL_out || WRRSTBUSY_out))
         wrerr_reg <= 1'b1;
      else
         wrerr_reg <= 1'b0;
      end

   always @ (posedge WRCLK_in or glblGSR) begin
      if (glblGSR || WRRSTBUSY_out) begin
         wr_addr_b    <= {ADDR_WIDTH-1{1'b0}};
         wr_addr_b_rd <= {ADDR_WIDTH-1{1'b0}};
         o_stages_full_sync2 <= 1'b0;
         o_stages_full_sync1 <= 1'b0;
         o_stages_full_sync  <= 1'b0;
         rd_addr_sync_wr2 <= {ADDR_WIDTH-1{1'b0}};
         rd_addr_sync_wr1 <= {ADDR_WIDTH-1{1'b0}};
         rd_addr_sync_wr  <= {ADDR_WIDTH-1{1'b0}};
         end
      else begin
         if (mem_wr_en_b) begin
            wr_addr_b <= wr_addr_b + wr_loops_b;
            end
         wr_addr_b_rd <= wr_addr_b;
         o_stages_full_sync2 <= ~o_stages_empty;
         o_stages_full_sync1 <= o_stages_full_sync2;
         o_stages_full_sync  <= o_stages_full_sync1;
         rd_addr_sync_wr2 <= rd_addr_a_wr;
         rd_addr_sync_wr1 <= rd_addr_sync_wr2;
         rd_addr_sync_wr  <= rd_addr_sync_wr1;
         end
      end

// full flag
   assign prog_full = ((full_count_masked <= prog_full_val) && ((full_count > 0) || FULL_out));
   assign prog_full_val = mem_depth - (PROG_FULL_THRESH_BIN * wr_loops_b) + m_full;
   assign unr_ratio = (wr_loops_b>=rd_loops_a) ? wr_loops_b/rd_loops_a - 1 : 0;
   assign m_full = (output_stages == 0) ? 0 : ((((m_full_raw-1)/wr_loops_b)+1)*wr_loops_b);
   assign m_full_raw = output_stages*rd_loops_a;
   assign n_empty = output_stages;
   assign prog_empty_val = (PROG_EMPTY_THRESH_BIN - n_empty + 1)*rd_loops_a;

   assign full_count_masked = full_count & wr_addr_b_mask;
   assign full_count = {1'b1, rd_addr_wr} - {1'b0, wr_addr_b};
   assign next_full_count = {1'b1, next_rd_addr_wr} - {1'b0, next_wr_addr_rd};

   assign FULL_out = (CLOCK_DOMAINS_BIN == CLOCK_DOMAINS_COMMON) ? ram_full_c : ram_full_i;
// ram_full independent clocks is one_from_full common clocks
   assign ram_one_from_full_i = ((full_count < 2*wr_loops_b) && (full_count > 0));
   assign ram_two_from_full_i = ((full_count < 3*wr_loops_b) && (full_count > 0));
   assign ram_one_from_full = (next_full_count < wr_loops_b) && ~ram_full_c;
   assign ram_two_from_full = (next_full_count < 2*wr_loops_b) && ~ram_full_c;
// when full common clocks, next read makes it not full
//   assign ram_one_read_from_not_full = ((full_count + rd_loops_a >= wr_loops_b) && ram_full_c);
   assign ram_one_read_from_not_full = (next_full_count >= wr_loops_b) && ram_full_c;

   always @ (posedge WRCLK_in or glblGSR) begin
      if (glblGSR || WRRSTBUSY_out) begin
         ram_full_c <= 1'b0;
         end
      else if (mem_wr_en_b &&
               (mem_rd_en_a && (rd_loops_a < wr_loops_b)) &&
               ram_one_from_full) begin
         ram_full_c <= 1'b1;
         end
      else if (mem_wr_en_b && ~mem_rd_en_a && ram_one_from_full) begin
         ram_full_c <= 1'b1;
         end
      else if (mem_rd_en_a && ram_one_read_from_not_full) begin
         ram_full_c <= 1'b0;
         end
      else begin
         ram_full_c <= ram_full_c;
         end
      end

   always @ (posedge WRCLK_in or glblGSR) begin
      if (glblGSR || WRRSTBUSY_out) begin
         ram_full_i <= 1'b0;
         end
      else if (mem_wr_en_b && ram_two_from_full_i && ~ram_full_i) begin
         ram_full_i <= 1'b1;
         end
      else if (~ram_one_from_full_i) begin
         ram_full_i <= 1'b0;
         end
      else begin
         ram_full_i <= ram_full_i;
         end
      end

   assign PROGFULL_out = prog_full_reg;
   always @ (posedge WRCLK_in or glblGSR) begin
      if (glblGSR || WRRSTBUSY_out) begin
         prog_full_reg <= 1'b0;
         end
      else begin
         prog_full_reg <= prog_full;
         end
      end

// empty flag
   assign empty_count = {1'b1, wr_addr_rd} - {1'b0, rd_addr_a};
   assign next_empty_count = {1'b1, next_wr_addr_rd} - {1'b0, next_rd_addr_wr};
   assign EMPTY_out = o_stages_empty;
   assign ram_empty = (CLOCK_DOMAINS_BIN == CLOCK_DOMAINS_COMMON) ? ram_empty_c : ram_empty_i;
   assign ram_one_read_from_empty_i = (empty_count < 2*rd_loops_a) && (empty_count >= rd_loops_a) && ~ram_empty;
   assign ram_one_read_from_empty = (next_empty_count < rd_loops_a) && ~ram_empty;
   assign ram_one_write_from_not_empty = (next_empty_count >= rd_loops_a) && ram_empty;
   assign ram_one_write_from_not_empty_i = (rd_loops_a < wr_loops_b) ? EMPTY_out : ((empty_count + wr_loops_b) >= rd_loops_a);
   assign prog_empty = ((empty_count < prog_empty_val) || (CLOCK_DOMAINS_BIN == CLOCK_DOMAINS_COMMON && ram_empty)) && (~FULL_out || (CLOCK_DOMAINS_BIN == CLOCK_DOMAINS_INDEPENDENT));

   always @ (posedge RDCLK_in or glblGSR) begin
      if (glblGSR || RDRST_int)
         ram_empty_c <= 1'b1;
// RD only makes empty
      else if (~mem_wr_en_b &&
               mem_rd_en_a  &&
               (ram_one_read_from_empty || ram_empty_c))
         ram_empty_c <= 1'b1;
// RD and WR when one read from empty and RD more than WR makes empty
      else if (mem_wr_en_b &&
              (mem_rd_en_a && (rd_loops_a > wr_loops_b)) &&
              (ram_one_read_from_empty || ram_empty_c))
         ram_empty_c <= 1'b1;
// CR701309 CC WR when empty always makes not empty. simultaneous RD gets ERR
      else if ( mem_wr_en_b && (ram_one_write_from_not_empty && ram_empty_c))
         ram_empty_c <= 1'b0;
      else
         ram_empty_c <= ram_empty_c;
      end

   always @ (posedge RDCLK_in or glblGSR) begin
      if (glblGSR || RDRST_int)
         ram_empty_i <= 1'b1;
      else if (mem_rd_en_a && ram_one_read_from_empty_i) // RDEN_in ?
         ram_empty_i <= 1'b1;
      else if (empty_count < rd_loops_a)
         ram_empty_i <= 1'b1;
      else
         ram_empty_i <= 1'b0;
      end

//   assign PROGEMPTY_out = (CLOCK_DOMAINS_BIN == CLOCK_DOMAINS_COMMON) ? prog_empty_cc : prog_empty;
   assign PROGEMPTY_out = prog_empty_cc;
   always @ (posedge RDCLK_in or glblGSR) begin
      if (glblGSR || RDRST_int)
         prog_empty_cc <= 1'b1;
      else
         prog_empty_cc <= prog_empty;
      end
// eccparity is flopped
    always @ (*) begin
      if (EN_ECC_WRITE_BIN == EN_ECC_WRITE_FALSE) synd_wr = 8'b0; 
      else begin
        if ((CASCADE_ORDER_BIN == CASCADE_ORDER_LAST) ||
            (CASCADE_ORDER_BIN == CASCADE_ORDER_MIDDLE)) 
         synd_wr = fn_ecc(encode, CASDIN_in, CASDINP_in);
        else
         synd_wr = fn_ecc(encode, DIN_in, DINP_in);
      end
    end
    always @ (*) begin
      if (EN_ECC_READ_BIN == EN_ECC_READ_TRUE) synd_rd = fn_ecc(decode, ram_rd_a, ramp_rd_a);
      else synd_rd =  8'b0;
    end
    always @ (*) begin
      if (EN_ECC_READ_BIN == EN_ECC_READ_TRUE) synd_ecc = synd_rd ^ ramp_rd_a;
      else  synd_ecc = 8'b0;
    end
    assign sbit_int = (|synd_ecc &&  synd_ecc[7]);
    assign dbit_int = (|synd_ecc && ~synd_ecc[7]);
    always @(posedge RDCLK_in) begin
       if (mem_rst_a) begin
         sbit_lat  <= 1'b0;
         dbit_lat  <= 1'b0;
         error_bit   <= 7'b0;
         end
       else if (mem_rd_en_a && (EN_ECC_READ_BIN == EN_ECC_READ_TRUE)) begin
         sbit_lat    <= sbit_int;
         dbit_lat    <= dbit_int;
         error_bit   <= synd_ecc[6:0];
         end
       end

//    assign {memp_a_ecc_cor, mem_a_ecc_cor} = sbit_int ?
//            fn_cor_bit(synd_ecc[6:0], mem_rd_a, memp_rd_a) :
//            {memp_rd_a, mem_rd_a};

    always @ (posedge WRCLK_in or glblGSR) begin
      if(glblGSR || (EN_ECC_WRITE_BIN == EN_ECC_WRITE_FALSE))
        eccparity_reg <= 8'h00;
      else if (mem_wr_en_b)
        eccparity_reg <= synd_wr;
    end

`ifdef XIL_TIMING
  reg notifier;
  wire rdclk_en_n;
  wire rdclk_en_p;
  wire wrclk_en_n;
  wire wrclk_en_p;
  assign rdclk_en_n = IS_RDCLK_INVERTED_BIN;
  assign rdclk_en_p = ~IS_RDCLK_INVERTED_BIN;
  assign wrclk_en_n = IS_WRCLK_INVERTED_BIN;
  assign wrclk_en_p = ~IS_WRCLK_INVERTED_BIN;
`endif

  specify
    (CASDIN *> CASDOUT) = (0:0:0, 0:0:0);
    (CASDIN *> DOUT) = (0:0:0, 0:0:0);
    (CASDINP *> CASDOUTP) = (0:0:0, 0:0:0);
    (CASDINP *> DOUTP) = (0:0:0, 0:0:0);
    (CASPRVEMPTY => CASPRVRDEN) = (0:0:0, 0:0:0);
    (RDCLK *> CASDOUT) = (100:100:100, 100:100:100);
    (RDCLK *> CASDOUTP) = (100:100:100, 100:100:100);
    (RDCLK *> DOUT) = (100:100:100, 100:100:100);
    (RDCLK *> DOUTP) = (100:100:100, 100:100:100);
    (RDCLK *> RDCOUNT) = (100:100:100, 100:100:100);
    (RDCLK *> WRCOUNT) = (100:100:100, 100:100:100);
    (RDCLK => CASNXTEMPTY) = (100:100:100, 100:100:100);
    (RDCLK => DBITERR) = (100:100:100, 100:100:100);
    (RDCLK => EMPTY) = (100:100:100, 100:100:100);
    (RDCLK => PROGEMPTY) = (100:100:100, 100:100:100);
    (RDCLK => RDERR) = (100:100:100, 100:100:100);
    (RDCLK => RDRSTBUSY) = (100:100:100, 100:100:100);
    (RDCLK => SBITERR) = (100:100:100, 100:100:100);
    (WRCLK *> CASDOUT) = (100:100:100, 100:100:100);
    (WRCLK *> CASDOUTP) = (100:100:100, 100:100:100);
    (WRCLK *> DOUT) = (100:100:100, 100:100:100);
    (WRCLK *> DOUTP) = (100:100:100, 100:100:100);
    (WRCLK *> ECCPARITY) = (100:100:100, 100:100:100);
    (WRCLK *> RDCOUNT) = (100:100:100, 100:100:100);
    (WRCLK *> WRCOUNT) = (100:100:100, 100:100:100);
    (WRCLK => CASPRVRDEN) = (100:100:100, 100:100:100);
    (WRCLK => FULL) = (100:100:100, 100:100:100);
    (WRCLK => PROGFULL) = (100:100:100, 100:100:100);
    (WRCLK => RDRSTBUSY) = (100:100:100, 100:100:100);
    (WRCLK => WRERR) = (100:100:100, 100:100:100);
    (WRCLK => WRRSTBUSY) = (100:100:100, 100:100:100);
`ifdef XIL_TIMING
    $period (negedge RDCLK, 0:0:0, notifier);
    $period (negedge WRCLK, 0:0:0, notifier);
    $period (posedge RDCLK, 0:0:0, notifier);
    $period (posedge WRCLK, 0:0:0, notifier);
    $setuphold (negedge RDCLK, negedge CASDIN, 0:0:0, 0:0:0, notifier,rdclk_en_n,rdclk_en_n, RDCLK_delay, CASDIN_delay);
    $setuphold (negedge RDCLK, negedge CASDINP, 0:0:0, 0:0:0, notifier,rdclk_en_n,rdclk_en_n, RDCLK_delay, CASDINP_delay);
    $setuphold (negedge RDCLK, negedge CASDOMUX, 0:0:0, 0:0:0, notifier,rdclk_en_n,rdclk_en_n, RDCLK_delay, CASDOMUX_delay);
    $setuphold (negedge RDCLK, negedge CASDOMUXEN, 0:0:0, 0:0:0, notifier,rdclk_en_n,rdclk_en_n, RDCLK_delay, CASDOMUXEN_delay);
    $setuphold (negedge RDCLK, negedge CASNXTRDEN, 0:0:0, 0:0:0, notifier,rdclk_en_n,rdclk_en_n, RDCLK_delay, CASNXTRDEN_delay);
    $setuphold (negedge RDCLK, negedge CASOREGIMUX, 0:0:0, 0:0:0, notifier,rdclk_en_n,rdclk_en_n, RDCLK_delay, CASOREGIMUX_delay);
    $setuphold (negedge RDCLK, negedge CASOREGIMUXEN, 0:0:0, 0:0:0, notifier,rdclk_en_n,rdclk_en_n, RDCLK_delay, CASOREGIMUXEN_delay);
    $setuphold (negedge RDCLK, negedge CASPRVEMPTY, 0:0:0, 0:0:0, notifier,rdclk_en_n,rdclk_en_n, RDCLK_delay, CASPRVEMPTY_delay);
    $setuphold (negedge RDCLK, negedge DIN, 0:0:0, 0:0:0, notifier,rdclk_en_n,rdclk_en_n, RDCLK_delay, DIN_delay);
    $setuphold (negedge RDCLK, negedge DINP, 0:0:0, 0:0:0, notifier,rdclk_en_n,rdclk_en_n, RDCLK_delay, DINP_delay);
    $setuphold (negedge RDCLK, negedge RDEN, 0:0:0, 0:0:0, notifier,rdclk_en_n,rdclk_en_n, RDCLK_delay, RDEN_delay);
    $setuphold (negedge RDCLK, negedge REGCE, 0:0:0, 0:0:0, notifier,rdclk_en_n,rdclk_en_n, RDCLK_delay, REGCE_delay);
    $setuphold (negedge RDCLK, negedge RSTREG, 0:0:0, 0:0:0, notifier,rdclk_en_n,rdclk_en_n, RDCLK_delay, RSTREG_delay);
    $setuphold (negedge RDCLK, negedge SLEEP, 0:0:0, 0:0:0, notifier,rdclk_en_n,rdclk_en_n, RDCLK_delay, SLEEP_delay);
    $setuphold (negedge RDCLK, negedge WREN, 0:0:0, 0:0:0, notifier,rdclk_en_n,rdclk_en_n, RDCLK_delay, WREN_delay);
    $setuphold (negedge RDCLK, posedge CASDIN, 0:0:0, 0:0:0, notifier,rdclk_en_n,rdclk_en_n, RDCLK_delay, CASDIN_delay);
    $setuphold (negedge RDCLK, posedge CASDINP, 0:0:0, 0:0:0, notifier,rdclk_en_n,rdclk_en_n, RDCLK_delay, CASDINP_delay);
    $setuphold (negedge RDCLK, posedge CASDOMUX, 0:0:0, 0:0:0, notifier,rdclk_en_n,rdclk_en_n, RDCLK_delay, CASDOMUX_delay);
    $setuphold (negedge RDCLK, posedge CASDOMUXEN, 0:0:0, 0:0:0, notifier,rdclk_en_n,rdclk_en_n, RDCLK_delay, CASDOMUXEN_delay);
    $setuphold (negedge RDCLK, posedge CASNXTRDEN, 0:0:0, 0:0:0, notifier,rdclk_en_n,rdclk_en_n, RDCLK_delay, CASNXTRDEN_delay);
    $setuphold (negedge RDCLK, posedge CASOREGIMUX, 0:0:0, 0:0:0, notifier,rdclk_en_n,rdclk_en_n, RDCLK_delay, CASOREGIMUX_delay);
    $setuphold (negedge RDCLK, posedge CASOREGIMUXEN, 0:0:0, 0:0:0, notifier,rdclk_en_n,rdclk_en_n, RDCLK_delay, CASOREGIMUXEN_delay);
    $setuphold (negedge RDCLK, posedge CASPRVEMPTY, 0:0:0, 0:0:0, notifier,rdclk_en_n,rdclk_en_n, RDCLK_delay, CASPRVEMPTY_delay);
    $setuphold (negedge RDCLK, posedge DIN, 0:0:0, 0:0:0, notifier,rdclk_en_n,rdclk_en_n, RDCLK_delay, DIN_delay);
    $setuphold (negedge RDCLK, posedge DINP, 0:0:0, 0:0:0, notifier,rdclk_en_n,rdclk_en_n, RDCLK_delay, DINP_delay);
    $setuphold (negedge RDCLK, posedge RDEN, 0:0:0, 0:0:0, notifier,rdclk_en_n,rdclk_en_n, RDCLK_delay, RDEN_delay);
    $setuphold (negedge RDCLK, posedge REGCE, 0:0:0, 0:0:0, notifier,rdclk_en_n,rdclk_en_n, RDCLK_delay, REGCE_delay);
    $setuphold (negedge RDCLK, posedge RSTREG, 0:0:0, 0:0:0, notifier,rdclk_en_n,rdclk_en_n, RDCLK_delay, RSTREG_delay);
    $setuphold (negedge RDCLK, posedge SLEEP, 0:0:0, 0:0:0, notifier,rdclk_en_n,rdclk_en_n, RDCLK_delay, SLEEP_delay);
    $setuphold (negedge RDCLK, posedge WREN, 0:0:0, 0:0:0, notifier,rdclk_en_n,rdclk_en_n, RDCLK_delay, WREN_delay);
    $setuphold (negedge WRCLK, negedge CASDIN, 0:0:0, 0:0:0, notifier,wrclk_en_n,wrclk_en_n, WRCLK_delay, CASDIN_delay);
    $setuphold (negedge WRCLK, negedge CASDINP, 0:0:0, 0:0:0, notifier,wrclk_en_n,wrclk_en_n, WRCLK_delay, CASDINP_delay);
    $setuphold (negedge WRCLK, negedge CASDOMUX, 0:0:0, 0:0:0, notifier,wrclk_en_n,wrclk_en_n, WRCLK_delay, CASDOMUX_delay);
    $setuphold (negedge WRCLK, negedge CASDOMUXEN, 0:0:0, 0:0:0, notifier,wrclk_en_n,wrclk_en_n, WRCLK_delay, CASDOMUXEN_delay);
    $setuphold (negedge WRCLK, negedge CASNXTRDEN, 0:0:0, 0:0:0, notifier,wrclk_en_n,wrclk_en_n, WRCLK_delay, CASNXTRDEN_delay);
    $setuphold (negedge WRCLK, negedge CASPRVEMPTY, 0:0:0, 0:0:0, notifier,wrclk_en_n,wrclk_en_n, WRCLK_delay, CASPRVEMPTY_delay);
    $setuphold (negedge WRCLK, negedge DIN, 0:0:0, 0:0:0, notifier,wrclk_en_n,wrclk_en_n, WRCLK_delay, DIN_delay);
    $setuphold (negedge WRCLK, negedge DINP, 0:0:0, 0:0:0, notifier,wrclk_en_n,wrclk_en_n, WRCLK_delay, DINP_delay);
    $setuphold (negedge WRCLK, negedge INJECTDBITERR, 0:0:0, 0:0:0, notifier,wrclk_en_n,wrclk_en_n, WRCLK_delay, INJECTDBITERR_delay);
    $setuphold (negedge WRCLK, negedge INJECTSBITERR, 0:0:0, 0:0:0, notifier,wrclk_en_n,wrclk_en_n, WRCLK_delay, INJECTSBITERR_delay);
    $setuphold (negedge WRCLK, negedge RDEN, 0:0:0, 0:0:0, notifier,wrclk_en_n,wrclk_en_n, WRCLK_delay, RDEN_delay);
    $setuphold (negedge WRCLK, negedge RST, 0:0:0, 0:0:0, notifier,wrclk_en_n,wrclk_en_n, WRCLK_delay, RST_delay);
    $setuphold (negedge WRCLK, negedge WREN, 0:0:0, 0:0:0, notifier,wrclk_en_n,wrclk_en_n, WRCLK_delay, WREN_delay);
    $setuphold (negedge WRCLK, posedge CASDIN, 0:0:0, 0:0:0, notifier,wrclk_en_n,wrclk_en_n, WRCLK_delay, CASDIN_delay);
    $setuphold (negedge WRCLK, posedge CASDINP, 0:0:0, 0:0:0, notifier,wrclk_en_n,wrclk_en_n, WRCLK_delay, CASDINP_delay);
    $setuphold (negedge WRCLK, posedge CASDOMUX, 0:0:0, 0:0:0, notifier,wrclk_en_n,wrclk_en_n, WRCLK_delay, CASDOMUX_delay);
    $setuphold (negedge WRCLK, posedge CASDOMUXEN, 0:0:0, 0:0:0, notifier,wrclk_en_n,wrclk_en_n, WRCLK_delay, CASDOMUXEN_delay);
    $setuphold (negedge WRCLK, posedge CASNXTRDEN, 0:0:0, 0:0:0, notifier,wrclk_en_n,wrclk_en_n, WRCLK_delay, CASNXTRDEN_delay);
    $setuphold (negedge WRCLK, posedge CASPRVEMPTY, 0:0:0, 0:0:0, notifier,wrclk_en_n,wrclk_en_n, WRCLK_delay, CASPRVEMPTY_delay);
    $setuphold (negedge WRCLK, posedge DIN, 0:0:0, 0:0:0, notifier,wrclk_en_n,wrclk_en_n, WRCLK_delay, DIN_delay);
    $setuphold (negedge WRCLK, posedge DINP, 0:0:0, 0:0:0, notifier,wrclk_en_n,wrclk_en_n, WRCLK_delay, DINP_delay);
    $setuphold (negedge WRCLK, posedge INJECTDBITERR, 0:0:0, 0:0:0, notifier,wrclk_en_n,wrclk_en_n, WRCLK_delay, INJECTDBITERR_delay);
    $setuphold (negedge WRCLK, posedge INJECTSBITERR, 0:0:0, 0:0:0, notifier,wrclk_en_n,wrclk_en_n, WRCLK_delay, INJECTSBITERR_delay);
    $setuphold (negedge WRCLK, posedge RDEN, 0:0:0, 0:0:0, notifier,wrclk_en_n,wrclk_en_n, WRCLK_delay, RDEN_delay);
    $setuphold (negedge WRCLK, posedge RST, 0:0:0, 0:0:0, notifier,wrclk_en_n,wrclk_en_n, WRCLK_delay, RST_delay);
    $setuphold (negedge WRCLK, posedge WREN, 0:0:0, 0:0:0, notifier,wrclk_en_n,wrclk_en_n, WRCLK_delay, WREN_delay);
    $setuphold (posedge RDCLK, negedge CASDIN, 0:0:0, 0:0:0, notifier,rdclk_en_p,rdclk_en_p, RDCLK_delay, CASDIN_delay);
    $setuphold (posedge RDCLK, negedge CASDINP, 0:0:0, 0:0:0, notifier,rdclk_en_p,rdclk_en_p, RDCLK_delay, CASDINP_delay);
    $setuphold (posedge RDCLK, negedge CASDOMUX, 0:0:0, 0:0:0, notifier,rdclk_en_p,rdclk_en_p, RDCLK_delay, CASDOMUX_delay);
    $setuphold (posedge RDCLK, negedge CASDOMUXEN, 0:0:0, 0:0:0, notifier,rdclk_en_p,rdclk_en_p, RDCLK_delay, CASDOMUXEN_delay);
    $setuphold (posedge RDCLK, negedge CASNXTRDEN, 0:0:0, 0:0:0, notifier,rdclk_en_p,rdclk_en_p, RDCLK_delay, CASNXTRDEN_delay);
    $setuphold (posedge RDCLK, negedge CASOREGIMUX, 0:0:0, 0:0:0, notifier,rdclk_en_p,rdclk_en_p, RDCLK_delay, CASOREGIMUX_delay);
    $setuphold (posedge RDCLK, negedge CASOREGIMUXEN, 0:0:0, 0:0:0, notifier,rdclk_en_p,rdclk_en_p, RDCLK_delay, CASOREGIMUXEN_delay);
    $setuphold (posedge RDCLK, negedge CASPRVEMPTY, 0:0:0, 0:0:0, notifier,rdclk_en_p,rdclk_en_p, RDCLK_delay, CASPRVEMPTY_delay);
    $setuphold (posedge RDCLK, negedge DIN, 0:0:0, 0:0:0, notifier,rdclk_en_p,rdclk_en_p, RDCLK_delay, DIN_delay);
    $setuphold (posedge RDCLK, negedge DINP, 0:0:0, 0:0:0, notifier,rdclk_en_p,rdclk_en_p, RDCLK_delay, DINP_delay);
    $setuphold (posedge RDCLK, negedge RDEN, 0:0:0, 0:0:0, notifier,rdclk_en_p,rdclk_en_p, RDCLK_delay, RDEN_delay);
    $setuphold (posedge RDCLK, negedge REGCE, 0:0:0, 0:0:0, notifier,rdclk_en_p,rdclk_en_p, RDCLK_delay, REGCE_delay);
    $setuphold (posedge RDCLK, negedge RSTREG, 0:0:0, 0:0:0, notifier,rdclk_en_p,rdclk_en_p, RDCLK_delay, RSTREG_delay);
    $setuphold (posedge RDCLK, negedge SLEEP, 0:0:0, 0:0:0, notifier,rdclk_en_p,rdclk_en_p, RDCLK_delay, SLEEP_delay);
    $setuphold (posedge RDCLK, negedge WREN, 0:0:0, 0:0:0, notifier,rdclk_en_p,rdclk_en_p, RDCLK_delay, WREN_delay);
    $setuphold (posedge RDCLK, posedge CASDIN, 0:0:0, 0:0:0, notifier,rdclk_en_p,rdclk_en_p, RDCLK_delay, CASDIN_delay);
    $setuphold (posedge RDCLK, posedge CASDINP, 0:0:0, 0:0:0, notifier,rdclk_en_p,rdclk_en_p, RDCLK_delay, CASDINP_delay);
    $setuphold (posedge RDCLK, posedge CASDOMUX, 0:0:0, 0:0:0, notifier,rdclk_en_p,rdclk_en_p, RDCLK_delay, CASDOMUX_delay);
    $setuphold (posedge RDCLK, posedge CASDOMUXEN, 0:0:0, 0:0:0, notifier,rdclk_en_p,rdclk_en_p, RDCLK_delay, CASDOMUXEN_delay);
    $setuphold (posedge RDCLK, posedge CASNXTRDEN, 0:0:0, 0:0:0, notifier,rdclk_en_p,rdclk_en_p, RDCLK_delay, CASNXTRDEN_delay);
    $setuphold (posedge RDCLK, posedge CASOREGIMUX, 0:0:0, 0:0:0, notifier,rdclk_en_p,rdclk_en_p, RDCLK_delay, CASOREGIMUX_delay);
    $setuphold (posedge RDCLK, posedge CASOREGIMUXEN, 0:0:0, 0:0:0, notifier,rdclk_en_p,rdclk_en_p, RDCLK_delay, CASOREGIMUXEN_delay);
    $setuphold (posedge RDCLK, posedge CASPRVEMPTY, 0:0:0, 0:0:0, notifier,rdclk_en_p,rdclk_en_p, RDCLK_delay, CASPRVEMPTY_delay);
    $setuphold (posedge RDCLK, posedge DIN, 0:0:0, 0:0:0, notifier,rdclk_en_p,rdclk_en_p, RDCLK_delay, DIN_delay);
    $setuphold (posedge RDCLK, posedge DINP, 0:0:0, 0:0:0, notifier,rdclk_en_p,rdclk_en_p, RDCLK_delay, DINP_delay);
    $setuphold (posedge RDCLK, posedge RDEN, 0:0:0, 0:0:0, notifier,rdclk_en_p,rdclk_en_p, RDCLK_delay, RDEN_delay);
    $setuphold (posedge RDCLK, posedge REGCE, 0:0:0, 0:0:0, notifier,rdclk_en_p,rdclk_en_p, RDCLK_delay, REGCE_delay);
    $setuphold (posedge RDCLK, posedge RSTREG, 0:0:0, 0:0:0, notifier,rdclk_en_p,rdclk_en_p, RDCLK_delay, RSTREG_delay);
    $setuphold (posedge RDCLK, posedge SLEEP, 0:0:0, 0:0:0, notifier,rdclk_en_p,rdclk_en_p, RDCLK_delay, SLEEP_delay);
    $setuphold (posedge RDCLK, posedge WREN, 0:0:0, 0:0:0, notifier,rdclk_en_p,rdclk_en_p, RDCLK_delay, WREN_delay);
    $setuphold (posedge WRCLK, negedge CASDIN, 0:0:0, 0:0:0, notifier,wrclk_en_p,wrclk_en_p, WRCLK_delay, CASDIN_delay);
    $setuphold (posedge WRCLK, negedge CASDINP, 0:0:0, 0:0:0, notifier,wrclk_en_p,wrclk_en_p, WRCLK_delay, CASDINP_delay);
    $setuphold (posedge WRCLK, negedge CASDOMUX, 0:0:0, 0:0:0, notifier,wrclk_en_p,wrclk_en_p, WRCLK_delay, CASDOMUX_delay);
    $setuphold (posedge WRCLK, negedge CASDOMUXEN, 0:0:0, 0:0:0, notifier,wrclk_en_p,wrclk_en_p, WRCLK_delay, CASDOMUXEN_delay);
    $setuphold (posedge WRCLK, negedge CASNXTRDEN, 0:0:0, 0:0:0, notifier,wrclk_en_p,wrclk_en_p, WRCLK_delay, CASNXTRDEN_delay);
    $setuphold (posedge WRCLK, negedge CASPRVEMPTY, 0:0:0, 0:0:0, notifier,wrclk_en_p,wrclk_en_p, WRCLK_delay, CASPRVEMPTY_delay);
    $setuphold (posedge WRCLK, negedge DIN, 0:0:0, 0:0:0, notifier,wrclk_en_p,wrclk_en_p, WRCLK_delay, DIN_delay);
    $setuphold (posedge WRCLK, negedge DINP, 0:0:0, 0:0:0, notifier,wrclk_en_p,wrclk_en_p, WRCLK_delay, DINP_delay);
    $setuphold (posedge WRCLK, negedge INJECTDBITERR, 0:0:0, 0:0:0, notifier,wrclk_en_p,wrclk_en_p, WRCLK_delay, INJECTDBITERR_delay);
    $setuphold (posedge WRCLK, negedge INJECTSBITERR, 0:0:0, 0:0:0, notifier,wrclk_en_p,wrclk_en_p, WRCLK_delay, INJECTSBITERR_delay);
    $setuphold (posedge WRCLK, negedge RDEN, 0:0:0, 0:0:0, notifier,wrclk_en_p,wrclk_en_p, WRCLK_delay, RDEN_delay);
    $setuphold (posedge WRCLK, negedge RST, 0:0:0, 0:0:0, notifier,wrclk_en_p,wrclk_en_p, WRCLK_delay, RST_delay);
    $setuphold (posedge WRCLK, negedge WREN, 0:0:0, 0:0:0, notifier,wrclk_en_p,wrclk_en_p, WRCLK_delay, WREN_delay);
    $setuphold (posedge WRCLK, posedge CASDIN, 0:0:0, 0:0:0, notifier,wrclk_en_p,wrclk_en_p, WRCLK_delay, CASDIN_delay);
    $setuphold (posedge WRCLK, posedge CASDINP, 0:0:0, 0:0:0, notifier,wrclk_en_p,wrclk_en_p, WRCLK_delay, CASDINP_delay);
    $setuphold (posedge WRCLK, posedge CASDOMUX, 0:0:0, 0:0:0, notifier,wrclk_en_p,wrclk_en_p, WRCLK_delay, CASDOMUX_delay);
    $setuphold (posedge WRCLK, posedge CASDOMUXEN, 0:0:0, 0:0:0, notifier,wrclk_en_p,wrclk_en_p, WRCLK_delay, CASDOMUXEN_delay);
    $setuphold (posedge WRCLK, posedge CASNXTRDEN, 0:0:0, 0:0:0, notifier,wrclk_en_p,wrclk_en_p, WRCLK_delay, CASNXTRDEN_delay);
    $setuphold (posedge WRCLK, posedge CASPRVEMPTY, 0:0:0, 0:0:0, notifier,wrclk_en_p,wrclk_en_p, WRCLK_delay, CASPRVEMPTY_delay);
    $setuphold (posedge WRCLK, posedge DIN, 0:0:0, 0:0:0, notifier,wrclk_en_p,wrclk_en_p, WRCLK_delay, DIN_delay);
    $setuphold (posedge WRCLK, posedge DINP, 0:0:0, 0:0:0, notifier,wrclk_en_p,wrclk_en_p, WRCLK_delay, DINP_delay);
    $setuphold (posedge WRCLK, posedge INJECTDBITERR, 0:0:0, 0:0:0, notifier,wrclk_en_p,wrclk_en_p, WRCLK_delay, INJECTDBITERR_delay);
    $setuphold (posedge WRCLK, posedge INJECTSBITERR, 0:0:0, 0:0:0, notifier,wrclk_en_p,wrclk_en_p, WRCLK_delay, INJECTSBITERR_delay);
    $setuphold (posedge WRCLK, posedge RDEN, 0:0:0, 0:0:0, notifier,wrclk_en_p,wrclk_en_p, WRCLK_delay, RDEN_delay);
    $setuphold (posedge WRCLK, posedge RST, 0:0:0, 0:0:0, notifier,wrclk_en_p,wrclk_en_p, WRCLK_delay, RST_delay);
    $setuphold (posedge WRCLK, posedge WREN, 0:0:0, 0:0:0, notifier,wrclk_en_p,wrclk_en_p, WRCLK_delay, WREN_delay);
    $width (negedge RDCLK, 0:0:0, 0, notifier);
    $width (negedge WRCLK, 0:0:0, 0, notifier);
    $width (posedge RDCLK, 0:0:0, 0, notifier);
    $width (posedge WRCLK, 0:0:0, 0, notifier);
`endif
    specparam PATHPULSE$ = 0;
  endspecify

endmodule

`endcelldefine
