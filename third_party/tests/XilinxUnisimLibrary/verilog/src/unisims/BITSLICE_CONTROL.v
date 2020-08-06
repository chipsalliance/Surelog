///////////////////////////////////////////////////////////////////////////////
//     Copyright (c) 1995/2016 Xilinx, Inc.
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
// \   \   \/      Version     : 2016.1
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        BITSLICE_CONTROL
// /___/   /\      Filename    : BITSLICE_CONTROL.v
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

module BITSLICE_CONTROL #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter CTRL_CLK = "EXTERNAL",
  parameter DIV_MODE = "DIV2",
  parameter EN_CLK_TO_EXT_NORTH = "DISABLE",
  parameter EN_CLK_TO_EXT_SOUTH = "DISABLE",
  parameter EN_DYN_ODLY_MODE = "FALSE",
  parameter EN_OTHER_NCLK = "FALSE",
  parameter EN_OTHER_PCLK = "FALSE",
  parameter IDLY_VT_TRACK = "TRUE",
  parameter INV_RXCLK = "FALSE",
  parameter ODLY_VT_TRACK = "TRUE",
  parameter QDLY_VT_TRACK = "TRUE",
  parameter [5:0] READ_IDLE_COUNT = 6'h00,
  parameter REFCLK_SRC = "PLLCLK",
  parameter integer ROUNDING_FACTOR = 16,
  parameter RXGATE_EXTEND = "FALSE",
  parameter RX_CLK_PHASE_N = "SHIFT_0",
  parameter RX_CLK_PHASE_P = "SHIFT_0",
  parameter RX_GATING = "DISABLE",
  parameter SELF_CALIBRATE = "ENABLE",
  parameter SERIAL_MODE = "FALSE",
  parameter SIM_DEVICE = "ULTRASCALE",
  parameter SIM_SPEEDUP = "FAST",
  parameter real SIM_VERSION = 2.0,
  parameter TX_GATING = "DISABLE"
)(
  output CLK_TO_EXT_NORTH,
  output CLK_TO_EXT_SOUTH,
  output DLY_RDY,
  output [6:0] DYN_DCI,
  output NCLK_NIBBLE_OUT,
  output PCLK_NIBBLE_OUT,
  output [15:0] RIU_RD_DATA,
  output RIU_VALID,
  output [39:0] RX_BIT_CTRL_OUT0,
  output [39:0] RX_BIT_CTRL_OUT1,
  output [39:0] RX_BIT_CTRL_OUT2,
  output [39:0] RX_BIT_CTRL_OUT3,
  output [39:0] RX_BIT_CTRL_OUT4,
  output [39:0] RX_BIT_CTRL_OUT5,
  output [39:0] RX_BIT_CTRL_OUT6,
  output [39:0] TX_BIT_CTRL_OUT0,
  output [39:0] TX_BIT_CTRL_OUT1,
  output [39:0] TX_BIT_CTRL_OUT2,
  output [39:0] TX_BIT_CTRL_OUT3,
  output [39:0] TX_BIT_CTRL_OUT4,
  output [39:0] TX_BIT_CTRL_OUT5,
  output [39:0] TX_BIT_CTRL_OUT6,
  output [39:0] TX_BIT_CTRL_OUT_TRI,
  output VTC_RDY,

  input CLK_FROM_EXT,
  input EN_VTC,
  input NCLK_NIBBLE_IN,
  input PCLK_NIBBLE_IN,
  input [3:0] PHY_RDCS0,
  input [3:0] PHY_RDCS1,
  input [3:0] PHY_RDEN,
  input [3:0] PHY_WRCS0,
  input [3:0] PHY_WRCS1,
  input PLL_CLK,
  input REFCLK,
  input [5:0] RIU_ADDR,
  input RIU_CLK,
  input RIU_NIBBLE_SEL,
  input [15:0] RIU_WR_DATA,
  input RIU_WR_EN,
  input RST,
  input [39:0] RX_BIT_CTRL_IN0,
  input [39:0] RX_BIT_CTRL_IN1,
  input [39:0] RX_BIT_CTRL_IN2,
  input [39:0] RX_BIT_CTRL_IN3,
  input [39:0] RX_BIT_CTRL_IN4,
  input [39:0] RX_BIT_CTRL_IN5,
  input [39:0] RX_BIT_CTRL_IN6,
  input [3:0] TBYTE_IN,
  input [39:0] TX_BIT_CTRL_IN0,
  input [39:0] TX_BIT_CTRL_IN1,
  input [39:0] TX_BIT_CTRL_IN2,
  input [39:0] TX_BIT_CTRL_IN3,
  input [39:0] TX_BIT_CTRL_IN4,
  input [39:0] TX_BIT_CTRL_IN5,
  input [39:0] TX_BIT_CTRL_IN6,
  input [39:0] TX_BIT_CTRL_IN_TRI
);

// define constants
  localparam MODULE_NAME = "BITSLICE_CONTROL";
  localparam in_delay    = 0;
  localparam out_delay   = 0;
  localparam inclk_delay    = 0;
  localparam outclk_delay   = 0;

  reg trig_attr = 1'b0;
// include dynamic registers - XILINX test only
`ifdef XIL_DR
  `include "BITSLICE_CONTROL_dr.v"
`else
  localparam [64:1] CTRL_CLK_REG = CTRL_CLK;
  localparam [32:1] DIV_MODE_REG = DIV_MODE;
  localparam [56:1] EN_CLK_TO_EXT_NORTH_REG = EN_CLK_TO_EXT_NORTH;
  localparam [56:1] EN_CLK_TO_EXT_SOUTH_REG = EN_CLK_TO_EXT_SOUTH;
  localparam [40:1] EN_DYN_ODLY_MODE_REG = EN_DYN_ODLY_MODE;
  localparam [40:1] EN_OTHER_NCLK_REG = EN_OTHER_NCLK;
  localparam [40:1] EN_OTHER_PCLK_REG = EN_OTHER_PCLK;
  localparam [40:1] IDLY_VT_TRACK_REG = IDLY_VT_TRACK;
  localparam [40:1] INV_RXCLK_REG = INV_RXCLK;
  localparam [40:1] ODLY_VT_TRACK_REG = ODLY_VT_TRACK;
  localparam [40:1] QDLY_VT_TRACK_REG = QDLY_VT_TRACK;
  localparam [5:0] READ_IDLE_COUNT_REG = READ_IDLE_COUNT;
  localparam [48:1] REFCLK_SRC_REG = REFCLK_SRC;
  localparam  [7:0] ROUNDING_FACTOR_REG = ROUNDING_FACTOR;
  localparam [40:1] RXGATE_EXTEND_REG = RXGATE_EXTEND;
  localparam [64:1] RX_CLK_PHASE_N_REG = RX_CLK_PHASE_N;
  localparam [64:1] RX_CLK_PHASE_P_REG = RX_CLK_PHASE_P;
  localparam [56:1] RX_GATING_REG = RX_GATING;
  localparam [56:1] SELF_CALIBRATE_REG = SELF_CALIBRATE;
  localparam [40:1] SERIAL_MODE_REG = SERIAL_MODE;
  localparam [152:1] SIM_DEVICE_REG = SIM_DEVICE;
  localparam [32:1] SIM_SPEEDUP_REG = SIM_SPEEDUP;
  localparam real SIM_VERSION_REG = SIM_VERSION;
  localparam [56:1] TX_GATING_REG = TX_GATING;
`endif

  localparam [40:1] BISC_MULTI_FREQ_EN_REG = "TRUE";
  localparam [56:1] CONTROL_DLY_TEST_EN_REG = "DISABLE";
  localparam [40:1] DC_ADJ_EN_REG = "FALSE";
  localparam [12:0] DLY_RNK0_REG = 13'h0000;
  localparam [12:0] DLY_RNK1_REG = 13'h0000;
  localparam [12:0] DLY_RNK2_REG = 13'h0000;
  localparam [12:0] DLY_RNK3_REG = 13'h0000;
  localparam [2:0] FDLY_REG = 3'b010;
  localparam [7:0] INCDEC_CRSE_REG = 8'h08;
  localparam [40:1] MASK_FIXDLY_REG = "FALSE";
  localparam [9:0] MON_REG = 10'h000;
  localparam [8:0] NQTR_REG = 9'h000;
  localparam [8:0] PQTR_REG = 9'h000;
  localparam [40:1] RIU_RL_ARBITRATION_FIX_EN_REG = "TRUE";
  localparam [1:0] SPARE_REG = 2'b00;

  wire [63:0] SIM_VERSION_BIN;

`ifdef XIL_ATTR_TEST
  reg attr_test = 1'b1;
`else
  reg attr_test = 1'b0;
`endif
  reg attr_err = 1'b0;
  tri0 glblGSR = glbl.GSR;

  wire CLK_TO_EXT_NORTH_out;
  wire CLK_TO_EXT_SOUTH_out;
  wire DLY_RDY_out;
  wire DLY_TEST_OUT_out;
  wire LOCAL_DIV_CLK_out;
  wire MASTER_PD_OUT_out;
  wire NCLK_NIBBLE_OUT_out;
  wire PCLK_NIBBLE_OUT_out;
  wire PLL_CLK_EN_out;
  wire REFCLK_DFD_out;
  wire RIU_VALID_out;
  wire VTC_RDY_out;
  wire [15:0] RIU_RD_DATA_out;
  wire [39:0] RX_BIT_CTRL_OUT0_out;
  wire [39:0] RX_BIT_CTRL_OUT1_out;
  wire [39:0] RX_BIT_CTRL_OUT2_out;
  wire [39:0] RX_BIT_CTRL_OUT3_out;
  wire [39:0] RX_BIT_CTRL_OUT4_out;
  wire [39:0] RX_BIT_CTRL_OUT5_out;
  wire [39:0] RX_BIT_CTRL_OUT6_out;
  wire [39:0] TX_BIT_CTRL_OUT0_out;
  wire [39:0] TX_BIT_CTRL_OUT1_out;
  wire [39:0] TX_BIT_CTRL_OUT2_out;
  wire [39:0] TX_BIT_CTRL_OUT3_out;
  wire [39:0] TX_BIT_CTRL_OUT4_out;
  wire [39:0] TX_BIT_CTRL_OUT5_out;
  wire [39:0] TX_BIT_CTRL_OUT6_out;
  wire [39:0] TX_BIT_CTRL_OUT_TRI_out;
  wire [6:0] DYN_DCI_out;

  wire CLK_TO_EXT_NORTH_delay;
  wire CLK_TO_EXT_SOUTH_delay;
  wire DLY_RDY_delay;
  wire NCLK_NIBBLE_OUT_delay;
  wire PCLK_NIBBLE_OUT_delay;
  wire RIU_VALID_delay;
  wire VTC_RDY_delay;
  wire [15:0] RIU_RD_DATA_delay;
  wire [39:0] RX_BIT_CTRL_OUT0_delay;
  wire [39:0] RX_BIT_CTRL_OUT1_delay;
  wire [39:0] RX_BIT_CTRL_OUT2_delay;
  wire [39:0] RX_BIT_CTRL_OUT3_delay;
  wire [39:0] RX_BIT_CTRL_OUT4_delay;
  wire [39:0] RX_BIT_CTRL_OUT5_delay;
  wire [39:0] RX_BIT_CTRL_OUT6_delay;
  wire [39:0] TX_BIT_CTRL_OUT0_delay;
  wire [39:0] TX_BIT_CTRL_OUT1_delay;
  wire [39:0] TX_BIT_CTRL_OUT2_delay;
  wire [39:0] TX_BIT_CTRL_OUT3_delay;
  wire [39:0] TX_BIT_CTRL_OUT4_delay;
  wire [39:0] TX_BIT_CTRL_OUT5_delay;
  wire [39:0] TX_BIT_CTRL_OUT6_delay;
  wire [39:0] TX_BIT_CTRL_OUT_TRI_delay;
  wire [6:0] DYN_DCI_delay;

  wire CLK_FROM_EXT_in;
  wire CLK_STOP_in;
  wire DLY_TEST_IN_in;
  wire EN_VTC_in;
  wire NCLK_NIBBLE_IN_in;
  wire PCLK_NIBBLE_IN_in;
  wire PLL_CLK_in;
  wire REFCLK_in;
  wire RIU_CLK_in;
  wire RIU_NIBBLE_SEL_in;
  wire RIU_WR_EN_in;
  wire RST_in;
  wire SCAN_INT_in;
  wire [15:0] RIU_WR_DATA_in;
  wire [39:0] RX_BIT_CTRL_IN0_in;
  wire [39:0] RX_BIT_CTRL_IN1_in;
  wire [39:0] RX_BIT_CTRL_IN2_in;
  wire [39:0] RX_BIT_CTRL_IN3_in;
  wire [39:0] RX_BIT_CTRL_IN4_in;
  wire [39:0] RX_BIT_CTRL_IN5_in;
  wire [39:0] RX_BIT_CTRL_IN6_in;
  wire [39:0] TX_BIT_CTRL_IN0_in;
  wire [39:0] TX_BIT_CTRL_IN1_in;
  wire [39:0] TX_BIT_CTRL_IN2_in;
  wire [39:0] TX_BIT_CTRL_IN3_in;
  wire [39:0] TX_BIT_CTRL_IN4_in;
  wire [39:0] TX_BIT_CTRL_IN5_in;
  wire [39:0] TX_BIT_CTRL_IN6_in;
  wire [39:0] TX_BIT_CTRL_IN_TRI_in;
  wire [3:0] PHY_RDCS0_in;
  wire [3:0] PHY_RDCS1_in;
  wire [3:0] PHY_RDEN_in;
  wire [3:0] PHY_WRCS0_in;
  wire [3:0] PHY_WRCS1_in;
  wire [3:0] TBYTE_IN_in;
  wire [5:0] RIU_ADDR_in;

  wire CLK_FROM_EXT_delay;
  wire EN_VTC_delay;
  wire NCLK_NIBBLE_IN_delay;
  wire PCLK_NIBBLE_IN_delay;
  wire PLL_CLK_delay;
  wire REFCLK_delay;
  wire RIU_CLK_delay;
  wire RIU_NIBBLE_SEL_delay;
  wire RIU_WR_EN_delay;
  wire RST_delay;
  wire [15:0] RIU_WR_DATA_delay;
  wire [39:0] RX_BIT_CTRL_IN0_delay;
  wire [39:0] RX_BIT_CTRL_IN1_delay;
  wire [39:0] RX_BIT_CTRL_IN2_delay;
  wire [39:0] RX_BIT_CTRL_IN3_delay;
  wire [39:0] RX_BIT_CTRL_IN4_delay;
  wire [39:0] RX_BIT_CTRL_IN5_delay;
  wire [39:0] RX_BIT_CTRL_IN6_delay;
  wire [39:0] TX_BIT_CTRL_IN0_delay;
  wire [39:0] TX_BIT_CTRL_IN1_delay;
  wire [39:0] TX_BIT_CTRL_IN2_delay;
  wire [39:0] TX_BIT_CTRL_IN3_delay;
  wire [39:0] TX_BIT_CTRL_IN4_delay;
  wire [39:0] TX_BIT_CTRL_IN5_delay;
  wire [39:0] TX_BIT_CTRL_IN6_delay;
  wire [39:0] TX_BIT_CTRL_IN_TRI_delay;
  wire [3:0] PHY_RDCS0_delay;
  wire [3:0] PHY_RDCS1_delay;
  wire [3:0] PHY_RDEN_delay;
  wire [3:0] PHY_WRCS0_delay;
  wire [3:0] PHY_WRCS1_delay;
  wire [3:0] TBYTE_IN_delay;
  wire [5:0] RIU_ADDR_delay;

  assign #(out_delay) CLK_TO_EXT_NORTH = CLK_TO_EXT_NORTH_delay;
  assign #(out_delay) CLK_TO_EXT_SOUTH = CLK_TO_EXT_SOUTH_delay;
  assign #(out_delay) DLY_RDY = DLY_RDY_delay;
  assign #(out_delay) DYN_DCI = DYN_DCI_delay;
  assign #(out_delay) NCLK_NIBBLE_OUT = NCLK_NIBBLE_OUT_delay;
  assign #(out_delay) PCLK_NIBBLE_OUT = PCLK_NIBBLE_OUT_delay;
  assign #(out_delay) RIU_RD_DATA = RIU_RD_DATA_delay;
  assign #(out_delay) RIU_VALID = RIU_VALID_delay;
  assign #(out_delay) RX_BIT_CTRL_OUT0 = RX_BIT_CTRL_OUT0_delay;
  assign #(out_delay) RX_BIT_CTRL_OUT1 = RX_BIT_CTRL_OUT1_delay;
  assign #(out_delay) RX_BIT_CTRL_OUT2 = RX_BIT_CTRL_OUT2_delay;
  assign #(out_delay) RX_BIT_CTRL_OUT3 = RX_BIT_CTRL_OUT3_delay;
  assign #(out_delay) RX_BIT_CTRL_OUT4 = RX_BIT_CTRL_OUT4_delay;
  assign #(out_delay) RX_BIT_CTRL_OUT5 = RX_BIT_CTRL_OUT5_delay;
  assign #(out_delay) RX_BIT_CTRL_OUT6 = RX_BIT_CTRL_OUT6_delay;
  assign #(out_delay) TX_BIT_CTRL_OUT0 = TX_BIT_CTRL_OUT0_delay;
  assign #(out_delay) TX_BIT_CTRL_OUT1 = TX_BIT_CTRL_OUT1_delay;
  assign #(out_delay) TX_BIT_CTRL_OUT2 = TX_BIT_CTRL_OUT2_delay;
  assign #(out_delay) TX_BIT_CTRL_OUT3 = TX_BIT_CTRL_OUT3_delay;
  assign #(out_delay) TX_BIT_CTRL_OUT4 = TX_BIT_CTRL_OUT4_delay;
  assign #(out_delay) TX_BIT_CTRL_OUT5 = TX_BIT_CTRL_OUT5_delay;
  assign #(out_delay) TX_BIT_CTRL_OUT6 = TX_BIT_CTRL_OUT6_delay;
  assign #(out_delay) TX_BIT_CTRL_OUT_TRI = TX_BIT_CTRL_OUT_TRI_delay;
  assign #(out_delay) VTC_RDY = VTC_RDY_delay;

`ifdef XIL_TIMING
  reg notifier;
`endif

`ifndef XIL_TIMING // inputs with timing checks

  assign #(in_delay) EN_VTC_delay = EN_VTC;
  assign #(in_delay) PHY_RDCS0_delay = PHY_RDCS0;
  assign #(in_delay) PHY_RDCS1_delay = PHY_RDCS1;
  assign #(in_delay) PHY_RDEN_delay = PHY_RDEN;
  assign #(in_delay) PHY_WRCS0_delay = PHY_WRCS0;
  assign #(in_delay) PHY_WRCS1_delay = PHY_WRCS1;
  assign #(inclk_delay) PLL_CLK_delay = PLL_CLK;
  assign #(inclk_delay) REFCLK_delay = REFCLK;
  assign #(in_delay) RIU_ADDR_delay = RIU_ADDR;
  assign #(inclk_delay) RIU_CLK_delay = RIU_CLK;
  assign #(in_delay) RIU_NIBBLE_SEL_delay = RIU_NIBBLE_SEL;
  assign #(in_delay) RIU_WR_DATA_delay = RIU_WR_DATA;
  assign #(in_delay) RIU_WR_EN_delay = RIU_WR_EN;
  assign #(in_delay) RST_delay = RST;
  assign #(in_delay) TBYTE_IN_delay = TBYTE_IN;

`endif

// inputs with no timing checks

  assign #(in_delay) CLK_FROM_EXT_delay = CLK_FROM_EXT;
  assign #(in_delay) NCLK_NIBBLE_IN_delay = NCLK_NIBBLE_IN;
  assign #(in_delay) PCLK_NIBBLE_IN_delay = PCLK_NIBBLE_IN;
  assign #(in_delay) RX_BIT_CTRL_IN0_delay = RX_BIT_CTRL_IN0;
  assign #(in_delay) RX_BIT_CTRL_IN1_delay = RX_BIT_CTRL_IN1;
  assign #(in_delay) RX_BIT_CTRL_IN2_delay = RX_BIT_CTRL_IN2;
  assign #(in_delay) RX_BIT_CTRL_IN3_delay = RX_BIT_CTRL_IN3;
  assign #(in_delay) RX_BIT_CTRL_IN4_delay = RX_BIT_CTRL_IN4;
  assign #(in_delay) RX_BIT_CTRL_IN5_delay = RX_BIT_CTRL_IN5;
  assign #(in_delay) RX_BIT_CTRL_IN6_delay = RX_BIT_CTRL_IN6;
  assign #(in_delay) TX_BIT_CTRL_IN0_delay = TX_BIT_CTRL_IN0;
  assign #(in_delay) TX_BIT_CTRL_IN1_delay = TX_BIT_CTRL_IN1;
  assign #(in_delay) TX_BIT_CTRL_IN2_delay = TX_BIT_CTRL_IN2;
  assign #(in_delay) TX_BIT_CTRL_IN3_delay = TX_BIT_CTRL_IN3;
  assign #(in_delay) TX_BIT_CTRL_IN4_delay = TX_BIT_CTRL_IN4;
  assign #(in_delay) TX_BIT_CTRL_IN5_delay = TX_BIT_CTRL_IN5;
  assign #(in_delay) TX_BIT_CTRL_IN6_delay = TX_BIT_CTRL_IN6;
  assign #(in_delay) TX_BIT_CTRL_IN_TRI_delay = TX_BIT_CTRL_IN_TRI;

  assign CLK_TO_EXT_NORTH_delay = CLK_TO_EXT_NORTH_out;
  assign CLK_TO_EXT_SOUTH_delay = CLK_TO_EXT_SOUTH_out;
  assign DLY_RDY_delay = DLY_RDY_out;
  assign DYN_DCI_delay = DYN_DCI_out;
  assign NCLK_NIBBLE_OUT_delay = NCLK_NIBBLE_OUT_out;
  assign PCLK_NIBBLE_OUT_delay = PCLK_NIBBLE_OUT_out;
  assign RIU_RD_DATA_delay = RIU_RD_DATA_out;
  assign RIU_VALID_delay = RIU_VALID_out;
  assign RX_BIT_CTRL_OUT0_delay = RX_BIT_CTRL_OUT0_out;
  assign RX_BIT_CTRL_OUT1_delay = RX_BIT_CTRL_OUT1_out;
  assign RX_BIT_CTRL_OUT2_delay = RX_BIT_CTRL_OUT2_out;
  assign RX_BIT_CTRL_OUT3_delay = RX_BIT_CTRL_OUT3_out;
  assign RX_BIT_CTRL_OUT4_delay = RX_BIT_CTRL_OUT4_out;
  assign RX_BIT_CTRL_OUT5_delay = RX_BIT_CTRL_OUT5_out;
  assign RX_BIT_CTRL_OUT6_delay = RX_BIT_CTRL_OUT6_out;
  assign TX_BIT_CTRL_OUT0_delay = TX_BIT_CTRL_OUT0_out;
  assign TX_BIT_CTRL_OUT1_delay = TX_BIT_CTRL_OUT1_out;
  assign TX_BIT_CTRL_OUT2_delay = TX_BIT_CTRL_OUT2_out;
  assign TX_BIT_CTRL_OUT3_delay = TX_BIT_CTRL_OUT3_out;
  assign TX_BIT_CTRL_OUT4_delay = TX_BIT_CTRL_OUT4_out;
  assign TX_BIT_CTRL_OUT5_delay = TX_BIT_CTRL_OUT5_out;
  assign TX_BIT_CTRL_OUT6_delay = TX_BIT_CTRL_OUT6_out;
  assign TX_BIT_CTRL_OUT_TRI_delay = TX_BIT_CTRL_OUT_TRI_out;
  assign VTC_RDY_delay = VTC_RDY_out;

  assign CLK_FROM_EXT_in = CLK_FROM_EXT_delay;
  assign EN_VTC_in = (EN_VTC === 1'bz) || EN_VTC_delay; // rv 1
  assign NCLK_NIBBLE_IN_in = NCLK_NIBBLE_IN_delay;
  assign PCLK_NIBBLE_IN_in = PCLK_NIBBLE_IN_delay;
  assign PHY_RDCS0_in = PHY_RDCS0_delay;
  assign PHY_RDCS1_in = PHY_RDCS1_delay;
  assign PHY_RDEN_in = PHY_RDEN_delay;
  assign PHY_WRCS0_in = PHY_WRCS0_delay;
  assign PHY_WRCS1_in = PHY_WRCS1_delay;
  assign PLL_CLK_in = PLL_CLK_delay;
  assign REFCLK_in = REFCLK_delay;
  assign RIU_ADDR_in = RIU_ADDR_delay;
  assign RIU_CLK_in = RIU_CLK_delay;
  assign RIU_NIBBLE_SEL_in = (RIU_NIBBLE_SEL !== 1'bz) && RIU_NIBBLE_SEL_delay; // rv 0
  assign RIU_WR_DATA_in = RIU_WR_DATA_delay;
  assign RIU_WR_EN_in = RIU_WR_EN_delay;
  assign RST_in = RST_delay;
  assign RX_BIT_CTRL_IN0_in = RX_BIT_CTRL_IN0_delay;
  assign RX_BIT_CTRL_IN1_in = RX_BIT_CTRL_IN1_delay;
  assign RX_BIT_CTRL_IN2_in = RX_BIT_CTRL_IN2_delay;
  assign RX_BIT_CTRL_IN3_in = RX_BIT_CTRL_IN3_delay;
  assign RX_BIT_CTRL_IN4_in = RX_BIT_CTRL_IN4_delay;
  assign RX_BIT_CTRL_IN5_in = RX_BIT_CTRL_IN5_delay;
  assign RX_BIT_CTRL_IN6_in = RX_BIT_CTRL_IN6_delay;
  assign TBYTE_IN_in[0] = (TBYTE_IN[0] !== 1'bz) && TBYTE_IN_delay[0]; // rv 0
  assign TBYTE_IN_in[1] = (TBYTE_IN[1] !== 1'bz) && TBYTE_IN_delay[1]; // rv 0
  assign TBYTE_IN_in[2] = (TBYTE_IN[2] !== 1'bz) && TBYTE_IN_delay[2]; // rv 0
  assign TBYTE_IN_in[3] = (TBYTE_IN[3] !== 1'bz) && TBYTE_IN_delay[3]; // rv 0
  assign TX_BIT_CTRL_IN0_in = TX_BIT_CTRL_IN0_delay;
  assign TX_BIT_CTRL_IN1_in = TX_BIT_CTRL_IN1_delay;
  assign TX_BIT_CTRL_IN2_in = TX_BIT_CTRL_IN2_delay;
  assign TX_BIT_CTRL_IN3_in = TX_BIT_CTRL_IN3_delay;
  assign TX_BIT_CTRL_IN4_in = TX_BIT_CTRL_IN4_delay;
  assign TX_BIT_CTRL_IN5_in = TX_BIT_CTRL_IN5_delay;
  assign TX_BIT_CTRL_IN6_in = TX_BIT_CTRL_IN6_delay;
  assign TX_BIT_CTRL_IN_TRI_in = TX_BIT_CTRL_IN_TRI_delay;

  assign SIM_VERSION_BIN = SIM_VERSION_REG * 1000;
  
  initial begin
    #1;
    trig_attr = ~trig_attr;
  end
  
  always @ (trig_attr) begin
    #1;
    if ((attr_test == 1'b1) ||
        ((CTRL_CLK_REG != "EXTERNAL") &&
         (CTRL_CLK_REG != "INTERNAL"))) begin
      $display("Error: [Unisim %s-103] CTRL_CLK attribute is set to %s.  Legal values for this attribute are EXTERNAL or INTERNAL. Instance: %m", MODULE_NAME, CTRL_CLK_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((DIV_MODE_REG != "DIV2") &&
         (DIV_MODE_REG != "DIV4"))) begin
      $display("Error: [Unisim %s-105] DIV_MODE attribute is set to %s.  Legal values for this attribute are DIV2 or DIV4. Instance: %m", MODULE_NAME, DIV_MODE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((EN_CLK_TO_EXT_NORTH_REG != "DISABLE") &&
         (EN_CLK_TO_EXT_NORTH_REG != "ENABLE"))) begin
      $display("Error: [Unisim %s-110] EN_CLK_TO_EXT_NORTH attribute is set to %s.  Legal values for this attribute are DISABLE or ENABLE. Instance: %m", MODULE_NAME, EN_CLK_TO_EXT_NORTH_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((EN_CLK_TO_EXT_SOUTH_REG != "DISABLE") &&
         (EN_CLK_TO_EXT_SOUTH_REG != "ENABLE"))) begin
      $display("Error: [Unisim %s-111] EN_CLK_TO_EXT_SOUTH attribute is set to %s.  Legal values for this attribute are DISABLE or ENABLE. Instance: %m", MODULE_NAME, EN_CLK_TO_EXT_SOUTH_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((EN_DYN_ODLY_MODE_REG != "FALSE") &&
         (EN_DYN_ODLY_MODE_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-112] EN_DYN_ODLY_MODE attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, EN_DYN_ODLY_MODE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((EN_OTHER_NCLK_REG != "FALSE") &&
         (EN_OTHER_NCLK_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-113] EN_OTHER_NCLK attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, EN_OTHER_NCLK_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((EN_OTHER_PCLK_REG != "FALSE") &&
         (EN_OTHER_PCLK_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-114] EN_OTHER_PCLK attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, EN_OTHER_PCLK_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((IDLY_VT_TRACK_REG != "TRUE") &&
         (IDLY_VT_TRACK_REG != "FALSE"))) begin
      $display("Error: [Unisim %s-116] IDLY_VT_TRACK attribute is set to %s.  Legal values for this attribute are TRUE or FALSE. Instance: %m", MODULE_NAME, IDLY_VT_TRACK_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((INV_RXCLK_REG != "FALSE") &&
         (INV_RXCLK_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-118] INV_RXCLK attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, INV_RXCLK_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((ODLY_VT_TRACK_REG != "TRUE") &&
         (ODLY_VT_TRACK_REG != "FALSE"))) begin
      $display("Error: [Unisim %s-122] ODLY_VT_TRACK attribute is set to %s.  Legal values for this attribute are TRUE or FALSE. Instance: %m", MODULE_NAME, ODLY_VT_TRACK_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((QDLY_VT_TRACK_REG != "TRUE") &&
         (QDLY_VT_TRACK_REG != "FALSE"))) begin
      $display("Error: [Unisim %s-124] QDLY_VT_TRACK attribute is set to %s.  Legal values for this attribute are TRUE or FALSE. Instance: %m", MODULE_NAME, QDLY_VT_TRACK_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((REFCLK_SRC_REG != "PLLCLK") &&
         (REFCLK_SRC_REG != "REFCLK"))) begin
      $display("Error: [Unisim %s-126] REFCLK_SRC attribute is set to %s.  Legal values for this attribute are PLLCLK or REFCLK. Instance: %m", MODULE_NAME, REFCLK_SRC_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((ROUNDING_FACTOR_REG != 16) &&
         (ROUNDING_FACTOR_REG != 2) &&
         (ROUNDING_FACTOR_REG != 4) &&
         (ROUNDING_FACTOR_REG != 8) &&
         (ROUNDING_FACTOR_REG != 32) &&
         (ROUNDING_FACTOR_REG != 64) &&
         (ROUNDING_FACTOR_REG != 128))) begin
      $display("Error: [Unisim %s-128] ROUNDING_FACTOR attribute is set to %d.  Legal values for this attribute are 16, 2, 4, 8, 32, 64 or 128. Instance: %m", MODULE_NAME, ROUNDING_FACTOR_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((RXGATE_EXTEND_REG != "FALSE") &&
         (RXGATE_EXTEND_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-129] RXGATE_EXTEND attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, RXGATE_EXTEND_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((RX_CLK_PHASE_N_REG != "SHIFT_0") &&
         (RX_CLK_PHASE_N_REG != "SHIFT_90"))) begin
      $display("Error: [Unisim %s-130] RX_CLK_PHASE_N attribute is set to %s.  Legal values for this attribute are SHIFT_0 or SHIFT_90. Instance: %m", MODULE_NAME, RX_CLK_PHASE_N_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((RX_CLK_PHASE_P_REG != "SHIFT_0") &&
         (RX_CLK_PHASE_P_REG != "SHIFT_90"))) begin
      $display("Error: [Unisim %s-131] RX_CLK_PHASE_P attribute is set to %s.  Legal values for this attribute are SHIFT_0 or SHIFT_90. Instance: %m", MODULE_NAME, RX_CLK_PHASE_P_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((RX_GATING_REG != "DISABLE") &&
         (RX_GATING_REG != "ENABLE"))) begin
      $display("Error: [Unisim %s-132] RX_GATING attribute is set to %s.  Legal values for this attribute are DISABLE or ENABLE. Instance: %m", MODULE_NAME, RX_GATING_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((SELF_CALIBRATE_REG != "ENABLE") &&
         (SELF_CALIBRATE_REG != "DISABLE"))) begin
      $display("Error: [Unisim %s-133] SELF_CALIBRATE attribute is set to %s.  Legal values for this attribute are ENABLE or DISABLE. Instance: %m", MODULE_NAME, SELF_CALIBRATE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((SERIAL_MODE_REG != "FALSE") &&
         (SERIAL_MODE_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-134] SERIAL_MODE attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, SERIAL_MODE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((SIM_DEVICE_REG != "ULTRASCALE") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES1") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES2"))) begin
      $display("Error: [Unisim %s-135] SIM_DEVICE attribute is set to %s.  Legal values for this attribute are ULTRASCALE, ULTRASCALE_PLUS, ULTRASCALE_PLUS_ES1 or ULTRASCALE_PLUS_ES2. Instance: %m", MODULE_NAME, SIM_DEVICE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((SIM_SPEEDUP_REG != "FAST") &&
         (SIM_SPEEDUP_REG != "SLOW"))) begin
      $display("Error: [Unisim %s-136] SIM_SPEEDUP attribute is set to %s.  Legal values for this attribute are FAST or SLOW. Instance: %m", MODULE_NAME, SIM_SPEEDUP_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
       ((SIM_VERSION_REG != 2.0) &&
        (SIM_VERSION_REG != 1.0))) begin
      $display("Error: [Unisim %s-137] SIM_VERSION attribute is set to %f.  Legal values for this attribute are 2.0 or 1.0. Instance: %m", MODULE_NAME, SIM_VERSION_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((TX_GATING_REG != "DISABLE") &&
         (TX_GATING_REG != "ENABLE"))) begin
      $display("Error: [Unisim %s-139] TX_GATING attribute is set to %s.  Legal values for this attribute are DISABLE or ENABLE. Instance: %m", MODULE_NAME, TX_GATING_REG);
      attr_err = 1'b1;
    end
    
    if (attr_err == 1'b1) #1 $finish;

    if (SIM_DEVICE_REG == "ULTRASCALE") begin
      if (RX_CLK_PHASE_P_REG == "SHIFT_90" || RX_CLK_PHASE_N_REG == "SHIFT_90") begin
        $display("WARNING: [Unisim %s-1] When using RX_CLK_PHASE_<P:N> = SHIFT_90 simulation may not match hardware when using RX_DELAY_VALUE > 0 or CASCADE = TRUE. Every BITSLICE_CONTROL must have at least one RX_BITSLICE with DELAY_VALUE = 0 in order to ensure proper alignment. Instance: %m",MODULE_NAME);
      end
    end
  end


  assign CLK_STOP_in = 1'b1; // tie off
  assign DLY_TEST_IN_in = 1'b0; // tie off
  assign SCAN_INT_in = 1'b1; // tie off

generate
if ((SIM_DEVICE == "ULTRASCALE_PLUS") || (SIM_DEVICE == "ULTRASCALE_PLUS_ES1") || (SIM_DEVICE == "ULTRASCALE_PLUS_ES2")) begin : generate_block1
  SIP_BITSLICE_CONTROL_D1 SIP_BITSLICE_CONTROL_INST (
    .BISC_MULTI_FREQ_EN (BISC_MULTI_FREQ_EN_REG),
    .CONTROL_DLY_TEST_EN (CONTROL_DLY_TEST_EN_REG),
    .CTRL_CLK (CTRL_CLK_REG),
    .DC_ADJ_EN (DC_ADJ_EN_REG),
    .DIV_MODE (DIV_MODE_REG),
    .DLY_RNK0 (DLY_RNK0_REG),
    .DLY_RNK1 (DLY_RNK1_REG),
    .DLY_RNK2 (DLY_RNK2_REG),
    .DLY_RNK3 (DLY_RNK3_REG),
    .EN_CLK_TO_EXT_NORTH (EN_CLK_TO_EXT_NORTH_REG),
    .EN_CLK_TO_EXT_SOUTH (EN_CLK_TO_EXT_SOUTH_REG),
    .EN_DYN_ODLY_MODE (EN_DYN_ODLY_MODE_REG),
    .EN_OTHER_NCLK (EN_OTHER_NCLK_REG),
    .EN_OTHER_PCLK (EN_OTHER_PCLK_REG),
    .FDLY (FDLY_REG),
    .IDLY_VT_TRACK (IDLY_VT_TRACK_REG),
    .INCDEC_CRSE (INCDEC_CRSE_REG),
    .INV_RXCLK (INV_RXCLK_REG),
    .MASK_FIXDLY (MASK_FIXDLY_REG),
    .MON (MON_REG),
    .NQTR (NQTR_REG),
    .ODLY_VT_TRACK (ODLY_VT_TRACK_REG),
    .PQTR (PQTR_REG),
    .QDLY_VT_TRACK (QDLY_VT_TRACK_REG),
    .READ_IDLE_COUNT (READ_IDLE_COUNT_REG),
    .REFCLK_SRC (REFCLK_SRC_REG),
    .RIU_RL_ARBITRATION_FIX_EN (RIU_RL_ARBITRATION_FIX_EN_REG),
    .ROUNDING_FACTOR (ROUNDING_FACTOR_REG),
    .RXGATE_EXTEND (RXGATE_EXTEND_REG),
    .RX_CLK_PHASE_N (RX_CLK_PHASE_N_REG),
    .RX_CLK_PHASE_P (RX_CLK_PHASE_P_REG),
    .RX_GATING (RX_GATING_REG),
    .SELF_CALIBRATE (SELF_CALIBRATE_REG),
    .SERIAL_MODE (SERIAL_MODE_REG),
    .SIM_SPEEDUP (SIM_SPEEDUP_REG),
    .SPARE (SPARE_REG),
    .TX_GATING (TX_GATING_REG),
    .CLK_TO_EXT_NORTH (CLK_TO_EXT_NORTH_out),
    .CLK_TO_EXT_SOUTH (CLK_TO_EXT_SOUTH_out),
    .DLY_RDY (DLY_RDY_out),
    .DLY_TEST_OUT (DLY_TEST_OUT_out),
    .DYN_DCI (DYN_DCI_out),
    .LOCAL_DIV_CLK (LOCAL_DIV_CLK_out),
    .MASTER_PD_OUT (MASTER_PD_OUT_out),
    .NCLK_NIBBLE_OUT (NCLK_NIBBLE_OUT_out),
    .PCLK_NIBBLE_OUT (PCLK_NIBBLE_OUT_out),
    .PLL_CLK_EN (PLL_CLK_EN_out),
    .REFCLK_DFD (REFCLK_DFD_out),
    .RIU_RD_DATA (RIU_RD_DATA_out),
    .RIU_VALID (RIU_VALID_out),
    .RX_BIT_CTRL_OUT0 (RX_BIT_CTRL_OUT0_out),
    .RX_BIT_CTRL_OUT1 (RX_BIT_CTRL_OUT1_out),
    .RX_BIT_CTRL_OUT2 (RX_BIT_CTRL_OUT2_out),
    .RX_BIT_CTRL_OUT3 (RX_BIT_CTRL_OUT3_out),
    .RX_BIT_CTRL_OUT4 (RX_BIT_CTRL_OUT4_out),
    .RX_BIT_CTRL_OUT5 (RX_BIT_CTRL_OUT5_out),
    .RX_BIT_CTRL_OUT6 (RX_BIT_CTRL_OUT6_out),
    .TX_BIT_CTRL_OUT0 (TX_BIT_CTRL_OUT0_out),
    .TX_BIT_CTRL_OUT1 (TX_BIT_CTRL_OUT1_out),
    .TX_BIT_CTRL_OUT2 (TX_BIT_CTRL_OUT2_out),
    .TX_BIT_CTRL_OUT3 (TX_BIT_CTRL_OUT3_out),
    .TX_BIT_CTRL_OUT4 (TX_BIT_CTRL_OUT4_out),
    .TX_BIT_CTRL_OUT5 (TX_BIT_CTRL_OUT5_out),
    .TX_BIT_CTRL_OUT6 (TX_BIT_CTRL_OUT6_out),
    .TX_BIT_CTRL_OUT_TRI (TX_BIT_CTRL_OUT_TRI_out),
    .VTC_RDY (VTC_RDY_out),
    .CLK_FROM_EXT (CLK_FROM_EXT_in),
    .CLK_STOP (CLK_STOP_in),
    .DLY_TEST_IN (DLY_TEST_IN_in),
    .EN_VTC (EN_VTC_in),
    .NCLK_NIBBLE_IN (NCLK_NIBBLE_IN_in),
    .PCLK_NIBBLE_IN (PCLK_NIBBLE_IN_in),
    .PHY_RDCS0 (PHY_RDCS0_in),
    .PHY_RDCS1 (PHY_RDCS1_in),
    .PHY_RDEN (PHY_RDEN_in),
    .PHY_WRCS0 (PHY_WRCS0_in),
    .PHY_WRCS1 (PHY_WRCS1_in),
    .PLL_CLK (PLL_CLK_in),
    .REFCLK (REFCLK_in),
    .RIU_ADDR (RIU_ADDR_in),
    .RIU_CLK (RIU_CLK_in),
    .RIU_NIBBLE_SEL (RIU_NIBBLE_SEL_in),
    .RIU_WR_DATA (RIU_WR_DATA_in),
    .RIU_WR_EN (RIU_WR_EN_in),
    .RST (RST_in),
    .RX_BIT_CTRL_IN0 (RX_BIT_CTRL_IN0_in),
    .RX_BIT_CTRL_IN1 (RX_BIT_CTRL_IN1_in),
    .RX_BIT_CTRL_IN2 (RX_BIT_CTRL_IN2_in),
    .RX_BIT_CTRL_IN3 (RX_BIT_CTRL_IN3_in),
    .RX_BIT_CTRL_IN4 (RX_BIT_CTRL_IN4_in),
    .RX_BIT_CTRL_IN5 (RX_BIT_CTRL_IN5_in),
    .RX_BIT_CTRL_IN6 (RX_BIT_CTRL_IN6_in),
    .SCAN_INT (SCAN_INT_in),
    .TBYTE_IN (TBYTE_IN_in),
    .TX_BIT_CTRL_IN0 (TX_BIT_CTRL_IN0_in),
    .TX_BIT_CTRL_IN1 (TX_BIT_CTRL_IN1_in),
    .TX_BIT_CTRL_IN2 (TX_BIT_CTRL_IN2_in),
    .TX_BIT_CTRL_IN3 (TX_BIT_CTRL_IN3_in),
    .TX_BIT_CTRL_IN4 (TX_BIT_CTRL_IN4_in),
    .TX_BIT_CTRL_IN5 (TX_BIT_CTRL_IN5_in),
    .TX_BIT_CTRL_IN6 (TX_BIT_CTRL_IN6_in),
    .TX_BIT_CTRL_IN_TRI (TX_BIT_CTRL_IN_TRI_in),
    .GSR (glblGSR)
  );
end 
else if (SIM_DEVICE == "ULTRASCALE") begin : generate_block1
  SIP_BITSLICE_CONTROL_K2 SIP_BITSLICE_CONTROL_INST (
    .CONTROL_DLY_TEST_EN (CONTROL_DLY_TEST_EN_REG),
    .CTRL_CLK (CTRL_CLK_REG),
    .DC_ADJ_EN (DC_ADJ_EN_REG),
    .DIV_MODE (DIV_MODE_REG),
    .DLY_RNK0 (DLY_RNK0_REG),
    .DLY_RNK1 (DLY_RNK1_REG),
    .DLY_RNK2 (DLY_RNK2_REG),
    .DLY_RNK3 (DLY_RNK3_REG),
    .EN_CLK_TO_EXT_NORTH (EN_CLK_TO_EXT_NORTH_REG),
    .EN_CLK_TO_EXT_SOUTH (EN_CLK_TO_EXT_SOUTH_REG),
    .EN_DYN_ODLY_MODE (EN_DYN_ODLY_MODE_REG),
    .EN_OTHER_NCLK (EN_OTHER_NCLK_REG),
    .EN_OTHER_PCLK (EN_OTHER_PCLK_REG),
    .FDLY (FDLY_REG),
    .IDLY_VT_TRACK (IDLY_VT_TRACK_REG),
    .INCDEC_CRSE (INCDEC_CRSE_REG),
    .INV_RXCLK (INV_RXCLK_REG),
    .MON (MON_REG),
    .NQTR (NQTR_REG),
    .ODLY_VT_TRACK (ODLY_VT_TRACK_REG),
    .PQTR (PQTR_REG),
    .QDLY_VT_TRACK (QDLY_VT_TRACK_REG),
    .READ_IDLE_COUNT (READ_IDLE_COUNT_REG),
    .REFCLK_SRC (REFCLK_SRC_REG),
    .ROUNDING_FACTOR (ROUNDING_FACTOR_REG),
    .RXGATE_EXTEND (RXGATE_EXTEND_REG),
    .RX_CLK_PHASE_N (RX_CLK_PHASE_N_REG),
    .RX_CLK_PHASE_P (RX_CLK_PHASE_P_REG),
    .RX_GATING (RX_GATING_REG),
    .SELF_CALIBRATE (SELF_CALIBRATE_REG),
    .SERIAL_MODE (SERIAL_MODE_REG),
    .SIM_SPEEDUP (SIM_SPEEDUP_REG),
    .SIM_VERSION (SIM_VERSION_BIN),
    .TX_GATING (TX_GATING_REG),
    .CLK_TO_EXT_NORTH (CLK_TO_EXT_NORTH_out),
    .CLK_TO_EXT_SOUTH (CLK_TO_EXT_SOUTH_out),
    .DLY_RDY (DLY_RDY_out),
    .DLY_TEST_OUT (DLY_TEST_OUT_out),
    .DYN_DCI (DYN_DCI_out),
    .LOCAL_DIV_CLK (LOCAL_DIV_CLK_out),
    .MASTER_PD_OUT (MASTER_PD_OUT_out),
    .NCLK_NIBBLE_OUT (NCLK_NIBBLE_OUT_out),
    .PCLK_NIBBLE_OUT (PCLK_NIBBLE_OUT_out),
    .PLL_CLK_EN (PLL_CLK_EN_out),
    .REFCLK_DFD (REFCLK_DFD_out),
    .RIU_RD_DATA (RIU_RD_DATA_out),
    .RIU_VALID (RIU_VALID_out),
    .RX_BIT_CTRL_OUT0 (RX_BIT_CTRL_OUT0_out),
    .RX_BIT_CTRL_OUT1 (RX_BIT_CTRL_OUT1_out),
    .RX_BIT_CTRL_OUT2 (RX_BIT_CTRL_OUT2_out),
    .RX_BIT_CTRL_OUT3 (RX_BIT_CTRL_OUT3_out),
    .RX_BIT_CTRL_OUT4 (RX_BIT_CTRL_OUT4_out),
    .RX_BIT_CTRL_OUT5 (RX_BIT_CTRL_OUT5_out),
    .RX_BIT_CTRL_OUT6 (RX_BIT_CTRL_OUT6_out),
    .TX_BIT_CTRL_OUT0 (TX_BIT_CTRL_OUT0_out),
    .TX_BIT_CTRL_OUT1 (TX_BIT_CTRL_OUT1_out),
    .TX_BIT_CTRL_OUT2 (TX_BIT_CTRL_OUT2_out),
    .TX_BIT_CTRL_OUT3 (TX_BIT_CTRL_OUT3_out),
    .TX_BIT_CTRL_OUT4 (TX_BIT_CTRL_OUT4_out),
    .TX_BIT_CTRL_OUT5 (TX_BIT_CTRL_OUT5_out),
    .TX_BIT_CTRL_OUT6 (TX_BIT_CTRL_OUT6_out),
    .TX_BIT_CTRL_OUT_TRI (TX_BIT_CTRL_OUT_TRI_out),
    .VTC_RDY (VTC_RDY_out),
    .CLK_FROM_EXT (CLK_FROM_EXT_in),
    .CLK_STOP (CLK_STOP_in),
    .DLY_TEST_IN (DLY_TEST_IN_in),
    .EN_VTC (EN_VTC_in),
    .NCLK_NIBBLE_IN (NCLK_NIBBLE_IN_in),
    .PCLK_NIBBLE_IN (PCLK_NIBBLE_IN_in),
    .PHY_RDCS0 (PHY_RDCS0_in),
    .PHY_RDCS1 (PHY_RDCS1_in),
    .PHY_RDEN (PHY_RDEN_in),
    .PHY_WRCS0 (PHY_WRCS0_in),
    .PHY_WRCS1 (PHY_WRCS1_in),
    .PLL_CLK (PLL_CLK_in),
    .REFCLK (REFCLK_in),
    .RIU_ADDR (RIU_ADDR_in),
    .RIU_CLK (RIU_CLK_in),
    .RIU_NIBBLE_SEL (RIU_NIBBLE_SEL_in),
    .RIU_WR_DATA (RIU_WR_DATA_in),
    .RIU_WR_EN (RIU_WR_EN_in),
    .RST (RST_in),
    .RX_BIT_CTRL_IN0 (RX_BIT_CTRL_IN0_in),
    .RX_BIT_CTRL_IN1 (RX_BIT_CTRL_IN1_in),
    .RX_BIT_CTRL_IN2 (RX_BIT_CTRL_IN2_in),
    .RX_BIT_CTRL_IN3 (RX_BIT_CTRL_IN3_in),
    .RX_BIT_CTRL_IN4 (RX_BIT_CTRL_IN4_in),
    .RX_BIT_CTRL_IN5 (RX_BIT_CTRL_IN5_in),
    .RX_BIT_CTRL_IN6 (RX_BIT_CTRL_IN6_in),
    .SCAN_INT (SCAN_INT_in),
    .TBYTE_IN (TBYTE_IN_in),
    .TX_BIT_CTRL_IN0 (TX_BIT_CTRL_IN0_in),
    .TX_BIT_CTRL_IN1 (TX_BIT_CTRL_IN1_in),
    .TX_BIT_CTRL_IN2 (TX_BIT_CTRL_IN2_in),
    .TX_BIT_CTRL_IN3 (TX_BIT_CTRL_IN3_in),
    .TX_BIT_CTRL_IN4 (TX_BIT_CTRL_IN4_in),
    .TX_BIT_CTRL_IN5 (TX_BIT_CTRL_IN5_in),
    .TX_BIT_CTRL_IN6 (TX_BIT_CTRL_IN6_in),
    .TX_BIT_CTRL_IN_TRI (TX_BIT_CTRL_IN_TRI_in),
    .GSR (glblGSR)
  );
end 
endgenerate
  specify
    (PLL_CLK => DLY_RDY) = (100:100:100, 100:100:100);
    (PLL_CLK => RX_BIT_CTRL_OUT0[20]) = (0:0:0, 0:0:0);
    (PLL_CLK => TX_BIT_CTRL_OUT0[25]) = (0:0:0, 0:0:0);
    (PLL_CLK => TX_BIT_CTRL_OUT0[26]) = (0:0:0, 0:0:0);
    (PLL_CLK => TX_BIT_CTRL_OUT1[25]) = (0:0:0, 0:0:0);
    (PLL_CLK => TX_BIT_CTRL_OUT1[26]) = (0:0:0, 0:0:0);
    (PLL_CLK => TX_BIT_CTRL_OUT2[25]) = (0:0:0, 0:0:0);
    (PLL_CLK => TX_BIT_CTRL_OUT2[26]) = (0:0:0, 0:0:0);
    (PLL_CLK => TX_BIT_CTRL_OUT3[25]) = (0:0:0, 0:0:0);
    (PLL_CLK => TX_BIT_CTRL_OUT3[26]) = (0:0:0, 0:0:0);
    (PLL_CLK => TX_BIT_CTRL_OUT4[25]) = (0:0:0, 0:0:0);
    (PLL_CLK => TX_BIT_CTRL_OUT4[26]) = (0:0:0, 0:0:0);
    (PLL_CLK => TX_BIT_CTRL_OUT5[25]) = (0:0:0, 0:0:0);
    (PLL_CLK => TX_BIT_CTRL_OUT5[26]) = (0:0:0, 0:0:0);
    (PLL_CLK => TX_BIT_CTRL_OUT6[25]) = (0:0:0, 0:0:0);
    (PLL_CLK => TX_BIT_CTRL_OUT6[26]) = (0:0:0, 0:0:0);
    (PLL_CLK => VTC_RDY) = (100:100:100, 100:100:100);
    (RIU_CLK => DLY_RDY) = (100:100:100, 100:100:100);
    (RIU_CLK => RIU_RD_DATA[0]) = (100:100:100, 100:100:100);
    (RIU_CLK => RIU_RD_DATA[10]) = (100:100:100, 100:100:100);
    (RIU_CLK => RIU_RD_DATA[11]) = (100:100:100, 100:100:100);
    (RIU_CLK => RIU_RD_DATA[12]) = (100:100:100, 100:100:100);
    (RIU_CLK => RIU_RD_DATA[13]) = (100:100:100, 100:100:100);
    (RIU_CLK => RIU_RD_DATA[14]) = (100:100:100, 100:100:100);
    (RIU_CLK => RIU_RD_DATA[15]) = (100:100:100, 100:100:100);
    (RIU_CLK => RIU_RD_DATA[1]) = (100:100:100, 100:100:100);
    (RIU_CLK => RIU_RD_DATA[2]) = (100:100:100, 100:100:100);
    (RIU_CLK => RIU_RD_DATA[3]) = (100:100:100, 100:100:100);
    (RIU_CLK => RIU_RD_DATA[4]) = (100:100:100, 100:100:100);
    (RIU_CLK => RIU_RD_DATA[5]) = (100:100:100, 100:100:100);
    (RIU_CLK => RIU_RD_DATA[6]) = (100:100:100, 100:100:100);
    (RIU_CLK => RIU_RD_DATA[7]) = (100:100:100, 100:100:100);
    (RIU_CLK => RIU_RD_DATA[8]) = (100:100:100, 100:100:100);
    (RIU_CLK => RIU_RD_DATA[9]) = (100:100:100, 100:100:100);
    (RIU_CLK => RIU_VALID) = (100:100:100, 100:100:100);
    (RIU_CLK => VTC_RDY) = (100:100:100, 100:100:100);
    (RX_BIT_CTRL_IN0[9] => RX_BIT_CTRL_OUT0[20]) = (0:0:0, 0:0:0);
    (posedge RST => (VTC_RDY +: 0)) = (100:100:100, 100:100:100);
    // (TX_BIT_CTRL_OUT0[26] => DLY_RDY) = (0:0:0, 0:0:0); // error prop output to output
    // (TX_BIT_CTRL_OUT0[26] => VTC_RDY) = (0:0:0, 0:0:0); // error prop output to output
`ifdef XIL_TIMING
    $period (negedge PLL_CLK, 0:0:0, notifier);
    $period (negedge REFCLK, 0:0:0, notifier);
    $period (negedge RIU_CLK, 0:0:0, notifier);
    $period (posedge PLL_CLK, 0:0:0, notifier);
    $period (posedge REFCLK, 0:0:0, notifier);
    $period (posedge RIU_CLK, 0:0:0, notifier);
    $recrem (negedge RST, posedge REFCLK, 0:0:0, 0:0:0, notifier, , , RST_delay, REFCLK_delay);
    $recrem (posedge RST, posedge REFCLK, 0:0:0, 0:0:0, notifier, , , RST_delay, REFCLK_delay);
    $setuphold (posedge PLL_CLK, negedge PHY_RDCS0[0], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_RDCS0_delay[0]);
    $setuphold (posedge PLL_CLK, negedge PHY_RDCS0[1], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_RDCS0_delay[1]);
    $setuphold (posedge PLL_CLK, negedge PHY_RDCS0[2], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_RDCS0_delay[2]);
    $setuphold (posedge PLL_CLK, negedge PHY_RDCS0[3], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_RDCS0_delay[3]);
    $setuphold (posedge PLL_CLK, negedge PHY_RDCS1[0], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_RDCS1_delay[0]);
    $setuphold (posedge PLL_CLK, negedge PHY_RDCS1[1], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_RDCS1_delay[1]);
    $setuphold (posedge PLL_CLK, negedge PHY_RDCS1[2], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_RDCS1_delay[2]);
    $setuphold (posedge PLL_CLK, negedge PHY_RDCS1[3], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_RDCS1_delay[3]);
    $setuphold (posedge PLL_CLK, negedge PHY_RDEN[0], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_RDEN_delay[0]);
    $setuphold (posedge PLL_CLK, negedge PHY_RDEN[1], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_RDEN_delay[1]);
    $setuphold (posedge PLL_CLK, negedge PHY_RDEN[2], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_RDEN_delay[2]);
    $setuphold (posedge PLL_CLK, negedge PHY_RDEN[3], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_RDEN_delay[3]);
    $setuphold (posedge PLL_CLK, negedge PHY_WRCS0[0], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_WRCS0_delay[0]);
    $setuphold (posedge PLL_CLK, negedge PHY_WRCS0[1], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_WRCS0_delay[1]);
    $setuphold (posedge PLL_CLK, negedge PHY_WRCS0[2], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_WRCS0_delay[2]);
    $setuphold (posedge PLL_CLK, negedge PHY_WRCS0[3], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_WRCS0_delay[3]);
    $setuphold (posedge PLL_CLK, negedge PHY_WRCS1[0], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_WRCS1_delay[0]);
    $setuphold (posedge PLL_CLK, negedge PHY_WRCS1[1], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_WRCS1_delay[1]);
    $setuphold (posedge PLL_CLK, negedge PHY_WRCS1[2], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_WRCS1_delay[2]);
    $setuphold (posedge PLL_CLK, negedge PHY_WRCS1[3], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_WRCS1_delay[3]);
    $setuphold (posedge PLL_CLK, negedge TBYTE_IN[0], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, TBYTE_IN_delay[0]);
    $setuphold (posedge PLL_CLK, negedge TBYTE_IN[1], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, TBYTE_IN_delay[1]);
    $setuphold (posedge PLL_CLK, negedge TBYTE_IN[2], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, TBYTE_IN_delay[2]);
    $setuphold (posedge PLL_CLK, negedge TBYTE_IN[3], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, TBYTE_IN_delay[3]);
    $setuphold (posedge PLL_CLK, posedge PHY_RDCS0[0], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_RDCS0_delay[0]);
    $setuphold (posedge PLL_CLK, posedge PHY_RDCS0[1], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_RDCS0_delay[1]);
    $setuphold (posedge PLL_CLK, posedge PHY_RDCS0[2], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_RDCS0_delay[2]);
    $setuphold (posedge PLL_CLK, posedge PHY_RDCS0[3], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_RDCS0_delay[3]);
    $setuphold (posedge PLL_CLK, posedge PHY_RDCS1[0], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_RDCS1_delay[0]);
    $setuphold (posedge PLL_CLK, posedge PHY_RDCS1[1], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_RDCS1_delay[1]);
    $setuphold (posedge PLL_CLK, posedge PHY_RDCS1[2], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_RDCS1_delay[2]);
    $setuphold (posedge PLL_CLK, posedge PHY_RDCS1[3], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_RDCS1_delay[3]);
    $setuphold (posedge PLL_CLK, posedge PHY_RDEN[0], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_RDEN_delay[0]);
    $setuphold (posedge PLL_CLK, posedge PHY_RDEN[1], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_RDEN_delay[1]);
    $setuphold (posedge PLL_CLK, posedge PHY_RDEN[2], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_RDEN_delay[2]);
    $setuphold (posedge PLL_CLK, posedge PHY_RDEN[3], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_RDEN_delay[3]);
    $setuphold (posedge PLL_CLK, posedge PHY_WRCS0[0], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_WRCS0_delay[0]);
    $setuphold (posedge PLL_CLK, posedge PHY_WRCS0[1], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_WRCS0_delay[1]);
    $setuphold (posedge PLL_CLK, posedge PHY_WRCS0[2], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_WRCS0_delay[2]);
    $setuphold (posedge PLL_CLK, posedge PHY_WRCS0[3], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_WRCS0_delay[3]);
    $setuphold (posedge PLL_CLK, posedge PHY_WRCS1[0], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_WRCS1_delay[0]);
    $setuphold (posedge PLL_CLK, posedge PHY_WRCS1[1], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_WRCS1_delay[1]);
    $setuphold (posedge PLL_CLK, posedge PHY_WRCS1[2], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_WRCS1_delay[2]);
    $setuphold (posedge PLL_CLK, posedge PHY_WRCS1[3], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, PHY_WRCS1_delay[3]);
    $setuphold (posedge PLL_CLK, posedge TBYTE_IN[0], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, TBYTE_IN_delay[0]);
    $setuphold (posedge PLL_CLK, posedge TBYTE_IN[1], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, TBYTE_IN_delay[1]);
    $setuphold (posedge PLL_CLK, posedge TBYTE_IN[2], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, TBYTE_IN_delay[2]);
    $setuphold (posedge PLL_CLK, posedge TBYTE_IN[3], 0:0:0, 0:0:0, notifier, , , PLL_CLK_delay, TBYTE_IN_delay[3]);
    $setuphold (posedge RIU_CLK, negedge EN_VTC, 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, EN_VTC_delay);
    $setuphold (posedge RIU_CLK, negedge RIU_ADDR[0], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_ADDR_delay[0]);
    $setuphold (posedge RIU_CLK, negedge RIU_ADDR[1], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_ADDR_delay[1]);
    $setuphold (posedge RIU_CLK, negedge RIU_ADDR[2], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_ADDR_delay[2]);
    $setuphold (posedge RIU_CLK, negedge RIU_ADDR[3], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_ADDR_delay[3]);
    $setuphold (posedge RIU_CLK, negedge RIU_ADDR[4], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_ADDR_delay[4]);
    $setuphold (posedge RIU_CLK, negedge RIU_ADDR[5], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_ADDR_delay[5]);
    $setuphold (posedge RIU_CLK, negedge RIU_NIBBLE_SEL, 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_NIBBLE_SEL_delay);
    $setuphold (posedge RIU_CLK, negedge RIU_WR_DATA[0], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[0]);
    $setuphold (posedge RIU_CLK, negedge RIU_WR_DATA[10], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[10]);
    $setuphold (posedge RIU_CLK, negedge RIU_WR_DATA[11], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[11]);
    $setuphold (posedge RIU_CLK, negedge RIU_WR_DATA[12], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[12]);
    $setuphold (posedge RIU_CLK, negedge RIU_WR_DATA[13], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[13]);
    $setuphold (posedge RIU_CLK, negedge RIU_WR_DATA[14], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[14]);
    $setuphold (posedge RIU_CLK, negedge RIU_WR_DATA[15], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[15]);
    $setuphold (posedge RIU_CLK, negedge RIU_WR_DATA[1], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[1]);
    $setuphold (posedge RIU_CLK, negedge RIU_WR_DATA[2], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[2]);
    $setuphold (posedge RIU_CLK, negedge RIU_WR_DATA[3], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[3]);
    $setuphold (posedge RIU_CLK, negedge RIU_WR_DATA[4], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[4]);
    $setuphold (posedge RIU_CLK, negedge RIU_WR_DATA[5], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[5]);
    $setuphold (posedge RIU_CLK, negedge RIU_WR_DATA[6], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[6]);
    $setuphold (posedge RIU_CLK, negedge RIU_WR_DATA[7], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[7]);
    $setuphold (posedge RIU_CLK, negedge RIU_WR_DATA[8], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[8]);
    $setuphold (posedge RIU_CLK, negedge RIU_WR_DATA[9], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[9]);
    $setuphold (posedge RIU_CLK, negedge RIU_WR_EN, 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_EN_delay);
    $setuphold (posedge RIU_CLK, posedge EN_VTC, 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, EN_VTC_delay);
    $setuphold (posedge RIU_CLK, posedge RIU_ADDR[0], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_ADDR_delay[0]);
    $setuphold (posedge RIU_CLK, posedge RIU_ADDR[1], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_ADDR_delay[1]);
    $setuphold (posedge RIU_CLK, posedge RIU_ADDR[2], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_ADDR_delay[2]);
    $setuphold (posedge RIU_CLK, posedge RIU_ADDR[3], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_ADDR_delay[3]);
    $setuphold (posedge RIU_CLK, posedge RIU_ADDR[4], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_ADDR_delay[4]);
    $setuphold (posedge RIU_CLK, posedge RIU_ADDR[5], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_ADDR_delay[5]);
    $setuphold (posedge RIU_CLK, posedge RIU_NIBBLE_SEL, 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_NIBBLE_SEL_delay);
    $setuphold (posedge RIU_CLK, posedge RIU_WR_DATA[0], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[0]);
    $setuphold (posedge RIU_CLK, posedge RIU_WR_DATA[10], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[10]);
    $setuphold (posedge RIU_CLK, posedge RIU_WR_DATA[11], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[11]);
    $setuphold (posedge RIU_CLK, posedge RIU_WR_DATA[12], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[12]);
    $setuphold (posedge RIU_CLK, posedge RIU_WR_DATA[13], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[13]);
    $setuphold (posedge RIU_CLK, posedge RIU_WR_DATA[14], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[14]);
    $setuphold (posedge RIU_CLK, posedge RIU_WR_DATA[15], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[15]);
    $setuphold (posedge RIU_CLK, posedge RIU_WR_DATA[1], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[1]);
    $setuphold (posedge RIU_CLK, posedge RIU_WR_DATA[2], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[2]);
    $setuphold (posedge RIU_CLK, posedge RIU_WR_DATA[3], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[3]);
    $setuphold (posedge RIU_CLK, posedge RIU_WR_DATA[4], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[4]);
    $setuphold (posedge RIU_CLK, posedge RIU_WR_DATA[5], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[5]);
    $setuphold (posedge RIU_CLK, posedge RIU_WR_DATA[6], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[6]);
    $setuphold (posedge RIU_CLK, posedge RIU_WR_DATA[7], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[7]);
    $setuphold (posedge RIU_CLK, posedge RIU_WR_DATA[8], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[8]);
    $setuphold (posedge RIU_CLK, posedge RIU_WR_DATA[9], 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_DATA_delay[9]);
    $setuphold (posedge RIU_CLK, posedge RIU_WR_EN, 0:0:0, 0:0:0, notifier, , , RIU_CLK_delay, RIU_WR_EN_delay);
    $width (negedge PLL_CLK, 0:0:0, 0, notifier);
    $width (negedge REFCLK, 0:0:0, 0, notifier);
    $width (negedge RIU_CLK, 0:0:0, 0, notifier);
    $width (negedge RST, 0:0:0, 0, notifier);
    $width (posedge PLL_CLK, 0:0:0, 0, notifier);
    $width (posedge REFCLK, 0:0:0, 0, notifier);
    $width (posedge RIU_CLK, 0:0:0, 0, notifier);
    $width (posedge RST, 0:0:0, 0, notifier);
`endif
    specparam PATHPULSE$ = 0;
  endspecify

endmodule

`endcelldefine
