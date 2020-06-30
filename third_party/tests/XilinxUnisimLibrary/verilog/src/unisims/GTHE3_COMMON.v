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
// \   \   \/      Version     : 2014.2
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        _no_description_
// /___/   /\      Filename    : GTHE3_COMMON.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//
//    10/22/14 - Added #1 to $finish (CR 808642).
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps

`celldefine

module GTHE3_COMMON #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter [15:0] BIAS_CFG0 = 16'h0000,
  parameter [15:0] BIAS_CFG1 = 16'h0000,
  parameter [15:0] BIAS_CFG2 = 16'h0000,
  parameter [15:0] BIAS_CFG3 = 16'h0040,
  parameter [15:0] BIAS_CFG4 = 16'h0000,
  parameter [9:0] BIAS_CFG_RSVD = 10'b0000000000,
  parameter [15:0] COMMON_CFG0 = 16'h0000,
  parameter [15:0] COMMON_CFG1 = 16'h0000,
  parameter [15:0] POR_CFG = 16'h0004,
  parameter [15:0] QPLL0_CFG0 = 16'h3018,
  parameter [15:0] QPLL0_CFG1 = 16'h0000,
  parameter [15:0] QPLL0_CFG1_G3 = 16'h0020,
  parameter [15:0] QPLL0_CFG2 = 16'h0000,
  parameter [15:0] QPLL0_CFG2_G3 = 16'h0000,
  parameter [15:0] QPLL0_CFG3 = 16'h0120,
  parameter [15:0] QPLL0_CFG4 = 16'h0009,
  parameter [9:0] QPLL0_CP = 10'b0000011111,
  parameter [9:0] QPLL0_CP_G3 = 10'b0000011111,
  parameter integer QPLL0_FBDIV = 66,
  parameter integer QPLL0_FBDIV_G3 = 80,
  parameter [15:0] QPLL0_INIT_CFG0 = 16'h0000,
  parameter [7:0] QPLL0_INIT_CFG1 = 8'h00,
  parameter [15:0] QPLL0_LOCK_CFG = 16'h01E8,
  parameter [15:0] QPLL0_LOCK_CFG_G3 = 16'h01E8,
  parameter [9:0] QPLL0_LPF = 10'b1111111111,
  parameter [9:0] QPLL0_LPF_G3 = 10'b1111111111,
  parameter integer QPLL0_REFCLK_DIV = 2,
  parameter [15:0] QPLL0_SDM_CFG0 = 16'b0000000000000000,
  parameter [15:0] QPLL0_SDM_CFG1 = 16'b0000000000000000,
  parameter [15:0] QPLL0_SDM_CFG2 = 16'b0000000000000000,
  parameter [15:0] QPLL1_CFG0 = 16'h3018,
  parameter [15:0] QPLL1_CFG1 = 16'h0000,
  parameter [15:0] QPLL1_CFG1_G3 = 16'h0020,
  parameter [15:0] QPLL1_CFG2 = 16'h0000,
  parameter [15:0] QPLL1_CFG2_G3 = 16'h0000,
  parameter [15:0] QPLL1_CFG3 = 16'h0120,
  parameter [15:0] QPLL1_CFG4 = 16'h0009,
  parameter [9:0] QPLL1_CP = 10'b0000011111,
  parameter [9:0] QPLL1_CP_G3 = 10'b0000011111,
  parameter integer QPLL1_FBDIV = 66,
  parameter integer QPLL1_FBDIV_G3 = 80,
  parameter [15:0] QPLL1_INIT_CFG0 = 16'h0000,
  parameter [7:0] QPLL1_INIT_CFG1 = 8'h00,
  parameter [15:0] QPLL1_LOCK_CFG = 16'h01E8,
  parameter [15:0] QPLL1_LOCK_CFG_G3 = 16'h21E8,
  parameter [9:0] QPLL1_LPF = 10'b1111111111,
  parameter [9:0] QPLL1_LPF_G3 = 10'b1111111111,
  parameter integer QPLL1_REFCLK_DIV = 2,
  parameter [15:0] QPLL1_SDM_CFG0 = 16'b0000000000000000,
  parameter [15:0] QPLL1_SDM_CFG1 = 16'b0000000000000000,
  parameter [15:0] QPLL1_SDM_CFG2 = 16'b0000000000000000,
  parameter [15:0] RSVD_ATTR0 = 16'h0000,
  parameter [15:0] RSVD_ATTR1 = 16'h0000,
  parameter [15:0] RSVD_ATTR2 = 16'h0000,
  parameter [15:0] RSVD_ATTR3 = 16'h0000,
  parameter [1:0] RXRECCLKOUT0_SEL = 2'b00,
  parameter [1:0] RXRECCLKOUT1_SEL = 2'b00,
  parameter [0:0] SARC_EN = 1'b1,
  parameter [0:0] SARC_SEL = 1'b0,
  parameter [15:0] SDM0DATA1_0 = 16'b0000000000000000,
  parameter [8:0] SDM0DATA1_1 = 9'b000000000,
  parameter [15:0] SDM0INITSEED0_0 = 16'b0000000000000000,
  parameter [8:0] SDM0INITSEED0_1 = 9'b000000000,
  parameter [0:0] SDM0_DATA_PIN_SEL = 1'b0,
  parameter [0:0] SDM0_WIDTH_PIN_SEL = 1'b0,
  parameter [15:0] SDM1DATA1_0 = 16'b0000000000000000,
  parameter [8:0] SDM1DATA1_1 = 9'b000000000,
  parameter [15:0] SDM1INITSEED0_0 = 16'b0000000000000000,
  parameter [8:0] SDM1INITSEED0_1 = 9'b000000000,
  parameter [0:0] SDM1_DATA_PIN_SEL = 1'b0,
  parameter [0:0] SDM1_WIDTH_PIN_SEL = 1'b0,
  parameter SIM_MODE = "FAST",
  parameter SIM_RESET_SPEEDUP = "TRUE",
  parameter integer SIM_VERSION = 2
)(
  output [15:0] DRPDO,
  output DRPRDY,
  output [7:0] PMARSVDOUT0,
  output [7:0] PMARSVDOUT1,
  output QPLL0FBCLKLOST,
  output QPLL0LOCK,
  output QPLL0OUTCLK,
  output QPLL0OUTREFCLK,
  output QPLL0REFCLKLOST,
  output QPLL1FBCLKLOST,
  output QPLL1LOCK,
  output QPLL1OUTCLK,
  output QPLL1OUTREFCLK,
  output QPLL1REFCLKLOST,
  output [7:0] QPLLDMONITOR0,
  output [7:0] QPLLDMONITOR1,
  output REFCLKOUTMONITOR0,
  output REFCLKOUTMONITOR1,
  output [1:0] RXRECCLK0_SEL,
  output [1:0] RXRECCLK1_SEL,

  input BGBYPASSB,
  input BGMONITORENB,
  input BGPDB,
  input [4:0] BGRCALOVRD,
  input BGRCALOVRDENB,
  input [8:0] DRPADDR,
  input DRPCLK,
  input [15:0] DRPDI,
  input DRPEN,
  input DRPWE,
  input GTGREFCLK0,
  input GTGREFCLK1,
  input GTNORTHREFCLK00,
  input GTNORTHREFCLK01,
  input GTNORTHREFCLK10,
  input GTNORTHREFCLK11,
  input GTREFCLK00,
  input GTREFCLK01,
  input GTREFCLK10,
  input GTREFCLK11,
  input GTSOUTHREFCLK00,
  input GTSOUTHREFCLK01,
  input GTSOUTHREFCLK10,
  input GTSOUTHREFCLK11,
  input [7:0] PMARSVD0,
  input [7:0] PMARSVD1,
  input QPLL0CLKRSVD0,
  input QPLL0CLKRSVD1,
  input QPLL0LOCKDETCLK,
  input QPLL0LOCKEN,
  input QPLL0PD,
  input [2:0] QPLL0REFCLKSEL,
  input QPLL0RESET,
  input QPLL1CLKRSVD0,
  input QPLL1CLKRSVD1,
  input QPLL1LOCKDETCLK,
  input QPLL1LOCKEN,
  input QPLL1PD,
  input [2:0] QPLL1REFCLKSEL,
  input QPLL1RESET,
  input [7:0] QPLLRSVD1,
  input [4:0] QPLLRSVD2,
  input [4:0] QPLLRSVD3,
  input [7:0] QPLLRSVD4,
  input RCALENB
);
  
// define constants
  localparam MODULE_NAME = "GTHE3_COMMON";
  localparam in_delay    = 0;
  localparam out_delay   = 0;
  localparam inclk_delay    = 0;
  localparam outclk_delay   = 0;

// include dynamic registers - XILINX test only
  reg trig_attr = 1'b0;
`ifdef XIL_DR
  `include "GTHE3_COMMON_dr.v"
`else
  localparam [15:0] BIAS_CFG0_REG = BIAS_CFG0;
  localparam [15:0] BIAS_CFG1_REG = BIAS_CFG1;
  localparam [15:0] BIAS_CFG2_REG = BIAS_CFG2;
  localparam [15:0] BIAS_CFG3_REG = BIAS_CFG3;
  localparam [15:0] BIAS_CFG4_REG = BIAS_CFG4;
  localparam [9:0] BIAS_CFG_RSVD_REG = BIAS_CFG_RSVD;
  localparam [15:0] COMMON_CFG0_REG = COMMON_CFG0;
  localparam [15:0] COMMON_CFG1_REG = COMMON_CFG1;
  localparam [15:0] POR_CFG_REG = POR_CFG;
  localparam [15:0] QPLL0_CFG0_REG = QPLL0_CFG0;
  localparam [15:0] QPLL0_CFG1_REG = QPLL0_CFG1;
  localparam [15:0] QPLL0_CFG1_G3_REG = QPLL0_CFG1_G3;
  localparam [15:0] QPLL0_CFG2_REG = QPLL0_CFG2;
  localparam [15:0] QPLL0_CFG2_G3_REG = QPLL0_CFG2_G3;
  localparam [15:0] QPLL0_CFG3_REG = QPLL0_CFG3;
  localparam [15:0] QPLL0_CFG4_REG = QPLL0_CFG4;
  localparam [9:0] QPLL0_CP_REG = QPLL0_CP;
  localparam [9:0] QPLL0_CP_G3_REG = QPLL0_CP_G3;
  localparam [7:0] QPLL0_FBDIV_REG = QPLL0_FBDIV;
  localparam [7:0] QPLL0_FBDIV_G3_REG = QPLL0_FBDIV_G3;
  localparam [15:0] QPLL0_INIT_CFG0_REG = QPLL0_INIT_CFG0;
  localparam [7:0] QPLL0_INIT_CFG1_REG = QPLL0_INIT_CFG1;
  localparam [15:0] QPLL0_LOCK_CFG_REG = QPLL0_LOCK_CFG;
  localparam [15:0] QPLL0_LOCK_CFG_G3_REG = QPLL0_LOCK_CFG_G3;
  localparam [9:0] QPLL0_LPF_REG = QPLL0_LPF;
  localparam [9:0] QPLL0_LPF_G3_REG = QPLL0_LPF_G3;
  localparam [4:0] QPLL0_REFCLK_DIV_REG = QPLL0_REFCLK_DIV;
  localparam [15:0] QPLL0_SDM_CFG0_REG = QPLL0_SDM_CFG0;
  localparam [15:0] QPLL0_SDM_CFG1_REG = QPLL0_SDM_CFG1;
  localparam [15:0] QPLL0_SDM_CFG2_REG = QPLL0_SDM_CFG2;
  localparam [15:0] QPLL1_CFG0_REG = QPLL1_CFG0;
  localparam [15:0] QPLL1_CFG1_REG = QPLL1_CFG1;
  localparam [15:0] QPLL1_CFG1_G3_REG = QPLL1_CFG1_G3;
  localparam [15:0] QPLL1_CFG2_REG = QPLL1_CFG2;
  localparam [15:0] QPLL1_CFG2_G3_REG = QPLL1_CFG2_G3;
  localparam [15:0] QPLL1_CFG3_REG = QPLL1_CFG3;
  localparam [15:0] QPLL1_CFG4_REG = QPLL1_CFG4;
  localparam [9:0] QPLL1_CP_REG = QPLL1_CP;
  localparam [9:0] QPLL1_CP_G3_REG = QPLL1_CP_G3;
  localparam [7:0] QPLL1_FBDIV_REG = QPLL1_FBDIV;
  localparam [7:0] QPLL1_FBDIV_G3_REG = QPLL1_FBDIV_G3;
  localparam [15:0] QPLL1_INIT_CFG0_REG = QPLL1_INIT_CFG0;
  localparam [7:0] QPLL1_INIT_CFG1_REG = QPLL1_INIT_CFG1;
  localparam [15:0] QPLL1_LOCK_CFG_REG = QPLL1_LOCK_CFG;
  localparam [15:0] QPLL1_LOCK_CFG_G3_REG = QPLL1_LOCK_CFG_G3;
  localparam [9:0] QPLL1_LPF_REG = QPLL1_LPF;
  localparam [9:0] QPLL1_LPF_G3_REG = QPLL1_LPF_G3;
  localparam [4:0] QPLL1_REFCLK_DIV_REG = QPLL1_REFCLK_DIV;
  localparam [15:0] QPLL1_SDM_CFG0_REG = QPLL1_SDM_CFG0;
  localparam [15:0] QPLL1_SDM_CFG1_REG = QPLL1_SDM_CFG1;
  localparam [15:0] QPLL1_SDM_CFG2_REG = QPLL1_SDM_CFG2;
  localparam [15:0] RSVD_ATTR0_REG = RSVD_ATTR0;
  localparam [15:0] RSVD_ATTR1_REG = RSVD_ATTR1;
  localparam [15:0] RSVD_ATTR2_REG = RSVD_ATTR2;
  localparam [15:0] RSVD_ATTR3_REG = RSVD_ATTR3;
  localparam [1:0] RXRECCLKOUT0_SEL_REG = RXRECCLKOUT0_SEL;
  localparam [1:0] RXRECCLKOUT1_SEL_REG = RXRECCLKOUT1_SEL;
  localparam [0:0] SARC_EN_REG = SARC_EN;
  localparam [0:0] SARC_SEL_REG = SARC_SEL;
  localparam [15:0] SDM0DATA1_0_REG = SDM0DATA1_0;
  localparam [8:0] SDM0DATA1_1_REG = SDM0DATA1_1;
  localparam [15:0] SDM0INITSEED0_0_REG = SDM0INITSEED0_0;
  localparam [8:0] SDM0INITSEED0_1_REG = SDM0INITSEED0_1;
  localparam [0:0] SDM0_DATA_PIN_SEL_REG = SDM0_DATA_PIN_SEL;
  localparam [0:0] SDM0_WIDTH_PIN_SEL_REG = SDM0_WIDTH_PIN_SEL;
  localparam [15:0] SDM1DATA1_0_REG = SDM1DATA1_0;
  localparam [8:0] SDM1DATA1_1_REG = SDM1DATA1_1;
  localparam [15:0] SDM1INITSEED0_0_REG = SDM1INITSEED0_0;
  localparam [8:0] SDM1INITSEED0_1_REG = SDM1INITSEED0_1;
  localparam [0:0] SDM1_DATA_PIN_SEL_REG = SDM1_DATA_PIN_SEL;
  localparam [0:0] SDM1_WIDTH_PIN_SEL_REG = SDM1_WIDTH_PIN_SEL;
  localparam [80:1] SIM_MODE_REG = SIM_MODE;
  localparam [40:1] SIM_RESET_SPEEDUP_REG = SIM_RESET_SPEEDUP;
  localparam [1:0] SIM_VERSION_REG = SIM_VERSION;
`endif

  localparam [0:0] AEN_BGBS0_REG = 1'b0;
  localparam [0:0] AEN_BGBS1_REG = 1'b0;
  localparam [0:0] AEN_MASTER0_REG = 1'b0;
  localparam [0:0] AEN_MASTER1_REG = 1'b0;
  localparam [0:0] AEN_PD0_REG = 1'b0;
  localparam [0:0] AEN_PD1_REG = 1'b0;
  localparam [0:0] AEN_QPLL0_REG = 1'b0;
  localparam [0:0] AEN_QPLL1_REG = 1'b0;
  localparam [0:0] AEN_REFCLK0_REG = 1'b0;
  localparam [0:0] AEN_REFCLK1_REG = 1'b0;
  localparam [0:0] AEN_RESET0_REG = 1'b0;
  localparam [0:0] AEN_RESET1_REG = 1'b0;
  localparam [3:0] AQDMUXSEL1_REG = 4'b0000;
  localparam [3:0] AVCC_SENSE_SEL_REG = 4'b0000;
  localparam [3:0] AVTT_SENSE_SEL_REG = 4'b0000;
  localparam [0:0] A_BGMONITOREN_REG = 1'b0;
  localparam [0:0] A_BGPD_REG = 1'b0;
  localparam [0:0] A_GTREFCLKPD0_REG = 1'b0;
  localparam [0:0] A_GTREFCLKPD1_REG = 1'b0;
  localparam [0:0] A_QPLL0LOCKEN_REG = 1'b0;
  localparam [0:0] A_QPLL0PD_REG = 1'b0;
  localparam [0:0] A_QPLL0RESET_REG = 1'b0;
  localparam [0:0] A_QPLL1LOCKEN_REG = 1'b0;
  localparam [0:0] A_QPLL1PD_REG = 1'b0;
  localparam [0:0] A_QPLL1RESET_REG = 1'b0;
  localparam [1:0] COMMON_AMUX_SEL0_REG = 2'b00;
  localparam [1:0] COMMON_AMUX_SEL1_REG = 2'b00;
  localparam [0:0] COMMON_INSTANTIATED_REG = 1'b1;
  localparam [15:0] PPF0_CFG_REG = 16'h0000;
  localparam [15:0] PPF1_CFG_REG = 16'h0000;
  localparam [2:0] QPLL0_AMONITOR_SEL_REG = 3'b000;
  localparam [2:0] QPLL1_AMONITOR_SEL_REG = 3'b000;
  localparam [0:0] RCALSAP_TESTEN_REG = 1'b0;
  localparam [0:0] RCAL_APROBE_REG = 1'b0;
  localparam [0:0] REFCLK0_EN_DC_COUP_REG = 1'b0;
  localparam [0:0] REFCLK0_VCM_HIGH_REG = 1'b0;
  localparam [0:0] REFCLK0_VCM_LOW_REG = 1'b0;
  localparam [0:0] REFCLK1_EN_DC_COUP_REG = 1'b0;
  localparam [0:0] REFCLK1_VCM_HIGH_REG = 1'b0;
  localparam [0:0] REFCLK1_VCM_LOW_REG = 1'b0;
  localparam [1:0] VCCAUX_SENSE_SEL_REG = 2'b00;

`ifdef XIL_ATTR_TEST
  reg attr_test = 1'b1;
`else
  reg attr_test = 1'b0;
`endif
  reg attr_err = 1'b0;
  tri0 glblGSR = glbl.GSR;

  wire DRPRDY_out;
  wire QPLL0FBCLKLOST_out;
  wire QPLL0LOCK_out;
  wire QPLL0OUTCLK_out;
  wire QPLL0OUTREFCLK_out;
  wire QPLL0REFCLKLOST_out;
  wire QPLL1FBCLKLOST_out;
  wire QPLL1LOCK_out;
  wire QPLL1OUTCLK_out;
  wire QPLL1OUTREFCLK_out;
  wire QPLL1REFCLKLOST_out;
  wire REFCLKOUTMONITOR0_out;
  wire REFCLKOUTMONITOR1_out;
  wire [15:0] DRPDO_out;
  wire [1:0] RXRECCLK0_SEL_out;
  wire [1:0] RXRECCLK1_SEL_out;
  wire [3:0] SARCCLK_out;
  wire [7:0] PMARSVDOUT0_out;
  wire [7:0] PMARSVDOUT1_out;
  wire [7:0] PMASCANOUT_out;
  wire [7:0] QPLLDMONITOR0_out;
  wire [7:0] QPLLDMONITOR1_out;

  wire DRPRDY_delay;
  wire QPLL0FBCLKLOST_delay;
  wire QPLL0LOCK_delay;
  wire QPLL0OUTCLK_delay;
  wire QPLL0OUTREFCLK_delay;
  wire QPLL0REFCLKLOST_delay;
  wire QPLL1FBCLKLOST_delay;
  wire QPLL1LOCK_delay;
  wire QPLL1OUTCLK_delay;
  wire QPLL1OUTREFCLK_delay;
  wire QPLL1REFCLKLOST_delay;
  wire REFCLKOUTMONITOR0_delay;
  wire REFCLKOUTMONITOR1_delay;
  wire [15:0] DRPDO_delay;
  wire [1:0] RXRECCLK0_SEL_delay;
  wire [1:0] RXRECCLK1_SEL_delay;
  wire [7:0] PMARSVDOUT0_delay;
  wire [7:0] PMARSVDOUT1_delay;
  wire [7:0] QPLLDMONITOR0_delay;
  wire [7:0] QPLLDMONITOR1_delay;

  wire BGBYPASSB_in;
  wire BGMONITORENB_in;
  wire BGPDB_in;
  wire BGRCALOVRDENB_in;
  wire DRPCLK_in;
  wire DRPEN_in;
  wire DRPWE_in;
  wire GTGREFCLK0_in;
  wire GTGREFCLK1_in;
  wire GTNORTHREFCLK00_in;
  wire GTNORTHREFCLK01_in;
  wire GTNORTHREFCLK10_in;
  wire GTNORTHREFCLK11_in;
  wire GTREFCLK00_in;
  wire GTREFCLK01_in;
  wire GTREFCLK10_in;
  wire GTREFCLK11_in;
  wire GTSOUTHREFCLK00_in;
  wire GTSOUTHREFCLK01_in;
  wire GTSOUTHREFCLK10_in;
  wire GTSOUTHREFCLK11_in;
  wire PMASCANENB_in;
  wire QDPMASCANMODEB_in;
  wire QDPMASCANRSTEN_in;
  wire QPLL0CLKRSVD0_in;
  wire QPLL0CLKRSVD1_in;
  wire QPLL0LOCKDETCLK_in;
  wire QPLL0LOCKEN_in;
  wire QPLL0PD_in;
  wire QPLL0RESET_in;
  wire QPLL1CLKRSVD0_in;
  wire QPLL1CLKRSVD1_in;
  wire QPLL1LOCKDETCLK_in;
  wire QPLL1LOCKEN_in;
  wire QPLL1PD_in;
  wire QPLL1RESET_in;
  wire RCALENB_in;
  wire [15:0] DRPDI_in;
  wire [2:0] QPLL0REFCLKSEL_in;
  wire [2:0] QPLL1REFCLKSEL_in;
  wire [3:0] RXRECCLK_in;
  wire [4:0] BGRCALOVRD_in;
  wire [4:0] QPLLRSVD2_in;
  wire [4:0] QPLLRSVD3_in;
  wire [7:0] PMARSVD0_in;
  wire [7:0] PMARSVD1_in;
  wire [7:0] PMASCANCLK_in;
  wire [7:0] PMASCANIN_in;
  wire [7:0] QPLLRSVD1_in;
  wire [7:0] QPLLRSVD4_in;
  wire [8:0] DRPADDR_in;

  wire BGBYPASSB_delay;
  wire BGMONITORENB_delay;
  wire BGPDB_delay;
  wire BGRCALOVRDENB_delay;
  wire DRPCLK_delay;
  wire DRPEN_delay;
  wire DRPWE_delay;
  wire GTGREFCLK0_delay;
  wire GTGREFCLK1_delay;
  wire GTNORTHREFCLK00_delay;
  wire GTNORTHREFCLK01_delay;
  wire GTNORTHREFCLK10_delay;
  wire GTNORTHREFCLK11_delay;
  wire GTREFCLK00_delay;
  wire GTREFCLK01_delay;
  wire GTREFCLK10_delay;
  wire GTREFCLK11_delay;
  wire GTSOUTHREFCLK00_delay;
  wire GTSOUTHREFCLK01_delay;
  wire GTSOUTHREFCLK10_delay;
  wire GTSOUTHREFCLK11_delay;
  wire QPLL0CLKRSVD0_delay;
  wire QPLL0CLKRSVD1_delay;
  wire QPLL0LOCKDETCLK_delay;
  wire QPLL0LOCKEN_delay;
  wire QPLL0PD_delay;
  wire QPLL0RESET_delay;
  wire QPLL1CLKRSVD0_delay;
  wire QPLL1CLKRSVD1_delay;
  wire QPLL1LOCKDETCLK_delay;
  wire QPLL1LOCKEN_delay;
  wire QPLL1PD_delay;
  wire QPLL1RESET_delay;
  wire RCALENB_delay;
  wire [15:0] DRPDI_delay;
  wire [2:0] QPLL0REFCLKSEL_delay;
  wire [2:0] QPLL1REFCLKSEL_delay;
  wire [4:0] BGRCALOVRD_delay;
  wire [4:0] QPLLRSVD2_delay;
  wire [4:0] QPLLRSVD3_delay;
  wire [7:0] PMARSVD0_delay;
  wire [7:0] PMARSVD1_delay;
  wire [7:0] QPLLRSVD1_delay;
  wire [7:0] QPLLRSVD4_delay;
  wire [8:0] DRPADDR_delay;

  assign #(out_delay) DRPDO = DRPDO_delay;
  assign #(out_delay) DRPRDY = DRPRDY_delay;
  assign #(out_delay) PMARSVDOUT0 = PMARSVDOUT0_delay;
  assign #(out_delay) PMARSVDOUT1 = PMARSVDOUT1_delay;
  assign #(out_delay) QPLL0FBCLKLOST = QPLL0FBCLKLOST_delay;
  assign #(out_delay) QPLL0LOCK = QPLL0LOCK_delay;
  assign #(out_delay) QPLL0OUTCLK = QPLL0OUTCLK_delay;
  assign #(out_delay) QPLL0OUTREFCLK = QPLL0OUTREFCLK_delay;
  assign #(out_delay) QPLL0REFCLKLOST = QPLL0REFCLKLOST_delay;
  assign #(out_delay) QPLL1FBCLKLOST = QPLL1FBCLKLOST_delay;
  assign #(out_delay) QPLL1LOCK = QPLL1LOCK_delay;
  assign #(out_delay) QPLL1OUTCLK = QPLL1OUTCLK_delay;
  assign #(out_delay) QPLL1OUTREFCLK = QPLL1OUTREFCLK_delay;
  assign #(out_delay) QPLL1REFCLKLOST = QPLL1REFCLKLOST_delay;
  assign #(out_delay) QPLLDMONITOR0 = QPLLDMONITOR0_delay;
  assign #(out_delay) QPLLDMONITOR1 = QPLLDMONITOR1_delay;
  assign #(out_delay) REFCLKOUTMONITOR0 = REFCLKOUTMONITOR0_delay;
  assign #(out_delay) REFCLKOUTMONITOR1 = REFCLKOUTMONITOR1_delay;
  assign #(out_delay) RXRECCLK0_SEL = RXRECCLK0_SEL_delay;
  assign #(out_delay) RXRECCLK1_SEL = RXRECCLK1_SEL_delay;

`ifdef XIL_TIMING
  reg notifier;
`endif

`ifndef XIL_TIMING // inputs with timing checks
  assign #(inclk_delay) DRPCLK_delay = DRPCLK;

  assign #(in_delay) DRPADDR_delay = DRPADDR;
  assign #(in_delay) DRPDI_delay = DRPDI;
  assign #(in_delay) DRPEN_delay = DRPEN;
  assign #(in_delay) DRPWE_delay = DRPWE;
`endif

// inputs with no timing checks
  assign #(inclk_delay) GTGREFCLK0_delay = GTGREFCLK0;
  assign #(inclk_delay) GTGREFCLK1_delay = GTGREFCLK1;
  assign #(inclk_delay) GTNORTHREFCLK00_delay = GTNORTHREFCLK00;
  assign #(inclk_delay) GTNORTHREFCLK01_delay = GTNORTHREFCLK01;
  assign #(inclk_delay) GTNORTHREFCLK10_delay = GTNORTHREFCLK10;
  assign #(inclk_delay) GTNORTHREFCLK11_delay = GTNORTHREFCLK11;
  assign #(inclk_delay) GTREFCLK00_delay = GTREFCLK00;
  assign #(inclk_delay) GTREFCLK01_delay = GTREFCLK01;
  assign #(inclk_delay) GTREFCLK10_delay = GTREFCLK10;
  assign #(inclk_delay) GTREFCLK11_delay = GTREFCLK11;
  assign #(inclk_delay) GTSOUTHREFCLK00_delay = GTSOUTHREFCLK00;
  assign #(inclk_delay) GTSOUTHREFCLK01_delay = GTSOUTHREFCLK01;
  assign #(inclk_delay) GTSOUTHREFCLK10_delay = GTSOUTHREFCLK10;
  assign #(inclk_delay) GTSOUTHREFCLK11_delay = GTSOUTHREFCLK11;
  assign #(inclk_delay) QPLL0CLKRSVD0_delay = QPLL0CLKRSVD0;
  assign #(inclk_delay) QPLL0CLKRSVD1_delay = QPLL0CLKRSVD1;
  assign #(inclk_delay) QPLL0LOCKDETCLK_delay = QPLL0LOCKDETCLK;
  assign #(inclk_delay) QPLL1CLKRSVD0_delay = QPLL1CLKRSVD0;
  assign #(inclk_delay) QPLL1CLKRSVD1_delay = QPLL1CLKRSVD1;
  assign #(inclk_delay) QPLL1LOCKDETCLK_delay = QPLL1LOCKDETCLK;

  assign #(in_delay) BGBYPASSB_delay = BGBYPASSB;
  assign #(in_delay) BGMONITORENB_delay = BGMONITORENB;
  assign #(in_delay) BGPDB_delay = BGPDB;
  assign #(in_delay) BGRCALOVRDENB_delay = BGRCALOVRDENB;
  assign #(in_delay) BGRCALOVRD_delay = BGRCALOVRD;
  assign #(in_delay) PMARSVD0_delay = PMARSVD0;
  assign #(in_delay) PMARSVD1_delay = PMARSVD1;
  assign #(in_delay) QPLL0LOCKEN_delay = QPLL0LOCKEN;
  assign #(in_delay) QPLL0PD_delay = QPLL0PD;
  assign #(in_delay) QPLL0REFCLKSEL_delay = QPLL0REFCLKSEL;
  assign #(in_delay) QPLL0RESET_delay = QPLL0RESET;
  assign #(in_delay) QPLL1LOCKEN_delay = QPLL1LOCKEN;
  assign #(in_delay) QPLL1PD_delay = QPLL1PD;
  assign #(in_delay) QPLL1REFCLKSEL_delay = QPLL1REFCLKSEL;
  assign #(in_delay) QPLL1RESET_delay = QPLL1RESET;
  assign #(in_delay) QPLLRSVD1_delay = QPLLRSVD1;
  assign #(in_delay) QPLLRSVD2_delay = QPLLRSVD2;
  assign #(in_delay) QPLLRSVD3_delay = QPLLRSVD3;
  assign #(in_delay) QPLLRSVD4_delay = QPLLRSVD4;
  assign #(in_delay) RCALENB_delay = RCALENB;

  assign DRPDO_delay = DRPDO_out;
  assign DRPRDY_delay = DRPRDY_out;
  assign PMARSVDOUT0_delay = PMARSVDOUT0_out;
  assign PMARSVDOUT1_delay = PMARSVDOUT1_out;
  assign QPLL0FBCLKLOST_delay = QPLL0FBCLKLOST_out;
  assign QPLL0LOCK_delay = QPLL0LOCK_out;
  assign QPLL0OUTCLK_delay = QPLL0OUTCLK_out;
  assign QPLL0OUTREFCLK_delay = QPLL0OUTREFCLK_out;
  assign QPLL0REFCLKLOST_delay = QPLL0REFCLKLOST_out;
  assign QPLL1FBCLKLOST_delay = QPLL1FBCLKLOST_out;
  assign QPLL1LOCK_delay = QPLL1LOCK_out;
  assign QPLL1OUTCLK_delay = QPLL1OUTCLK_out;
  assign QPLL1OUTREFCLK_delay = QPLL1OUTREFCLK_out;
  assign QPLL1REFCLKLOST_delay = QPLL1REFCLKLOST_out;
  assign QPLLDMONITOR0_delay = QPLLDMONITOR0_out;
  assign QPLLDMONITOR1_delay = QPLLDMONITOR1_out;
  assign REFCLKOUTMONITOR0_delay = REFCLKOUTMONITOR0_out;
  assign REFCLKOUTMONITOR1_delay = REFCLKOUTMONITOR1_out;
  assign RXRECCLK0_SEL_delay = RXRECCLK0_SEL_out;
  assign RXRECCLK1_SEL_delay = RXRECCLK1_SEL_out;

  assign BGBYPASSB_in = BGBYPASSB_delay;
  assign BGMONITORENB_in = BGMONITORENB_delay;
  assign BGPDB_in = BGPDB_delay;
  assign BGRCALOVRDENB_in = BGRCALOVRDENB_delay;
  assign BGRCALOVRD_in = BGRCALOVRD_delay;
  assign DRPADDR_in[0] = (DRPADDR[0] !== 1'bz) && DRPADDR_delay[0]; // rv 0
  assign DRPADDR_in[1] = (DRPADDR[1] !== 1'bz) && DRPADDR_delay[1]; // rv 0
  assign DRPADDR_in[2] = (DRPADDR[2] !== 1'bz) && DRPADDR_delay[2]; // rv 0
  assign DRPADDR_in[3] = (DRPADDR[3] !== 1'bz) && DRPADDR_delay[3]; // rv 0
  assign DRPADDR_in[4] = (DRPADDR[4] !== 1'bz) && DRPADDR_delay[4]; // rv 0
  assign DRPADDR_in[5] = (DRPADDR[5] !== 1'bz) && DRPADDR_delay[5]; // rv 0
  assign DRPADDR_in[6] = (DRPADDR[6] !== 1'bz) && DRPADDR_delay[6]; // rv 0
  assign DRPADDR_in[7] = (DRPADDR[7] !== 1'bz) && DRPADDR_delay[7]; // rv 0
  assign DRPADDR_in[8] = (DRPADDR[8] !== 1'bz) && DRPADDR_delay[8]; // rv 0
  assign DRPCLK_in = (DRPCLK !== 1'bz) && DRPCLK_delay; // rv 0
  assign DRPDI_in[0] = (DRPDI[0] !== 1'bz) && DRPDI_delay[0]; // rv 0
  assign DRPDI_in[10] = (DRPDI[10] !== 1'bz) && DRPDI_delay[10]; // rv 0
  assign DRPDI_in[11] = (DRPDI[11] !== 1'bz) && DRPDI_delay[11]; // rv 0
  assign DRPDI_in[12] = (DRPDI[12] !== 1'bz) && DRPDI_delay[12]; // rv 0
  assign DRPDI_in[13] = (DRPDI[13] !== 1'bz) && DRPDI_delay[13]; // rv 0
  assign DRPDI_in[14] = (DRPDI[14] !== 1'bz) && DRPDI_delay[14]; // rv 0
  assign DRPDI_in[15] = (DRPDI[15] !== 1'bz) && DRPDI_delay[15]; // rv 0
  assign DRPDI_in[1] = (DRPDI[1] !== 1'bz) && DRPDI_delay[1]; // rv 0
  assign DRPDI_in[2] = (DRPDI[2] !== 1'bz) && DRPDI_delay[2]; // rv 0
  assign DRPDI_in[3] = (DRPDI[3] !== 1'bz) && DRPDI_delay[3]; // rv 0
  assign DRPDI_in[4] = (DRPDI[4] !== 1'bz) && DRPDI_delay[4]; // rv 0
  assign DRPDI_in[5] = (DRPDI[5] !== 1'bz) && DRPDI_delay[5]; // rv 0
  assign DRPDI_in[6] = (DRPDI[6] !== 1'bz) && DRPDI_delay[6]; // rv 0
  assign DRPDI_in[7] = (DRPDI[7] !== 1'bz) && DRPDI_delay[7]; // rv 0
  assign DRPDI_in[8] = (DRPDI[8] !== 1'bz) && DRPDI_delay[8]; // rv 0
  assign DRPDI_in[9] = (DRPDI[9] !== 1'bz) && DRPDI_delay[9]; // rv 0
  assign DRPEN_in = (DRPEN !== 1'bz) && DRPEN_delay; // rv 0
  assign DRPWE_in = (DRPWE !== 1'bz) && DRPWE_delay; // rv 0
  assign GTGREFCLK0_in = GTGREFCLK0_delay;
  assign GTGREFCLK1_in = GTGREFCLK1_delay;
  assign GTNORTHREFCLK00_in = GTNORTHREFCLK00_delay;
  assign GTNORTHREFCLK01_in = GTNORTHREFCLK01_delay;
  assign GTNORTHREFCLK10_in = GTNORTHREFCLK10_delay;
  assign GTNORTHREFCLK11_in = GTNORTHREFCLK11_delay;
  assign GTREFCLK00_in = GTREFCLK00_delay;
  assign GTREFCLK01_in = GTREFCLK01_delay;
  assign GTREFCLK10_in = GTREFCLK10_delay;
  assign GTREFCLK11_in = GTREFCLK11_delay;
  assign GTSOUTHREFCLK00_in = GTSOUTHREFCLK00_delay;
  assign GTSOUTHREFCLK01_in = GTSOUTHREFCLK01_delay;
  assign GTSOUTHREFCLK10_in = GTSOUTHREFCLK10_delay;
  assign GTSOUTHREFCLK11_in = GTSOUTHREFCLK11_delay;
  assign PMARSVD0_in[0] = (PMARSVD0[0] !== 1'bz) && PMARSVD0_delay[0]; // rv 0
  assign PMARSVD0_in[1] = (PMARSVD0[1] !== 1'bz) && PMARSVD0_delay[1]; // rv 0
  assign PMARSVD0_in[2] = (PMARSVD0[2] !== 1'bz) && PMARSVD0_delay[2]; // rv 0
  assign PMARSVD0_in[3] = (PMARSVD0[3] !== 1'bz) && PMARSVD0_delay[3]; // rv 0
  assign PMARSVD0_in[4] = (PMARSVD0[4] !== 1'bz) && PMARSVD0_delay[4]; // rv 0
  assign PMARSVD0_in[5] = (PMARSVD0[5] !== 1'bz) && PMARSVD0_delay[5]; // rv 0
  assign PMARSVD0_in[6] = (PMARSVD0[6] !== 1'bz) && PMARSVD0_delay[6]; // rv 0
  assign PMARSVD0_in[7] = (PMARSVD0[7] !== 1'bz) && PMARSVD0_delay[7]; // rv 0
  assign PMARSVD1_in[0] = (PMARSVD1[0] !== 1'bz) && PMARSVD1_delay[0]; // rv 0
  assign PMARSVD1_in[1] = (PMARSVD1[1] !== 1'bz) && PMARSVD1_delay[1]; // rv 0
  assign PMARSVD1_in[2] = (PMARSVD1[2] !== 1'bz) && PMARSVD1_delay[2]; // rv 0
  assign PMARSVD1_in[3] = (PMARSVD1[3] !== 1'bz) && PMARSVD1_delay[3]; // rv 0
  assign PMARSVD1_in[4] = (PMARSVD1[4] !== 1'bz) && PMARSVD1_delay[4]; // rv 0
  assign PMARSVD1_in[5] = (PMARSVD1[5] !== 1'bz) && PMARSVD1_delay[5]; // rv 0
  assign PMARSVD1_in[6] = (PMARSVD1[6] !== 1'bz) && PMARSVD1_delay[6]; // rv 0
  assign PMARSVD1_in[7] = (PMARSVD1[7] !== 1'bz) && PMARSVD1_delay[7]; // rv 0
  assign QPLL0CLKRSVD0_in = (QPLL0CLKRSVD0 === 1'bz) || QPLL0CLKRSVD0_delay; // rv 1
  assign QPLL0CLKRSVD1_in = (QPLL0CLKRSVD1 === 1'bz) || QPLL0CLKRSVD1_delay; // rv 1
  assign QPLL0LOCKDETCLK_in = (QPLL0LOCKDETCLK === 1'bz) || QPLL0LOCKDETCLK_delay; // rv 1
  assign QPLL0LOCKEN_in = (QPLL0LOCKEN !== 1'bz) && QPLL0LOCKEN_delay; // rv 0
  assign QPLL0PD_in = (QPLL0PD !== 1'bz) && QPLL0PD_delay; // rv 0
  assign QPLL0REFCLKSEL_in[0] = (QPLL0REFCLKSEL[0] === 1'bz) || QPLL0REFCLKSEL_delay[0]; // rv 1
  assign QPLL0REFCLKSEL_in[1] = (QPLL0REFCLKSEL[1] !== 1'bz) && QPLL0REFCLKSEL_delay[1]; // rv 0
  assign QPLL0REFCLKSEL_in[2] = (QPLL0REFCLKSEL[2] !== 1'bz) && QPLL0REFCLKSEL_delay[2]; // rv 0
  assign QPLL0RESET_in = (QPLL0RESET !== 1'bz) && QPLL0RESET_delay; // rv 0
  assign QPLL1CLKRSVD0_in = (QPLL1CLKRSVD0 === 1'bz) || QPLL1CLKRSVD0_delay; // rv 1
  assign QPLL1CLKRSVD1_in = (QPLL1CLKRSVD1 === 1'bz) || QPLL1CLKRSVD1_delay; // rv 1
  assign QPLL1LOCKDETCLK_in = (QPLL1LOCKDETCLK === 1'bz) || QPLL1LOCKDETCLK_delay; // rv 1
  assign QPLL1LOCKEN_in = (QPLL1LOCKEN !== 1'bz) && QPLL1LOCKEN_delay; // rv 0
  assign QPLL1PD_in = (QPLL1PD !== 1'bz) && QPLL1PD_delay; // rv 0
  assign QPLL1REFCLKSEL_in[0] = (QPLL1REFCLKSEL[0] === 1'bz) || QPLL1REFCLKSEL_delay[0]; // rv 1
  assign QPLL1REFCLKSEL_in[1] = (QPLL1REFCLKSEL[1] !== 1'bz) && QPLL1REFCLKSEL_delay[1]; // rv 0
  assign QPLL1REFCLKSEL_in[2] = (QPLL1REFCLKSEL[2] !== 1'bz) && QPLL1REFCLKSEL_delay[2]; // rv 0
  assign QPLL1RESET_in = (QPLL1RESET !== 1'bz) && QPLL1RESET_delay; // rv 0
  assign QPLLRSVD1_in[0] = (QPLLRSVD1[0] !== 1'bz) && QPLLRSVD1_delay[0]; // rv 0
  assign QPLLRSVD1_in[1] = (QPLLRSVD1[1] !== 1'bz) && QPLLRSVD1_delay[1]; // rv 0
  assign QPLLRSVD1_in[2] = (QPLLRSVD1[2] !== 1'bz) && QPLLRSVD1_delay[2]; // rv 0
  assign QPLLRSVD1_in[3] = (QPLLRSVD1[3] !== 1'bz) && QPLLRSVD1_delay[3]; // rv 0
  assign QPLLRSVD1_in[4] = (QPLLRSVD1[4] !== 1'bz) && QPLLRSVD1_delay[4]; // rv 0
  assign QPLLRSVD1_in[5] = (QPLLRSVD1[5] !== 1'bz) && QPLLRSVD1_delay[5]; // rv 0
  assign QPLLRSVD1_in[6] = (QPLLRSVD1[6] !== 1'bz) && QPLLRSVD1_delay[6]; // rv 0
  assign QPLLRSVD1_in[7] = (QPLLRSVD1[7] !== 1'bz) && QPLLRSVD1_delay[7]; // rv 0
  assign QPLLRSVD2_in[0] = (QPLLRSVD2[0] !== 1'bz) && QPLLRSVD2_delay[0]; // rv 0
  assign QPLLRSVD2_in[1] = (QPLLRSVD2[1] !== 1'bz) && QPLLRSVD2_delay[1]; // rv 0
  assign QPLLRSVD2_in[2] = (QPLLRSVD2[2] !== 1'bz) && QPLLRSVD2_delay[2]; // rv 0
  assign QPLLRSVD2_in[3] = (QPLLRSVD2[3] !== 1'bz) && QPLLRSVD2_delay[3]; // rv 0
  assign QPLLRSVD2_in[4] = (QPLLRSVD2[4] !== 1'bz) && QPLLRSVD2_delay[4]; // rv 0
  assign QPLLRSVD3_in[0] = (QPLLRSVD3[0] !== 1'bz) && QPLLRSVD3_delay[0]; // rv 0
  assign QPLLRSVD3_in[1] = (QPLLRSVD3[1] !== 1'bz) && QPLLRSVD3_delay[1]; // rv 0
  assign QPLLRSVD3_in[2] = (QPLLRSVD3[2] !== 1'bz) && QPLLRSVD3_delay[2]; // rv 0
  assign QPLLRSVD3_in[3] = (QPLLRSVD3[3] !== 1'bz) && QPLLRSVD3_delay[3]; // rv 0
  assign QPLLRSVD3_in[4] = (QPLLRSVD3[4] !== 1'bz) && QPLLRSVD3_delay[4]; // rv 0
  assign QPLLRSVD4_in[0] = (QPLLRSVD4[0] !== 1'bz) && QPLLRSVD4_delay[0]; // rv 0
  assign QPLLRSVD4_in[1] = (QPLLRSVD4[1] !== 1'bz) && QPLLRSVD4_delay[1]; // rv 0
  assign QPLLRSVD4_in[2] = (QPLLRSVD4[2] !== 1'bz) && QPLLRSVD4_delay[2]; // rv 0
  assign QPLLRSVD4_in[3] = (QPLLRSVD4[3] !== 1'bz) && QPLLRSVD4_delay[3]; // rv 0
  assign QPLLRSVD4_in[4] = (QPLLRSVD4[4] !== 1'bz) && QPLLRSVD4_delay[4]; // rv 0
  assign QPLLRSVD4_in[5] = (QPLLRSVD4[5] !== 1'bz) && QPLLRSVD4_delay[5]; // rv 0
  assign QPLLRSVD4_in[6] = (QPLLRSVD4[6] !== 1'bz) && QPLLRSVD4_delay[6]; // rv 0
  assign QPLLRSVD4_in[7] = (QPLLRSVD4[7] !== 1'bz) && QPLLRSVD4_delay[7]; // rv 0
  assign RCALENB_in = RCALENB_delay;

  initial begin
    #1;
    trig_attr = ~trig_attr;
  end

  always @ (trig_attr) begin
    #1;
    if ((attr_test == 1'b1) ||
        ((QPLL0_FBDIV_REG < 16) || (QPLL0_FBDIV_REG > 160))) begin
      $display("Error: [Unisim %s-150] QPLL0_FBDIV attribute is set to %d.  Legal values for this attribute are 16 to 160. Instance: %m", MODULE_NAME, QPLL0_FBDIV_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((QPLL0_FBDIV_G3_REG < 16) || (QPLL0_FBDIV_G3_REG > 160))) begin
      $display("Error: [Unisim %s-151] QPLL0_FBDIV_G3 attribute is set to %d.  Legal values for this attribute are 16 to 160. Instance: %m", MODULE_NAME, QPLL0_FBDIV_G3_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((QPLL0_REFCLK_DIV_REG != 2) &&
         (QPLL0_REFCLK_DIV_REG != 1) &&
         (QPLL0_REFCLK_DIV_REG != 3) &&
         (QPLL0_REFCLK_DIV_REG != 4) &&
         (QPLL0_REFCLK_DIV_REG != 5) &&
         (QPLL0_REFCLK_DIV_REG != 6) &&
         (QPLL0_REFCLK_DIV_REG != 8) &&
         (QPLL0_REFCLK_DIV_REG != 10) &&
         (QPLL0_REFCLK_DIV_REG != 12) &&
         (QPLL0_REFCLK_DIV_REG != 16) &&
         (QPLL0_REFCLK_DIV_REG != 20))) begin
      $display("Error: [Unisim %s-158] QPLL0_REFCLK_DIV attribute is set to %d.  Legal values for this attribute are 2, 1, 3, 4, 5, 6, 8, 10, 12, 16 or 20. Instance: %m", MODULE_NAME, QPLL0_REFCLK_DIV_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((QPLL1_FBDIV_REG < 16) || (QPLL1_FBDIV_REG > 160))) begin
      $display("Error: [Unisim %s-172] QPLL1_FBDIV attribute is set to %d.  Legal values for this attribute are 16 to 160. Instance: %m", MODULE_NAME, QPLL1_FBDIV_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((QPLL1_FBDIV_G3_REG < 16) || (QPLL1_FBDIV_G3_REG > 160))) begin
      $display("Error: [Unisim %s-173] QPLL1_FBDIV_G3 attribute is set to %d.  Legal values for this attribute are 16 to 160. Instance: %m", MODULE_NAME, QPLL1_FBDIV_G3_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((QPLL1_REFCLK_DIV_REG != 2) &&
         (QPLL1_REFCLK_DIV_REG != 1) &&
         (QPLL1_REFCLK_DIV_REG != 3) &&
         (QPLL1_REFCLK_DIV_REG != 4) &&
         (QPLL1_REFCLK_DIV_REG != 5) &&
         (QPLL1_REFCLK_DIV_REG != 6) &&
         (QPLL1_REFCLK_DIV_REG != 8) &&
         (QPLL1_REFCLK_DIV_REG != 10) &&
         (QPLL1_REFCLK_DIV_REG != 12) &&
         (QPLL1_REFCLK_DIV_REG != 16) &&
         (QPLL1_REFCLK_DIV_REG != 20))) begin
      $display("Error: [Unisim %s-180] QPLL1_REFCLK_DIV attribute is set to %d.  Legal values for this attribute are 2, 1, 3, 4, 5, 6, 8, 10, 12, 16 or 20. Instance: %m", MODULE_NAME, QPLL1_REFCLK_DIV_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        (SIM_MODE_REG != "FAST")) begin
      $display("Error: [Unisim %s-212] SIM_MODE attribute is set to %s.  Legal values for this attribute are FAST. Instance: %m", MODULE_NAME, SIM_MODE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((SIM_RESET_SPEEDUP_REG != "TRUE") &&
         (SIM_RESET_SPEEDUP_REG != "FALSE"))) begin
      $display("Error: [Unisim %s-213] SIM_RESET_SPEEDUP attribute is set to %s.  Legal values for this attribute are TRUE, or FALSE. Instance: %m", MODULE_NAME, SIM_RESET_SPEEDUP_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((SIM_VERSION_REG != 2) &&
         (SIM_VERSION_REG != 1) &&
         (SIM_VERSION_REG != 3))) begin
      $display("Error: [Unisim %s-214] SIM_VERSION attribute is set to %d.  Legal values for this attribute are 2, 1 or 3. Instance: %m", MODULE_NAME, SIM_VERSION_REG);
      attr_err = 1'b1;
    end
    
    if (attr_err == 1'b1) #1 $finish;
  end


  assign PMASCANCLK_in = 8'b11111111; // tie off

  assign PMASCANENB_in = 1'b1; // tie off
  assign PMASCANIN_in = 8'b11111111; // tie off
  assign QDPMASCANMODEB_in = 1'b1; // tie off
  assign QDPMASCANRSTEN_in = 1'b1; // tie off
  assign RXRECCLK_in = 4'b1111; // tie off

  SIP_GTHE3_COMMON #(
    .SIM_RESET_SPEEDUP (SIM_RESET_SPEEDUP_REG),
    .SIM_VERSION (SIM_VERSION_REG)
) SIP_GTHE3_COMMON_INST (
    .AEN_BGBS0 (AEN_BGBS0_REG),
    .AEN_BGBS1 (AEN_BGBS1_REG),
    .AEN_MASTER0 (AEN_MASTER0_REG),
    .AEN_MASTER1 (AEN_MASTER1_REG),
    .AEN_PD0 (AEN_PD0_REG),
    .AEN_PD1 (AEN_PD1_REG),
    .AEN_QPLL0 (AEN_QPLL0_REG),
    .AEN_QPLL1 (AEN_QPLL1_REG),
    .AEN_REFCLK0 (AEN_REFCLK0_REG),
    .AEN_REFCLK1 (AEN_REFCLK1_REG),
    .AEN_RESET0 (AEN_RESET0_REG),
    .AEN_RESET1 (AEN_RESET1_REG),
    .AQDMUXSEL1 (AQDMUXSEL1_REG),
    .AVCC_SENSE_SEL (AVCC_SENSE_SEL_REG),
    .AVTT_SENSE_SEL (AVTT_SENSE_SEL_REG),
    .A_BGMONITOREN (A_BGMONITOREN_REG),
    .A_BGPD (A_BGPD_REG),
    .A_GTREFCLKPD0 (A_GTREFCLKPD0_REG),
    .A_GTREFCLKPD1 (A_GTREFCLKPD1_REG),
    .A_QPLL0LOCKEN (A_QPLL0LOCKEN_REG),
    .A_QPLL0PD (A_QPLL0PD_REG),
    .A_QPLL0RESET (A_QPLL0RESET_REG),
    .A_QPLL1LOCKEN (A_QPLL1LOCKEN_REG),
    .A_QPLL1PD (A_QPLL1PD_REG),
    .A_QPLL1RESET (A_QPLL1RESET_REG),
    .BIAS_CFG0 (BIAS_CFG0_REG),
    .BIAS_CFG1 (BIAS_CFG1_REG),
    .BIAS_CFG2 (BIAS_CFG2_REG),
    .BIAS_CFG3 (BIAS_CFG3_REG),
    .BIAS_CFG4 (BIAS_CFG4_REG),
    .BIAS_CFG_RSVD (BIAS_CFG_RSVD_REG),
    .COMMON_AMUX_SEL0 (COMMON_AMUX_SEL0_REG),
    .COMMON_AMUX_SEL1 (COMMON_AMUX_SEL1_REG),
    .COMMON_CFG0 (COMMON_CFG0_REG),
    .COMMON_CFG1 (COMMON_CFG1_REG),
    .COMMON_INSTANTIATED (COMMON_INSTANTIATED_REG),
    .POR_CFG (POR_CFG_REG),
    .PPF0_CFG (PPF0_CFG_REG),
    .PPF1_CFG (PPF1_CFG_REG),
    .QPLL0_AMONITOR_SEL (QPLL0_AMONITOR_SEL_REG),
    .QPLL0_CFG0 (QPLL0_CFG0_REG),
    .QPLL0_CFG1 (QPLL0_CFG1_REG),
    .QPLL0_CFG1_G3 (QPLL0_CFG1_G3_REG),
    .QPLL0_CFG2 (QPLL0_CFG2_REG),
    .QPLL0_CFG2_G3 (QPLL0_CFG2_G3_REG),
    .QPLL0_CFG3 (QPLL0_CFG3_REG),
    .QPLL0_CFG4 (QPLL0_CFG4_REG),
    .QPLL0_CP (QPLL0_CP_REG),
    .QPLL0_CP_G3 (QPLL0_CP_G3_REG),
    .QPLL0_FBDIV (QPLL0_FBDIV_REG),
    .QPLL0_FBDIV_G3 (QPLL0_FBDIV_G3_REG),
    .QPLL0_INIT_CFG0 (QPLL0_INIT_CFG0_REG),
    .QPLL0_INIT_CFG1 (QPLL0_INIT_CFG1_REG),
    .QPLL0_LOCK_CFG (QPLL0_LOCK_CFG_REG),
    .QPLL0_LOCK_CFG_G3 (QPLL0_LOCK_CFG_G3_REG),
    .QPLL0_LPF (QPLL0_LPF_REG),
    .QPLL0_LPF_G3 (QPLL0_LPF_G3_REG),
    .QPLL0_REFCLK_DIV (QPLL0_REFCLK_DIV_REG),
    .QPLL0_SDM_CFG0 (QPLL0_SDM_CFG0_REG),
    .QPLL0_SDM_CFG1 (QPLL0_SDM_CFG1_REG),
    .QPLL0_SDM_CFG2 (QPLL0_SDM_CFG2_REG),
    .QPLL1_AMONITOR_SEL (QPLL1_AMONITOR_SEL_REG),
    .QPLL1_CFG0 (QPLL1_CFG0_REG),
    .QPLL1_CFG1 (QPLL1_CFG1_REG),
    .QPLL1_CFG1_G3 (QPLL1_CFG1_G3_REG),
    .QPLL1_CFG2 (QPLL1_CFG2_REG),
    .QPLL1_CFG2_G3 (QPLL1_CFG2_G3_REG),
    .QPLL1_CFG3 (QPLL1_CFG3_REG),
    .QPLL1_CFG4 (QPLL1_CFG4_REG),
    .QPLL1_CP (QPLL1_CP_REG),
    .QPLL1_CP_G3 (QPLL1_CP_G3_REG),
    .QPLL1_FBDIV (QPLL1_FBDIV_REG),
    .QPLL1_FBDIV_G3 (QPLL1_FBDIV_G3_REG),
    .QPLL1_INIT_CFG0 (QPLL1_INIT_CFG0_REG),
    .QPLL1_INIT_CFG1 (QPLL1_INIT_CFG1_REG),
    .QPLL1_LOCK_CFG (QPLL1_LOCK_CFG_REG),
    .QPLL1_LOCK_CFG_G3 (QPLL1_LOCK_CFG_G3_REG),
    .QPLL1_LPF (QPLL1_LPF_REG),
    .QPLL1_LPF_G3 (QPLL1_LPF_G3_REG),
    .QPLL1_REFCLK_DIV (QPLL1_REFCLK_DIV_REG),
    .QPLL1_SDM_CFG0 (QPLL1_SDM_CFG0_REG),
    .QPLL1_SDM_CFG1 (QPLL1_SDM_CFG1_REG),
    .QPLL1_SDM_CFG2 (QPLL1_SDM_CFG2_REG),
    .RCALSAP_TESTEN (RCALSAP_TESTEN_REG),
    .RCAL_APROBE (RCAL_APROBE_REG),
    .REFCLK0_EN_DC_COUP (REFCLK0_EN_DC_COUP_REG),
    .REFCLK0_VCM_HIGH (REFCLK0_VCM_HIGH_REG),
    .REFCLK0_VCM_LOW (REFCLK0_VCM_LOW_REG),
    .REFCLK1_EN_DC_COUP (REFCLK1_EN_DC_COUP_REG),
    .REFCLK1_VCM_HIGH (REFCLK1_VCM_HIGH_REG),
    .REFCLK1_VCM_LOW (REFCLK1_VCM_LOW_REG),
    .RSVD_ATTR0 (RSVD_ATTR0_REG),
    .RSVD_ATTR1 (RSVD_ATTR1_REG),
    .RSVD_ATTR2 (RSVD_ATTR2_REG),
    .RSVD_ATTR3 (RSVD_ATTR3_REG),
    .RXRECCLKOUT0_SEL (RXRECCLKOUT0_SEL_REG),
    .RXRECCLKOUT1_SEL (RXRECCLKOUT1_SEL_REG),
    .SARC_EN (SARC_EN_REG),
    .SARC_SEL (SARC_SEL_REG),
    .SDM0DATA1_0 (SDM0DATA1_0_REG),
    .SDM0DATA1_1 (SDM0DATA1_1_REG),
    .SDM0INITSEED0_0 (SDM0INITSEED0_0_REG),
    .SDM0INITSEED0_1 (SDM0INITSEED0_1_REG),
    .SDM0_DATA_PIN_SEL (SDM0_DATA_PIN_SEL_REG),
    .SDM0_WIDTH_PIN_SEL (SDM0_WIDTH_PIN_SEL_REG),
    .SDM1DATA1_0 (SDM1DATA1_0_REG),
    .SDM1DATA1_1 (SDM1DATA1_1_REG),
    .SDM1INITSEED0_0 (SDM1INITSEED0_0_REG),
    .SDM1INITSEED0_1 (SDM1INITSEED0_1_REG),
    .SDM1_DATA_PIN_SEL (SDM1_DATA_PIN_SEL_REG),
    .SDM1_WIDTH_PIN_SEL (SDM1_WIDTH_PIN_SEL_REG),
    .VCCAUX_SENSE_SEL (VCCAUX_SENSE_SEL_REG),
    .DRPDO (DRPDO_out),
    .DRPRDY (DRPRDY_out),
    .PMARSVDOUT0 (PMARSVDOUT0_out),
    .PMARSVDOUT1 (PMARSVDOUT1_out),
    .PMASCANOUT (PMASCANOUT_out),
    .QPLL0FBCLKLOST (QPLL0FBCLKLOST_out),
    .QPLL0LOCK (QPLL0LOCK_out),
    .QPLL0OUTCLK (QPLL0OUTCLK_out),
    .QPLL0OUTREFCLK (QPLL0OUTREFCLK_out),
    .QPLL0REFCLKLOST (QPLL0REFCLKLOST_out),
    .QPLL1FBCLKLOST (QPLL1FBCLKLOST_out),
    .QPLL1LOCK (QPLL1LOCK_out),
    .QPLL1OUTCLK (QPLL1OUTCLK_out),
    .QPLL1OUTREFCLK (QPLL1OUTREFCLK_out),
    .QPLL1REFCLKLOST (QPLL1REFCLKLOST_out),
    .QPLLDMONITOR0 (QPLLDMONITOR0_out),
    .QPLLDMONITOR1 (QPLLDMONITOR1_out),
    .REFCLKOUTMONITOR0 (REFCLKOUTMONITOR0_out),
    .REFCLKOUTMONITOR1 (REFCLKOUTMONITOR1_out),
    .RXRECCLK0_SEL (RXRECCLK0_SEL_out),
    .RXRECCLK1_SEL (RXRECCLK1_SEL_out),
    .SARCCLK (SARCCLK_out),
    .BGBYPASSB (BGBYPASSB_in),
    .BGMONITORENB (BGMONITORENB_in),
    .BGPDB (BGPDB_in),
    .BGRCALOVRD (BGRCALOVRD_in),
    .BGRCALOVRDENB (BGRCALOVRDENB_in),
    .DRPADDR (DRPADDR_in),
    .DRPCLK (DRPCLK_in),
    .DRPDI (DRPDI_in),
    .DRPEN (DRPEN_in),
    .DRPWE (DRPWE_in),
    .GTGREFCLK0 (GTGREFCLK0_in),
    .GTGREFCLK1 (GTGREFCLK1_in),
    .GTNORTHREFCLK00 (GTNORTHREFCLK00_in),
    .GTNORTHREFCLK01 (GTNORTHREFCLK01_in),
    .GTNORTHREFCLK10 (GTNORTHREFCLK10_in),
    .GTNORTHREFCLK11 (GTNORTHREFCLK11_in),
    .GTREFCLK00 (GTREFCLK00_in),
    .GTREFCLK01 (GTREFCLK01_in),
    .GTREFCLK10 (GTREFCLK10_in),
    .GTREFCLK11 (GTREFCLK11_in),
    .GTSOUTHREFCLK00 (GTSOUTHREFCLK00_in),
    .GTSOUTHREFCLK01 (GTSOUTHREFCLK01_in),
    .GTSOUTHREFCLK10 (GTSOUTHREFCLK10_in),
    .GTSOUTHREFCLK11 (GTSOUTHREFCLK11_in),
    .PMARSVD0 (PMARSVD0_in),
    .PMARSVD1 (PMARSVD1_in),
    .PMASCANCLK (PMASCANCLK_in),
    .PMASCANENB (PMASCANENB_in),
    .PMASCANIN (PMASCANIN_in),
    .QDPMASCANMODEB (QDPMASCANMODEB_in),
    .QDPMASCANRSTEN (QDPMASCANRSTEN_in),
    .QPLL0CLKRSVD0 (QPLL0CLKRSVD0_in),
    .QPLL0CLKRSVD1 (QPLL0CLKRSVD1_in),
    .QPLL0LOCKDETCLK (QPLL0LOCKDETCLK_in),
    .QPLL0LOCKEN (QPLL0LOCKEN_in),
    .QPLL0PD (QPLL0PD_in),
    .QPLL0REFCLKSEL (QPLL0REFCLKSEL_in),
    .QPLL0RESET (QPLL0RESET_in),
    .QPLL1CLKRSVD0 (QPLL1CLKRSVD0_in),
    .QPLL1CLKRSVD1 (QPLL1CLKRSVD1_in),
    .QPLL1LOCKDETCLK (QPLL1LOCKDETCLK_in),
    .QPLL1LOCKEN (QPLL1LOCKEN_in),
    .QPLL1PD (QPLL1PD_in),
    .QPLL1REFCLKSEL (QPLL1REFCLKSEL_in),
    .QPLL1RESET (QPLL1RESET_in),
    .QPLLRSVD1 (QPLLRSVD1_in),
    .QPLLRSVD2 (QPLLRSVD2_in),
    .QPLLRSVD3 (QPLLRSVD3_in),
    .QPLLRSVD4 (QPLLRSVD4_in),
    .RCALENB (RCALENB_in),
    .RXRECCLK (RXRECCLK_in),
    .GSR (glblGSR)
  );

  specify
    (DRPCLK *> DRPDO) = (100:100:100, 100:100:100);
    (DRPCLK => DRPRDY) = (100:100:100, 100:100:100);
    (GTGREFCLK0 => QPLL0OUTREFCLK) = (0:0:0, 0:0:0);
    (GTGREFCLK1 => QPLL1OUTREFCLK) = (0:0:0, 0:0:0);
    (GTNORTHREFCLK00 => QPLL0OUTREFCLK) = (0:0:0, 0:0:0);
    (GTNORTHREFCLK01 => QPLL1OUTREFCLK) = (0:0:0, 0:0:0);
    (GTNORTHREFCLK10 => QPLL0OUTREFCLK) = (0:0:0, 0:0:0);
    (GTNORTHREFCLK11 => QPLL1OUTREFCLK) = (0:0:0, 0:0:0);
    (GTREFCLK00 => QPLL0OUTREFCLK) = (0:0:0, 0:0:0);
    (GTREFCLK01 => QPLL1OUTREFCLK) = (0:0:0, 0:0:0);
    (GTREFCLK10 => QPLL0OUTREFCLK) = (0:0:0, 0:0:0);
    (GTREFCLK11 => QPLL1OUTREFCLK) = (0:0:0, 0:0:0);
    (GTSOUTHREFCLK00 => QPLL0OUTREFCLK) = (0:0:0, 0:0:0);
    (GTSOUTHREFCLK01 => QPLL1OUTREFCLK) = (0:0:0, 0:0:0);
    (GTSOUTHREFCLK10 => QPLL0OUTREFCLK) = (0:0:0, 0:0:0);
    (GTSOUTHREFCLK11 => QPLL1OUTREFCLK) = (0:0:0, 0:0:0);
    // (QPLL0OUTREFCLK => REFCLKOUTMONITOR0) = (0:0:0, 0:0:0); // error prop output to output
    // (QPLL1OUTREFCLK => REFCLKOUTMONITOR1) = (0:0:0, 0:0:0); // error prop output to output
`ifdef XIL_TIMING
    $period (negedge DRPCLK, 0:0:0, notifier);
    $period (posedge DRPCLK, 0:0:0, notifier);
    $setuphold (posedge DRPCLK, negedge DRPADDR, 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay);
    $setuphold (posedge DRPCLK, negedge DRPDI, 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay);
    $setuphold (posedge DRPCLK, negedge DRPEN, 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPEN_delay);
    $setuphold (posedge DRPCLK, negedge DRPWE, 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPWE_delay);
    $setuphold (posedge DRPCLK, posedge DRPADDR, 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay);
    $setuphold (posedge DRPCLK, posedge DRPDI, 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay);
    $setuphold (posedge DRPCLK, posedge DRPEN, 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPEN_delay);
    $setuphold (posedge DRPCLK, posedge DRPWE, 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPWE_delay);
    $width (negedge DRPCLK, 0:0:0, 0, notifier);
    $width (posedge DRPCLK, 0:0:0, 0, notifier);
`endif
    specparam PATHPULSE$ = 0;
  endspecify

endmodule

`endcelldefine
