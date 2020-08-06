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
//  /   /                        Gigabit Transceiver for UltraScale+ devices
// /___/   /\      Filename    : GTYE4_COMMON.v
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

module GTYE4_COMMON #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter [0:0] AEN_QPLL0_FBDIV = 1'b1,
  parameter [0:0] AEN_QPLL1_FBDIV = 1'b1,
  parameter [0:0] AEN_SDM0TOGGLE = 1'b0,
  parameter [0:0] AEN_SDM1TOGGLE = 1'b0,
  parameter [0:0] A_SDM0TOGGLE = 1'b0,
  parameter [8:0] A_SDM1DATA_HIGH = 9'b000000000,
  parameter [15:0] A_SDM1DATA_LOW = 16'b0000000000000000,
  parameter [0:0] A_SDM1TOGGLE = 1'b0,
  parameter [15:0] BIAS_CFG0 = 16'h0000,
  parameter [15:0] BIAS_CFG1 = 16'h0000,
  parameter [15:0] BIAS_CFG2 = 16'h0000,
  parameter [15:0] BIAS_CFG3 = 16'h0000,
  parameter [15:0] BIAS_CFG4 = 16'h0000,
  parameter [15:0] BIAS_CFG_RSVD = 16'h0000,
  parameter [15:0] COMMON_CFG0 = 16'h0000,
  parameter [15:0] COMMON_CFG1 = 16'h0000,
  parameter [15:0] POR_CFG = 16'h0000,
  parameter [15:0] PPF0_CFG = 16'h0F00,
  parameter [15:0] PPF1_CFG = 16'h0F00,
  parameter QPLL0CLKOUT_RATE = "FULL",
  parameter [15:0] QPLL0_CFG0 = 16'h391C,
  parameter [15:0] QPLL0_CFG1 = 16'h0000,
  parameter [15:0] QPLL0_CFG1_G3 = 16'h0020,
  parameter [15:0] QPLL0_CFG2 = 16'h0F80,
  parameter [15:0] QPLL0_CFG2_G3 = 16'h0F80,
  parameter [15:0] QPLL0_CFG3 = 16'h0120,
  parameter [15:0] QPLL0_CFG4 = 16'h0002,
  parameter [9:0] QPLL0_CP = 10'b0000011111,
  parameter [9:0] QPLL0_CP_G3 = 10'b0000011111,
  parameter integer QPLL0_FBDIV = 66,
  parameter integer QPLL0_FBDIV_G3 = 80,
  parameter [15:0] QPLL0_INIT_CFG0 = 16'h0000,
  parameter [7:0] QPLL0_INIT_CFG1 = 8'h00,
  parameter [15:0] QPLL0_LOCK_CFG = 16'h01E8,
  parameter [15:0] QPLL0_LOCK_CFG_G3 = 16'h21E8,
  parameter [9:0] QPLL0_LPF = 10'b1011111111,
  parameter [9:0] QPLL0_LPF_G3 = 10'b1111111111,
  parameter [0:0] QPLL0_PCI_EN = 1'b0,
  parameter [0:0] QPLL0_RATE_SW_USE_DRP = 1'b0,
  parameter integer QPLL0_REFCLK_DIV = 1,
  parameter [15:0] QPLL0_SDM_CFG0 = 16'h0040,
  parameter [15:0] QPLL0_SDM_CFG1 = 16'h0000,
  parameter [15:0] QPLL0_SDM_CFG2 = 16'h0000,
  parameter QPLL1CLKOUT_RATE = "FULL",
  parameter [15:0] QPLL1_CFG0 = 16'h691C,
  parameter [15:0] QPLL1_CFG1 = 16'h0020,
  parameter [15:0] QPLL1_CFG1_G3 = 16'h0020,
  parameter [15:0] QPLL1_CFG2 = 16'h0F80,
  parameter [15:0] QPLL1_CFG2_G3 = 16'h0F80,
  parameter [15:0] QPLL1_CFG3 = 16'h0120,
  parameter [15:0] QPLL1_CFG4 = 16'h0002,
  parameter [9:0] QPLL1_CP = 10'b0000011111,
  parameter [9:0] QPLL1_CP_G3 = 10'b0000011111,
  parameter integer QPLL1_FBDIV = 66,
  parameter integer QPLL1_FBDIV_G3 = 80,
  parameter [15:0] QPLL1_INIT_CFG0 = 16'h0000,
  parameter [7:0] QPLL1_INIT_CFG1 = 8'h00,
  parameter [15:0] QPLL1_LOCK_CFG = 16'h01E8,
  parameter [15:0] QPLL1_LOCK_CFG_G3 = 16'h21E8,
  parameter [9:0] QPLL1_LPF = 10'b1011111111,
  parameter [9:0] QPLL1_LPF_G3 = 10'b1111111111,
  parameter [0:0] QPLL1_PCI_EN = 1'b0,
  parameter [0:0] QPLL1_RATE_SW_USE_DRP = 1'b0,
  parameter integer QPLL1_REFCLK_DIV = 1,
  parameter [15:0] QPLL1_SDM_CFG0 = 16'h0000,
  parameter [15:0] QPLL1_SDM_CFG1 = 16'h0000,
  parameter [15:0] QPLL1_SDM_CFG2 = 16'h0000,
  parameter [15:0] RSVD_ATTR0 = 16'h0000,
  parameter [15:0] RSVD_ATTR1 = 16'h0000,
  parameter [15:0] RSVD_ATTR2 = 16'h0000,
  parameter [15:0] RSVD_ATTR3 = 16'h0000,
  parameter [1:0] RXRECCLKOUT0_SEL = 2'b00,
  parameter [1:0] RXRECCLKOUT1_SEL = 2'b00,
  parameter [0:0] SARC_ENB = 1'b0,
  parameter [0:0] SARC_SEL = 1'b0,
  parameter [15:0] SDM0INITSEED0_0 = 16'b0000000000000000,
  parameter [8:0] SDM0INITSEED0_1 = 9'b000000000,
  parameter [15:0] SDM1INITSEED0_0 = 16'b0000000000000000,
  parameter [8:0] SDM1INITSEED0_1 = 9'b000000000,
  parameter SIM_DEVICE = "ULTRASCALE_PLUS",
  parameter SIM_MODE = "FAST",
  parameter SIM_RESET_SPEEDUP = "TRUE",
  parameter [15:0] UB_CFG0 = 16'h0000,
  parameter [15:0] UB_CFG1 = 16'h0000,
  parameter [15:0] UB_CFG2 = 16'h0000,
  parameter [15:0] UB_CFG3 = 16'h0000,
  parameter [15:0] UB_CFG4 = 16'h0000,
  parameter [15:0] UB_CFG5 = 16'h0400,
  parameter [15:0] UB_CFG6 = 16'h0000
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
  output [1:0] RXRECCLK0SEL,
  output [1:0] RXRECCLK1SEL,
  output [3:0] SDM0FINALOUT,
  output [14:0] SDM0TESTDATA,
  output [3:0] SDM1FINALOUT,
  output [14:0] SDM1TESTDATA,
  output [15:0] UBDADDR,
  output UBDEN,
  output [15:0] UBDI,
  output UBDWE,
  output UBMDMTDO,
  output UBRSVDOUT,
  output UBTXUART,

  input BGBYPASSB,
  input BGMONITORENB,
  input BGPDB,
  input [4:0] BGRCALOVRD,
  input BGRCALOVRDENB,
  input [15:0] DRPADDR,
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
  input [2:0] PCIERATEQPLL0,
  input [2:0] PCIERATEQPLL1,
  input [7:0] PMARSVD0,
  input [7:0] PMARSVD1,
  input QPLL0CLKRSVD0,
  input QPLL0CLKRSVD1,
  input [7:0] QPLL0FBDIV,
  input QPLL0LOCKDETCLK,
  input QPLL0LOCKEN,
  input QPLL0PD,
  input [2:0] QPLL0REFCLKSEL,
  input QPLL0RESET,
  input QPLL1CLKRSVD0,
  input QPLL1CLKRSVD1,
  input [7:0] QPLL1FBDIV,
  input QPLL1LOCKDETCLK,
  input QPLL1LOCKEN,
  input QPLL1PD,
  input [2:0] QPLL1REFCLKSEL,
  input QPLL1RESET,
  input [7:0] QPLLRSVD1,
  input [4:0] QPLLRSVD2,
  input [4:0] QPLLRSVD3,
  input [7:0] QPLLRSVD4,
  input RCALENB,
  input [24:0] SDM0DATA,
  input SDM0RESET,
  input SDM0TOGGLE,
  input [1:0] SDM0WIDTH,
  input [24:0] SDM1DATA,
  input SDM1RESET,
  input SDM1TOGGLE,
  input [1:0] SDM1WIDTH,
  input UBCFGSTREAMEN,
  input [15:0] UBDO,
  input UBDRDY,
  input UBENABLE,
  input [1:0] UBGPI,
  input [1:0] UBINTR,
  input UBIOLMBRST,
  input UBMBRST,
  input UBMDMCAPTURE,
  input UBMDMDBGRST,
  input UBMDMDBGUPDATE,
  input [3:0] UBMDMREGEN,
  input UBMDMSHIFT,
  input UBMDMSYSRST,
  input UBMDMTCK,
  input UBMDMTDI
);

// define constants
  localparam MODULE_NAME = "GTYE4_COMMON";
  
  reg trig_attr = 1'b0;
// include dynamic registers - XILINX test only
`ifdef XIL_DR
  `include "GTYE4_COMMON_dr.v"
`else
  localparam [0:0] AEN_QPLL0_FBDIV_REG = AEN_QPLL0_FBDIV;
  localparam [0:0] AEN_QPLL1_FBDIV_REG = AEN_QPLL1_FBDIV;
  localparam [0:0] AEN_SDM0TOGGLE_REG = AEN_SDM0TOGGLE;
  localparam [0:0] AEN_SDM1TOGGLE_REG = AEN_SDM1TOGGLE;
  localparam [0:0] A_SDM0TOGGLE_REG = A_SDM0TOGGLE;
  localparam [8:0] A_SDM1DATA_HIGH_REG = A_SDM1DATA_HIGH;
  localparam [15:0] A_SDM1DATA_LOW_REG = A_SDM1DATA_LOW;
  localparam [0:0] A_SDM1TOGGLE_REG = A_SDM1TOGGLE;
  localparam [15:0] BIAS_CFG0_REG = BIAS_CFG0;
  localparam [15:0] BIAS_CFG1_REG = BIAS_CFG1;
  localparam [15:0] BIAS_CFG2_REG = BIAS_CFG2;
  localparam [15:0] BIAS_CFG3_REG = BIAS_CFG3;
  localparam [15:0] BIAS_CFG4_REG = BIAS_CFG4;
  localparam [15:0] BIAS_CFG_RSVD_REG = BIAS_CFG_RSVD;
  localparam [15:0] COMMON_CFG0_REG = COMMON_CFG0;
  localparam [15:0] COMMON_CFG1_REG = COMMON_CFG1;
  localparam [15:0] POR_CFG_REG = POR_CFG;
  localparam [15:0] PPF0_CFG_REG = PPF0_CFG;
  localparam [15:0] PPF1_CFG_REG = PPF1_CFG;
  localparam [32:1] QPLL0CLKOUT_RATE_REG = QPLL0CLKOUT_RATE;
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
  localparam [0:0] QPLL0_PCI_EN_REG = QPLL0_PCI_EN;
  localparam [0:0] QPLL0_RATE_SW_USE_DRP_REG = QPLL0_RATE_SW_USE_DRP;
  localparam [4:0] QPLL0_REFCLK_DIV_REG = QPLL0_REFCLK_DIV;
  localparam [15:0] QPLL0_SDM_CFG0_REG = QPLL0_SDM_CFG0;
  localparam [15:0] QPLL0_SDM_CFG1_REG = QPLL0_SDM_CFG1;
  localparam [15:0] QPLL0_SDM_CFG2_REG = QPLL0_SDM_CFG2;
  localparam [32:1] QPLL1CLKOUT_RATE_REG = QPLL1CLKOUT_RATE;
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
  localparam [0:0] QPLL1_PCI_EN_REG = QPLL1_PCI_EN;
  localparam [0:0] QPLL1_RATE_SW_USE_DRP_REG = QPLL1_RATE_SW_USE_DRP;
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
  localparam [0:0] SARC_ENB_REG = SARC_ENB;
  localparam [0:0] SARC_SEL_REG = SARC_SEL;
  localparam [15:0] SDM0INITSEED0_0_REG = SDM0INITSEED0_0;
  localparam [8:0] SDM0INITSEED0_1_REG = SDM0INITSEED0_1;
  localparam [15:0] SDM1INITSEED0_0_REG = SDM1INITSEED0_0;
  localparam [8:0] SDM1INITSEED0_1_REG = SDM1INITSEED0_1;
  localparam [160:1] SIM_DEVICE_REG = SIM_DEVICE;
  localparam [48:1] SIM_MODE_REG = SIM_MODE;
  localparam [40:1] SIM_RESET_SPEEDUP_REG = SIM_RESET_SPEEDUP;
  localparam [15:0] UB_CFG0_REG = UB_CFG0;
  localparam [15:0] UB_CFG1_REG = UB_CFG1;
  localparam [15:0] UB_CFG2_REG = UB_CFG2;
  localparam [15:0] UB_CFG3_REG = UB_CFG3;
  localparam [15:0] UB_CFG4_REG = UB_CFG4;
  localparam [15:0] UB_CFG5_REG = UB_CFG5;
  localparam [15:0] UB_CFG6_REG = UB_CFG6;
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
  localparam [0:0] AEN_SDM0DATA_REG = 1'b0;
  localparam [0:0] AEN_SDM0RESET_REG = 1'b0;
  localparam [0:0] AEN_SDM0WIDTH_REG = 1'b0;
  localparam [0:0] AEN_SDM1DATA_REG = 1'b0;
  localparam [0:0] AEN_SDM1RESET_REG = 1'b0;
  localparam [0:0] AEN_SDM1WIDTH_REG = 1'b0;
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
  localparam [8:0] A_SDM0DATA_HIGH_REG = 9'b000000000;
  localparam [15:0] A_SDM0DATA_LOW_REG = 16'b0000000000000000;
  localparam [0:0] A_SDM0RESET_REG = 1'b0;
  localparam [0:0] A_SDM1RESET_REG = 1'b0;
  localparam [1:0] COMMON_AMUX_SEL0_REG = 2'b00;
  localparam [1:0] COMMON_AMUX_SEL1_REG = 2'b00;
  localparam [0:0] COMMON_INSTANTIATED_REG = 1'b1;
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

  wire CSSDSTOPCLKDONE0_out;
  wire CSSDSTOPCLKDONE1_out;
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
  wire UBDEN_out;
  wire UBDWE_out;
  wire UBMDMTDO_out;
  wire UBRSVDOUT_out;
  wire UBTXUART_out;
  wire [13:0] PMASCANOUT_out;
  wire [14:0] SDM0TESTDATA_out;
  wire [14:0] SDM1TESTDATA_out;
  wire [15:0] DRPDO_out;
  wire [15:0] UBDADDR_out;
  wire [15:0] UBDI_out;
  wire [1:0] RXRECCLK0SEL_out;
  wire [1:0] RXRECCLK1SEL_out;
  wire [3:0] SARCCLK_out;
  wire [3:0] SDM0FINALOUT_out;
  wire [3:0] SDM1FINALOUT_out;
  wire [7:0] PMARSVDOUT0_out;
  wire [7:0] PMARSVDOUT1_out;
  wire [7:0] QPLLDMONITOR0_out;
  wire [7:0] QPLLDMONITOR1_out;

  wire BGBYPASSB_in;
  wire BGMONITORENB_in;
  wire BGPDB_in;
  wire BGRCALOVRDENB_in;
  wire CSSDSTOPCLK0_in;
  wire CSSDSTOPCLK1_in;
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
  wire SDM0RESET_in;
  wire SDM0TOGGLE_in;
  wire SDM1RESET_in;
  wire SDM1TOGGLE_in;
  wire UBCFGSTREAMEN_in;
  wire UBDRDY_in;
  wire UBENABLE_in;
  wire UBIOLMBRST_in;
  wire UBMBRST_in;
  wire UBMDMCAPTURE_in;
  wire UBMDMDBGRST_in;
  wire UBMDMDBGUPDATE_in;
  wire UBMDMSHIFT_in;
  wire UBMDMSYSRST_in;
  wire UBMDMTCK_in;
  wire UBMDMTDI_in;
  wire [13:0] PMASCANCLK_in;
  wire [13:0] PMASCANIN_in;
  wire [15:0] DRPADDR_in;
  wire [15:0] DRPDI_in;
  wire [15:0] UBDO_in;
  wire [1:0] SDM0WIDTH_in;
  wire [1:0] SDM1WIDTH_in;
  wire [1:0] UBGPI_in;
  wire [1:0] UBINTR_in;
  wire [24:0] SDM0DATA_in;
  wire [24:0] SDM1DATA_in;
  wire [2:0] PCIERATEQPLL0_in;
  wire [2:0] PCIERATEQPLL1_in;
  wire [2:0] QPLL0REFCLKSEL_in;
  wire [2:0] QPLL1REFCLKSEL_in;
  wire [3:0] RXRECCLK_in;
  wire [3:0] UBMDMREGEN_in;
  wire [4:0] BGRCALOVRD_in;
  wire [4:0] QPLLRSVD2_in;
  wire [4:0] QPLLRSVD3_in;
  wire [7:0] PMARSVD0_in;
  wire [7:0] PMARSVD1_in;
  wire [7:0] QPLL0FBDIV_in;
  wire [7:0] QPLL1FBDIV_in;
  wire [7:0] QPLLRSVD1_in;
  wire [7:0] QPLLRSVD4_in;

`ifdef XIL_TIMING
  wire DRPCLK_delay;
  wire DRPEN_delay;
  wire DRPWE_delay;
  wire UBDRDY_delay;
  wire [15:0] DRPADDR_delay;
  wire [15:0] DRPDI_delay;
  wire [15:0] UBDO_delay;
`endif

  assign DRPDO = DRPDO_out;
  assign DRPRDY = DRPRDY_out;
  assign PMARSVDOUT0 = PMARSVDOUT0_out;
  assign PMARSVDOUT1 = PMARSVDOUT1_out;
  assign QPLL0FBCLKLOST = QPLL0FBCLKLOST_out;
  assign QPLL0LOCK = QPLL0LOCK_out;
  assign QPLL0OUTCLK = QPLL0OUTCLK_out;
  assign QPLL0OUTREFCLK = QPLL0OUTREFCLK_out;
  assign QPLL0REFCLKLOST = QPLL0REFCLKLOST_out;
  assign QPLL1FBCLKLOST = QPLL1FBCLKLOST_out;
  assign QPLL1LOCK = QPLL1LOCK_out;
  assign QPLL1OUTCLK = QPLL1OUTCLK_out;
  assign QPLL1OUTREFCLK = QPLL1OUTREFCLK_out;
  assign QPLL1REFCLKLOST = QPLL1REFCLKLOST_out;
  assign QPLLDMONITOR0 = QPLLDMONITOR0_out;
  assign QPLLDMONITOR1 = QPLLDMONITOR1_out;
  assign REFCLKOUTMONITOR0 = REFCLKOUTMONITOR0_out;
  assign REFCLKOUTMONITOR1 = REFCLKOUTMONITOR1_out;
  assign RXRECCLK0SEL = RXRECCLK0SEL_out;
  assign RXRECCLK1SEL = RXRECCLK1SEL_out;
  assign SDM0FINALOUT = SDM0FINALOUT_out;
  assign SDM0TESTDATA = SDM0TESTDATA_out;
  assign SDM1FINALOUT = SDM1FINALOUT_out;
  assign SDM1TESTDATA = SDM1TESTDATA_out;
  assign UBDADDR = UBDADDR_out;
  assign UBDEN = UBDEN_out;
  assign UBDI = UBDI_out;
  assign UBDWE = UBDWE_out;
  assign UBMDMTDO = UBMDMTDO_out;
  assign UBRSVDOUT = UBRSVDOUT_out;
  assign UBTXUART = UBTXUART_out;

`ifdef XIL_TIMING
  assign DRPADDR_in[0] = (DRPADDR[0] !== 1'bz) && DRPADDR_delay[0]; // rv 0
  assign DRPADDR_in[10] = (DRPADDR[10] !== 1'bz) && DRPADDR_delay[10]; // rv 0
  assign DRPADDR_in[11] = (DRPADDR[11] !== 1'bz) && DRPADDR_delay[11]; // rv 0
  assign DRPADDR_in[12] = (DRPADDR[12] !== 1'bz) && DRPADDR_delay[12]; // rv 0
  assign DRPADDR_in[13] = (DRPADDR[13] !== 1'bz) && DRPADDR_delay[13]; // rv 0
  assign DRPADDR_in[14] = (DRPADDR[14] !== 1'bz) && DRPADDR_delay[14]; // rv 0
  assign DRPADDR_in[15] = (DRPADDR[15] !== 1'bz) && DRPADDR_delay[15]; // rv 0
  assign DRPADDR_in[1] = (DRPADDR[1] !== 1'bz) && DRPADDR_delay[1]; // rv 0
  assign DRPADDR_in[2] = (DRPADDR[2] !== 1'bz) && DRPADDR_delay[2]; // rv 0
  assign DRPADDR_in[3] = (DRPADDR[3] !== 1'bz) && DRPADDR_delay[3]; // rv 0
  assign DRPADDR_in[4] = (DRPADDR[4] !== 1'bz) && DRPADDR_delay[4]; // rv 0
  assign DRPADDR_in[5] = (DRPADDR[5] !== 1'bz) && DRPADDR_delay[5]; // rv 0
  assign DRPADDR_in[6] = (DRPADDR[6] !== 1'bz) && DRPADDR_delay[6]; // rv 0
  assign DRPADDR_in[7] = (DRPADDR[7] !== 1'bz) && DRPADDR_delay[7]; // rv 0
  assign DRPADDR_in[8] = (DRPADDR[8] !== 1'bz) && DRPADDR_delay[8]; // rv 0
  assign DRPADDR_in[9] = (DRPADDR[9] !== 1'bz) && DRPADDR_delay[9]; // rv 0
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
  assign UBDO_in[0] = (UBDO[0] !== 1'bz) && UBDO_delay[0]; // rv 0
  assign UBDO_in[10] = (UBDO[10] !== 1'bz) && UBDO_delay[10]; // rv 0
  assign UBDO_in[11] = (UBDO[11] !== 1'bz) && UBDO_delay[11]; // rv 0
  assign UBDO_in[12] = (UBDO[12] !== 1'bz) && UBDO_delay[12]; // rv 0
  assign UBDO_in[13] = (UBDO[13] !== 1'bz) && UBDO_delay[13]; // rv 0
  assign UBDO_in[14] = (UBDO[14] !== 1'bz) && UBDO_delay[14]; // rv 0
  assign UBDO_in[15] = (UBDO[15] !== 1'bz) && UBDO_delay[15]; // rv 0
  assign UBDO_in[1] = (UBDO[1] !== 1'bz) && UBDO_delay[1]; // rv 0
  assign UBDO_in[2] = (UBDO[2] !== 1'bz) && UBDO_delay[2]; // rv 0
  assign UBDO_in[3] = (UBDO[3] !== 1'bz) && UBDO_delay[3]; // rv 0
  assign UBDO_in[4] = (UBDO[4] !== 1'bz) && UBDO_delay[4]; // rv 0
  assign UBDO_in[5] = (UBDO[5] !== 1'bz) && UBDO_delay[5]; // rv 0
  assign UBDO_in[6] = (UBDO[6] !== 1'bz) && UBDO_delay[6]; // rv 0
  assign UBDO_in[7] = (UBDO[7] !== 1'bz) && UBDO_delay[7]; // rv 0
  assign UBDO_in[8] = (UBDO[8] !== 1'bz) && UBDO_delay[8]; // rv 0
  assign UBDO_in[9] = (UBDO[9] !== 1'bz) && UBDO_delay[9]; // rv 0
  assign UBDRDY_in = (UBDRDY !== 1'bz) && UBDRDY_delay; // rv 0
`else
  assign DRPADDR_in[0] = (DRPADDR[0] !== 1'bz) && DRPADDR[0]; // rv 0
  assign DRPADDR_in[10] = (DRPADDR[10] !== 1'bz) && DRPADDR[10]; // rv 0
  assign DRPADDR_in[11] = (DRPADDR[11] !== 1'bz) && DRPADDR[11]; // rv 0
  assign DRPADDR_in[12] = (DRPADDR[12] !== 1'bz) && DRPADDR[12]; // rv 0
  assign DRPADDR_in[13] = (DRPADDR[13] !== 1'bz) && DRPADDR[13]; // rv 0
  assign DRPADDR_in[14] = (DRPADDR[14] !== 1'bz) && DRPADDR[14]; // rv 0
  assign DRPADDR_in[15] = (DRPADDR[15] !== 1'bz) && DRPADDR[15]; // rv 0
  assign DRPADDR_in[1] = (DRPADDR[1] !== 1'bz) && DRPADDR[1]; // rv 0
  assign DRPADDR_in[2] = (DRPADDR[2] !== 1'bz) && DRPADDR[2]; // rv 0
  assign DRPADDR_in[3] = (DRPADDR[3] !== 1'bz) && DRPADDR[3]; // rv 0
  assign DRPADDR_in[4] = (DRPADDR[4] !== 1'bz) && DRPADDR[4]; // rv 0
  assign DRPADDR_in[5] = (DRPADDR[5] !== 1'bz) && DRPADDR[5]; // rv 0
  assign DRPADDR_in[6] = (DRPADDR[6] !== 1'bz) && DRPADDR[6]; // rv 0
  assign DRPADDR_in[7] = (DRPADDR[7] !== 1'bz) && DRPADDR[7]; // rv 0
  assign DRPADDR_in[8] = (DRPADDR[8] !== 1'bz) && DRPADDR[8]; // rv 0
  assign DRPADDR_in[9] = (DRPADDR[9] !== 1'bz) && DRPADDR[9]; // rv 0
  assign DRPCLK_in = (DRPCLK !== 1'bz) && DRPCLK; // rv 0
  assign DRPDI_in[0] = (DRPDI[0] !== 1'bz) && DRPDI[0]; // rv 0
  assign DRPDI_in[10] = (DRPDI[10] !== 1'bz) && DRPDI[10]; // rv 0
  assign DRPDI_in[11] = (DRPDI[11] !== 1'bz) && DRPDI[11]; // rv 0
  assign DRPDI_in[12] = (DRPDI[12] !== 1'bz) && DRPDI[12]; // rv 0
  assign DRPDI_in[13] = (DRPDI[13] !== 1'bz) && DRPDI[13]; // rv 0
  assign DRPDI_in[14] = (DRPDI[14] !== 1'bz) && DRPDI[14]; // rv 0
  assign DRPDI_in[15] = (DRPDI[15] !== 1'bz) && DRPDI[15]; // rv 0
  assign DRPDI_in[1] = (DRPDI[1] !== 1'bz) && DRPDI[1]; // rv 0
  assign DRPDI_in[2] = (DRPDI[2] !== 1'bz) && DRPDI[2]; // rv 0
  assign DRPDI_in[3] = (DRPDI[3] !== 1'bz) && DRPDI[3]; // rv 0
  assign DRPDI_in[4] = (DRPDI[4] !== 1'bz) && DRPDI[4]; // rv 0
  assign DRPDI_in[5] = (DRPDI[5] !== 1'bz) && DRPDI[5]; // rv 0
  assign DRPDI_in[6] = (DRPDI[6] !== 1'bz) && DRPDI[6]; // rv 0
  assign DRPDI_in[7] = (DRPDI[7] !== 1'bz) && DRPDI[7]; // rv 0
  assign DRPDI_in[8] = (DRPDI[8] !== 1'bz) && DRPDI[8]; // rv 0
  assign DRPDI_in[9] = (DRPDI[9] !== 1'bz) && DRPDI[9]; // rv 0
  assign DRPEN_in = (DRPEN !== 1'bz) && DRPEN; // rv 0
  assign DRPWE_in = (DRPWE !== 1'bz) && DRPWE; // rv 0
  assign UBDO_in[0] = (UBDO[0] !== 1'bz) && UBDO[0]; // rv 0
  assign UBDO_in[10] = (UBDO[10] !== 1'bz) && UBDO[10]; // rv 0
  assign UBDO_in[11] = (UBDO[11] !== 1'bz) && UBDO[11]; // rv 0
  assign UBDO_in[12] = (UBDO[12] !== 1'bz) && UBDO[12]; // rv 0
  assign UBDO_in[13] = (UBDO[13] !== 1'bz) && UBDO[13]; // rv 0
  assign UBDO_in[14] = (UBDO[14] !== 1'bz) && UBDO[14]; // rv 0
  assign UBDO_in[15] = (UBDO[15] !== 1'bz) && UBDO[15]; // rv 0
  assign UBDO_in[1] = (UBDO[1] !== 1'bz) && UBDO[1]; // rv 0
  assign UBDO_in[2] = (UBDO[2] !== 1'bz) && UBDO[2]; // rv 0
  assign UBDO_in[3] = (UBDO[3] !== 1'bz) && UBDO[3]; // rv 0
  assign UBDO_in[4] = (UBDO[4] !== 1'bz) && UBDO[4]; // rv 0
  assign UBDO_in[5] = (UBDO[5] !== 1'bz) && UBDO[5]; // rv 0
  assign UBDO_in[6] = (UBDO[6] !== 1'bz) && UBDO[6]; // rv 0
  assign UBDO_in[7] = (UBDO[7] !== 1'bz) && UBDO[7]; // rv 0
  assign UBDO_in[8] = (UBDO[8] !== 1'bz) && UBDO[8]; // rv 0
  assign UBDO_in[9] = (UBDO[9] !== 1'bz) && UBDO[9]; // rv 0
  assign UBDRDY_in = (UBDRDY !== 1'bz) && UBDRDY; // rv 0
`endif

  assign BGBYPASSB_in = BGBYPASSB;
  assign BGMONITORENB_in = BGMONITORENB;
  assign BGPDB_in = BGPDB;
  assign BGRCALOVRDENB_in = (BGRCALOVRDENB === 1'bz) || BGRCALOVRDENB; // rv 1
  assign BGRCALOVRD_in = BGRCALOVRD;
  assign GTGREFCLK0_in = GTGREFCLK0;
  assign GTGREFCLK1_in = GTGREFCLK1;
  assign GTNORTHREFCLK00_in = GTNORTHREFCLK00;
  assign GTNORTHREFCLK01_in = GTNORTHREFCLK01;
  assign GTNORTHREFCLK10_in = GTNORTHREFCLK10;
  assign GTNORTHREFCLK11_in = GTNORTHREFCLK11;
  assign GTREFCLK00_in = GTREFCLK00;
  assign GTREFCLK01_in = GTREFCLK01;
  assign GTREFCLK10_in = GTREFCLK10;
  assign GTREFCLK11_in = GTREFCLK11;
  assign GTSOUTHREFCLK00_in = GTSOUTHREFCLK00;
  assign GTSOUTHREFCLK01_in = GTSOUTHREFCLK01;
  assign GTSOUTHREFCLK10_in = GTSOUTHREFCLK10;
  assign GTSOUTHREFCLK11_in = GTSOUTHREFCLK11;
  assign PCIERATEQPLL0_in[0] = (PCIERATEQPLL0[0] !== 1'bz) && PCIERATEQPLL0[0]; // rv 0
  assign PCIERATEQPLL0_in[1] = (PCIERATEQPLL0[1] !== 1'bz) && PCIERATEQPLL0[1]; // rv 0
  assign PCIERATEQPLL0_in[2] = (PCIERATEQPLL0[2] !== 1'bz) && PCIERATEQPLL0[2]; // rv 0
  assign PCIERATEQPLL1_in[0] = (PCIERATEQPLL1[0] !== 1'bz) && PCIERATEQPLL1[0]; // rv 0
  assign PCIERATEQPLL1_in[1] = (PCIERATEQPLL1[1] !== 1'bz) && PCIERATEQPLL1[1]; // rv 0
  assign PCIERATEQPLL1_in[2] = (PCIERATEQPLL1[2] !== 1'bz) && PCIERATEQPLL1[2]; // rv 0
  assign PMARSVD0_in[0] = (PMARSVD0[0] !== 1'bz) && PMARSVD0[0]; // rv 0
  assign PMARSVD0_in[1] = (PMARSVD0[1] !== 1'bz) && PMARSVD0[1]; // rv 0
  assign PMARSVD0_in[2] = (PMARSVD0[2] !== 1'bz) && PMARSVD0[2]; // rv 0
  assign PMARSVD0_in[3] = (PMARSVD0[3] !== 1'bz) && PMARSVD0[3]; // rv 0
  assign PMARSVD0_in[4] = (PMARSVD0[4] !== 1'bz) && PMARSVD0[4]; // rv 0
  assign PMARSVD0_in[5] = (PMARSVD0[5] !== 1'bz) && PMARSVD0[5]; // rv 0
  assign PMARSVD0_in[6] = (PMARSVD0[6] !== 1'bz) && PMARSVD0[6]; // rv 0
  assign PMARSVD0_in[7] = (PMARSVD0[7] !== 1'bz) && PMARSVD0[7]; // rv 0
  assign PMARSVD1_in[0] = (PMARSVD1[0] !== 1'bz) && PMARSVD1[0]; // rv 0
  assign PMARSVD1_in[1] = (PMARSVD1[1] !== 1'bz) && PMARSVD1[1]; // rv 0
  assign PMARSVD1_in[2] = (PMARSVD1[2] !== 1'bz) && PMARSVD1[2]; // rv 0
  assign PMARSVD1_in[3] = (PMARSVD1[3] !== 1'bz) && PMARSVD1[3]; // rv 0
  assign PMARSVD1_in[4] = (PMARSVD1[4] !== 1'bz) && PMARSVD1[4]; // rv 0
  assign PMARSVD1_in[5] = (PMARSVD1[5] !== 1'bz) && PMARSVD1[5]; // rv 0
  assign PMARSVD1_in[6] = (PMARSVD1[6] !== 1'bz) && PMARSVD1[6]; // rv 0
  assign PMARSVD1_in[7] = (PMARSVD1[7] !== 1'bz) && PMARSVD1[7]; // rv 0
  assign QPLL0CLKRSVD0_in = (QPLL0CLKRSVD0 !== 1'bz) && QPLL0CLKRSVD0; // rv 0
  assign QPLL0CLKRSVD1_in = (QPLL0CLKRSVD1 !== 1'bz) && QPLL0CLKRSVD1; // rv 0
  assign QPLL0FBDIV_in[0] = (QPLL0FBDIV[0] !== 1'bz) && QPLL0FBDIV[0]; // rv 0
  assign QPLL0FBDIV_in[1] = (QPLL0FBDIV[1] !== 1'bz) && QPLL0FBDIV[1]; // rv 0
  assign QPLL0FBDIV_in[2] = (QPLL0FBDIV[2] !== 1'bz) && QPLL0FBDIV[2]; // rv 0
  assign QPLL0FBDIV_in[3] = (QPLL0FBDIV[3] !== 1'bz) && QPLL0FBDIV[3]; // rv 0
  assign QPLL0FBDIV_in[4] = (QPLL0FBDIV[4] !== 1'bz) && QPLL0FBDIV[4]; // rv 0
  assign QPLL0FBDIV_in[5] = (QPLL0FBDIV[5] !== 1'bz) && QPLL0FBDIV[5]; // rv 0
  assign QPLL0FBDIV_in[6] = (QPLL0FBDIV[6] !== 1'bz) && QPLL0FBDIV[6]; // rv 0
  assign QPLL0FBDIV_in[7] = (QPLL0FBDIV[7] !== 1'bz) && QPLL0FBDIV[7]; // rv 0
  assign QPLL0LOCKDETCLK_in = (QPLL0LOCKDETCLK !== 1'bz) && QPLL0LOCKDETCLK; // rv 0
  assign QPLL0LOCKEN_in = (QPLL0LOCKEN !== 1'bz) && QPLL0LOCKEN; // rv 0
  assign QPLL0PD_in = (QPLL0PD !== 1'bz) && QPLL0PD; // rv 0
  assign QPLL0REFCLKSEL_in[0] = (QPLL0REFCLKSEL[0] === 1'bz) || QPLL0REFCLKSEL[0]; // rv 1
  assign QPLL0REFCLKSEL_in[1] = (QPLL0REFCLKSEL[1] !== 1'bz) && QPLL0REFCLKSEL[1]; // rv 0
  assign QPLL0REFCLKSEL_in[2] = (QPLL0REFCLKSEL[2] !== 1'bz) && QPLL0REFCLKSEL[2]; // rv 0
  assign QPLL0RESET_in = (QPLL0RESET === 1'bz) || QPLL0RESET; // rv 1
  assign QPLL1CLKRSVD0_in = (QPLL1CLKRSVD0 !== 1'bz) && QPLL1CLKRSVD0; // rv 0
  assign QPLL1CLKRSVD1_in = (QPLL1CLKRSVD1 !== 1'bz) && QPLL1CLKRSVD1; // rv 0
  assign QPLL1FBDIV_in[0] = (QPLL1FBDIV[0] !== 1'bz) && QPLL1FBDIV[0]; // rv 0
  assign QPLL1FBDIV_in[1] = (QPLL1FBDIV[1] !== 1'bz) && QPLL1FBDIV[1]; // rv 0
  assign QPLL1FBDIV_in[2] = (QPLL1FBDIV[2] !== 1'bz) && QPLL1FBDIV[2]; // rv 0
  assign QPLL1FBDIV_in[3] = (QPLL1FBDIV[3] !== 1'bz) && QPLL1FBDIV[3]; // rv 0
  assign QPLL1FBDIV_in[4] = (QPLL1FBDIV[4] !== 1'bz) && QPLL1FBDIV[4]; // rv 0
  assign QPLL1FBDIV_in[5] = (QPLL1FBDIV[5] !== 1'bz) && QPLL1FBDIV[5]; // rv 0
  assign QPLL1FBDIV_in[6] = (QPLL1FBDIV[6] !== 1'bz) && QPLL1FBDIV[6]; // rv 0
  assign QPLL1FBDIV_in[7] = (QPLL1FBDIV[7] !== 1'bz) && QPLL1FBDIV[7]; // rv 0
  assign QPLL1LOCKDETCLK_in = (QPLL1LOCKDETCLK !== 1'bz) && QPLL1LOCKDETCLK; // rv 0
  assign QPLL1LOCKEN_in = (QPLL1LOCKEN !== 1'bz) && QPLL1LOCKEN; // rv 0
  assign QPLL1PD_in = (QPLL1PD !== 1'bz) && QPLL1PD; // rv 0
  assign QPLL1REFCLKSEL_in[0] = (QPLL1REFCLKSEL[0] === 1'bz) || QPLL1REFCLKSEL[0]; // rv 1
  assign QPLL1REFCLKSEL_in[1] = (QPLL1REFCLKSEL[1] !== 1'bz) && QPLL1REFCLKSEL[1]; // rv 0
  assign QPLL1REFCLKSEL_in[2] = (QPLL1REFCLKSEL[2] !== 1'bz) && QPLL1REFCLKSEL[2]; // rv 0
  assign QPLL1RESET_in = (QPLL1RESET === 1'bz) || QPLL1RESET; // rv 1
  assign QPLLRSVD1_in[0] = (QPLLRSVD1[0] !== 1'bz) && QPLLRSVD1[0]; // rv 0
  assign QPLLRSVD1_in[1] = (QPLLRSVD1[1] !== 1'bz) && QPLLRSVD1[1]; // rv 0
  assign QPLLRSVD1_in[2] = (QPLLRSVD1[2] !== 1'bz) && QPLLRSVD1[2]; // rv 0
  assign QPLLRSVD1_in[3] = (QPLLRSVD1[3] !== 1'bz) && QPLLRSVD1[3]; // rv 0
  assign QPLLRSVD1_in[4] = (QPLLRSVD1[4] !== 1'bz) && QPLLRSVD1[4]; // rv 0
  assign QPLLRSVD1_in[5] = (QPLLRSVD1[5] !== 1'bz) && QPLLRSVD1[5]; // rv 0
  assign QPLLRSVD1_in[6] = (QPLLRSVD1[6] !== 1'bz) && QPLLRSVD1[6]; // rv 0
  assign QPLLRSVD1_in[7] = (QPLLRSVD1[7] !== 1'bz) && QPLLRSVD1[7]; // rv 0
  assign QPLLRSVD2_in[0] = (QPLLRSVD2[0] !== 1'bz) && QPLLRSVD2[0]; // rv 0
  assign QPLLRSVD2_in[1] = (QPLLRSVD2[1] !== 1'bz) && QPLLRSVD2[1]; // rv 0
  assign QPLLRSVD2_in[2] = (QPLLRSVD2[2] !== 1'bz) && QPLLRSVD2[2]; // rv 0
  assign QPLLRSVD2_in[3] = (QPLLRSVD2[3] !== 1'bz) && QPLLRSVD2[3]; // rv 0
  assign QPLLRSVD2_in[4] = (QPLLRSVD2[4] !== 1'bz) && QPLLRSVD2[4]; // rv 0
  assign QPLLRSVD3_in[0] = (QPLLRSVD3[0] !== 1'bz) && QPLLRSVD3[0]; // rv 0
  assign QPLLRSVD3_in[1] = (QPLLRSVD3[1] !== 1'bz) && QPLLRSVD3[1]; // rv 0
  assign QPLLRSVD3_in[2] = (QPLLRSVD3[2] !== 1'bz) && QPLLRSVD3[2]; // rv 0
  assign QPLLRSVD3_in[3] = (QPLLRSVD3[3] !== 1'bz) && QPLLRSVD3[3]; // rv 0
  assign QPLLRSVD3_in[4] = (QPLLRSVD3[4] !== 1'bz) && QPLLRSVD3[4]; // rv 0
  assign QPLLRSVD4_in[0] = (QPLLRSVD4[0] !== 1'bz) && QPLLRSVD4[0]; // rv 0
  assign QPLLRSVD4_in[1] = (QPLLRSVD4[1] !== 1'bz) && QPLLRSVD4[1]; // rv 0
  assign QPLLRSVD4_in[2] = (QPLLRSVD4[2] !== 1'bz) && QPLLRSVD4[2]; // rv 0
  assign QPLLRSVD4_in[3] = (QPLLRSVD4[3] !== 1'bz) && QPLLRSVD4[3]; // rv 0
  assign QPLLRSVD4_in[4] = (QPLLRSVD4[4] !== 1'bz) && QPLLRSVD4[4]; // rv 0
  assign QPLLRSVD4_in[5] = (QPLLRSVD4[5] !== 1'bz) && QPLLRSVD4[5]; // rv 0
  assign QPLLRSVD4_in[6] = (QPLLRSVD4[6] !== 1'bz) && QPLLRSVD4[6]; // rv 0
  assign QPLLRSVD4_in[7] = (QPLLRSVD4[7] !== 1'bz) && QPLLRSVD4[7]; // rv 0
  assign RCALENB_in = RCALENB;
  assign SDM0DATA_in[0] = (SDM0DATA[0] !== 1'bz) && SDM0DATA[0]; // rv 0
  assign SDM0DATA_in[10] = (SDM0DATA[10] !== 1'bz) && SDM0DATA[10]; // rv 0
  assign SDM0DATA_in[11] = (SDM0DATA[11] !== 1'bz) && SDM0DATA[11]; // rv 0
  assign SDM0DATA_in[12] = (SDM0DATA[12] !== 1'bz) && SDM0DATA[12]; // rv 0
  assign SDM0DATA_in[13] = (SDM0DATA[13] !== 1'bz) && SDM0DATA[13]; // rv 0
  assign SDM0DATA_in[14] = (SDM0DATA[14] !== 1'bz) && SDM0DATA[14]; // rv 0
  assign SDM0DATA_in[15] = (SDM0DATA[15] !== 1'bz) && SDM0DATA[15]; // rv 0
  assign SDM0DATA_in[16] = (SDM0DATA[16] !== 1'bz) && SDM0DATA[16]; // rv 0
  assign SDM0DATA_in[17] = (SDM0DATA[17] !== 1'bz) && SDM0DATA[17]; // rv 0
  assign SDM0DATA_in[18] = (SDM0DATA[18] !== 1'bz) && SDM0DATA[18]; // rv 0
  assign SDM0DATA_in[19] = (SDM0DATA[19] !== 1'bz) && SDM0DATA[19]; // rv 0
  assign SDM0DATA_in[1] = (SDM0DATA[1] !== 1'bz) && SDM0DATA[1]; // rv 0
  assign SDM0DATA_in[20] = (SDM0DATA[20] !== 1'bz) && SDM0DATA[20]; // rv 0
  assign SDM0DATA_in[21] = (SDM0DATA[21] !== 1'bz) && SDM0DATA[21]; // rv 0
  assign SDM0DATA_in[22] = (SDM0DATA[22] !== 1'bz) && SDM0DATA[22]; // rv 0
  assign SDM0DATA_in[23] = (SDM0DATA[23] !== 1'bz) && SDM0DATA[23]; // rv 0
  assign SDM0DATA_in[24] = (SDM0DATA[24] !== 1'bz) && SDM0DATA[24]; // rv 0
  assign SDM0DATA_in[2] = (SDM0DATA[2] !== 1'bz) && SDM0DATA[2]; // rv 0
  assign SDM0DATA_in[3] = (SDM0DATA[3] !== 1'bz) && SDM0DATA[3]; // rv 0
  assign SDM0DATA_in[4] = (SDM0DATA[4] !== 1'bz) && SDM0DATA[4]; // rv 0
  assign SDM0DATA_in[5] = (SDM0DATA[5] !== 1'bz) && SDM0DATA[5]; // rv 0
  assign SDM0DATA_in[6] = (SDM0DATA[6] !== 1'bz) && SDM0DATA[6]; // rv 0
  assign SDM0DATA_in[7] = (SDM0DATA[7] !== 1'bz) && SDM0DATA[7]; // rv 0
  assign SDM0DATA_in[8] = (SDM0DATA[8] !== 1'bz) && SDM0DATA[8]; // rv 0
  assign SDM0DATA_in[9] = (SDM0DATA[9] !== 1'bz) && SDM0DATA[9]; // rv 0
  assign SDM0RESET_in = (SDM0RESET === 1'bz) || SDM0RESET; // rv 1
  assign SDM0TOGGLE_in = (SDM0TOGGLE !== 1'bz) && SDM0TOGGLE; // rv 0
  assign SDM0WIDTH_in[0] = (SDM0WIDTH[0] !== 1'bz) && SDM0WIDTH[0]; // rv 0
  assign SDM0WIDTH_in[1] = (SDM0WIDTH[1] !== 1'bz) && SDM0WIDTH[1]; // rv 0
  assign SDM1DATA_in[0] = (SDM1DATA[0] !== 1'bz) && SDM1DATA[0]; // rv 0
  assign SDM1DATA_in[10] = (SDM1DATA[10] !== 1'bz) && SDM1DATA[10]; // rv 0
  assign SDM1DATA_in[11] = (SDM1DATA[11] !== 1'bz) && SDM1DATA[11]; // rv 0
  assign SDM1DATA_in[12] = (SDM1DATA[12] !== 1'bz) && SDM1DATA[12]; // rv 0
  assign SDM1DATA_in[13] = (SDM1DATA[13] !== 1'bz) && SDM1DATA[13]; // rv 0
  assign SDM1DATA_in[14] = (SDM1DATA[14] !== 1'bz) && SDM1DATA[14]; // rv 0
  assign SDM1DATA_in[15] = (SDM1DATA[15] !== 1'bz) && SDM1DATA[15]; // rv 0
  assign SDM1DATA_in[16] = (SDM1DATA[16] !== 1'bz) && SDM1DATA[16]; // rv 0
  assign SDM1DATA_in[17] = (SDM1DATA[17] !== 1'bz) && SDM1DATA[17]; // rv 0
  assign SDM1DATA_in[18] = (SDM1DATA[18] !== 1'bz) && SDM1DATA[18]; // rv 0
  assign SDM1DATA_in[19] = (SDM1DATA[19] !== 1'bz) && SDM1DATA[19]; // rv 0
  assign SDM1DATA_in[1] = (SDM1DATA[1] !== 1'bz) && SDM1DATA[1]; // rv 0
  assign SDM1DATA_in[20] = (SDM1DATA[20] !== 1'bz) && SDM1DATA[20]; // rv 0
  assign SDM1DATA_in[21] = (SDM1DATA[21] !== 1'bz) && SDM1DATA[21]; // rv 0
  assign SDM1DATA_in[22] = (SDM1DATA[22] !== 1'bz) && SDM1DATA[22]; // rv 0
  assign SDM1DATA_in[23] = (SDM1DATA[23] !== 1'bz) && SDM1DATA[23]; // rv 0
  assign SDM1DATA_in[24] = (SDM1DATA[24] !== 1'bz) && SDM1DATA[24]; // rv 0
  assign SDM1DATA_in[2] = (SDM1DATA[2] !== 1'bz) && SDM1DATA[2]; // rv 0
  assign SDM1DATA_in[3] = (SDM1DATA[3] !== 1'bz) && SDM1DATA[3]; // rv 0
  assign SDM1DATA_in[4] = (SDM1DATA[4] !== 1'bz) && SDM1DATA[4]; // rv 0
  assign SDM1DATA_in[5] = (SDM1DATA[5] !== 1'bz) && SDM1DATA[5]; // rv 0
  assign SDM1DATA_in[6] = (SDM1DATA[6] !== 1'bz) && SDM1DATA[6]; // rv 0
  assign SDM1DATA_in[7] = (SDM1DATA[7] !== 1'bz) && SDM1DATA[7]; // rv 0
  assign SDM1DATA_in[8] = (SDM1DATA[8] !== 1'bz) && SDM1DATA[8]; // rv 0
  assign SDM1DATA_in[9] = (SDM1DATA[9] !== 1'bz) && SDM1DATA[9]; // rv 0
  assign SDM1RESET_in = (SDM1RESET === 1'bz) || SDM1RESET; // rv 1
  assign SDM1TOGGLE_in = (SDM1TOGGLE !== 1'bz) && SDM1TOGGLE; // rv 0
  assign SDM1WIDTH_in[0] = (SDM1WIDTH[0] !== 1'bz) && SDM1WIDTH[0]; // rv 0
  assign SDM1WIDTH_in[1] = (SDM1WIDTH[1] !== 1'bz) && SDM1WIDTH[1]; // rv 0
  assign UBCFGSTREAMEN_in = (UBCFGSTREAMEN !== 1'bz) && UBCFGSTREAMEN; // rv 0
  assign UBENABLE_in = (UBENABLE !== 1'bz) && UBENABLE; // rv 0
  assign UBGPI_in[0] = (UBGPI[0] !== 1'bz) && UBGPI[0]; // rv 0
  assign UBGPI_in[1] = (UBGPI[1] !== 1'bz) && UBGPI[1]; // rv 0
  assign UBINTR_in[0] = (UBINTR[0] !== 1'bz) && UBINTR[0]; // rv 0
  assign UBINTR_in[1] = (UBINTR[1] !== 1'bz) && UBINTR[1]; // rv 0
  assign UBIOLMBRST_in = (UBIOLMBRST === 1'bz) || UBIOLMBRST; // rv 1
  assign UBMBRST_in = (UBMBRST === 1'bz) || UBMBRST; // rv 1
  assign UBMDMCAPTURE_in = (UBMDMCAPTURE !== 1'bz) && UBMDMCAPTURE; // rv 0
  assign UBMDMDBGRST_in = (UBMDMDBGRST !== 1'bz) && UBMDMDBGRST; // rv 0
  assign UBMDMDBGUPDATE_in = (UBMDMDBGUPDATE !== 1'bz) && UBMDMDBGUPDATE; // rv 0
  assign UBMDMREGEN_in[0] = (UBMDMREGEN[0] !== 1'bz) && UBMDMREGEN[0]; // rv 0
  assign UBMDMREGEN_in[1] = (UBMDMREGEN[1] !== 1'bz) && UBMDMREGEN[1]; // rv 0
  assign UBMDMREGEN_in[2] = (UBMDMREGEN[2] !== 1'bz) && UBMDMREGEN[2]; // rv 0
  assign UBMDMREGEN_in[3] = (UBMDMREGEN[3] !== 1'bz) && UBMDMREGEN[3]; // rv 0
  assign UBMDMSHIFT_in = (UBMDMSHIFT !== 1'bz) && UBMDMSHIFT; // rv 0
  assign UBMDMSYSRST_in = (UBMDMSYSRST !== 1'bz) && UBMDMSYSRST; // rv 0
  assign UBMDMTCK_in = (UBMDMTCK !== 1'bz) && UBMDMTCK; // rv 0
  assign UBMDMTDI_in = (UBMDMTDI !== 1'bz) && UBMDMTDI; // rv 0

`ifndef XIL_XECLIB
always @ (trig_attr) begin
  #1;
  if ((attr_test == 1'b1) ||
      ((QPLL0CLKOUT_RATE_REG != "FULL") &&
       (QPLL0CLKOUT_RATE_REG != "HALF"))) begin
    $display("Error: [Unisim %s-158] QPLL0CLKOUT_RATE attribute is set to %s.  Legal values for this attribute are FULL or HALF. Instance: %m", MODULE_NAME, QPLL0CLKOUT_RATE_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((QPLL0_FBDIV_REG < 16) || (QPLL0_FBDIV_REG > 160))) begin
    $display("Error: [Unisim %s-169] QPLL0_FBDIV attribute is set to %d.  Legal values for this attribute are 16 to 160. Instance: %m", MODULE_NAME, QPLL0_FBDIV_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((QPLL0_FBDIV_G3_REG < 16) || (QPLL0_FBDIV_G3_REG > 160))) begin
    $display("Error: [Unisim %s-170] QPLL0_FBDIV_G3 attribute is set to %d.  Legal values for this attribute are 16 to 160. Instance: %m", MODULE_NAME, QPLL0_FBDIV_G3_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((QPLL0_REFCLK_DIV_REG != 1) &&
       (QPLL0_REFCLK_DIV_REG != 2) &&
       (QPLL0_REFCLK_DIV_REG != 3) &&
       (QPLL0_REFCLK_DIV_REG != 4) &&
       (QPLL0_REFCLK_DIV_REG != 5) &&
       (QPLL0_REFCLK_DIV_REG != 6) &&
       (QPLL0_REFCLK_DIV_REG != 8) &&
       (QPLL0_REFCLK_DIV_REG != 10) &&
       (QPLL0_REFCLK_DIV_REG != 12) &&
       (QPLL0_REFCLK_DIV_REG != 16) &&
       (QPLL0_REFCLK_DIV_REG != 20))) begin
    $display("Error: [Unisim %s-179] QPLL0_REFCLK_DIV attribute is set to %d.  Legal values for this attribute are 1, 2, 3, 4, 5, 6, 8, 10, 12, 16 or 20. Instance: %m", MODULE_NAME, QPLL0_REFCLK_DIV_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((QPLL1CLKOUT_RATE_REG != "FULL") &&
       (QPLL1CLKOUT_RATE_REG != "HALF"))) begin
    $display("Error: [Unisim %s-183] QPLL1CLKOUT_RATE attribute is set to %s.  Legal values for this attribute are FULL or HALF. Instance: %m", MODULE_NAME, QPLL1CLKOUT_RATE_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((QPLL1_FBDIV_REG < 16) || (QPLL1_FBDIV_REG > 160))) begin
    $display("Error: [Unisim %s-194] QPLL1_FBDIV attribute is set to %d.  Legal values for this attribute are 16 to 160. Instance: %m", MODULE_NAME, QPLL1_FBDIV_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((QPLL1_FBDIV_G3_REG < 16) || (QPLL1_FBDIV_G3_REG > 160))) begin
    $display("Error: [Unisim %s-195] QPLL1_FBDIV_G3 attribute is set to %d.  Legal values for this attribute are 16 to 160. Instance: %m", MODULE_NAME, QPLL1_FBDIV_G3_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((QPLL1_REFCLK_DIV_REG != 1) &&
       (QPLL1_REFCLK_DIV_REG != 2) &&
       (QPLL1_REFCLK_DIV_REG != 3) &&
       (QPLL1_REFCLK_DIV_REG != 4) &&
       (QPLL1_REFCLK_DIV_REG != 5) &&
       (QPLL1_REFCLK_DIV_REG != 6) &&
       (QPLL1_REFCLK_DIV_REG != 8) &&
       (QPLL1_REFCLK_DIV_REG != 10) &&
       (QPLL1_REFCLK_DIV_REG != 12) &&
       (QPLL1_REFCLK_DIV_REG != 16) &&
       (QPLL1_REFCLK_DIV_REG != 20))) begin
    $display("Error: [Unisim %s-204] QPLL1_REFCLK_DIV attribute is set to %d.  Legal values for this attribute are 1, 2, 3, 4, 5, 6, 8, 10, 12, 16 or 20. Instance: %m", MODULE_NAME, QPLL1_REFCLK_DIV_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((SIM_DEVICE_REG != "ULTRASCALE_PLUS") &&
       (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES1") &&
       (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES1p") &&
       (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES2"))) begin
    $display("Error: [Unisim %s-228] SIM_DEVICE attribute is set to %s.  Legal values for this attribute are ULTRASCALE_PLUS, ULTRASCALE_PLUS_ES1, ULTRASCALE_PLUS_ES1p or ULTRASCALE_PLUS_ES2. Instance: %m", MODULE_NAME, SIM_DEVICE_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((SIM_MODE_REG != "FAST") &&
       (SIM_MODE_REG != "LEGACY"))) begin
    $display("Error: [Unisim %s-229] SIM_MODE attribute is set to %s.  Legal values for this attribute are FAST or LEGACY. Instance: %m", MODULE_NAME, SIM_MODE_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((SIM_RESET_SPEEDUP_REG != "TRUE") &&
       (SIM_RESET_SPEEDUP_REG != "FALSE"))) begin
    $display("Error: [Unisim %s-230] SIM_RESET_SPEEDUP attribute is set to %s.  Legal values for this attribute are TRUE or FALSE. Instance: %m", MODULE_NAME, SIM_RESET_SPEEDUP_REG);
    attr_err = 1'b1;
  end
  
  if (attr_err == 1'b1) #1 $finish;
end
`endif

assign PMASCANCLK_in = 14'b11111111111111; // tie off

assign CSSDSTOPCLK0_in = 1'b1; // tie off
assign CSSDSTOPCLK1_in = 1'b1; // tie off
assign PMASCANENB_in = 1'b1; // tie off
assign PMASCANIN_in = 14'b11111111111111; // tie off
assign QDPMASCANMODEB_in = 1'b1; // tie off
assign QDPMASCANRSTEN_in = 1'b1; // tie off
assign RXRECCLK_in = 4'b1111; // tie off

SIP_GTYE4_COMMON SIP_GTYE4_COMMON_INST (
  .AEN_BGBS0 (AEN_BGBS0_REG),
  .AEN_BGBS1 (AEN_BGBS1_REG),
  .AEN_MASTER0 (AEN_MASTER0_REG),
  .AEN_MASTER1 (AEN_MASTER1_REG),
  .AEN_PD0 (AEN_PD0_REG),
  .AEN_PD1 (AEN_PD1_REG),
  .AEN_QPLL0 (AEN_QPLL0_REG),
  .AEN_QPLL0_FBDIV (AEN_QPLL0_FBDIV_REG),
  .AEN_QPLL1 (AEN_QPLL1_REG),
  .AEN_QPLL1_FBDIV (AEN_QPLL1_FBDIV_REG),
  .AEN_REFCLK0 (AEN_REFCLK0_REG),
  .AEN_REFCLK1 (AEN_REFCLK1_REG),
  .AEN_RESET0 (AEN_RESET0_REG),
  .AEN_RESET1 (AEN_RESET1_REG),
  .AEN_SDM0DATA (AEN_SDM0DATA_REG),
  .AEN_SDM0RESET (AEN_SDM0RESET_REG),
  .AEN_SDM0TOGGLE (AEN_SDM0TOGGLE_REG),
  .AEN_SDM0WIDTH (AEN_SDM0WIDTH_REG),
  .AEN_SDM1DATA (AEN_SDM1DATA_REG),
  .AEN_SDM1RESET (AEN_SDM1RESET_REG),
  .AEN_SDM1TOGGLE (AEN_SDM1TOGGLE_REG),
  .AEN_SDM1WIDTH (AEN_SDM1WIDTH_REG),
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
  .A_SDM0DATA_HIGH (A_SDM0DATA_HIGH_REG),
  .A_SDM0DATA_LOW (A_SDM0DATA_LOW_REG),
  .A_SDM0RESET (A_SDM0RESET_REG),
  .A_SDM0TOGGLE (A_SDM0TOGGLE_REG),
  .A_SDM1DATA_HIGH (A_SDM1DATA_HIGH_REG),
  .A_SDM1DATA_LOW (A_SDM1DATA_LOW_REG),
  .A_SDM1RESET (A_SDM1RESET_REG),
  .A_SDM1TOGGLE (A_SDM1TOGGLE_REG),
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
  .QPLL0CLKOUT_RATE (QPLL0CLKOUT_RATE_REG),
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
  .QPLL0_PCI_EN (QPLL0_PCI_EN_REG),
  .QPLL0_RATE_SW_USE_DRP (QPLL0_RATE_SW_USE_DRP_REG),
  .QPLL0_REFCLK_DIV (QPLL0_REFCLK_DIV_REG),
  .QPLL0_SDM_CFG0 (QPLL0_SDM_CFG0_REG),
  .QPLL0_SDM_CFG1 (QPLL0_SDM_CFG1_REG),
  .QPLL0_SDM_CFG2 (QPLL0_SDM_CFG2_REG),
  .QPLL1CLKOUT_RATE (QPLL1CLKOUT_RATE_REG),
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
  .QPLL1_PCI_EN (QPLL1_PCI_EN_REG),
  .QPLL1_RATE_SW_USE_DRP (QPLL1_RATE_SW_USE_DRP_REG),
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
  .SARC_ENB (SARC_ENB_REG),
  .SARC_SEL (SARC_SEL_REG),
  .SDM0INITSEED0_0 (SDM0INITSEED0_0_REG),
  .SDM0INITSEED0_1 (SDM0INITSEED0_1_REG),
  .SDM1INITSEED0_0 (SDM1INITSEED0_0_REG),
  .SDM1INITSEED0_1 (SDM1INITSEED0_1_REG),
  .SIM_DEVICE (SIM_DEVICE_REG),
  .SIM_MODE (SIM_MODE_REG),
  .SIM_RESET_SPEEDUP (SIM_RESET_SPEEDUP_REG),
  .UB_CFG0 (UB_CFG0_REG),
  .UB_CFG1 (UB_CFG1_REG),
  .UB_CFG2 (UB_CFG2_REG),
  .UB_CFG3 (UB_CFG3_REG),
  .UB_CFG4 (UB_CFG4_REG),
  .UB_CFG5 (UB_CFG5_REG),
  .UB_CFG6 (UB_CFG6_REG),
  .VCCAUX_SENSE_SEL (VCCAUX_SENSE_SEL_REG),
  .CSSDSTOPCLKDONE0 (CSSDSTOPCLKDONE0_out),
  .CSSDSTOPCLKDONE1 (CSSDSTOPCLKDONE1_out),
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
  .RXRECCLK0SEL (RXRECCLK0SEL_out),
  .RXRECCLK1SEL (RXRECCLK1SEL_out),
  .SARCCLK (SARCCLK_out),
  .SDM0FINALOUT (SDM0FINALOUT_out),
  .SDM0TESTDATA (SDM0TESTDATA_out),
  .SDM1FINALOUT (SDM1FINALOUT_out),
  .SDM1TESTDATA (SDM1TESTDATA_out),
  .UBDADDR (UBDADDR_out),
  .UBDEN (UBDEN_out),
  .UBDI (UBDI_out),
  .UBDWE (UBDWE_out),
  .UBMDMTDO (UBMDMTDO_out),
  .UBRSVDOUT (UBRSVDOUT_out),
  .UBTXUART (UBTXUART_out),
  .BGBYPASSB (BGBYPASSB_in),
  .BGMONITORENB (BGMONITORENB_in),
  .BGPDB (BGPDB_in),
  .BGRCALOVRD (BGRCALOVRD_in),
  .BGRCALOVRDENB (BGRCALOVRDENB_in),
  .CSSDSTOPCLK0 (CSSDSTOPCLK0_in),
  .CSSDSTOPCLK1 (CSSDSTOPCLK1_in),
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
  .PCIERATEQPLL0 (PCIERATEQPLL0_in),
  .PCIERATEQPLL1 (PCIERATEQPLL1_in),
  .PMARSVD0 (PMARSVD0_in),
  .PMARSVD1 (PMARSVD1_in),
  .PMASCANCLK (PMASCANCLK_in),
  .PMASCANENB (PMASCANENB_in),
  .PMASCANIN (PMASCANIN_in),
  .QDPMASCANMODEB (QDPMASCANMODEB_in),
  .QDPMASCANRSTEN (QDPMASCANRSTEN_in),
  .QPLL0CLKRSVD0 (QPLL0CLKRSVD0_in),
  .QPLL0CLKRSVD1 (QPLL0CLKRSVD1_in),
  .QPLL0FBDIV (QPLL0FBDIV_in),
  .QPLL0LOCKDETCLK (QPLL0LOCKDETCLK_in),
  .QPLL0LOCKEN (QPLL0LOCKEN_in),
  .QPLL0PD (QPLL0PD_in),
  .QPLL0REFCLKSEL (QPLL0REFCLKSEL_in),
  .QPLL0RESET (QPLL0RESET_in),
  .QPLL1CLKRSVD0 (QPLL1CLKRSVD0_in),
  .QPLL1CLKRSVD1 (QPLL1CLKRSVD1_in),
  .QPLL1FBDIV (QPLL1FBDIV_in),
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
  .SDM0DATA (SDM0DATA_in),
  .SDM0RESET (SDM0RESET_in),
  .SDM0TOGGLE (SDM0TOGGLE_in),
  .SDM0WIDTH (SDM0WIDTH_in),
  .SDM1DATA (SDM1DATA_in),
  .SDM1RESET (SDM1RESET_in),
  .SDM1TOGGLE (SDM1TOGGLE_in),
  .SDM1WIDTH (SDM1WIDTH_in),
  .UBCFGSTREAMEN (UBCFGSTREAMEN_in),
  .UBDO (UBDO_in),
  .UBDRDY (UBDRDY_in),
  .UBENABLE (UBENABLE_in),
  .UBGPI (UBGPI_in),
  .UBINTR (UBINTR_in),
  .UBIOLMBRST (UBIOLMBRST_in),
  .UBMBRST (UBMBRST_in),
  .UBMDMCAPTURE (UBMDMCAPTURE_in),
  .UBMDMDBGRST (UBMDMDBGRST_in),
  .UBMDMDBGUPDATE (UBMDMDBGUPDATE_in),
  .UBMDMREGEN (UBMDMREGEN_in),
  .UBMDMSHIFT (UBMDMSHIFT_in),
  .UBMDMSYSRST (UBMDMSYSRST_in),
  .UBMDMTCK (UBMDMTCK_in),
  .UBMDMTDI (UBMDMTDI_in),
  .GSR (glblGSR)
);

`ifndef XIL_XECLIB
`ifdef XIL_TIMING
  reg notifier;
`endif

  specify
    (DRPCLK => DRPDO[0]) = (100:100:100, 100:100:100);
    (DRPCLK => DRPDO[10]) = (100:100:100, 100:100:100);
    (DRPCLK => DRPDO[11]) = (100:100:100, 100:100:100);
    (DRPCLK => DRPDO[12]) = (100:100:100, 100:100:100);
    (DRPCLK => DRPDO[13]) = (100:100:100, 100:100:100);
    (DRPCLK => DRPDO[14]) = (100:100:100, 100:100:100);
    (DRPCLK => DRPDO[15]) = (100:100:100, 100:100:100);
    (DRPCLK => DRPDO[1]) = (100:100:100, 100:100:100);
    (DRPCLK => DRPDO[2]) = (100:100:100, 100:100:100);
    (DRPCLK => DRPDO[3]) = (100:100:100, 100:100:100);
    (DRPCLK => DRPDO[4]) = (100:100:100, 100:100:100);
    (DRPCLK => DRPDO[5]) = (100:100:100, 100:100:100);
    (DRPCLK => DRPDO[6]) = (100:100:100, 100:100:100);
    (DRPCLK => DRPDO[7]) = (100:100:100, 100:100:100);
    (DRPCLK => DRPDO[8]) = (100:100:100, 100:100:100);
    (DRPCLK => DRPDO[9]) = (100:100:100, 100:100:100);
    (DRPCLK => DRPRDY) = (100:100:100, 100:100:100);
    (DRPCLK => UBDADDR[0]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDADDR[10]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDADDR[11]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDADDR[12]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDADDR[13]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDADDR[14]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDADDR[15]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDADDR[1]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDADDR[2]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDADDR[3]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDADDR[4]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDADDR[5]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDADDR[6]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDADDR[7]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDADDR[8]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDADDR[9]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDEN) = (100:100:100, 100:100:100);
    (DRPCLK => UBDI[0]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDI[10]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDI[11]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDI[12]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDI[13]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDI[14]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDI[15]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDI[1]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDI[2]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDI[3]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDI[4]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDI[5]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDI[6]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDI[7]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDI[8]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDI[9]) = (100:100:100, 100:100:100);
    (DRPCLK => UBDWE) = (100:100:100, 100:100:100);
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
    $setuphold (posedge DRPCLK, negedge DRPADDR[0], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay[0]);
    $setuphold (posedge DRPCLK, negedge DRPADDR[10], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay[10]);
    $setuphold (posedge DRPCLK, negedge DRPADDR[11], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay[11]);
    $setuphold (posedge DRPCLK, negedge DRPADDR[12], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay[12]);
    $setuphold (posedge DRPCLK, negedge DRPADDR[13], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay[13]);
    $setuphold (posedge DRPCLK, negedge DRPADDR[1], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay[1]);
    $setuphold (posedge DRPCLK, negedge DRPADDR[2], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay[2]);
    $setuphold (posedge DRPCLK, negedge DRPADDR[3], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay[3]);
    $setuphold (posedge DRPCLK, negedge DRPADDR[4], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay[4]);
    $setuphold (posedge DRPCLK, negedge DRPADDR[5], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay[5]);
    $setuphold (posedge DRPCLK, negedge DRPADDR[6], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay[6]);
    $setuphold (posedge DRPCLK, negedge DRPADDR[7], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay[7]);
    $setuphold (posedge DRPCLK, negedge DRPADDR[8], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay[8]);
    $setuphold (posedge DRPCLK, negedge DRPADDR[9], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay[9]);
    $setuphold (posedge DRPCLK, negedge DRPDI[0], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[0]);
    $setuphold (posedge DRPCLK, negedge DRPDI[10], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[10]);
    $setuphold (posedge DRPCLK, negedge DRPDI[11], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[11]);
    $setuphold (posedge DRPCLK, negedge DRPDI[12], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[12]);
    $setuphold (posedge DRPCLK, negedge DRPDI[13], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[13]);
    $setuphold (posedge DRPCLK, negedge DRPDI[14], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[14]);
    $setuphold (posedge DRPCLK, negedge DRPDI[15], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[15]);
    $setuphold (posedge DRPCLK, negedge DRPDI[1], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[1]);
    $setuphold (posedge DRPCLK, negedge DRPDI[2], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[2]);
    $setuphold (posedge DRPCLK, negedge DRPDI[3], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[3]);
    $setuphold (posedge DRPCLK, negedge DRPDI[4], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[4]);
    $setuphold (posedge DRPCLK, negedge DRPDI[5], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[5]);
    $setuphold (posedge DRPCLK, negedge DRPDI[6], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[6]);
    $setuphold (posedge DRPCLK, negedge DRPDI[7], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[7]);
    $setuphold (posedge DRPCLK, negedge DRPDI[8], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[8]);
    $setuphold (posedge DRPCLK, negedge DRPDI[9], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[9]);
    $setuphold (posedge DRPCLK, negedge DRPEN, 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPEN_delay);
    $setuphold (posedge DRPCLK, negedge DRPWE, 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPWE_delay);
    $setuphold (posedge DRPCLK, negedge UBDO[0], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[0]);
    $setuphold (posedge DRPCLK, negedge UBDO[10], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[10]);
    $setuphold (posedge DRPCLK, negedge UBDO[11], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[11]);
    $setuphold (posedge DRPCLK, negedge UBDO[12], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[12]);
    $setuphold (posedge DRPCLK, negedge UBDO[13], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[13]);
    $setuphold (posedge DRPCLK, negedge UBDO[14], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[14]);
    $setuphold (posedge DRPCLK, negedge UBDO[15], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[15]);
    $setuphold (posedge DRPCLK, negedge UBDO[1], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[1]);
    $setuphold (posedge DRPCLK, negedge UBDO[2], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[2]);
    $setuphold (posedge DRPCLK, negedge UBDO[3], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[3]);
    $setuphold (posedge DRPCLK, negedge UBDO[4], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[4]);
    $setuphold (posedge DRPCLK, negedge UBDO[5], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[5]);
    $setuphold (posedge DRPCLK, negedge UBDO[6], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[6]);
    $setuphold (posedge DRPCLK, negedge UBDO[7], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[7]);
    $setuphold (posedge DRPCLK, negedge UBDO[8], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[8]);
    $setuphold (posedge DRPCLK, negedge UBDO[9], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[9]);
    $setuphold (posedge DRPCLK, negedge UBDRDY, 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDRDY_delay);
    $setuphold (posedge DRPCLK, posedge DRPADDR[0], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay[0]);
    $setuphold (posedge DRPCLK, posedge DRPADDR[10], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay[10]);
    $setuphold (posedge DRPCLK, posedge DRPADDR[11], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay[11]);
    $setuphold (posedge DRPCLK, posedge DRPADDR[12], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay[12]);
    $setuphold (posedge DRPCLK, posedge DRPADDR[13], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay[13]);
    $setuphold (posedge DRPCLK, posedge DRPADDR[1], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay[1]);
    $setuphold (posedge DRPCLK, posedge DRPADDR[2], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay[2]);
    $setuphold (posedge DRPCLK, posedge DRPADDR[3], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay[3]);
    $setuphold (posedge DRPCLK, posedge DRPADDR[4], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay[4]);
    $setuphold (posedge DRPCLK, posedge DRPADDR[5], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay[5]);
    $setuphold (posedge DRPCLK, posedge DRPADDR[6], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay[6]);
    $setuphold (posedge DRPCLK, posedge DRPADDR[7], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay[7]);
    $setuphold (posedge DRPCLK, posedge DRPADDR[8], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay[8]);
    $setuphold (posedge DRPCLK, posedge DRPADDR[9], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay[9]);
    $setuphold (posedge DRPCLK, posedge DRPDI[0], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[0]);
    $setuphold (posedge DRPCLK, posedge DRPDI[10], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[10]);
    $setuphold (posedge DRPCLK, posedge DRPDI[11], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[11]);
    $setuphold (posedge DRPCLK, posedge DRPDI[12], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[12]);
    $setuphold (posedge DRPCLK, posedge DRPDI[13], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[13]);
    $setuphold (posedge DRPCLK, posedge DRPDI[14], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[14]);
    $setuphold (posedge DRPCLK, posedge DRPDI[15], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[15]);
    $setuphold (posedge DRPCLK, posedge DRPDI[1], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[1]);
    $setuphold (posedge DRPCLK, posedge DRPDI[2], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[2]);
    $setuphold (posedge DRPCLK, posedge DRPDI[3], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[3]);
    $setuphold (posedge DRPCLK, posedge DRPDI[4], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[4]);
    $setuphold (posedge DRPCLK, posedge DRPDI[5], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[5]);
    $setuphold (posedge DRPCLK, posedge DRPDI[6], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[6]);
    $setuphold (posedge DRPCLK, posedge DRPDI[7], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[7]);
    $setuphold (posedge DRPCLK, posedge DRPDI[8], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[8]);
    $setuphold (posedge DRPCLK, posedge DRPDI[9], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPDI_delay[9]);
    $setuphold (posedge DRPCLK, posedge DRPEN, 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPEN_delay);
    $setuphold (posedge DRPCLK, posedge DRPWE, 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPWE_delay);
    $setuphold (posedge DRPCLK, posedge UBDO[0], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[0]);
    $setuphold (posedge DRPCLK, posedge UBDO[10], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[10]);
    $setuphold (posedge DRPCLK, posedge UBDO[11], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[11]);
    $setuphold (posedge DRPCLK, posedge UBDO[12], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[12]);
    $setuphold (posedge DRPCLK, posedge UBDO[13], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[13]);
    $setuphold (posedge DRPCLK, posedge UBDO[14], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[14]);
    $setuphold (posedge DRPCLK, posedge UBDO[15], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[15]);
    $setuphold (posedge DRPCLK, posedge UBDO[1], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[1]);
    $setuphold (posedge DRPCLK, posedge UBDO[2], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[2]);
    $setuphold (posedge DRPCLK, posedge UBDO[3], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[3]);
    $setuphold (posedge DRPCLK, posedge UBDO[4], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[4]);
    $setuphold (posedge DRPCLK, posedge UBDO[5], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[5]);
    $setuphold (posedge DRPCLK, posedge UBDO[6], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[6]);
    $setuphold (posedge DRPCLK, posedge UBDO[7], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[7]);
    $setuphold (posedge DRPCLK, posedge UBDO[8], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[8]);
    $setuphold (posedge DRPCLK, posedge UBDO[9], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDO_delay[9]);
    $setuphold (posedge DRPCLK, posedge UBDRDY, 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, UBDRDY_delay);
    $width (negedge DRPCLK, 0:0:0, 0, notifier);
    $width (posedge DRPCLK, 0:0:0, 0, notifier);
`endif
    specparam PATHPULSE$ = 0;
  endspecify
`endif
endmodule

`endcelldefine
