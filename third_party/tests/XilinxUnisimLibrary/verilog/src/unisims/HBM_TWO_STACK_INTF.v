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
//  /   /                        HBM_TWO_STACK_INTF
// /___/   /\      Filename    : HBM_TWO_STACK_INTF.v
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

module HBM_TWO_STACK_INTF #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter CLK_SEL_00 = "FALSE",
  parameter CLK_SEL_01 = "FALSE",
  parameter CLK_SEL_02 = "FALSE",
  parameter CLK_SEL_03 = "FALSE",
  parameter CLK_SEL_04 = "FALSE",
  parameter CLK_SEL_05 = "FALSE",
  parameter CLK_SEL_06 = "FALSE",
  parameter CLK_SEL_07 = "FALSE",
  parameter CLK_SEL_08 = "FALSE",
  parameter CLK_SEL_09 = "FALSE",
  parameter CLK_SEL_10 = "FALSE",
  parameter CLK_SEL_11 = "FALSE",
  parameter CLK_SEL_12 = "FALSE",
  parameter CLK_SEL_13 = "FALSE",
  parameter CLK_SEL_14 = "FALSE",
  parameter CLK_SEL_15 = "FALSE",
  parameter CLK_SEL_16 = "FALSE",
  parameter CLK_SEL_17 = "FALSE",
  parameter CLK_SEL_18 = "FALSE",
  parameter CLK_SEL_19 = "FALSE",
  parameter CLK_SEL_20 = "FALSE",
  parameter CLK_SEL_21 = "FALSE",
  parameter CLK_SEL_22 = "FALSE",
  parameter CLK_SEL_23 = "FALSE",
  parameter CLK_SEL_24 = "FALSE",
  parameter CLK_SEL_25 = "FALSE",
  parameter CLK_SEL_26 = "FALSE",
  parameter CLK_SEL_27 = "FALSE",
  parameter CLK_SEL_28 = "FALSE",
  parameter CLK_SEL_29 = "FALSE",
  parameter CLK_SEL_30 = "FALSE",
  parameter CLK_SEL_31 = "FALSE",
  parameter integer DATARATE_00 = 1800,
  parameter integer DATARATE_01 = 1800,
  parameter integer DATARATE_02 = 1800,
  parameter integer DATARATE_03 = 1800,
  parameter integer DATARATE_04 = 1800,
  parameter integer DATARATE_05 = 1800,
  parameter integer DATARATE_06 = 1800,
  parameter integer DATARATE_07 = 1800,
  parameter integer DATARATE_08 = 1800,
  parameter integer DATARATE_09 = 1800,
  parameter integer DATARATE_10 = 1800,
  parameter integer DATARATE_11 = 1800,
  parameter integer DATARATE_12 = 1800,
  parameter integer DATARATE_13 = 1800,
  parameter integer DATARATE_14 = 1800,
  parameter integer DATARATE_15 = 1800,
  parameter DA_LOCKOUT_0 = "FALSE",
  parameter DA_LOCKOUT_1 = "FALSE",
  parameter [0:0] IS_APB_0_PCLK_INVERTED = 1'b0,
  parameter [0:0] IS_APB_0_PRESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_APB_1_PCLK_INVERTED = 1'b0,
  parameter [0:0] IS_APB_1_PRESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_00_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_00_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_01_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_01_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_02_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_02_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_03_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_03_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_04_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_04_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_05_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_05_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_06_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_06_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_07_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_07_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_08_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_08_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_09_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_09_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_10_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_10_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_11_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_11_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_12_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_12_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_13_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_13_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_14_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_14_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_15_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_15_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_16_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_16_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_17_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_17_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_18_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_18_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_19_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_19_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_20_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_20_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_21_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_21_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_22_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_22_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_23_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_23_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_24_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_24_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_25_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_25_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_26_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_26_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_27_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_27_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_28_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_28_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_29_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_29_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_30_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_30_ARESET_N_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_31_ACLK_INVERTED = 1'b0,
  parameter [0:0] IS_AXI_31_ARESET_N_INVERTED = 1'b0,
  parameter MC_ENABLE_00 = "FALSE",
  parameter MC_ENABLE_01 = "FALSE",
  parameter MC_ENABLE_02 = "FALSE",
  parameter MC_ENABLE_03 = "FALSE",
  parameter MC_ENABLE_04 = "FALSE",
  parameter MC_ENABLE_05 = "FALSE",
  parameter MC_ENABLE_06 = "FALSE",
  parameter MC_ENABLE_07 = "FALSE",
  parameter MC_ENABLE_08 = "FALSE",
  parameter MC_ENABLE_09 = "FALSE",
  parameter MC_ENABLE_10 = "FALSE",
  parameter MC_ENABLE_11 = "FALSE",
  parameter MC_ENABLE_12 = "FALSE",
  parameter MC_ENABLE_13 = "FALSE",
  parameter MC_ENABLE_14 = "FALSE",
  parameter MC_ENABLE_15 = "FALSE",
  parameter MC_ENABLE_APB_00 = "FALSE",
  parameter MC_ENABLE_APB_01 = "FALSE",
  parameter integer PAGEHIT_PERCENT_00 = 75,
  parameter integer PAGEHIT_PERCENT_01 = 75,
  parameter PHY_ENABLE_00 = "FALSE",
  parameter PHY_ENABLE_01 = "FALSE",
  parameter PHY_ENABLE_02 = "FALSE",
  parameter PHY_ENABLE_03 = "FALSE",
  parameter PHY_ENABLE_04 = "FALSE",
  parameter PHY_ENABLE_05 = "FALSE",
  parameter PHY_ENABLE_06 = "FALSE",
  parameter PHY_ENABLE_07 = "FALSE",
  parameter PHY_ENABLE_08 = "FALSE",
  parameter PHY_ENABLE_09 = "FALSE",
  parameter PHY_ENABLE_10 = "FALSE",
  parameter PHY_ENABLE_11 = "FALSE",
  parameter PHY_ENABLE_12 = "FALSE",
  parameter PHY_ENABLE_13 = "FALSE",
  parameter PHY_ENABLE_14 = "FALSE",
  parameter PHY_ENABLE_15 = "FALSE",
  parameter PHY_ENABLE_16 = "FALSE",
  parameter PHY_ENABLE_17 = "FALSE",
  parameter PHY_ENABLE_18 = "FALSE",
  parameter PHY_ENABLE_19 = "FALSE",
  parameter PHY_ENABLE_20 = "FALSE",
  parameter PHY_ENABLE_21 = "FALSE",
  parameter PHY_ENABLE_22 = "FALSE",
  parameter PHY_ENABLE_23 = "FALSE",
  parameter PHY_ENABLE_24 = "FALSE",
  parameter PHY_ENABLE_25 = "FALSE",
  parameter PHY_ENABLE_26 = "FALSE",
  parameter PHY_ENABLE_27 = "FALSE",
  parameter PHY_ENABLE_28 = "FALSE",
  parameter PHY_ENABLE_29 = "FALSE",
  parameter PHY_ENABLE_30 = "FALSE",
  parameter PHY_ENABLE_31 = "FALSE",
  parameter PHY_ENABLE_APB_00 = "FALSE",
  parameter PHY_ENABLE_APB_01 = "FALSE",
  parameter PHY_PCLK_INVERT_01 = "FALSE",
  parameter PHY_PCLK_INVERT_02 = "FALSE",
  parameter integer READ_PERCENT_00 = 50,
  parameter integer READ_PERCENT_01 = 50,
  parameter integer READ_PERCENT_02 = 50,
  parameter integer READ_PERCENT_03 = 50,
  parameter integer READ_PERCENT_04 = 50,
  parameter integer READ_PERCENT_05 = 50,
  parameter integer READ_PERCENT_06 = 50,
  parameter integer READ_PERCENT_07 = 50,
  parameter integer READ_PERCENT_08 = 50,
  parameter integer READ_PERCENT_09 = 50,
  parameter integer READ_PERCENT_10 = 50,
  parameter integer READ_PERCENT_11 = 50,
  parameter integer READ_PERCENT_12 = 50,
  parameter integer READ_PERCENT_13 = 50,
  parameter integer READ_PERCENT_14 = 50,
  parameter integer READ_PERCENT_15 = 50,
  parameter integer READ_PERCENT_16 = 50,
  parameter integer READ_PERCENT_17 = 50,
  parameter integer READ_PERCENT_18 = 50,
  parameter integer READ_PERCENT_19 = 50,
  parameter integer READ_PERCENT_20 = 50,
  parameter integer READ_PERCENT_21 = 50,
  parameter integer READ_PERCENT_22 = 50,
  parameter integer READ_PERCENT_23 = 50,
  parameter integer READ_PERCENT_24 = 50,
  parameter integer READ_PERCENT_25 = 50,
  parameter integer READ_PERCENT_26 = 50,
  parameter integer READ_PERCENT_27 = 50,
  parameter integer READ_PERCENT_28 = 50,
  parameter integer READ_PERCENT_29 = 50,
  parameter integer READ_PERCENT_30 = 50,
  parameter integer READ_PERCENT_31 = 50,
  parameter SIM_DEVICE = "ULTRASCALE_PLUS",
  parameter SWITCH_ENABLE_00 = "FALSE",
  parameter SWITCH_ENABLE_01 = "FALSE",
  parameter integer WRITE_PERCENT_00 = 50,
  parameter integer WRITE_PERCENT_01 = 50,
  parameter integer WRITE_PERCENT_02 = 50,
  parameter integer WRITE_PERCENT_03 = 50,
  parameter integer WRITE_PERCENT_04 = 50,
  parameter integer WRITE_PERCENT_05 = 50,
  parameter integer WRITE_PERCENT_06 = 50,
  parameter integer WRITE_PERCENT_07 = 50,
  parameter integer WRITE_PERCENT_08 = 50,
  parameter integer WRITE_PERCENT_09 = 50,
  parameter integer WRITE_PERCENT_10 = 50,
  parameter integer WRITE_PERCENT_11 = 50,
  parameter integer WRITE_PERCENT_12 = 50,
  parameter integer WRITE_PERCENT_13 = 50,
  parameter integer WRITE_PERCENT_14 = 50,
  parameter integer WRITE_PERCENT_15 = 50,
  parameter integer WRITE_PERCENT_16 = 50,
  parameter integer WRITE_PERCENT_17 = 50,
  parameter integer WRITE_PERCENT_18 = 50,
  parameter integer WRITE_PERCENT_19 = 50,
  parameter integer WRITE_PERCENT_20 = 50,
  parameter integer WRITE_PERCENT_21 = 50,
  parameter integer WRITE_PERCENT_22 = 50,
  parameter integer WRITE_PERCENT_23 = 50,
  parameter integer WRITE_PERCENT_24 = 50,
  parameter integer WRITE_PERCENT_25 = 50,
  parameter integer WRITE_PERCENT_26 = 50,
  parameter integer WRITE_PERCENT_27 = 50,
  parameter integer WRITE_PERCENT_28 = 50,
  parameter integer WRITE_PERCENT_29 = 50,
  parameter integer WRITE_PERCENT_30 = 50,
  parameter integer WRITE_PERCENT_31 = 50
)(
  output [31:0] APB_0_PRDATA,
  output APB_0_PREADY,
  output APB_0_PSLVERR,
  output [31:0] APB_1_PRDATA,
  output APB_1_PREADY,
  output APB_1_PSLVERR,
  output AXI_00_ARREADY,
  output AXI_00_AWREADY,
  output [5:0] AXI_00_BID,
  output [1:0] AXI_00_BRESP,
  output AXI_00_BVALID,
  output [1:0] AXI_00_DFI_AW_AERR_N,
  output AXI_00_DFI_CLK_BUF,
  output [7:0] AXI_00_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_00_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_00_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_00_DFI_DW_RDDATA_VALID,
  output AXI_00_DFI_INIT_COMPLETE,
  output AXI_00_DFI_PHYUPD_REQ,
  output AXI_00_DFI_PHY_LP_STATE,
  output AXI_00_DFI_RST_N_BUF,
  output [5:0] AXI_00_MC_STATUS,
  output [7:0] AXI_00_PHY_STATUS,
  output [255:0] AXI_00_RDATA,
  output [31:0] AXI_00_RDATA_PARITY,
  output [5:0] AXI_00_RID,
  output AXI_00_RLAST,
  output [1:0] AXI_00_RRESP,
  output AXI_00_RVALID,
  output AXI_00_WREADY,
  output AXI_01_ARREADY,
  output AXI_01_AWREADY,
  output [5:0] AXI_01_BID,
  output [1:0] AXI_01_BRESP,
  output AXI_01_BVALID,
  output [1:0] AXI_01_DFI_AW_AERR_N,
  output AXI_01_DFI_CLK_BUF,
  output [7:0] AXI_01_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_01_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_01_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_01_DFI_DW_RDDATA_VALID,
  output AXI_01_DFI_INIT_COMPLETE,
  output AXI_01_DFI_PHYUPD_REQ,
  output AXI_01_DFI_PHY_LP_STATE,
  output AXI_01_DFI_RST_N_BUF,
  output [255:0] AXI_01_RDATA,
  output [31:0] AXI_01_RDATA_PARITY,
  output [5:0] AXI_01_RID,
  output AXI_01_RLAST,
  output [1:0] AXI_01_RRESP,
  output AXI_01_RVALID,
  output AXI_01_WREADY,
  output AXI_02_ARREADY,
  output AXI_02_AWREADY,
  output [5:0] AXI_02_BID,
  output [1:0] AXI_02_BRESP,
  output AXI_02_BVALID,
  output [1:0] AXI_02_DFI_AW_AERR_N,
  output AXI_02_DFI_CLK_BUF,
  output [7:0] AXI_02_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_02_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_02_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_02_DFI_DW_RDDATA_VALID,
  output AXI_02_DFI_INIT_COMPLETE,
  output AXI_02_DFI_PHYUPD_REQ,
  output AXI_02_DFI_PHY_LP_STATE,
  output AXI_02_DFI_RST_N_BUF,
  output [5:0] AXI_02_MC_STATUS,
  output [7:0] AXI_02_PHY_STATUS,
  output [255:0] AXI_02_RDATA,
  output [31:0] AXI_02_RDATA_PARITY,
  output [5:0] AXI_02_RID,
  output AXI_02_RLAST,
  output [1:0] AXI_02_RRESP,
  output AXI_02_RVALID,
  output AXI_02_WREADY,
  output AXI_03_ARREADY,
  output AXI_03_AWREADY,
  output [5:0] AXI_03_BID,
  output [1:0] AXI_03_BRESP,
  output AXI_03_BVALID,
  output [1:0] AXI_03_DFI_AW_AERR_N,
  output AXI_03_DFI_CLK_BUF,
  output [7:0] AXI_03_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_03_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_03_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_03_DFI_DW_RDDATA_VALID,
  output AXI_03_DFI_INIT_COMPLETE,
  output AXI_03_DFI_PHYUPD_REQ,
  output AXI_03_DFI_PHY_LP_STATE,
  output AXI_03_DFI_RST_N_BUF,
  output [255:0] AXI_03_RDATA,
  output [31:0] AXI_03_RDATA_PARITY,
  output [5:0] AXI_03_RID,
  output AXI_03_RLAST,
  output [1:0] AXI_03_RRESP,
  output AXI_03_RVALID,
  output AXI_03_WREADY,
  output AXI_04_ARREADY,
  output AXI_04_AWREADY,
  output [5:0] AXI_04_BID,
  output [1:0] AXI_04_BRESP,
  output AXI_04_BVALID,
  output [1:0] AXI_04_DFI_AW_AERR_N,
  output AXI_04_DFI_CLK_BUF,
  output [7:0] AXI_04_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_04_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_04_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_04_DFI_DW_RDDATA_VALID,
  output AXI_04_DFI_INIT_COMPLETE,
  output AXI_04_DFI_PHYUPD_REQ,
  output AXI_04_DFI_PHY_LP_STATE,
  output AXI_04_DFI_RST_N_BUF,
  output [5:0] AXI_04_MC_STATUS,
  output [7:0] AXI_04_PHY_STATUS,
  output [255:0] AXI_04_RDATA,
  output [31:0] AXI_04_RDATA_PARITY,
  output [5:0] AXI_04_RID,
  output AXI_04_RLAST,
  output [1:0] AXI_04_RRESP,
  output AXI_04_RVALID,
  output AXI_04_WREADY,
  output AXI_05_ARREADY,
  output AXI_05_AWREADY,
  output [5:0] AXI_05_BID,
  output [1:0] AXI_05_BRESP,
  output AXI_05_BVALID,
  output [1:0] AXI_05_DFI_AW_AERR_N,
  output AXI_05_DFI_CLK_BUF,
  output [7:0] AXI_05_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_05_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_05_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_05_DFI_DW_RDDATA_VALID,
  output AXI_05_DFI_INIT_COMPLETE,
  output AXI_05_DFI_PHYUPD_REQ,
  output AXI_05_DFI_PHY_LP_STATE,
  output AXI_05_DFI_RST_N_BUF,
  output [255:0] AXI_05_RDATA,
  output [31:0] AXI_05_RDATA_PARITY,
  output [5:0] AXI_05_RID,
  output AXI_05_RLAST,
  output [1:0] AXI_05_RRESP,
  output AXI_05_RVALID,
  output AXI_05_WREADY,
  output AXI_06_ARREADY,
  output AXI_06_AWREADY,
  output [5:0] AXI_06_BID,
  output [1:0] AXI_06_BRESP,
  output AXI_06_BVALID,
  output [1:0] AXI_06_DFI_AW_AERR_N,
  output AXI_06_DFI_CLK_BUF,
  output [7:0] AXI_06_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_06_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_06_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_06_DFI_DW_RDDATA_VALID,
  output AXI_06_DFI_INIT_COMPLETE,
  output AXI_06_DFI_PHYUPD_REQ,
  output AXI_06_DFI_PHY_LP_STATE,
  output AXI_06_DFI_RST_N_BUF,
  output [5:0] AXI_06_MC_STATUS,
  output [7:0] AXI_06_PHY_STATUS,
  output [255:0] AXI_06_RDATA,
  output [31:0] AXI_06_RDATA_PARITY,
  output [5:0] AXI_06_RID,
  output AXI_06_RLAST,
  output [1:0] AXI_06_RRESP,
  output AXI_06_RVALID,
  output AXI_06_WREADY,
  output AXI_07_ARREADY,
  output AXI_07_AWREADY,
  output [5:0] AXI_07_BID,
  output [1:0] AXI_07_BRESP,
  output AXI_07_BVALID,
  output [1:0] AXI_07_DFI_AW_AERR_N,
  output AXI_07_DFI_CLK_BUF,
  output [7:0] AXI_07_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_07_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_07_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_07_DFI_DW_RDDATA_VALID,
  output AXI_07_DFI_INIT_COMPLETE,
  output AXI_07_DFI_PHYUPD_REQ,
  output AXI_07_DFI_PHY_LP_STATE,
  output AXI_07_DFI_RST_N_BUF,
  output [255:0] AXI_07_RDATA,
  output [31:0] AXI_07_RDATA_PARITY,
  output [5:0] AXI_07_RID,
  output AXI_07_RLAST,
  output [1:0] AXI_07_RRESP,
  output AXI_07_RVALID,
  output AXI_07_WREADY,
  output AXI_08_ARREADY,
  output AXI_08_AWREADY,
  output [5:0] AXI_08_BID,
  output [1:0] AXI_08_BRESP,
  output AXI_08_BVALID,
  output [1:0] AXI_08_DFI_AW_AERR_N,
  output AXI_08_DFI_CLK_BUF,
  output [7:0] AXI_08_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_08_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_08_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_08_DFI_DW_RDDATA_VALID,
  output AXI_08_DFI_INIT_COMPLETE,
  output AXI_08_DFI_PHYUPD_REQ,
  output AXI_08_DFI_PHY_LP_STATE,
  output AXI_08_DFI_RST_N_BUF,
  output [5:0] AXI_08_MC_STATUS,
  output [7:0] AXI_08_PHY_STATUS,
  output [255:0] AXI_08_RDATA,
  output [31:0] AXI_08_RDATA_PARITY,
  output [5:0] AXI_08_RID,
  output AXI_08_RLAST,
  output [1:0] AXI_08_RRESP,
  output AXI_08_RVALID,
  output AXI_08_WREADY,
  output AXI_09_ARREADY,
  output AXI_09_AWREADY,
  output [5:0] AXI_09_BID,
  output [1:0] AXI_09_BRESP,
  output AXI_09_BVALID,
  output [1:0] AXI_09_DFI_AW_AERR_N,
  output AXI_09_DFI_CLK_BUF,
  output [7:0] AXI_09_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_09_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_09_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_09_DFI_DW_RDDATA_VALID,
  output AXI_09_DFI_INIT_COMPLETE,
  output AXI_09_DFI_PHYUPD_REQ,
  output AXI_09_DFI_PHY_LP_STATE,
  output AXI_09_DFI_RST_N_BUF,
  output [255:0] AXI_09_RDATA,
  output [31:0] AXI_09_RDATA_PARITY,
  output [5:0] AXI_09_RID,
  output AXI_09_RLAST,
  output [1:0] AXI_09_RRESP,
  output AXI_09_RVALID,
  output AXI_09_WREADY,
  output AXI_10_ARREADY,
  output AXI_10_AWREADY,
  output [5:0] AXI_10_BID,
  output [1:0] AXI_10_BRESP,
  output AXI_10_BVALID,
  output [1:0] AXI_10_DFI_AW_AERR_N,
  output AXI_10_DFI_CLK_BUF,
  output [7:0] AXI_10_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_10_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_10_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_10_DFI_DW_RDDATA_VALID,
  output AXI_10_DFI_INIT_COMPLETE,
  output AXI_10_DFI_PHYUPD_REQ,
  output AXI_10_DFI_PHY_LP_STATE,
  output AXI_10_DFI_RST_N_BUF,
  output [5:0] AXI_10_MC_STATUS,
  output [7:0] AXI_10_PHY_STATUS,
  output [255:0] AXI_10_RDATA,
  output [31:0] AXI_10_RDATA_PARITY,
  output [5:0] AXI_10_RID,
  output AXI_10_RLAST,
  output [1:0] AXI_10_RRESP,
  output AXI_10_RVALID,
  output AXI_10_WREADY,
  output AXI_11_ARREADY,
  output AXI_11_AWREADY,
  output [5:0] AXI_11_BID,
  output [1:0] AXI_11_BRESP,
  output AXI_11_BVALID,
  output [1:0] AXI_11_DFI_AW_AERR_N,
  output AXI_11_DFI_CLK_BUF,
  output [7:0] AXI_11_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_11_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_11_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_11_DFI_DW_RDDATA_VALID,
  output AXI_11_DFI_INIT_COMPLETE,
  output AXI_11_DFI_PHYUPD_REQ,
  output AXI_11_DFI_PHY_LP_STATE,
  output AXI_11_DFI_RST_N_BUF,
  output [255:0] AXI_11_RDATA,
  output [31:0] AXI_11_RDATA_PARITY,
  output [5:0] AXI_11_RID,
  output AXI_11_RLAST,
  output [1:0] AXI_11_RRESP,
  output AXI_11_RVALID,
  output AXI_11_WREADY,
  output AXI_12_ARREADY,
  output AXI_12_AWREADY,
  output [5:0] AXI_12_BID,
  output [1:0] AXI_12_BRESP,
  output AXI_12_BVALID,
  output [1:0] AXI_12_DFI_AW_AERR_N,
  output AXI_12_DFI_CLK_BUF,
  output [7:0] AXI_12_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_12_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_12_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_12_DFI_DW_RDDATA_VALID,
  output AXI_12_DFI_INIT_COMPLETE,
  output AXI_12_DFI_PHYUPD_REQ,
  output AXI_12_DFI_PHY_LP_STATE,
  output AXI_12_DFI_RST_N_BUF,
  output [5:0] AXI_12_MC_STATUS,
  output [7:0] AXI_12_PHY_STATUS,
  output [255:0] AXI_12_RDATA,
  output [31:0] AXI_12_RDATA_PARITY,
  output [5:0] AXI_12_RID,
  output AXI_12_RLAST,
  output [1:0] AXI_12_RRESP,
  output AXI_12_RVALID,
  output AXI_12_WREADY,
  output AXI_13_ARREADY,
  output AXI_13_AWREADY,
  output [5:0] AXI_13_BID,
  output [1:0] AXI_13_BRESP,
  output AXI_13_BVALID,
  output [1:0] AXI_13_DFI_AW_AERR_N,
  output AXI_13_DFI_CLK_BUF,
  output [7:0] AXI_13_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_13_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_13_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_13_DFI_DW_RDDATA_VALID,
  output AXI_13_DFI_INIT_COMPLETE,
  output AXI_13_DFI_PHYUPD_REQ,
  output AXI_13_DFI_PHY_LP_STATE,
  output AXI_13_DFI_RST_N_BUF,
  output [255:0] AXI_13_RDATA,
  output [31:0] AXI_13_RDATA_PARITY,
  output [5:0] AXI_13_RID,
  output AXI_13_RLAST,
  output [1:0] AXI_13_RRESP,
  output AXI_13_RVALID,
  output AXI_13_WREADY,
  output AXI_14_ARREADY,
  output AXI_14_AWREADY,
  output [5:0] AXI_14_BID,
  output [1:0] AXI_14_BRESP,
  output AXI_14_BVALID,
  output [1:0] AXI_14_DFI_AW_AERR_N,
  output AXI_14_DFI_CLK_BUF,
  output [7:0] AXI_14_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_14_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_14_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_14_DFI_DW_RDDATA_VALID,
  output AXI_14_DFI_INIT_COMPLETE,
  output AXI_14_DFI_PHYUPD_REQ,
  output AXI_14_DFI_PHY_LP_STATE,
  output AXI_14_DFI_RST_N_BUF,
  output [5:0] AXI_14_MC_STATUS,
  output [7:0] AXI_14_PHY_STATUS,
  output [255:0] AXI_14_RDATA,
  output [31:0] AXI_14_RDATA_PARITY,
  output [5:0] AXI_14_RID,
  output AXI_14_RLAST,
  output [1:0] AXI_14_RRESP,
  output AXI_14_RVALID,
  output AXI_14_WREADY,
  output AXI_15_ARREADY,
  output AXI_15_AWREADY,
  output [5:0] AXI_15_BID,
  output [1:0] AXI_15_BRESP,
  output AXI_15_BVALID,
  output [1:0] AXI_15_DFI_AW_AERR_N,
  output AXI_15_DFI_CLK_BUF,
  output [7:0] AXI_15_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_15_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_15_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_15_DFI_DW_RDDATA_VALID,
  output AXI_15_DFI_INIT_COMPLETE,
  output AXI_15_DFI_PHYUPD_REQ,
  output AXI_15_DFI_PHY_LP_STATE,
  output AXI_15_DFI_RST_N_BUF,
  output [255:0] AXI_15_RDATA,
  output [31:0] AXI_15_RDATA_PARITY,
  output [5:0] AXI_15_RID,
  output AXI_15_RLAST,
  output [1:0] AXI_15_RRESP,
  output AXI_15_RVALID,
  output AXI_15_WREADY,
  output AXI_16_ARREADY,
  output AXI_16_AWREADY,
  output [5:0] AXI_16_BID,
  output [1:0] AXI_16_BRESP,
  output AXI_16_BVALID,
  output [1:0] AXI_16_DFI_AW_AERR_N,
  output AXI_16_DFI_CLK_BUF,
  output [7:0] AXI_16_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_16_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_16_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_16_DFI_DW_RDDATA_VALID,
  output AXI_16_DFI_INIT_COMPLETE,
  output AXI_16_DFI_PHYUPD_REQ,
  output AXI_16_DFI_PHY_LP_STATE,
  output AXI_16_DFI_RST_N_BUF,
  output [5:0] AXI_16_MC_STATUS,
  output [7:0] AXI_16_PHY_STATUS,
  output [255:0] AXI_16_RDATA,
  output [31:0] AXI_16_RDATA_PARITY,
  output [5:0] AXI_16_RID,
  output AXI_16_RLAST,
  output [1:0] AXI_16_RRESP,
  output AXI_16_RVALID,
  output AXI_16_WREADY,
  output AXI_17_ARREADY,
  output AXI_17_AWREADY,
  output [5:0] AXI_17_BID,
  output [1:0] AXI_17_BRESP,
  output AXI_17_BVALID,
  output [1:0] AXI_17_DFI_AW_AERR_N,
  output AXI_17_DFI_CLK_BUF,
  output [7:0] AXI_17_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_17_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_17_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_17_DFI_DW_RDDATA_VALID,
  output AXI_17_DFI_INIT_COMPLETE,
  output AXI_17_DFI_PHYUPD_REQ,
  output AXI_17_DFI_PHY_LP_STATE,
  output AXI_17_DFI_RST_N_BUF,
  output [255:0] AXI_17_RDATA,
  output [31:0] AXI_17_RDATA_PARITY,
  output [5:0] AXI_17_RID,
  output AXI_17_RLAST,
  output [1:0] AXI_17_RRESP,
  output AXI_17_RVALID,
  output AXI_17_WREADY,
  output AXI_18_ARREADY,
  output AXI_18_AWREADY,
  output [5:0] AXI_18_BID,
  output [1:0] AXI_18_BRESP,
  output AXI_18_BVALID,
  output [1:0] AXI_18_DFI_AW_AERR_N,
  output AXI_18_DFI_CLK_BUF,
  output [7:0] AXI_18_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_18_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_18_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_18_DFI_DW_RDDATA_VALID,
  output AXI_18_DFI_INIT_COMPLETE,
  output AXI_18_DFI_PHYUPD_REQ,
  output AXI_18_DFI_PHY_LP_STATE,
  output AXI_18_DFI_RST_N_BUF,
  output [5:0] AXI_18_MC_STATUS,
  output [7:0] AXI_18_PHY_STATUS,
  output [255:0] AXI_18_RDATA,
  output [31:0] AXI_18_RDATA_PARITY,
  output [5:0] AXI_18_RID,
  output AXI_18_RLAST,
  output [1:0] AXI_18_RRESP,
  output AXI_18_RVALID,
  output AXI_18_WREADY,
  output AXI_19_ARREADY,
  output AXI_19_AWREADY,
  output [5:0] AXI_19_BID,
  output [1:0] AXI_19_BRESP,
  output AXI_19_BVALID,
  output [1:0] AXI_19_DFI_AW_AERR_N,
  output AXI_19_DFI_CLK_BUF,
  output [7:0] AXI_19_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_19_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_19_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_19_DFI_DW_RDDATA_VALID,
  output AXI_19_DFI_INIT_COMPLETE,
  output AXI_19_DFI_PHYUPD_REQ,
  output AXI_19_DFI_PHY_LP_STATE,
  output AXI_19_DFI_RST_N_BUF,
  output [255:0] AXI_19_RDATA,
  output [31:0] AXI_19_RDATA_PARITY,
  output [5:0] AXI_19_RID,
  output AXI_19_RLAST,
  output [1:0] AXI_19_RRESP,
  output AXI_19_RVALID,
  output AXI_19_WREADY,
  output AXI_20_ARREADY,
  output AXI_20_AWREADY,
  output [5:0] AXI_20_BID,
  output [1:0] AXI_20_BRESP,
  output AXI_20_BVALID,
  output [1:0] AXI_20_DFI_AW_AERR_N,
  output AXI_20_DFI_CLK_BUF,
  output [7:0] AXI_20_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_20_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_20_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_20_DFI_DW_RDDATA_VALID,
  output AXI_20_DFI_INIT_COMPLETE,
  output AXI_20_DFI_PHYUPD_REQ,
  output AXI_20_DFI_PHY_LP_STATE,
  output AXI_20_DFI_RST_N_BUF,
  output [5:0] AXI_20_MC_STATUS,
  output [7:0] AXI_20_PHY_STATUS,
  output [255:0] AXI_20_RDATA,
  output [31:0] AXI_20_RDATA_PARITY,
  output [5:0] AXI_20_RID,
  output AXI_20_RLAST,
  output [1:0] AXI_20_RRESP,
  output AXI_20_RVALID,
  output AXI_20_WREADY,
  output AXI_21_ARREADY,
  output AXI_21_AWREADY,
  output [5:0] AXI_21_BID,
  output [1:0] AXI_21_BRESP,
  output AXI_21_BVALID,
  output [1:0] AXI_21_DFI_AW_AERR_N,
  output AXI_21_DFI_CLK_BUF,
  output [7:0] AXI_21_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_21_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_21_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_21_DFI_DW_RDDATA_VALID,
  output AXI_21_DFI_INIT_COMPLETE,
  output AXI_21_DFI_PHYUPD_REQ,
  output AXI_21_DFI_PHY_LP_STATE,
  output AXI_21_DFI_RST_N_BUF,
  output [255:0] AXI_21_RDATA,
  output [31:0] AXI_21_RDATA_PARITY,
  output [5:0] AXI_21_RID,
  output AXI_21_RLAST,
  output [1:0] AXI_21_RRESP,
  output AXI_21_RVALID,
  output AXI_21_WREADY,
  output AXI_22_ARREADY,
  output AXI_22_AWREADY,
  output [5:0] AXI_22_BID,
  output [1:0] AXI_22_BRESP,
  output AXI_22_BVALID,
  output [1:0] AXI_22_DFI_AW_AERR_N,
  output AXI_22_DFI_CLK_BUF,
  output [7:0] AXI_22_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_22_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_22_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_22_DFI_DW_RDDATA_VALID,
  output AXI_22_DFI_INIT_COMPLETE,
  output AXI_22_DFI_PHYUPD_REQ,
  output AXI_22_DFI_PHY_LP_STATE,
  output AXI_22_DFI_RST_N_BUF,
  output [5:0] AXI_22_MC_STATUS,
  output [7:0] AXI_22_PHY_STATUS,
  output [255:0] AXI_22_RDATA,
  output [31:0] AXI_22_RDATA_PARITY,
  output [5:0] AXI_22_RID,
  output AXI_22_RLAST,
  output [1:0] AXI_22_RRESP,
  output AXI_22_RVALID,
  output AXI_22_WREADY,
  output AXI_23_ARREADY,
  output AXI_23_AWREADY,
  output [5:0] AXI_23_BID,
  output [1:0] AXI_23_BRESP,
  output AXI_23_BVALID,
  output [1:0] AXI_23_DFI_AW_AERR_N,
  output AXI_23_DFI_CLK_BUF,
  output [7:0] AXI_23_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_23_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_23_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_23_DFI_DW_RDDATA_VALID,
  output AXI_23_DFI_INIT_COMPLETE,
  output AXI_23_DFI_PHYUPD_REQ,
  output AXI_23_DFI_PHY_LP_STATE,
  output AXI_23_DFI_RST_N_BUF,
  output [255:0] AXI_23_RDATA,
  output [31:0] AXI_23_RDATA_PARITY,
  output [5:0] AXI_23_RID,
  output AXI_23_RLAST,
  output [1:0] AXI_23_RRESP,
  output AXI_23_RVALID,
  output AXI_23_WREADY,
  output AXI_24_ARREADY,
  output AXI_24_AWREADY,
  output [5:0] AXI_24_BID,
  output [1:0] AXI_24_BRESP,
  output AXI_24_BVALID,
  output [1:0] AXI_24_DFI_AW_AERR_N,
  output AXI_24_DFI_CLK_BUF,
  output [7:0] AXI_24_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_24_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_24_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_24_DFI_DW_RDDATA_VALID,
  output AXI_24_DFI_INIT_COMPLETE,
  output AXI_24_DFI_PHYUPD_REQ,
  output AXI_24_DFI_PHY_LP_STATE,
  output AXI_24_DFI_RST_N_BUF,
  output [5:0] AXI_24_MC_STATUS,
  output [7:0] AXI_24_PHY_STATUS,
  output [255:0] AXI_24_RDATA,
  output [31:0] AXI_24_RDATA_PARITY,
  output [5:0] AXI_24_RID,
  output AXI_24_RLAST,
  output [1:0] AXI_24_RRESP,
  output AXI_24_RVALID,
  output AXI_24_WREADY,
  output AXI_25_ARREADY,
  output AXI_25_AWREADY,
  output [5:0] AXI_25_BID,
  output [1:0] AXI_25_BRESP,
  output AXI_25_BVALID,
  output [1:0] AXI_25_DFI_AW_AERR_N,
  output AXI_25_DFI_CLK_BUF,
  output [7:0] AXI_25_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_25_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_25_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_25_DFI_DW_RDDATA_VALID,
  output AXI_25_DFI_INIT_COMPLETE,
  output AXI_25_DFI_PHYUPD_REQ,
  output AXI_25_DFI_PHY_LP_STATE,
  output AXI_25_DFI_RST_N_BUF,
  output [255:0] AXI_25_RDATA,
  output [31:0] AXI_25_RDATA_PARITY,
  output [5:0] AXI_25_RID,
  output AXI_25_RLAST,
  output [1:0] AXI_25_RRESP,
  output AXI_25_RVALID,
  output AXI_25_WREADY,
  output AXI_26_ARREADY,
  output AXI_26_AWREADY,
  output [5:0] AXI_26_BID,
  output [1:0] AXI_26_BRESP,
  output AXI_26_BVALID,
  output [1:0] AXI_26_DFI_AW_AERR_N,
  output AXI_26_DFI_CLK_BUF,
  output [7:0] AXI_26_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_26_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_26_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_26_DFI_DW_RDDATA_VALID,
  output AXI_26_DFI_INIT_COMPLETE,
  output AXI_26_DFI_PHYUPD_REQ,
  output AXI_26_DFI_PHY_LP_STATE,
  output AXI_26_DFI_RST_N_BUF,
  output [5:0] AXI_26_MC_STATUS,
  output [7:0] AXI_26_PHY_STATUS,
  output [255:0] AXI_26_RDATA,
  output [31:0] AXI_26_RDATA_PARITY,
  output [5:0] AXI_26_RID,
  output AXI_26_RLAST,
  output [1:0] AXI_26_RRESP,
  output AXI_26_RVALID,
  output AXI_26_WREADY,
  output AXI_27_ARREADY,
  output AXI_27_AWREADY,
  output [5:0] AXI_27_BID,
  output [1:0] AXI_27_BRESP,
  output AXI_27_BVALID,
  output [1:0] AXI_27_DFI_AW_AERR_N,
  output AXI_27_DFI_CLK_BUF,
  output [7:0] AXI_27_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_27_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_27_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_27_DFI_DW_RDDATA_VALID,
  output AXI_27_DFI_INIT_COMPLETE,
  output AXI_27_DFI_PHYUPD_REQ,
  output AXI_27_DFI_PHY_LP_STATE,
  output AXI_27_DFI_RST_N_BUF,
  output [255:0] AXI_27_RDATA,
  output [31:0] AXI_27_RDATA_PARITY,
  output [5:0] AXI_27_RID,
  output AXI_27_RLAST,
  output [1:0] AXI_27_RRESP,
  output AXI_27_RVALID,
  output AXI_27_WREADY,
  output AXI_28_ARREADY,
  output AXI_28_AWREADY,
  output [5:0] AXI_28_BID,
  output [1:0] AXI_28_BRESP,
  output AXI_28_BVALID,
  output [1:0] AXI_28_DFI_AW_AERR_N,
  output AXI_28_DFI_CLK_BUF,
  output [7:0] AXI_28_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_28_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_28_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_28_DFI_DW_RDDATA_VALID,
  output AXI_28_DFI_INIT_COMPLETE,
  output AXI_28_DFI_PHYUPD_REQ,
  output AXI_28_DFI_PHY_LP_STATE,
  output AXI_28_DFI_RST_N_BUF,
  output [5:0] AXI_28_MC_STATUS,
  output [7:0] AXI_28_PHY_STATUS,
  output [255:0] AXI_28_RDATA,
  output [31:0] AXI_28_RDATA_PARITY,
  output [5:0] AXI_28_RID,
  output AXI_28_RLAST,
  output [1:0] AXI_28_RRESP,
  output AXI_28_RVALID,
  output AXI_28_WREADY,
  output AXI_29_ARREADY,
  output AXI_29_AWREADY,
  output [5:0] AXI_29_BID,
  output [1:0] AXI_29_BRESP,
  output AXI_29_BVALID,
  output [1:0] AXI_29_DFI_AW_AERR_N,
  output AXI_29_DFI_CLK_BUF,
  output [7:0] AXI_29_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_29_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_29_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_29_DFI_DW_RDDATA_VALID,
  output AXI_29_DFI_INIT_COMPLETE,
  output AXI_29_DFI_PHYUPD_REQ,
  output AXI_29_DFI_PHY_LP_STATE,
  output AXI_29_DFI_RST_N_BUF,
  output [255:0] AXI_29_RDATA,
  output [31:0] AXI_29_RDATA_PARITY,
  output [5:0] AXI_29_RID,
  output AXI_29_RLAST,
  output [1:0] AXI_29_RRESP,
  output AXI_29_RVALID,
  output AXI_29_WREADY,
  output AXI_30_ARREADY,
  output AXI_30_AWREADY,
  output [5:0] AXI_30_BID,
  output [1:0] AXI_30_BRESP,
  output AXI_30_BVALID,
  output [1:0] AXI_30_DFI_AW_AERR_N,
  output AXI_30_DFI_CLK_BUF,
  output [7:0] AXI_30_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_30_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_30_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_30_DFI_DW_RDDATA_VALID,
  output AXI_30_DFI_INIT_COMPLETE,
  output AXI_30_DFI_PHYUPD_REQ,
  output AXI_30_DFI_PHY_LP_STATE,
  output AXI_30_DFI_RST_N_BUF,
  output [5:0] AXI_30_MC_STATUS,
  output [7:0] AXI_30_PHY_STATUS,
  output [255:0] AXI_30_RDATA,
  output [31:0] AXI_30_RDATA_PARITY,
  output [5:0] AXI_30_RID,
  output AXI_30_RLAST,
  output [1:0] AXI_30_RRESP,
  output AXI_30_RVALID,
  output AXI_30_WREADY,
  output AXI_31_ARREADY,
  output AXI_31_AWREADY,
  output [5:0] AXI_31_BID,
  output [1:0] AXI_31_BRESP,
  output AXI_31_BVALID,
  output [1:0] AXI_31_DFI_AW_AERR_N,
  output AXI_31_DFI_CLK_BUF,
  output [7:0] AXI_31_DFI_DBI_BYTE_DISABLE,
  output [20:0] AXI_31_DFI_DW_RDDATA_DBI,
  output [7:0] AXI_31_DFI_DW_RDDATA_DERR,
  output [1:0] AXI_31_DFI_DW_RDDATA_VALID,
  output AXI_31_DFI_INIT_COMPLETE,
  output AXI_31_DFI_PHYUPD_REQ,
  output AXI_31_DFI_PHY_LP_STATE,
  output AXI_31_DFI_RST_N_BUF,
  output [255:0] AXI_31_RDATA,
  output [31:0] AXI_31_RDATA_PARITY,
  output [5:0] AXI_31_RID,
  output AXI_31_RLAST,
  output [1:0] AXI_31_RRESP,
  output AXI_31_RVALID,
  output AXI_31_WREADY,
  output DRAM_0_STAT_CATTRIP,
  output [2:0] DRAM_0_STAT_TEMP,
  output DRAM_1_STAT_CATTRIP,
  output [2:0] DRAM_1_STAT_TEMP,

  input [21:0] APB_0_PADDR,
  input APB_0_PCLK,
  input APB_0_PENABLE,
  input APB_0_PRESET_N,
  input APB_0_PSEL,
  input [31:0] APB_0_PWDATA,
  input APB_0_PWRITE,
  input [21:0] APB_1_PADDR,
  input APB_1_PCLK,
  input APB_1_PENABLE,
  input APB_1_PRESET_N,
  input APB_1_PSEL,
  input [31:0] APB_1_PWDATA,
  input APB_1_PWRITE,
  input AXI_00_ACLK,
  input [36:0] AXI_00_ARADDR,
  input [1:0] AXI_00_ARBURST,
  input AXI_00_ARESET_N,
  input [5:0] AXI_00_ARID,
  input [3:0] AXI_00_ARLEN,
  input [2:0] AXI_00_ARSIZE,
  input AXI_00_ARVALID,
  input [36:0] AXI_00_AWADDR,
  input [1:0] AXI_00_AWBURST,
  input [5:0] AXI_00_AWID,
  input [3:0] AXI_00_AWLEN,
  input [2:0] AXI_00_AWSIZE,
  input AXI_00_AWVALID,
  input AXI_00_BREADY,
  input AXI_00_DFI_LP_PWR_X_REQ,
  input AXI_00_RREADY,
  input [255:0] AXI_00_WDATA,
  input [31:0] AXI_00_WDATA_PARITY,
  input AXI_00_WLAST,
  input [31:0] AXI_00_WSTRB,
  input AXI_00_WVALID,
  input AXI_01_ACLK,
  input [36:0] AXI_01_ARADDR,
  input [1:0] AXI_01_ARBURST,
  input AXI_01_ARESET_N,
  input [5:0] AXI_01_ARID,
  input [3:0] AXI_01_ARLEN,
  input [2:0] AXI_01_ARSIZE,
  input AXI_01_ARVALID,
  input [36:0] AXI_01_AWADDR,
  input [1:0] AXI_01_AWBURST,
  input [5:0] AXI_01_AWID,
  input [3:0] AXI_01_AWLEN,
  input [2:0] AXI_01_AWSIZE,
  input AXI_01_AWVALID,
  input AXI_01_BREADY,
  input AXI_01_DFI_LP_PWR_X_REQ,
  input AXI_01_RREADY,
  input [255:0] AXI_01_WDATA,
  input [31:0] AXI_01_WDATA_PARITY,
  input AXI_01_WLAST,
  input [31:0] AXI_01_WSTRB,
  input AXI_01_WVALID,
  input AXI_02_ACLK,
  input [36:0] AXI_02_ARADDR,
  input [1:0] AXI_02_ARBURST,
  input AXI_02_ARESET_N,
  input [5:0] AXI_02_ARID,
  input [3:0] AXI_02_ARLEN,
  input [2:0] AXI_02_ARSIZE,
  input AXI_02_ARVALID,
  input [36:0] AXI_02_AWADDR,
  input [1:0] AXI_02_AWBURST,
  input [5:0] AXI_02_AWID,
  input [3:0] AXI_02_AWLEN,
  input [2:0] AXI_02_AWSIZE,
  input AXI_02_AWVALID,
  input AXI_02_BREADY,
  input AXI_02_DFI_LP_PWR_X_REQ,
  input AXI_02_RREADY,
  input [255:0] AXI_02_WDATA,
  input [31:0] AXI_02_WDATA_PARITY,
  input AXI_02_WLAST,
  input [31:0] AXI_02_WSTRB,
  input AXI_02_WVALID,
  input AXI_03_ACLK,
  input [36:0] AXI_03_ARADDR,
  input [1:0] AXI_03_ARBURST,
  input AXI_03_ARESET_N,
  input [5:0] AXI_03_ARID,
  input [3:0] AXI_03_ARLEN,
  input [2:0] AXI_03_ARSIZE,
  input AXI_03_ARVALID,
  input [36:0] AXI_03_AWADDR,
  input [1:0] AXI_03_AWBURST,
  input [5:0] AXI_03_AWID,
  input [3:0] AXI_03_AWLEN,
  input [2:0] AXI_03_AWSIZE,
  input AXI_03_AWVALID,
  input AXI_03_BREADY,
  input AXI_03_DFI_LP_PWR_X_REQ,
  input AXI_03_RREADY,
  input [255:0] AXI_03_WDATA,
  input [31:0] AXI_03_WDATA_PARITY,
  input AXI_03_WLAST,
  input [31:0] AXI_03_WSTRB,
  input AXI_03_WVALID,
  input AXI_04_ACLK,
  input [36:0] AXI_04_ARADDR,
  input [1:0] AXI_04_ARBURST,
  input AXI_04_ARESET_N,
  input [5:0] AXI_04_ARID,
  input [3:0] AXI_04_ARLEN,
  input [2:0] AXI_04_ARSIZE,
  input AXI_04_ARVALID,
  input [36:0] AXI_04_AWADDR,
  input [1:0] AXI_04_AWBURST,
  input [5:0] AXI_04_AWID,
  input [3:0] AXI_04_AWLEN,
  input [2:0] AXI_04_AWSIZE,
  input AXI_04_AWVALID,
  input AXI_04_BREADY,
  input AXI_04_DFI_LP_PWR_X_REQ,
  input AXI_04_RREADY,
  input [255:0] AXI_04_WDATA,
  input [31:0] AXI_04_WDATA_PARITY,
  input AXI_04_WLAST,
  input [31:0] AXI_04_WSTRB,
  input AXI_04_WVALID,
  input AXI_05_ACLK,
  input [36:0] AXI_05_ARADDR,
  input [1:0] AXI_05_ARBURST,
  input AXI_05_ARESET_N,
  input [5:0] AXI_05_ARID,
  input [3:0] AXI_05_ARLEN,
  input [2:0] AXI_05_ARSIZE,
  input AXI_05_ARVALID,
  input [36:0] AXI_05_AWADDR,
  input [1:0] AXI_05_AWBURST,
  input [5:0] AXI_05_AWID,
  input [3:0] AXI_05_AWLEN,
  input [2:0] AXI_05_AWSIZE,
  input AXI_05_AWVALID,
  input AXI_05_BREADY,
  input AXI_05_DFI_LP_PWR_X_REQ,
  input AXI_05_RREADY,
  input [255:0] AXI_05_WDATA,
  input [31:0] AXI_05_WDATA_PARITY,
  input AXI_05_WLAST,
  input [31:0] AXI_05_WSTRB,
  input AXI_05_WVALID,
  input AXI_06_ACLK,
  input [36:0] AXI_06_ARADDR,
  input [1:0] AXI_06_ARBURST,
  input AXI_06_ARESET_N,
  input [5:0] AXI_06_ARID,
  input [3:0] AXI_06_ARLEN,
  input [2:0] AXI_06_ARSIZE,
  input AXI_06_ARVALID,
  input [36:0] AXI_06_AWADDR,
  input [1:0] AXI_06_AWBURST,
  input [5:0] AXI_06_AWID,
  input [3:0] AXI_06_AWLEN,
  input [2:0] AXI_06_AWSIZE,
  input AXI_06_AWVALID,
  input AXI_06_BREADY,
  input AXI_06_DFI_LP_PWR_X_REQ,
  input AXI_06_RREADY,
  input [255:0] AXI_06_WDATA,
  input [31:0] AXI_06_WDATA_PARITY,
  input AXI_06_WLAST,
  input [31:0] AXI_06_WSTRB,
  input AXI_06_WVALID,
  input AXI_07_ACLK,
  input [36:0] AXI_07_ARADDR,
  input [1:0] AXI_07_ARBURST,
  input AXI_07_ARESET_N,
  input [5:0] AXI_07_ARID,
  input [3:0] AXI_07_ARLEN,
  input [2:0] AXI_07_ARSIZE,
  input AXI_07_ARVALID,
  input [36:0] AXI_07_AWADDR,
  input [1:0] AXI_07_AWBURST,
  input [5:0] AXI_07_AWID,
  input [3:0] AXI_07_AWLEN,
  input [2:0] AXI_07_AWSIZE,
  input AXI_07_AWVALID,
  input AXI_07_BREADY,
  input AXI_07_DFI_LP_PWR_X_REQ,
  input AXI_07_RREADY,
  input [255:0] AXI_07_WDATA,
  input [31:0] AXI_07_WDATA_PARITY,
  input AXI_07_WLAST,
  input [31:0] AXI_07_WSTRB,
  input AXI_07_WVALID,
  input AXI_08_ACLK,
  input [36:0] AXI_08_ARADDR,
  input [1:0] AXI_08_ARBURST,
  input AXI_08_ARESET_N,
  input [5:0] AXI_08_ARID,
  input [3:0] AXI_08_ARLEN,
  input [2:0] AXI_08_ARSIZE,
  input AXI_08_ARVALID,
  input [36:0] AXI_08_AWADDR,
  input [1:0] AXI_08_AWBURST,
  input [5:0] AXI_08_AWID,
  input [3:0] AXI_08_AWLEN,
  input [2:0] AXI_08_AWSIZE,
  input AXI_08_AWVALID,
  input AXI_08_BREADY,
  input AXI_08_DFI_LP_PWR_X_REQ,
  input AXI_08_RREADY,
  input [255:0] AXI_08_WDATA,
  input [31:0] AXI_08_WDATA_PARITY,
  input AXI_08_WLAST,
  input [31:0] AXI_08_WSTRB,
  input AXI_08_WVALID,
  input AXI_09_ACLK,
  input [36:0] AXI_09_ARADDR,
  input [1:0] AXI_09_ARBURST,
  input AXI_09_ARESET_N,
  input [5:0] AXI_09_ARID,
  input [3:0] AXI_09_ARLEN,
  input [2:0] AXI_09_ARSIZE,
  input AXI_09_ARVALID,
  input [36:0] AXI_09_AWADDR,
  input [1:0] AXI_09_AWBURST,
  input [5:0] AXI_09_AWID,
  input [3:0] AXI_09_AWLEN,
  input [2:0] AXI_09_AWSIZE,
  input AXI_09_AWVALID,
  input AXI_09_BREADY,
  input AXI_09_DFI_LP_PWR_X_REQ,
  input AXI_09_RREADY,
  input [255:0] AXI_09_WDATA,
  input [31:0] AXI_09_WDATA_PARITY,
  input AXI_09_WLAST,
  input [31:0] AXI_09_WSTRB,
  input AXI_09_WVALID,
  input AXI_10_ACLK,
  input [36:0] AXI_10_ARADDR,
  input [1:0] AXI_10_ARBURST,
  input AXI_10_ARESET_N,
  input [5:0] AXI_10_ARID,
  input [3:0] AXI_10_ARLEN,
  input [2:0] AXI_10_ARSIZE,
  input AXI_10_ARVALID,
  input [36:0] AXI_10_AWADDR,
  input [1:0] AXI_10_AWBURST,
  input [5:0] AXI_10_AWID,
  input [3:0] AXI_10_AWLEN,
  input [2:0] AXI_10_AWSIZE,
  input AXI_10_AWVALID,
  input AXI_10_BREADY,
  input AXI_10_DFI_LP_PWR_X_REQ,
  input AXI_10_RREADY,
  input [255:0] AXI_10_WDATA,
  input [31:0] AXI_10_WDATA_PARITY,
  input AXI_10_WLAST,
  input [31:0] AXI_10_WSTRB,
  input AXI_10_WVALID,
  input AXI_11_ACLK,
  input [36:0] AXI_11_ARADDR,
  input [1:0] AXI_11_ARBURST,
  input AXI_11_ARESET_N,
  input [5:0] AXI_11_ARID,
  input [3:0] AXI_11_ARLEN,
  input [2:0] AXI_11_ARSIZE,
  input AXI_11_ARVALID,
  input [36:0] AXI_11_AWADDR,
  input [1:0] AXI_11_AWBURST,
  input [5:0] AXI_11_AWID,
  input [3:0] AXI_11_AWLEN,
  input [2:0] AXI_11_AWSIZE,
  input AXI_11_AWVALID,
  input AXI_11_BREADY,
  input AXI_11_DFI_LP_PWR_X_REQ,
  input AXI_11_RREADY,
  input [255:0] AXI_11_WDATA,
  input [31:0] AXI_11_WDATA_PARITY,
  input AXI_11_WLAST,
  input [31:0] AXI_11_WSTRB,
  input AXI_11_WVALID,
  input AXI_12_ACLK,
  input [36:0] AXI_12_ARADDR,
  input [1:0] AXI_12_ARBURST,
  input AXI_12_ARESET_N,
  input [5:0] AXI_12_ARID,
  input [3:0] AXI_12_ARLEN,
  input [2:0] AXI_12_ARSIZE,
  input AXI_12_ARVALID,
  input [36:0] AXI_12_AWADDR,
  input [1:0] AXI_12_AWBURST,
  input [5:0] AXI_12_AWID,
  input [3:0] AXI_12_AWLEN,
  input [2:0] AXI_12_AWSIZE,
  input AXI_12_AWVALID,
  input AXI_12_BREADY,
  input AXI_12_DFI_LP_PWR_X_REQ,
  input AXI_12_RREADY,
  input [255:0] AXI_12_WDATA,
  input [31:0] AXI_12_WDATA_PARITY,
  input AXI_12_WLAST,
  input [31:0] AXI_12_WSTRB,
  input AXI_12_WVALID,
  input AXI_13_ACLK,
  input [36:0] AXI_13_ARADDR,
  input [1:0] AXI_13_ARBURST,
  input AXI_13_ARESET_N,
  input [5:0] AXI_13_ARID,
  input [3:0] AXI_13_ARLEN,
  input [2:0] AXI_13_ARSIZE,
  input AXI_13_ARVALID,
  input [36:0] AXI_13_AWADDR,
  input [1:0] AXI_13_AWBURST,
  input [5:0] AXI_13_AWID,
  input [3:0] AXI_13_AWLEN,
  input [2:0] AXI_13_AWSIZE,
  input AXI_13_AWVALID,
  input AXI_13_BREADY,
  input AXI_13_DFI_LP_PWR_X_REQ,
  input AXI_13_RREADY,
  input [255:0] AXI_13_WDATA,
  input [31:0] AXI_13_WDATA_PARITY,
  input AXI_13_WLAST,
  input [31:0] AXI_13_WSTRB,
  input AXI_13_WVALID,
  input AXI_14_ACLK,
  input [36:0] AXI_14_ARADDR,
  input [1:0] AXI_14_ARBURST,
  input AXI_14_ARESET_N,
  input [5:0] AXI_14_ARID,
  input [3:0] AXI_14_ARLEN,
  input [2:0] AXI_14_ARSIZE,
  input AXI_14_ARVALID,
  input [36:0] AXI_14_AWADDR,
  input [1:0] AXI_14_AWBURST,
  input [5:0] AXI_14_AWID,
  input [3:0] AXI_14_AWLEN,
  input [2:0] AXI_14_AWSIZE,
  input AXI_14_AWVALID,
  input AXI_14_BREADY,
  input AXI_14_DFI_LP_PWR_X_REQ,
  input AXI_14_RREADY,
  input [255:0] AXI_14_WDATA,
  input [31:0] AXI_14_WDATA_PARITY,
  input AXI_14_WLAST,
  input [31:0] AXI_14_WSTRB,
  input AXI_14_WVALID,
  input AXI_15_ACLK,
  input [36:0] AXI_15_ARADDR,
  input [1:0] AXI_15_ARBURST,
  input AXI_15_ARESET_N,
  input [5:0] AXI_15_ARID,
  input [3:0] AXI_15_ARLEN,
  input [2:0] AXI_15_ARSIZE,
  input AXI_15_ARVALID,
  input [36:0] AXI_15_AWADDR,
  input [1:0] AXI_15_AWBURST,
  input [5:0] AXI_15_AWID,
  input [3:0] AXI_15_AWLEN,
  input [2:0] AXI_15_AWSIZE,
  input AXI_15_AWVALID,
  input AXI_15_BREADY,
  input AXI_15_DFI_LP_PWR_X_REQ,
  input AXI_15_RREADY,
  input [255:0] AXI_15_WDATA,
  input [31:0] AXI_15_WDATA_PARITY,
  input AXI_15_WLAST,
  input [31:0] AXI_15_WSTRB,
  input AXI_15_WVALID,
  input AXI_16_ACLK,
  input [36:0] AXI_16_ARADDR,
  input [1:0] AXI_16_ARBURST,
  input AXI_16_ARESET_N,
  input [5:0] AXI_16_ARID,
  input [3:0] AXI_16_ARLEN,
  input [2:0] AXI_16_ARSIZE,
  input AXI_16_ARVALID,
  input [36:0] AXI_16_AWADDR,
  input [1:0] AXI_16_AWBURST,
  input [5:0] AXI_16_AWID,
  input [3:0] AXI_16_AWLEN,
  input [2:0] AXI_16_AWSIZE,
  input AXI_16_AWVALID,
  input AXI_16_BREADY,
  input AXI_16_DFI_LP_PWR_X_REQ,
  input AXI_16_RREADY,
  input [255:0] AXI_16_WDATA,
  input [31:0] AXI_16_WDATA_PARITY,
  input AXI_16_WLAST,
  input [31:0] AXI_16_WSTRB,
  input AXI_16_WVALID,
  input AXI_17_ACLK,
  input [36:0] AXI_17_ARADDR,
  input [1:0] AXI_17_ARBURST,
  input AXI_17_ARESET_N,
  input [5:0] AXI_17_ARID,
  input [3:0] AXI_17_ARLEN,
  input [2:0] AXI_17_ARSIZE,
  input AXI_17_ARVALID,
  input [36:0] AXI_17_AWADDR,
  input [1:0] AXI_17_AWBURST,
  input [5:0] AXI_17_AWID,
  input [3:0] AXI_17_AWLEN,
  input [2:0] AXI_17_AWSIZE,
  input AXI_17_AWVALID,
  input AXI_17_BREADY,
  input AXI_17_DFI_LP_PWR_X_REQ,
  input AXI_17_RREADY,
  input [255:0] AXI_17_WDATA,
  input [31:0] AXI_17_WDATA_PARITY,
  input AXI_17_WLAST,
  input [31:0] AXI_17_WSTRB,
  input AXI_17_WVALID,
  input AXI_18_ACLK,
  input [36:0] AXI_18_ARADDR,
  input [1:0] AXI_18_ARBURST,
  input AXI_18_ARESET_N,
  input [5:0] AXI_18_ARID,
  input [3:0] AXI_18_ARLEN,
  input [2:0] AXI_18_ARSIZE,
  input AXI_18_ARVALID,
  input [36:0] AXI_18_AWADDR,
  input [1:0] AXI_18_AWBURST,
  input [5:0] AXI_18_AWID,
  input [3:0] AXI_18_AWLEN,
  input [2:0] AXI_18_AWSIZE,
  input AXI_18_AWVALID,
  input AXI_18_BREADY,
  input AXI_18_DFI_LP_PWR_X_REQ,
  input AXI_18_RREADY,
  input [255:0] AXI_18_WDATA,
  input [31:0] AXI_18_WDATA_PARITY,
  input AXI_18_WLAST,
  input [31:0] AXI_18_WSTRB,
  input AXI_18_WVALID,
  input AXI_19_ACLK,
  input [36:0] AXI_19_ARADDR,
  input [1:0] AXI_19_ARBURST,
  input AXI_19_ARESET_N,
  input [5:0] AXI_19_ARID,
  input [3:0] AXI_19_ARLEN,
  input [2:0] AXI_19_ARSIZE,
  input AXI_19_ARVALID,
  input [36:0] AXI_19_AWADDR,
  input [1:0] AXI_19_AWBURST,
  input [5:0] AXI_19_AWID,
  input [3:0] AXI_19_AWLEN,
  input [2:0] AXI_19_AWSIZE,
  input AXI_19_AWVALID,
  input AXI_19_BREADY,
  input AXI_19_DFI_LP_PWR_X_REQ,
  input AXI_19_RREADY,
  input [255:0] AXI_19_WDATA,
  input [31:0] AXI_19_WDATA_PARITY,
  input AXI_19_WLAST,
  input [31:0] AXI_19_WSTRB,
  input AXI_19_WVALID,
  input AXI_20_ACLK,
  input [36:0] AXI_20_ARADDR,
  input [1:0] AXI_20_ARBURST,
  input AXI_20_ARESET_N,
  input [5:0] AXI_20_ARID,
  input [3:0] AXI_20_ARLEN,
  input [2:0] AXI_20_ARSIZE,
  input AXI_20_ARVALID,
  input [36:0] AXI_20_AWADDR,
  input [1:0] AXI_20_AWBURST,
  input [5:0] AXI_20_AWID,
  input [3:0] AXI_20_AWLEN,
  input [2:0] AXI_20_AWSIZE,
  input AXI_20_AWVALID,
  input AXI_20_BREADY,
  input AXI_20_DFI_LP_PWR_X_REQ,
  input AXI_20_RREADY,
  input [255:0] AXI_20_WDATA,
  input [31:0] AXI_20_WDATA_PARITY,
  input AXI_20_WLAST,
  input [31:0] AXI_20_WSTRB,
  input AXI_20_WVALID,
  input AXI_21_ACLK,
  input [36:0] AXI_21_ARADDR,
  input [1:0] AXI_21_ARBURST,
  input AXI_21_ARESET_N,
  input [5:0] AXI_21_ARID,
  input [3:0] AXI_21_ARLEN,
  input [2:0] AXI_21_ARSIZE,
  input AXI_21_ARVALID,
  input [36:0] AXI_21_AWADDR,
  input [1:0] AXI_21_AWBURST,
  input [5:0] AXI_21_AWID,
  input [3:0] AXI_21_AWLEN,
  input [2:0] AXI_21_AWSIZE,
  input AXI_21_AWVALID,
  input AXI_21_BREADY,
  input AXI_21_DFI_LP_PWR_X_REQ,
  input AXI_21_RREADY,
  input [255:0] AXI_21_WDATA,
  input [31:0] AXI_21_WDATA_PARITY,
  input AXI_21_WLAST,
  input [31:0] AXI_21_WSTRB,
  input AXI_21_WVALID,
  input AXI_22_ACLK,
  input [36:0] AXI_22_ARADDR,
  input [1:0] AXI_22_ARBURST,
  input AXI_22_ARESET_N,
  input [5:0] AXI_22_ARID,
  input [3:0] AXI_22_ARLEN,
  input [2:0] AXI_22_ARSIZE,
  input AXI_22_ARVALID,
  input [36:0] AXI_22_AWADDR,
  input [1:0] AXI_22_AWBURST,
  input [5:0] AXI_22_AWID,
  input [3:0] AXI_22_AWLEN,
  input [2:0] AXI_22_AWSIZE,
  input AXI_22_AWVALID,
  input AXI_22_BREADY,
  input AXI_22_DFI_LP_PWR_X_REQ,
  input AXI_22_RREADY,
  input [255:0] AXI_22_WDATA,
  input [31:0] AXI_22_WDATA_PARITY,
  input AXI_22_WLAST,
  input [31:0] AXI_22_WSTRB,
  input AXI_22_WVALID,
  input AXI_23_ACLK,
  input [36:0] AXI_23_ARADDR,
  input [1:0] AXI_23_ARBURST,
  input AXI_23_ARESET_N,
  input [5:0] AXI_23_ARID,
  input [3:0] AXI_23_ARLEN,
  input [2:0] AXI_23_ARSIZE,
  input AXI_23_ARVALID,
  input [36:0] AXI_23_AWADDR,
  input [1:0] AXI_23_AWBURST,
  input [5:0] AXI_23_AWID,
  input [3:0] AXI_23_AWLEN,
  input [2:0] AXI_23_AWSIZE,
  input AXI_23_AWVALID,
  input AXI_23_BREADY,
  input AXI_23_DFI_LP_PWR_X_REQ,
  input AXI_23_RREADY,
  input [255:0] AXI_23_WDATA,
  input [31:0] AXI_23_WDATA_PARITY,
  input AXI_23_WLAST,
  input [31:0] AXI_23_WSTRB,
  input AXI_23_WVALID,
  input AXI_24_ACLK,
  input [36:0] AXI_24_ARADDR,
  input [1:0] AXI_24_ARBURST,
  input AXI_24_ARESET_N,
  input [5:0] AXI_24_ARID,
  input [3:0] AXI_24_ARLEN,
  input [2:0] AXI_24_ARSIZE,
  input AXI_24_ARVALID,
  input [36:0] AXI_24_AWADDR,
  input [1:0] AXI_24_AWBURST,
  input [5:0] AXI_24_AWID,
  input [3:0] AXI_24_AWLEN,
  input [2:0] AXI_24_AWSIZE,
  input AXI_24_AWVALID,
  input AXI_24_BREADY,
  input AXI_24_DFI_LP_PWR_X_REQ,
  input AXI_24_RREADY,
  input [255:0] AXI_24_WDATA,
  input [31:0] AXI_24_WDATA_PARITY,
  input AXI_24_WLAST,
  input [31:0] AXI_24_WSTRB,
  input AXI_24_WVALID,
  input AXI_25_ACLK,
  input [36:0] AXI_25_ARADDR,
  input [1:0] AXI_25_ARBURST,
  input AXI_25_ARESET_N,
  input [5:0] AXI_25_ARID,
  input [3:0] AXI_25_ARLEN,
  input [2:0] AXI_25_ARSIZE,
  input AXI_25_ARVALID,
  input [36:0] AXI_25_AWADDR,
  input [1:0] AXI_25_AWBURST,
  input [5:0] AXI_25_AWID,
  input [3:0] AXI_25_AWLEN,
  input [2:0] AXI_25_AWSIZE,
  input AXI_25_AWVALID,
  input AXI_25_BREADY,
  input AXI_25_DFI_LP_PWR_X_REQ,
  input AXI_25_RREADY,
  input [255:0] AXI_25_WDATA,
  input [31:0] AXI_25_WDATA_PARITY,
  input AXI_25_WLAST,
  input [31:0] AXI_25_WSTRB,
  input AXI_25_WVALID,
  input AXI_26_ACLK,
  input [36:0] AXI_26_ARADDR,
  input [1:0] AXI_26_ARBURST,
  input AXI_26_ARESET_N,
  input [5:0] AXI_26_ARID,
  input [3:0] AXI_26_ARLEN,
  input [2:0] AXI_26_ARSIZE,
  input AXI_26_ARVALID,
  input [36:0] AXI_26_AWADDR,
  input [1:0] AXI_26_AWBURST,
  input [5:0] AXI_26_AWID,
  input [3:0] AXI_26_AWLEN,
  input [2:0] AXI_26_AWSIZE,
  input AXI_26_AWVALID,
  input AXI_26_BREADY,
  input AXI_26_DFI_LP_PWR_X_REQ,
  input AXI_26_RREADY,
  input [255:0] AXI_26_WDATA,
  input [31:0] AXI_26_WDATA_PARITY,
  input AXI_26_WLAST,
  input [31:0] AXI_26_WSTRB,
  input AXI_26_WVALID,
  input AXI_27_ACLK,
  input [36:0] AXI_27_ARADDR,
  input [1:0] AXI_27_ARBURST,
  input AXI_27_ARESET_N,
  input [5:0] AXI_27_ARID,
  input [3:0] AXI_27_ARLEN,
  input [2:0] AXI_27_ARSIZE,
  input AXI_27_ARVALID,
  input [36:0] AXI_27_AWADDR,
  input [1:0] AXI_27_AWBURST,
  input [5:0] AXI_27_AWID,
  input [3:0] AXI_27_AWLEN,
  input [2:0] AXI_27_AWSIZE,
  input AXI_27_AWVALID,
  input AXI_27_BREADY,
  input AXI_27_DFI_LP_PWR_X_REQ,
  input AXI_27_RREADY,
  input [255:0] AXI_27_WDATA,
  input [31:0] AXI_27_WDATA_PARITY,
  input AXI_27_WLAST,
  input [31:0] AXI_27_WSTRB,
  input AXI_27_WVALID,
  input AXI_28_ACLK,
  input [36:0] AXI_28_ARADDR,
  input [1:0] AXI_28_ARBURST,
  input AXI_28_ARESET_N,
  input [5:0] AXI_28_ARID,
  input [3:0] AXI_28_ARLEN,
  input [2:0] AXI_28_ARSIZE,
  input AXI_28_ARVALID,
  input [36:0] AXI_28_AWADDR,
  input [1:0] AXI_28_AWBURST,
  input [5:0] AXI_28_AWID,
  input [3:0] AXI_28_AWLEN,
  input [2:0] AXI_28_AWSIZE,
  input AXI_28_AWVALID,
  input AXI_28_BREADY,
  input AXI_28_DFI_LP_PWR_X_REQ,
  input AXI_28_RREADY,
  input [255:0] AXI_28_WDATA,
  input [31:0] AXI_28_WDATA_PARITY,
  input AXI_28_WLAST,
  input [31:0] AXI_28_WSTRB,
  input AXI_28_WVALID,
  input AXI_29_ACLK,
  input [36:0] AXI_29_ARADDR,
  input [1:0] AXI_29_ARBURST,
  input AXI_29_ARESET_N,
  input [5:0] AXI_29_ARID,
  input [3:0] AXI_29_ARLEN,
  input [2:0] AXI_29_ARSIZE,
  input AXI_29_ARVALID,
  input [36:0] AXI_29_AWADDR,
  input [1:0] AXI_29_AWBURST,
  input [5:0] AXI_29_AWID,
  input [3:0] AXI_29_AWLEN,
  input [2:0] AXI_29_AWSIZE,
  input AXI_29_AWVALID,
  input AXI_29_BREADY,
  input AXI_29_DFI_LP_PWR_X_REQ,
  input AXI_29_RREADY,
  input [255:0] AXI_29_WDATA,
  input [31:0] AXI_29_WDATA_PARITY,
  input AXI_29_WLAST,
  input [31:0] AXI_29_WSTRB,
  input AXI_29_WVALID,
  input AXI_30_ACLK,
  input [36:0] AXI_30_ARADDR,
  input [1:0] AXI_30_ARBURST,
  input AXI_30_ARESET_N,
  input [5:0] AXI_30_ARID,
  input [3:0] AXI_30_ARLEN,
  input [2:0] AXI_30_ARSIZE,
  input AXI_30_ARVALID,
  input [36:0] AXI_30_AWADDR,
  input [1:0] AXI_30_AWBURST,
  input [5:0] AXI_30_AWID,
  input [3:0] AXI_30_AWLEN,
  input [2:0] AXI_30_AWSIZE,
  input AXI_30_AWVALID,
  input AXI_30_BREADY,
  input AXI_30_DFI_LP_PWR_X_REQ,
  input AXI_30_RREADY,
  input [255:0] AXI_30_WDATA,
  input [31:0] AXI_30_WDATA_PARITY,
  input AXI_30_WLAST,
  input [31:0] AXI_30_WSTRB,
  input AXI_30_WVALID,
  input AXI_31_ACLK,
  input [36:0] AXI_31_ARADDR,
  input [1:0] AXI_31_ARBURST,
  input AXI_31_ARESET_N,
  input [5:0] AXI_31_ARID,
  input [3:0] AXI_31_ARLEN,
  input [2:0] AXI_31_ARSIZE,
  input AXI_31_ARVALID,
  input [36:0] AXI_31_AWADDR,
  input [1:0] AXI_31_AWBURST,
  input [5:0] AXI_31_AWID,
  input [3:0] AXI_31_AWLEN,
  input [2:0] AXI_31_AWSIZE,
  input AXI_31_AWVALID,
  input AXI_31_BREADY,
  input AXI_31_DFI_LP_PWR_X_REQ,
  input AXI_31_RREADY,
  input [255:0] AXI_31_WDATA,
  input [31:0] AXI_31_WDATA_PARITY,
  input AXI_31_WLAST,
  input [31:0] AXI_31_WSTRB,
  input AXI_31_WVALID,
  input BSCAN_DRCK_0,
  input BSCAN_DRCK_1,
  input BSCAN_TCK_0,
  input BSCAN_TCK_1,
  input HBM_REF_CLK_0,
  input HBM_REF_CLK_1,
  input MBIST_EN_00,
  input MBIST_EN_01,
  input MBIST_EN_02,
  input MBIST_EN_03,
  input MBIST_EN_04,
  input MBIST_EN_05,
  input MBIST_EN_06,
  input MBIST_EN_07,
  input MBIST_EN_08,
  input MBIST_EN_09,
  input MBIST_EN_10,
  input MBIST_EN_11,
  input MBIST_EN_12,
  input MBIST_EN_13,
  input MBIST_EN_14,
  input MBIST_EN_15
);

// define constants
  localparam MODULE_NAME = "HBM_TWO_STACK_INTF";
  
// Parameter encodings and registers
  localparam PHY_PCLK_INVERT_01_FALSE = 0;
  localparam PHY_PCLK_INVERT_01_TRUE = 1;
  localparam PHY_PCLK_INVERT_02_FALSE = 0;
  localparam PHY_PCLK_INVERT_02_TRUE = 1;

  reg trig_attr;
// include dynamic registers - XILINX test only
`ifdef XIL_DR
  `include "HBM_TWO_STACK_INTF_dr.v"
`else
  localparam [40:1] CLK_SEL_00_REG = CLK_SEL_00;
  localparam [40:1] CLK_SEL_01_REG = CLK_SEL_01;
  localparam [40:1] CLK_SEL_02_REG = CLK_SEL_02;
  localparam [40:1] CLK_SEL_03_REG = CLK_SEL_03;
  localparam [40:1] CLK_SEL_04_REG = CLK_SEL_04;
  localparam [40:1] CLK_SEL_05_REG = CLK_SEL_05;
  localparam [40:1] CLK_SEL_06_REG = CLK_SEL_06;
  localparam [40:1] CLK_SEL_07_REG = CLK_SEL_07;
  localparam [40:1] CLK_SEL_08_REG = CLK_SEL_08;
  localparam [40:1] CLK_SEL_09_REG = CLK_SEL_09;
  localparam [40:1] CLK_SEL_10_REG = CLK_SEL_10;
  localparam [40:1] CLK_SEL_11_REG = CLK_SEL_11;
  localparam [40:1] CLK_SEL_12_REG = CLK_SEL_12;
  localparam [40:1] CLK_SEL_13_REG = CLK_SEL_13;
  localparam [40:1] CLK_SEL_14_REG = CLK_SEL_14;
  localparam [40:1] CLK_SEL_15_REG = CLK_SEL_15;
  localparam [40:1] CLK_SEL_16_REG = CLK_SEL_16;
  localparam [40:1] CLK_SEL_17_REG = CLK_SEL_17;
  localparam [40:1] CLK_SEL_18_REG = CLK_SEL_18;
  localparam [40:1] CLK_SEL_19_REG = CLK_SEL_19;
  localparam [40:1] CLK_SEL_20_REG = CLK_SEL_20;
  localparam [40:1] CLK_SEL_21_REG = CLK_SEL_21;
  localparam [40:1] CLK_SEL_22_REG = CLK_SEL_22;
  localparam [40:1] CLK_SEL_23_REG = CLK_SEL_23;
  localparam [40:1] CLK_SEL_24_REG = CLK_SEL_24;
  localparam [40:1] CLK_SEL_25_REG = CLK_SEL_25;
  localparam [40:1] CLK_SEL_26_REG = CLK_SEL_26;
  localparam [40:1] CLK_SEL_27_REG = CLK_SEL_27;
  localparam [40:1] CLK_SEL_28_REG = CLK_SEL_28;
  localparam [40:1] CLK_SEL_29_REG = CLK_SEL_29;
  localparam [40:1] CLK_SEL_30_REG = CLK_SEL_30;
  localparam [40:1] CLK_SEL_31_REG = CLK_SEL_31;
  localparam [10:0] DATARATE_00_REG = DATARATE_00;
  localparam [10:0] DATARATE_01_REG = DATARATE_01;
  localparam [10:0] DATARATE_02_REG = DATARATE_02;
  localparam [10:0] DATARATE_03_REG = DATARATE_03;
  localparam [10:0] DATARATE_04_REG = DATARATE_04;
  localparam [10:0] DATARATE_05_REG = DATARATE_05;
  localparam [10:0] DATARATE_06_REG = DATARATE_06;
  localparam [10:0] DATARATE_07_REG = DATARATE_07;
  localparam [10:0] DATARATE_08_REG = DATARATE_08;
  localparam [10:0] DATARATE_09_REG = DATARATE_09;
  localparam [10:0] DATARATE_10_REG = DATARATE_10;
  localparam [10:0] DATARATE_11_REG = DATARATE_11;
  localparam [10:0] DATARATE_12_REG = DATARATE_12;
  localparam [10:0] DATARATE_13_REG = DATARATE_13;
  localparam [10:0] DATARATE_14_REG = DATARATE_14;
  localparam [10:0] DATARATE_15_REG = DATARATE_15;
  localparam [40:1] DA_LOCKOUT_0_REG = DA_LOCKOUT_0;
  localparam [40:1] DA_LOCKOUT_1_REG = DA_LOCKOUT_1;
  localparam [0:0] IS_APB_0_PCLK_INVERTED_REG = IS_APB_0_PCLK_INVERTED;
  localparam [0:0] IS_APB_0_PRESET_N_INVERTED_REG = IS_APB_0_PRESET_N_INVERTED;
  localparam [0:0] IS_APB_1_PCLK_INVERTED_REG = IS_APB_1_PCLK_INVERTED;
  localparam [0:0] IS_APB_1_PRESET_N_INVERTED_REG = IS_APB_1_PRESET_N_INVERTED;
  localparam [0:0] IS_AXI_00_ACLK_INVERTED_REG = IS_AXI_00_ACLK_INVERTED;
  localparam [0:0] IS_AXI_00_ARESET_N_INVERTED_REG = IS_AXI_00_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_01_ACLK_INVERTED_REG = IS_AXI_01_ACLK_INVERTED;
  localparam [0:0] IS_AXI_01_ARESET_N_INVERTED_REG = IS_AXI_01_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_02_ACLK_INVERTED_REG = IS_AXI_02_ACLK_INVERTED;
  localparam [0:0] IS_AXI_02_ARESET_N_INVERTED_REG = IS_AXI_02_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_03_ACLK_INVERTED_REG = IS_AXI_03_ACLK_INVERTED;
  localparam [0:0] IS_AXI_03_ARESET_N_INVERTED_REG = IS_AXI_03_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_04_ACLK_INVERTED_REG = IS_AXI_04_ACLK_INVERTED;
  localparam [0:0] IS_AXI_04_ARESET_N_INVERTED_REG = IS_AXI_04_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_05_ACLK_INVERTED_REG = IS_AXI_05_ACLK_INVERTED;
  localparam [0:0] IS_AXI_05_ARESET_N_INVERTED_REG = IS_AXI_05_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_06_ACLK_INVERTED_REG = IS_AXI_06_ACLK_INVERTED;
  localparam [0:0] IS_AXI_06_ARESET_N_INVERTED_REG = IS_AXI_06_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_07_ACLK_INVERTED_REG = IS_AXI_07_ACLK_INVERTED;
  localparam [0:0] IS_AXI_07_ARESET_N_INVERTED_REG = IS_AXI_07_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_08_ACLK_INVERTED_REG = IS_AXI_08_ACLK_INVERTED;
  localparam [0:0] IS_AXI_08_ARESET_N_INVERTED_REG = IS_AXI_08_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_09_ACLK_INVERTED_REG = IS_AXI_09_ACLK_INVERTED;
  localparam [0:0] IS_AXI_09_ARESET_N_INVERTED_REG = IS_AXI_09_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_10_ACLK_INVERTED_REG = IS_AXI_10_ACLK_INVERTED;
  localparam [0:0] IS_AXI_10_ARESET_N_INVERTED_REG = IS_AXI_10_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_11_ACLK_INVERTED_REG = IS_AXI_11_ACLK_INVERTED;
  localparam [0:0] IS_AXI_11_ARESET_N_INVERTED_REG = IS_AXI_11_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_12_ACLK_INVERTED_REG = IS_AXI_12_ACLK_INVERTED;
  localparam [0:0] IS_AXI_12_ARESET_N_INVERTED_REG = IS_AXI_12_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_13_ACLK_INVERTED_REG = IS_AXI_13_ACLK_INVERTED;
  localparam [0:0] IS_AXI_13_ARESET_N_INVERTED_REG = IS_AXI_13_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_14_ACLK_INVERTED_REG = IS_AXI_14_ACLK_INVERTED;
  localparam [0:0] IS_AXI_14_ARESET_N_INVERTED_REG = IS_AXI_14_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_15_ACLK_INVERTED_REG = IS_AXI_15_ACLK_INVERTED;
  localparam [0:0] IS_AXI_15_ARESET_N_INVERTED_REG = IS_AXI_15_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_16_ACLK_INVERTED_REG = IS_AXI_16_ACLK_INVERTED;
  localparam [0:0] IS_AXI_16_ARESET_N_INVERTED_REG = IS_AXI_16_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_17_ACLK_INVERTED_REG = IS_AXI_17_ACLK_INVERTED;
  localparam [0:0] IS_AXI_17_ARESET_N_INVERTED_REG = IS_AXI_17_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_18_ACLK_INVERTED_REG = IS_AXI_18_ACLK_INVERTED;
  localparam [0:0] IS_AXI_18_ARESET_N_INVERTED_REG = IS_AXI_18_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_19_ACLK_INVERTED_REG = IS_AXI_19_ACLK_INVERTED;
  localparam [0:0] IS_AXI_19_ARESET_N_INVERTED_REG = IS_AXI_19_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_20_ACLK_INVERTED_REG = IS_AXI_20_ACLK_INVERTED;
  localparam [0:0] IS_AXI_20_ARESET_N_INVERTED_REG = IS_AXI_20_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_21_ACLK_INVERTED_REG = IS_AXI_21_ACLK_INVERTED;
  localparam [0:0] IS_AXI_21_ARESET_N_INVERTED_REG = IS_AXI_21_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_22_ACLK_INVERTED_REG = IS_AXI_22_ACLK_INVERTED;
  localparam [0:0] IS_AXI_22_ARESET_N_INVERTED_REG = IS_AXI_22_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_23_ACLK_INVERTED_REG = IS_AXI_23_ACLK_INVERTED;
  localparam [0:0] IS_AXI_23_ARESET_N_INVERTED_REG = IS_AXI_23_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_24_ACLK_INVERTED_REG = IS_AXI_24_ACLK_INVERTED;
  localparam [0:0] IS_AXI_24_ARESET_N_INVERTED_REG = IS_AXI_24_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_25_ACLK_INVERTED_REG = IS_AXI_25_ACLK_INVERTED;
  localparam [0:0] IS_AXI_25_ARESET_N_INVERTED_REG = IS_AXI_25_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_26_ACLK_INVERTED_REG = IS_AXI_26_ACLK_INVERTED;
  localparam [0:0] IS_AXI_26_ARESET_N_INVERTED_REG = IS_AXI_26_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_27_ACLK_INVERTED_REG = IS_AXI_27_ACLK_INVERTED;
  localparam [0:0] IS_AXI_27_ARESET_N_INVERTED_REG = IS_AXI_27_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_28_ACLK_INVERTED_REG = IS_AXI_28_ACLK_INVERTED;
  localparam [0:0] IS_AXI_28_ARESET_N_INVERTED_REG = IS_AXI_28_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_29_ACLK_INVERTED_REG = IS_AXI_29_ACLK_INVERTED;
  localparam [0:0] IS_AXI_29_ARESET_N_INVERTED_REG = IS_AXI_29_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_30_ACLK_INVERTED_REG = IS_AXI_30_ACLK_INVERTED;
  localparam [0:0] IS_AXI_30_ARESET_N_INVERTED_REG = IS_AXI_30_ARESET_N_INVERTED;
  localparam [0:0] IS_AXI_31_ACLK_INVERTED_REG = IS_AXI_31_ACLK_INVERTED;
  localparam [0:0] IS_AXI_31_ARESET_N_INVERTED_REG = IS_AXI_31_ARESET_N_INVERTED;
  localparam [40:1] MC_ENABLE_00_REG = MC_ENABLE_00;
  localparam [40:1] MC_ENABLE_01_REG = MC_ENABLE_01;
  localparam [40:1] MC_ENABLE_02_REG = MC_ENABLE_02;
  localparam [40:1] MC_ENABLE_03_REG = MC_ENABLE_03;
  localparam [40:1] MC_ENABLE_04_REG = MC_ENABLE_04;
  localparam [40:1] MC_ENABLE_05_REG = MC_ENABLE_05;
  localparam [40:1] MC_ENABLE_06_REG = MC_ENABLE_06;
  localparam [40:1] MC_ENABLE_07_REG = MC_ENABLE_07;
  localparam [40:1] MC_ENABLE_08_REG = MC_ENABLE_08;
  localparam [40:1] MC_ENABLE_09_REG = MC_ENABLE_09;
  localparam [40:1] MC_ENABLE_10_REG = MC_ENABLE_10;
  localparam [40:1] MC_ENABLE_11_REG = MC_ENABLE_11;
  localparam [40:1] MC_ENABLE_12_REG = MC_ENABLE_12;
  localparam [40:1] MC_ENABLE_13_REG = MC_ENABLE_13;
  localparam [40:1] MC_ENABLE_14_REG = MC_ENABLE_14;
  localparam [40:1] MC_ENABLE_15_REG = MC_ENABLE_15;
  localparam [40:1] MC_ENABLE_APB_00_REG = MC_ENABLE_APB_00;
  localparam [40:1] MC_ENABLE_APB_01_REG = MC_ENABLE_APB_01;
  localparam [6:0] PAGEHIT_PERCENT_00_REG = PAGEHIT_PERCENT_00;
  localparam [6:0] PAGEHIT_PERCENT_01_REG = PAGEHIT_PERCENT_01;
  localparam [40:1] PHY_ENABLE_00_REG = PHY_ENABLE_00;
  localparam [40:1] PHY_ENABLE_01_REG = PHY_ENABLE_01;
  localparam [40:1] PHY_ENABLE_02_REG = PHY_ENABLE_02;
  localparam [40:1] PHY_ENABLE_03_REG = PHY_ENABLE_03;
  localparam [40:1] PHY_ENABLE_04_REG = PHY_ENABLE_04;
  localparam [40:1] PHY_ENABLE_05_REG = PHY_ENABLE_05;
  localparam [40:1] PHY_ENABLE_06_REG = PHY_ENABLE_06;
  localparam [40:1] PHY_ENABLE_07_REG = PHY_ENABLE_07;
  localparam [40:1] PHY_ENABLE_08_REG = PHY_ENABLE_08;
  localparam [40:1] PHY_ENABLE_09_REG = PHY_ENABLE_09;
  localparam [40:1] PHY_ENABLE_10_REG = PHY_ENABLE_10;
  localparam [40:1] PHY_ENABLE_11_REG = PHY_ENABLE_11;
  localparam [40:1] PHY_ENABLE_12_REG = PHY_ENABLE_12;
  localparam [40:1] PHY_ENABLE_13_REG = PHY_ENABLE_13;
  localparam [40:1] PHY_ENABLE_14_REG = PHY_ENABLE_14;
  localparam [40:1] PHY_ENABLE_15_REG = PHY_ENABLE_15;
  localparam [40:1] PHY_ENABLE_16_REG = PHY_ENABLE_16;
  localparam [40:1] PHY_ENABLE_17_REG = PHY_ENABLE_17;
  localparam [40:1] PHY_ENABLE_18_REG = PHY_ENABLE_18;
  localparam [40:1] PHY_ENABLE_19_REG = PHY_ENABLE_19;
  localparam [40:1] PHY_ENABLE_20_REG = PHY_ENABLE_20;
  localparam [40:1] PHY_ENABLE_21_REG = PHY_ENABLE_21;
  localparam [40:1] PHY_ENABLE_22_REG = PHY_ENABLE_22;
  localparam [40:1] PHY_ENABLE_23_REG = PHY_ENABLE_23;
  localparam [40:1] PHY_ENABLE_24_REG = PHY_ENABLE_24;
  localparam [40:1] PHY_ENABLE_25_REG = PHY_ENABLE_25;
  localparam [40:1] PHY_ENABLE_26_REG = PHY_ENABLE_26;
  localparam [40:1] PHY_ENABLE_27_REG = PHY_ENABLE_27;
  localparam [40:1] PHY_ENABLE_28_REG = PHY_ENABLE_28;
  localparam [40:1] PHY_ENABLE_29_REG = PHY_ENABLE_29;
  localparam [40:1] PHY_ENABLE_30_REG = PHY_ENABLE_30;
  localparam [40:1] PHY_ENABLE_31_REG = PHY_ENABLE_31;
  localparam [40:1] PHY_ENABLE_APB_00_REG = PHY_ENABLE_APB_00;
  localparam [40:1] PHY_ENABLE_APB_01_REG = PHY_ENABLE_APB_01;
  localparam [40:1] PHY_PCLK_INVERT_01_REG = PHY_PCLK_INVERT_01;
  localparam [40:1] PHY_PCLK_INVERT_02_REG = PHY_PCLK_INVERT_02;
  localparam [6:0] READ_PERCENT_00_REG = READ_PERCENT_00;
  localparam [6:0] READ_PERCENT_01_REG = READ_PERCENT_01;
  localparam [6:0] READ_PERCENT_02_REG = READ_PERCENT_02;
  localparam [6:0] READ_PERCENT_03_REG = READ_PERCENT_03;
  localparam [6:0] READ_PERCENT_04_REG = READ_PERCENT_04;
  localparam [6:0] READ_PERCENT_05_REG = READ_PERCENT_05;
  localparam [6:0] READ_PERCENT_06_REG = READ_PERCENT_06;
  localparam [6:0] READ_PERCENT_07_REG = READ_PERCENT_07;
  localparam [6:0] READ_PERCENT_08_REG = READ_PERCENT_08;
  localparam [6:0] READ_PERCENT_09_REG = READ_PERCENT_09;
  localparam [6:0] READ_PERCENT_10_REG = READ_PERCENT_10;
  localparam [6:0] READ_PERCENT_11_REG = READ_PERCENT_11;
  localparam [6:0] READ_PERCENT_12_REG = READ_PERCENT_12;
  localparam [6:0] READ_PERCENT_13_REG = READ_PERCENT_13;
  localparam [6:0] READ_PERCENT_14_REG = READ_PERCENT_14;
  localparam [6:0] READ_PERCENT_15_REG = READ_PERCENT_15;
  localparam [6:0] READ_PERCENT_16_REG = READ_PERCENT_16;
  localparam [6:0] READ_PERCENT_17_REG = READ_PERCENT_17;
  localparam [6:0] READ_PERCENT_18_REG = READ_PERCENT_18;
  localparam [6:0] READ_PERCENT_19_REG = READ_PERCENT_19;
  localparam [6:0] READ_PERCENT_20_REG = READ_PERCENT_20;
  localparam [6:0] READ_PERCENT_21_REG = READ_PERCENT_21;
  localparam [6:0] READ_PERCENT_22_REG = READ_PERCENT_22;
  localparam [6:0] READ_PERCENT_23_REG = READ_PERCENT_23;
  localparam [6:0] READ_PERCENT_24_REG = READ_PERCENT_24;
  localparam [6:0] READ_PERCENT_25_REG = READ_PERCENT_25;
  localparam [6:0] READ_PERCENT_26_REG = READ_PERCENT_26;
  localparam [6:0] READ_PERCENT_27_REG = READ_PERCENT_27;
  localparam [6:0] READ_PERCENT_28_REG = READ_PERCENT_28;
  localparam [6:0] READ_PERCENT_29_REG = READ_PERCENT_29;
  localparam [6:0] READ_PERCENT_30_REG = READ_PERCENT_30;
  localparam [6:0] READ_PERCENT_31_REG = READ_PERCENT_31;
  localparam [152:1] SIM_DEVICE_REG = SIM_DEVICE;
  localparam [40:1] SWITCH_ENABLE_00_REG = SWITCH_ENABLE_00;
  localparam [40:1] SWITCH_ENABLE_01_REG = SWITCH_ENABLE_01;
  localparam [6:0] WRITE_PERCENT_00_REG = WRITE_PERCENT_00;
  localparam [6:0] WRITE_PERCENT_01_REG = WRITE_PERCENT_01;
  localparam [6:0] WRITE_PERCENT_02_REG = WRITE_PERCENT_02;
  localparam [6:0] WRITE_PERCENT_03_REG = WRITE_PERCENT_03;
  localparam [6:0] WRITE_PERCENT_04_REG = WRITE_PERCENT_04;
  localparam [6:0] WRITE_PERCENT_05_REG = WRITE_PERCENT_05;
  localparam [6:0] WRITE_PERCENT_06_REG = WRITE_PERCENT_06;
  localparam [6:0] WRITE_PERCENT_07_REG = WRITE_PERCENT_07;
  localparam [6:0] WRITE_PERCENT_08_REG = WRITE_PERCENT_08;
  localparam [6:0] WRITE_PERCENT_09_REG = WRITE_PERCENT_09;
  localparam [6:0] WRITE_PERCENT_10_REG = WRITE_PERCENT_10;
  localparam [6:0] WRITE_PERCENT_11_REG = WRITE_PERCENT_11;
  localparam [6:0] WRITE_PERCENT_12_REG = WRITE_PERCENT_12;
  localparam [6:0] WRITE_PERCENT_13_REG = WRITE_PERCENT_13;
  localparam [6:0] WRITE_PERCENT_14_REG = WRITE_PERCENT_14;
  localparam [6:0] WRITE_PERCENT_15_REG = WRITE_PERCENT_15;
  localparam [6:0] WRITE_PERCENT_16_REG = WRITE_PERCENT_16;
  localparam [6:0] WRITE_PERCENT_17_REG = WRITE_PERCENT_17;
  localparam [6:0] WRITE_PERCENT_18_REG = WRITE_PERCENT_18;
  localparam [6:0] WRITE_PERCENT_19_REG = WRITE_PERCENT_19;
  localparam [6:0] WRITE_PERCENT_20_REG = WRITE_PERCENT_20;
  localparam [6:0] WRITE_PERCENT_21_REG = WRITE_PERCENT_21;
  localparam [6:0] WRITE_PERCENT_22_REG = WRITE_PERCENT_22;
  localparam [6:0] WRITE_PERCENT_23_REG = WRITE_PERCENT_23;
  localparam [6:0] WRITE_PERCENT_24_REG = WRITE_PERCENT_24;
  localparam [6:0] WRITE_PERCENT_25_REG = WRITE_PERCENT_25;
  localparam [6:0] WRITE_PERCENT_26_REG = WRITE_PERCENT_26;
  localparam [6:0] WRITE_PERCENT_27_REG = WRITE_PERCENT_27;
  localparam [6:0] WRITE_PERCENT_28_REG = WRITE_PERCENT_28;
  localparam [6:0] WRITE_PERCENT_29_REG = WRITE_PERCENT_29;
  localparam [6:0] WRITE_PERCENT_30_REG = WRITE_PERCENT_30;
  localparam [6:0] WRITE_PERCENT_31_REG = WRITE_PERCENT_31;
`endif

  localparam [7:0] ANALOG_MUX_SEL_0_REG = 8'h00;
  localparam [7:0] ANALOG_MUX_SEL_1_REG = 8'h00;
  localparam [40:1] APB_BYPASS_EN_0_REG = "FALSE";
  localparam [40:1] APB_BYPASS_EN_1_REG = "FALSE";
  localparam [40:1] AXI_BYPASS_EN_0_REG = "FALSE";
  localparam [40:1] AXI_BYPASS_EN_1_REG = "FALSE";
  localparam [40:1] BLI_TESTMODE_SEL_0_REG = "FALSE";
  localparam [40:1] BLI_TESTMODE_SEL_1_REG = "FALSE";
  localparam [51:0] DBG_BYPASS_VAL_0_REG = 52'hFFFFFFFFFFFFF;
  localparam [51:0] DBG_BYPASS_VAL_1_REG = 52'hFFFFFFFFFFFFF;
  localparam [40:1] DEBUG_MODE_0_REG = "FALSE";
  localparam [40:1] DEBUG_MODE_1_REG = "FALSE";
  localparam [51:0] DFI_BYPASS_VAL_0_REG = 52'h0000000000000;
  localparam [51:0] DFI_BYPASS_VAL_1_REG = 52'h0000000000000;
  localparam [40:1] DLL_TESTMODE_SEL_0_REG = "FALSE";
  localparam [40:1] DLL_TESTMODE_SEL_1_REG = "FALSE";
  localparam [40:1] IO_TESTMODE_SEL_0_REG = "FALSE";
  localparam [40:1] IO_TESTMODE_SEL_1_REG = "FALSE";
  localparam [40:1] MC_CSSD_SEL_0_REG = "FALSE";
  localparam [40:1] MC_CSSD_SEL_1_REG = "FALSE";
  localparam [40:1] MC_CSSD_SEL_10_REG = "FALSE";
  localparam [40:1] MC_CSSD_SEL_11_REG = "FALSE";
  localparam [40:1] MC_CSSD_SEL_12_REG = "FALSE";
  localparam [40:1] MC_CSSD_SEL_13_REG = "FALSE";
  localparam [40:1] MC_CSSD_SEL_14_REG = "FALSE";
  localparam [40:1] MC_CSSD_SEL_15_REG = "FALSE";
  localparam [40:1] MC_CSSD_SEL_2_REG = "FALSE";
  localparam [40:1] MC_CSSD_SEL_3_REG = "FALSE";
  localparam [40:1] MC_CSSD_SEL_4_REG = "FALSE";
  localparam [40:1] MC_CSSD_SEL_5_REG = "FALSE";
  localparam [40:1] MC_CSSD_SEL_6_REG = "FALSE";
  localparam [40:1] MC_CSSD_SEL_7_REG = "FALSE";
  localparam [40:1] MC_CSSD_SEL_8_REG = "FALSE";
  localparam [40:1] MC_CSSD_SEL_9_REG = "FALSE";
  localparam [40:1] MC_TESTMODE_SEL_0_REG = "FALSE";
  localparam [40:1] MC_TESTMODE_SEL_1_REG = "FALSE";
  localparam [40:1] MC_TESTMODE_SEL_10_REG = "FALSE";
  localparam [40:1] MC_TESTMODE_SEL_11_REG = "FALSE";
  localparam [40:1] MC_TESTMODE_SEL_12_REG = "FALSE";
  localparam [40:1] MC_TESTMODE_SEL_13_REG = "FALSE";
  localparam [40:1] MC_TESTMODE_SEL_14_REG = "FALSE";
  localparam [40:1] MC_TESTMODE_SEL_15_REG = "FALSE";
  localparam [40:1] MC_TESTMODE_SEL_2_REG = "FALSE";
  localparam [40:1] MC_TESTMODE_SEL_3_REG = "FALSE";
  localparam [40:1] MC_TESTMODE_SEL_4_REG = "FALSE";
  localparam [40:1] MC_TESTMODE_SEL_5_REG = "FALSE";
  localparam [40:1] MC_TESTMODE_SEL_6_REG = "FALSE";
  localparam [40:1] MC_TESTMODE_SEL_7_REG = "FALSE";
  localparam [40:1] MC_TESTMODE_SEL_8_REG = "FALSE";
  localparam [40:1] MC_TESTMODE_SEL_9_REG = "FALSE";
  localparam [40:1] PHY_CSSD_SEL_0_REG = "FALSE";
  localparam [40:1] PHY_CSSD_SEL_1_REG = "FALSE";
  localparam [40:1] PHY_TESTMODE_SEL_0_REG = "FALSE";
  localparam [40:1] PHY_TESTMODE_SEL_1_REG = "FALSE";
  localparam [40:1] SWITCH_ENABLE_0_REG = "FALSE";
  localparam [40:1] SWITCH_ENABLE_1_REG = "FALSE";
  localparam [40:1] SW_TESTMODE_SEL_0_REG = "FALSE";
  localparam [40:1] SW_TESTMODE_SEL_1_REG = "FALSE";

`ifdef XIL_XECLIB
  wire PHY_PCLK_INVERT_01_BIN;
  wire PHY_PCLK_INVERT_02_BIN;
`else
  reg PHY_PCLK_INVERT_01_BIN;
  reg PHY_PCLK_INVERT_02_BIN;
`endif

  reg attr_test;
  reg attr_err;
  tri0 glblGSR = glbl.GSR;

  wire APB_0_PREADY_out;
  wire APB_0_PSLVERR_out;
  wire APB_1_PREADY_out;
  wire APB_1_PSLVERR_out;
  wire AXI_00_ARREADY_out;
  wire AXI_00_AWREADY_out;
  wire AXI_00_BVALID_out;
  wire AXI_00_DFI_CLK_BUF_out;
  wire AXI_00_DFI_INIT_COMPLETE_out;
  wire AXI_00_DFI_PHYUPD_REQ_out;
  wire AXI_00_DFI_PHY_LP_STATE_out;
  wire AXI_00_DFI_RST_N_BUF_out;
  wire AXI_00_RLAST_out;
  wire AXI_00_RVALID_out;
  wire AXI_00_WREADY_out;
  wire AXI_01_ARREADY_out;
  wire AXI_01_AWREADY_out;
  wire AXI_01_BVALID_out;
  wire AXI_01_DFI_CLK_BUF_out;
  wire AXI_01_DFI_INIT_COMPLETE_out;
  wire AXI_01_DFI_PHYUPD_REQ_out;
  wire AXI_01_DFI_PHY_LP_STATE_out;
  wire AXI_01_DFI_RST_N_BUF_out;
  wire AXI_01_RLAST_out;
  wire AXI_01_RVALID_out;
  wire AXI_01_WREADY_out;
  wire AXI_02_ARREADY_out;
  wire AXI_02_AWREADY_out;
  wire AXI_02_BVALID_out;
  wire AXI_02_DFI_CLK_BUF_out;
  wire AXI_02_DFI_INIT_COMPLETE_out;
  wire AXI_02_DFI_PHYUPD_REQ_out;
  wire AXI_02_DFI_PHY_LP_STATE_out;
  wire AXI_02_DFI_RST_N_BUF_out;
  wire AXI_02_RLAST_out;
  wire AXI_02_RVALID_out;
  wire AXI_02_WREADY_out;
  wire AXI_03_ARREADY_out;
  wire AXI_03_AWREADY_out;
  wire AXI_03_BVALID_out;
  wire AXI_03_DFI_CLK_BUF_out;
  wire AXI_03_DFI_INIT_COMPLETE_out;
  wire AXI_03_DFI_PHYUPD_REQ_out;
  wire AXI_03_DFI_PHY_LP_STATE_out;
  wire AXI_03_DFI_RST_N_BUF_out;
  wire AXI_03_RLAST_out;
  wire AXI_03_RVALID_out;
  wire AXI_03_WREADY_out;
  wire AXI_04_ARREADY_out;
  wire AXI_04_AWREADY_out;
  wire AXI_04_BVALID_out;
  wire AXI_04_DFI_CLK_BUF_out;
  wire AXI_04_DFI_INIT_COMPLETE_out;
  wire AXI_04_DFI_PHYUPD_REQ_out;
  wire AXI_04_DFI_PHY_LP_STATE_out;
  wire AXI_04_DFI_RST_N_BUF_out;
  wire AXI_04_RLAST_out;
  wire AXI_04_RVALID_out;
  wire AXI_04_WREADY_out;
  wire AXI_05_ARREADY_out;
  wire AXI_05_AWREADY_out;
  wire AXI_05_BVALID_out;
  wire AXI_05_DFI_CLK_BUF_out;
  wire AXI_05_DFI_INIT_COMPLETE_out;
  wire AXI_05_DFI_PHYUPD_REQ_out;
  wire AXI_05_DFI_PHY_LP_STATE_out;
  wire AXI_05_DFI_RST_N_BUF_out;
  wire AXI_05_RLAST_out;
  wire AXI_05_RVALID_out;
  wire AXI_05_WREADY_out;
  wire AXI_06_ARREADY_out;
  wire AXI_06_AWREADY_out;
  wire AXI_06_BVALID_out;
  wire AXI_06_DFI_CLK_BUF_out;
  wire AXI_06_DFI_INIT_COMPLETE_out;
  wire AXI_06_DFI_PHYUPD_REQ_out;
  wire AXI_06_DFI_PHY_LP_STATE_out;
  wire AXI_06_DFI_RST_N_BUF_out;
  wire AXI_06_RLAST_out;
  wire AXI_06_RVALID_out;
  wire AXI_06_WREADY_out;
  wire AXI_07_ARREADY_out;
  wire AXI_07_AWREADY_out;
  wire AXI_07_BVALID_out;
  wire AXI_07_DFI_CLK_BUF_out;
  wire AXI_07_DFI_INIT_COMPLETE_out;
  wire AXI_07_DFI_PHYUPD_REQ_out;
  wire AXI_07_DFI_PHY_LP_STATE_out;
  wire AXI_07_DFI_RST_N_BUF_out;
  wire AXI_07_RLAST_out;
  wire AXI_07_RVALID_out;
  wire AXI_07_WREADY_out;
  wire AXI_08_ARREADY_out;
  wire AXI_08_AWREADY_out;
  wire AXI_08_BVALID_out;
  wire AXI_08_DFI_CLK_BUF_out;
  wire AXI_08_DFI_INIT_COMPLETE_out;
  wire AXI_08_DFI_PHYUPD_REQ_out;
  wire AXI_08_DFI_PHY_LP_STATE_out;
  wire AXI_08_DFI_RST_N_BUF_out;
  wire AXI_08_RLAST_out;
  wire AXI_08_RVALID_out;
  wire AXI_08_WREADY_out;
  wire AXI_09_ARREADY_out;
  wire AXI_09_AWREADY_out;
  wire AXI_09_BVALID_out;
  wire AXI_09_DFI_CLK_BUF_out;
  wire AXI_09_DFI_INIT_COMPLETE_out;
  wire AXI_09_DFI_PHYUPD_REQ_out;
  wire AXI_09_DFI_PHY_LP_STATE_out;
  wire AXI_09_DFI_RST_N_BUF_out;
  wire AXI_09_RLAST_out;
  wire AXI_09_RVALID_out;
  wire AXI_09_WREADY_out;
  wire AXI_10_ARREADY_out;
  wire AXI_10_AWREADY_out;
  wire AXI_10_BVALID_out;
  wire AXI_10_DFI_CLK_BUF_out;
  wire AXI_10_DFI_INIT_COMPLETE_out;
  wire AXI_10_DFI_PHYUPD_REQ_out;
  wire AXI_10_DFI_PHY_LP_STATE_out;
  wire AXI_10_DFI_RST_N_BUF_out;
  wire AXI_10_RLAST_out;
  wire AXI_10_RVALID_out;
  wire AXI_10_WREADY_out;
  wire AXI_11_ARREADY_out;
  wire AXI_11_AWREADY_out;
  wire AXI_11_BVALID_out;
  wire AXI_11_DFI_CLK_BUF_out;
  wire AXI_11_DFI_INIT_COMPLETE_out;
  wire AXI_11_DFI_PHYUPD_REQ_out;
  wire AXI_11_DFI_PHY_LP_STATE_out;
  wire AXI_11_DFI_RST_N_BUF_out;
  wire AXI_11_RLAST_out;
  wire AXI_11_RVALID_out;
  wire AXI_11_WREADY_out;
  wire AXI_12_ARREADY_out;
  wire AXI_12_AWREADY_out;
  wire AXI_12_BVALID_out;
  wire AXI_12_DFI_CLK_BUF_out;
  wire AXI_12_DFI_INIT_COMPLETE_out;
  wire AXI_12_DFI_PHYUPD_REQ_out;
  wire AXI_12_DFI_PHY_LP_STATE_out;
  wire AXI_12_DFI_RST_N_BUF_out;
  wire AXI_12_RLAST_out;
  wire AXI_12_RVALID_out;
  wire AXI_12_WREADY_out;
  wire AXI_13_ARREADY_out;
  wire AXI_13_AWREADY_out;
  wire AXI_13_BVALID_out;
  wire AXI_13_DFI_CLK_BUF_out;
  wire AXI_13_DFI_INIT_COMPLETE_out;
  wire AXI_13_DFI_PHYUPD_REQ_out;
  wire AXI_13_DFI_PHY_LP_STATE_out;
  wire AXI_13_DFI_RST_N_BUF_out;
  wire AXI_13_RLAST_out;
  wire AXI_13_RVALID_out;
  wire AXI_13_WREADY_out;
  wire AXI_14_ARREADY_out;
  wire AXI_14_AWREADY_out;
  wire AXI_14_BVALID_out;
  wire AXI_14_DFI_CLK_BUF_out;
  wire AXI_14_DFI_INIT_COMPLETE_out;
  wire AXI_14_DFI_PHYUPD_REQ_out;
  wire AXI_14_DFI_PHY_LP_STATE_out;
  wire AXI_14_DFI_RST_N_BUF_out;
  wire AXI_14_RLAST_out;
  wire AXI_14_RVALID_out;
  wire AXI_14_WREADY_out;
  wire AXI_15_ARREADY_out;
  wire AXI_15_AWREADY_out;
  wire AXI_15_BVALID_out;
  wire AXI_15_DFI_CLK_BUF_out;
  wire AXI_15_DFI_INIT_COMPLETE_out;
  wire AXI_15_DFI_PHYUPD_REQ_out;
  wire AXI_15_DFI_PHY_LP_STATE_out;
  wire AXI_15_DFI_RST_N_BUF_out;
  wire AXI_15_RLAST_out;
  wire AXI_15_RVALID_out;
  wire AXI_15_WREADY_out;
  wire AXI_16_ARREADY_out;
  wire AXI_16_AWREADY_out;
  wire AXI_16_BVALID_out;
  wire AXI_16_DFI_CLK_BUF_out;
  wire AXI_16_DFI_INIT_COMPLETE_out;
  wire AXI_16_DFI_PHYUPD_REQ_out;
  wire AXI_16_DFI_PHY_LP_STATE_out;
  wire AXI_16_DFI_RST_N_BUF_out;
  wire AXI_16_RLAST_out;
  wire AXI_16_RVALID_out;
  wire AXI_16_WREADY_out;
  wire AXI_17_ARREADY_out;
  wire AXI_17_AWREADY_out;
  wire AXI_17_BVALID_out;
  wire AXI_17_DFI_CLK_BUF_out;
  wire AXI_17_DFI_INIT_COMPLETE_out;
  wire AXI_17_DFI_PHYUPD_REQ_out;
  wire AXI_17_DFI_PHY_LP_STATE_out;
  wire AXI_17_DFI_RST_N_BUF_out;
  wire AXI_17_RLAST_out;
  wire AXI_17_RVALID_out;
  wire AXI_17_WREADY_out;
  wire AXI_18_ARREADY_out;
  wire AXI_18_AWREADY_out;
  wire AXI_18_BVALID_out;
  wire AXI_18_DFI_CLK_BUF_out;
  wire AXI_18_DFI_INIT_COMPLETE_out;
  wire AXI_18_DFI_PHYUPD_REQ_out;
  wire AXI_18_DFI_PHY_LP_STATE_out;
  wire AXI_18_DFI_RST_N_BUF_out;
  wire AXI_18_RLAST_out;
  wire AXI_18_RVALID_out;
  wire AXI_18_WREADY_out;
  wire AXI_19_ARREADY_out;
  wire AXI_19_AWREADY_out;
  wire AXI_19_BVALID_out;
  wire AXI_19_DFI_CLK_BUF_out;
  wire AXI_19_DFI_INIT_COMPLETE_out;
  wire AXI_19_DFI_PHYUPD_REQ_out;
  wire AXI_19_DFI_PHY_LP_STATE_out;
  wire AXI_19_DFI_RST_N_BUF_out;
  wire AXI_19_RLAST_out;
  wire AXI_19_RVALID_out;
  wire AXI_19_WREADY_out;
  wire AXI_20_ARREADY_out;
  wire AXI_20_AWREADY_out;
  wire AXI_20_BVALID_out;
  wire AXI_20_DFI_CLK_BUF_out;
  wire AXI_20_DFI_INIT_COMPLETE_out;
  wire AXI_20_DFI_PHYUPD_REQ_out;
  wire AXI_20_DFI_PHY_LP_STATE_out;
  wire AXI_20_DFI_RST_N_BUF_out;
  wire AXI_20_RLAST_out;
  wire AXI_20_RVALID_out;
  wire AXI_20_WREADY_out;
  wire AXI_21_ARREADY_out;
  wire AXI_21_AWREADY_out;
  wire AXI_21_BVALID_out;
  wire AXI_21_DFI_CLK_BUF_out;
  wire AXI_21_DFI_INIT_COMPLETE_out;
  wire AXI_21_DFI_PHYUPD_REQ_out;
  wire AXI_21_DFI_PHY_LP_STATE_out;
  wire AXI_21_DFI_RST_N_BUF_out;
  wire AXI_21_RLAST_out;
  wire AXI_21_RVALID_out;
  wire AXI_21_WREADY_out;
  wire AXI_22_ARREADY_out;
  wire AXI_22_AWREADY_out;
  wire AXI_22_BVALID_out;
  wire AXI_22_DFI_CLK_BUF_out;
  wire AXI_22_DFI_INIT_COMPLETE_out;
  wire AXI_22_DFI_PHYUPD_REQ_out;
  wire AXI_22_DFI_PHY_LP_STATE_out;
  wire AXI_22_DFI_RST_N_BUF_out;
  wire AXI_22_RLAST_out;
  wire AXI_22_RVALID_out;
  wire AXI_22_WREADY_out;
  wire AXI_23_ARREADY_out;
  wire AXI_23_AWREADY_out;
  wire AXI_23_BVALID_out;
  wire AXI_23_DFI_CLK_BUF_out;
  wire AXI_23_DFI_INIT_COMPLETE_out;
  wire AXI_23_DFI_PHYUPD_REQ_out;
  wire AXI_23_DFI_PHY_LP_STATE_out;
  wire AXI_23_DFI_RST_N_BUF_out;
  wire AXI_23_RLAST_out;
  wire AXI_23_RVALID_out;
  wire AXI_23_WREADY_out;
  wire AXI_24_ARREADY_out;
  wire AXI_24_AWREADY_out;
  wire AXI_24_BVALID_out;
  wire AXI_24_DFI_CLK_BUF_out;
  wire AXI_24_DFI_INIT_COMPLETE_out;
  wire AXI_24_DFI_PHYUPD_REQ_out;
  wire AXI_24_DFI_PHY_LP_STATE_out;
  wire AXI_24_DFI_RST_N_BUF_out;
  wire AXI_24_RLAST_out;
  wire AXI_24_RVALID_out;
  wire AXI_24_WREADY_out;
  wire AXI_25_ARREADY_out;
  wire AXI_25_AWREADY_out;
  wire AXI_25_BVALID_out;
  wire AXI_25_DFI_CLK_BUF_out;
  wire AXI_25_DFI_INIT_COMPLETE_out;
  wire AXI_25_DFI_PHYUPD_REQ_out;
  wire AXI_25_DFI_PHY_LP_STATE_out;
  wire AXI_25_DFI_RST_N_BUF_out;
  wire AXI_25_RLAST_out;
  wire AXI_25_RVALID_out;
  wire AXI_25_WREADY_out;
  wire AXI_26_ARREADY_out;
  wire AXI_26_AWREADY_out;
  wire AXI_26_BVALID_out;
  wire AXI_26_DFI_CLK_BUF_out;
  wire AXI_26_DFI_INIT_COMPLETE_out;
  wire AXI_26_DFI_PHYUPD_REQ_out;
  wire AXI_26_DFI_PHY_LP_STATE_out;
  wire AXI_26_DFI_RST_N_BUF_out;
  wire AXI_26_RLAST_out;
  wire AXI_26_RVALID_out;
  wire AXI_26_WREADY_out;
  wire AXI_27_ARREADY_out;
  wire AXI_27_AWREADY_out;
  wire AXI_27_BVALID_out;
  wire AXI_27_DFI_CLK_BUF_out;
  wire AXI_27_DFI_INIT_COMPLETE_out;
  wire AXI_27_DFI_PHYUPD_REQ_out;
  wire AXI_27_DFI_PHY_LP_STATE_out;
  wire AXI_27_DFI_RST_N_BUF_out;
  wire AXI_27_RLAST_out;
  wire AXI_27_RVALID_out;
  wire AXI_27_WREADY_out;
  wire AXI_28_ARREADY_out;
  wire AXI_28_AWREADY_out;
  wire AXI_28_BVALID_out;
  wire AXI_28_DFI_CLK_BUF_out;
  wire AXI_28_DFI_INIT_COMPLETE_out;
  wire AXI_28_DFI_PHYUPD_REQ_out;
  wire AXI_28_DFI_PHY_LP_STATE_out;
  wire AXI_28_DFI_RST_N_BUF_out;
  wire AXI_28_RLAST_out;
  wire AXI_28_RVALID_out;
  wire AXI_28_WREADY_out;
  wire AXI_29_ARREADY_out;
  wire AXI_29_AWREADY_out;
  wire AXI_29_BVALID_out;
  wire AXI_29_DFI_CLK_BUF_out;
  wire AXI_29_DFI_INIT_COMPLETE_out;
  wire AXI_29_DFI_PHYUPD_REQ_out;
  wire AXI_29_DFI_PHY_LP_STATE_out;
  wire AXI_29_DFI_RST_N_BUF_out;
  wire AXI_29_RLAST_out;
  wire AXI_29_RVALID_out;
  wire AXI_29_WREADY_out;
  wire AXI_30_ARREADY_out;
  wire AXI_30_AWREADY_out;
  wire AXI_30_BVALID_out;
  wire AXI_30_DFI_CLK_BUF_out;
  wire AXI_30_DFI_INIT_COMPLETE_out;
  wire AXI_30_DFI_PHYUPD_REQ_out;
  wire AXI_30_DFI_PHY_LP_STATE_out;
  wire AXI_30_DFI_RST_N_BUF_out;
  wire AXI_30_RLAST_out;
  wire AXI_30_RVALID_out;
  wire AXI_30_WREADY_out;
  wire AXI_31_ARREADY_out;
  wire AXI_31_AWREADY_out;
  wire AXI_31_BVALID_out;
  wire AXI_31_DFI_CLK_BUF_out;
  wire AXI_31_DFI_INIT_COMPLETE_out;
  wire AXI_31_DFI_PHYUPD_REQ_out;
  wire AXI_31_DFI_PHY_LP_STATE_out;
  wire AXI_31_DFI_RST_N_BUF_out;
  wire AXI_31_RLAST_out;
  wire AXI_31_RVALID_out;
  wire AXI_31_WREADY_out;
  wire DRAM_0_STAT_CATTRIP_out;
  wire DRAM_1_STAT_CATTRIP_out;
  wire [17:0] DBG_OUT_00_out;
  wire [17:0] DBG_OUT_01_out;
  wire [17:0] DBG_OUT_02_out;
  wire [17:0] DBG_OUT_03_out;
  wire [17:0] DBG_OUT_04_out;
  wire [17:0] DBG_OUT_05_out;
  wire [17:0] DBG_OUT_06_out;
  wire [17:0] DBG_OUT_07_out;
  wire [17:0] DBG_OUT_08_out;
  wire [17:0] DBG_OUT_09_out;
  wire [17:0] DBG_OUT_10_out;
  wire [17:0] DBG_OUT_11_out;
  wire [17:0] DBG_OUT_12_out;
  wire [17:0] DBG_OUT_13_out;
  wire [17:0] DBG_OUT_14_out;
  wire [17:0] DBG_OUT_15_out;
  wire [17:0] DBG_OUT_16_out;
  wire [17:0] DBG_OUT_17_out;
  wire [17:0] DBG_OUT_18_out;
  wire [17:0] DBG_OUT_19_out;
  wire [17:0] DBG_OUT_20_out;
  wire [17:0] DBG_OUT_21_out;
  wire [17:0] DBG_OUT_22_out;
  wire [17:0] DBG_OUT_23_out;
  wire [17:0] DBG_OUT_24_out;
  wire [17:0] DBG_OUT_25_out;
  wire [17:0] DBG_OUT_26_out;
  wire [17:0] DBG_OUT_27_out;
  wire [17:0] DBG_OUT_28_out;
  wire [17:0] DBG_OUT_29_out;
  wire [17:0] DBG_OUT_30_out;
  wire [17:0] DBG_OUT_31_out;
  wire [1:0] AXI_00_BRESP_out;
  wire [1:0] AXI_00_DFI_AW_AERR_N_out;
  wire [1:0] AXI_00_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_00_RRESP_out;
  wire [1:0] AXI_01_BRESP_out;
  wire [1:0] AXI_01_DFI_AW_AERR_N_out;
  wire [1:0] AXI_01_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_01_RRESP_out;
  wire [1:0] AXI_02_BRESP_out;
  wire [1:0] AXI_02_DFI_AW_AERR_N_out;
  wire [1:0] AXI_02_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_02_RRESP_out;
  wire [1:0] AXI_03_BRESP_out;
  wire [1:0] AXI_03_DFI_AW_AERR_N_out;
  wire [1:0] AXI_03_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_03_RRESP_out;
  wire [1:0] AXI_04_BRESP_out;
  wire [1:0] AXI_04_DFI_AW_AERR_N_out;
  wire [1:0] AXI_04_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_04_RRESP_out;
  wire [1:0] AXI_05_BRESP_out;
  wire [1:0] AXI_05_DFI_AW_AERR_N_out;
  wire [1:0] AXI_05_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_05_RRESP_out;
  wire [1:0] AXI_06_BRESP_out;
  wire [1:0] AXI_06_DFI_AW_AERR_N_out;
  wire [1:0] AXI_06_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_06_RRESP_out;
  wire [1:0] AXI_07_BRESP_out;
  wire [1:0] AXI_07_DFI_AW_AERR_N_out;
  wire [1:0] AXI_07_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_07_RRESP_out;
  wire [1:0] AXI_08_BRESP_out;
  wire [1:0] AXI_08_DFI_AW_AERR_N_out;
  wire [1:0] AXI_08_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_08_RRESP_out;
  wire [1:0] AXI_09_BRESP_out;
  wire [1:0] AXI_09_DFI_AW_AERR_N_out;
  wire [1:0] AXI_09_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_09_RRESP_out;
  wire [1:0] AXI_10_BRESP_out;
  wire [1:0] AXI_10_DFI_AW_AERR_N_out;
  wire [1:0] AXI_10_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_10_RRESP_out;
  wire [1:0] AXI_11_BRESP_out;
  wire [1:0] AXI_11_DFI_AW_AERR_N_out;
  wire [1:0] AXI_11_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_11_RRESP_out;
  wire [1:0] AXI_12_BRESP_out;
  wire [1:0] AXI_12_DFI_AW_AERR_N_out;
  wire [1:0] AXI_12_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_12_RRESP_out;
  wire [1:0] AXI_13_BRESP_out;
  wire [1:0] AXI_13_DFI_AW_AERR_N_out;
  wire [1:0] AXI_13_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_13_RRESP_out;
  wire [1:0] AXI_14_BRESP_out;
  wire [1:0] AXI_14_DFI_AW_AERR_N_out;
  wire [1:0] AXI_14_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_14_RRESP_out;
  wire [1:0] AXI_15_BRESP_out;
  wire [1:0] AXI_15_DFI_AW_AERR_N_out;
  wire [1:0] AXI_15_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_15_RRESP_out;
  wire [1:0] AXI_16_BRESP_out;
  wire [1:0] AXI_16_DFI_AW_AERR_N_out;
  wire [1:0] AXI_16_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_16_RRESP_out;
  wire [1:0] AXI_17_BRESP_out;
  wire [1:0] AXI_17_DFI_AW_AERR_N_out;
  wire [1:0] AXI_17_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_17_RRESP_out;
  wire [1:0] AXI_18_BRESP_out;
  wire [1:0] AXI_18_DFI_AW_AERR_N_out;
  wire [1:0] AXI_18_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_18_RRESP_out;
  wire [1:0] AXI_19_BRESP_out;
  wire [1:0] AXI_19_DFI_AW_AERR_N_out;
  wire [1:0] AXI_19_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_19_RRESP_out;
  wire [1:0] AXI_20_BRESP_out;
  wire [1:0] AXI_20_DFI_AW_AERR_N_out;
  wire [1:0] AXI_20_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_20_RRESP_out;
  wire [1:0] AXI_21_BRESP_out;
  wire [1:0] AXI_21_DFI_AW_AERR_N_out;
  wire [1:0] AXI_21_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_21_RRESP_out;
  wire [1:0] AXI_22_BRESP_out;
  wire [1:0] AXI_22_DFI_AW_AERR_N_out;
  wire [1:0] AXI_22_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_22_RRESP_out;
  wire [1:0] AXI_23_BRESP_out;
  wire [1:0] AXI_23_DFI_AW_AERR_N_out;
  wire [1:0] AXI_23_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_23_RRESP_out;
  wire [1:0] AXI_24_BRESP_out;
  wire [1:0] AXI_24_DFI_AW_AERR_N_out;
  wire [1:0] AXI_24_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_24_RRESP_out;
  wire [1:0] AXI_25_BRESP_out;
  wire [1:0] AXI_25_DFI_AW_AERR_N_out;
  wire [1:0] AXI_25_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_25_RRESP_out;
  wire [1:0] AXI_26_BRESP_out;
  wire [1:0] AXI_26_DFI_AW_AERR_N_out;
  wire [1:0] AXI_26_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_26_RRESP_out;
  wire [1:0] AXI_27_BRESP_out;
  wire [1:0] AXI_27_DFI_AW_AERR_N_out;
  wire [1:0] AXI_27_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_27_RRESP_out;
  wire [1:0] AXI_28_BRESP_out;
  wire [1:0] AXI_28_DFI_AW_AERR_N_out;
  wire [1:0] AXI_28_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_28_RRESP_out;
  wire [1:0] AXI_29_BRESP_out;
  wire [1:0] AXI_29_DFI_AW_AERR_N_out;
  wire [1:0] AXI_29_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_29_RRESP_out;
  wire [1:0] AXI_30_BRESP_out;
  wire [1:0] AXI_30_DFI_AW_AERR_N_out;
  wire [1:0] AXI_30_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_30_RRESP_out;
  wire [1:0] AXI_31_BRESP_out;
  wire [1:0] AXI_31_DFI_AW_AERR_N_out;
  wire [1:0] AXI_31_DFI_DW_RDDATA_VALID_out;
  wire [1:0] AXI_31_RRESP_out;
  wire [1:0] DLL_SCAN_OUT_00_out;
  wire [1:0] DLL_SCAN_OUT_01_out;
  wire [1:0] IO_SCAN_OUT_00_out;
  wire [1:0] IO_SCAN_OUT_01_out;
  wire [1:0] MC_SCAN_OUT_00_out;
  wire [1:0] MC_SCAN_OUT_01_out;
  wire [1:0] MC_SCAN_OUT_02_out;
  wire [1:0] MC_SCAN_OUT_03_out;
  wire [1:0] MC_SCAN_OUT_04_out;
  wire [1:0] MC_SCAN_OUT_05_out;
  wire [1:0] MC_SCAN_OUT_06_out;
  wire [1:0] MC_SCAN_OUT_07_out;
  wire [1:0] MC_SCAN_OUT_08_out;
  wire [1:0] MC_SCAN_OUT_09_out;
  wire [1:0] MC_SCAN_OUT_10_out;
  wire [1:0] MC_SCAN_OUT_11_out;
  wire [1:0] MC_SCAN_OUT_12_out;
  wire [1:0] MC_SCAN_OUT_13_out;
  wire [1:0] MC_SCAN_OUT_14_out;
  wire [1:0] MC_SCAN_OUT_15_out;
  wire [1:0] PHY_SCAN_OUT_00_out;
  wire [1:0] PHY_SCAN_OUT_01_out;
  wire [1:0] STATUS_00_out;
  wire [1:0] STATUS_01_out;
  wire [1:0] STATUS_02_out;
  wire [1:0] STATUS_03_out;
  wire [1:0] STATUS_04_out;
  wire [1:0] STATUS_05_out;
  wire [1:0] STATUS_06_out;
  wire [1:0] STATUS_07_out;
  wire [1:0] STATUS_08_out;
  wire [1:0] STATUS_09_out;
  wire [1:0] STATUS_10_out;
  wire [1:0] STATUS_11_out;
  wire [1:0] STATUS_12_out;
  wire [1:0] STATUS_13_out;
  wire [1:0] STATUS_14_out;
  wire [1:0] STATUS_15_out;
  wire [1:0] SW_SCAN_OUT_00_out;
  wire [1:0] SW_SCAN_OUT_01_out;
  wire [1:0] SW_SCAN_OUT_02_out;
  wire [1:0] SW_SCAN_OUT_03_out;
  wire [1:0] SW_SCAN_OUT_04_out;
  wire [1:0] SW_SCAN_OUT_05_out;
  wire [1:0] SW_SCAN_OUT_06_out;
  wire [1:0] SW_SCAN_OUT_07_out;
  wire [20:0] AXI_00_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_01_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_02_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_03_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_04_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_05_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_06_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_07_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_08_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_09_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_10_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_11_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_12_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_13_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_14_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_15_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_16_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_17_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_18_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_19_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_20_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_21_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_22_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_23_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_24_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_25_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_26_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_27_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_28_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_29_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_30_DFI_DW_RDDATA_DBI_out;
  wire [20:0] AXI_31_DFI_DW_RDDATA_DBI_out;
  wire [255:0] AXI_00_RDATA_out;
  wire [255:0] AXI_01_RDATA_out;
  wire [255:0] AXI_02_RDATA_out;
  wire [255:0] AXI_03_RDATA_out;
  wire [255:0] AXI_04_RDATA_out;
  wire [255:0] AXI_05_RDATA_out;
  wire [255:0] AXI_06_RDATA_out;
  wire [255:0] AXI_07_RDATA_out;
  wire [255:0] AXI_08_RDATA_out;
  wire [255:0] AXI_09_RDATA_out;
  wire [255:0] AXI_10_RDATA_out;
  wire [255:0] AXI_11_RDATA_out;
  wire [255:0] AXI_12_RDATA_out;
  wire [255:0] AXI_13_RDATA_out;
  wire [255:0] AXI_14_RDATA_out;
  wire [255:0] AXI_15_RDATA_out;
  wire [255:0] AXI_16_RDATA_out;
  wire [255:0] AXI_17_RDATA_out;
  wire [255:0] AXI_18_RDATA_out;
  wire [255:0] AXI_19_RDATA_out;
  wire [255:0] AXI_20_RDATA_out;
  wire [255:0] AXI_21_RDATA_out;
  wire [255:0] AXI_22_RDATA_out;
  wire [255:0] AXI_23_RDATA_out;
  wire [255:0] AXI_24_RDATA_out;
  wire [255:0] AXI_25_RDATA_out;
  wire [255:0] AXI_26_RDATA_out;
  wire [255:0] AXI_27_RDATA_out;
  wire [255:0] AXI_28_RDATA_out;
  wire [255:0] AXI_29_RDATA_out;
  wire [255:0] AXI_30_RDATA_out;
  wire [255:0] AXI_31_RDATA_out;
  wire [2:0] DRAM_0_STAT_TEMP_out;
  wire [2:0] DRAM_1_STAT_TEMP_out;
  wire [31:0] APB_0_PRDATA_out;
  wire [31:0] APB_1_PRDATA_out;
  wire [31:0] AXI_00_RDATA_PARITY_out;
  wire [31:0] AXI_01_RDATA_PARITY_out;
  wire [31:0] AXI_02_RDATA_PARITY_out;
  wire [31:0] AXI_03_RDATA_PARITY_out;
  wire [31:0] AXI_04_RDATA_PARITY_out;
  wire [31:0] AXI_05_RDATA_PARITY_out;
  wire [31:0] AXI_06_RDATA_PARITY_out;
  wire [31:0] AXI_07_RDATA_PARITY_out;
  wire [31:0] AXI_08_RDATA_PARITY_out;
  wire [31:0] AXI_09_RDATA_PARITY_out;
  wire [31:0] AXI_10_RDATA_PARITY_out;
  wire [31:0] AXI_11_RDATA_PARITY_out;
  wire [31:0] AXI_12_RDATA_PARITY_out;
  wire [31:0] AXI_13_RDATA_PARITY_out;
  wire [31:0] AXI_14_RDATA_PARITY_out;
  wire [31:0] AXI_15_RDATA_PARITY_out;
  wire [31:0] AXI_16_RDATA_PARITY_out;
  wire [31:0] AXI_17_RDATA_PARITY_out;
  wire [31:0] AXI_18_RDATA_PARITY_out;
  wire [31:0] AXI_19_RDATA_PARITY_out;
  wire [31:0] AXI_20_RDATA_PARITY_out;
  wire [31:0] AXI_21_RDATA_PARITY_out;
  wire [31:0] AXI_22_RDATA_PARITY_out;
  wire [31:0] AXI_23_RDATA_PARITY_out;
  wire [31:0] AXI_24_RDATA_PARITY_out;
  wire [31:0] AXI_25_RDATA_PARITY_out;
  wire [31:0] AXI_26_RDATA_PARITY_out;
  wire [31:0] AXI_27_RDATA_PARITY_out;
  wire [31:0] AXI_28_RDATA_PARITY_out;
  wire [31:0] AXI_29_RDATA_PARITY_out;
  wire [31:0] AXI_30_RDATA_PARITY_out;
  wire [31:0] AXI_31_RDATA_PARITY_out;
  wire [5:0] AXI_00_BID_out;
  wire [5:0] AXI_00_MC_STATUS_out;
  wire [5:0] AXI_00_RID_out;
  wire [5:0] AXI_01_BID_out;
  wire [5:0] AXI_01_RID_out;
  wire [5:0] AXI_02_BID_out;
  wire [5:0] AXI_02_MC_STATUS_out;
  wire [5:0] AXI_02_RID_out;
  wire [5:0] AXI_03_BID_out;
  wire [5:0] AXI_03_RID_out;
  wire [5:0] AXI_04_BID_out;
  wire [5:0] AXI_04_MC_STATUS_out;
  wire [5:0] AXI_04_RID_out;
  wire [5:0] AXI_05_BID_out;
  wire [5:0] AXI_05_RID_out;
  wire [5:0] AXI_06_BID_out;
  wire [5:0] AXI_06_MC_STATUS_out;
  wire [5:0] AXI_06_RID_out;
  wire [5:0] AXI_07_BID_out;
  wire [5:0] AXI_07_RID_out;
  wire [5:0] AXI_08_BID_out;
  wire [5:0] AXI_08_MC_STATUS_out;
  wire [5:0] AXI_08_RID_out;
  wire [5:0] AXI_09_BID_out;
  wire [5:0] AXI_09_RID_out;
  wire [5:0] AXI_10_BID_out;
  wire [5:0] AXI_10_MC_STATUS_out;
  wire [5:0] AXI_10_RID_out;
  wire [5:0] AXI_11_BID_out;
  wire [5:0] AXI_11_RID_out;
  wire [5:0] AXI_12_BID_out;
  wire [5:0] AXI_12_MC_STATUS_out;
  wire [5:0] AXI_12_RID_out;
  wire [5:0] AXI_13_BID_out;
  wire [5:0] AXI_13_RID_out;
  wire [5:0] AXI_14_BID_out;
  wire [5:0] AXI_14_MC_STATUS_out;
  wire [5:0] AXI_14_RID_out;
  wire [5:0] AXI_15_BID_out;
  wire [5:0] AXI_15_RID_out;
  wire [5:0] AXI_16_BID_out;
  wire [5:0] AXI_16_MC_STATUS_out;
  wire [5:0] AXI_16_RID_out;
  wire [5:0] AXI_17_BID_out;
  wire [5:0] AXI_17_RID_out;
  wire [5:0] AXI_18_BID_out;
  wire [5:0] AXI_18_MC_STATUS_out;
  wire [5:0] AXI_18_RID_out;
  wire [5:0] AXI_19_BID_out;
  wire [5:0] AXI_19_RID_out;
  wire [5:0] AXI_20_BID_out;
  wire [5:0] AXI_20_MC_STATUS_out;
  wire [5:0] AXI_20_RID_out;
  wire [5:0] AXI_21_BID_out;
  wire [5:0] AXI_21_RID_out;
  wire [5:0] AXI_22_BID_out;
  wire [5:0] AXI_22_MC_STATUS_out;
  wire [5:0] AXI_22_RID_out;
  wire [5:0] AXI_23_BID_out;
  wire [5:0] AXI_23_RID_out;
  wire [5:0] AXI_24_BID_out;
  wire [5:0] AXI_24_MC_STATUS_out;
  wire [5:0] AXI_24_RID_out;
  wire [5:0] AXI_25_BID_out;
  wire [5:0] AXI_25_RID_out;
  wire [5:0] AXI_26_BID_out;
  wire [5:0] AXI_26_MC_STATUS_out;
  wire [5:0] AXI_26_RID_out;
  wire [5:0] AXI_27_BID_out;
  wire [5:0] AXI_27_RID_out;
  wire [5:0] AXI_28_BID_out;
  wire [5:0] AXI_28_MC_STATUS_out;
  wire [5:0] AXI_28_RID_out;
  wire [5:0] AXI_29_BID_out;
  wire [5:0] AXI_29_RID_out;
  wire [5:0] AXI_30_BID_out;
  wire [5:0] AXI_30_MC_STATUS_out;
  wire [5:0] AXI_30_RID_out;
  wire [5:0] AXI_31_BID_out;
  wire [5:0] AXI_31_RID_out;
  wire [7:0] AXI_00_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_00_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_00_PHY_STATUS_out;
  wire [7:0] AXI_01_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_01_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_02_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_02_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_02_PHY_STATUS_out;
  wire [7:0] AXI_03_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_03_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_04_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_04_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_04_PHY_STATUS_out;
  wire [7:0] AXI_05_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_05_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_06_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_06_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_06_PHY_STATUS_out;
  wire [7:0] AXI_07_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_07_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_08_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_08_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_08_PHY_STATUS_out;
  wire [7:0] AXI_09_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_09_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_10_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_10_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_10_PHY_STATUS_out;
  wire [7:0] AXI_11_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_11_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_12_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_12_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_12_PHY_STATUS_out;
  wire [7:0] AXI_13_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_13_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_14_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_14_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_14_PHY_STATUS_out;
  wire [7:0] AXI_15_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_15_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_16_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_16_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_16_PHY_STATUS_out;
  wire [7:0] AXI_17_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_17_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_18_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_18_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_18_PHY_STATUS_out;
  wire [7:0] AXI_19_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_19_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_20_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_20_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_20_PHY_STATUS_out;
  wire [7:0] AXI_21_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_21_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_22_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_22_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_22_PHY_STATUS_out;
  wire [7:0] AXI_23_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_23_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_24_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_24_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_24_PHY_STATUS_out;
  wire [7:0] AXI_25_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_25_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_26_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_26_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_26_PHY_STATUS_out;
  wire [7:0] AXI_27_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_27_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_28_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_28_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_28_PHY_STATUS_out;
  wire [7:0] AXI_29_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_29_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_30_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_30_DFI_DW_RDDATA_DERR_out;
  wire [7:0] AXI_30_PHY_STATUS_out;
  wire [7:0] AXI_31_DFI_DBI_BYTE_DISABLE_out;
  wire [7:0] AXI_31_DFI_DW_RDDATA_DERR_out;
  wire [7:0] BLI_SCAN_OUT_00_out;
  wire [7:0] BLI_SCAN_OUT_01_out;
  wire [7:0] BLI_SCAN_OUT_02_out;
  wire [7:0] BLI_SCAN_OUT_03_out;
  wire [7:0] BLI_SCAN_OUT_04_out;
  wire [7:0] BLI_SCAN_OUT_05_out;
  wire [7:0] BLI_SCAN_OUT_06_out;
  wire [7:0] BLI_SCAN_OUT_07_out;
  wire [7:0] BLI_SCAN_OUT_08_out;
  wire [7:0] BLI_SCAN_OUT_09_out;
  wire [7:0] BLI_SCAN_OUT_10_out;
  wire [7:0] BLI_SCAN_OUT_11_out;
  wire [7:0] BLI_SCAN_OUT_12_out;
  wire [7:0] BLI_SCAN_OUT_13_out;
  wire [7:0] BLI_SCAN_OUT_14_out;
  wire [7:0] BLI_SCAN_OUT_15_out;
  wire [7:0] BLI_SCAN_OUT_16_out;
  wire [7:0] BLI_SCAN_OUT_17_out;
  wire [7:0] BLI_SCAN_OUT_18_out;
  wire [7:0] BLI_SCAN_OUT_19_out;
  wire [7:0] BLI_SCAN_OUT_20_out;
  wire [7:0] BLI_SCAN_OUT_21_out;
  wire [7:0] BLI_SCAN_OUT_22_out;
  wire [7:0] BLI_SCAN_OUT_23_out;
  wire [7:0] BLI_SCAN_OUT_24_out;
  wire [7:0] BLI_SCAN_OUT_25_out;
  wire [7:0] BLI_SCAN_OUT_26_out;
  wire [7:0] BLI_SCAN_OUT_27_out;
  wire [7:0] BLI_SCAN_OUT_28_out;
  wire [7:0] BLI_SCAN_OUT_29_out;
  wire [7:0] BLI_SCAN_OUT_30_out;
  wire [7:0] BLI_SCAN_OUT_31_out;

  wire ANALOG_HBM_SEL_00_in;
  wire ANALOG_HBM_SEL_01_in;
  wire APB_0_PCLK_in;
  wire APB_0_PENABLE_in;
  wire APB_0_PRESET_N_in;
  wire APB_0_PSEL_in;
  wire APB_0_PWRITE_in;
  wire APB_1_PCLK_in;
  wire APB_1_PENABLE_in;
  wire APB_1_PRESET_N_in;
  wire APB_1_PSEL_in;
  wire APB_1_PWRITE_in;
  wire AXI_00_ACLK_in;
  wire AXI_00_ARESET_N_in;
  wire AXI_00_ARVALID_in;
  wire AXI_00_AWVALID_in;
  wire AXI_00_BREADY_in;
  wire AXI_00_DFI_LP_PWR_X_REQ_in;
  wire AXI_00_RREADY_in;
  wire AXI_00_WLAST_in;
  wire AXI_00_WVALID_in;
  wire AXI_01_ACLK_in;
  wire AXI_01_ARESET_N_in;
  wire AXI_01_ARVALID_in;
  wire AXI_01_AWVALID_in;
  wire AXI_01_BREADY_in;
  wire AXI_01_DFI_LP_PWR_X_REQ_in;
  wire AXI_01_RREADY_in;
  wire AXI_01_WLAST_in;
  wire AXI_01_WVALID_in;
  wire AXI_02_ACLK_in;
  wire AXI_02_ARESET_N_in;
  wire AXI_02_ARVALID_in;
  wire AXI_02_AWVALID_in;
  wire AXI_02_BREADY_in;
  wire AXI_02_DFI_LP_PWR_X_REQ_in;
  wire AXI_02_RREADY_in;
  wire AXI_02_WLAST_in;
  wire AXI_02_WVALID_in;
  wire AXI_03_ACLK_in;
  wire AXI_03_ARESET_N_in;
  wire AXI_03_ARVALID_in;
  wire AXI_03_AWVALID_in;
  wire AXI_03_BREADY_in;
  wire AXI_03_DFI_LP_PWR_X_REQ_in;
  wire AXI_03_RREADY_in;
  wire AXI_03_WLAST_in;
  wire AXI_03_WVALID_in;
  wire AXI_04_ACLK_in;
  wire AXI_04_ARESET_N_in;
  wire AXI_04_ARVALID_in;
  wire AXI_04_AWVALID_in;
  wire AXI_04_BREADY_in;
  wire AXI_04_DFI_LP_PWR_X_REQ_in;
  wire AXI_04_RREADY_in;
  wire AXI_04_WLAST_in;
  wire AXI_04_WVALID_in;
  wire AXI_05_ACLK_in;
  wire AXI_05_ARESET_N_in;
  wire AXI_05_ARVALID_in;
  wire AXI_05_AWVALID_in;
  wire AXI_05_BREADY_in;
  wire AXI_05_DFI_LP_PWR_X_REQ_in;
  wire AXI_05_RREADY_in;
  wire AXI_05_WLAST_in;
  wire AXI_05_WVALID_in;
  wire AXI_06_ACLK_in;
  wire AXI_06_ARESET_N_in;
  wire AXI_06_ARVALID_in;
  wire AXI_06_AWVALID_in;
  wire AXI_06_BREADY_in;
  wire AXI_06_DFI_LP_PWR_X_REQ_in;
  wire AXI_06_RREADY_in;
  wire AXI_06_WLAST_in;
  wire AXI_06_WVALID_in;
  wire AXI_07_ACLK_in;
  wire AXI_07_ARESET_N_in;
  wire AXI_07_ARVALID_in;
  wire AXI_07_AWVALID_in;
  wire AXI_07_BREADY_in;
  wire AXI_07_DFI_LP_PWR_X_REQ_in;
  wire AXI_07_RREADY_in;
  wire AXI_07_WLAST_in;
  wire AXI_07_WVALID_in;
  wire AXI_08_ACLK_in;
  wire AXI_08_ARESET_N_in;
  wire AXI_08_ARVALID_in;
  wire AXI_08_AWVALID_in;
  wire AXI_08_BREADY_in;
  wire AXI_08_DFI_LP_PWR_X_REQ_in;
  wire AXI_08_RREADY_in;
  wire AXI_08_WLAST_in;
  wire AXI_08_WVALID_in;
  wire AXI_09_ACLK_in;
  wire AXI_09_ARESET_N_in;
  wire AXI_09_ARVALID_in;
  wire AXI_09_AWVALID_in;
  wire AXI_09_BREADY_in;
  wire AXI_09_DFI_LP_PWR_X_REQ_in;
  wire AXI_09_RREADY_in;
  wire AXI_09_WLAST_in;
  wire AXI_09_WVALID_in;
  wire AXI_10_ACLK_in;
  wire AXI_10_ARESET_N_in;
  wire AXI_10_ARVALID_in;
  wire AXI_10_AWVALID_in;
  wire AXI_10_BREADY_in;
  wire AXI_10_DFI_LP_PWR_X_REQ_in;
  wire AXI_10_RREADY_in;
  wire AXI_10_WLAST_in;
  wire AXI_10_WVALID_in;
  wire AXI_11_ACLK_in;
  wire AXI_11_ARESET_N_in;
  wire AXI_11_ARVALID_in;
  wire AXI_11_AWVALID_in;
  wire AXI_11_BREADY_in;
  wire AXI_11_DFI_LP_PWR_X_REQ_in;
  wire AXI_11_RREADY_in;
  wire AXI_11_WLAST_in;
  wire AXI_11_WVALID_in;
  wire AXI_12_ACLK_in;
  wire AXI_12_ARESET_N_in;
  wire AXI_12_ARVALID_in;
  wire AXI_12_AWVALID_in;
  wire AXI_12_BREADY_in;
  wire AXI_12_DFI_LP_PWR_X_REQ_in;
  wire AXI_12_RREADY_in;
  wire AXI_12_WLAST_in;
  wire AXI_12_WVALID_in;
  wire AXI_13_ACLK_in;
  wire AXI_13_ARESET_N_in;
  wire AXI_13_ARVALID_in;
  wire AXI_13_AWVALID_in;
  wire AXI_13_BREADY_in;
  wire AXI_13_DFI_LP_PWR_X_REQ_in;
  wire AXI_13_RREADY_in;
  wire AXI_13_WLAST_in;
  wire AXI_13_WVALID_in;
  wire AXI_14_ACLK_in;
  wire AXI_14_ARESET_N_in;
  wire AXI_14_ARVALID_in;
  wire AXI_14_AWVALID_in;
  wire AXI_14_BREADY_in;
  wire AXI_14_DFI_LP_PWR_X_REQ_in;
  wire AXI_14_RREADY_in;
  wire AXI_14_WLAST_in;
  wire AXI_14_WVALID_in;
  wire AXI_15_ACLK_in;
  wire AXI_15_ARESET_N_in;
  wire AXI_15_ARVALID_in;
  wire AXI_15_AWVALID_in;
  wire AXI_15_BREADY_in;
  wire AXI_15_DFI_LP_PWR_X_REQ_in;
  wire AXI_15_RREADY_in;
  wire AXI_15_WLAST_in;
  wire AXI_15_WVALID_in;
  wire AXI_16_ACLK_in;
  wire AXI_16_ARESET_N_in;
  wire AXI_16_ARVALID_in;
  wire AXI_16_AWVALID_in;
  wire AXI_16_BREADY_in;
  wire AXI_16_DFI_LP_PWR_X_REQ_in;
  wire AXI_16_RREADY_in;
  wire AXI_16_WLAST_in;
  wire AXI_16_WVALID_in;
  wire AXI_17_ACLK_in;
  wire AXI_17_ARESET_N_in;
  wire AXI_17_ARVALID_in;
  wire AXI_17_AWVALID_in;
  wire AXI_17_BREADY_in;
  wire AXI_17_DFI_LP_PWR_X_REQ_in;
  wire AXI_17_RREADY_in;
  wire AXI_17_WLAST_in;
  wire AXI_17_WVALID_in;
  wire AXI_18_ACLK_in;
  wire AXI_18_ARESET_N_in;
  wire AXI_18_ARVALID_in;
  wire AXI_18_AWVALID_in;
  wire AXI_18_BREADY_in;
  wire AXI_18_DFI_LP_PWR_X_REQ_in;
  wire AXI_18_RREADY_in;
  wire AXI_18_WLAST_in;
  wire AXI_18_WVALID_in;
  wire AXI_19_ACLK_in;
  wire AXI_19_ARESET_N_in;
  wire AXI_19_ARVALID_in;
  wire AXI_19_AWVALID_in;
  wire AXI_19_BREADY_in;
  wire AXI_19_DFI_LP_PWR_X_REQ_in;
  wire AXI_19_RREADY_in;
  wire AXI_19_WLAST_in;
  wire AXI_19_WVALID_in;
  wire AXI_20_ACLK_in;
  wire AXI_20_ARESET_N_in;
  wire AXI_20_ARVALID_in;
  wire AXI_20_AWVALID_in;
  wire AXI_20_BREADY_in;
  wire AXI_20_DFI_LP_PWR_X_REQ_in;
  wire AXI_20_RREADY_in;
  wire AXI_20_WLAST_in;
  wire AXI_20_WVALID_in;
  wire AXI_21_ACLK_in;
  wire AXI_21_ARESET_N_in;
  wire AXI_21_ARVALID_in;
  wire AXI_21_AWVALID_in;
  wire AXI_21_BREADY_in;
  wire AXI_21_DFI_LP_PWR_X_REQ_in;
  wire AXI_21_RREADY_in;
  wire AXI_21_WLAST_in;
  wire AXI_21_WVALID_in;
  wire AXI_22_ACLK_in;
  wire AXI_22_ARESET_N_in;
  wire AXI_22_ARVALID_in;
  wire AXI_22_AWVALID_in;
  wire AXI_22_BREADY_in;
  wire AXI_22_DFI_LP_PWR_X_REQ_in;
  wire AXI_22_RREADY_in;
  wire AXI_22_WLAST_in;
  wire AXI_22_WVALID_in;
  wire AXI_23_ACLK_in;
  wire AXI_23_ARESET_N_in;
  wire AXI_23_ARVALID_in;
  wire AXI_23_AWVALID_in;
  wire AXI_23_BREADY_in;
  wire AXI_23_DFI_LP_PWR_X_REQ_in;
  wire AXI_23_RREADY_in;
  wire AXI_23_WLAST_in;
  wire AXI_23_WVALID_in;
  wire AXI_24_ACLK_in;
  wire AXI_24_ARESET_N_in;
  wire AXI_24_ARVALID_in;
  wire AXI_24_AWVALID_in;
  wire AXI_24_BREADY_in;
  wire AXI_24_DFI_LP_PWR_X_REQ_in;
  wire AXI_24_RREADY_in;
  wire AXI_24_WLAST_in;
  wire AXI_24_WVALID_in;
  wire AXI_25_ACLK_in;
  wire AXI_25_ARESET_N_in;
  wire AXI_25_ARVALID_in;
  wire AXI_25_AWVALID_in;
  wire AXI_25_BREADY_in;
  wire AXI_25_DFI_LP_PWR_X_REQ_in;
  wire AXI_25_RREADY_in;
  wire AXI_25_WLAST_in;
  wire AXI_25_WVALID_in;
  wire AXI_26_ACLK_in;
  wire AXI_26_ARESET_N_in;
  wire AXI_26_ARVALID_in;
  wire AXI_26_AWVALID_in;
  wire AXI_26_BREADY_in;
  wire AXI_26_DFI_LP_PWR_X_REQ_in;
  wire AXI_26_RREADY_in;
  wire AXI_26_WLAST_in;
  wire AXI_26_WVALID_in;
  wire AXI_27_ACLK_in;
  wire AXI_27_ARESET_N_in;
  wire AXI_27_ARVALID_in;
  wire AXI_27_AWVALID_in;
  wire AXI_27_BREADY_in;
  wire AXI_27_DFI_LP_PWR_X_REQ_in;
  wire AXI_27_RREADY_in;
  wire AXI_27_WLAST_in;
  wire AXI_27_WVALID_in;
  wire AXI_28_ACLK_in;
  wire AXI_28_ARESET_N_in;
  wire AXI_28_ARVALID_in;
  wire AXI_28_AWVALID_in;
  wire AXI_28_BREADY_in;
  wire AXI_28_DFI_LP_PWR_X_REQ_in;
  wire AXI_28_RREADY_in;
  wire AXI_28_WLAST_in;
  wire AXI_28_WVALID_in;
  wire AXI_29_ACLK_in;
  wire AXI_29_ARESET_N_in;
  wire AXI_29_ARVALID_in;
  wire AXI_29_AWVALID_in;
  wire AXI_29_BREADY_in;
  wire AXI_29_DFI_LP_PWR_X_REQ_in;
  wire AXI_29_RREADY_in;
  wire AXI_29_WLAST_in;
  wire AXI_29_WVALID_in;
  wire AXI_30_ACLK_in;
  wire AXI_30_ARESET_N_in;
  wire AXI_30_ARVALID_in;
  wire AXI_30_AWVALID_in;
  wire AXI_30_BREADY_in;
  wire AXI_30_DFI_LP_PWR_X_REQ_in;
  wire AXI_30_RREADY_in;
  wire AXI_30_WLAST_in;
  wire AXI_30_WVALID_in;
  wire AXI_31_ACLK_in;
  wire AXI_31_ARESET_N_in;
  wire AXI_31_ARVALID_in;
  wire AXI_31_AWVALID_in;
  wire AXI_31_BREADY_in;
  wire AXI_31_DFI_LP_PWR_X_REQ_in;
  wire AXI_31_RREADY_in;
  wire AXI_31_WLAST_in;
  wire AXI_31_WVALID_in;
  wire BLI_SCAN_ENABLE_00_in;
  wire BLI_SCAN_ENABLE_01_in;
  wire BLI_SCAN_ENABLE_02_in;
  wire BLI_SCAN_ENABLE_03_in;
  wire BLI_SCAN_ENABLE_04_in;
  wire BLI_SCAN_ENABLE_05_in;
  wire BLI_SCAN_ENABLE_06_in;
  wire BLI_SCAN_ENABLE_07_in;
  wire BLI_SCAN_ENABLE_08_in;
  wire BLI_SCAN_ENABLE_09_in;
  wire BLI_SCAN_ENABLE_10_in;
  wire BLI_SCAN_ENABLE_11_in;
  wire BLI_SCAN_ENABLE_12_in;
  wire BLI_SCAN_ENABLE_13_in;
  wire BLI_SCAN_ENABLE_14_in;
  wire BLI_SCAN_ENABLE_15_in;
  wire BLI_SCAN_ENABLE_16_in;
  wire BLI_SCAN_ENABLE_17_in;
  wire BLI_SCAN_ENABLE_18_in;
  wire BLI_SCAN_ENABLE_19_in;
  wire BLI_SCAN_ENABLE_20_in;
  wire BLI_SCAN_ENABLE_21_in;
  wire BLI_SCAN_ENABLE_22_in;
  wire BLI_SCAN_ENABLE_23_in;
  wire BLI_SCAN_ENABLE_24_in;
  wire BLI_SCAN_ENABLE_25_in;
  wire BLI_SCAN_ENABLE_26_in;
  wire BLI_SCAN_ENABLE_27_in;
  wire BLI_SCAN_ENABLE_28_in;
  wire BLI_SCAN_ENABLE_29_in;
  wire BLI_SCAN_ENABLE_30_in;
  wire BLI_SCAN_ENABLE_31_in;
  wire BSCAN_DRCK_0_in;
  wire BSCAN_DRCK_1_in;
  wire BSCAN_TCK_0_in;
  wire BSCAN_TCK_1_in;
  wire DLL_SCAN_CK_00_in;
  wire DLL_SCAN_CK_01_in;
  wire DLL_SCAN_ENABLE_00_in;
  wire DLL_SCAN_ENABLE_01_in;
  wire DLL_SCAN_MODE_00_in;
  wire DLL_SCAN_MODE_01_in;
  wire DLL_SCAN_RST_N_00_in;
  wire DLL_SCAN_RST_N_01_in;
  wire HBM_REF_CLK_0_in;
  wire HBM_REF_CLK_1_in;
  wire IO_SCAN_CK_00_in;
  wire IO_SCAN_CK_01_in;
  wire IO_SCAN_ENABLE_00_in;
  wire IO_SCAN_ENABLE_01_in;
  wire IO_SCAN_MODE_00_in;
  wire IO_SCAN_MODE_01_in;
  wire IO_SCAN_RST_N_00_in;
  wire IO_SCAN_RST_N_01_in;
  wire MBIST_EN_00_in;
  wire MBIST_EN_01_in;
  wire MBIST_EN_02_in;
  wire MBIST_EN_03_in;
  wire MBIST_EN_04_in;
  wire MBIST_EN_05_in;
  wire MBIST_EN_06_in;
  wire MBIST_EN_07_in;
  wire MBIST_EN_08_in;
  wire MBIST_EN_09_in;
  wire MBIST_EN_10_in;
  wire MBIST_EN_11_in;
  wire MBIST_EN_12_in;
  wire MBIST_EN_13_in;
  wire MBIST_EN_14_in;
  wire MBIST_EN_15_in;
  wire MC_SCAN_CK_00_in;
  wire MC_SCAN_CK_01_in;
  wire MC_SCAN_CK_02_in;
  wire MC_SCAN_CK_03_in;
  wire MC_SCAN_CK_04_in;
  wire MC_SCAN_CK_05_in;
  wire MC_SCAN_CK_06_in;
  wire MC_SCAN_CK_07_in;
  wire MC_SCAN_CK_08_in;
  wire MC_SCAN_CK_09_in;
  wire MC_SCAN_CK_10_in;
  wire MC_SCAN_CK_11_in;
  wire MC_SCAN_CK_12_in;
  wire MC_SCAN_CK_13_in;
  wire MC_SCAN_CK_14_in;
  wire MC_SCAN_CK_15_in;
  wire MC_SCAN_ENABLE_00_in;
  wire MC_SCAN_ENABLE_01_in;
  wire MC_SCAN_ENABLE_02_in;
  wire MC_SCAN_ENABLE_03_in;
  wire MC_SCAN_ENABLE_04_in;
  wire MC_SCAN_ENABLE_05_in;
  wire MC_SCAN_ENABLE_06_in;
  wire MC_SCAN_ENABLE_07_in;
  wire MC_SCAN_ENABLE_08_in;
  wire MC_SCAN_ENABLE_09_in;
  wire MC_SCAN_ENABLE_10_in;
  wire MC_SCAN_ENABLE_11_in;
  wire MC_SCAN_ENABLE_12_in;
  wire MC_SCAN_ENABLE_13_in;
  wire MC_SCAN_ENABLE_14_in;
  wire MC_SCAN_ENABLE_15_in;
  wire MC_SCAN_MODE_00_in;
  wire MC_SCAN_MODE_01_in;
  wire MC_SCAN_MODE_02_in;
  wire MC_SCAN_MODE_03_in;
  wire MC_SCAN_MODE_04_in;
  wire MC_SCAN_MODE_05_in;
  wire MC_SCAN_MODE_06_in;
  wire MC_SCAN_MODE_07_in;
  wire MC_SCAN_MODE_08_in;
  wire MC_SCAN_MODE_09_in;
  wire MC_SCAN_MODE_10_in;
  wire MC_SCAN_MODE_11_in;
  wire MC_SCAN_MODE_12_in;
  wire MC_SCAN_MODE_13_in;
  wire MC_SCAN_MODE_14_in;
  wire MC_SCAN_MODE_15_in;
  wire MC_SCAN_RST_N_00_in;
  wire MC_SCAN_RST_N_01_in;
  wire MC_SCAN_RST_N_02_in;
  wire MC_SCAN_RST_N_03_in;
  wire MC_SCAN_RST_N_04_in;
  wire MC_SCAN_RST_N_05_in;
  wire MC_SCAN_RST_N_06_in;
  wire MC_SCAN_RST_N_07_in;
  wire MC_SCAN_RST_N_08_in;
  wire MC_SCAN_RST_N_09_in;
  wire MC_SCAN_RST_N_10_in;
  wire MC_SCAN_RST_N_11_in;
  wire MC_SCAN_RST_N_12_in;
  wire MC_SCAN_RST_N_13_in;
  wire MC_SCAN_RST_N_14_in;
  wire MC_SCAN_RST_N_15_in;
  wire PHY_SCAN_CK_00_in;
  wire PHY_SCAN_CK_01_in;
  wire PHY_SCAN_ENABLE_00_in;
  wire PHY_SCAN_ENABLE_01_in;
  wire PHY_SCAN_MODE_00_in;
  wire PHY_SCAN_MODE_01_in;
  wire PHY_SCAN_RST_N_00_in;
  wire PHY_SCAN_RST_N_01_in;
  wire SW_SCAN_CK_00_in;
  wire SW_SCAN_CK_01_in;
  wire SW_SCAN_ENABLE_00_in;
  wire SW_SCAN_ENABLE_01_in;
  wire SW_SCAN_MODE_00_in;
  wire SW_SCAN_MODE_01_in;
  wire SW_SCAN_RST_N_00_in;
  wire SW_SCAN_RST_N_01_in;
  wire [1:0] AXI_00_ARBURST_in;
  wire [1:0] AXI_00_AWBURST_in;
  wire [1:0] AXI_01_ARBURST_in;
  wire [1:0] AXI_01_AWBURST_in;
  wire [1:0] AXI_02_ARBURST_in;
  wire [1:0] AXI_02_AWBURST_in;
  wire [1:0] AXI_03_ARBURST_in;
  wire [1:0] AXI_03_AWBURST_in;
  wire [1:0] AXI_04_ARBURST_in;
  wire [1:0] AXI_04_AWBURST_in;
  wire [1:0] AXI_05_ARBURST_in;
  wire [1:0] AXI_05_AWBURST_in;
  wire [1:0] AXI_06_ARBURST_in;
  wire [1:0] AXI_06_AWBURST_in;
  wire [1:0] AXI_07_ARBURST_in;
  wire [1:0] AXI_07_AWBURST_in;
  wire [1:0] AXI_08_ARBURST_in;
  wire [1:0] AXI_08_AWBURST_in;
  wire [1:0] AXI_09_ARBURST_in;
  wire [1:0] AXI_09_AWBURST_in;
  wire [1:0] AXI_10_ARBURST_in;
  wire [1:0] AXI_10_AWBURST_in;
  wire [1:0] AXI_11_ARBURST_in;
  wire [1:0] AXI_11_AWBURST_in;
  wire [1:0] AXI_12_ARBURST_in;
  wire [1:0] AXI_12_AWBURST_in;
  wire [1:0] AXI_13_ARBURST_in;
  wire [1:0] AXI_13_AWBURST_in;
  wire [1:0] AXI_14_ARBURST_in;
  wire [1:0] AXI_14_AWBURST_in;
  wire [1:0] AXI_15_ARBURST_in;
  wire [1:0] AXI_15_AWBURST_in;
  wire [1:0] AXI_16_ARBURST_in;
  wire [1:0] AXI_16_AWBURST_in;
  wire [1:0] AXI_17_ARBURST_in;
  wire [1:0] AXI_17_AWBURST_in;
  wire [1:0] AXI_18_ARBURST_in;
  wire [1:0] AXI_18_AWBURST_in;
  wire [1:0] AXI_19_ARBURST_in;
  wire [1:0] AXI_19_AWBURST_in;
  wire [1:0] AXI_20_ARBURST_in;
  wire [1:0] AXI_20_AWBURST_in;
  wire [1:0] AXI_21_ARBURST_in;
  wire [1:0] AXI_21_AWBURST_in;
  wire [1:0] AXI_22_ARBURST_in;
  wire [1:0] AXI_22_AWBURST_in;
  wire [1:0] AXI_23_ARBURST_in;
  wire [1:0] AXI_23_AWBURST_in;
  wire [1:0] AXI_24_ARBURST_in;
  wire [1:0] AXI_24_AWBURST_in;
  wire [1:0] AXI_25_ARBURST_in;
  wire [1:0] AXI_25_AWBURST_in;
  wire [1:0] AXI_26_ARBURST_in;
  wire [1:0] AXI_26_AWBURST_in;
  wire [1:0] AXI_27_ARBURST_in;
  wire [1:0] AXI_27_AWBURST_in;
  wire [1:0] AXI_28_ARBURST_in;
  wire [1:0] AXI_28_AWBURST_in;
  wire [1:0] AXI_29_ARBURST_in;
  wire [1:0] AXI_29_AWBURST_in;
  wire [1:0] AXI_30_ARBURST_in;
  wire [1:0] AXI_30_AWBURST_in;
  wire [1:0] AXI_31_ARBURST_in;
  wire [1:0] AXI_31_AWBURST_in;
  wire [1:0] DLL_SCAN_IN_00_in;
  wire [1:0] DLL_SCAN_IN_01_in;
  wire [1:0] IO_SCAN_IN_00_in;
  wire [1:0] IO_SCAN_IN_01_in;
  wire [1:0] MC_SCAN_IN_00_in;
  wire [1:0] MC_SCAN_IN_01_in;
  wire [1:0] MC_SCAN_IN_02_in;
  wire [1:0] MC_SCAN_IN_03_in;
  wire [1:0] MC_SCAN_IN_04_in;
  wire [1:0] MC_SCAN_IN_05_in;
  wire [1:0] MC_SCAN_IN_06_in;
  wire [1:0] MC_SCAN_IN_07_in;
  wire [1:0] MC_SCAN_IN_08_in;
  wire [1:0] MC_SCAN_IN_09_in;
  wire [1:0] MC_SCAN_IN_10_in;
  wire [1:0] MC_SCAN_IN_11_in;
  wire [1:0] MC_SCAN_IN_12_in;
  wire [1:0] MC_SCAN_IN_13_in;
  wire [1:0] MC_SCAN_IN_14_in;
  wire [1:0] MC_SCAN_IN_15_in;
  wire [1:0] PHY_SCAN_IN_00_in;
  wire [1:0] PHY_SCAN_IN_01_in;
  wire [1:0] SW_SCAN_IN_00_in;
  wire [1:0] SW_SCAN_IN_01_in;
  wire [1:0] SW_SCAN_IN_02_in;
  wire [1:0] SW_SCAN_IN_03_in;
  wire [1:0] SW_SCAN_IN_04_in;
  wire [1:0] SW_SCAN_IN_05_in;
  wire [1:0] SW_SCAN_IN_06_in;
  wire [1:0] SW_SCAN_IN_07_in;
  wire [21:0] APB_0_PADDR_in;
  wire [21:0] APB_1_PADDR_in;
  wire [23:0] DBG_IN_00_in;
  wire [23:0] DBG_IN_01_in;
  wire [23:0] DBG_IN_02_in;
  wire [23:0] DBG_IN_03_in;
  wire [23:0] DBG_IN_04_in;
  wire [23:0] DBG_IN_05_in;
  wire [23:0] DBG_IN_06_in;
  wire [23:0] DBG_IN_07_in;
  wire [23:0] DBG_IN_08_in;
  wire [23:0] DBG_IN_09_in;
  wire [23:0] DBG_IN_10_in;
  wire [23:0] DBG_IN_11_in;
  wire [23:0] DBG_IN_12_in;
  wire [23:0] DBG_IN_13_in;
  wire [23:0] DBG_IN_14_in;
  wire [23:0] DBG_IN_15_in;
  wire [23:0] DBG_IN_16_in;
  wire [23:0] DBG_IN_17_in;
  wire [23:0] DBG_IN_18_in;
  wire [23:0] DBG_IN_19_in;
  wire [23:0] DBG_IN_20_in;
  wire [23:0] DBG_IN_21_in;
  wire [23:0] DBG_IN_22_in;
  wire [23:0] DBG_IN_23_in;
  wire [23:0] DBG_IN_24_in;
  wire [23:0] DBG_IN_25_in;
  wire [23:0] DBG_IN_26_in;
  wire [23:0] DBG_IN_27_in;
  wire [23:0] DBG_IN_28_in;
  wire [23:0] DBG_IN_29_in;
  wire [23:0] DBG_IN_30_in;
  wire [23:0] DBG_IN_31_in;
  wire [255:0] AXI_00_WDATA_in;
  wire [255:0] AXI_01_WDATA_in;
  wire [255:0] AXI_02_WDATA_in;
  wire [255:0] AXI_03_WDATA_in;
  wire [255:0] AXI_04_WDATA_in;
  wire [255:0] AXI_05_WDATA_in;
  wire [255:0] AXI_06_WDATA_in;
  wire [255:0] AXI_07_WDATA_in;
  wire [255:0] AXI_08_WDATA_in;
  wire [255:0] AXI_09_WDATA_in;
  wire [255:0] AXI_10_WDATA_in;
  wire [255:0] AXI_11_WDATA_in;
  wire [255:0] AXI_12_WDATA_in;
  wire [255:0] AXI_13_WDATA_in;
  wire [255:0] AXI_14_WDATA_in;
  wire [255:0] AXI_15_WDATA_in;
  wire [255:0] AXI_16_WDATA_in;
  wire [255:0] AXI_17_WDATA_in;
  wire [255:0] AXI_18_WDATA_in;
  wire [255:0] AXI_19_WDATA_in;
  wire [255:0] AXI_20_WDATA_in;
  wire [255:0] AXI_21_WDATA_in;
  wire [255:0] AXI_22_WDATA_in;
  wire [255:0] AXI_23_WDATA_in;
  wire [255:0] AXI_24_WDATA_in;
  wire [255:0] AXI_25_WDATA_in;
  wire [255:0] AXI_26_WDATA_in;
  wire [255:0] AXI_27_WDATA_in;
  wire [255:0] AXI_28_WDATA_in;
  wire [255:0] AXI_29_WDATA_in;
  wire [255:0] AXI_30_WDATA_in;
  wire [255:0] AXI_31_WDATA_in;
  wire [2:0] AXI_00_ARSIZE_in;
  wire [2:0] AXI_00_AWSIZE_in;
  wire [2:0] AXI_01_ARSIZE_in;
  wire [2:0] AXI_01_AWSIZE_in;
  wire [2:0] AXI_02_ARSIZE_in;
  wire [2:0] AXI_02_AWSIZE_in;
  wire [2:0] AXI_03_ARSIZE_in;
  wire [2:0] AXI_03_AWSIZE_in;
  wire [2:0] AXI_04_ARSIZE_in;
  wire [2:0] AXI_04_AWSIZE_in;
  wire [2:0] AXI_05_ARSIZE_in;
  wire [2:0] AXI_05_AWSIZE_in;
  wire [2:0] AXI_06_ARSIZE_in;
  wire [2:0] AXI_06_AWSIZE_in;
  wire [2:0] AXI_07_ARSIZE_in;
  wire [2:0] AXI_07_AWSIZE_in;
  wire [2:0] AXI_08_ARSIZE_in;
  wire [2:0] AXI_08_AWSIZE_in;
  wire [2:0] AXI_09_ARSIZE_in;
  wire [2:0] AXI_09_AWSIZE_in;
  wire [2:0] AXI_10_ARSIZE_in;
  wire [2:0] AXI_10_AWSIZE_in;
  wire [2:0] AXI_11_ARSIZE_in;
  wire [2:0] AXI_11_AWSIZE_in;
  wire [2:0] AXI_12_ARSIZE_in;
  wire [2:0] AXI_12_AWSIZE_in;
  wire [2:0] AXI_13_ARSIZE_in;
  wire [2:0] AXI_13_AWSIZE_in;
  wire [2:0] AXI_14_ARSIZE_in;
  wire [2:0] AXI_14_AWSIZE_in;
  wire [2:0] AXI_15_ARSIZE_in;
  wire [2:0] AXI_15_AWSIZE_in;
  wire [2:0] AXI_16_ARSIZE_in;
  wire [2:0] AXI_16_AWSIZE_in;
  wire [2:0] AXI_17_ARSIZE_in;
  wire [2:0] AXI_17_AWSIZE_in;
  wire [2:0] AXI_18_ARSIZE_in;
  wire [2:0] AXI_18_AWSIZE_in;
  wire [2:0] AXI_19_ARSIZE_in;
  wire [2:0] AXI_19_AWSIZE_in;
  wire [2:0] AXI_20_ARSIZE_in;
  wire [2:0] AXI_20_AWSIZE_in;
  wire [2:0] AXI_21_ARSIZE_in;
  wire [2:0] AXI_21_AWSIZE_in;
  wire [2:0] AXI_22_ARSIZE_in;
  wire [2:0] AXI_22_AWSIZE_in;
  wire [2:0] AXI_23_ARSIZE_in;
  wire [2:0] AXI_23_AWSIZE_in;
  wire [2:0] AXI_24_ARSIZE_in;
  wire [2:0] AXI_24_AWSIZE_in;
  wire [2:0] AXI_25_ARSIZE_in;
  wire [2:0] AXI_25_AWSIZE_in;
  wire [2:0] AXI_26_ARSIZE_in;
  wire [2:0] AXI_26_AWSIZE_in;
  wire [2:0] AXI_27_ARSIZE_in;
  wire [2:0] AXI_27_AWSIZE_in;
  wire [2:0] AXI_28_ARSIZE_in;
  wire [2:0] AXI_28_AWSIZE_in;
  wire [2:0] AXI_29_ARSIZE_in;
  wire [2:0] AXI_29_AWSIZE_in;
  wire [2:0] AXI_30_ARSIZE_in;
  wire [2:0] AXI_30_AWSIZE_in;
  wire [2:0] AXI_31_ARSIZE_in;
  wire [2:0] AXI_31_AWSIZE_in;
  wire [31:0] APB_0_PWDATA_in;
  wire [31:0] APB_1_PWDATA_in;
  wire [31:0] AXI_00_WDATA_PARITY_in;
  wire [31:0] AXI_00_WSTRB_in;
  wire [31:0] AXI_01_WDATA_PARITY_in;
  wire [31:0] AXI_01_WSTRB_in;
  wire [31:0] AXI_02_WDATA_PARITY_in;
  wire [31:0] AXI_02_WSTRB_in;
  wire [31:0] AXI_03_WDATA_PARITY_in;
  wire [31:0] AXI_03_WSTRB_in;
  wire [31:0] AXI_04_WDATA_PARITY_in;
  wire [31:0] AXI_04_WSTRB_in;
  wire [31:0] AXI_05_WDATA_PARITY_in;
  wire [31:0] AXI_05_WSTRB_in;
  wire [31:0] AXI_06_WDATA_PARITY_in;
  wire [31:0] AXI_06_WSTRB_in;
  wire [31:0] AXI_07_WDATA_PARITY_in;
  wire [31:0] AXI_07_WSTRB_in;
  wire [31:0] AXI_08_WDATA_PARITY_in;
  wire [31:0] AXI_08_WSTRB_in;
  wire [31:0] AXI_09_WDATA_PARITY_in;
  wire [31:0] AXI_09_WSTRB_in;
  wire [31:0] AXI_10_WDATA_PARITY_in;
  wire [31:0] AXI_10_WSTRB_in;
  wire [31:0] AXI_11_WDATA_PARITY_in;
  wire [31:0] AXI_11_WSTRB_in;
  wire [31:0] AXI_12_WDATA_PARITY_in;
  wire [31:0] AXI_12_WSTRB_in;
  wire [31:0] AXI_13_WDATA_PARITY_in;
  wire [31:0] AXI_13_WSTRB_in;
  wire [31:0] AXI_14_WDATA_PARITY_in;
  wire [31:0] AXI_14_WSTRB_in;
  wire [31:0] AXI_15_WDATA_PARITY_in;
  wire [31:0] AXI_15_WSTRB_in;
  wire [31:0] AXI_16_WDATA_PARITY_in;
  wire [31:0] AXI_16_WSTRB_in;
  wire [31:0] AXI_17_WDATA_PARITY_in;
  wire [31:0] AXI_17_WSTRB_in;
  wire [31:0] AXI_18_WDATA_PARITY_in;
  wire [31:0] AXI_18_WSTRB_in;
  wire [31:0] AXI_19_WDATA_PARITY_in;
  wire [31:0] AXI_19_WSTRB_in;
  wire [31:0] AXI_20_WDATA_PARITY_in;
  wire [31:0] AXI_20_WSTRB_in;
  wire [31:0] AXI_21_WDATA_PARITY_in;
  wire [31:0] AXI_21_WSTRB_in;
  wire [31:0] AXI_22_WDATA_PARITY_in;
  wire [31:0] AXI_22_WSTRB_in;
  wire [31:0] AXI_23_WDATA_PARITY_in;
  wire [31:0] AXI_23_WSTRB_in;
  wire [31:0] AXI_24_WDATA_PARITY_in;
  wire [31:0] AXI_24_WSTRB_in;
  wire [31:0] AXI_25_WDATA_PARITY_in;
  wire [31:0] AXI_25_WSTRB_in;
  wire [31:0] AXI_26_WDATA_PARITY_in;
  wire [31:0] AXI_26_WSTRB_in;
  wire [31:0] AXI_27_WDATA_PARITY_in;
  wire [31:0] AXI_27_WSTRB_in;
  wire [31:0] AXI_28_WDATA_PARITY_in;
  wire [31:0] AXI_28_WSTRB_in;
  wire [31:0] AXI_29_WDATA_PARITY_in;
  wire [31:0] AXI_29_WSTRB_in;
  wire [31:0] AXI_30_WDATA_PARITY_in;
  wire [31:0] AXI_30_WSTRB_in;
  wire [31:0] AXI_31_WDATA_PARITY_in;
  wire [31:0] AXI_31_WSTRB_in;
  wire [36:0] AXI_00_ARADDR_in;
  wire [36:0] AXI_00_AWADDR_in;
  wire [36:0] AXI_01_ARADDR_in;
  wire [36:0] AXI_01_AWADDR_in;
  wire [36:0] AXI_02_ARADDR_in;
  wire [36:0] AXI_02_AWADDR_in;
  wire [36:0] AXI_03_ARADDR_in;
  wire [36:0] AXI_03_AWADDR_in;
  wire [36:0] AXI_04_ARADDR_in;
  wire [36:0] AXI_04_AWADDR_in;
  wire [36:0] AXI_05_ARADDR_in;
  wire [36:0] AXI_05_AWADDR_in;
  wire [36:0] AXI_06_ARADDR_in;
  wire [36:0] AXI_06_AWADDR_in;
  wire [36:0] AXI_07_ARADDR_in;
  wire [36:0] AXI_07_AWADDR_in;
  wire [36:0] AXI_08_ARADDR_in;
  wire [36:0] AXI_08_AWADDR_in;
  wire [36:0] AXI_09_ARADDR_in;
  wire [36:0] AXI_09_AWADDR_in;
  wire [36:0] AXI_10_ARADDR_in;
  wire [36:0] AXI_10_AWADDR_in;
  wire [36:0] AXI_11_ARADDR_in;
  wire [36:0] AXI_11_AWADDR_in;
  wire [36:0] AXI_12_ARADDR_in;
  wire [36:0] AXI_12_AWADDR_in;
  wire [36:0] AXI_13_ARADDR_in;
  wire [36:0] AXI_13_AWADDR_in;
  wire [36:0] AXI_14_ARADDR_in;
  wire [36:0] AXI_14_AWADDR_in;
  wire [36:0] AXI_15_ARADDR_in;
  wire [36:0] AXI_15_AWADDR_in;
  wire [36:0] AXI_16_ARADDR_in;
  wire [36:0] AXI_16_AWADDR_in;
  wire [36:0] AXI_17_ARADDR_in;
  wire [36:0] AXI_17_AWADDR_in;
  wire [36:0] AXI_18_ARADDR_in;
  wire [36:0] AXI_18_AWADDR_in;
  wire [36:0] AXI_19_ARADDR_in;
  wire [36:0] AXI_19_AWADDR_in;
  wire [36:0] AXI_20_ARADDR_in;
  wire [36:0] AXI_20_AWADDR_in;
  wire [36:0] AXI_21_ARADDR_in;
  wire [36:0] AXI_21_AWADDR_in;
  wire [36:0] AXI_22_ARADDR_in;
  wire [36:0] AXI_22_AWADDR_in;
  wire [36:0] AXI_23_ARADDR_in;
  wire [36:0] AXI_23_AWADDR_in;
  wire [36:0] AXI_24_ARADDR_in;
  wire [36:0] AXI_24_AWADDR_in;
  wire [36:0] AXI_25_ARADDR_in;
  wire [36:0] AXI_25_AWADDR_in;
  wire [36:0] AXI_26_ARADDR_in;
  wire [36:0] AXI_26_AWADDR_in;
  wire [36:0] AXI_27_ARADDR_in;
  wire [36:0] AXI_27_AWADDR_in;
  wire [36:0] AXI_28_ARADDR_in;
  wire [36:0] AXI_28_AWADDR_in;
  wire [36:0] AXI_29_ARADDR_in;
  wire [36:0] AXI_29_AWADDR_in;
  wire [36:0] AXI_30_ARADDR_in;
  wire [36:0] AXI_30_AWADDR_in;
  wire [36:0] AXI_31_ARADDR_in;
  wire [36:0] AXI_31_AWADDR_in;
  wire [3:0] AXI_00_ARLEN_in;
  wire [3:0] AXI_00_AWLEN_in;
  wire [3:0] AXI_01_ARLEN_in;
  wire [3:0] AXI_01_AWLEN_in;
  wire [3:0] AXI_02_ARLEN_in;
  wire [3:0] AXI_02_AWLEN_in;
  wire [3:0] AXI_03_ARLEN_in;
  wire [3:0] AXI_03_AWLEN_in;
  wire [3:0] AXI_04_ARLEN_in;
  wire [3:0] AXI_04_AWLEN_in;
  wire [3:0] AXI_05_ARLEN_in;
  wire [3:0] AXI_05_AWLEN_in;
  wire [3:0] AXI_06_ARLEN_in;
  wire [3:0] AXI_06_AWLEN_in;
  wire [3:0] AXI_07_ARLEN_in;
  wire [3:0] AXI_07_AWLEN_in;
  wire [3:0] AXI_08_ARLEN_in;
  wire [3:0] AXI_08_AWLEN_in;
  wire [3:0] AXI_09_ARLEN_in;
  wire [3:0] AXI_09_AWLEN_in;
  wire [3:0] AXI_10_ARLEN_in;
  wire [3:0] AXI_10_AWLEN_in;
  wire [3:0] AXI_11_ARLEN_in;
  wire [3:0] AXI_11_AWLEN_in;
  wire [3:0] AXI_12_ARLEN_in;
  wire [3:0] AXI_12_AWLEN_in;
  wire [3:0] AXI_13_ARLEN_in;
  wire [3:0] AXI_13_AWLEN_in;
  wire [3:0] AXI_14_ARLEN_in;
  wire [3:0] AXI_14_AWLEN_in;
  wire [3:0] AXI_15_ARLEN_in;
  wire [3:0] AXI_15_AWLEN_in;
  wire [3:0] AXI_16_ARLEN_in;
  wire [3:0] AXI_16_AWLEN_in;
  wire [3:0] AXI_17_ARLEN_in;
  wire [3:0] AXI_17_AWLEN_in;
  wire [3:0] AXI_18_ARLEN_in;
  wire [3:0] AXI_18_AWLEN_in;
  wire [3:0] AXI_19_ARLEN_in;
  wire [3:0] AXI_19_AWLEN_in;
  wire [3:0] AXI_20_ARLEN_in;
  wire [3:0] AXI_20_AWLEN_in;
  wire [3:0] AXI_21_ARLEN_in;
  wire [3:0] AXI_21_AWLEN_in;
  wire [3:0] AXI_22_ARLEN_in;
  wire [3:0] AXI_22_AWLEN_in;
  wire [3:0] AXI_23_ARLEN_in;
  wire [3:0] AXI_23_AWLEN_in;
  wire [3:0] AXI_24_ARLEN_in;
  wire [3:0] AXI_24_AWLEN_in;
  wire [3:0] AXI_25_ARLEN_in;
  wire [3:0] AXI_25_AWLEN_in;
  wire [3:0] AXI_26_ARLEN_in;
  wire [3:0] AXI_26_AWLEN_in;
  wire [3:0] AXI_27_ARLEN_in;
  wire [3:0] AXI_27_AWLEN_in;
  wire [3:0] AXI_28_ARLEN_in;
  wire [3:0] AXI_28_AWLEN_in;
  wire [3:0] AXI_29_ARLEN_in;
  wire [3:0] AXI_29_AWLEN_in;
  wire [3:0] AXI_30_ARLEN_in;
  wire [3:0] AXI_30_AWLEN_in;
  wire [3:0] AXI_31_ARLEN_in;
  wire [3:0] AXI_31_AWLEN_in;
  wire [5:0] AXI_00_ARID_in;
  wire [5:0] AXI_00_AWID_in;
  wire [5:0] AXI_01_ARID_in;
  wire [5:0] AXI_01_AWID_in;
  wire [5:0] AXI_02_ARID_in;
  wire [5:0] AXI_02_AWID_in;
  wire [5:0] AXI_03_ARID_in;
  wire [5:0] AXI_03_AWID_in;
  wire [5:0] AXI_04_ARID_in;
  wire [5:0] AXI_04_AWID_in;
  wire [5:0] AXI_05_ARID_in;
  wire [5:0] AXI_05_AWID_in;
  wire [5:0] AXI_06_ARID_in;
  wire [5:0] AXI_06_AWID_in;
  wire [5:0] AXI_07_ARID_in;
  wire [5:0] AXI_07_AWID_in;
  wire [5:0] AXI_08_ARID_in;
  wire [5:0] AXI_08_AWID_in;
  wire [5:0] AXI_09_ARID_in;
  wire [5:0] AXI_09_AWID_in;
  wire [5:0] AXI_10_ARID_in;
  wire [5:0] AXI_10_AWID_in;
  wire [5:0] AXI_11_ARID_in;
  wire [5:0] AXI_11_AWID_in;
  wire [5:0] AXI_12_ARID_in;
  wire [5:0] AXI_12_AWID_in;
  wire [5:0] AXI_13_ARID_in;
  wire [5:0] AXI_13_AWID_in;
  wire [5:0] AXI_14_ARID_in;
  wire [5:0] AXI_14_AWID_in;
  wire [5:0] AXI_15_ARID_in;
  wire [5:0] AXI_15_AWID_in;
  wire [5:0] AXI_16_ARID_in;
  wire [5:0] AXI_16_AWID_in;
  wire [5:0] AXI_17_ARID_in;
  wire [5:0] AXI_17_AWID_in;
  wire [5:0] AXI_18_ARID_in;
  wire [5:0] AXI_18_AWID_in;
  wire [5:0] AXI_19_ARID_in;
  wire [5:0] AXI_19_AWID_in;
  wire [5:0] AXI_20_ARID_in;
  wire [5:0] AXI_20_AWID_in;
  wire [5:0] AXI_21_ARID_in;
  wire [5:0] AXI_21_AWID_in;
  wire [5:0] AXI_22_ARID_in;
  wire [5:0] AXI_22_AWID_in;
  wire [5:0] AXI_23_ARID_in;
  wire [5:0] AXI_23_AWID_in;
  wire [5:0] AXI_24_ARID_in;
  wire [5:0] AXI_24_AWID_in;
  wire [5:0] AXI_25_ARID_in;
  wire [5:0] AXI_25_AWID_in;
  wire [5:0] AXI_26_ARID_in;
  wire [5:0] AXI_26_AWID_in;
  wire [5:0] AXI_27_ARID_in;
  wire [5:0] AXI_27_AWID_in;
  wire [5:0] AXI_28_ARID_in;
  wire [5:0] AXI_28_AWID_in;
  wire [5:0] AXI_29_ARID_in;
  wire [5:0] AXI_29_AWID_in;
  wire [5:0] AXI_30_ARID_in;
  wire [5:0] AXI_30_AWID_in;
  wire [5:0] AXI_31_ARID_in;
  wire [5:0] AXI_31_AWID_in;
  wire [7:0] BLI_SCAN_IN_00_in;
  wire [7:0] BLI_SCAN_IN_01_in;
  wire [7:0] BLI_SCAN_IN_02_in;
  wire [7:0] BLI_SCAN_IN_03_in;
  wire [7:0] BLI_SCAN_IN_04_in;
  wire [7:0] BLI_SCAN_IN_05_in;
  wire [7:0] BLI_SCAN_IN_06_in;
  wire [7:0] BLI_SCAN_IN_07_in;
  wire [7:0] BLI_SCAN_IN_08_in;
  wire [7:0] BLI_SCAN_IN_09_in;
  wire [7:0] BLI_SCAN_IN_10_in;
  wire [7:0] BLI_SCAN_IN_11_in;
  wire [7:0] BLI_SCAN_IN_12_in;
  wire [7:0] BLI_SCAN_IN_13_in;
  wire [7:0] BLI_SCAN_IN_14_in;
  wire [7:0] BLI_SCAN_IN_15_in;
  wire [7:0] BLI_SCAN_IN_16_in;
  wire [7:0] BLI_SCAN_IN_17_in;
  wire [7:0] BLI_SCAN_IN_18_in;
  wire [7:0] BLI_SCAN_IN_19_in;
  wire [7:0] BLI_SCAN_IN_20_in;
  wire [7:0] BLI_SCAN_IN_21_in;
  wire [7:0] BLI_SCAN_IN_22_in;
  wire [7:0] BLI_SCAN_IN_23_in;
  wire [7:0] BLI_SCAN_IN_24_in;
  wire [7:0] BLI_SCAN_IN_25_in;
  wire [7:0] BLI_SCAN_IN_26_in;
  wire [7:0] BLI_SCAN_IN_27_in;
  wire [7:0] BLI_SCAN_IN_28_in;
  wire [7:0] BLI_SCAN_IN_29_in;
  wire [7:0] BLI_SCAN_IN_30_in;
  wire [7:0] BLI_SCAN_IN_31_in;

  assign APB_0_PRDATA = APB_0_PRDATA_out;
  assign APB_0_PREADY = APB_0_PREADY_out;
  assign APB_0_PSLVERR = APB_0_PSLVERR_out;
  assign APB_1_PRDATA = APB_1_PRDATA_out;
  assign APB_1_PREADY = APB_1_PREADY_out;
  assign APB_1_PSLVERR = APB_1_PSLVERR_out;
  assign AXI_00_ARREADY = AXI_00_ARREADY_out;
  assign AXI_00_AWREADY = AXI_00_AWREADY_out;
  assign AXI_00_BID = AXI_00_BID_out;
  assign AXI_00_BRESP = AXI_00_BRESP_out;
  assign AXI_00_BVALID = AXI_00_BVALID_out;
  assign AXI_00_DFI_AW_AERR_N = AXI_00_DFI_AW_AERR_N_out;
  assign AXI_00_DFI_CLK_BUF = AXI_00_DFI_CLK_BUF_out;
  assign AXI_00_DFI_DBI_BYTE_DISABLE = AXI_00_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_00_DFI_DW_RDDATA_DBI = AXI_00_DFI_DW_RDDATA_DBI_out;
  assign AXI_00_DFI_DW_RDDATA_DERR = AXI_00_DFI_DW_RDDATA_DERR_out;
  assign AXI_00_DFI_DW_RDDATA_VALID = AXI_00_DFI_DW_RDDATA_VALID_out;
  assign AXI_00_DFI_INIT_COMPLETE = AXI_00_DFI_INIT_COMPLETE_out;
  assign AXI_00_DFI_PHYUPD_REQ = AXI_00_DFI_PHYUPD_REQ_out;
  assign AXI_00_DFI_PHY_LP_STATE = AXI_00_DFI_PHY_LP_STATE_out;
  assign AXI_00_DFI_RST_N_BUF = AXI_00_DFI_RST_N_BUF_out;
  assign AXI_00_MC_STATUS = AXI_00_MC_STATUS_out;
  assign AXI_00_PHY_STATUS = AXI_00_PHY_STATUS_out;
  assign AXI_00_RDATA = AXI_00_RDATA_out;
  assign AXI_00_RDATA_PARITY = AXI_00_RDATA_PARITY_out;
  assign AXI_00_RID = AXI_00_RID_out;
  assign AXI_00_RLAST = AXI_00_RLAST_out;
  assign AXI_00_RRESP = AXI_00_RRESP_out;
  assign AXI_00_RVALID = AXI_00_RVALID_out;
  assign AXI_00_WREADY = AXI_00_WREADY_out;
  assign AXI_01_ARREADY = AXI_01_ARREADY_out;
  assign AXI_01_AWREADY = AXI_01_AWREADY_out;
  assign AXI_01_BID = AXI_01_BID_out;
  assign AXI_01_BRESP = AXI_01_BRESP_out;
  assign AXI_01_BVALID = AXI_01_BVALID_out;
  assign AXI_01_DFI_AW_AERR_N = AXI_01_DFI_AW_AERR_N_out;
  assign AXI_01_DFI_CLK_BUF = AXI_01_DFI_CLK_BUF_out;
  assign AXI_01_DFI_DBI_BYTE_DISABLE = AXI_01_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_01_DFI_DW_RDDATA_DBI = AXI_01_DFI_DW_RDDATA_DBI_out;
  assign AXI_01_DFI_DW_RDDATA_DERR = AXI_01_DFI_DW_RDDATA_DERR_out;
  assign AXI_01_DFI_DW_RDDATA_VALID = AXI_01_DFI_DW_RDDATA_VALID_out;
  assign AXI_01_DFI_INIT_COMPLETE = AXI_01_DFI_INIT_COMPLETE_out;
  assign AXI_01_DFI_PHYUPD_REQ = AXI_01_DFI_PHYUPD_REQ_out;
  assign AXI_01_DFI_PHY_LP_STATE = AXI_01_DFI_PHY_LP_STATE_out;
  assign AXI_01_DFI_RST_N_BUF = AXI_01_DFI_RST_N_BUF_out;
  assign AXI_01_RDATA = AXI_01_RDATA_out;
  assign AXI_01_RDATA_PARITY = AXI_01_RDATA_PARITY_out;
  assign AXI_01_RID = AXI_01_RID_out;
  assign AXI_01_RLAST = AXI_01_RLAST_out;
  assign AXI_01_RRESP = AXI_01_RRESP_out;
  assign AXI_01_RVALID = AXI_01_RVALID_out;
  assign AXI_01_WREADY = AXI_01_WREADY_out;
  assign AXI_02_ARREADY = AXI_02_ARREADY_out;
  assign AXI_02_AWREADY = AXI_02_AWREADY_out;
  assign AXI_02_BID = AXI_02_BID_out;
  assign AXI_02_BRESP = AXI_02_BRESP_out;
  assign AXI_02_BVALID = AXI_02_BVALID_out;
  assign AXI_02_DFI_AW_AERR_N = AXI_02_DFI_AW_AERR_N_out;
  assign AXI_02_DFI_CLK_BUF = AXI_02_DFI_CLK_BUF_out;
  assign AXI_02_DFI_DBI_BYTE_DISABLE = AXI_02_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_02_DFI_DW_RDDATA_DBI = AXI_02_DFI_DW_RDDATA_DBI_out;
  assign AXI_02_DFI_DW_RDDATA_DERR = AXI_02_DFI_DW_RDDATA_DERR_out;
  assign AXI_02_DFI_DW_RDDATA_VALID = AXI_02_DFI_DW_RDDATA_VALID_out;
  assign AXI_02_DFI_INIT_COMPLETE = AXI_02_DFI_INIT_COMPLETE_out;
  assign AXI_02_DFI_PHYUPD_REQ = AXI_02_DFI_PHYUPD_REQ_out;
  assign AXI_02_DFI_PHY_LP_STATE = AXI_02_DFI_PHY_LP_STATE_out;
  assign AXI_02_DFI_RST_N_BUF = AXI_02_DFI_RST_N_BUF_out;
  assign AXI_02_MC_STATUS = AXI_02_MC_STATUS_out;
  assign AXI_02_PHY_STATUS = AXI_02_PHY_STATUS_out;
  assign AXI_02_RDATA = AXI_02_RDATA_out;
  assign AXI_02_RDATA_PARITY = AXI_02_RDATA_PARITY_out;
  assign AXI_02_RID = AXI_02_RID_out;
  assign AXI_02_RLAST = AXI_02_RLAST_out;
  assign AXI_02_RRESP = AXI_02_RRESP_out;
  assign AXI_02_RVALID = AXI_02_RVALID_out;
  assign AXI_02_WREADY = AXI_02_WREADY_out;
  assign AXI_03_ARREADY = AXI_03_ARREADY_out;
  assign AXI_03_AWREADY = AXI_03_AWREADY_out;
  assign AXI_03_BID = AXI_03_BID_out;
  assign AXI_03_BRESP = AXI_03_BRESP_out;
  assign AXI_03_BVALID = AXI_03_BVALID_out;
  assign AXI_03_DFI_AW_AERR_N = AXI_03_DFI_AW_AERR_N_out;
  assign AXI_03_DFI_CLK_BUF = AXI_03_DFI_CLK_BUF_out;
  assign AXI_03_DFI_DBI_BYTE_DISABLE = AXI_03_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_03_DFI_DW_RDDATA_DBI = AXI_03_DFI_DW_RDDATA_DBI_out;
  assign AXI_03_DFI_DW_RDDATA_DERR = AXI_03_DFI_DW_RDDATA_DERR_out;
  assign AXI_03_DFI_DW_RDDATA_VALID = AXI_03_DFI_DW_RDDATA_VALID_out;
  assign AXI_03_DFI_INIT_COMPLETE = AXI_03_DFI_INIT_COMPLETE_out;
  assign AXI_03_DFI_PHYUPD_REQ = AXI_03_DFI_PHYUPD_REQ_out;
  assign AXI_03_DFI_PHY_LP_STATE = AXI_03_DFI_PHY_LP_STATE_out;
  assign AXI_03_DFI_RST_N_BUF = AXI_03_DFI_RST_N_BUF_out;
  assign AXI_03_RDATA = AXI_03_RDATA_out;
  assign AXI_03_RDATA_PARITY = AXI_03_RDATA_PARITY_out;
  assign AXI_03_RID = AXI_03_RID_out;
  assign AXI_03_RLAST = AXI_03_RLAST_out;
  assign AXI_03_RRESP = AXI_03_RRESP_out;
  assign AXI_03_RVALID = AXI_03_RVALID_out;
  assign AXI_03_WREADY = AXI_03_WREADY_out;
  assign AXI_04_ARREADY = AXI_04_ARREADY_out;
  assign AXI_04_AWREADY = AXI_04_AWREADY_out;
  assign AXI_04_BID = AXI_04_BID_out;
  assign AXI_04_BRESP = AXI_04_BRESP_out;
  assign AXI_04_BVALID = AXI_04_BVALID_out;
  assign AXI_04_DFI_AW_AERR_N = AXI_04_DFI_AW_AERR_N_out;
  assign AXI_04_DFI_CLK_BUF = AXI_04_DFI_CLK_BUF_out;
  assign AXI_04_DFI_DBI_BYTE_DISABLE = AXI_04_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_04_DFI_DW_RDDATA_DBI = AXI_04_DFI_DW_RDDATA_DBI_out;
  assign AXI_04_DFI_DW_RDDATA_DERR = AXI_04_DFI_DW_RDDATA_DERR_out;
  assign AXI_04_DFI_DW_RDDATA_VALID = AXI_04_DFI_DW_RDDATA_VALID_out;
  assign AXI_04_DFI_INIT_COMPLETE = AXI_04_DFI_INIT_COMPLETE_out;
  assign AXI_04_DFI_PHYUPD_REQ = AXI_04_DFI_PHYUPD_REQ_out;
  assign AXI_04_DFI_PHY_LP_STATE = AXI_04_DFI_PHY_LP_STATE_out;
  assign AXI_04_DFI_RST_N_BUF = AXI_04_DFI_RST_N_BUF_out;
  assign AXI_04_MC_STATUS = AXI_04_MC_STATUS_out;
  assign AXI_04_PHY_STATUS = AXI_04_PHY_STATUS_out;
  assign AXI_04_RDATA = AXI_04_RDATA_out;
  assign AXI_04_RDATA_PARITY = AXI_04_RDATA_PARITY_out;
  assign AXI_04_RID = AXI_04_RID_out;
  assign AXI_04_RLAST = AXI_04_RLAST_out;
  assign AXI_04_RRESP = AXI_04_RRESP_out;
  assign AXI_04_RVALID = AXI_04_RVALID_out;
  assign AXI_04_WREADY = AXI_04_WREADY_out;
  assign AXI_05_ARREADY = AXI_05_ARREADY_out;
  assign AXI_05_AWREADY = AXI_05_AWREADY_out;
  assign AXI_05_BID = AXI_05_BID_out;
  assign AXI_05_BRESP = AXI_05_BRESP_out;
  assign AXI_05_BVALID = AXI_05_BVALID_out;
  assign AXI_05_DFI_AW_AERR_N = AXI_05_DFI_AW_AERR_N_out;
  assign AXI_05_DFI_CLK_BUF = AXI_05_DFI_CLK_BUF_out;
  assign AXI_05_DFI_DBI_BYTE_DISABLE = AXI_05_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_05_DFI_DW_RDDATA_DBI = AXI_05_DFI_DW_RDDATA_DBI_out;
  assign AXI_05_DFI_DW_RDDATA_DERR = AXI_05_DFI_DW_RDDATA_DERR_out;
  assign AXI_05_DFI_DW_RDDATA_VALID = AXI_05_DFI_DW_RDDATA_VALID_out;
  assign AXI_05_DFI_INIT_COMPLETE = AXI_05_DFI_INIT_COMPLETE_out;
  assign AXI_05_DFI_PHYUPD_REQ = AXI_05_DFI_PHYUPD_REQ_out;
  assign AXI_05_DFI_PHY_LP_STATE = AXI_05_DFI_PHY_LP_STATE_out;
  assign AXI_05_DFI_RST_N_BUF = AXI_05_DFI_RST_N_BUF_out;
  assign AXI_05_RDATA = AXI_05_RDATA_out;
  assign AXI_05_RDATA_PARITY = AXI_05_RDATA_PARITY_out;
  assign AXI_05_RID = AXI_05_RID_out;
  assign AXI_05_RLAST = AXI_05_RLAST_out;
  assign AXI_05_RRESP = AXI_05_RRESP_out;
  assign AXI_05_RVALID = AXI_05_RVALID_out;
  assign AXI_05_WREADY = AXI_05_WREADY_out;
  assign AXI_06_ARREADY = AXI_06_ARREADY_out;
  assign AXI_06_AWREADY = AXI_06_AWREADY_out;
  assign AXI_06_BID = AXI_06_BID_out;
  assign AXI_06_BRESP = AXI_06_BRESP_out;
  assign AXI_06_BVALID = AXI_06_BVALID_out;
  assign AXI_06_DFI_AW_AERR_N = AXI_06_DFI_AW_AERR_N_out;
  assign AXI_06_DFI_CLK_BUF = AXI_06_DFI_CLK_BUF_out;
  assign AXI_06_DFI_DBI_BYTE_DISABLE = AXI_06_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_06_DFI_DW_RDDATA_DBI = AXI_06_DFI_DW_RDDATA_DBI_out;
  assign AXI_06_DFI_DW_RDDATA_DERR = AXI_06_DFI_DW_RDDATA_DERR_out;
  assign AXI_06_DFI_DW_RDDATA_VALID = AXI_06_DFI_DW_RDDATA_VALID_out;
  assign AXI_06_DFI_INIT_COMPLETE = AXI_06_DFI_INIT_COMPLETE_out;
  assign AXI_06_DFI_PHYUPD_REQ = AXI_06_DFI_PHYUPD_REQ_out;
  assign AXI_06_DFI_PHY_LP_STATE = AXI_06_DFI_PHY_LP_STATE_out;
  assign AXI_06_DFI_RST_N_BUF = AXI_06_DFI_RST_N_BUF_out;
  assign AXI_06_MC_STATUS = AXI_06_MC_STATUS_out;
  assign AXI_06_PHY_STATUS = AXI_06_PHY_STATUS_out;
  assign AXI_06_RDATA = AXI_06_RDATA_out;
  assign AXI_06_RDATA_PARITY = AXI_06_RDATA_PARITY_out;
  assign AXI_06_RID = AXI_06_RID_out;
  assign AXI_06_RLAST = AXI_06_RLAST_out;
  assign AXI_06_RRESP = AXI_06_RRESP_out;
  assign AXI_06_RVALID = AXI_06_RVALID_out;
  assign AXI_06_WREADY = AXI_06_WREADY_out;
  assign AXI_07_ARREADY = AXI_07_ARREADY_out;
  assign AXI_07_AWREADY = AXI_07_AWREADY_out;
  assign AXI_07_BID = AXI_07_BID_out;
  assign AXI_07_BRESP = AXI_07_BRESP_out;
  assign AXI_07_BVALID = AXI_07_BVALID_out;
  assign AXI_07_DFI_AW_AERR_N = AXI_07_DFI_AW_AERR_N_out;
  assign AXI_07_DFI_CLK_BUF = AXI_07_DFI_CLK_BUF_out;
  assign AXI_07_DFI_DBI_BYTE_DISABLE = AXI_07_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_07_DFI_DW_RDDATA_DBI = AXI_07_DFI_DW_RDDATA_DBI_out;
  assign AXI_07_DFI_DW_RDDATA_DERR = AXI_07_DFI_DW_RDDATA_DERR_out;
  assign AXI_07_DFI_DW_RDDATA_VALID = AXI_07_DFI_DW_RDDATA_VALID_out;
  assign AXI_07_DFI_INIT_COMPLETE = AXI_07_DFI_INIT_COMPLETE_out;
  assign AXI_07_DFI_PHYUPD_REQ = AXI_07_DFI_PHYUPD_REQ_out;
  assign AXI_07_DFI_PHY_LP_STATE = AXI_07_DFI_PHY_LP_STATE_out;
  assign AXI_07_DFI_RST_N_BUF = AXI_07_DFI_RST_N_BUF_out;
  assign AXI_07_RDATA = AXI_07_RDATA_out;
  assign AXI_07_RDATA_PARITY = AXI_07_RDATA_PARITY_out;
  assign AXI_07_RID = AXI_07_RID_out;
  assign AXI_07_RLAST = AXI_07_RLAST_out;
  assign AXI_07_RRESP = AXI_07_RRESP_out;
  assign AXI_07_RVALID = AXI_07_RVALID_out;
  assign AXI_07_WREADY = AXI_07_WREADY_out;
  assign AXI_08_ARREADY = AXI_08_ARREADY_out;
  assign AXI_08_AWREADY = AXI_08_AWREADY_out;
  assign AXI_08_BID = AXI_08_BID_out;
  assign AXI_08_BRESP = AXI_08_BRESP_out;
  assign AXI_08_BVALID = AXI_08_BVALID_out;
  assign AXI_08_DFI_AW_AERR_N = AXI_08_DFI_AW_AERR_N_out;
  assign AXI_08_DFI_CLK_BUF = AXI_08_DFI_CLK_BUF_out;
  assign AXI_08_DFI_DBI_BYTE_DISABLE = AXI_08_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_08_DFI_DW_RDDATA_DBI = AXI_08_DFI_DW_RDDATA_DBI_out;
  assign AXI_08_DFI_DW_RDDATA_DERR = AXI_08_DFI_DW_RDDATA_DERR_out;
  assign AXI_08_DFI_DW_RDDATA_VALID = AXI_08_DFI_DW_RDDATA_VALID_out;
  assign AXI_08_DFI_INIT_COMPLETE = AXI_08_DFI_INIT_COMPLETE_out;
  assign AXI_08_DFI_PHYUPD_REQ = AXI_08_DFI_PHYUPD_REQ_out;
  assign AXI_08_DFI_PHY_LP_STATE = AXI_08_DFI_PHY_LP_STATE_out;
  assign AXI_08_DFI_RST_N_BUF = AXI_08_DFI_RST_N_BUF_out;
  assign AXI_08_MC_STATUS = AXI_08_MC_STATUS_out;
  assign AXI_08_PHY_STATUS = AXI_08_PHY_STATUS_out;
  assign AXI_08_RDATA = AXI_08_RDATA_out;
  assign AXI_08_RDATA_PARITY = AXI_08_RDATA_PARITY_out;
  assign AXI_08_RID = AXI_08_RID_out;
  assign AXI_08_RLAST = AXI_08_RLAST_out;
  assign AXI_08_RRESP = AXI_08_RRESP_out;
  assign AXI_08_RVALID = AXI_08_RVALID_out;
  assign AXI_08_WREADY = AXI_08_WREADY_out;
  assign AXI_09_ARREADY = AXI_09_ARREADY_out;
  assign AXI_09_AWREADY = AXI_09_AWREADY_out;
  assign AXI_09_BID = AXI_09_BID_out;
  assign AXI_09_BRESP = AXI_09_BRESP_out;
  assign AXI_09_BVALID = AXI_09_BVALID_out;
  assign AXI_09_DFI_AW_AERR_N = AXI_09_DFI_AW_AERR_N_out;
  assign AXI_09_DFI_CLK_BUF = AXI_09_DFI_CLK_BUF_out;
  assign AXI_09_DFI_DBI_BYTE_DISABLE = AXI_09_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_09_DFI_DW_RDDATA_DBI = AXI_09_DFI_DW_RDDATA_DBI_out;
  assign AXI_09_DFI_DW_RDDATA_DERR = AXI_09_DFI_DW_RDDATA_DERR_out;
  assign AXI_09_DFI_DW_RDDATA_VALID = AXI_09_DFI_DW_RDDATA_VALID_out;
  assign AXI_09_DFI_INIT_COMPLETE = AXI_09_DFI_INIT_COMPLETE_out;
  assign AXI_09_DFI_PHYUPD_REQ = AXI_09_DFI_PHYUPD_REQ_out;
  assign AXI_09_DFI_PHY_LP_STATE = AXI_09_DFI_PHY_LP_STATE_out;
  assign AXI_09_DFI_RST_N_BUF = AXI_09_DFI_RST_N_BUF_out;
  assign AXI_09_RDATA = AXI_09_RDATA_out;
  assign AXI_09_RDATA_PARITY = AXI_09_RDATA_PARITY_out;
  assign AXI_09_RID = AXI_09_RID_out;
  assign AXI_09_RLAST = AXI_09_RLAST_out;
  assign AXI_09_RRESP = AXI_09_RRESP_out;
  assign AXI_09_RVALID = AXI_09_RVALID_out;
  assign AXI_09_WREADY = AXI_09_WREADY_out;
  assign AXI_10_ARREADY = AXI_10_ARREADY_out;
  assign AXI_10_AWREADY = AXI_10_AWREADY_out;
  assign AXI_10_BID = AXI_10_BID_out;
  assign AXI_10_BRESP = AXI_10_BRESP_out;
  assign AXI_10_BVALID = AXI_10_BVALID_out;
  assign AXI_10_DFI_AW_AERR_N = AXI_10_DFI_AW_AERR_N_out;
  assign AXI_10_DFI_CLK_BUF = AXI_10_DFI_CLK_BUF_out;
  assign AXI_10_DFI_DBI_BYTE_DISABLE = AXI_10_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_10_DFI_DW_RDDATA_DBI = AXI_10_DFI_DW_RDDATA_DBI_out;
  assign AXI_10_DFI_DW_RDDATA_DERR = AXI_10_DFI_DW_RDDATA_DERR_out;
  assign AXI_10_DFI_DW_RDDATA_VALID = AXI_10_DFI_DW_RDDATA_VALID_out;
  assign AXI_10_DFI_INIT_COMPLETE = AXI_10_DFI_INIT_COMPLETE_out;
  assign AXI_10_DFI_PHYUPD_REQ = AXI_10_DFI_PHYUPD_REQ_out;
  assign AXI_10_DFI_PHY_LP_STATE = AXI_10_DFI_PHY_LP_STATE_out;
  assign AXI_10_DFI_RST_N_BUF = AXI_10_DFI_RST_N_BUF_out;
  assign AXI_10_MC_STATUS = AXI_10_MC_STATUS_out;
  assign AXI_10_PHY_STATUS = AXI_10_PHY_STATUS_out;
  assign AXI_10_RDATA = AXI_10_RDATA_out;
  assign AXI_10_RDATA_PARITY = AXI_10_RDATA_PARITY_out;
  assign AXI_10_RID = AXI_10_RID_out;
  assign AXI_10_RLAST = AXI_10_RLAST_out;
  assign AXI_10_RRESP = AXI_10_RRESP_out;
  assign AXI_10_RVALID = AXI_10_RVALID_out;
  assign AXI_10_WREADY = AXI_10_WREADY_out;
  assign AXI_11_ARREADY = AXI_11_ARREADY_out;
  assign AXI_11_AWREADY = AXI_11_AWREADY_out;
  assign AXI_11_BID = AXI_11_BID_out;
  assign AXI_11_BRESP = AXI_11_BRESP_out;
  assign AXI_11_BVALID = AXI_11_BVALID_out;
  assign AXI_11_DFI_AW_AERR_N = AXI_11_DFI_AW_AERR_N_out;
  assign AXI_11_DFI_CLK_BUF = AXI_11_DFI_CLK_BUF_out;
  assign AXI_11_DFI_DBI_BYTE_DISABLE = AXI_11_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_11_DFI_DW_RDDATA_DBI = AXI_11_DFI_DW_RDDATA_DBI_out;
  assign AXI_11_DFI_DW_RDDATA_DERR = AXI_11_DFI_DW_RDDATA_DERR_out;
  assign AXI_11_DFI_DW_RDDATA_VALID = AXI_11_DFI_DW_RDDATA_VALID_out;
  assign AXI_11_DFI_INIT_COMPLETE = AXI_11_DFI_INIT_COMPLETE_out;
  assign AXI_11_DFI_PHYUPD_REQ = AXI_11_DFI_PHYUPD_REQ_out;
  assign AXI_11_DFI_PHY_LP_STATE = AXI_11_DFI_PHY_LP_STATE_out;
  assign AXI_11_DFI_RST_N_BUF = AXI_11_DFI_RST_N_BUF_out;
  assign AXI_11_RDATA = AXI_11_RDATA_out;
  assign AXI_11_RDATA_PARITY = AXI_11_RDATA_PARITY_out;
  assign AXI_11_RID = AXI_11_RID_out;
  assign AXI_11_RLAST = AXI_11_RLAST_out;
  assign AXI_11_RRESP = AXI_11_RRESP_out;
  assign AXI_11_RVALID = AXI_11_RVALID_out;
  assign AXI_11_WREADY = AXI_11_WREADY_out;
  assign AXI_12_ARREADY = AXI_12_ARREADY_out;
  assign AXI_12_AWREADY = AXI_12_AWREADY_out;
  assign AXI_12_BID = AXI_12_BID_out;
  assign AXI_12_BRESP = AXI_12_BRESP_out;
  assign AXI_12_BVALID = AXI_12_BVALID_out;
  assign AXI_12_DFI_AW_AERR_N = AXI_12_DFI_AW_AERR_N_out;
  assign AXI_12_DFI_CLK_BUF = AXI_12_DFI_CLK_BUF_out;
  assign AXI_12_DFI_DBI_BYTE_DISABLE = AXI_12_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_12_DFI_DW_RDDATA_DBI = AXI_12_DFI_DW_RDDATA_DBI_out;
  assign AXI_12_DFI_DW_RDDATA_DERR = AXI_12_DFI_DW_RDDATA_DERR_out;
  assign AXI_12_DFI_DW_RDDATA_VALID = AXI_12_DFI_DW_RDDATA_VALID_out;
  assign AXI_12_DFI_INIT_COMPLETE = AXI_12_DFI_INIT_COMPLETE_out;
  assign AXI_12_DFI_PHYUPD_REQ = AXI_12_DFI_PHYUPD_REQ_out;
  assign AXI_12_DFI_PHY_LP_STATE = AXI_12_DFI_PHY_LP_STATE_out;
  assign AXI_12_DFI_RST_N_BUF = AXI_12_DFI_RST_N_BUF_out;
  assign AXI_12_MC_STATUS = AXI_12_MC_STATUS_out;
  assign AXI_12_PHY_STATUS = AXI_12_PHY_STATUS_out;
  assign AXI_12_RDATA = AXI_12_RDATA_out;
  assign AXI_12_RDATA_PARITY = AXI_12_RDATA_PARITY_out;
  assign AXI_12_RID = AXI_12_RID_out;
  assign AXI_12_RLAST = AXI_12_RLAST_out;
  assign AXI_12_RRESP = AXI_12_RRESP_out;
  assign AXI_12_RVALID = AXI_12_RVALID_out;
  assign AXI_12_WREADY = AXI_12_WREADY_out;
  assign AXI_13_ARREADY = AXI_13_ARREADY_out;
  assign AXI_13_AWREADY = AXI_13_AWREADY_out;
  assign AXI_13_BID = AXI_13_BID_out;
  assign AXI_13_BRESP = AXI_13_BRESP_out;
  assign AXI_13_BVALID = AXI_13_BVALID_out;
  assign AXI_13_DFI_AW_AERR_N = AXI_13_DFI_AW_AERR_N_out;
  assign AXI_13_DFI_CLK_BUF = AXI_13_DFI_CLK_BUF_out;
  assign AXI_13_DFI_DBI_BYTE_DISABLE = AXI_13_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_13_DFI_DW_RDDATA_DBI = AXI_13_DFI_DW_RDDATA_DBI_out;
  assign AXI_13_DFI_DW_RDDATA_DERR = AXI_13_DFI_DW_RDDATA_DERR_out;
  assign AXI_13_DFI_DW_RDDATA_VALID = AXI_13_DFI_DW_RDDATA_VALID_out;
  assign AXI_13_DFI_INIT_COMPLETE = AXI_13_DFI_INIT_COMPLETE_out;
  assign AXI_13_DFI_PHYUPD_REQ = AXI_13_DFI_PHYUPD_REQ_out;
  assign AXI_13_DFI_PHY_LP_STATE = AXI_13_DFI_PHY_LP_STATE_out;
  assign AXI_13_DFI_RST_N_BUF = AXI_13_DFI_RST_N_BUF_out;
  assign AXI_13_RDATA = AXI_13_RDATA_out;
  assign AXI_13_RDATA_PARITY = AXI_13_RDATA_PARITY_out;
  assign AXI_13_RID = AXI_13_RID_out;
  assign AXI_13_RLAST = AXI_13_RLAST_out;
  assign AXI_13_RRESP = AXI_13_RRESP_out;
  assign AXI_13_RVALID = AXI_13_RVALID_out;
  assign AXI_13_WREADY = AXI_13_WREADY_out;
  assign AXI_14_ARREADY = AXI_14_ARREADY_out;
  assign AXI_14_AWREADY = AXI_14_AWREADY_out;
  assign AXI_14_BID = AXI_14_BID_out;
  assign AXI_14_BRESP = AXI_14_BRESP_out;
  assign AXI_14_BVALID = AXI_14_BVALID_out;
  assign AXI_14_DFI_AW_AERR_N = AXI_14_DFI_AW_AERR_N_out;
  assign AXI_14_DFI_CLK_BUF = AXI_14_DFI_CLK_BUF_out;
  assign AXI_14_DFI_DBI_BYTE_DISABLE = AXI_14_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_14_DFI_DW_RDDATA_DBI = AXI_14_DFI_DW_RDDATA_DBI_out;
  assign AXI_14_DFI_DW_RDDATA_DERR = AXI_14_DFI_DW_RDDATA_DERR_out;
  assign AXI_14_DFI_DW_RDDATA_VALID = AXI_14_DFI_DW_RDDATA_VALID_out;
  assign AXI_14_DFI_INIT_COMPLETE = AXI_14_DFI_INIT_COMPLETE_out;
  assign AXI_14_DFI_PHYUPD_REQ = AXI_14_DFI_PHYUPD_REQ_out;
  assign AXI_14_DFI_PHY_LP_STATE = AXI_14_DFI_PHY_LP_STATE_out;
  assign AXI_14_DFI_RST_N_BUF = AXI_14_DFI_RST_N_BUF_out;
  assign AXI_14_MC_STATUS = AXI_14_MC_STATUS_out;
  assign AXI_14_PHY_STATUS = AXI_14_PHY_STATUS_out;
  assign AXI_14_RDATA = AXI_14_RDATA_out;
  assign AXI_14_RDATA_PARITY = AXI_14_RDATA_PARITY_out;
  assign AXI_14_RID = AXI_14_RID_out;
  assign AXI_14_RLAST = AXI_14_RLAST_out;
  assign AXI_14_RRESP = AXI_14_RRESP_out;
  assign AXI_14_RVALID = AXI_14_RVALID_out;
  assign AXI_14_WREADY = AXI_14_WREADY_out;
  assign AXI_15_ARREADY = AXI_15_ARREADY_out;
  assign AXI_15_AWREADY = AXI_15_AWREADY_out;
  assign AXI_15_BID = AXI_15_BID_out;
  assign AXI_15_BRESP = AXI_15_BRESP_out;
  assign AXI_15_BVALID = AXI_15_BVALID_out;
  assign AXI_15_DFI_AW_AERR_N = AXI_15_DFI_AW_AERR_N_out;
  assign AXI_15_DFI_CLK_BUF = AXI_15_DFI_CLK_BUF_out;
  assign AXI_15_DFI_DBI_BYTE_DISABLE = AXI_15_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_15_DFI_DW_RDDATA_DBI = AXI_15_DFI_DW_RDDATA_DBI_out;
  assign AXI_15_DFI_DW_RDDATA_DERR = AXI_15_DFI_DW_RDDATA_DERR_out;
  assign AXI_15_DFI_DW_RDDATA_VALID = AXI_15_DFI_DW_RDDATA_VALID_out;
  assign AXI_15_DFI_INIT_COMPLETE = AXI_15_DFI_INIT_COMPLETE_out;
  assign AXI_15_DFI_PHYUPD_REQ = AXI_15_DFI_PHYUPD_REQ_out;
  assign AXI_15_DFI_PHY_LP_STATE = AXI_15_DFI_PHY_LP_STATE_out;
  assign AXI_15_DFI_RST_N_BUF = AXI_15_DFI_RST_N_BUF_out;
  assign AXI_15_RDATA = AXI_15_RDATA_out;
  assign AXI_15_RDATA_PARITY = AXI_15_RDATA_PARITY_out;
  assign AXI_15_RID = AXI_15_RID_out;
  assign AXI_15_RLAST = AXI_15_RLAST_out;
  assign AXI_15_RRESP = AXI_15_RRESP_out;
  assign AXI_15_RVALID = AXI_15_RVALID_out;
  assign AXI_15_WREADY = AXI_15_WREADY_out;
  assign AXI_16_ARREADY = AXI_16_ARREADY_out;
  assign AXI_16_AWREADY = AXI_16_AWREADY_out;
  assign AXI_16_BID = AXI_16_BID_out;
  assign AXI_16_BRESP = AXI_16_BRESP_out;
  assign AXI_16_BVALID = AXI_16_BVALID_out;
  assign AXI_16_DFI_AW_AERR_N = AXI_16_DFI_AW_AERR_N_out;
  assign AXI_16_DFI_CLK_BUF = AXI_16_DFI_CLK_BUF_out;
  assign AXI_16_DFI_DBI_BYTE_DISABLE = AXI_16_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_16_DFI_DW_RDDATA_DBI = AXI_16_DFI_DW_RDDATA_DBI_out;
  assign AXI_16_DFI_DW_RDDATA_DERR = AXI_16_DFI_DW_RDDATA_DERR_out;
  assign AXI_16_DFI_DW_RDDATA_VALID = AXI_16_DFI_DW_RDDATA_VALID_out;
  assign AXI_16_DFI_INIT_COMPLETE = AXI_16_DFI_INIT_COMPLETE_out;
  assign AXI_16_DFI_PHYUPD_REQ = AXI_16_DFI_PHYUPD_REQ_out;
  assign AXI_16_DFI_PHY_LP_STATE = AXI_16_DFI_PHY_LP_STATE_out;
  assign AXI_16_DFI_RST_N_BUF = AXI_16_DFI_RST_N_BUF_out;
  assign AXI_16_MC_STATUS = AXI_16_MC_STATUS_out;
  assign AXI_16_PHY_STATUS = AXI_16_PHY_STATUS_out;
  assign AXI_16_RDATA = AXI_16_RDATA_out;
  assign AXI_16_RDATA_PARITY = AXI_16_RDATA_PARITY_out;
  assign AXI_16_RID = AXI_16_RID_out;
  assign AXI_16_RLAST = AXI_16_RLAST_out;
  assign AXI_16_RRESP = AXI_16_RRESP_out;
  assign AXI_16_RVALID = AXI_16_RVALID_out;
  assign AXI_16_WREADY = AXI_16_WREADY_out;
  assign AXI_17_ARREADY = AXI_17_ARREADY_out;
  assign AXI_17_AWREADY = AXI_17_AWREADY_out;
  assign AXI_17_BID = AXI_17_BID_out;
  assign AXI_17_BRESP = AXI_17_BRESP_out;
  assign AXI_17_BVALID = AXI_17_BVALID_out;
  assign AXI_17_DFI_AW_AERR_N = AXI_17_DFI_AW_AERR_N_out;
  assign AXI_17_DFI_CLK_BUF = AXI_17_DFI_CLK_BUF_out;
  assign AXI_17_DFI_DBI_BYTE_DISABLE = AXI_17_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_17_DFI_DW_RDDATA_DBI = AXI_17_DFI_DW_RDDATA_DBI_out;
  assign AXI_17_DFI_DW_RDDATA_DERR = AXI_17_DFI_DW_RDDATA_DERR_out;
  assign AXI_17_DFI_DW_RDDATA_VALID = AXI_17_DFI_DW_RDDATA_VALID_out;
  assign AXI_17_DFI_INIT_COMPLETE = AXI_17_DFI_INIT_COMPLETE_out;
  assign AXI_17_DFI_PHYUPD_REQ = AXI_17_DFI_PHYUPD_REQ_out;
  assign AXI_17_DFI_PHY_LP_STATE = AXI_17_DFI_PHY_LP_STATE_out;
  assign AXI_17_DFI_RST_N_BUF = AXI_17_DFI_RST_N_BUF_out;
  assign AXI_17_RDATA = AXI_17_RDATA_out;
  assign AXI_17_RDATA_PARITY = AXI_17_RDATA_PARITY_out;
  assign AXI_17_RID = AXI_17_RID_out;
  assign AXI_17_RLAST = AXI_17_RLAST_out;
  assign AXI_17_RRESP = AXI_17_RRESP_out;
  assign AXI_17_RVALID = AXI_17_RVALID_out;
  assign AXI_17_WREADY = AXI_17_WREADY_out;
  assign AXI_18_ARREADY = AXI_18_ARREADY_out;
  assign AXI_18_AWREADY = AXI_18_AWREADY_out;
  assign AXI_18_BID = AXI_18_BID_out;
  assign AXI_18_BRESP = AXI_18_BRESP_out;
  assign AXI_18_BVALID = AXI_18_BVALID_out;
  assign AXI_18_DFI_AW_AERR_N = AXI_18_DFI_AW_AERR_N_out;
  assign AXI_18_DFI_CLK_BUF = AXI_18_DFI_CLK_BUF_out;
  assign AXI_18_DFI_DBI_BYTE_DISABLE = AXI_18_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_18_DFI_DW_RDDATA_DBI = AXI_18_DFI_DW_RDDATA_DBI_out;
  assign AXI_18_DFI_DW_RDDATA_DERR = AXI_18_DFI_DW_RDDATA_DERR_out;
  assign AXI_18_DFI_DW_RDDATA_VALID = AXI_18_DFI_DW_RDDATA_VALID_out;
  assign AXI_18_DFI_INIT_COMPLETE = AXI_18_DFI_INIT_COMPLETE_out;
  assign AXI_18_DFI_PHYUPD_REQ = AXI_18_DFI_PHYUPD_REQ_out;
  assign AXI_18_DFI_PHY_LP_STATE = AXI_18_DFI_PHY_LP_STATE_out;
  assign AXI_18_DFI_RST_N_BUF = AXI_18_DFI_RST_N_BUF_out;
  assign AXI_18_MC_STATUS = AXI_18_MC_STATUS_out;
  assign AXI_18_PHY_STATUS = AXI_18_PHY_STATUS_out;
  assign AXI_18_RDATA = AXI_18_RDATA_out;
  assign AXI_18_RDATA_PARITY = AXI_18_RDATA_PARITY_out;
  assign AXI_18_RID = AXI_18_RID_out;
  assign AXI_18_RLAST = AXI_18_RLAST_out;
  assign AXI_18_RRESP = AXI_18_RRESP_out;
  assign AXI_18_RVALID = AXI_18_RVALID_out;
  assign AXI_18_WREADY = AXI_18_WREADY_out;
  assign AXI_19_ARREADY = AXI_19_ARREADY_out;
  assign AXI_19_AWREADY = AXI_19_AWREADY_out;
  assign AXI_19_BID = AXI_19_BID_out;
  assign AXI_19_BRESP = AXI_19_BRESP_out;
  assign AXI_19_BVALID = AXI_19_BVALID_out;
  assign AXI_19_DFI_AW_AERR_N = AXI_19_DFI_AW_AERR_N_out;
  assign AXI_19_DFI_CLK_BUF = AXI_19_DFI_CLK_BUF_out;
  assign AXI_19_DFI_DBI_BYTE_DISABLE = AXI_19_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_19_DFI_DW_RDDATA_DBI = AXI_19_DFI_DW_RDDATA_DBI_out;
  assign AXI_19_DFI_DW_RDDATA_DERR = AXI_19_DFI_DW_RDDATA_DERR_out;
  assign AXI_19_DFI_DW_RDDATA_VALID = AXI_19_DFI_DW_RDDATA_VALID_out;
  assign AXI_19_DFI_INIT_COMPLETE = AXI_19_DFI_INIT_COMPLETE_out;
  assign AXI_19_DFI_PHYUPD_REQ = AXI_19_DFI_PHYUPD_REQ_out;
  assign AXI_19_DFI_PHY_LP_STATE = AXI_19_DFI_PHY_LP_STATE_out;
  assign AXI_19_DFI_RST_N_BUF = AXI_19_DFI_RST_N_BUF_out;
  assign AXI_19_RDATA = AXI_19_RDATA_out;
  assign AXI_19_RDATA_PARITY = AXI_19_RDATA_PARITY_out;
  assign AXI_19_RID = AXI_19_RID_out;
  assign AXI_19_RLAST = AXI_19_RLAST_out;
  assign AXI_19_RRESP = AXI_19_RRESP_out;
  assign AXI_19_RVALID = AXI_19_RVALID_out;
  assign AXI_19_WREADY = AXI_19_WREADY_out;
  assign AXI_20_ARREADY = AXI_20_ARREADY_out;
  assign AXI_20_AWREADY = AXI_20_AWREADY_out;
  assign AXI_20_BID = AXI_20_BID_out;
  assign AXI_20_BRESP = AXI_20_BRESP_out;
  assign AXI_20_BVALID = AXI_20_BVALID_out;
  assign AXI_20_DFI_AW_AERR_N = AXI_20_DFI_AW_AERR_N_out;
  assign AXI_20_DFI_CLK_BUF = AXI_20_DFI_CLK_BUF_out;
  assign AXI_20_DFI_DBI_BYTE_DISABLE = AXI_20_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_20_DFI_DW_RDDATA_DBI = AXI_20_DFI_DW_RDDATA_DBI_out;
  assign AXI_20_DFI_DW_RDDATA_DERR = AXI_20_DFI_DW_RDDATA_DERR_out;
  assign AXI_20_DFI_DW_RDDATA_VALID = AXI_20_DFI_DW_RDDATA_VALID_out;
  assign AXI_20_DFI_INIT_COMPLETE = AXI_20_DFI_INIT_COMPLETE_out;
  assign AXI_20_DFI_PHYUPD_REQ = AXI_20_DFI_PHYUPD_REQ_out;
  assign AXI_20_DFI_PHY_LP_STATE = AXI_20_DFI_PHY_LP_STATE_out;
  assign AXI_20_DFI_RST_N_BUF = AXI_20_DFI_RST_N_BUF_out;
  assign AXI_20_MC_STATUS = AXI_20_MC_STATUS_out;
  assign AXI_20_PHY_STATUS = AXI_20_PHY_STATUS_out;
  assign AXI_20_RDATA = AXI_20_RDATA_out;
  assign AXI_20_RDATA_PARITY = AXI_20_RDATA_PARITY_out;
  assign AXI_20_RID = AXI_20_RID_out;
  assign AXI_20_RLAST = AXI_20_RLAST_out;
  assign AXI_20_RRESP = AXI_20_RRESP_out;
  assign AXI_20_RVALID = AXI_20_RVALID_out;
  assign AXI_20_WREADY = AXI_20_WREADY_out;
  assign AXI_21_ARREADY = AXI_21_ARREADY_out;
  assign AXI_21_AWREADY = AXI_21_AWREADY_out;
  assign AXI_21_BID = AXI_21_BID_out;
  assign AXI_21_BRESP = AXI_21_BRESP_out;
  assign AXI_21_BVALID = AXI_21_BVALID_out;
  assign AXI_21_DFI_AW_AERR_N = AXI_21_DFI_AW_AERR_N_out;
  assign AXI_21_DFI_CLK_BUF = AXI_21_DFI_CLK_BUF_out;
  assign AXI_21_DFI_DBI_BYTE_DISABLE = AXI_21_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_21_DFI_DW_RDDATA_DBI = AXI_21_DFI_DW_RDDATA_DBI_out;
  assign AXI_21_DFI_DW_RDDATA_DERR = AXI_21_DFI_DW_RDDATA_DERR_out;
  assign AXI_21_DFI_DW_RDDATA_VALID = AXI_21_DFI_DW_RDDATA_VALID_out;
  assign AXI_21_DFI_INIT_COMPLETE = AXI_21_DFI_INIT_COMPLETE_out;
  assign AXI_21_DFI_PHYUPD_REQ = AXI_21_DFI_PHYUPD_REQ_out;
  assign AXI_21_DFI_PHY_LP_STATE = AXI_21_DFI_PHY_LP_STATE_out;
  assign AXI_21_DFI_RST_N_BUF = AXI_21_DFI_RST_N_BUF_out;
  assign AXI_21_RDATA = AXI_21_RDATA_out;
  assign AXI_21_RDATA_PARITY = AXI_21_RDATA_PARITY_out;
  assign AXI_21_RID = AXI_21_RID_out;
  assign AXI_21_RLAST = AXI_21_RLAST_out;
  assign AXI_21_RRESP = AXI_21_RRESP_out;
  assign AXI_21_RVALID = AXI_21_RVALID_out;
  assign AXI_21_WREADY = AXI_21_WREADY_out;
  assign AXI_22_ARREADY = AXI_22_ARREADY_out;
  assign AXI_22_AWREADY = AXI_22_AWREADY_out;
  assign AXI_22_BID = AXI_22_BID_out;
  assign AXI_22_BRESP = AXI_22_BRESP_out;
  assign AXI_22_BVALID = AXI_22_BVALID_out;
  assign AXI_22_DFI_AW_AERR_N = AXI_22_DFI_AW_AERR_N_out;
  assign AXI_22_DFI_CLK_BUF = AXI_22_DFI_CLK_BUF_out;
  assign AXI_22_DFI_DBI_BYTE_DISABLE = AXI_22_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_22_DFI_DW_RDDATA_DBI = AXI_22_DFI_DW_RDDATA_DBI_out;
  assign AXI_22_DFI_DW_RDDATA_DERR = AXI_22_DFI_DW_RDDATA_DERR_out;
  assign AXI_22_DFI_DW_RDDATA_VALID = AXI_22_DFI_DW_RDDATA_VALID_out;
  assign AXI_22_DFI_INIT_COMPLETE = AXI_22_DFI_INIT_COMPLETE_out;
  assign AXI_22_DFI_PHYUPD_REQ = AXI_22_DFI_PHYUPD_REQ_out;
  assign AXI_22_DFI_PHY_LP_STATE = AXI_22_DFI_PHY_LP_STATE_out;
  assign AXI_22_DFI_RST_N_BUF = AXI_22_DFI_RST_N_BUF_out;
  assign AXI_22_MC_STATUS = AXI_22_MC_STATUS_out;
  assign AXI_22_PHY_STATUS = AXI_22_PHY_STATUS_out;
  assign AXI_22_RDATA = AXI_22_RDATA_out;
  assign AXI_22_RDATA_PARITY = AXI_22_RDATA_PARITY_out;
  assign AXI_22_RID = AXI_22_RID_out;
  assign AXI_22_RLAST = AXI_22_RLAST_out;
  assign AXI_22_RRESP = AXI_22_RRESP_out;
  assign AXI_22_RVALID = AXI_22_RVALID_out;
  assign AXI_22_WREADY = AXI_22_WREADY_out;
  assign AXI_23_ARREADY = AXI_23_ARREADY_out;
  assign AXI_23_AWREADY = AXI_23_AWREADY_out;
  assign AXI_23_BID = AXI_23_BID_out;
  assign AXI_23_BRESP = AXI_23_BRESP_out;
  assign AXI_23_BVALID = AXI_23_BVALID_out;
  assign AXI_23_DFI_AW_AERR_N = AXI_23_DFI_AW_AERR_N_out;
  assign AXI_23_DFI_CLK_BUF = AXI_23_DFI_CLK_BUF_out;
  assign AXI_23_DFI_DBI_BYTE_DISABLE = AXI_23_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_23_DFI_DW_RDDATA_DBI = AXI_23_DFI_DW_RDDATA_DBI_out;
  assign AXI_23_DFI_DW_RDDATA_DERR = AXI_23_DFI_DW_RDDATA_DERR_out;
  assign AXI_23_DFI_DW_RDDATA_VALID = AXI_23_DFI_DW_RDDATA_VALID_out;
  assign AXI_23_DFI_INIT_COMPLETE = AXI_23_DFI_INIT_COMPLETE_out;
  assign AXI_23_DFI_PHYUPD_REQ = AXI_23_DFI_PHYUPD_REQ_out;
  assign AXI_23_DFI_PHY_LP_STATE = AXI_23_DFI_PHY_LP_STATE_out;
  assign AXI_23_DFI_RST_N_BUF = AXI_23_DFI_RST_N_BUF_out;
  assign AXI_23_RDATA = AXI_23_RDATA_out;
  assign AXI_23_RDATA_PARITY = AXI_23_RDATA_PARITY_out;
  assign AXI_23_RID = AXI_23_RID_out;
  assign AXI_23_RLAST = AXI_23_RLAST_out;
  assign AXI_23_RRESP = AXI_23_RRESP_out;
  assign AXI_23_RVALID = AXI_23_RVALID_out;
  assign AXI_23_WREADY = AXI_23_WREADY_out;
  assign AXI_24_ARREADY = AXI_24_ARREADY_out;
  assign AXI_24_AWREADY = AXI_24_AWREADY_out;
  assign AXI_24_BID = AXI_24_BID_out;
  assign AXI_24_BRESP = AXI_24_BRESP_out;
  assign AXI_24_BVALID = AXI_24_BVALID_out;
  assign AXI_24_DFI_AW_AERR_N = AXI_24_DFI_AW_AERR_N_out;
  assign AXI_24_DFI_CLK_BUF = AXI_24_DFI_CLK_BUF_out;
  assign AXI_24_DFI_DBI_BYTE_DISABLE = AXI_24_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_24_DFI_DW_RDDATA_DBI = AXI_24_DFI_DW_RDDATA_DBI_out;
  assign AXI_24_DFI_DW_RDDATA_DERR = AXI_24_DFI_DW_RDDATA_DERR_out;
  assign AXI_24_DFI_DW_RDDATA_VALID = AXI_24_DFI_DW_RDDATA_VALID_out;
  assign AXI_24_DFI_INIT_COMPLETE = AXI_24_DFI_INIT_COMPLETE_out;
  assign AXI_24_DFI_PHYUPD_REQ = AXI_24_DFI_PHYUPD_REQ_out;
  assign AXI_24_DFI_PHY_LP_STATE = AXI_24_DFI_PHY_LP_STATE_out;
  assign AXI_24_DFI_RST_N_BUF = AXI_24_DFI_RST_N_BUF_out;
  assign AXI_24_MC_STATUS = AXI_24_MC_STATUS_out;
  assign AXI_24_PHY_STATUS = AXI_24_PHY_STATUS_out;
  assign AXI_24_RDATA = AXI_24_RDATA_out;
  assign AXI_24_RDATA_PARITY = AXI_24_RDATA_PARITY_out;
  assign AXI_24_RID = AXI_24_RID_out;
  assign AXI_24_RLAST = AXI_24_RLAST_out;
  assign AXI_24_RRESP = AXI_24_RRESP_out;
  assign AXI_24_RVALID = AXI_24_RVALID_out;
  assign AXI_24_WREADY = AXI_24_WREADY_out;
  assign AXI_25_ARREADY = AXI_25_ARREADY_out;
  assign AXI_25_AWREADY = AXI_25_AWREADY_out;
  assign AXI_25_BID = AXI_25_BID_out;
  assign AXI_25_BRESP = AXI_25_BRESP_out;
  assign AXI_25_BVALID = AXI_25_BVALID_out;
  assign AXI_25_DFI_AW_AERR_N = AXI_25_DFI_AW_AERR_N_out;
  assign AXI_25_DFI_CLK_BUF = AXI_25_DFI_CLK_BUF_out;
  assign AXI_25_DFI_DBI_BYTE_DISABLE = AXI_25_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_25_DFI_DW_RDDATA_DBI = AXI_25_DFI_DW_RDDATA_DBI_out;
  assign AXI_25_DFI_DW_RDDATA_DERR = AXI_25_DFI_DW_RDDATA_DERR_out;
  assign AXI_25_DFI_DW_RDDATA_VALID = AXI_25_DFI_DW_RDDATA_VALID_out;
  assign AXI_25_DFI_INIT_COMPLETE = AXI_25_DFI_INIT_COMPLETE_out;
  assign AXI_25_DFI_PHYUPD_REQ = AXI_25_DFI_PHYUPD_REQ_out;
  assign AXI_25_DFI_PHY_LP_STATE = AXI_25_DFI_PHY_LP_STATE_out;
  assign AXI_25_DFI_RST_N_BUF = AXI_25_DFI_RST_N_BUF_out;
  assign AXI_25_RDATA = AXI_25_RDATA_out;
  assign AXI_25_RDATA_PARITY = AXI_25_RDATA_PARITY_out;
  assign AXI_25_RID = AXI_25_RID_out;
  assign AXI_25_RLAST = AXI_25_RLAST_out;
  assign AXI_25_RRESP = AXI_25_RRESP_out;
  assign AXI_25_RVALID = AXI_25_RVALID_out;
  assign AXI_25_WREADY = AXI_25_WREADY_out;
  assign AXI_26_ARREADY = AXI_26_ARREADY_out;
  assign AXI_26_AWREADY = AXI_26_AWREADY_out;
  assign AXI_26_BID = AXI_26_BID_out;
  assign AXI_26_BRESP = AXI_26_BRESP_out;
  assign AXI_26_BVALID = AXI_26_BVALID_out;
  assign AXI_26_DFI_AW_AERR_N = AXI_26_DFI_AW_AERR_N_out;
  assign AXI_26_DFI_CLK_BUF = AXI_26_DFI_CLK_BUF_out;
  assign AXI_26_DFI_DBI_BYTE_DISABLE = AXI_26_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_26_DFI_DW_RDDATA_DBI = AXI_26_DFI_DW_RDDATA_DBI_out;
  assign AXI_26_DFI_DW_RDDATA_DERR = AXI_26_DFI_DW_RDDATA_DERR_out;
  assign AXI_26_DFI_DW_RDDATA_VALID = AXI_26_DFI_DW_RDDATA_VALID_out;
  assign AXI_26_DFI_INIT_COMPLETE = AXI_26_DFI_INIT_COMPLETE_out;
  assign AXI_26_DFI_PHYUPD_REQ = AXI_26_DFI_PHYUPD_REQ_out;
  assign AXI_26_DFI_PHY_LP_STATE = AXI_26_DFI_PHY_LP_STATE_out;
  assign AXI_26_DFI_RST_N_BUF = AXI_26_DFI_RST_N_BUF_out;
  assign AXI_26_MC_STATUS = AXI_26_MC_STATUS_out;
  assign AXI_26_PHY_STATUS = AXI_26_PHY_STATUS_out;
  assign AXI_26_RDATA = AXI_26_RDATA_out;
  assign AXI_26_RDATA_PARITY = AXI_26_RDATA_PARITY_out;
  assign AXI_26_RID = AXI_26_RID_out;
  assign AXI_26_RLAST = AXI_26_RLAST_out;
  assign AXI_26_RRESP = AXI_26_RRESP_out;
  assign AXI_26_RVALID = AXI_26_RVALID_out;
  assign AXI_26_WREADY = AXI_26_WREADY_out;
  assign AXI_27_ARREADY = AXI_27_ARREADY_out;
  assign AXI_27_AWREADY = AXI_27_AWREADY_out;
  assign AXI_27_BID = AXI_27_BID_out;
  assign AXI_27_BRESP = AXI_27_BRESP_out;
  assign AXI_27_BVALID = AXI_27_BVALID_out;
  assign AXI_27_DFI_AW_AERR_N = AXI_27_DFI_AW_AERR_N_out;
  assign AXI_27_DFI_CLK_BUF = AXI_27_DFI_CLK_BUF_out;
  assign AXI_27_DFI_DBI_BYTE_DISABLE = AXI_27_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_27_DFI_DW_RDDATA_DBI = AXI_27_DFI_DW_RDDATA_DBI_out;
  assign AXI_27_DFI_DW_RDDATA_DERR = AXI_27_DFI_DW_RDDATA_DERR_out;
  assign AXI_27_DFI_DW_RDDATA_VALID = AXI_27_DFI_DW_RDDATA_VALID_out;
  assign AXI_27_DFI_INIT_COMPLETE = AXI_27_DFI_INIT_COMPLETE_out;
  assign AXI_27_DFI_PHYUPD_REQ = AXI_27_DFI_PHYUPD_REQ_out;
  assign AXI_27_DFI_PHY_LP_STATE = AXI_27_DFI_PHY_LP_STATE_out;
  assign AXI_27_DFI_RST_N_BUF = AXI_27_DFI_RST_N_BUF_out;
  assign AXI_27_RDATA = AXI_27_RDATA_out;
  assign AXI_27_RDATA_PARITY = AXI_27_RDATA_PARITY_out;
  assign AXI_27_RID = AXI_27_RID_out;
  assign AXI_27_RLAST = AXI_27_RLAST_out;
  assign AXI_27_RRESP = AXI_27_RRESP_out;
  assign AXI_27_RVALID = AXI_27_RVALID_out;
  assign AXI_27_WREADY = AXI_27_WREADY_out;
  assign AXI_28_ARREADY = AXI_28_ARREADY_out;
  assign AXI_28_AWREADY = AXI_28_AWREADY_out;
  assign AXI_28_BID = AXI_28_BID_out;
  assign AXI_28_BRESP = AXI_28_BRESP_out;
  assign AXI_28_BVALID = AXI_28_BVALID_out;
  assign AXI_28_DFI_AW_AERR_N = AXI_28_DFI_AW_AERR_N_out;
  assign AXI_28_DFI_CLK_BUF = AXI_28_DFI_CLK_BUF_out;
  assign AXI_28_DFI_DBI_BYTE_DISABLE = AXI_28_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_28_DFI_DW_RDDATA_DBI = AXI_28_DFI_DW_RDDATA_DBI_out;
  assign AXI_28_DFI_DW_RDDATA_DERR = AXI_28_DFI_DW_RDDATA_DERR_out;
  assign AXI_28_DFI_DW_RDDATA_VALID = AXI_28_DFI_DW_RDDATA_VALID_out;
  assign AXI_28_DFI_INIT_COMPLETE = AXI_28_DFI_INIT_COMPLETE_out;
  assign AXI_28_DFI_PHYUPD_REQ = AXI_28_DFI_PHYUPD_REQ_out;
  assign AXI_28_DFI_PHY_LP_STATE = AXI_28_DFI_PHY_LP_STATE_out;
  assign AXI_28_DFI_RST_N_BUF = AXI_28_DFI_RST_N_BUF_out;
  assign AXI_28_MC_STATUS = AXI_28_MC_STATUS_out;
  assign AXI_28_PHY_STATUS = AXI_28_PHY_STATUS_out;
  assign AXI_28_RDATA = AXI_28_RDATA_out;
  assign AXI_28_RDATA_PARITY = AXI_28_RDATA_PARITY_out;
  assign AXI_28_RID = AXI_28_RID_out;
  assign AXI_28_RLAST = AXI_28_RLAST_out;
  assign AXI_28_RRESP = AXI_28_RRESP_out;
  assign AXI_28_RVALID = AXI_28_RVALID_out;
  assign AXI_28_WREADY = AXI_28_WREADY_out;
  assign AXI_29_ARREADY = AXI_29_ARREADY_out;
  assign AXI_29_AWREADY = AXI_29_AWREADY_out;
  assign AXI_29_BID = AXI_29_BID_out;
  assign AXI_29_BRESP = AXI_29_BRESP_out;
  assign AXI_29_BVALID = AXI_29_BVALID_out;
  assign AXI_29_DFI_AW_AERR_N = AXI_29_DFI_AW_AERR_N_out;
  assign AXI_29_DFI_CLK_BUF = AXI_29_DFI_CLK_BUF_out;
  assign AXI_29_DFI_DBI_BYTE_DISABLE = AXI_29_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_29_DFI_DW_RDDATA_DBI = AXI_29_DFI_DW_RDDATA_DBI_out;
  assign AXI_29_DFI_DW_RDDATA_DERR = AXI_29_DFI_DW_RDDATA_DERR_out;
  assign AXI_29_DFI_DW_RDDATA_VALID = AXI_29_DFI_DW_RDDATA_VALID_out;
  assign AXI_29_DFI_INIT_COMPLETE = AXI_29_DFI_INIT_COMPLETE_out;
  assign AXI_29_DFI_PHYUPD_REQ = AXI_29_DFI_PHYUPD_REQ_out;
  assign AXI_29_DFI_PHY_LP_STATE = AXI_29_DFI_PHY_LP_STATE_out;
  assign AXI_29_DFI_RST_N_BUF = AXI_29_DFI_RST_N_BUF_out;
  assign AXI_29_RDATA = AXI_29_RDATA_out;
  assign AXI_29_RDATA_PARITY = AXI_29_RDATA_PARITY_out;
  assign AXI_29_RID = AXI_29_RID_out;
  assign AXI_29_RLAST = AXI_29_RLAST_out;
  assign AXI_29_RRESP = AXI_29_RRESP_out;
  assign AXI_29_RVALID = AXI_29_RVALID_out;
  assign AXI_29_WREADY = AXI_29_WREADY_out;
  assign AXI_30_ARREADY = AXI_30_ARREADY_out;
  assign AXI_30_AWREADY = AXI_30_AWREADY_out;
  assign AXI_30_BID = AXI_30_BID_out;
  assign AXI_30_BRESP = AXI_30_BRESP_out;
  assign AXI_30_BVALID = AXI_30_BVALID_out;
  assign AXI_30_DFI_AW_AERR_N = AXI_30_DFI_AW_AERR_N_out;
  assign AXI_30_DFI_CLK_BUF = AXI_30_DFI_CLK_BUF_out;
  assign AXI_30_DFI_DBI_BYTE_DISABLE = AXI_30_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_30_DFI_DW_RDDATA_DBI = AXI_30_DFI_DW_RDDATA_DBI_out;
  assign AXI_30_DFI_DW_RDDATA_DERR = AXI_30_DFI_DW_RDDATA_DERR_out;
  assign AXI_30_DFI_DW_RDDATA_VALID = AXI_30_DFI_DW_RDDATA_VALID_out;
  assign AXI_30_DFI_INIT_COMPLETE = AXI_30_DFI_INIT_COMPLETE_out;
  assign AXI_30_DFI_PHYUPD_REQ = AXI_30_DFI_PHYUPD_REQ_out;
  assign AXI_30_DFI_PHY_LP_STATE = AXI_30_DFI_PHY_LP_STATE_out;
  assign AXI_30_DFI_RST_N_BUF = AXI_30_DFI_RST_N_BUF_out;
  assign AXI_30_MC_STATUS = AXI_30_MC_STATUS_out;
  assign AXI_30_PHY_STATUS = AXI_30_PHY_STATUS_out;
  assign AXI_30_RDATA = AXI_30_RDATA_out;
  assign AXI_30_RDATA_PARITY = AXI_30_RDATA_PARITY_out;
  assign AXI_30_RID = AXI_30_RID_out;
  assign AXI_30_RLAST = AXI_30_RLAST_out;
  assign AXI_30_RRESP = AXI_30_RRESP_out;
  assign AXI_30_RVALID = AXI_30_RVALID_out;
  assign AXI_30_WREADY = AXI_30_WREADY_out;
  assign AXI_31_ARREADY = AXI_31_ARREADY_out;
  assign AXI_31_AWREADY = AXI_31_AWREADY_out;
  assign AXI_31_BID = AXI_31_BID_out;
  assign AXI_31_BRESP = AXI_31_BRESP_out;
  assign AXI_31_BVALID = AXI_31_BVALID_out;
  assign AXI_31_DFI_AW_AERR_N = AXI_31_DFI_AW_AERR_N_out;
  assign AXI_31_DFI_CLK_BUF = AXI_31_DFI_CLK_BUF_out;
  assign AXI_31_DFI_DBI_BYTE_DISABLE = AXI_31_DFI_DBI_BYTE_DISABLE_out;
  assign AXI_31_DFI_DW_RDDATA_DBI = AXI_31_DFI_DW_RDDATA_DBI_out;
  assign AXI_31_DFI_DW_RDDATA_DERR = AXI_31_DFI_DW_RDDATA_DERR_out;
  assign AXI_31_DFI_DW_RDDATA_VALID = AXI_31_DFI_DW_RDDATA_VALID_out;
  assign AXI_31_DFI_INIT_COMPLETE = AXI_31_DFI_INIT_COMPLETE_out;
  assign AXI_31_DFI_PHYUPD_REQ = AXI_31_DFI_PHYUPD_REQ_out;
  assign AXI_31_DFI_PHY_LP_STATE = AXI_31_DFI_PHY_LP_STATE_out;
  assign AXI_31_DFI_RST_N_BUF = AXI_31_DFI_RST_N_BUF_out;
  assign AXI_31_RDATA = AXI_31_RDATA_out;
  assign AXI_31_RDATA_PARITY = AXI_31_RDATA_PARITY_out;
  assign AXI_31_RID = AXI_31_RID_out;
  assign AXI_31_RLAST = AXI_31_RLAST_out;
  assign AXI_31_RRESP = AXI_31_RRESP_out;
  assign AXI_31_RVALID = AXI_31_RVALID_out;
  assign AXI_31_WREADY = AXI_31_WREADY_out;
  assign DRAM_0_STAT_CATTRIP = DRAM_0_STAT_CATTRIP_out;
  assign DRAM_0_STAT_TEMP = DRAM_0_STAT_TEMP_out;
  assign DRAM_1_STAT_CATTRIP = DRAM_1_STAT_CATTRIP_out;
  assign DRAM_1_STAT_TEMP = DRAM_1_STAT_TEMP_out;

  assign APB_0_PADDR_in = APB_0_PADDR;
  assign APB_0_PCLK_in = APB_0_PCLK;
  assign APB_0_PENABLE_in = APB_0_PENABLE;
  assign APB_0_PRESET_N_in = APB_0_PRESET_N;
  assign APB_0_PSEL_in = APB_0_PSEL;
  assign APB_0_PWDATA_in = APB_0_PWDATA;
  assign APB_0_PWRITE_in = APB_0_PWRITE;
  assign APB_1_PADDR_in = APB_1_PADDR;
  assign APB_1_PCLK_in = APB_1_PCLK;
  assign APB_1_PENABLE_in = APB_1_PENABLE;
  assign APB_1_PRESET_N_in = APB_1_PRESET_N;
  assign APB_1_PSEL_in = APB_1_PSEL;
  assign APB_1_PWDATA_in = APB_1_PWDATA;
  assign APB_1_PWRITE_in = APB_1_PWRITE;
  assign AXI_00_ACLK_in = AXI_00_ACLK;
  assign AXI_00_ARADDR_in = AXI_00_ARADDR;
  assign AXI_00_ARBURST_in = AXI_00_ARBURST;
  assign AXI_00_ARESET_N_in = AXI_00_ARESET_N;
  assign AXI_00_ARID_in = AXI_00_ARID;
  assign AXI_00_ARLEN_in = AXI_00_ARLEN;
  assign AXI_00_ARSIZE_in = AXI_00_ARSIZE;
  assign AXI_00_ARVALID_in = AXI_00_ARVALID;
  assign AXI_00_AWADDR_in = AXI_00_AWADDR;
  assign AXI_00_AWBURST_in = AXI_00_AWBURST;
  assign AXI_00_AWID_in = AXI_00_AWID;
  assign AXI_00_AWLEN_in = AXI_00_AWLEN;
  assign AXI_00_AWSIZE_in = AXI_00_AWSIZE;
  assign AXI_00_AWVALID_in = AXI_00_AWVALID;
  assign AXI_00_BREADY_in = AXI_00_BREADY;
  assign AXI_00_DFI_LP_PWR_X_REQ_in = AXI_00_DFI_LP_PWR_X_REQ;
  assign AXI_00_RREADY_in = AXI_00_RREADY;
  assign AXI_00_WDATA_PARITY_in = AXI_00_WDATA_PARITY;
  assign AXI_00_WDATA_in = AXI_00_WDATA;
  assign AXI_00_WLAST_in = AXI_00_WLAST;
  assign AXI_00_WSTRB_in = AXI_00_WSTRB;
  assign AXI_00_WVALID_in = AXI_00_WVALID;
  assign AXI_01_ACLK_in = AXI_01_ACLK;
  assign AXI_01_ARADDR_in = AXI_01_ARADDR;
  assign AXI_01_ARBURST_in = AXI_01_ARBURST;
  assign AXI_01_ARESET_N_in = AXI_01_ARESET_N;
  assign AXI_01_ARID_in = AXI_01_ARID;
  assign AXI_01_ARLEN_in = AXI_01_ARLEN;
  assign AXI_01_ARSIZE_in = AXI_01_ARSIZE;
  assign AXI_01_ARVALID_in = AXI_01_ARVALID;
  assign AXI_01_AWADDR_in = AXI_01_AWADDR;
  assign AXI_01_AWBURST_in = AXI_01_AWBURST;
  assign AXI_01_AWID_in = AXI_01_AWID;
  assign AXI_01_AWLEN_in = AXI_01_AWLEN;
  assign AXI_01_AWSIZE_in = AXI_01_AWSIZE;
  assign AXI_01_AWVALID_in = AXI_01_AWVALID;
  assign AXI_01_BREADY_in = AXI_01_BREADY;
  assign AXI_01_DFI_LP_PWR_X_REQ_in = AXI_01_DFI_LP_PWR_X_REQ;
  assign AXI_01_RREADY_in = AXI_01_RREADY;
  assign AXI_01_WDATA_PARITY_in = AXI_01_WDATA_PARITY;
  assign AXI_01_WDATA_in = AXI_01_WDATA;
  assign AXI_01_WLAST_in = AXI_01_WLAST;
  assign AXI_01_WSTRB_in = AXI_01_WSTRB;
  assign AXI_01_WVALID_in = AXI_01_WVALID;
  assign AXI_02_ACLK_in = AXI_02_ACLK;
  assign AXI_02_ARADDR_in = AXI_02_ARADDR;
  assign AXI_02_ARBURST_in = AXI_02_ARBURST;
  assign AXI_02_ARESET_N_in = AXI_02_ARESET_N;
  assign AXI_02_ARID_in = AXI_02_ARID;
  assign AXI_02_ARLEN_in = AXI_02_ARLEN;
  assign AXI_02_ARSIZE_in = AXI_02_ARSIZE;
  assign AXI_02_ARVALID_in = AXI_02_ARVALID;
  assign AXI_02_AWADDR_in = AXI_02_AWADDR;
  assign AXI_02_AWBURST_in = AXI_02_AWBURST;
  assign AXI_02_AWID_in = AXI_02_AWID;
  assign AXI_02_AWLEN_in = AXI_02_AWLEN;
  assign AXI_02_AWSIZE_in = AXI_02_AWSIZE;
  assign AXI_02_AWVALID_in = AXI_02_AWVALID;
  assign AXI_02_BREADY_in = AXI_02_BREADY;
  assign AXI_02_DFI_LP_PWR_X_REQ_in = AXI_02_DFI_LP_PWR_X_REQ;
  assign AXI_02_RREADY_in = AXI_02_RREADY;
  assign AXI_02_WDATA_PARITY_in = AXI_02_WDATA_PARITY;
  assign AXI_02_WDATA_in = AXI_02_WDATA;
  assign AXI_02_WLAST_in = AXI_02_WLAST;
  assign AXI_02_WSTRB_in = AXI_02_WSTRB;
  assign AXI_02_WVALID_in = AXI_02_WVALID;
  assign AXI_03_ACLK_in = AXI_03_ACLK;
  assign AXI_03_ARADDR_in = AXI_03_ARADDR;
  assign AXI_03_ARBURST_in = AXI_03_ARBURST;
  assign AXI_03_ARESET_N_in = AXI_03_ARESET_N;
  assign AXI_03_ARID_in = AXI_03_ARID;
  assign AXI_03_ARLEN_in = AXI_03_ARLEN;
  assign AXI_03_ARSIZE_in = AXI_03_ARSIZE;
  assign AXI_03_ARVALID_in = AXI_03_ARVALID;
  assign AXI_03_AWADDR_in = AXI_03_AWADDR;
  assign AXI_03_AWBURST_in = AXI_03_AWBURST;
  assign AXI_03_AWID_in = AXI_03_AWID;
  assign AXI_03_AWLEN_in = AXI_03_AWLEN;
  assign AXI_03_AWSIZE_in = AXI_03_AWSIZE;
  assign AXI_03_AWVALID_in = AXI_03_AWVALID;
  assign AXI_03_BREADY_in = AXI_03_BREADY;
  assign AXI_03_DFI_LP_PWR_X_REQ_in = AXI_03_DFI_LP_PWR_X_REQ;
  assign AXI_03_RREADY_in = AXI_03_RREADY;
  assign AXI_03_WDATA_PARITY_in = AXI_03_WDATA_PARITY;
  assign AXI_03_WDATA_in = AXI_03_WDATA;
  assign AXI_03_WLAST_in = AXI_03_WLAST;
  assign AXI_03_WSTRB_in = AXI_03_WSTRB;
  assign AXI_03_WVALID_in = AXI_03_WVALID;
  assign AXI_04_ACLK_in = AXI_04_ACLK;
  assign AXI_04_ARADDR_in = AXI_04_ARADDR;
  assign AXI_04_ARBURST_in = AXI_04_ARBURST;
  assign AXI_04_ARESET_N_in = AXI_04_ARESET_N;
  assign AXI_04_ARID_in = AXI_04_ARID;
  assign AXI_04_ARLEN_in = AXI_04_ARLEN;
  assign AXI_04_ARSIZE_in = AXI_04_ARSIZE;
  assign AXI_04_ARVALID_in = AXI_04_ARVALID;
  assign AXI_04_AWADDR_in = AXI_04_AWADDR;
  assign AXI_04_AWBURST_in = AXI_04_AWBURST;
  assign AXI_04_AWID_in = AXI_04_AWID;
  assign AXI_04_AWLEN_in = AXI_04_AWLEN;
  assign AXI_04_AWSIZE_in = AXI_04_AWSIZE;
  assign AXI_04_AWVALID_in = AXI_04_AWVALID;
  assign AXI_04_BREADY_in = AXI_04_BREADY;
  assign AXI_04_DFI_LP_PWR_X_REQ_in = AXI_04_DFI_LP_PWR_X_REQ;
  assign AXI_04_RREADY_in = AXI_04_RREADY;
  assign AXI_04_WDATA_PARITY_in = AXI_04_WDATA_PARITY;
  assign AXI_04_WDATA_in = AXI_04_WDATA;
  assign AXI_04_WLAST_in = AXI_04_WLAST;
  assign AXI_04_WSTRB_in = AXI_04_WSTRB;
  assign AXI_04_WVALID_in = AXI_04_WVALID;
  assign AXI_05_ACLK_in = AXI_05_ACLK;
  assign AXI_05_ARADDR_in = AXI_05_ARADDR;
  assign AXI_05_ARBURST_in = AXI_05_ARBURST;
  assign AXI_05_ARESET_N_in = AXI_05_ARESET_N;
  assign AXI_05_ARID_in = AXI_05_ARID;
  assign AXI_05_ARLEN_in = AXI_05_ARLEN;
  assign AXI_05_ARSIZE_in = AXI_05_ARSIZE;
  assign AXI_05_ARVALID_in = AXI_05_ARVALID;
  assign AXI_05_AWADDR_in = AXI_05_AWADDR;
  assign AXI_05_AWBURST_in = AXI_05_AWBURST;
  assign AXI_05_AWID_in = AXI_05_AWID;
  assign AXI_05_AWLEN_in = AXI_05_AWLEN;
  assign AXI_05_AWSIZE_in = AXI_05_AWSIZE;
  assign AXI_05_AWVALID_in = AXI_05_AWVALID;
  assign AXI_05_BREADY_in = AXI_05_BREADY;
  assign AXI_05_DFI_LP_PWR_X_REQ_in = AXI_05_DFI_LP_PWR_X_REQ;
  assign AXI_05_RREADY_in = AXI_05_RREADY;
  assign AXI_05_WDATA_PARITY_in = AXI_05_WDATA_PARITY;
  assign AXI_05_WDATA_in = AXI_05_WDATA;
  assign AXI_05_WLAST_in = AXI_05_WLAST;
  assign AXI_05_WSTRB_in = AXI_05_WSTRB;
  assign AXI_05_WVALID_in = AXI_05_WVALID;
  assign AXI_06_ACLK_in = AXI_06_ACLK;
  assign AXI_06_ARADDR_in = AXI_06_ARADDR;
  assign AXI_06_ARBURST_in = AXI_06_ARBURST;
  assign AXI_06_ARESET_N_in = AXI_06_ARESET_N;
  assign AXI_06_ARID_in = AXI_06_ARID;
  assign AXI_06_ARLEN_in = AXI_06_ARLEN;
  assign AXI_06_ARSIZE_in = AXI_06_ARSIZE;
  assign AXI_06_ARVALID_in = AXI_06_ARVALID;
  assign AXI_06_AWADDR_in = AXI_06_AWADDR;
  assign AXI_06_AWBURST_in = AXI_06_AWBURST;
  assign AXI_06_AWID_in = AXI_06_AWID;
  assign AXI_06_AWLEN_in = AXI_06_AWLEN;
  assign AXI_06_AWSIZE_in = AXI_06_AWSIZE;
  assign AXI_06_AWVALID_in = AXI_06_AWVALID;
  assign AXI_06_BREADY_in = AXI_06_BREADY;
  assign AXI_06_DFI_LP_PWR_X_REQ_in = AXI_06_DFI_LP_PWR_X_REQ;
  assign AXI_06_RREADY_in = AXI_06_RREADY;
  assign AXI_06_WDATA_PARITY_in = AXI_06_WDATA_PARITY;
  assign AXI_06_WDATA_in = AXI_06_WDATA;
  assign AXI_06_WLAST_in = AXI_06_WLAST;
  assign AXI_06_WSTRB_in = AXI_06_WSTRB;
  assign AXI_06_WVALID_in = AXI_06_WVALID;
  assign AXI_07_ACLK_in = AXI_07_ACLK;
  assign AXI_07_ARADDR_in = AXI_07_ARADDR;
  assign AXI_07_ARBURST_in = AXI_07_ARBURST;
  assign AXI_07_ARESET_N_in = AXI_07_ARESET_N;
  assign AXI_07_ARID_in = AXI_07_ARID;
  assign AXI_07_ARLEN_in = AXI_07_ARLEN;
  assign AXI_07_ARSIZE_in = AXI_07_ARSIZE;
  assign AXI_07_ARVALID_in = AXI_07_ARVALID;
  assign AXI_07_AWADDR_in = AXI_07_AWADDR;
  assign AXI_07_AWBURST_in = AXI_07_AWBURST;
  assign AXI_07_AWID_in = AXI_07_AWID;
  assign AXI_07_AWLEN_in = AXI_07_AWLEN;
  assign AXI_07_AWSIZE_in = AXI_07_AWSIZE;
  assign AXI_07_AWVALID_in = AXI_07_AWVALID;
  assign AXI_07_BREADY_in = AXI_07_BREADY;
  assign AXI_07_DFI_LP_PWR_X_REQ_in = AXI_07_DFI_LP_PWR_X_REQ;
  assign AXI_07_RREADY_in = AXI_07_RREADY;
  assign AXI_07_WDATA_PARITY_in = AXI_07_WDATA_PARITY;
  assign AXI_07_WDATA_in = AXI_07_WDATA;
  assign AXI_07_WLAST_in = AXI_07_WLAST;
  assign AXI_07_WSTRB_in = AXI_07_WSTRB;
  assign AXI_07_WVALID_in = AXI_07_WVALID;
  assign AXI_08_ACLK_in = AXI_08_ACLK;
  assign AXI_08_ARADDR_in = AXI_08_ARADDR;
  assign AXI_08_ARBURST_in = AXI_08_ARBURST;
  assign AXI_08_ARESET_N_in = AXI_08_ARESET_N;
  assign AXI_08_ARID_in = AXI_08_ARID;
  assign AXI_08_ARLEN_in = AXI_08_ARLEN;
  assign AXI_08_ARSIZE_in = AXI_08_ARSIZE;
  assign AXI_08_ARVALID_in = AXI_08_ARVALID;
  assign AXI_08_AWADDR_in = AXI_08_AWADDR;
  assign AXI_08_AWBURST_in = AXI_08_AWBURST;
  assign AXI_08_AWID_in = AXI_08_AWID;
  assign AXI_08_AWLEN_in = AXI_08_AWLEN;
  assign AXI_08_AWSIZE_in = AXI_08_AWSIZE;
  assign AXI_08_AWVALID_in = AXI_08_AWVALID;
  assign AXI_08_BREADY_in = AXI_08_BREADY;
  assign AXI_08_DFI_LP_PWR_X_REQ_in = AXI_08_DFI_LP_PWR_X_REQ;
  assign AXI_08_RREADY_in = AXI_08_RREADY;
  assign AXI_08_WDATA_PARITY_in = AXI_08_WDATA_PARITY;
  assign AXI_08_WDATA_in = AXI_08_WDATA;
  assign AXI_08_WLAST_in = AXI_08_WLAST;
  assign AXI_08_WSTRB_in = AXI_08_WSTRB;
  assign AXI_08_WVALID_in = AXI_08_WVALID;
  assign AXI_09_ACLK_in = AXI_09_ACLK;
  assign AXI_09_ARADDR_in = AXI_09_ARADDR;
  assign AXI_09_ARBURST_in = AXI_09_ARBURST;
  assign AXI_09_ARESET_N_in = AXI_09_ARESET_N;
  assign AXI_09_ARID_in = AXI_09_ARID;
  assign AXI_09_ARLEN_in = AXI_09_ARLEN;
  assign AXI_09_ARSIZE_in = AXI_09_ARSIZE;
  assign AXI_09_ARVALID_in = AXI_09_ARVALID;
  assign AXI_09_AWADDR_in = AXI_09_AWADDR;
  assign AXI_09_AWBURST_in = AXI_09_AWBURST;
  assign AXI_09_AWID_in = AXI_09_AWID;
  assign AXI_09_AWLEN_in = AXI_09_AWLEN;
  assign AXI_09_AWSIZE_in = AXI_09_AWSIZE;
  assign AXI_09_AWVALID_in = AXI_09_AWVALID;
  assign AXI_09_BREADY_in = AXI_09_BREADY;
  assign AXI_09_DFI_LP_PWR_X_REQ_in = AXI_09_DFI_LP_PWR_X_REQ;
  assign AXI_09_RREADY_in = AXI_09_RREADY;
  assign AXI_09_WDATA_PARITY_in = AXI_09_WDATA_PARITY;
  assign AXI_09_WDATA_in = AXI_09_WDATA;
  assign AXI_09_WLAST_in = AXI_09_WLAST;
  assign AXI_09_WSTRB_in = AXI_09_WSTRB;
  assign AXI_09_WVALID_in = AXI_09_WVALID;
  assign AXI_10_ACLK_in = AXI_10_ACLK;
  assign AXI_10_ARADDR_in = AXI_10_ARADDR;
  assign AXI_10_ARBURST_in = AXI_10_ARBURST;
  assign AXI_10_ARESET_N_in = AXI_10_ARESET_N;
  assign AXI_10_ARID_in = AXI_10_ARID;
  assign AXI_10_ARLEN_in = AXI_10_ARLEN;
  assign AXI_10_ARSIZE_in = AXI_10_ARSIZE;
  assign AXI_10_ARVALID_in = AXI_10_ARVALID;
  assign AXI_10_AWADDR_in = AXI_10_AWADDR;
  assign AXI_10_AWBURST_in = AXI_10_AWBURST;
  assign AXI_10_AWID_in = AXI_10_AWID;
  assign AXI_10_AWLEN_in = AXI_10_AWLEN;
  assign AXI_10_AWSIZE_in = AXI_10_AWSIZE;
  assign AXI_10_AWVALID_in = AXI_10_AWVALID;
  assign AXI_10_BREADY_in = AXI_10_BREADY;
  assign AXI_10_DFI_LP_PWR_X_REQ_in = AXI_10_DFI_LP_PWR_X_REQ;
  assign AXI_10_RREADY_in = AXI_10_RREADY;
  assign AXI_10_WDATA_PARITY_in = AXI_10_WDATA_PARITY;
  assign AXI_10_WDATA_in = AXI_10_WDATA;
  assign AXI_10_WLAST_in = AXI_10_WLAST;
  assign AXI_10_WSTRB_in = AXI_10_WSTRB;
  assign AXI_10_WVALID_in = AXI_10_WVALID;
  assign AXI_11_ACLK_in = AXI_11_ACLK;
  assign AXI_11_ARADDR_in = AXI_11_ARADDR;
  assign AXI_11_ARBURST_in = AXI_11_ARBURST;
  assign AXI_11_ARESET_N_in = AXI_11_ARESET_N;
  assign AXI_11_ARID_in = AXI_11_ARID;
  assign AXI_11_ARLEN_in = AXI_11_ARLEN;
  assign AXI_11_ARSIZE_in = AXI_11_ARSIZE;
  assign AXI_11_ARVALID_in = AXI_11_ARVALID;
  assign AXI_11_AWADDR_in = AXI_11_AWADDR;
  assign AXI_11_AWBURST_in = AXI_11_AWBURST;
  assign AXI_11_AWID_in = AXI_11_AWID;
  assign AXI_11_AWLEN_in = AXI_11_AWLEN;
  assign AXI_11_AWSIZE_in = AXI_11_AWSIZE;
  assign AXI_11_AWVALID_in = AXI_11_AWVALID;
  assign AXI_11_BREADY_in = AXI_11_BREADY;
  assign AXI_11_DFI_LP_PWR_X_REQ_in = AXI_11_DFI_LP_PWR_X_REQ;
  assign AXI_11_RREADY_in = AXI_11_RREADY;
  assign AXI_11_WDATA_PARITY_in = AXI_11_WDATA_PARITY;
  assign AXI_11_WDATA_in = AXI_11_WDATA;
  assign AXI_11_WLAST_in = AXI_11_WLAST;
  assign AXI_11_WSTRB_in = AXI_11_WSTRB;
  assign AXI_11_WVALID_in = AXI_11_WVALID;
  assign AXI_12_ACLK_in = AXI_12_ACLK;
  assign AXI_12_ARADDR_in = AXI_12_ARADDR;
  assign AXI_12_ARBURST_in = AXI_12_ARBURST;
  assign AXI_12_ARESET_N_in = AXI_12_ARESET_N;
  assign AXI_12_ARID_in = AXI_12_ARID;
  assign AXI_12_ARLEN_in = AXI_12_ARLEN;
  assign AXI_12_ARSIZE_in = AXI_12_ARSIZE;
  assign AXI_12_ARVALID_in = AXI_12_ARVALID;
  assign AXI_12_AWADDR_in = AXI_12_AWADDR;
  assign AXI_12_AWBURST_in = AXI_12_AWBURST;
  assign AXI_12_AWID_in = AXI_12_AWID;
  assign AXI_12_AWLEN_in = AXI_12_AWLEN;
  assign AXI_12_AWSIZE_in = AXI_12_AWSIZE;
  assign AXI_12_AWVALID_in = AXI_12_AWVALID;
  assign AXI_12_BREADY_in = AXI_12_BREADY;
  assign AXI_12_DFI_LP_PWR_X_REQ_in = AXI_12_DFI_LP_PWR_X_REQ;
  assign AXI_12_RREADY_in = AXI_12_RREADY;
  assign AXI_12_WDATA_PARITY_in = AXI_12_WDATA_PARITY;
  assign AXI_12_WDATA_in = AXI_12_WDATA;
  assign AXI_12_WLAST_in = AXI_12_WLAST;
  assign AXI_12_WSTRB_in = AXI_12_WSTRB;
  assign AXI_12_WVALID_in = AXI_12_WVALID;
  assign AXI_13_ACLK_in = AXI_13_ACLK;
  assign AXI_13_ARADDR_in = AXI_13_ARADDR;
  assign AXI_13_ARBURST_in = AXI_13_ARBURST;
  assign AXI_13_ARESET_N_in = AXI_13_ARESET_N;
  assign AXI_13_ARID_in = AXI_13_ARID;
  assign AXI_13_ARLEN_in = AXI_13_ARLEN;
  assign AXI_13_ARSIZE_in = AXI_13_ARSIZE;
  assign AXI_13_ARVALID_in = AXI_13_ARVALID;
  assign AXI_13_AWADDR_in = AXI_13_AWADDR;
  assign AXI_13_AWBURST_in = AXI_13_AWBURST;
  assign AXI_13_AWID_in = AXI_13_AWID;
  assign AXI_13_AWLEN_in = AXI_13_AWLEN;
  assign AXI_13_AWSIZE_in = AXI_13_AWSIZE;
  assign AXI_13_AWVALID_in = AXI_13_AWVALID;
  assign AXI_13_BREADY_in = AXI_13_BREADY;
  assign AXI_13_DFI_LP_PWR_X_REQ_in = AXI_13_DFI_LP_PWR_X_REQ;
  assign AXI_13_RREADY_in = AXI_13_RREADY;
  assign AXI_13_WDATA_PARITY_in = AXI_13_WDATA_PARITY;
  assign AXI_13_WDATA_in = AXI_13_WDATA;
  assign AXI_13_WLAST_in = AXI_13_WLAST;
  assign AXI_13_WSTRB_in = AXI_13_WSTRB;
  assign AXI_13_WVALID_in = AXI_13_WVALID;
  assign AXI_14_ACLK_in = AXI_14_ACLK;
  assign AXI_14_ARADDR_in = AXI_14_ARADDR;
  assign AXI_14_ARBURST_in = AXI_14_ARBURST;
  assign AXI_14_ARESET_N_in = AXI_14_ARESET_N;
  assign AXI_14_ARID_in = AXI_14_ARID;
  assign AXI_14_ARLEN_in = AXI_14_ARLEN;
  assign AXI_14_ARSIZE_in = AXI_14_ARSIZE;
  assign AXI_14_ARVALID_in = AXI_14_ARVALID;
  assign AXI_14_AWADDR_in = AXI_14_AWADDR;
  assign AXI_14_AWBURST_in = AXI_14_AWBURST;
  assign AXI_14_AWID_in = AXI_14_AWID;
  assign AXI_14_AWLEN_in = AXI_14_AWLEN;
  assign AXI_14_AWSIZE_in = AXI_14_AWSIZE;
  assign AXI_14_AWVALID_in = AXI_14_AWVALID;
  assign AXI_14_BREADY_in = AXI_14_BREADY;
  assign AXI_14_DFI_LP_PWR_X_REQ_in = AXI_14_DFI_LP_PWR_X_REQ;
  assign AXI_14_RREADY_in = AXI_14_RREADY;
  assign AXI_14_WDATA_PARITY_in = AXI_14_WDATA_PARITY;
  assign AXI_14_WDATA_in = AXI_14_WDATA;
  assign AXI_14_WLAST_in = AXI_14_WLAST;
  assign AXI_14_WSTRB_in = AXI_14_WSTRB;
  assign AXI_14_WVALID_in = AXI_14_WVALID;
  assign AXI_15_ACLK_in = AXI_15_ACLK;
  assign AXI_15_ARADDR_in = AXI_15_ARADDR;
  assign AXI_15_ARBURST_in = AXI_15_ARBURST;
  assign AXI_15_ARESET_N_in = AXI_15_ARESET_N;
  assign AXI_15_ARID_in = AXI_15_ARID;
  assign AXI_15_ARLEN_in = AXI_15_ARLEN;
  assign AXI_15_ARSIZE_in = AXI_15_ARSIZE;
  assign AXI_15_ARVALID_in = AXI_15_ARVALID;
  assign AXI_15_AWADDR_in = AXI_15_AWADDR;
  assign AXI_15_AWBURST_in = AXI_15_AWBURST;
  assign AXI_15_AWID_in = AXI_15_AWID;
  assign AXI_15_AWLEN_in = AXI_15_AWLEN;
  assign AXI_15_AWSIZE_in = AXI_15_AWSIZE;
  assign AXI_15_AWVALID_in = AXI_15_AWVALID;
  assign AXI_15_BREADY_in = AXI_15_BREADY;
  assign AXI_15_DFI_LP_PWR_X_REQ_in = AXI_15_DFI_LP_PWR_X_REQ;
  assign AXI_15_RREADY_in = AXI_15_RREADY;
  assign AXI_15_WDATA_PARITY_in = AXI_15_WDATA_PARITY;
  assign AXI_15_WDATA_in = AXI_15_WDATA;
  assign AXI_15_WLAST_in = AXI_15_WLAST;
  assign AXI_15_WSTRB_in = AXI_15_WSTRB;
  assign AXI_15_WVALID_in = AXI_15_WVALID;
  assign AXI_16_ACLK_in = AXI_16_ACLK;
  assign AXI_16_ARADDR_in = AXI_16_ARADDR;
  assign AXI_16_ARBURST_in = AXI_16_ARBURST;
  assign AXI_16_ARESET_N_in = AXI_16_ARESET_N;
  assign AXI_16_ARID_in = AXI_16_ARID;
  assign AXI_16_ARLEN_in = AXI_16_ARLEN;
  assign AXI_16_ARSIZE_in = AXI_16_ARSIZE;
  assign AXI_16_ARVALID_in = AXI_16_ARVALID;
  assign AXI_16_AWADDR_in = AXI_16_AWADDR;
  assign AXI_16_AWBURST_in = AXI_16_AWBURST;
  assign AXI_16_AWID_in = AXI_16_AWID;
  assign AXI_16_AWLEN_in = AXI_16_AWLEN;
  assign AXI_16_AWSIZE_in = AXI_16_AWSIZE;
  assign AXI_16_AWVALID_in = AXI_16_AWVALID;
  assign AXI_16_BREADY_in = AXI_16_BREADY;
  assign AXI_16_DFI_LP_PWR_X_REQ_in = AXI_16_DFI_LP_PWR_X_REQ;
  assign AXI_16_RREADY_in = AXI_16_RREADY;
  assign AXI_16_WDATA_PARITY_in = AXI_16_WDATA_PARITY;
  assign AXI_16_WDATA_in = AXI_16_WDATA;
  assign AXI_16_WLAST_in = AXI_16_WLAST;
  assign AXI_16_WSTRB_in = AXI_16_WSTRB;
  assign AXI_16_WVALID_in = AXI_16_WVALID;
  assign AXI_17_ACLK_in = AXI_17_ACLK;
  assign AXI_17_ARADDR_in = AXI_17_ARADDR;
  assign AXI_17_ARBURST_in = AXI_17_ARBURST;
  assign AXI_17_ARESET_N_in = AXI_17_ARESET_N;
  assign AXI_17_ARID_in = AXI_17_ARID;
  assign AXI_17_ARLEN_in = AXI_17_ARLEN;
  assign AXI_17_ARSIZE_in = AXI_17_ARSIZE;
  assign AXI_17_ARVALID_in = AXI_17_ARVALID;
  assign AXI_17_AWADDR_in = AXI_17_AWADDR;
  assign AXI_17_AWBURST_in = AXI_17_AWBURST;
  assign AXI_17_AWID_in = AXI_17_AWID;
  assign AXI_17_AWLEN_in = AXI_17_AWLEN;
  assign AXI_17_AWSIZE_in = AXI_17_AWSIZE;
  assign AXI_17_AWVALID_in = AXI_17_AWVALID;
  assign AXI_17_BREADY_in = AXI_17_BREADY;
  assign AXI_17_DFI_LP_PWR_X_REQ_in = AXI_17_DFI_LP_PWR_X_REQ;
  assign AXI_17_RREADY_in = AXI_17_RREADY;
  assign AXI_17_WDATA_PARITY_in = AXI_17_WDATA_PARITY;
  assign AXI_17_WDATA_in = AXI_17_WDATA;
  assign AXI_17_WLAST_in = AXI_17_WLAST;
  assign AXI_17_WSTRB_in = AXI_17_WSTRB;
  assign AXI_17_WVALID_in = AXI_17_WVALID;
  assign AXI_18_ACLK_in = AXI_18_ACLK;
  assign AXI_18_ARADDR_in = AXI_18_ARADDR;
  assign AXI_18_ARBURST_in = AXI_18_ARBURST;
  assign AXI_18_ARESET_N_in = AXI_18_ARESET_N;
  assign AXI_18_ARID_in = AXI_18_ARID;
  assign AXI_18_ARLEN_in = AXI_18_ARLEN;
  assign AXI_18_ARSIZE_in = AXI_18_ARSIZE;
  assign AXI_18_ARVALID_in = AXI_18_ARVALID;
  assign AXI_18_AWADDR_in = AXI_18_AWADDR;
  assign AXI_18_AWBURST_in = AXI_18_AWBURST;
  assign AXI_18_AWID_in = AXI_18_AWID;
  assign AXI_18_AWLEN_in = AXI_18_AWLEN;
  assign AXI_18_AWSIZE_in = AXI_18_AWSIZE;
  assign AXI_18_AWVALID_in = AXI_18_AWVALID;
  assign AXI_18_BREADY_in = AXI_18_BREADY;
  assign AXI_18_DFI_LP_PWR_X_REQ_in = AXI_18_DFI_LP_PWR_X_REQ;
  assign AXI_18_RREADY_in = AXI_18_RREADY;
  assign AXI_18_WDATA_PARITY_in = AXI_18_WDATA_PARITY;
  assign AXI_18_WDATA_in = AXI_18_WDATA;
  assign AXI_18_WLAST_in = AXI_18_WLAST;
  assign AXI_18_WSTRB_in = AXI_18_WSTRB;
  assign AXI_18_WVALID_in = AXI_18_WVALID;
  assign AXI_19_ACLK_in = AXI_19_ACLK;
  assign AXI_19_ARADDR_in = AXI_19_ARADDR;
  assign AXI_19_ARBURST_in = AXI_19_ARBURST;
  assign AXI_19_ARESET_N_in = AXI_19_ARESET_N;
  assign AXI_19_ARID_in = AXI_19_ARID;
  assign AXI_19_ARLEN_in = AXI_19_ARLEN;
  assign AXI_19_ARSIZE_in = AXI_19_ARSIZE;
  assign AXI_19_ARVALID_in = AXI_19_ARVALID;
  assign AXI_19_AWADDR_in = AXI_19_AWADDR;
  assign AXI_19_AWBURST_in = AXI_19_AWBURST;
  assign AXI_19_AWID_in = AXI_19_AWID;
  assign AXI_19_AWLEN_in = AXI_19_AWLEN;
  assign AXI_19_AWSIZE_in = AXI_19_AWSIZE;
  assign AXI_19_AWVALID_in = AXI_19_AWVALID;
  assign AXI_19_BREADY_in = AXI_19_BREADY;
  assign AXI_19_DFI_LP_PWR_X_REQ_in = AXI_19_DFI_LP_PWR_X_REQ;
  assign AXI_19_RREADY_in = AXI_19_RREADY;
  assign AXI_19_WDATA_PARITY_in = AXI_19_WDATA_PARITY;
  assign AXI_19_WDATA_in = AXI_19_WDATA;
  assign AXI_19_WLAST_in = AXI_19_WLAST;
  assign AXI_19_WSTRB_in = AXI_19_WSTRB;
  assign AXI_19_WVALID_in = AXI_19_WVALID;
  assign AXI_20_ACLK_in = AXI_20_ACLK;
  assign AXI_20_ARADDR_in = AXI_20_ARADDR;
  assign AXI_20_ARBURST_in = AXI_20_ARBURST;
  assign AXI_20_ARESET_N_in = AXI_20_ARESET_N;
  assign AXI_20_ARID_in = AXI_20_ARID;
  assign AXI_20_ARLEN_in = AXI_20_ARLEN;
  assign AXI_20_ARSIZE_in = AXI_20_ARSIZE;
  assign AXI_20_ARVALID_in = AXI_20_ARVALID;
  assign AXI_20_AWADDR_in = AXI_20_AWADDR;
  assign AXI_20_AWBURST_in = AXI_20_AWBURST;
  assign AXI_20_AWID_in = AXI_20_AWID;
  assign AXI_20_AWLEN_in = AXI_20_AWLEN;
  assign AXI_20_AWSIZE_in = AXI_20_AWSIZE;
  assign AXI_20_AWVALID_in = AXI_20_AWVALID;
  assign AXI_20_BREADY_in = AXI_20_BREADY;
  assign AXI_20_DFI_LP_PWR_X_REQ_in = AXI_20_DFI_LP_PWR_X_REQ;
  assign AXI_20_RREADY_in = AXI_20_RREADY;
  assign AXI_20_WDATA_PARITY_in = AXI_20_WDATA_PARITY;
  assign AXI_20_WDATA_in = AXI_20_WDATA;
  assign AXI_20_WLAST_in = AXI_20_WLAST;
  assign AXI_20_WSTRB_in = AXI_20_WSTRB;
  assign AXI_20_WVALID_in = AXI_20_WVALID;
  assign AXI_21_ACLK_in = AXI_21_ACLK;
  assign AXI_21_ARADDR_in = AXI_21_ARADDR;
  assign AXI_21_ARBURST_in = AXI_21_ARBURST;
  assign AXI_21_ARESET_N_in = AXI_21_ARESET_N;
  assign AXI_21_ARID_in = AXI_21_ARID;
  assign AXI_21_ARLEN_in = AXI_21_ARLEN;
  assign AXI_21_ARSIZE_in = AXI_21_ARSIZE;
  assign AXI_21_ARVALID_in = AXI_21_ARVALID;
  assign AXI_21_AWADDR_in = AXI_21_AWADDR;
  assign AXI_21_AWBURST_in = AXI_21_AWBURST;
  assign AXI_21_AWID_in = AXI_21_AWID;
  assign AXI_21_AWLEN_in = AXI_21_AWLEN;
  assign AXI_21_AWSIZE_in = AXI_21_AWSIZE;
  assign AXI_21_AWVALID_in = AXI_21_AWVALID;
  assign AXI_21_BREADY_in = AXI_21_BREADY;
  assign AXI_21_DFI_LP_PWR_X_REQ_in = AXI_21_DFI_LP_PWR_X_REQ;
  assign AXI_21_RREADY_in = AXI_21_RREADY;
  assign AXI_21_WDATA_PARITY_in = AXI_21_WDATA_PARITY;
  assign AXI_21_WDATA_in = AXI_21_WDATA;
  assign AXI_21_WLAST_in = AXI_21_WLAST;
  assign AXI_21_WSTRB_in = AXI_21_WSTRB;
  assign AXI_21_WVALID_in = AXI_21_WVALID;
  assign AXI_22_ACLK_in = AXI_22_ACLK;
  assign AXI_22_ARADDR_in = AXI_22_ARADDR;
  assign AXI_22_ARBURST_in = AXI_22_ARBURST;
  assign AXI_22_ARESET_N_in = AXI_22_ARESET_N;
  assign AXI_22_ARID_in = AXI_22_ARID;
  assign AXI_22_ARLEN_in = AXI_22_ARLEN;
  assign AXI_22_ARSIZE_in = AXI_22_ARSIZE;
  assign AXI_22_ARVALID_in = AXI_22_ARVALID;
  assign AXI_22_AWADDR_in = AXI_22_AWADDR;
  assign AXI_22_AWBURST_in = AXI_22_AWBURST;
  assign AXI_22_AWID_in = AXI_22_AWID;
  assign AXI_22_AWLEN_in = AXI_22_AWLEN;
  assign AXI_22_AWSIZE_in = AXI_22_AWSIZE;
  assign AXI_22_AWVALID_in = AXI_22_AWVALID;
  assign AXI_22_BREADY_in = AXI_22_BREADY;
  assign AXI_22_DFI_LP_PWR_X_REQ_in = AXI_22_DFI_LP_PWR_X_REQ;
  assign AXI_22_RREADY_in = AXI_22_RREADY;
  assign AXI_22_WDATA_PARITY_in = AXI_22_WDATA_PARITY;
  assign AXI_22_WDATA_in = AXI_22_WDATA;
  assign AXI_22_WLAST_in = AXI_22_WLAST;
  assign AXI_22_WSTRB_in = AXI_22_WSTRB;
  assign AXI_22_WVALID_in = AXI_22_WVALID;
  assign AXI_23_ACLK_in = AXI_23_ACLK;
  assign AXI_23_ARADDR_in = AXI_23_ARADDR;
  assign AXI_23_ARBURST_in = AXI_23_ARBURST;
  assign AXI_23_ARESET_N_in = AXI_23_ARESET_N;
  assign AXI_23_ARID_in = AXI_23_ARID;
  assign AXI_23_ARLEN_in = AXI_23_ARLEN;
  assign AXI_23_ARSIZE_in = AXI_23_ARSIZE;
  assign AXI_23_ARVALID_in = AXI_23_ARVALID;
  assign AXI_23_AWADDR_in = AXI_23_AWADDR;
  assign AXI_23_AWBURST_in = AXI_23_AWBURST;
  assign AXI_23_AWID_in = AXI_23_AWID;
  assign AXI_23_AWLEN_in = AXI_23_AWLEN;
  assign AXI_23_AWSIZE_in = AXI_23_AWSIZE;
  assign AXI_23_AWVALID_in = AXI_23_AWVALID;
  assign AXI_23_BREADY_in = AXI_23_BREADY;
  assign AXI_23_DFI_LP_PWR_X_REQ_in = AXI_23_DFI_LP_PWR_X_REQ;
  assign AXI_23_RREADY_in = AXI_23_RREADY;
  assign AXI_23_WDATA_PARITY_in = AXI_23_WDATA_PARITY;
  assign AXI_23_WDATA_in = AXI_23_WDATA;
  assign AXI_23_WLAST_in = AXI_23_WLAST;
  assign AXI_23_WSTRB_in = AXI_23_WSTRB;
  assign AXI_23_WVALID_in = AXI_23_WVALID;
  assign AXI_24_ACLK_in = AXI_24_ACLK;
  assign AXI_24_ARADDR_in = AXI_24_ARADDR;
  assign AXI_24_ARBURST_in = AXI_24_ARBURST;
  assign AXI_24_ARESET_N_in = AXI_24_ARESET_N;
  assign AXI_24_ARID_in = AXI_24_ARID;
  assign AXI_24_ARLEN_in = AXI_24_ARLEN;
  assign AXI_24_ARSIZE_in = AXI_24_ARSIZE;
  assign AXI_24_ARVALID_in = AXI_24_ARVALID;
  assign AXI_24_AWADDR_in = AXI_24_AWADDR;
  assign AXI_24_AWBURST_in = AXI_24_AWBURST;
  assign AXI_24_AWID_in = AXI_24_AWID;
  assign AXI_24_AWLEN_in = AXI_24_AWLEN;
  assign AXI_24_AWSIZE_in = AXI_24_AWSIZE;
  assign AXI_24_AWVALID_in = AXI_24_AWVALID;
  assign AXI_24_BREADY_in = AXI_24_BREADY;
  assign AXI_24_DFI_LP_PWR_X_REQ_in = AXI_24_DFI_LP_PWR_X_REQ;
  assign AXI_24_RREADY_in = AXI_24_RREADY;
  assign AXI_24_WDATA_PARITY_in = AXI_24_WDATA_PARITY;
  assign AXI_24_WDATA_in = AXI_24_WDATA;
  assign AXI_24_WLAST_in = AXI_24_WLAST;
  assign AXI_24_WSTRB_in = AXI_24_WSTRB;
  assign AXI_24_WVALID_in = AXI_24_WVALID;
  assign AXI_25_ACLK_in = AXI_25_ACLK;
  assign AXI_25_ARADDR_in = AXI_25_ARADDR;
  assign AXI_25_ARBURST_in = AXI_25_ARBURST;
  assign AXI_25_ARESET_N_in = AXI_25_ARESET_N;
  assign AXI_25_ARID_in = AXI_25_ARID;
  assign AXI_25_ARLEN_in = AXI_25_ARLEN;
  assign AXI_25_ARSIZE_in = AXI_25_ARSIZE;
  assign AXI_25_ARVALID_in = AXI_25_ARVALID;
  assign AXI_25_AWADDR_in = AXI_25_AWADDR;
  assign AXI_25_AWBURST_in = AXI_25_AWBURST;
  assign AXI_25_AWID_in = AXI_25_AWID;
  assign AXI_25_AWLEN_in = AXI_25_AWLEN;
  assign AXI_25_AWSIZE_in = AXI_25_AWSIZE;
  assign AXI_25_AWVALID_in = AXI_25_AWVALID;
  assign AXI_25_BREADY_in = AXI_25_BREADY;
  assign AXI_25_DFI_LP_PWR_X_REQ_in = AXI_25_DFI_LP_PWR_X_REQ;
  assign AXI_25_RREADY_in = AXI_25_RREADY;
  assign AXI_25_WDATA_PARITY_in = AXI_25_WDATA_PARITY;
  assign AXI_25_WDATA_in = AXI_25_WDATA;
  assign AXI_25_WLAST_in = AXI_25_WLAST;
  assign AXI_25_WSTRB_in = AXI_25_WSTRB;
  assign AXI_25_WVALID_in = AXI_25_WVALID;
  assign AXI_26_ACLK_in = AXI_26_ACLK;
  assign AXI_26_ARADDR_in = AXI_26_ARADDR;
  assign AXI_26_ARBURST_in = AXI_26_ARBURST;
  assign AXI_26_ARESET_N_in = AXI_26_ARESET_N;
  assign AXI_26_ARID_in = AXI_26_ARID;
  assign AXI_26_ARLEN_in = AXI_26_ARLEN;
  assign AXI_26_ARSIZE_in = AXI_26_ARSIZE;
  assign AXI_26_ARVALID_in = AXI_26_ARVALID;
  assign AXI_26_AWADDR_in = AXI_26_AWADDR;
  assign AXI_26_AWBURST_in = AXI_26_AWBURST;
  assign AXI_26_AWID_in = AXI_26_AWID;
  assign AXI_26_AWLEN_in = AXI_26_AWLEN;
  assign AXI_26_AWSIZE_in = AXI_26_AWSIZE;
  assign AXI_26_AWVALID_in = AXI_26_AWVALID;
  assign AXI_26_BREADY_in = AXI_26_BREADY;
  assign AXI_26_DFI_LP_PWR_X_REQ_in = AXI_26_DFI_LP_PWR_X_REQ;
  assign AXI_26_RREADY_in = AXI_26_RREADY;
  assign AXI_26_WDATA_PARITY_in = AXI_26_WDATA_PARITY;
  assign AXI_26_WDATA_in = AXI_26_WDATA;
  assign AXI_26_WLAST_in = AXI_26_WLAST;
  assign AXI_26_WSTRB_in = AXI_26_WSTRB;
  assign AXI_26_WVALID_in = AXI_26_WVALID;
  assign AXI_27_ACLK_in = AXI_27_ACLK;
  assign AXI_27_ARADDR_in = AXI_27_ARADDR;
  assign AXI_27_ARBURST_in = AXI_27_ARBURST;
  assign AXI_27_ARESET_N_in = AXI_27_ARESET_N;
  assign AXI_27_ARID_in = AXI_27_ARID;
  assign AXI_27_ARLEN_in = AXI_27_ARLEN;
  assign AXI_27_ARSIZE_in = AXI_27_ARSIZE;
  assign AXI_27_ARVALID_in = AXI_27_ARVALID;
  assign AXI_27_AWADDR_in = AXI_27_AWADDR;
  assign AXI_27_AWBURST_in = AXI_27_AWBURST;
  assign AXI_27_AWID_in = AXI_27_AWID;
  assign AXI_27_AWLEN_in = AXI_27_AWLEN;
  assign AXI_27_AWSIZE_in = AXI_27_AWSIZE;
  assign AXI_27_AWVALID_in = AXI_27_AWVALID;
  assign AXI_27_BREADY_in = AXI_27_BREADY;
  assign AXI_27_DFI_LP_PWR_X_REQ_in = AXI_27_DFI_LP_PWR_X_REQ;
  assign AXI_27_RREADY_in = AXI_27_RREADY;
  assign AXI_27_WDATA_PARITY_in = AXI_27_WDATA_PARITY;
  assign AXI_27_WDATA_in = AXI_27_WDATA;
  assign AXI_27_WLAST_in = AXI_27_WLAST;
  assign AXI_27_WSTRB_in = AXI_27_WSTRB;
  assign AXI_27_WVALID_in = AXI_27_WVALID;
  assign AXI_28_ACLK_in = AXI_28_ACLK;
  assign AXI_28_ARADDR_in = AXI_28_ARADDR;
  assign AXI_28_ARBURST_in = AXI_28_ARBURST;
  assign AXI_28_ARESET_N_in = AXI_28_ARESET_N;
  assign AXI_28_ARID_in = AXI_28_ARID;
  assign AXI_28_ARLEN_in = AXI_28_ARLEN;
  assign AXI_28_ARSIZE_in = AXI_28_ARSIZE;
  assign AXI_28_ARVALID_in = AXI_28_ARVALID;
  assign AXI_28_AWADDR_in = AXI_28_AWADDR;
  assign AXI_28_AWBURST_in = AXI_28_AWBURST;
  assign AXI_28_AWID_in = AXI_28_AWID;
  assign AXI_28_AWLEN_in = AXI_28_AWLEN;
  assign AXI_28_AWSIZE_in = AXI_28_AWSIZE;
  assign AXI_28_AWVALID_in = AXI_28_AWVALID;
  assign AXI_28_BREADY_in = AXI_28_BREADY;
  assign AXI_28_DFI_LP_PWR_X_REQ_in = AXI_28_DFI_LP_PWR_X_REQ;
  assign AXI_28_RREADY_in = AXI_28_RREADY;
  assign AXI_28_WDATA_PARITY_in = AXI_28_WDATA_PARITY;
  assign AXI_28_WDATA_in = AXI_28_WDATA;
  assign AXI_28_WLAST_in = AXI_28_WLAST;
  assign AXI_28_WSTRB_in = AXI_28_WSTRB;
  assign AXI_28_WVALID_in = AXI_28_WVALID;
  assign AXI_29_ACLK_in = AXI_29_ACLK;
  assign AXI_29_ARADDR_in = AXI_29_ARADDR;
  assign AXI_29_ARBURST_in = AXI_29_ARBURST;
  assign AXI_29_ARESET_N_in = AXI_29_ARESET_N;
  assign AXI_29_ARID_in = AXI_29_ARID;
  assign AXI_29_ARLEN_in = AXI_29_ARLEN;
  assign AXI_29_ARSIZE_in = AXI_29_ARSIZE;
  assign AXI_29_ARVALID_in = AXI_29_ARVALID;
  assign AXI_29_AWADDR_in = AXI_29_AWADDR;
  assign AXI_29_AWBURST_in = AXI_29_AWBURST;
  assign AXI_29_AWID_in = AXI_29_AWID;
  assign AXI_29_AWLEN_in = AXI_29_AWLEN;
  assign AXI_29_AWSIZE_in = AXI_29_AWSIZE;
  assign AXI_29_AWVALID_in = AXI_29_AWVALID;
  assign AXI_29_BREADY_in = AXI_29_BREADY;
  assign AXI_29_DFI_LP_PWR_X_REQ_in = AXI_29_DFI_LP_PWR_X_REQ;
  assign AXI_29_RREADY_in = AXI_29_RREADY;
  assign AXI_29_WDATA_PARITY_in = AXI_29_WDATA_PARITY;
  assign AXI_29_WDATA_in = AXI_29_WDATA;
  assign AXI_29_WLAST_in = AXI_29_WLAST;
  assign AXI_29_WSTRB_in = AXI_29_WSTRB;
  assign AXI_29_WVALID_in = AXI_29_WVALID;
  assign AXI_30_ACLK_in = AXI_30_ACLK;
  assign AXI_30_ARADDR_in = AXI_30_ARADDR;
  assign AXI_30_ARBURST_in = AXI_30_ARBURST;
  assign AXI_30_ARESET_N_in = AXI_30_ARESET_N;
  assign AXI_30_ARID_in = AXI_30_ARID;
  assign AXI_30_ARLEN_in = AXI_30_ARLEN;
  assign AXI_30_ARSIZE_in = AXI_30_ARSIZE;
  assign AXI_30_ARVALID_in = AXI_30_ARVALID;
  assign AXI_30_AWADDR_in = AXI_30_AWADDR;
  assign AXI_30_AWBURST_in = AXI_30_AWBURST;
  assign AXI_30_AWID_in = AXI_30_AWID;
  assign AXI_30_AWLEN_in = AXI_30_AWLEN;
  assign AXI_30_AWSIZE_in = AXI_30_AWSIZE;
  assign AXI_30_AWVALID_in = AXI_30_AWVALID;
  assign AXI_30_BREADY_in = AXI_30_BREADY;
  assign AXI_30_DFI_LP_PWR_X_REQ_in = AXI_30_DFI_LP_PWR_X_REQ;
  assign AXI_30_RREADY_in = AXI_30_RREADY;
  assign AXI_30_WDATA_PARITY_in = AXI_30_WDATA_PARITY;
  assign AXI_30_WDATA_in = AXI_30_WDATA;
  assign AXI_30_WLAST_in = AXI_30_WLAST;
  assign AXI_30_WSTRB_in = AXI_30_WSTRB;
  assign AXI_30_WVALID_in = AXI_30_WVALID;
  assign AXI_31_ACLK_in = AXI_31_ACLK;
  assign AXI_31_ARADDR_in = AXI_31_ARADDR;
  assign AXI_31_ARBURST_in = AXI_31_ARBURST;
  assign AXI_31_ARESET_N_in = AXI_31_ARESET_N;
  assign AXI_31_ARID_in = AXI_31_ARID;
  assign AXI_31_ARLEN_in = AXI_31_ARLEN;
  assign AXI_31_ARSIZE_in = AXI_31_ARSIZE;
  assign AXI_31_ARVALID_in = AXI_31_ARVALID;
  assign AXI_31_AWADDR_in = AXI_31_AWADDR;
  assign AXI_31_AWBURST_in = AXI_31_AWBURST;
  assign AXI_31_AWID_in = AXI_31_AWID;
  assign AXI_31_AWLEN_in = AXI_31_AWLEN;
  assign AXI_31_AWSIZE_in = AXI_31_AWSIZE;
  assign AXI_31_AWVALID_in = AXI_31_AWVALID;
  assign AXI_31_BREADY_in = AXI_31_BREADY;
  assign AXI_31_DFI_LP_PWR_X_REQ_in = AXI_31_DFI_LP_PWR_X_REQ;
  assign AXI_31_RREADY_in = AXI_31_RREADY;
  assign AXI_31_WDATA_PARITY_in = AXI_31_WDATA_PARITY;
  assign AXI_31_WDATA_in = AXI_31_WDATA;
  assign AXI_31_WLAST_in = AXI_31_WLAST;
  assign AXI_31_WSTRB_in = AXI_31_WSTRB;
  assign AXI_31_WVALID_in = AXI_31_WVALID;
  assign BSCAN_DRCK_0_in = BSCAN_DRCK_0;
  assign BSCAN_DRCK_1_in = BSCAN_DRCK_1;
  assign BSCAN_TCK_0_in = BSCAN_TCK_0;
  assign BSCAN_TCK_1_in = BSCAN_TCK_1;
  assign HBM_REF_CLK_0_in = HBM_REF_CLK_0;
  assign HBM_REF_CLK_1_in = HBM_REF_CLK_1;
  assign MBIST_EN_00_in = MBIST_EN_00;
  assign MBIST_EN_01_in = MBIST_EN_01;
  assign MBIST_EN_02_in = MBIST_EN_02;
  assign MBIST_EN_03_in = MBIST_EN_03;
  assign MBIST_EN_04_in = MBIST_EN_04;
  assign MBIST_EN_05_in = MBIST_EN_05;
  assign MBIST_EN_06_in = MBIST_EN_06;
  assign MBIST_EN_07_in = MBIST_EN_07;
  assign MBIST_EN_08_in = MBIST_EN_08;
  assign MBIST_EN_09_in = MBIST_EN_09;
  assign MBIST_EN_10_in = MBIST_EN_10;
  assign MBIST_EN_11_in = MBIST_EN_11;
  assign MBIST_EN_12_in = MBIST_EN_12;
  assign MBIST_EN_13_in = MBIST_EN_13;
  assign MBIST_EN_14_in = MBIST_EN_14;
  assign MBIST_EN_15_in = MBIST_EN_15;

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

`ifndef XIL_XECLIB
always @ (trig_attr) begin
  #1;
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_00_REG != "FALSE") &&
       (CLK_SEL_00_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-109] CLK_SEL_00 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_00_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_01_REG != "FALSE") &&
       (CLK_SEL_01_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-110] CLK_SEL_01 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_01_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_02_REG != "FALSE") &&
       (CLK_SEL_02_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-111] CLK_SEL_02 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_02_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_03_REG != "FALSE") &&
       (CLK_SEL_03_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-112] CLK_SEL_03 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_03_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_04_REG != "FALSE") &&
       (CLK_SEL_04_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-113] CLK_SEL_04 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_04_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_05_REG != "FALSE") &&
       (CLK_SEL_05_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-114] CLK_SEL_05 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_05_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_06_REG != "FALSE") &&
       (CLK_SEL_06_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-115] CLK_SEL_06 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_06_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_07_REG != "FALSE") &&
       (CLK_SEL_07_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-116] CLK_SEL_07 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_07_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_08_REG != "FALSE") &&
       (CLK_SEL_08_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-117] CLK_SEL_08 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_08_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_09_REG != "FALSE") &&
       (CLK_SEL_09_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-118] CLK_SEL_09 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_09_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_10_REG != "FALSE") &&
       (CLK_SEL_10_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-119] CLK_SEL_10 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_10_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_11_REG != "FALSE") &&
       (CLK_SEL_11_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-120] CLK_SEL_11 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_11_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_12_REG != "FALSE") &&
       (CLK_SEL_12_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-121] CLK_SEL_12 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_12_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_13_REG != "FALSE") &&
       (CLK_SEL_13_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-122] CLK_SEL_13 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_13_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_14_REG != "FALSE") &&
       (CLK_SEL_14_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-123] CLK_SEL_14 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_14_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_15_REG != "FALSE") &&
       (CLK_SEL_15_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-124] CLK_SEL_15 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_15_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_16_REG != "FALSE") &&
       (CLK_SEL_16_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-125] CLK_SEL_16 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_16_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_17_REG != "FALSE") &&
       (CLK_SEL_17_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-126] CLK_SEL_17 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_17_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_18_REG != "FALSE") &&
       (CLK_SEL_18_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-127] CLK_SEL_18 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_18_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_19_REG != "FALSE") &&
       (CLK_SEL_19_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-128] CLK_SEL_19 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_19_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_20_REG != "FALSE") &&
       (CLK_SEL_20_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-129] CLK_SEL_20 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_20_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_21_REG != "FALSE") &&
       (CLK_SEL_21_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-130] CLK_SEL_21 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_21_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_22_REG != "FALSE") &&
       (CLK_SEL_22_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-131] CLK_SEL_22 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_22_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_23_REG != "FALSE") &&
       (CLK_SEL_23_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-132] CLK_SEL_23 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_23_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_24_REG != "FALSE") &&
       (CLK_SEL_24_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-133] CLK_SEL_24 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_24_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_25_REG != "FALSE") &&
       (CLK_SEL_25_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-134] CLK_SEL_25 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_25_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_26_REG != "FALSE") &&
       (CLK_SEL_26_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-135] CLK_SEL_26 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_26_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_27_REG != "FALSE") &&
       (CLK_SEL_27_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-136] CLK_SEL_27 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_27_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_28_REG != "FALSE") &&
       (CLK_SEL_28_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-137] CLK_SEL_28 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_28_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_29_REG != "FALSE") &&
       (CLK_SEL_29_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-138] CLK_SEL_29 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_29_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_30_REG != "FALSE") &&
       (CLK_SEL_30_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-139] CLK_SEL_30 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_30_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_31_REG != "FALSE") &&
       (CLK_SEL_31_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-140] CLK_SEL_31 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_31_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DATARATE_00_REG < 50) || (DATARATE_00_REG > 1800))) begin
    $display("Error: [Unisim %s-141] DATARATE_00 attribute is set to %d.  Legal values for this attribute are 50 to 1800. Instance: %m", MODULE_NAME, DATARATE_00_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DATARATE_01_REG < 50) || (DATARATE_01_REG > 1800))) begin
    $display("Error: [Unisim %s-142] DATARATE_01 attribute is set to %d.  Legal values for this attribute are 50 to 1800. Instance: %m", MODULE_NAME, DATARATE_01_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DATARATE_02_REG < 50) || (DATARATE_02_REG > 1800))) begin
    $display("Error: [Unisim %s-143] DATARATE_02 attribute is set to %d.  Legal values for this attribute are 50 to 1800. Instance: %m", MODULE_NAME, DATARATE_02_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DATARATE_03_REG < 50) || (DATARATE_03_REG > 1800))) begin
    $display("Error: [Unisim %s-144] DATARATE_03 attribute is set to %d.  Legal values for this attribute are 50 to 1800. Instance: %m", MODULE_NAME, DATARATE_03_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DATARATE_04_REG < 50) || (DATARATE_04_REG > 1800))) begin
    $display("Error: [Unisim %s-145] DATARATE_04 attribute is set to %d.  Legal values for this attribute are 50 to 1800. Instance: %m", MODULE_NAME, DATARATE_04_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DATARATE_05_REG < 50) || (DATARATE_05_REG > 1800))) begin
    $display("Error: [Unisim %s-146] DATARATE_05 attribute is set to %d.  Legal values for this attribute are 50 to 1800. Instance: %m", MODULE_NAME, DATARATE_05_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DATARATE_06_REG < 50) || (DATARATE_06_REG > 1800))) begin
    $display("Error: [Unisim %s-147] DATARATE_06 attribute is set to %d.  Legal values for this attribute are 50 to 1800. Instance: %m", MODULE_NAME, DATARATE_06_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DATARATE_07_REG < 50) || (DATARATE_07_REG > 1800))) begin
    $display("Error: [Unisim %s-148] DATARATE_07 attribute is set to %d.  Legal values for this attribute are 50 to 1800. Instance: %m", MODULE_NAME, DATARATE_07_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DATARATE_08_REG < 50) || (DATARATE_08_REG > 1800))) begin
    $display("Error: [Unisim %s-149] DATARATE_08 attribute is set to %d.  Legal values for this attribute are 50 to 1800. Instance: %m", MODULE_NAME, DATARATE_08_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DATARATE_09_REG < 50) || (DATARATE_09_REG > 1800))) begin
    $display("Error: [Unisim %s-150] DATARATE_09 attribute is set to %d.  Legal values for this attribute are 50 to 1800. Instance: %m", MODULE_NAME, DATARATE_09_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DATARATE_10_REG < 50) || (DATARATE_10_REG > 1800))) begin
    $display("Error: [Unisim %s-151] DATARATE_10 attribute is set to %d.  Legal values for this attribute are 50 to 1800. Instance: %m", MODULE_NAME, DATARATE_10_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DATARATE_11_REG < 50) || (DATARATE_11_REG > 1800))) begin
    $display("Error: [Unisim %s-152] DATARATE_11 attribute is set to %d.  Legal values for this attribute are 50 to 1800. Instance: %m", MODULE_NAME, DATARATE_11_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DATARATE_12_REG < 50) || (DATARATE_12_REG > 1800))) begin
    $display("Error: [Unisim %s-153] DATARATE_12 attribute is set to %d.  Legal values for this attribute are 50 to 1800. Instance: %m", MODULE_NAME, DATARATE_12_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DATARATE_13_REG < 50) || (DATARATE_13_REG > 1800))) begin
    $display("Error: [Unisim %s-154] DATARATE_13 attribute is set to %d.  Legal values for this attribute are 50 to 1800. Instance: %m", MODULE_NAME, DATARATE_13_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DATARATE_14_REG < 50) || (DATARATE_14_REG > 1800))) begin
    $display("Error: [Unisim %s-155] DATARATE_14 attribute is set to %d.  Legal values for this attribute are 50 to 1800. Instance: %m", MODULE_NAME, DATARATE_14_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DATARATE_15_REG < 50) || (DATARATE_15_REG > 1800))) begin
    $display("Error: [Unisim %s-156] DATARATE_15 attribute is set to %d.  Legal values for this attribute are 50 to 1800. Instance: %m", MODULE_NAME, DATARATE_15_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DA_LOCKOUT_0_REG != "FALSE") &&
       (DA_LOCKOUT_0_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-157] DA_LOCKOUT_0 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, DA_LOCKOUT_0_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DA_LOCKOUT_1_REG != "FALSE") &&
       (DA_LOCKOUT_1_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-158] DA_LOCKOUT_1 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, DA_LOCKOUT_1_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((MC_ENABLE_00_REG != "FALSE") &&
       (MC_ENABLE_00_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-253] MC_ENABLE_00 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, MC_ENABLE_00_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((MC_ENABLE_01_REG != "FALSE") &&
       (MC_ENABLE_01_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-254] MC_ENABLE_01 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, MC_ENABLE_01_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((MC_ENABLE_02_REG != "FALSE") &&
       (MC_ENABLE_02_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-255] MC_ENABLE_02 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, MC_ENABLE_02_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((MC_ENABLE_03_REG != "FALSE") &&
       (MC_ENABLE_03_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-256] MC_ENABLE_03 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, MC_ENABLE_03_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((MC_ENABLE_04_REG != "FALSE") &&
       (MC_ENABLE_04_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-257] MC_ENABLE_04 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, MC_ENABLE_04_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((MC_ENABLE_05_REG != "FALSE") &&
       (MC_ENABLE_05_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-258] MC_ENABLE_05 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, MC_ENABLE_05_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((MC_ENABLE_06_REG != "FALSE") &&
       (MC_ENABLE_06_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-259] MC_ENABLE_06 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, MC_ENABLE_06_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((MC_ENABLE_07_REG != "FALSE") &&
       (MC_ENABLE_07_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-260] MC_ENABLE_07 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, MC_ENABLE_07_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((MC_ENABLE_08_REG != "FALSE") &&
       (MC_ENABLE_08_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-261] MC_ENABLE_08 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, MC_ENABLE_08_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((MC_ENABLE_09_REG != "FALSE") &&
       (MC_ENABLE_09_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-262] MC_ENABLE_09 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, MC_ENABLE_09_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((MC_ENABLE_10_REG != "FALSE") &&
       (MC_ENABLE_10_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-263] MC_ENABLE_10 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, MC_ENABLE_10_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((MC_ENABLE_11_REG != "FALSE") &&
       (MC_ENABLE_11_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-264] MC_ENABLE_11 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, MC_ENABLE_11_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((MC_ENABLE_12_REG != "FALSE") &&
       (MC_ENABLE_12_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-265] MC_ENABLE_12 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, MC_ENABLE_12_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((MC_ENABLE_13_REG != "FALSE") &&
       (MC_ENABLE_13_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-266] MC_ENABLE_13 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, MC_ENABLE_13_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((MC_ENABLE_14_REG != "FALSE") &&
       (MC_ENABLE_14_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-267] MC_ENABLE_14 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, MC_ENABLE_14_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((MC_ENABLE_15_REG != "FALSE") &&
       (MC_ENABLE_15_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-268] MC_ENABLE_15 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, MC_ENABLE_15_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((MC_ENABLE_APB_00_REG != "FALSE") &&
       (MC_ENABLE_APB_00_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-269] MC_ENABLE_APB_00 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, MC_ENABLE_APB_00_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((MC_ENABLE_APB_01_REG != "FALSE") &&
       (MC_ENABLE_APB_01_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-270] MC_ENABLE_APB_01 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, MC_ENABLE_APB_01_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PAGEHIT_PERCENT_00_REG < 0) || (PAGEHIT_PERCENT_00_REG > 100))) begin
    $display("Error: [Unisim %s-287] PAGEHIT_PERCENT_00 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, PAGEHIT_PERCENT_00_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PAGEHIT_PERCENT_01_REG < 0) || (PAGEHIT_PERCENT_01_REG > 100))) begin
    $display("Error: [Unisim %s-288] PAGEHIT_PERCENT_01 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, PAGEHIT_PERCENT_01_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_00_REG != "FALSE") &&
       (PHY_ENABLE_00_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-291] PHY_ENABLE_00 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_00_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_01_REG != "FALSE") &&
       (PHY_ENABLE_01_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-292] PHY_ENABLE_01 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_01_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_02_REG != "FALSE") &&
       (PHY_ENABLE_02_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-293] PHY_ENABLE_02 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_02_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_03_REG != "FALSE") &&
       (PHY_ENABLE_03_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-294] PHY_ENABLE_03 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_03_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_04_REG != "FALSE") &&
       (PHY_ENABLE_04_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-295] PHY_ENABLE_04 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_04_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_05_REG != "FALSE") &&
       (PHY_ENABLE_05_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-296] PHY_ENABLE_05 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_05_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_06_REG != "FALSE") &&
       (PHY_ENABLE_06_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-297] PHY_ENABLE_06 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_06_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_07_REG != "FALSE") &&
       (PHY_ENABLE_07_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-298] PHY_ENABLE_07 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_07_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_08_REG != "FALSE") &&
       (PHY_ENABLE_08_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-299] PHY_ENABLE_08 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_08_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_09_REG != "FALSE") &&
       (PHY_ENABLE_09_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-300] PHY_ENABLE_09 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_09_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_10_REG != "FALSE") &&
       (PHY_ENABLE_10_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-301] PHY_ENABLE_10 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_10_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_11_REG != "FALSE") &&
       (PHY_ENABLE_11_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-302] PHY_ENABLE_11 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_11_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_12_REG != "FALSE") &&
       (PHY_ENABLE_12_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-303] PHY_ENABLE_12 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_12_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_13_REG != "FALSE") &&
       (PHY_ENABLE_13_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-304] PHY_ENABLE_13 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_13_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_14_REG != "FALSE") &&
       (PHY_ENABLE_14_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-305] PHY_ENABLE_14 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_14_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_15_REG != "FALSE") &&
       (PHY_ENABLE_15_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-306] PHY_ENABLE_15 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_15_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_16_REG != "FALSE") &&
       (PHY_ENABLE_16_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-307] PHY_ENABLE_16 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_16_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_17_REG != "FALSE") &&
       (PHY_ENABLE_17_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-308] PHY_ENABLE_17 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_17_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_18_REG != "FALSE") &&
       (PHY_ENABLE_18_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-309] PHY_ENABLE_18 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_18_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_19_REG != "FALSE") &&
       (PHY_ENABLE_19_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-310] PHY_ENABLE_19 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_19_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_20_REG != "FALSE") &&
       (PHY_ENABLE_20_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-311] PHY_ENABLE_20 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_20_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_21_REG != "FALSE") &&
       (PHY_ENABLE_21_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-312] PHY_ENABLE_21 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_21_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_22_REG != "FALSE") &&
       (PHY_ENABLE_22_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-313] PHY_ENABLE_22 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_22_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_23_REG != "FALSE") &&
       (PHY_ENABLE_23_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-314] PHY_ENABLE_23 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_23_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_24_REG != "FALSE") &&
       (PHY_ENABLE_24_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-315] PHY_ENABLE_24 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_24_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_25_REG != "FALSE") &&
       (PHY_ENABLE_25_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-316] PHY_ENABLE_25 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_25_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_26_REG != "FALSE") &&
       (PHY_ENABLE_26_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-317] PHY_ENABLE_26 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_26_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_27_REG != "FALSE") &&
       (PHY_ENABLE_27_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-318] PHY_ENABLE_27 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_27_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_28_REG != "FALSE") &&
       (PHY_ENABLE_28_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-319] PHY_ENABLE_28 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_28_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_29_REG != "FALSE") &&
       (PHY_ENABLE_29_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-320] PHY_ENABLE_29 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_29_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_30_REG != "FALSE") &&
       (PHY_ENABLE_30_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-321] PHY_ENABLE_30 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_30_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_31_REG != "FALSE") &&
       (PHY_ENABLE_31_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-322] PHY_ENABLE_31 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_31_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_APB_00_REG != "FALSE") &&
       (PHY_ENABLE_APB_00_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-323] PHY_ENABLE_APB_00 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_APB_00_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_APB_01_REG != "FALSE") &&
       (PHY_ENABLE_APB_01_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-324] PHY_ENABLE_APB_01 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_APB_01_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_PCLK_INVERT_01_REG != "FALSE") &&
       (PHY_PCLK_INVERT_01_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-325] PHY_PCLK_INVERT_01 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_PCLK_INVERT_01_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_PCLK_INVERT_02_REG != "FALSE") &&
       (PHY_PCLK_INVERT_02_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-326] PHY_PCLK_INVERT_02 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_PCLK_INVERT_02_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_00_REG < 0) || (READ_PERCENT_00_REG > 100))) begin
    $display("Error: [Unisim %s-329] READ_PERCENT_00 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_00_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_01_REG < 0) || (READ_PERCENT_01_REG > 100))) begin
    $display("Error: [Unisim %s-330] READ_PERCENT_01 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_01_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_02_REG < 0) || (READ_PERCENT_02_REG > 100))) begin
    $display("Error: [Unisim %s-331] READ_PERCENT_02 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_02_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_03_REG < 0) || (READ_PERCENT_03_REG > 100))) begin
    $display("Error: [Unisim %s-332] READ_PERCENT_03 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_03_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_04_REG < 0) || (READ_PERCENT_04_REG > 100))) begin
    $display("Error: [Unisim %s-333] READ_PERCENT_04 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_04_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_05_REG < 0) || (READ_PERCENT_05_REG > 100))) begin
    $display("Error: [Unisim %s-334] READ_PERCENT_05 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_05_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_06_REG < 0) || (READ_PERCENT_06_REG > 100))) begin
    $display("Error: [Unisim %s-335] READ_PERCENT_06 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_06_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_07_REG < 0) || (READ_PERCENT_07_REG > 100))) begin
    $display("Error: [Unisim %s-336] READ_PERCENT_07 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_07_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_08_REG < 0) || (READ_PERCENT_08_REG > 100))) begin
    $display("Error: [Unisim %s-337] READ_PERCENT_08 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_08_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_09_REG < 0) || (READ_PERCENT_09_REG > 100))) begin
    $display("Error: [Unisim %s-338] READ_PERCENT_09 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_09_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_10_REG < 0) || (READ_PERCENT_10_REG > 100))) begin
    $display("Error: [Unisim %s-339] READ_PERCENT_10 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_10_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_11_REG < 0) || (READ_PERCENT_11_REG > 100))) begin
    $display("Error: [Unisim %s-340] READ_PERCENT_11 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_11_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_12_REG < 0) || (READ_PERCENT_12_REG > 100))) begin
    $display("Error: [Unisim %s-341] READ_PERCENT_12 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_12_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_13_REG < 0) || (READ_PERCENT_13_REG > 100))) begin
    $display("Error: [Unisim %s-342] READ_PERCENT_13 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_13_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_14_REG < 0) || (READ_PERCENT_14_REG > 100))) begin
    $display("Error: [Unisim %s-343] READ_PERCENT_14 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_14_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_15_REG < 0) || (READ_PERCENT_15_REG > 100))) begin
    $display("Error: [Unisim %s-344] READ_PERCENT_15 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_15_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_16_REG < 0) || (READ_PERCENT_16_REG > 100))) begin
    $display("Error: [Unisim %s-345] READ_PERCENT_16 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_16_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_17_REG < 0) || (READ_PERCENT_17_REG > 100))) begin
    $display("Error: [Unisim %s-346] READ_PERCENT_17 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_17_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_18_REG < 0) || (READ_PERCENT_18_REG > 100))) begin
    $display("Error: [Unisim %s-347] READ_PERCENT_18 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_18_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_19_REG < 0) || (READ_PERCENT_19_REG > 100))) begin
    $display("Error: [Unisim %s-348] READ_PERCENT_19 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_19_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_20_REG < 0) || (READ_PERCENT_20_REG > 100))) begin
    $display("Error: [Unisim %s-349] READ_PERCENT_20 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_20_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_21_REG < 0) || (READ_PERCENT_21_REG > 100))) begin
    $display("Error: [Unisim %s-350] READ_PERCENT_21 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_21_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_22_REG < 0) || (READ_PERCENT_22_REG > 100))) begin
    $display("Error: [Unisim %s-351] READ_PERCENT_22 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_22_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_23_REG < 0) || (READ_PERCENT_23_REG > 100))) begin
    $display("Error: [Unisim %s-352] READ_PERCENT_23 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_23_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_24_REG < 0) || (READ_PERCENT_24_REG > 100))) begin
    $display("Error: [Unisim %s-353] READ_PERCENT_24 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_24_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_25_REG < 0) || (READ_PERCENT_25_REG > 100))) begin
    $display("Error: [Unisim %s-354] READ_PERCENT_25 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_25_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_26_REG < 0) || (READ_PERCENT_26_REG > 100))) begin
    $display("Error: [Unisim %s-355] READ_PERCENT_26 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_26_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_27_REG < 0) || (READ_PERCENT_27_REG > 100))) begin
    $display("Error: [Unisim %s-356] READ_PERCENT_27 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_27_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_28_REG < 0) || (READ_PERCENT_28_REG > 100))) begin
    $display("Error: [Unisim %s-357] READ_PERCENT_28 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_28_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_29_REG < 0) || (READ_PERCENT_29_REG > 100))) begin
    $display("Error: [Unisim %s-358] READ_PERCENT_29 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_29_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_30_REG < 0) || (READ_PERCENT_30_REG > 100))) begin
    $display("Error: [Unisim %s-359] READ_PERCENT_30 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_30_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_31_REG < 0) || (READ_PERCENT_31_REG > 100))) begin
    $display("Error: [Unisim %s-360] READ_PERCENT_31 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_31_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
        ((SIM_DEVICE_REG != "ULTRASCALE_PLUS") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES1") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES2"))) begin
      $display("Error: [Unisim %s-361] SIM_DEVICE attribute is set to %s.  Legal values for this attribute are ULTRASCALE_PLUS, ULTRASCALE_PLUS_ES1 or ULTRASCALE_PLUS_ES2. Instance: %m", MODULE_NAME, SIM_DEVICE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
      ((SWITCH_ENABLE_00_REG != "FALSE") &&
       (SWITCH_ENABLE_00_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-363] SWITCH_ENABLE_00 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, SWITCH_ENABLE_00_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((SWITCH_ENABLE_01_REG != "FALSE") &&
       (SWITCH_ENABLE_01_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-364] SWITCH_ENABLE_01 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, SWITCH_ENABLE_01_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_00_REG < 0) || (WRITE_PERCENT_00_REG > 100))) begin
      $display("Error: [Unisim %s-368] WRITE_PERCENT_00 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_00_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_01_REG < 0) || (WRITE_PERCENT_01_REG > 100))) begin
      $display("Error: [Unisim %s-369] WRITE_PERCENT_01 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_01_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_02_REG < 0) || (WRITE_PERCENT_02_REG > 100))) begin
      $display("Error: [Unisim %s-370] WRITE_PERCENT_02 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_02_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_03_REG < 0) || (WRITE_PERCENT_03_REG > 100))) begin
      $display("Error: [Unisim %s-371] WRITE_PERCENT_03 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_03_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_04_REG < 0) || (WRITE_PERCENT_04_REG > 100))) begin
      $display("Error: [Unisim %s-372] WRITE_PERCENT_04 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_04_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_05_REG < 0) || (WRITE_PERCENT_05_REG > 100))) begin
      $display("Error: [Unisim %s-373] WRITE_PERCENT_05 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_05_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_06_REG < 0) || (WRITE_PERCENT_06_REG > 100))) begin
      $display("Error: [Unisim %s-374] WRITE_PERCENT_06 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_06_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_07_REG < 0) || (WRITE_PERCENT_07_REG > 100))) begin
      $display("Error: [Unisim %s-375] WRITE_PERCENT_07 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_07_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_08_REG < 0) || (WRITE_PERCENT_08_REG > 100))) begin
      $display("Error: [Unisim %s-376] WRITE_PERCENT_08 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_08_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_09_REG < 0) || (WRITE_PERCENT_09_REG > 100))) begin
      $display("Error: [Unisim %s-377] WRITE_PERCENT_09 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_09_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_10_REG < 0) || (WRITE_PERCENT_10_REG > 100))) begin
      $display("Error: [Unisim %s-378] WRITE_PERCENT_10 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_10_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_11_REG < 0) || (WRITE_PERCENT_11_REG > 100))) begin
      $display("Error: [Unisim %s-379] WRITE_PERCENT_11 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_11_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_12_REG < 0) || (WRITE_PERCENT_12_REG > 100))) begin
      $display("Error: [Unisim %s-380] WRITE_PERCENT_12 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_12_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_13_REG < 0) || (WRITE_PERCENT_13_REG > 100))) begin
      $display("Error: [Unisim %s-381] WRITE_PERCENT_13 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_13_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_14_REG < 0) || (WRITE_PERCENT_14_REG > 100))) begin
      $display("Error: [Unisim %s-382] WRITE_PERCENT_14 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_14_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_15_REG < 0) || (WRITE_PERCENT_15_REG > 100))) begin
      $display("Error: [Unisim %s-383] WRITE_PERCENT_15 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_15_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_16_REG < 0) || (WRITE_PERCENT_16_REG > 100))) begin
      $display("Error: [Unisim %s-384] WRITE_PERCENT_16 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_16_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_17_REG < 0) || (WRITE_PERCENT_17_REG > 100))) begin
      $display("Error: [Unisim %s-385] WRITE_PERCENT_17 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_17_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_18_REG < 0) || (WRITE_PERCENT_18_REG > 100))) begin
      $display("Error: [Unisim %s-386] WRITE_PERCENT_18 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_18_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_19_REG < 0) || (WRITE_PERCENT_19_REG > 100))) begin
      $display("Error: [Unisim %s-387] WRITE_PERCENT_19 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_19_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_20_REG < 0) || (WRITE_PERCENT_20_REG > 100))) begin
      $display("Error: [Unisim %s-388] WRITE_PERCENT_20 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_20_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_21_REG < 0) || (WRITE_PERCENT_21_REG > 100))) begin
      $display("Error: [Unisim %s-389] WRITE_PERCENT_21 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_21_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_22_REG < 0) || (WRITE_PERCENT_22_REG > 100))) begin
      $display("Error: [Unisim %s-390] WRITE_PERCENT_22 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_22_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_23_REG < 0) || (WRITE_PERCENT_23_REG > 100))) begin
      $display("Error: [Unisim %s-391] WRITE_PERCENT_23 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_23_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_24_REG < 0) || (WRITE_PERCENT_24_REG > 100))) begin
      $display("Error: [Unisim %s-392] WRITE_PERCENT_24 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_24_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_25_REG < 0) || (WRITE_PERCENT_25_REG > 100))) begin
      $display("Error: [Unisim %s-393] WRITE_PERCENT_25 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_25_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_26_REG < 0) || (WRITE_PERCENT_26_REG > 100))) begin
      $display("Error: [Unisim %s-394] WRITE_PERCENT_26 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_26_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_27_REG < 0) || (WRITE_PERCENT_27_REG > 100))) begin
      $display("Error: [Unisim %s-395] WRITE_PERCENT_27 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_27_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_28_REG < 0) || (WRITE_PERCENT_28_REG > 100))) begin
      $display("Error: [Unisim %s-396] WRITE_PERCENT_28 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_28_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_29_REG < 0) || (WRITE_PERCENT_29_REG > 100))) begin
      $display("Error: [Unisim %s-397] WRITE_PERCENT_29 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_29_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_30_REG < 0) || (WRITE_PERCENT_30_REG > 100))) begin
      $display("Error: [Unisim %s-398] WRITE_PERCENT_30 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_30_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_31_REG < 0) || (WRITE_PERCENT_31_REG > 100))) begin
      $display("Error: [Unisim %s-399] WRITE_PERCENT_31 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_31_REG);
    attr_err = 1'b1;
  end
  
  if (attr_err == 1'b1) #1 $finish;
end
`endif



assign ANALOG_HBM_SEL_00_in = 1'b1; // tie off
assign ANALOG_HBM_SEL_01_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_00_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_01_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_02_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_03_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_04_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_05_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_06_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_07_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_08_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_09_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_10_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_11_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_12_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_13_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_14_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_15_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_16_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_17_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_18_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_19_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_20_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_21_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_22_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_23_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_24_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_25_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_26_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_27_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_28_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_29_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_30_in = 1'b1; // tie off
assign BLI_SCAN_ENABLE_31_in = 1'b1; // tie off
assign BLI_SCAN_IN_00_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_01_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_02_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_03_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_04_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_05_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_06_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_07_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_08_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_09_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_10_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_11_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_12_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_13_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_14_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_15_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_16_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_17_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_18_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_19_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_20_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_21_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_22_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_23_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_24_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_25_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_26_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_27_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_28_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_29_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_30_in = 8'b11111111; // tie off
assign BLI_SCAN_IN_31_in = 8'b11111111; // tie off
assign DBG_IN_00_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_01_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_02_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_03_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_04_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_05_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_06_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_07_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_08_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_09_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_10_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_11_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_12_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_13_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_14_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_15_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_16_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_17_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_18_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_19_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_20_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_21_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_22_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_23_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_24_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_25_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_26_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_27_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_28_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_29_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_30_in = 24'b111111111111111111111111; // tie off
assign DBG_IN_31_in = 24'b111111111111111111111111; // tie off
assign DLL_SCAN_CK_00_in = 1'b1; // tie off
assign DLL_SCAN_CK_01_in = 1'b1; // tie off
assign DLL_SCAN_ENABLE_00_in = 1'b1; // tie off
assign DLL_SCAN_ENABLE_01_in = 1'b1; // tie off
assign DLL_SCAN_IN_00_in = 2'b11; // tie off
assign DLL_SCAN_IN_01_in = 2'b11; // tie off
assign DLL_SCAN_MODE_00_in = 1'b1; // tie off
assign DLL_SCAN_MODE_01_in = 1'b1; // tie off
assign DLL_SCAN_RST_N_00_in = 1'b1; // tie off
assign DLL_SCAN_RST_N_01_in = 1'b1; // tie off
assign IO_SCAN_CK_00_in = 1'b1; // tie off
assign IO_SCAN_CK_01_in = 1'b1; // tie off
assign IO_SCAN_ENABLE_00_in = 1'b1; // tie off
assign IO_SCAN_ENABLE_01_in = 1'b1; // tie off
assign IO_SCAN_IN_00_in = 2'b11; // tie off
assign IO_SCAN_IN_01_in = 2'b11; // tie off
assign IO_SCAN_MODE_00_in = 1'b1; // tie off
assign IO_SCAN_MODE_01_in = 1'b1; // tie off
assign IO_SCAN_RST_N_00_in = 1'b1; // tie off
assign IO_SCAN_RST_N_01_in = 1'b1; // tie off
assign MC_SCAN_CK_00_in = 1'b1; // tie off
assign MC_SCAN_CK_01_in = 1'b1; // tie off
assign MC_SCAN_CK_02_in = 1'b1; // tie off
assign MC_SCAN_CK_03_in = 1'b1; // tie off
assign MC_SCAN_CK_04_in = 1'b1; // tie off
assign MC_SCAN_CK_05_in = 1'b1; // tie off
assign MC_SCAN_CK_06_in = 1'b1; // tie off
assign MC_SCAN_CK_07_in = 1'b1; // tie off
assign MC_SCAN_CK_08_in = 1'b1; // tie off
assign MC_SCAN_CK_09_in = 1'b1; // tie off
assign MC_SCAN_CK_10_in = 1'b1; // tie off
assign MC_SCAN_CK_11_in = 1'b1; // tie off
assign MC_SCAN_CK_12_in = 1'b1; // tie off
assign MC_SCAN_CK_13_in = 1'b1; // tie off
assign MC_SCAN_CK_14_in = 1'b1; // tie off
assign MC_SCAN_CK_15_in = 1'b1; // tie off
assign MC_SCAN_ENABLE_00_in = 1'b1; // tie off
assign MC_SCAN_ENABLE_01_in = 1'b1; // tie off
assign MC_SCAN_ENABLE_02_in = 1'b1; // tie off
assign MC_SCAN_ENABLE_03_in = 1'b1; // tie off
assign MC_SCAN_ENABLE_04_in = 1'b1; // tie off
assign MC_SCAN_ENABLE_05_in = 1'b1; // tie off
assign MC_SCAN_ENABLE_06_in = 1'b1; // tie off
assign MC_SCAN_ENABLE_07_in = 1'b1; // tie off
assign MC_SCAN_ENABLE_08_in = 1'b1; // tie off
assign MC_SCAN_ENABLE_09_in = 1'b1; // tie off
assign MC_SCAN_ENABLE_10_in = 1'b1; // tie off
assign MC_SCAN_ENABLE_11_in = 1'b1; // tie off
assign MC_SCAN_ENABLE_12_in = 1'b1; // tie off
assign MC_SCAN_ENABLE_13_in = 1'b1; // tie off
assign MC_SCAN_ENABLE_14_in = 1'b1; // tie off
assign MC_SCAN_ENABLE_15_in = 1'b1; // tie off
assign MC_SCAN_IN_00_in = 2'b11; // tie off
assign MC_SCAN_IN_01_in = 2'b11; // tie off
assign MC_SCAN_IN_02_in = 2'b11; // tie off
assign MC_SCAN_IN_03_in = 2'b11; // tie off
assign MC_SCAN_IN_04_in = 2'b11; // tie off
assign MC_SCAN_IN_05_in = 2'b11; // tie off
assign MC_SCAN_IN_06_in = 2'b11; // tie off
assign MC_SCAN_IN_07_in = 2'b11; // tie off
assign MC_SCAN_IN_08_in = 2'b11; // tie off
assign MC_SCAN_IN_09_in = 2'b11; // tie off
assign MC_SCAN_IN_10_in = 2'b11; // tie off
assign MC_SCAN_IN_11_in = 2'b11; // tie off
assign MC_SCAN_IN_12_in = 2'b11; // tie off
assign MC_SCAN_IN_13_in = 2'b11; // tie off
assign MC_SCAN_IN_14_in = 2'b11; // tie off
assign MC_SCAN_IN_15_in = 2'b11; // tie off
assign MC_SCAN_MODE_00_in = 1'b1; // tie off
assign MC_SCAN_MODE_01_in = 1'b1; // tie off
assign MC_SCAN_MODE_02_in = 1'b1; // tie off
assign MC_SCAN_MODE_03_in = 1'b1; // tie off
assign MC_SCAN_MODE_04_in = 1'b1; // tie off
assign MC_SCAN_MODE_05_in = 1'b1; // tie off
assign MC_SCAN_MODE_06_in = 1'b1; // tie off
assign MC_SCAN_MODE_07_in = 1'b1; // tie off
assign MC_SCAN_MODE_08_in = 1'b1; // tie off
assign MC_SCAN_MODE_09_in = 1'b1; // tie off
assign MC_SCAN_MODE_10_in = 1'b1; // tie off
assign MC_SCAN_MODE_11_in = 1'b1; // tie off
assign MC_SCAN_MODE_12_in = 1'b1; // tie off
assign MC_SCAN_MODE_13_in = 1'b1; // tie off
assign MC_SCAN_MODE_14_in = 1'b1; // tie off
assign MC_SCAN_MODE_15_in = 1'b1; // tie off
assign MC_SCAN_RST_N_00_in = 1'b1; // tie off
assign MC_SCAN_RST_N_01_in = 1'b1; // tie off
assign MC_SCAN_RST_N_02_in = 1'b1; // tie off
assign MC_SCAN_RST_N_03_in = 1'b1; // tie off
assign MC_SCAN_RST_N_04_in = 1'b1; // tie off
assign MC_SCAN_RST_N_05_in = 1'b1; // tie off
assign MC_SCAN_RST_N_06_in = 1'b1; // tie off
assign MC_SCAN_RST_N_07_in = 1'b1; // tie off
assign MC_SCAN_RST_N_08_in = 1'b1; // tie off
assign MC_SCAN_RST_N_09_in = 1'b1; // tie off
assign MC_SCAN_RST_N_10_in = 1'b1; // tie off
assign MC_SCAN_RST_N_11_in = 1'b1; // tie off
assign MC_SCAN_RST_N_12_in = 1'b1; // tie off
assign MC_SCAN_RST_N_13_in = 1'b1; // tie off
assign MC_SCAN_RST_N_14_in = 1'b1; // tie off
assign MC_SCAN_RST_N_15_in = 1'b1; // tie off
assign PHY_SCAN_CK_00_in = 1'b1; // tie off
assign PHY_SCAN_CK_01_in = 1'b1; // tie off
assign PHY_SCAN_ENABLE_00_in = 1'b1; // tie off
assign PHY_SCAN_ENABLE_01_in = 1'b1; // tie off
assign PHY_SCAN_IN_00_in = 2'b11; // tie off
assign PHY_SCAN_IN_01_in = 2'b11; // tie off
assign PHY_SCAN_MODE_00_in = 1'b1; // tie off
assign PHY_SCAN_MODE_01_in = 1'b1; // tie off
assign PHY_SCAN_RST_N_00_in = 1'b1; // tie off
assign PHY_SCAN_RST_N_01_in = 1'b1; // tie off
assign SW_SCAN_CK_00_in = 1'b1; // tie off
assign SW_SCAN_CK_01_in = 1'b1; // tie off
assign SW_SCAN_ENABLE_00_in = 1'b1; // tie off
assign SW_SCAN_ENABLE_01_in = 1'b1; // tie off
assign SW_SCAN_IN_00_in = 2'b11; // tie off
assign SW_SCAN_IN_01_in = 2'b11; // tie off
assign SW_SCAN_IN_02_in = 2'b11; // tie off
assign SW_SCAN_IN_03_in = 2'b11; // tie off
assign SW_SCAN_IN_04_in = 2'b11; // tie off
assign SW_SCAN_IN_05_in = 2'b11; // tie off
assign SW_SCAN_IN_06_in = 2'b11; // tie off
assign SW_SCAN_IN_07_in = 2'b11; // tie off
assign SW_SCAN_MODE_00_in = 1'b1; // tie off
assign SW_SCAN_MODE_01_in = 1'b1; // tie off
assign SW_SCAN_RST_N_00_in = 1'b1; // tie off
assign SW_SCAN_RST_N_01_in = 1'b1; // tie off

SIP_HBM_TWO_STACK_INTF SIP_HBM_TWO_STACK_INTF_INST (
  .ANALOG_MUX_SEL_0 (ANALOG_MUX_SEL_0_REG),
  .ANALOG_MUX_SEL_1 (ANALOG_MUX_SEL_1_REG),
  .APB_BYPASS_EN_0 (APB_BYPASS_EN_0_REG),
  .APB_BYPASS_EN_1 (APB_BYPASS_EN_1_REG),
  .AXI_BYPASS_EN_0 (AXI_BYPASS_EN_0_REG),
  .AXI_BYPASS_EN_1 (AXI_BYPASS_EN_1_REG),
  .BLI_TESTMODE_SEL_0 (BLI_TESTMODE_SEL_0_REG),
  .BLI_TESTMODE_SEL_1 (BLI_TESTMODE_SEL_1_REG),
  .CLK_SEL_00 (CLK_SEL_00_REG),
  .CLK_SEL_01 (CLK_SEL_01_REG),
  .CLK_SEL_02 (CLK_SEL_02_REG),
  .CLK_SEL_03 (CLK_SEL_03_REG),
  .CLK_SEL_04 (CLK_SEL_04_REG),
  .CLK_SEL_05 (CLK_SEL_05_REG),
  .CLK_SEL_06 (CLK_SEL_06_REG),
  .CLK_SEL_07 (CLK_SEL_07_REG),
  .CLK_SEL_08 (CLK_SEL_08_REG),
  .CLK_SEL_09 (CLK_SEL_09_REG),
  .CLK_SEL_10 (CLK_SEL_10_REG),
  .CLK_SEL_11 (CLK_SEL_11_REG),
  .CLK_SEL_12 (CLK_SEL_12_REG),
  .CLK_SEL_13 (CLK_SEL_13_REG),
  .CLK_SEL_14 (CLK_SEL_14_REG),
  .CLK_SEL_15 (CLK_SEL_15_REG),
  .CLK_SEL_16 (CLK_SEL_16_REG),
  .CLK_SEL_17 (CLK_SEL_17_REG),
  .CLK_SEL_18 (CLK_SEL_18_REG),
  .CLK_SEL_19 (CLK_SEL_19_REG),
  .CLK_SEL_20 (CLK_SEL_20_REG),
  .CLK_SEL_21 (CLK_SEL_21_REG),
  .CLK_SEL_22 (CLK_SEL_22_REG),
  .CLK_SEL_23 (CLK_SEL_23_REG),
  .CLK_SEL_24 (CLK_SEL_24_REG),
  .CLK_SEL_25 (CLK_SEL_25_REG),
  .CLK_SEL_26 (CLK_SEL_26_REG),
  .CLK_SEL_27 (CLK_SEL_27_REG),
  .CLK_SEL_28 (CLK_SEL_28_REG),
  .CLK_SEL_29 (CLK_SEL_29_REG),
  .CLK_SEL_30 (CLK_SEL_30_REG),
  .CLK_SEL_31 (CLK_SEL_31_REG),
  .DATARATE_00 (DATARATE_00_REG),
  .DATARATE_01 (DATARATE_01_REG),
  .DATARATE_02 (DATARATE_02_REG),
  .DATARATE_03 (DATARATE_03_REG),
  .DATARATE_04 (DATARATE_04_REG),
  .DATARATE_05 (DATARATE_05_REG),
  .DATARATE_06 (DATARATE_06_REG),
  .DATARATE_07 (DATARATE_07_REG),
  .DATARATE_08 (DATARATE_08_REG),
  .DATARATE_09 (DATARATE_09_REG),
  .DATARATE_10 (DATARATE_10_REG),
  .DATARATE_11 (DATARATE_11_REG),
  .DATARATE_12 (DATARATE_12_REG),
  .DATARATE_13 (DATARATE_13_REG),
  .DATARATE_14 (DATARATE_14_REG),
  .DATARATE_15 (DATARATE_15_REG),
  .DA_LOCKOUT_0 (DA_LOCKOUT_0_REG),
  .DA_LOCKOUT_1 (DA_LOCKOUT_1_REG),
  .DBG_BYPASS_VAL_0 (DBG_BYPASS_VAL_0_REG),
  .DBG_BYPASS_VAL_1 (DBG_BYPASS_VAL_1_REG),
  .DEBUG_MODE_0 (DEBUG_MODE_0_REG),
  .DEBUG_MODE_1 (DEBUG_MODE_1_REG),
  .DFI_BYPASS_VAL_0 (DFI_BYPASS_VAL_0_REG),
  .DFI_BYPASS_VAL_1 (DFI_BYPASS_VAL_1_REG),
  .DLL_TESTMODE_SEL_0 (DLL_TESTMODE_SEL_0_REG),
  .DLL_TESTMODE_SEL_1 (DLL_TESTMODE_SEL_1_REG),
  .IO_TESTMODE_SEL_0 (IO_TESTMODE_SEL_0_REG),
  .IO_TESTMODE_SEL_1 (IO_TESTMODE_SEL_1_REG),
  .IS_APB_0_PCLK_INVERTED (IS_APB_0_PCLK_INVERTED_REG),
  .IS_APB_0_PRESET_N_INVERTED (IS_APB_0_PRESET_N_INVERTED_REG),
  .IS_APB_1_PCLK_INVERTED (IS_APB_1_PCLK_INVERTED_REG),
  .IS_APB_1_PRESET_N_INVERTED (IS_APB_1_PRESET_N_INVERTED_REG),
  .IS_AXI_00_ACLK_INVERTED (IS_AXI_00_ACLK_INVERTED_REG),
  .IS_AXI_00_ARESET_N_INVERTED (IS_AXI_00_ARESET_N_INVERTED_REG),
  .IS_AXI_01_ACLK_INVERTED (IS_AXI_01_ACLK_INVERTED_REG),
  .IS_AXI_01_ARESET_N_INVERTED (IS_AXI_01_ARESET_N_INVERTED_REG),
  .IS_AXI_02_ACLK_INVERTED (IS_AXI_02_ACLK_INVERTED_REG),
  .IS_AXI_02_ARESET_N_INVERTED (IS_AXI_02_ARESET_N_INVERTED_REG),
  .IS_AXI_03_ACLK_INVERTED (IS_AXI_03_ACLK_INVERTED_REG),
  .IS_AXI_03_ARESET_N_INVERTED (IS_AXI_03_ARESET_N_INVERTED_REG),
  .IS_AXI_04_ACLK_INVERTED (IS_AXI_04_ACLK_INVERTED_REG),
  .IS_AXI_04_ARESET_N_INVERTED (IS_AXI_04_ARESET_N_INVERTED_REG),
  .IS_AXI_05_ACLK_INVERTED (IS_AXI_05_ACLK_INVERTED_REG),
  .IS_AXI_05_ARESET_N_INVERTED (IS_AXI_05_ARESET_N_INVERTED_REG),
  .IS_AXI_06_ACLK_INVERTED (IS_AXI_06_ACLK_INVERTED_REG),
  .IS_AXI_06_ARESET_N_INVERTED (IS_AXI_06_ARESET_N_INVERTED_REG),
  .IS_AXI_07_ACLK_INVERTED (IS_AXI_07_ACLK_INVERTED_REG),
  .IS_AXI_07_ARESET_N_INVERTED (IS_AXI_07_ARESET_N_INVERTED_REG),
  .IS_AXI_08_ACLK_INVERTED (IS_AXI_08_ACLK_INVERTED_REG),
  .IS_AXI_08_ARESET_N_INVERTED (IS_AXI_08_ARESET_N_INVERTED_REG),
  .IS_AXI_09_ACLK_INVERTED (IS_AXI_09_ACLK_INVERTED_REG),
  .IS_AXI_09_ARESET_N_INVERTED (IS_AXI_09_ARESET_N_INVERTED_REG),
  .IS_AXI_10_ACLK_INVERTED (IS_AXI_10_ACLK_INVERTED_REG),
  .IS_AXI_10_ARESET_N_INVERTED (IS_AXI_10_ARESET_N_INVERTED_REG),
  .IS_AXI_11_ACLK_INVERTED (IS_AXI_11_ACLK_INVERTED_REG),
  .IS_AXI_11_ARESET_N_INVERTED (IS_AXI_11_ARESET_N_INVERTED_REG),
  .IS_AXI_12_ACLK_INVERTED (IS_AXI_12_ACLK_INVERTED_REG),
  .IS_AXI_12_ARESET_N_INVERTED (IS_AXI_12_ARESET_N_INVERTED_REG),
  .IS_AXI_13_ACLK_INVERTED (IS_AXI_13_ACLK_INVERTED_REG),
  .IS_AXI_13_ARESET_N_INVERTED (IS_AXI_13_ARESET_N_INVERTED_REG),
  .IS_AXI_14_ACLK_INVERTED (IS_AXI_14_ACLK_INVERTED_REG),
  .IS_AXI_14_ARESET_N_INVERTED (IS_AXI_14_ARESET_N_INVERTED_REG),
  .IS_AXI_15_ACLK_INVERTED (IS_AXI_15_ACLK_INVERTED_REG),
  .IS_AXI_15_ARESET_N_INVERTED (IS_AXI_15_ARESET_N_INVERTED_REG),
  .IS_AXI_16_ACLK_INVERTED (IS_AXI_16_ACLK_INVERTED_REG),
  .IS_AXI_16_ARESET_N_INVERTED (IS_AXI_16_ARESET_N_INVERTED_REG),
  .IS_AXI_17_ACLK_INVERTED (IS_AXI_17_ACLK_INVERTED_REG),
  .IS_AXI_17_ARESET_N_INVERTED (IS_AXI_17_ARESET_N_INVERTED_REG),
  .IS_AXI_18_ACLK_INVERTED (IS_AXI_18_ACLK_INVERTED_REG),
  .IS_AXI_18_ARESET_N_INVERTED (IS_AXI_18_ARESET_N_INVERTED_REG),
  .IS_AXI_19_ACLK_INVERTED (IS_AXI_19_ACLK_INVERTED_REG),
  .IS_AXI_19_ARESET_N_INVERTED (IS_AXI_19_ARESET_N_INVERTED_REG),
  .IS_AXI_20_ACLK_INVERTED (IS_AXI_20_ACLK_INVERTED_REG),
  .IS_AXI_20_ARESET_N_INVERTED (IS_AXI_20_ARESET_N_INVERTED_REG),
  .IS_AXI_21_ACLK_INVERTED (IS_AXI_21_ACLK_INVERTED_REG),
  .IS_AXI_21_ARESET_N_INVERTED (IS_AXI_21_ARESET_N_INVERTED_REG),
  .IS_AXI_22_ACLK_INVERTED (IS_AXI_22_ACLK_INVERTED_REG),
  .IS_AXI_22_ARESET_N_INVERTED (IS_AXI_22_ARESET_N_INVERTED_REG),
  .IS_AXI_23_ACLK_INVERTED (IS_AXI_23_ACLK_INVERTED_REG),
  .IS_AXI_23_ARESET_N_INVERTED (IS_AXI_23_ARESET_N_INVERTED_REG),
  .IS_AXI_24_ACLK_INVERTED (IS_AXI_24_ACLK_INVERTED_REG),
  .IS_AXI_24_ARESET_N_INVERTED (IS_AXI_24_ARESET_N_INVERTED_REG),
  .IS_AXI_25_ACLK_INVERTED (IS_AXI_25_ACLK_INVERTED_REG),
  .IS_AXI_25_ARESET_N_INVERTED (IS_AXI_25_ARESET_N_INVERTED_REG),
  .IS_AXI_26_ACLK_INVERTED (IS_AXI_26_ACLK_INVERTED_REG),
  .IS_AXI_26_ARESET_N_INVERTED (IS_AXI_26_ARESET_N_INVERTED_REG),
  .IS_AXI_27_ACLK_INVERTED (IS_AXI_27_ACLK_INVERTED_REG),
  .IS_AXI_27_ARESET_N_INVERTED (IS_AXI_27_ARESET_N_INVERTED_REG),
  .IS_AXI_28_ACLK_INVERTED (IS_AXI_28_ACLK_INVERTED_REG),
  .IS_AXI_28_ARESET_N_INVERTED (IS_AXI_28_ARESET_N_INVERTED_REG),
  .IS_AXI_29_ACLK_INVERTED (IS_AXI_29_ACLK_INVERTED_REG),
  .IS_AXI_29_ARESET_N_INVERTED (IS_AXI_29_ARESET_N_INVERTED_REG),
  .IS_AXI_30_ACLK_INVERTED (IS_AXI_30_ACLK_INVERTED_REG),
  .IS_AXI_30_ARESET_N_INVERTED (IS_AXI_30_ARESET_N_INVERTED_REG),
  .IS_AXI_31_ACLK_INVERTED (IS_AXI_31_ACLK_INVERTED_REG),
  .IS_AXI_31_ARESET_N_INVERTED (IS_AXI_31_ARESET_N_INVERTED_REG),
  .MC_CSSD_SEL_0 (MC_CSSD_SEL_0_REG),
  .MC_CSSD_SEL_1 (MC_CSSD_SEL_1_REG),
  .MC_CSSD_SEL_10 (MC_CSSD_SEL_10_REG),
  .MC_CSSD_SEL_11 (MC_CSSD_SEL_11_REG),
  .MC_CSSD_SEL_12 (MC_CSSD_SEL_12_REG),
  .MC_CSSD_SEL_13 (MC_CSSD_SEL_13_REG),
  .MC_CSSD_SEL_14 (MC_CSSD_SEL_14_REG),
  .MC_CSSD_SEL_15 (MC_CSSD_SEL_15_REG),
  .MC_CSSD_SEL_2 (MC_CSSD_SEL_2_REG),
  .MC_CSSD_SEL_3 (MC_CSSD_SEL_3_REG),
  .MC_CSSD_SEL_4 (MC_CSSD_SEL_4_REG),
  .MC_CSSD_SEL_5 (MC_CSSD_SEL_5_REG),
  .MC_CSSD_SEL_6 (MC_CSSD_SEL_6_REG),
  .MC_CSSD_SEL_7 (MC_CSSD_SEL_7_REG),
  .MC_CSSD_SEL_8 (MC_CSSD_SEL_8_REG),
  .MC_CSSD_SEL_9 (MC_CSSD_SEL_9_REG),
  .MC_ENABLE_00 (MC_ENABLE_00_REG),
  .MC_ENABLE_01 (MC_ENABLE_01_REG),
  .MC_ENABLE_02 (MC_ENABLE_02_REG),
  .MC_ENABLE_03 (MC_ENABLE_03_REG),
  .MC_ENABLE_04 (MC_ENABLE_04_REG),
  .MC_ENABLE_05 (MC_ENABLE_05_REG),
  .MC_ENABLE_06 (MC_ENABLE_06_REG),
  .MC_ENABLE_07 (MC_ENABLE_07_REG),
  .MC_ENABLE_08 (MC_ENABLE_08_REG),
  .MC_ENABLE_09 (MC_ENABLE_09_REG),
  .MC_ENABLE_10 (MC_ENABLE_10_REG),
  .MC_ENABLE_11 (MC_ENABLE_11_REG),
  .MC_ENABLE_12 (MC_ENABLE_12_REG),
  .MC_ENABLE_13 (MC_ENABLE_13_REG),
  .MC_ENABLE_14 (MC_ENABLE_14_REG),
  .MC_ENABLE_15 (MC_ENABLE_15_REG),
  .MC_ENABLE_APB_00 (MC_ENABLE_APB_00_REG),
  .MC_ENABLE_APB_01 (MC_ENABLE_APB_01_REG),
  .MC_TESTMODE_SEL_0 (MC_TESTMODE_SEL_0_REG),
  .MC_TESTMODE_SEL_1 (MC_TESTMODE_SEL_1_REG),
  .MC_TESTMODE_SEL_10 (MC_TESTMODE_SEL_10_REG),
  .MC_TESTMODE_SEL_11 (MC_TESTMODE_SEL_11_REG),
  .MC_TESTMODE_SEL_12 (MC_TESTMODE_SEL_12_REG),
  .MC_TESTMODE_SEL_13 (MC_TESTMODE_SEL_13_REG),
  .MC_TESTMODE_SEL_14 (MC_TESTMODE_SEL_14_REG),
  .MC_TESTMODE_SEL_15 (MC_TESTMODE_SEL_15_REG),
  .MC_TESTMODE_SEL_2 (MC_TESTMODE_SEL_2_REG),
  .MC_TESTMODE_SEL_3 (MC_TESTMODE_SEL_3_REG),
  .MC_TESTMODE_SEL_4 (MC_TESTMODE_SEL_4_REG),
  .MC_TESTMODE_SEL_5 (MC_TESTMODE_SEL_5_REG),
  .MC_TESTMODE_SEL_6 (MC_TESTMODE_SEL_6_REG),
  .MC_TESTMODE_SEL_7 (MC_TESTMODE_SEL_7_REG),
  .MC_TESTMODE_SEL_8 (MC_TESTMODE_SEL_8_REG),
  .MC_TESTMODE_SEL_9 (MC_TESTMODE_SEL_9_REG),
  .PAGEHIT_PERCENT_00 (PAGEHIT_PERCENT_00_REG),
  .PAGEHIT_PERCENT_01 (PAGEHIT_PERCENT_01_REG),
  .PHY_CSSD_SEL_0 (PHY_CSSD_SEL_0_REG),
  .PHY_CSSD_SEL_1 (PHY_CSSD_SEL_1_REG),
  .PHY_ENABLE_00 (PHY_ENABLE_00_REG),
  .PHY_ENABLE_01 (PHY_ENABLE_01_REG),
  .PHY_ENABLE_02 (PHY_ENABLE_02_REG),
  .PHY_ENABLE_03 (PHY_ENABLE_03_REG),
  .PHY_ENABLE_04 (PHY_ENABLE_04_REG),
  .PHY_ENABLE_05 (PHY_ENABLE_05_REG),
  .PHY_ENABLE_06 (PHY_ENABLE_06_REG),
  .PHY_ENABLE_07 (PHY_ENABLE_07_REG),
  .PHY_ENABLE_08 (PHY_ENABLE_08_REG),
  .PHY_ENABLE_09 (PHY_ENABLE_09_REG),
  .PHY_ENABLE_10 (PHY_ENABLE_10_REG),
  .PHY_ENABLE_11 (PHY_ENABLE_11_REG),
  .PHY_ENABLE_12 (PHY_ENABLE_12_REG),
  .PHY_ENABLE_13 (PHY_ENABLE_13_REG),
  .PHY_ENABLE_14 (PHY_ENABLE_14_REG),
  .PHY_ENABLE_15 (PHY_ENABLE_15_REG),
  .PHY_ENABLE_16 (PHY_ENABLE_16_REG),
  .PHY_ENABLE_17 (PHY_ENABLE_17_REG),
  .PHY_ENABLE_18 (PHY_ENABLE_18_REG),
  .PHY_ENABLE_19 (PHY_ENABLE_19_REG),
  .PHY_ENABLE_20 (PHY_ENABLE_20_REG),
  .PHY_ENABLE_21 (PHY_ENABLE_21_REG),
  .PHY_ENABLE_22 (PHY_ENABLE_22_REG),
  .PHY_ENABLE_23 (PHY_ENABLE_23_REG),
  .PHY_ENABLE_24 (PHY_ENABLE_24_REG),
  .PHY_ENABLE_25 (PHY_ENABLE_25_REG),
  .PHY_ENABLE_26 (PHY_ENABLE_26_REG),
  .PHY_ENABLE_27 (PHY_ENABLE_27_REG),
  .PHY_ENABLE_28 (PHY_ENABLE_28_REG),
  .PHY_ENABLE_29 (PHY_ENABLE_29_REG),
  .PHY_ENABLE_30 (PHY_ENABLE_30_REG),
  .PHY_ENABLE_31 (PHY_ENABLE_31_REG),
  .PHY_ENABLE_APB_00 (PHY_ENABLE_APB_00_REG),
  .PHY_ENABLE_APB_01 (PHY_ENABLE_APB_01_REG),
  .PHY_PCLK_INVERT_01 (PHY_PCLK_INVERT_01_REG),
  .PHY_PCLK_INVERT_02 (PHY_PCLK_INVERT_02_REG),
  .PHY_TESTMODE_SEL_0 (PHY_TESTMODE_SEL_0_REG),
  .PHY_TESTMODE_SEL_1 (PHY_TESTMODE_SEL_1_REG),
  .READ_PERCENT_00 (READ_PERCENT_00_REG),
  .READ_PERCENT_01 (READ_PERCENT_01_REG),
  .READ_PERCENT_02 (READ_PERCENT_02_REG),
  .READ_PERCENT_03 (READ_PERCENT_03_REG),
  .READ_PERCENT_04 (READ_PERCENT_04_REG),
  .READ_PERCENT_05 (READ_PERCENT_05_REG),
  .READ_PERCENT_06 (READ_PERCENT_06_REG),
  .READ_PERCENT_07 (READ_PERCENT_07_REG),
  .READ_PERCENT_08 (READ_PERCENT_08_REG),
  .READ_PERCENT_09 (READ_PERCENT_09_REG),
  .READ_PERCENT_10 (READ_PERCENT_10_REG),
  .READ_PERCENT_11 (READ_PERCENT_11_REG),
  .READ_PERCENT_12 (READ_PERCENT_12_REG),
  .READ_PERCENT_13 (READ_PERCENT_13_REG),
  .READ_PERCENT_14 (READ_PERCENT_14_REG),
  .READ_PERCENT_15 (READ_PERCENT_15_REG),
  .READ_PERCENT_16 (READ_PERCENT_16_REG),
  .READ_PERCENT_17 (READ_PERCENT_17_REG),
  .READ_PERCENT_18 (READ_PERCENT_18_REG),
  .READ_PERCENT_19 (READ_PERCENT_19_REG),
  .READ_PERCENT_20 (READ_PERCENT_20_REG),
  .READ_PERCENT_21 (READ_PERCENT_21_REG),
  .READ_PERCENT_22 (READ_PERCENT_22_REG),
  .READ_PERCENT_23 (READ_PERCENT_23_REG),
  .READ_PERCENT_24 (READ_PERCENT_24_REG),
  .READ_PERCENT_25 (READ_PERCENT_25_REG),
  .READ_PERCENT_26 (READ_PERCENT_26_REG),
  .READ_PERCENT_27 (READ_PERCENT_27_REG),
  .READ_PERCENT_28 (READ_PERCENT_28_REG),
  .READ_PERCENT_29 (READ_PERCENT_29_REG),
  .READ_PERCENT_30 (READ_PERCENT_30_REG),
  .READ_PERCENT_31 (READ_PERCENT_31_REG),
  .SWITCH_ENABLE_0 (SWITCH_ENABLE_0_REG),
  .SWITCH_ENABLE_00 (SWITCH_ENABLE_00_REG),
  .SWITCH_ENABLE_01 (SWITCH_ENABLE_01_REG),
  .SWITCH_ENABLE_1 (SWITCH_ENABLE_1_REG),
  .SW_TESTMODE_SEL_0 (SW_TESTMODE_SEL_0_REG),
  .SW_TESTMODE_SEL_1 (SW_TESTMODE_SEL_1_REG),
  .WRITE_PERCENT_00 (WRITE_PERCENT_00_REG),
  .WRITE_PERCENT_01 (WRITE_PERCENT_01_REG),
  .WRITE_PERCENT_02 (WRITE_PERCENT_02_REG),
  .WRITE_PERCENT_03 (WRITE_PERCENT_03_REG),
  .WRITE_PERCENT_04 (WRITE_PERCENT_04_REG),
  .WRITE_PERCENT_05 (WRITE_PERCENT_05_REG),
  .WRITE_PERCENT_06 (WRITE_PERCENT_06_REG),
  .WRITE_PERCENT_07 (WRITE_PERCENT_07_REG),
  .WRITE_PERCENT_08 (WRITE_PERCENT_08_REG),
  .WRITE_PERCENT_09 (WRITE_PERCENT_09_REG),
  .WRITE_PERCENT_10 (WRITE_PERCENT_10_REG),
  .WRITE_PERCENT_11 (WRITE_PERCENT_11_REG),
  .WRITE_PERCENT_12 (WRITE_PERCENT_12_REG),
  .WRITE_PERCENT_13 (WRITE_PERCENT_13_REG),
  .WRITE_PERCENT_14 (WRITE_PERCENT_14_REG),
  .WRITE_PERCENT_15 (WRITE_PERCENT_15_REG),
  .WRITE_PERCENT_16 (WRITE_PERCENT_16_REG),
  .WRITE_PERCENT_17 (WRITE_PERCENT_17_REG),
  .WRITE_PERCENT_18 (WRITE_PERCENT_18_REG),
  .WRITE_PERCENT_19 (WRITE_PERCENT_19_REG),
  .WRITE_PERCENT_20 (WRITE_PERCENT_20_REG),
  .WRITE_PERCENT_21 (WRITE_PERCENT_21_REG),
  .WRITE_PERCENT_22 (WRITE_PERCENT_22_REG),
  .WRITE_PERCENT_23 (WRITE_PERCENT_23_REG),
  .WRITE_PERCENT_24 (WRITE_PERCENT_24_REG),
  .WRITE_PERCENT_25 (WRITE_PERCENT_25_REG),
  .WRITE_PERCENT_26 (WRITE_PERCENT_26_REG),
  .WRITE_PERCENT_27 (WRITE_PERCENT_27_REG),
  .WRITE_PERCENT_28 (WRITE_PERCENT_28_REG),
  .WRITE_PERCENT_29 (WRITE_PERCENT_29_REG),
  .WRITE_PERCENT_30 (WRITE_PERCENT_30_REG),
  .WRITE_PERCENT_31 (WRITE_PERCENT_31_REG),
  .APB_0_PRDATA (APB_0_PRDATA_out),
  .APB_0_PREADY (APB_0_PREADY_out),
  .APB_0_PSLVERR (APB_0_PSLVERR_out),
  .APB_1_PRDATA (APB_1_PRDATA_out),
  .APB_1_PREADY (APB_1_PREADY_out),
  .APB_1_PSLVERR (APB_1_PSLVERR_out),
  .AXI_00_ARREADY (AXI_00_ARREADY_out),
  .AXI_00_AWREADY (AXI_00_AWREADY_out),
  .AXI_00_BID (AXI_00_BID_out),
  .AXI_00_BRESP (AXI_00_BRESP_out),
  .AXI_00_BVALID (AXI_00_BVALID_out),
  .AXI_00_DFI_AW_AERR_N (AXI_00_DFI_AW_AERR_N_out),
  .AXI_00_DFI_CLK_BUF (AXI_00_DFI_CLK_BUF_out),
  .AXI_00_DFI_DBI_BYTE_DISABLE (AXI_00_DFI_DBI_BYTE_DISABLE_out),
  .AXI_00_DFI_DW_RDDATA_DBI (AXI_00_DFI_DW_RDDATA_DBI_out),
  .AXI_00_DFI_DW_RDDATA_DERR (AXI_00_DFI_DW_RDDATA_DERR_out),
  .AXI_00_DFI_DW_RDDATA_VALID (AXI_00_DFI_DW_RDDATA_VALID_out),
  .AXI_00_DFI_INIT_COMPLETE (AXI_00_DFI_INIT_COMPLETE_out),
  .AXI_00_DFI_PHYUPD_REQ (AXI_00_DFI_PHYUPD_REQ_out),
  .AXI_00_DFI_PHY_LP_STATE (AXI_00_DFI_PHY_LP_STATE_out),
  .AXI_00_DFI_RST_N_BUF (AXI_00_DFI_RST_N_BUF_out),
  .AXI_00_MC_STATUS (AXI_00_MC_STATUS_out),
  .AXI_00_PHY_STATUS (AXI_00_PHY_STATUS_out),
  .AXI_00_RDATA (AXI_00_RDATA_out),
  .AXI_00_RDATA_PARITY (AXI_00_RDATA_PARITY_out),
  .AXI_00_RID (AXI_00_RID_out),
  .AXI_00_RLAST (AXI_00_RLAST_out),
  .AXI_00_RRESP (AXI_00_RRESP_out),
  .AXI_00_RVALID (AXI_00_RVALID_out),
  .AXI_00_WREADY (AXI_00_WREADY_out),
  .AXI_01_ARREADY (AXI_01_ARREADY_out),
  .AXI_01_AWREADY (AXI_01_AWREADY_out),
  .AXI_01_BID (AXI_01_BID_out),
  .AXI_01_BRESP (AXI_01_BRESP_out),
  .AXI_01_BVALID (AXI_01_BVALID_out),
  .AXI_01_DFI_AW_AERR_N (AXI_01_DFI_AW_AERR_N_out),
  .AXI_01_DFI_CLK_BUF (AXI_01_DFI_CLK_BUF_out),
  .AXI_01_DFI_DBI_BYTE_DISABLE (AXI_01_DFI_DBI_BYTE_DISABLE_out),
  .AXI_01_DFI_DW_RDDATA_DBI (AXI_01_DFI_DW_RDDATA_DBI_out),
  .AXI_01_DFI_DW_RDDATA_DERR (AXI_01_DFI_DW_RDDATA_DERR_out),
  .AXI_01_DFI_DW_RDDATA_VALID (AXI_01_DFI_DW_RDDATA_VALID_out),
  .AXI_01_DFI_INIT_COMPLETE (AXI_01_DFI_INIT_COMPLETE_out),
  .AXI_01_DFI_PHYUPD_REQ (AXI_01_DFI_PHYUPD_REQ_out),
  .AXI_01_DFI_PHY_LP_STATE (AXI_01_DFI_PHY_LP_STATE_out),
  .AXI_01_DFI_RST_N_BUF (AXI_01_DFI_RST_N_BUF_out),
  .AXI_01_RDATA (AXI_01_RDATA_out),
  .AXI_01_RDATA_PARITY (AXI_01_RDATA_PARITY_out),
  .AXI_01_RID (AXI_01_RID_out),
  .AXI_01_RLAST (AXI_01_RLAST_out),
  .AXI_01_RRESP (AXI_01_RRESP_out),
  .AXI_01_RVALID (AXI_01_RVALID_out),
  .AXI_01_WREADY (AXI_01_WREADY_out),
  .AXI_02_ARREADY (AXI_02_ARREADY_out),
  .AXI_02_AWREADY (AXI_02_AWREADY_out),
  .AXI_02_BID (AXI_02_BID_out),
  .AXI_02_BRESP (AXI_02_BRESP_out),
  .AXI_02_BVALID (AXI_02_BVALID_out),
  .AXI_02_DFI_AW_AERR_N (AXI_02_DFI_AW_AERR_N_out),
  .AXI_02_DFI_CLK_BUF (AXI_02_DFI_CLK_BUF_out),
  .AXI_02_DFI_DBI_BYTE_DISABLE (AXI_02_DFI_DBI_BYTE_DISABLE_out),
  .AXI_02_DFI_DW_RDDATA_DBI (AXI_02_DFI_DW_RDDATA_DBI_out),
  .AXI_02_DFI_DW_RDDATA_DERR (AXI_02_DFI_DW_RDDATA_DERR_out),
  .AXI_02_DFI_DW_RDDATA_VALID (AXI_02_DFI_DW_RDDATA_VALID_out),
  .AXI_02_DFI_INIT_COMPLETE (AXI_02_DFI_INIT_COMPLETE_out),
  .AXI_02_DFI_PHYUPD_REQ (AXI_02_DFI_PHYUPD_REQ_out),
  .AXI_02_DFI_PHY_LP_STATE (AXI_02_DFI_PHY_LP_STATE_out),
  .AXI_02_DFI_RST_N_BUF (AXI_02_DFI_RST_N_BUF_out),
  .AXI_02_MC_STATUS (AXI_02_MC_STATUS_out),
  .AXI_02_PHY_STATUS (AXI_02_PHY_STATUS_out),
  .AXI_02_RDATA (AXI_02_RDATA_out),
  .AXI_02_RDATA_PARITY (AXI_02_RDATA_PARITY_out),
  .AXI_02_RID (AXI_02_RID_out),
  .AXI_02_RLAST (AXI_02_RLAST_out),
  .AXI_02_RRESP (AXI_02_RRESP_out),
  .AXI_02_RVALID (AXI_02_RVALID_out),
  .AXI_02_WREADY (AXI_02_WREADY_out),
  .AXI_03_ARREADY (AXI_03_ARREADY_out),
  .AXI_03_AWREADY (AXI_03_AWREADY_out),
  .AXI_03_BID (AXI_03_BID_out),
  .AXI_03_BRESP (AXI_03_BRESP_out),
  .AXI_03_BVALID (AXI_03_BVALID_out),
  .AXI_03_DFI_AW_AERR_N (AXI_03_DFI_AW_AERR_N_out),
  .AXI_03_DFI_CLK_BUF (AXI_03_DFI_CLK_BUF_out),
  .AXI_03_DFI_DBI_BYTE_DISABLE (AXI_03_DFI_DBI_BYTE_DISABLE_out),
  .AXI_03_DFI_DW_RDDATA_DBI (AXI_03_DFI_DW_RDDATA_DBI_out),
  .AXI_03_DFI_DW_RDDATA_DERR (AXI_03_DFI_DW_RDDATA_DERR_out),
  .AXI_03_DFI_DW_RDDATA_VALID (AXI_03_DFI_DW_RDDATA_VALID_out),
  .AXI_03_DFI_INIT_COMPLETE (AXI_03_DFI_INIT_COMPLETE_out),
  .AXI_03_DFI_PHYUPD_REQ (AXI_03_DFI_PHYUPD_REQ_out),
  .AXI_03_DFI_PHY_LP_STATE (AXI_03_DFI_PHY_LP_STATE_out),
  .AXI_03_DFI_RST_N_BUF (AXI_03_DFI_RST_N_BUF_out),
  .AXI_03_RDATA (AXI_03_RDATA_out),
  .AXI_03_RDATA_PARITY (AXI_03_RDATA_PARITY_out),
  .AXI_03_RID (AXI_03_RID_out),
  .AXI_03_RLAST (AXI_03_RLAST_out),
  .AXI_03_RRESP (AXI_03_RRESP_out),
  .AXI_03_RVALID (AXI_03_RVALID_out),
  .AXI_03_WREADY (AXI_03_WREADY_out),
  .AXI_04_ARREADY (AXI_04_ARREADY_out),
  .AXI_04_AWREADY (AXI_04_AWREADY_out),
  .AXI_04_BID (AXI_04_BID_out),
  .AXI_04_BRESP (AXI_04_BRESP_out),
  .AXI_04_BVALID (AXI_04_BVALID_out),
  .AXI_04_DFI_AW_AERR_N (AXI_04_DFI_AW_AERR_N_out),
  .AXI_04_DFI_CLK_BUF (AXI_04_DFI_CLK_BUF_out),
  .AXI_04_DFI_DBI_BYTE_DISABLE (AXI_04_DFI_DBI_BYTE_DISABLE_out),
  .AXI_04_DFI_DW_RDDATA_DBI (AXI_04_DFI_DW_RDDATA_DBI_out),
  .AXI_04_DFI_DW_RDDATA_DERR (AXI_04_DFI_DW_RDDATA_DERR_out),
  .AXI_04_DFI_DW_RDDATA_VALID (AXI_04_DFI_DW_RDDATA_VALID_out),
  .AXI_04_DFI_INIT_COMPLETE (AXI_04_DFI_INIT_COMPLETE_out),
  .AXI_04_DFI_PHYUPD_REQ (AXI_04_DFI_PHYUPD_REQ_out),
  .AXI_04_DFI_PHY_LP_STATE (AXI_04_DFI_PHY_LP_STATE_out),
  .AXI_04_DFI_RST_N_BUF (AXI_04_DFI_RST_N_BUF_out),
  .AXI_04_MC_STATUS (AXI_04_MC_STATUS_out),
  .AXI_04_PHY_STATUS (AXI_04_PHY_STATUS_out),
  .AXI_04_RDATA (AXI_04_RDATA_out),
  .AXI_04_RDATA_PARITY (AXI_04_RDATA_PARITY_out),
  .AXI_04_RID (AXI_04_RID_out),
  .AXI_04_RLAST (AXI_04_RLAST_out),
  .AXI_04_RRESP (AXI_04_RRESP_out),
  .AXI_04_RVALID (AXI_04_RVALID_out),
  .AXI_04_WREADY (AXI_04_WREADY_out),
  .AXI_05_ARREADY (AXI_05_ARREADY_out),
  .AXI_05_AWREADY (AXI_05_AWREADY_out),
  .AXI_05_BID (AXI_05_BID_out),
  .AXI_05_BRESP (AXI_05_BRESP_out),
  .AXI_05_BVALID (AXI_05_BVALID_out),
  .AXI_05_DFI_AW_AERR_N (AXI_05_DFI_AW_AERR_N_out),
  .AXI_05_DFI_CLK_BUF (AXI_05_DFI_CLK_BUF_out),
  .AXI_05_DFI_DBI_BYTE_DISABLE (AXI_05_DFI_DBI_BYTE_DISABLE_out),
  .AXI_05_DFI_DW_RDDATA_DBI (AXI_05_DFI_DW_RDDATA_DBI_out),
  .AXI_05_DFI_DW_RDDATA_DERR (AXI_05_DFI_DW_RDDATA_DERR_out),
  .AXI_05_DFI_DW_RDDATA_VALID (AXI_05_DFI_DW_RDDATA_VALID_out),
  .AXI_05_DFI_INIT_COMPLETE (AXI_05_DFI_INIT_COMPLETE_out),
  .AXI_05_DFI_PHYUPD_REQ (AXI_05_DFI_PHYUPD_REQ_out),
  .AXI_05_DFI_PHY_LP_STATE (AXI_05_DFI_PHY_LP_STATE_out),
  .AXI_05_DFI_RST_N_BUF (AXI_05_DFI_RST_N_BUF_out),
  .AXI_05_RDATA (AXI_05_RDATA_out),
  .AXI_05_RDATA_PARITY (AXI_05_RDATA_PARITY_out),
  .AXI_05_RID (AXI_05_RID_out),
  .AXI_05_RLAST (AXI_05_RLAST_out),
  .AXI_05_RRESP (AXI_05_RRESP_out),
  .AXI_05_RVALID (AXI_05_RVALID_out),
  .AXI_05_WREADY (AXI_05_WREADY_out),
  .AXI_06_ARREADY (AXI_06_ARREADY_out),
  .AXI_06_AWREADY (AXI_06_AWREADY_out),
  .AXI_06_BID (AXI_06_BID_out),
  .AXI_06_BRESP (AXI_06_BRESP_out),
  .AXI_06_BVALID (AXI_06_BVALID_out),
  .AXI_06_DFI_AW_AERR_N (AXI_06_DFI_AW_AERR_N_out),
  .AXI_06_DFI_CLK_BUF (AXI_06_DFI_CLK_BUF_out),
  .AXI_06_DFI_DBI_BYTE_DISABLE (AXI_06_DFI_DBI_BYTE_DISABLE_out),
  .AXI_06_DFI_DW_RDDATA_DBI (AXI_06_DFI_DW_RDDATA_DBI_out),
  .AXI_06_DFI_DW_RDDATA_DERR (AXI_06_DFI_DW_RDDATA_DERR_out),
  .AXI_06_DFI_DW_RDDATA_VALID (AXI_06_DFI_DW_RDDATA_VALID_out),
  .AXI_06_DFI_INIT_COMPLETE (AXI_06_DFI_INIT_COMPLETE_out),
  .AXI_06_DFI_PHYUPD_REQ (AXI_06_DFI_PHYUPD_REQ_out),
  .AXI_06_DFI_PHY_LP_STATE (AXI_06_DFI_PHY_LP_STATE_out),
  .AXI_06_DFI_RST_N_BUF (AXI_06_DFI_RST_N_BUF_out),
  .AXI_06_MC_STATUS (AXI_06_MC_STATUS_out),
  .AXI_06_PHY_STATUS (AXI_06_PHY_STATUS_out),
  .AXI_06_RDATA (AXI_06_RDATA_out),
  .AXI_06_RDATA_PARITY (AXI_06_RDATA_PARITY_out),
  .AXI_06_RID (AXI_06_RID_out),
  .AXI_06_RLAST (AXI_06_RLAST_out),
  .AXI_06_RRESP (AXI_06_RRESP_out),
  .AXI_06_RVALID (AXI_06_RVALID_out),
  .AXI_06_WREADY (AXI_06_WREADY_out),
  .AXI_07_ARREADY (AXI_07_ARREADY_out),
  .AXI_07_AWREADY (AXI_07_AWREADY_out),
  .AXI_07_BID (AXI_07_BID_out),
  .AXI_07_BRESP (AXI_07_BRESP_out),
  .AXI_07_BVALID (AXI_07_BVALID_out),
  .AXI_07_DFI_AW_AERR_N (AXI_07_DFI_AW_AERR_N_out),
  .AXI_07_DFI_CLK_BUF (AXI_07_DFI_CLK_BUF_out),
  .AXI_07_DFI_DBI_BYTE_DISABLE (AXI_07_DFI_DBI_BYTE_DISABLE_out),
  .AXI_07_DFI_DW_RDDATA_DBI (AXI_07_DFI_DW_RDDATA_DBI_out),
  .AXI_07_DFI_DW_RDDATA_DERR (AXI_07_DFI_DW_RDDATA_DERR_out),
  .AXI_07_DFI_DW_RDDATA_VALID (AXI_07_DFI_DW_RDDATA_VALID_out),
  .AXI_07_DFI_INIT_COMPLETE (AXI_07_DFI_INIT_COMPLETE_out),
  .AXI_07_DFI_PHYUPD_REQ (AXI_07_DFI_PHYUPD_REQ_out),
  .AXI_07_DFI_PHY_LP_STATE (AXI_07_DFI_PHY_LP_STATE_out),
  .AXI_07_DFI_RST_N_BUF (AXI_07_DFI_RST_N_BUF_out),
  .AXI_07_RDATA (AXI_07_RDATA_out),
  .AXI_07_RDATA_PARITY (AXI_07_RDATA_PARITY_out),
  .AXI_07_RID (AXI_07_RID_out),
  .AXI_07_RLAST (AXI_07_RLAST_out),
  .AXI_07_RRESP (AXI_07_RRESP_out),
  .AXI_07_RVALID (AXI_07_RVALID_out),
  .AXI_07_WREADY (AXI_07_WREADY_out),
  .AXI_08_ARREADY (AXI_08_ARREADY_out),
  .AXI_08_AWREADY (AXI_08_AWREADY_out),
  .AXI_08_BID (AXI_08_BID_out),
  .AXI_08_BRESP (AXI_08_BRESP_out),
  .AXI_08_BVALID (AXI_08_BVALID_out),
  .AXI_08_DFI_AW_AERR_N (AXI_08_DFI_AW_AERR_N_out),
  .AXI_08_DFI_CLK_BUF (AXI_08_DFI_CLK_BUF_out),
  .AXI_08_DFI_DBI_BYTE_DISABLE (AXI_08_DFI_DBI_BYTE_DISABLE_out),
  .AXI_08_DFI_DW_RDDATA_DBI (AXI_08_DFI_DW_RDDATA_DBI_out),
  .AXI_08_DFI_DW_RDDATA_DERR (AXI_08_DFI_DW_RDDATA_DERR_out),
  .AXI_08_DFI_DW_RDDATA_VALID (AXI_08_DFI_DW_RDDATA_VALID_out),
  .AXI_08_DFI_INIT_COMPLETE (AXI_08_DFI_INIT_COMPLETE_out),
  .AXI_08_DFI_PHYUPD_REQ (AXI_08_DFI_PHYUPD_REQ_out),
  .AXI_08_DFI_PHY_LP_STATE (AXI_08_DFI_PHY_LP_STATE_out),
  .AXI_08_DFI_RST_N_BUF (AXI_08_DFI_RST_N_BUF_out),
  .AXI_08_MC_STATUS (AXI_08_MC_STATUS_out),
  .AXI_08_PHY_STATUS (AXI_08_PHY_STATUS_out),
  .AXI_08_RDATA (AXI_08_RDATA_out),
  .AXI_08_RDATA_PARITY (AXI_08_RDATA_PARITY_out),
  .AXI_08_RID (AXI_08_RID_out),
  .AXI_08_RLAST (AXI_08_RLAST_out),
  .AXI_08_RRESP (AXI_08_RRESP_out),
  .AXI_08_RVALID (AXI_08_RVALID_out),
  .AXI_08_WREADY (AXI_08_WREADY_out),
  .AXI_09_ARREADY (AXI_09_ARREADY_out),
  .AXI_09_AWREADY (AXI_09_AWREADY_out),
  .AXI_09_BID (AXI_09_BID_out),
  .AXI_09_BRESP (AXI_09_BRESP_out),
  .AXI_09_BVALID (AXI_09_BVALID_out),
  .AXI_09_DFI_AW_AERR_N (AXI_09_DFI_AW_AERR_N_out),
  .AXI_09_DFI_CLK_BUF (AXI_09_DFI_CLK_BUF_out),
  .AXI_09_DFI_DBI_BYTE_DISABLE (AXI_09_DFI_DBI_BYTE_DISABLE_out),
  .AXI_09_DFI_DW_RDDATA_DBI (AXI_09_DFI_DW_RDDATA_DBI_out),
  .AXI_09_DFI_DW_RDDATA_DERR (AXI_09_DFI_DW_RDDATA_DERR_out),
  .AXI_09_DFI_DW_RDDATA_VALID (AXI_09_DFI_DW_RDDATA_VALID_out),
  .AXI_09_DFI_INIT_COMPLETE (AXI_09_DFI_INIT_COMPLETE_out),
  .AXI_09_DFI_PHYUPD_REQ (AXI_09_DFI_PHYUPD_REQ_out),
  .AXI_09_DFI_PHY_LP_STATE (AXI_09_DFI_PHY_LP_STATE_out),
  .AXI_09_DFI_RST_N_BUF (AXI_09_DFI_RST_N_BUF_out),
  .AXI_09_RDATA (AXI_09_RDATA_out),
  .AXI_09_RDATA_PARITY (AXI_09_RDATA_PARITY_out),
  .AXI_09_RID (AXI_09_RID_out),
  .AXI_09_RLAST (AXI_09_RLAST_out),
  .AXI_09_RRESP (AXI_09_RRESP_out),
  .AXI_09_RVALID (AXI_09_RVALID_out),
  .AXI_09_WREADY (AXI_09_WREADY_out),
  .AXI_10_ARREADY (AXI_10_ARREADY_out),
  .AXI_10_AWREADY (AXI_10_AWREADY_out),
  .AXI_10_BID (AXI_10_BID_out),
  .AXI_10_BRESP (AXI_10_BRESP_out),
  .AXI_10_BVALID (AXI_10_BVALID_out),
  .AXI_10_DFI_AW_AERR_N (AXI_10_DFI_AW_AERR_N_out),
  .AXI_10_DFI_CLK_BUF (AXI_10_DFI_CLK_BUF_out),
  .AXI_10_DFI_DBI_BYTE_DISABLE (AXI_10_DFI_DBI_BYTE_DISABLE_out),
  .AXI_10_DFI_DW_RDDATA_DBI (AXI_10_DFI_DW_RDDATA_DBI_out),
  .AXI_10_DFI_DW_RDDATA_DERR (AXI_10_DFI_DW_RDDATA_DERR_out),
  .AXI_10_DFI_DW_RDDATA_VALID (AXI_10_DFI_DW_RDDATA_VALID_out),
  .AXI_10_DFI_INIT_COMPLETE (AXI_10_DFI_INIT_COMPLETE_out),
  .AXI_10_DFI_PHYUPD_REQ (AXI_10_DFI_PHYUPD_REQ_out),
  .AXI_10_DFI_PHY_LP_STATE (AXI_10_DFI_PHY_LP_STATE_out),
  .AXI_10_DFI_RST_N_BUF (AXI_10_DFI_RST_N_BUF_out),
  .AXI_10_MC_STATUS (AXI_10_MC_STATUS_out),
  .AXI_10_PHY_STATUS (AXI_10_PHY_STATUS_out),
  .AXI_10_RDATA (AXI_10_RDATA_out),
  .AXI_10_RDATA_PARITY (AXI_10_RDATA_PARITY_out),
  .AXI_10_RID (AXI_10_RID_out),
  .AXI_10_RLAST (AXI_10_RLAST_out),
  .AXI_10_RRESP (AXI_10_RRESP_out),
  .AXI_10_RVALID (AXI_10_RVALID_out),
  .AXI_10_WREADY (AXI_10_WREADY_out),
  .AXI_11_ARREADY (AXI_11_ARREADY_out),
  .AXI_11_AWREADY (AXI_11_AWREADY_out),
  .AXI_11_BID (AXI_11_BID_out),
  .AXI_11_BRESP (AXI_11_BRESP_out),
  .AXI_11_BVALID (AXI_11_BVALID_out),
  .AXI_11_DFI_AW_AERR_N (AXI_11_DFI_AW_AERR_N_out),
  .AXI_11_DFI_CLK_BUF (AXI_11_DFI_CLK_BUF_out),
  .AXI_11_DFI_DBI_BYTE_DISABLE (AXI_11_DFI_DBI_BYTE_DISABLE_out),
  .AXI_11_DFI_DW_RDDATA_DBI (AXI_11_DFI_DW_RDDATA_DBI_out),
  .AXI_11_DFI_DW_RDDATA_DERR (AXI_11_DFI_DW_RDDATA_DERR_out),
  .AXI_11_DFI_DW_RDDATA_VALID (AXI_11_DFI_DW_RDDATA_VALID_out),
  .AXI_11_DFI_INIT_COMPLETE (AXI_11_DFI_INIT_COMPLETE_out),
  .AXI_11_DFI_PHYUPD_REQ (AXI_11_DFI_PHYUPD_REQ_out),
  .AXI_11_DFI_PHY_LP_STATE (AXI_11_DFI_PHY_LP_STATE_out),
  .AXI_11_DFI_RST_N_BUF (AXI_11_DFI_RST_N_BUF_out),
  .AXI_11_RDATA (AXI_11_RDATA_out),
  .AXI_11_RDATA_PARITY (AXI_11_RDATA_PARITY_out),
  .AXI_11_RID (AXI_11_RID_out),
  .AXI_11_RLAST (AXI_11_RLAST_out),
  .AXI_11_RRESP (AXI_11_RRESP_out),
  .AXI_11_RVALID (AXI_11_RVALID_out),
  .AXI_11_WREADY (AXI_11_WREADY_out),
  .AXI_12_ARREADY (AXI_12_ARREADY_out),
  .AXI_12_AWREADY (AXI_12_AWREADY_out),
  .AXI_12_BID (AXI_12_BID_out),
  .AXI_12_BRESP (AXI_12_BRESP_out),
  .AXI_12_BVALID (AXI_12_BVALID_out),
  .AXI_12_DFI_AW_AERR_N (AXI_12_DFI_AW_AERR_N_out),
  .AXI_12_DFI_CLK_BUF (AXI_12_DFI_CLK_BUF_out),
  .AXI_12_DFI_DBI_BYTE_DISABLE (AXI_12_DFI_DBI_BYTE_DISABLE_out),
  .AXI_12_DFI_DW_RDDATA_DBI (AXI_12_DFI_DW_RDDATA_DBI_out),
  .AXI_12_DFI_DW_RDDATA_DERR (AXI_12_DFI_DW_RDDATA_DERR_out),
  .AXI_12_DFI_DW_RDDATA_VALID (AXI_12_DFI_DW_RDDATA_VALID_out),
  .AXI_12_DFI_INIT_COMPLETE (AXI_12_DFI_INIT_COMPLETE_out),
  .AXI_12_DFI_PHYUPD_REQ (AXI_12_DFI_PHYUPD_REQ_out),
  .AXI_12_DFI_PHY_LP_STATE (AXI_12_DFI_PHY_LP_STATE_out),
  .AXI_12_DFI_RST_N_BUF (AXI_12_DFI_RST_N_BUF_out),
  .AXI_12_MC_STATUS (AXI_12_MC_STATUS_out),
  .AXI_12_PHY_STATUS (AXI_12_PHY_STATUS_out),
  .AXI_12_RDATA (AXI_12_RDATA_out),
  .AXI_12_RDATA_PARITY (AXI_12_RDATA_PARITY_out),
  .AXI_12_RID (AXI_12_RID_out),
  .AXI_12_RLAST (AXI_12_RLAST_out),
  .AXI_12_RRESP (AXI_12_RRESP_out),
  .AXI_12_RVALID (AXI_12_RVALID_out),
  .AXI_12_WREADY (AXI_12_WREADY_out),
  .AXI_13_ARREADY (AXI_13_ARREADY_out),
  .AXI_13_AWREADY (AXI_13_AWREADY_out),
  .AXI_13_BID (AXI_13_BID_out),
  .AXI_13_BRESP (AXI_13_BRESP_out),
  .AXI_13_BVALID (AXI_13_BVALID_out),
  .AXI_13_DFI_AW_AERR_N (AXI_13_DFI_AW_AERR_N_out),
  .AXI_13_DFI_CLK_BUF (AXI_13_DFI_CLK_BUF_out),
  .AXI_13_DFI_DBI_BYTE_DISABLE (AXI_13_DFI_DBI_BYTE_DISABLE_out),
  .AXI_13_DFI_DW_RDDATA_DBI (AXI_13_DFI_DW_RDDATA_DBI_out),
  .AXI_13_DFI_DW_RDDATA_DERR (AXI_13_DFI_DW_RDDATA_DERR_out),
  .AXI_13_DFI_DW_RDDATA_VALID (AXI_13_DFI_DW_RDDATA_VALID_out),
  .AXI_13_DFI_INIT_COMPLETE (AXI_13_DFI_INIT_COMPLETE_out),
  .AXI_13_DFI_PHYUPD_REQ (AXI_13_DFI_PHYUPD_REQ_out),
  .AXI_13_DFI_PHY_LP_STATE (AXI_13_DFI_PHY_LP_STATE_out),
  .AXI_13_DFI_RST_N_BUF (AXI_13_DFI_RST_N_BUF_out),
  .AXI_13_RDATA (AXI_13_RDATA_out),
  .AXI_13_RDATA_PARITY (AXI_13_RDATA_PARITY_out),
  .AXI_13_RID (AXI_13_RID_out),
  .AXI_13_RLAST (AXI_13_RLAST_out),
  .AXI_13_RRESP (AXI_13_RRESP_out),
  .AXI_13_RVALID (AXI_13_RVALID_out),
  .AXI_13_WREADY (AXI_13_WREADY_out),
  .AXI_14_ARREADY (AXI_14_ARREADY_out),
  .AXI_14_AWREADY (AXI_14_AWREADY_out),
  .AXI_14_BID (AXI_14_BID_out),
  .AXI_14_BRESP (AXI_14_BRESP_out),
  .AXI_14_BVALID (AXI_14_BVALID_out),
  .AXI_14_DFI_AW_AERR_N (AXI_14_DFI_AW_AERR_N_out),
  .AXI_14_DFI_CLK_BUF (AXI_14_DFI_CLK_BUF_out),
  .AXI_14_DFI_DBI_BYTE_DISABLE (AXI_14_DFI_DBI_BYTE_DISABLE_out),
  .AXI_14_DFI_DW_RDDATA_DBI (AXI_14_DFI_DW_RDDATA_DBI_out),
  .AXI_14_DFI_DW_RDDATA_DERR (AXI_14_DFI_DW_RDDATA_DERR_out),
  .AXI_14_DFI_DW_RDDATA_VALID (AXI_14_DFI_DW_RDDATA_VALID_out),
  .AXI_14_DFI_INIT_COMPLETE (AXI_14_DFI_INIT_COMPLETE_out),
  .AXI_14_DFI_PHYUPD_REQ (AXI_14_DFI_PHYUPD_REQ_out),
  .AXI_14_DFI_PHY_LP_STATE (AXI_14_DFI_PHY_LP_STATE_out),
  .AXI_14_DFI_RST_N_BUF (AXI_14_DFI_RST_N_BUF_out),
  .AXI_14_MC_STATUS (AXI_14_MC_STATUS_out),
  .AXI_14_PHY_STATUS (AXI_14_PHY_STATUS_out),
  .AXI_14_RDATA (AXI_14_RDATA_out),
  .AXI_14_RDATA_PARITY (AXI_14_RDATA_PARITY_out),
  .AXI_14_RID (AXI_14_RID_out),
  .AXI_14_RLAST (AXI_14_RLAST_out),
  .AXI_14_RRESP (AXI_14_RRESP_out),
  .AXI_14_RVALID (AXI_14_RVALID_out),
  .AXI_14_WREADY (AXI_14_WREADY_out),
  .AXI_15_ARREADY (AXI_15_ARREADY_out),
  .AXI_15_AWREADY (AXI_15_AWREADY_out),
  .AXI_15_BID (AXI_15_BID_out),
  .AXI_15_BRESP (AXI_15_BRESP_out),
  .AXI_15_BVALID (AXI_15_BVALID_out),
  .AXI_15_DFI_AW_AERR_N (AXI_15_DFI_AW_AERR_N_out),
  .AXI_15_DFI_CLK_BUF (AXI_15_DFI_CLK_BUF_out),
  .AXI_15_DFI_DBI_BYTE_DISABLE (AXI_15_DFI_DBI_BYTE_DISABLE_out),
  .AXI_15_DFI_DW_RDDATA_DBI (AXI_15_DFI_DW_RDDATA_DBI_out),
  .AXI_15_DFI_DW_RDDATA_DERR (AXI_15_DFI_DW_RDDATA_DERR_out),
  .AXI_15_DFI_DW_RDDATA_VALID (AXI_15_DFI_DW_RDDATA_VALID_out),
  .AXI_15_DFI_INIT_COMPLETE (AXI_15_DFI_INIT_COMPLETE_out),
  .AXI_15_DFI_PHYUPD_REQ (AXI_15_DFI_PHYUPD_REQ_out),
  .AXI_15_DFI_PHY_LP_STATE (AXI_15_DFI_PHY_LP_STATE_out),
  .AXI_15_DFI_RST_N_BUF (AXI_15_DFI_RST_N_BUF_out),
  .AXI_15_RDATA (AXI_15_RDATA_out),
  .AXI_15_RDATA_PARITY (AXI_15_RDATA_PARITY_out),
  .AXI_15_RID (AXI_15_RID_out),
  .AXI_15_RLAST (AXI_15_RLAST_out),
  .AXI_15_RRESP (AXI_15_RRESP_out),
  .AXI_15_RVALID (AXI_15_RVALID_out),
  .AXI_15_WREADY (AXI_15_WREADY_out),
  .AXI_16_ARREADY (AXI_16_ARREADY_out),
  .AXI_16_AWREADY (AXI_16_AWREADY_out),
  .AXI_16_BID (AXI_16_BID_out),
  .AXI_16_BRESP (AXI_16_BRESP_out),
  .AXI_16_BVALID (AXI_16_BVALID_out),
  .AXI_16_DFI_AW_AERR_N (AXI_16_DFI_AW_AERR_N_out),
  .AXI_16_DFI_CLK_BUF (AXI_16_DFI_CLK_BUF_out),
  .AXI_16_DFI_DBI_BYTE_DISABLE (AXI_16_DFI_DBI_BYTE_DISABLE_out),
  .AXI_16_DFI_DW_RDDATA_DBI (AXI_16_DFI_DW_RDDATA_DBI_out),
  .AXI_16_DFI_DW_RDDATA_DERR (AXI_16_DFI_DW_RDDATA_DERR_out),
  .AXI_16_DFI_DW_RDDATA_VALID (AXI_16_DFI_DW_RDDATA_VALID_out),
  .AXI_16_DFI_INIT_COMPLETE (AXI_16_DFI_INIT_COMPLETE_out),
  .AXI_16_DFI_PHYUPD_REQ (AXI_16_DFI_PHYUPD_REQ_out),
  .AXI_16_DFI_PHY_LP_STATE (AXI_16_DFI_PHY_LP_STATE_out),
  .AXI_16_DFI_RST_N_BUF (AXI_16_DFI_RST_N_BUF_out),
  .AXI_16_MC_STATUS (AXI_16_MC_STATUS_out),
  .AXI_16_PHY_STATUS (AXI_16_PHY_STATUS_out),
  .AXI_16_RDATA (AXI_16_RDATA_out),
  .AXI_16_RDATA_PARITY (AXI_16_RDATA_PARITY_out),
  .AXI_16_RID (AXI_16_RID_out),
  .AXI_16_RLAST (AXI_16_RLAST_out),
  .AXI_16_RRESP (AXI_16_RRESP_out),
  .AXI_16_RVALID (AXI_16_RVALID_out),
  .AXI_16_WREADY (AXI_16_WREADY_out),
  .AXI_17_ARREADY (AXI_17_ARREADY_out),
  .AXI_17_AWREADY (AXI_17_AWREADY_out),
  .AXI_17_BID (AXI_17_BID_out),
  .AXI_17_BRESP (AXI_17_BRESP_out),
  .AXI_17_BVALID (AXI_17_BVALID_out),
  .AXI_17_DFI_AW_AERR_N (AXI_17_DFI_AW_AERR_N_out),
  .AXI_17_DFI_CLK_BUF (AXI_17_DFI_CLK_BUF_out),
  .AXI_17_DFI_DBI_BYTE_DISABLE (AXI_17_DFI_DBI_BYTE_DISABLE_out),
  .AXI_17_DFI_DW_RDDATA_DBI (AXI_17_DFI_DW_RDDATA_DBI_out),
  .AXI_17_DFI_DW_RDDATA_DERR (AXI_17_DFI_DW_RDDATA_DERR_out),
  .AXI_17_DFI_DW_RDDATA_VALID (AXI_17_DFI_DW_RDDATA_VALID_out),
  .AXI_17_DFI_INIT_COMPLETE (AXI_17_DFI_INIT_COMPLETE_out),
  .AXI_17_DFI_PHYUPD_REQ (AXI_17_DFI_PHYUPD_REQ_out),
  .AXI_17_DFI_PHY_LP_STATE (AXI_17_DFI_PHY_LP_STATE_out),
  .AXI_17_DFI_RST_N_BUF (AXI_17_DFI_RST_N_BUF_out),
  .AXI_17_RDATA (AXI_17_RDATA_out),
  .AXI_17_RDATA_PARITY (AXI_17_RDATA_PARITY_out),
  .AXI_17_RID (AXI_17_RID_out),
  .AXI_17_RLAST (AXI_17_RLAST_out),
  .AXI_17_RRESP (AXI_17_RRESP_out),
  .AXI_17_RVALID (AXI_17_RVALID_out),
  .AXI_17_WREADY (AXI_17_WREADY_out),
  .AXI_18_ARREADY (AXI_18_ARREADY_out),
  .AXI_18_AWREADY (AXI_18_AWREADY_out),
  .AXI_18_BID (AXI_18_BID_out),
  .AXI_18_BRESP (AXI_18_BRESP_out),
  .AXI_18_BVALID (AXI_18_BVALID_out),
  .AXI_18_DFI_AW_AERR_N (AXI_18_DFI_AW_AERR_N_out),
  .AXI_18_DFI_CLK_BUF (AXI_18_DFI_CLK_BUF_out),
  .AXI_18_DFI_DBI_BYTE_DISABLE (AXI_18_DFI_DBI_BYTE_DISABLE_out),
  .AXI_18_DFI_DW_RDDATA_DBI (AXI_18_DFI_DW_RDDATA_DBI_out),
  .AXI_18_DFI_DW_RDDATA_DERR (AXI_18_DFI_DW_RDDATA_DERR_out),
  .AXI_18_DFI_DW_RDDATA_VALID (AXI_18_DFI_DW_RDDATA_VALID_out),
  .AXI_18_DFI_INIT_COMPLETE (AXI_18_DFI_INIT_COMPLETE_out),
  .AXI_18_DFI_PHYUPD_REQ (AXI_18_DFI_PHYUPD_REQ_out),
  .AXI_18_DFI_PHY_LP_STATE (AXI_18_DFI_PHY_LP_STATE_out),
  .AXI_18_DFI_RST_N_BUF (AXI_18_DFI_RST_N_BUF_out),
  .AXI_18_MC_STATUS (AXI_18_MC_STATUS_out),
  .AXI_18_PHY_STATUS (AXI_18_PHY_STATUS_out),
  .AXI_18_RDATA (AXI_18_RDATA_out),
  .AXI_18_RDATA_PARITY (AXI_18_RDATA_PARITY_out),
  .AXI_18_RID (AXI_18_RID_out),
  .AXI_18_RLAST (AXI_18_RLAST_out),
  .AXI_18_RRESP (AXI_18_RRESP_out),
  .AXI_18_RVALID (AXI_18_RVALID_out),
  .AXI_18_WREADY (AXI_18_WREADY_out),
  .AXI_19_ARREADY (AXI_19_ARREADY_out),
  .AXI_19_AWREADY (AXI_19_AWREADY_out),
  .AXI_19_BID (AXI_19_BID_out),
  .AXI_19_BRESP (AXI_19_BRESP_out),
  .AXI_19_BVALID (AXI_19_BVALID_out),
  .AXI_19_DFI_AW_AERR_N (AXI_19_DFI_AW_AERR_N_out),
  .AXI_19_DFI_CLK_BUF (AXI_19_DFI_CLK_BUF_out),
  .AXI_19_DFI_DBI_BYTE_DISABLE (AXI_19_DFI_DBI_BYTE_DISABLE_out),
  .AXI_19_DFI_DW_RDDATA_DBI (AXI_19_DFI_DW_RDDATA_DBI_out),
  .AXI_19_DFI_DW_RDDATA_DERR (AXI_19_DFI_DW_RDDATA_DERR_out),
  .AXI_19_DFI_DW_RDDATA_VALID (AXI_19_DFI_DW_RDDATA_VALID_out),
  .AXI_19_DFI_INIT_COMPLETE (AXI_19_DFI_INIT_COMPLETE_out),
  .AXI_19_DFI_PHYUPD_REQ (AXI_19_DFI_PHYUPD_REQ_out),
  .AXI_19_DFI_PHY_LP_STATE (AXI_19_DFI_PHY_LP_STATE_out),
  .AXI_19_DFI_RST_N_BUF (AXI_19_DFI_RST_N_BUF_out),
  .AXI_19_RDATA (AXI_19_RDATA_out),
  .AXI_19_RDATA_PARITY (AXI_19_RDATA_PARITY_out),
  .AXI_19_RID (AXI_19_RID_out),
  .AXI_19_RLAST (AXI_19_RLAST_out),
  .AXI_19_RRESP (AXI_19_RRESP_out),
  .AXI_19_RVALID (AXI_19_RVALID_out),
  .AXI_19_WREADY (AXI_19_WREADY_out),
  .AXI_20_ARREADY (AXI_20_ARREADY_out),
  .AXI_20_AWREADY (AXI_20_AWREADY_out),
  .AXI_20_BID (AXI_20_BID_out),
  .AXI_20_BRESP (AXI_20_BRESP_out),
  .AXI_20_BVALID (AXI_20_BVALID_out),
  .AXI_20_DFI_AW_AERR_N (AXI_20_DFI_AW_AERR_N_out),
  .AXI_20_DFI_CLK_BUF (AXI_20_DFI_CLK_BUF_out),
  .AXI_20_DFI_DBI_BYTE_DISABLE (AXI_20_DFI_DBI_BYTE_DISABLE_out),
  .AXI_20_DFI_DW_RDDATA_DBI (AXI_20_DFI_DW_RDDATA_DBI_out),
  .AXI_20_DFI_DW_RDDATA_DERR (AXI_20_DFI_DW_RDDATA_DERR_out),
  .AXI_20_DFI_DW_RDDATA_VALID (AXI_20_DFI_DW_RDDATA_VALID_out),
  .AXI_20_DFI_INIT_COMPLETE (AXI_20_DFI_INIT_COMPLETE_out),
  .AXI_20_DFI_PHYUPD_REQ (AXI_20_DFI_PHYUPD_REQ_out),
  .AXI_20_DFI_PHY_LP_STATE (AXI_20_DFI_PHY_LP_STATE_out),
  .AXI_20_DFI_RST_N_BUF (AXI_20_DFI_RST_N_BUF_out),
  .AXI_20_MC_STATUS (AXI_20_MC_STATUS_out),
  .AXI_20_PHY_STATUS (AXI_20_PHY_STATUS_out),
  .AXI_20_RDATA (AXI_20_RDATA_out),
  .AXI_20_RDATA_PARITY (AXI_20_RDATA_PARITY_out),
  .AXI_20_RID (AXI_20_RID_out),
  .AXI_20_RLAST (AXI_20_RLAST_out),
  .AXI_20_RRESP (AXI_20_RRESP_out),
  .AXI_20_RVALID (AXI_20_RVALID_out),
  .AXI_20_WREADY (AXI_20_WREADY_out),
  .AXI_21_ARREADY (AXI_21_ARREADY_out),
  .AXI_21_AWREADY (AXI_21_AWREADY_out),
  .AXI_21_BID (AXI_21_BID_out),
  .AXI_21_BRESP (AXI_21_BRESP_out),
  .AXI_21_BVALID (AXI_21_BVALID_out),
  .AXI_21_DFI_AW_AERR_N (AXI_21_DFI_AW_AERR_N_out),
  .AXI_21_DFI_CLK_BUF (AXI_21_DFI_CLK_BUF_out),
  .AXI_21_DFI_DBI_BYTE_DISABLE (AXI_21_DFI_DBI_BYTE_DISABLE_out),
  .AXI_21_DFI_DW_RDDATA_DBI (AXI_21_DFI_DW_RDDATA_DBI_out),
  .AXI_21_DFI_DW_RDDATA_DERR (AXI_21_DFI_DW_RDDATA_DERR_out),
  .AXI_21_DFI_DW_RDDATA_VALID (AXI_21_DFI_DW_RDDATA_VALID_out),
  .AXI_21_DFI_INIT_COMPLETE (AXI_21_DFI_INIT_COMPLETE_out),
  .AXI_21_DFI_PHYUPD_REQ (AXI_21_DFI_PHYUPD_REQ_out),
  .AXI_21_DFI_PHY_LP_STATE (AXI_21_DFI_PHY_LP_STATE_out),
  .AXI_21_DFI_RST_N_BUF (AXI_21_DFI_RST_N_BUF_out),
  .AXI_21_RDATA (AXI_21_RDATA_out),
  .AXI_21_RDATA_PARITY (AXI_21_RDATA_PARITY_out),
  .AXI_21_RID (AXI_21_RID_out),
  .AXI_21_RLAST (AXI_21_RLAST_out),
  .AXI_21_RRESP (AXI_21_RRESP_out),
  .AXI_21_RVALID (AXI_21_RVALID_out),
  .AXI_21_WREADY (AXI_21_WREADY_out),
  .AXI_22_ARREADY (AXI_22_ARREADY_out),
  .AXI_22_AWREADY (AXI_22_AWREADY_out),
  .AXI_22_BID (AXI_22_BID_out),
  .AXI_22_BRESP (AXI_22_BRESP_out),
  .AXI_22_BVALID (AXI_22_BVALID_out),
  .AXI_22_DFI_AW_AERR_N (AXI_22_DFI_AW_AERR_N_out),
  .AXI_22_DFI_CLK_BUF (AXI_22_DFI_CLK_BUF_out),
  .AXI_22_DFI_DBI_BYTE_DISABLE (AXI_22_DFI_DBI_BYTE_DISABLE_out),
  .AXI_22_DFI_DW_RDDATA_DBI (AXI_22_DFI_DW_RDDATA_DBI_out),
  .AXI_22_DFI_DW_RDDATA_DERR (AXI_22_DFI_DW_RDDATA_DERR_out),
  .AXI_22_DFI_DW_RDDATA_VALID (AXI_22_DFI_DW_RDDATA_VALID_out),
  .AXI_22_DFI_INIT_COMPLETE (AXI_22_DFI_INIT_COMPLETE_out),
  .AXI_22_DFI_PHYUPD_REQ (AXI_22_DFI_PHYUPD_REQ_out),
  .AXI_22_DFI_PHY_LP_STATE (AXI_22_DFI_PHY_LP_STATE_out),
  .AXI_22_DFI_RST_N_BUF (AXI_22_DFI_RST_N_BUF_out),
  .AXI_22_MC_STATUS (AXI_22_MC_STATUS_out),
  .AXI_22_PHY_STATUS (AXI_22_PHY_STATUS_out),
  .AXI_22_RDATA (AXI_22_RDATA_out),
  .AXI_22_RDATA_PARITY (AXI_22_RDATA_PARITY_out),
  .AXI_22_RID (AXI_22_RID_out),
  .AXI_22_RLAST (AXI_22_RLAST_out),
  .AXI_22_RRESP (AXI_22_RRESP_out),
  .AXI_22_RVALID (AXI_22_RVALID_out),
  .AXI_22_WREADY (AXI_22_WREADY_out),
  .AXI_23_ARREADY (AXI_23_ARREADY_out),
  .AXI_23_AWREADY (AXI_23_AWREADY_out),
  .AXI_23_BID (AXI_23_BID_out),
  .AXI_23_BRESP (AXI_23_BRESP_out),
  .AXI_23_BVALID (AXI_23_BVALID_out),
  .AXI_23_DFI_AW_AERR_N (AXI_23_DFI_AW_AERR_N_out),
  .AXI_23_DFI_CLK_BUF (AXI_23_DFI_CLK_BUF_out),
  .AXI_23_DFI_DBI_BYTE_DISABLE (AXI_23_DFI_DBI_BYTE_DISABLE_out),
  .AXI_23_DFI_DW_RDDATA_DBI (AXI_23_DFI_DW_RDDATA_DBI_out),
  .AXI_23_DFI_DW_RDDATA_DERR (AXI_23_DFI_DW_RDDATA_DERR_out),
  .AXI_23_DFI_DW_RDDATA_VALID (AXI_23_DFI_DW_RDDATA_VALID_out),
  .AXI_23_DFI_INIT_COMPLETE (AXI_23_DFI_INIT_COMPLETE_out),
  .AXI_23_DFI_PHYUPD_REQ (AXI_23_DFI_PHYUPD_REQ_out),
  .AXI_23_DFI_PHY_LP_STATE (AXI_23_DFI_PHY_LP_STATE_out),
  .AXI_23_DFI_RST_N_BUF (AXI_23_DFI_RST_N_BUF_out),
  .AXI_23_RDATA (AXI_23_RDATA_out),
  .AXI_23_RDATA_PARITY (AXI_23_RDATA_PARITY_out),
  .AXI_23_RID (AXI_23_RID_out),
  .AXI_23_RLAST (AXI_23_RLAST_out),
  .AXI_23_RRESP (AXI_23_RRESP_out),
  .AXI_23_RVALID (AXI_23_RVALID_out),
  .AXI_23_WREADY (AXI_23_WREADY_out),
  .AXI_24_ARREADY (AXI_24_ARREADY_out),
  .AXI_24_AWREADY (AXI_24_AWREADY_out),
  .AXI_24_BID (AXI_24_BID_out),
  .AXI_24_BRESP (AXI_24_BRESP_out),
  .AXI_24_BVALID (AXI_24_BVALID_out),
  .AXI_24_DFI_AW_AERR_N (AXI_24_DFI_AW_AERR_N_out),
  .AXI_24_DFI_CLK_BUF (AXI_24_DFI_CLK_BUF_out),
  .AXI_24_DFI_DBI_BYTE_DISABLE (AXI_24_DFI_DBI_BYTE_DISABLE_out),
  .AXI_24_DFI_DW_RDDATA_DBI (AXI_24_DFI_DW_RDDATA_DBI_out),
  .AXI_24_DFI_DW_RDDATA_DERR (AXI_24_DFI_DW_RDDATA_DERR_out),
  .AXI_24_DFI_DW_RDDATA_VALID (AXI_24_DFI_DW_RDDATA_VALID_out),
  .AXI_24_DFI_INIT_COMPLETE (AXI_24_DFI_INIT_COMPLETE_out),
  .AXI_24_DFI_PHYUPD_REQ (AXI_24_DFI_PHYUPD_REQ_out),
  .AXI_24_DFI_PHY_LP_STATE (AXI_24_DFI_PHY_LP_STATE_out),
  .AXI_24_DFI_RST_N_BUF (AXI_24_DFI_RST_N_BUF_out),
  .AXI_24_MC_STATUS (AXI_24_MC_STATUS_out),
  .AXI_24_PHY_STATUS (AXI_24_PHY_STATUS_out),
  .AXI_24_RDATA (AXI_24_RDATA_out),
  .AXI_24_RDATA_PARITY (AXI_24_RDATA_PARITY_out),
  .AXI_24_RID (AXI_24_RID_out),
  .AXI_24_RLAST (AXI_24_RLAST_out),
  .AXI_24_RRESP (AXI_24_RRESP_out),
  .AXI_24_RVALID (AXI_24_RVALID_out),
  .AXI_24_WREADY (AXI_24_WREADY_out),
  .AXI_25_ARREADY (AXI_25_ARREADY_out),
  .AXI_25_AWREADY (AXI_25_AWREADY_out),
  .AXI_25_BID (AXI_25_BID_out),
  .AXI_25_BRESP (AXI_25_BRESP_out),
  .AXI_25_BVALID (AXI_25_BVALID_out),
  .AXI_25_DFI_AW_AERR_N (AXI_25_DFI_AW_AERR_N_out),
  .AXI_25_DFI_CLK_BUF (AXI_25_DFI_CLK_BUF_out),
  .AXI_25_DFI_DBI_BYTE_DISABLE (AXI_25_DFI_DBI_BYTE_DISABLE_out),
  .AXI_25_DFI_DW_RDDATA_DBI (AXI_25_DFI_DW_RDDATA_DBI_out),
  .AXI_25_DFI_DW_RDDATA_DERR (AXI_25_DFI_DW_RDDATA_DERR_out),
  .AXI_25_DFI_DW_RDDATA_VALID (AXI_25_DFI_DW_RDDATA_VALID_out),
  .AXI_25_DFI_INIT_COMPLETE (AXI_25_DFI_INIT_COMPLETE_out),
  .AXI_25_DFI_PHYUPD_REQ (AXI_25_DFI_PHYUPD_REQ_out),
  .AXI_25_DFI_PHY_LP_STATE (AXI_25_DFI_PHY_LP_STATE_out),
  .AXI_25_DFI_RST_N_BUF (AXI_25_DFI_RST_N_BUF_out),
  .AXI_25_RDATA (AXI_25_RDATA_out),
  .AXI_25_RDATA_PARITY (AXI_25_RDATA_PARITY_out),
  .AXI_25_RID (AXI_25_RID_out),
  .AXI_25_RLAST (AXI_25_RLAST_out),
  .AXI_25_RRESP (AXI_25_RRESP_out),
  .AXI_25_RVALID (AXI_25_RVALID_out),
  .AXI_25_WREADY (AXI_25_WREADY_out),
  .AXI_26_ARREADY (AXI_26_ARREADY_out),
  .AXI_26_AWREADY (AXI_26_AWREADY_out),
  .AXI_26_BID (AXI_26_BID_out),
  .AXI_26_BRESP (AXI_26_BRESP_out),
  .AXI_26_BVALID (AXI_26_BVALID_out),
  .AXI_26_DFI_AW_AERR_N (AXI_26_DFI_AW_AERR_N_out),
  .AXI_26_DFI_CLK_BUF (AXI_26_DFI_CLK_BUF_out),
  .AXI_26_DFI_DBI_BYTE_DISABLE (AXI_26_DFI_DBI_BYTE_DISABLE_out),
  .AXI_26_DFI_DW_RDDATA_DBI (AXI_26_DFI_DW_RDDATA_DBI_out),
  .AXI_26_DFI_DW_RDDATA_DERR (AXI_26_DFI_DW_RDDATA_DERR_out),
  .AXI_26_DFI_DW_RDDATA_VALID (AXI_26_DFI_DW_RDDATA_VALID_out),
  .AXI_26_DFI_INIT_COMPLETE (AXI_26_DFI_INIT_COMPLETE_out),
  .AXI_26_DFI_PHYUPD_REQ (AXI_26_DFI_PHYUPD_REQ_out),
  .AXI_26_DFI_PHY_LP_STATE (AXI_26_DFI_PHY_LP_STATE_out),
  .AXI_26_DFI_RST_N_BUF (AXI_26_DFI_RST_N_BUF_out),
  .AXI_26_MC_STATUS (AXI_26_MC_STATUS_out),
  .AXI_26_PHY_STATUS (AXI_26_PHY_STATUS_out),
  .AXI_26_RDATA (AXI_26_RDATA_out),
  .AXI_26_RDATA_PARITY (AXI_26_RDATA_PARITY_out),
  .AXI_26_RID (AXI_26_RID_out),
  .AXI_26_RLAST (AXI_26_RLAST_out),
  .AXI_26_RRESP (AXI_26_RRESP_out),
  .AXI_26_RVALID (AXI_26_RVALID_out),
  .AXI_26_WREADY (AXI_26_WREADY_out),
  .AXI_27_ARREADY (AXI_27_ARREADY_out),
  .AXI_27_AWREADY (AXI_27_AWREADY_out),
  .AXI_27_BID (AXI_27_BID_out),
  .AXI_27_BRESP (AXI_27_BRESP_out),
  .AXI_27_BVALID (AXI_27_BVALID_out),
  .AXI_27_DFI_AW_AERR_N (AXI_27_DFI_AW_AERR_N_out),
  .AXI_27_DFI_CLK_BUF (AXI_27_DFI_CLK_BUF_out),
  .AXI_27_DFI_DBI_BYTE_DISABLE (AXI_27_DFI_DBI_BYTE_DISABLE_out),
  .AXI_27_DFI_DW_RDDATA_DBI (AXI_27_DFI_DW_RDDATA_DBI_out),
  .AXI_27_DFI_DW_RDDATA_DERR (AXI_27_DFI_DW_RDDATA_DERR_out),
  .AXI_27_DFI_DW_RDDATA_VALID (AXI_27_DFI_DW_RDDATA_VALID_out),
  .AXI_27_DFI_INIT_COMPLETE (AXI_27_DFI_INIT_COMPLETE_out),
  .AXI_27_DFI_PHYUPD_REQ (AXI_27_DFI_PHYUPD_REQ_out),
  .AXI_27_DFI_PHY_LP_STATE (AXI_27_DFI_PHY_LP_STATE_out),
  .AXI_27_DFI_RST_N_BUF (AXI_27_DFI_RST_N_BUF_out),
  .AXI_27_RDATA (AXI_27_RDATA_out),
  .AXI_27_RDATA_PARITY (AXI_27_RDATA_PARITY_out),
  .AXI_27_RID (AXI_27_RID_out),
  .AXI_27_RLAST (AXI_27_RLAST_out),
  .AXI_27_RRESP (AXI_27_RRESP_out),
  .AXI_27_RVALID (AXI_27_RVALID_out),
  .AXI_27_WREADY (AXI_27_WREADY_out),
  .AXI_28_ARREADY (AXI_28_ARREADY_out),
  .AXI_28_AWREADY (AXI_28_AWREADY_out),
  .AXI_28_BID (AXI_28_BID_out),
  .AXI_28_BRESP (AXI_28_BRESP_out),
  .AXI_28_BVALID (AXI_28_BVALID_out),
  .AXI_28_DFI_AW_AERR_N (AXI_28_DFI_AW_AERR_N_out),
  .AXI_28_DFI_CLK_BUF (AXI_28_DFI_CLK_BUF_out),
  .AXI_28_DFI_DBI_BYTE_DISABLE (AXI_28_DFI_DBI_BYTE_DISABLE_out),
  .AXI_28_DFI_DW_RDDATA_DBI (AXI_28_DFI_DW_RDDATA_DBI_out),
  .AXI_28_DFI_DW_RDDATA_DERR (AXI_28_DFI_DW_RDDATA_DERR_out),
  .AXI_28_DFI_DW_RDDATA_VALID (AXI_28_DFI_DW_RDDATA_VALID_out),
  .AXI_28_DFI_INIT_COMPLETE (AXI_28_DFI_INIT_COMPLETE_out),
  .AXI_28_DFI_PHYUPD_REQ (AXI_28_DFI_PHYUPD_REQ_out),
  .AXI_28_DFI_PHY_LP_STATE (AXI_28_DFI_PHY_LP_STATE_out),
  .AXI_28_DFI_RST_N_BUF (AXI_28_DFI_RST_N_BUF_out),
  .AXI_28_MC_STATUS (AXI_28_MC_STATUS_out),
  .AXI_28_PHY_STATUS (AXI_28_PHY_STATUS_out),
  .AXI_28_RDATA (AXI_28_RDATA_out),
  .AXI_28_RDATA_PARITY (AXI_28_RDATA_PARITY_out),
  .AXI_28_RID (AXI_28_RID_out),
  .AXI_28_RLAST (AXI_28_RLAST_out),
  .AXI_28_RRESP (AXI_28_RRESP_out),
  .AXI_28_RVALID (AXI_28_RVALID_out),
  .AXI_28_WREADY (AXI_28_WREADY_out),
  .AXI_29_ARREADY (AXI_29_ARREADY_out),
  .AXI_29_AWREADY (AXI_29_AWREADY_out),
  .AXI_29_BID (AXI_29_BID_out),
  .AXI_29_BRESP (AXI_29_BRESP_out),
  .AXI_29_BVALID (AXI_29_BVALID_out),
  .AXI_29_DFI_AW_AERR_N (AXI_29_DFI_AW_AERR_N_out),
  .AXI_29_DFI_CLK_BUF (AXI_29_DFI_CLK_BUF_out),
  .AXI_29_DFI_DBI_BYTE_DISABLE (AXI_29_DFI_DBI_BYTE_DISABLE_out),
  .AXI_29_DFI_DW_RDDATA_DBI (AXI_29_DFI_DW_RDDATA_DBI_out),
  .AXI_29_DFI_DW_RDDATA_DERR (AXI_29_DFI_DW_RDDATA_DERR_out),
  .AXI_29_DFI_DW_RDDATA_VALID (AXI_29_DFI_DW_RDDATA_VALID_out),
  .AXI_29_DFI_INIT_COMPLETE (AXI_29_DFI_INIT_COMPLETE_out),
  .AXI_29_DFI_PHYUPD_REQ (AXI_29_DFI_PHYUPD_REQ_out),
  .AXI_29_DFI_PHY_LP_STATE (AXI_29_DFI_PHY_LP_STATE_out),
  .AXI_29_DFI_RST_N_BUF (AXI_29_DFI_RST_N_BUF_out),
  .AXI_29_RDATA (AXI_29_RDATA_out),
  .AXI_29_RDATA_PARITY (AXI_29_RDATA_PARITY_out),
  .AXI_29_RID (AXI_29_RID_out),
  .AXI_29_RLAST (AXI_29_RLAST_out),
  .AXI_29_RRESP (AXI_29_RRESP_out),
  .AXI_29_RVALID (AXI_29_RVALID_out),
  .AXI_29_WREADY (AXI_29_WREADY_out),
  .AXI_30_ARREADY (AXI_30_ARREADY_out),
  .AXI_30_AWREADY (AXI_30_AWREADY_out),
  .AXI_30_BID (AXI_30_BID_out),
  .AXI_30_BRESP (AXI_30_BRESP_out),
  .AXI_30_BVALID (AXI_30_BVALID_out),
  .AXI_30_DFI_AW_AERR_N (AXI_30_DFI_AW_AERR_N_out),
  .AXI_30_DFI_CLK_BUF (AXI_30_DFI_CLK_BUF_out),
  .AXI_30_DFI_DBI_BYTE_DISABLE (AXI_30_DFI_DBI_BYTE_DISABLE_out),
  .AXI_30_DFI_DW_RDDATA_DBI (AXI_30_DFI_DW_RDDATA_DBI_out),
  .AXI_30_DFI_DW_RDDATA_DERR (AXI_30_DFI_DW_RDDATA_DERR_out),
  .AXI_30_DFI_DW_RDDATA_VALID (AXI_30_DFI_DW_RDDATA_VALID_out),
  .AXI_30_DFI_INIT_COMPLETE (AXI_30_DFI_INIT_COMPLETE_out),
  .AXI_30_DFI_PHYUPD_REQ (AXI_30_DFI_PHYUPD_REQ_out),
  .AXI_30_DFI_PHY_LP_STATE (AXI_30_DFI_PHY_LP_STATE_out),
  .AXI_30_DFI_RST_N_BUF (AXI_30_DFI_RST_N_BUF_out),
  .AXI_30_MC_STATUS (AXI_30_MC_STATUS_out),
  .AXI_30_PHY_STATUS (AXI_30_PHY_STATUS_out),
  .AXI_30_RDATA (AXI_30_RDATA_out),
  .AXI_30_RDATA_PARITY (AXI_30_RDATA_PARITY_out),
  .AXI_30_RID (AXI_30_RID_out),
  .AXI_30_RLAST (AXI_30_RLAST_out),
  .AXI_30_RRESP (AXI_30_RRESP_out),
  .AXI_30_RVALID (AXI_30_RVALID_out),
  .AXI_30_WREADY (AXI_30_WREADY_out),
  .AXI_31_ARREADY (AXI_31_ARREADY_out),
  .AXI_31_AWREADY (AXI_31_AWREADY_out),
  .AXI_31_BID (AXI_31_BID_out),
  .AXI_31_BRESP (AXI_31_BRESP_out),
  .AXI_31_BVALID (AXI_31_BVALID_out),
  .AXI_31_DFI_AW_AERR_N (AXI_31_DFI_AW_AERR_N_out),
  .AXI_31_DFI_CLK_BUF (AXI_31_DFI_CLK_BUF_out),
  .AXI_31_DFI_DBI_BYTE_DISABLE (AXI_31_DFI_DBI_BYTE_DISABLE_out),
  .AXI_31_DFI_DW_RDDATA_DBI (AXI_31_DFI_DW_RDDATA_DBI_out),
  .AXI_31_DFI_DW_RDDATA_DERR (AXI_31_DFI_DW_RDDATA_DERR_out),
  .AXI_31_DFI_DW_RDDATA_VALID (AXI_31_DFI_DW_RDDATA_VALID_out),
  .AXI_31_DFI_INIT_COMPLETE (AXI_31_DFI_INIT_COMPLETE_out),
  .AXI_31_DFI_PHYUPD_REQ (AXI_31_DFI_PHYUPD_REQ_out),
  .AXI_31_DFI_PHY_LP_STATE (AXI_31_DFI_PHY_LP_STATE_out),
  .AXI_31_DFI_RST_N_BUF (AXI_31_DFI_RST_N_BUF_out),
  .AXI_31_RDATA (AXI_31_RDATA_out),
  .AXI_31_RDATA_PARITY (AXI_31_RDATA_PARITY_out),
  .AXI_31_RID (AXI_31_RID_out),
  .AXI_31_RLAST (AXI_31_RLAST_out),
  .AXI_31_RRESP (AXI_31_RRESP_out),
  .AXI_31_RVALID (AXI_31_RVALID_out),
  .AXI_31_WREADY (AXI_31_WREADY_out),
  .BLI_SCAN_OUT_00 (BLI_SCAN_OUT_00_out),
  .BLI_SCAN_OUT_01 (BLI_SCAN_OUT_01_out),
  .BLI_SCAN_OUT_02 (BLI_SCAN_OUT_02_out),
  .BLI_SCAN_OUT_03 (BLI_SCAN_OUT_03_out),
  .BLI_SCAN_OUT_04 (BLI_SCAN_OUT_04_out),
  .BLI_SCAN_OUT_05 (BLI_SCAN_OUT_05_out),
  .BLI_SCAN_OUT_06 (BLI_SCAN_OUT_06_out),
  .BLI_SCAN_OUT_07 (BLI_SCAN_OUT_07_out),
  .BLI_SCAN_OUT_08 (BLI_SCAN_OUT_08_out),
  .BLI_SCAN_OUT_09 (BLI_SCAN_OUT_09_out),
  .BLI_SCAN_OUT_10 (BLI_SCAN_OUT_10_out),
  .BLI_SCAN_OUT_11 (BLI_SCAN_OUT_11_out),
  .BLI_SCAN_OUT_12 (BLI_SCAN_OUT_12_out),
  .BLI_SCAN_OUT_13 (BLI_SCAN_OUT_13_out),
  .BLI_SCAN_OUT_14 (BLI_SCAN_OUT_14_out),
  .BLI_SCAN_OUT_15 (BLI_SCAN_OUT_15_out),
  .BLI_SCAN_OUT_16 (BLI_SCAN_OUT_16_out),
  .BLI_SCAN_OUT_17 (BLI_SCAN_OUT_17_out),
  .BLI_SCAN_OUT_18 (BLI_SCAN_OUT_18_out),
  .BLI_SCAN_OUT_19 (BLI_SCAN_OUT_19_out),
  .BLI_SCAN_OUT_20 (BLI_SCAN_OUT_20_out),
  .BLI_SCAN_OUT_21 (BLI_SCAN_OUT_21_out),
  .BLI_SCAN_OUT_22 (BLI_SCAN_OUT_22_out),
  .BLI_SCAN_OUT_23 (BLI_SCAN_OUT_23_out),
  .BLI_SCAN_OUT_24 (BLI_SCAN_OUT_24_out),
  .BLI_SCAN_OUT_25 (BLI_SCAN_OUT_25_out),
  .BLI_SCAN_OUT_26 (BLI_SCAN_OUT_26_out),
  .BLI_SCAN_OUT_27 (BLI_SCAN_OUT_27_out),
  .BLI_SCAN_OUT_28 (BLI_SCAN_OUT_28_out),
  .BLI_SCAN_OUT_29 (BLI_SCAN_OUT_29_out),
  .BLI_SCAN_OUT_30 (BLI_SCAN_OUT_30_out),
  .BLI_SCAN_OUT_31 (BLI_SCAN_OUT_31_out),
  .DBG_OUT_00 (DBG_OUT_00_out),
  .DBG_OUT_01 (DBG_OUT_01_out),
  .DBG_OUT_02 (DBG_OUT_02_out),
  .DBG_OUT_03 (DBG_OUT_03_out),
  .DBG_OUT_04 (DBG_OUT_04_out),
  .DBG_OUT_05 (DBG_OUT_05_out),
  .DBG_OUT_06 (DBG_OUT_06_out),
  .DBG_OUT_07 (DBG_OUT_07_out),
  .DBG_OUT_08 (DBG_OUT_08_out),
  .DBG_OUT_09 (DBG_OUT_09_out),
  .DBG_OUT_10 (DBG_OUT_10_out),
  .DBG_OUT_11 (DBG_OUT_11_out),
  .DBG_OUT_12 (DBG_OUT_12_out),
  .DBG_OUT_13 (DBG_OUT_13_out),
  .DBG_OUT_14 (DBG_OUT_14_out),
  .DBG_OUT_15 (DBG_OUT_15_out),
  .DBG_OUT_16 (DBG_OUT_16_out),
  .DBG_OUT_17 (DBG_OUT_17_out),
  .DBG_OUT_18 (DBG_OUT_18_out),
  .DBG_OUT_19 (DBG_OUT_19_out),
  .DBG_OUT_20 (DBG_OUT_20_out),
  .DBG_OUT_21 (DBG_OUT_21_out),
  .DBG_OUT_22 (DBG_OUT_22_out),
  .DBG_OUT_23 (DBG_OUT_23_out),
  .DBG_OUT_24 (DBG_OUT_24_out),
  .DBG_OUT_25 (DBG_OUT_25_out),
  .DBG_OUT_26 (DBG_OUT_26_out),
  .DBG_OUT_27 (DBG_OUT_27_out),
  .DBG_OUT_28 (DBG_OUT_28_out),
  .DBG_OUT_29 (DBG_OUT_29_out),
  .DBG_OUT_30 (DBG_OUT_30_out),
  .DBG_OUT_31 (DBG_OUT_31_out),
  .DLL_SCAN_OUT_00 (DLL_SCAN_OUT_00_out),
  .DLL_SCAN_OUT_01 (DLL_SCAN_OUT_01_out),
  .DRAM_0_STAT_CATTRIP (DRAM_0_STAT_CATTRIP_out),
  .DRAM_0_STAT_TEMP (DRAM_0_STAT_TEMP_out),
  .DRAM_1_STAT_CATTRIP (DRAM_1_STAT_CATTRIP_out),
  .DRAM_1_STAT_TEMP (DRAM_1_STAT_TEMP_out),
  .IO_SCAN_OUT_00 (IO_SCAN_OUT_00_out),
  .IO_SCAN_OUT_01 (IO_SCAN_OUT_01_out),
  .MC_SCAN_OUT_00 (MC_SCAN_OUT_00_out),
  .MC_SCAN_OUT_01 (MC_SCAN_OUT_01_out),
  .MC_SCAN_OUT_02 (MC_SCAN_OUT_02_out),
  .MC_SCAN_OUT_03 (MC_SCAN_OUT_03_out),
  .MC_SCAN_OUT_04 (MC_SCAN_OUT_04_out),
  .MC_SCAN_OUT_05 (MC_SCAN_OUT_05_out),
  .MC_SCAN_OUT_06 (MC_SCAN_OUT_06_out),
  .MC_SCAN_OUT_07 (MC_SCAN_OUT_07_out),
  .MC_SCAN_OUT_08 (MC_SCAN_OUT_08_out),
  .MC_SCAN_OUT_09 (MC_SCAN_OUT_09_out),
  .MC_SCAN_OUT_10 (MC_SCAN_OUT_10_out),
  .MC_SCAN_OUT_11 (MC_SCAN_OUT_11_out),
  .MC_SCAN_OUT_12 (MC_SCAN_OUT_12_out),
  .MC_SCAN_OUT_13 (MC_SCAN_OUT_13_out),
  .MC_SCAN_OUT_14 (MC_SCAN_OUT_14_out),
  .MC_SCAN_OUT_15 (MC_SCAN_OUT_15_out),
  .PHY_SCAN_OUT_00 (PHY_SCAN_OUT_00_out),
  .PHY_SCAN_OUT_01 (PHY_SCAN_OUT_01_out),
  .STATUS_00 (STATUS_00_out),
  .STATUS_01 (STATUS_01_out),
  .STATUS_02 (STATUS_02_out),
  .STATUS_03 (STATUS_03_out),
  .STATUS_04 (STATUS_04_out),
  .STATUS_05 (STATUS_05_out),
  .STATUS_06 (STATUS_06_out),
  .STATUS_07 (STATUS_07_out),
  .STATUS_08 (STATUS_08_out),
  .STATUS_09 (STATUS_09_out),
  .STATUS_10 (STATUS_10_out),
  .STATUS_11 (STATUS_11_out),
  .STATUS_12 (STATUS_12_out),
  .STATUS_13 (STATUS_13_out),
  .STATUS_14 (STATUS_14_out),
  .STATUS_15 (STATUS_15_out),
  .SW_SCAN_OUT_00 (SW_SCAN_OUT_00_out),
  .SW_SCAN_OUT_01 (SW_SCAN_OUT_01_out),
  .SW_SCAN_OUT_02 (SW_SCAN_OUT_02_out),
  .SW_SCAN_OUT_03 (SW_SCAN_OUT_03_out),
  .SW_SCAN_OUT_04 (SW_SCAN_OUT_04_out),
  .SW_SCAN_OUT_05 (SW_SCAN_OUT_05_out),
  .SW_SCAN_OUT_06 (SW_SCAN_OUT_06_out),
  .SW_SCAN_OUT_07 (SW_SCAN_OUT_07_out),
  .ANALOG_HBM_SEL_00 (ANALOG_HBM_SEL_00_in),
  .ANALOG_HBM_SEL_01 (ANALOG_HBM_SEL_01_in),
  .APB_0_PADDR (APB_0_PADDR_in),
  .APB_0_PCLK (APB_0_PCLK_in),
  .APB_0_PENABLE (APB_0_PENABLE_in),
  .APB_0_PRESET_N (APB_0_PRESET_N_in),
  .APB_0_PSEL (APB_0_PSEL_in),
  .APB_0_PWDATA (APB_0_PWDATA_in),
  .APB_0_PWRITE (APB_0_PWRITE_in),
  .APB_1_PADDR (APB_1_PADDR_in),
  .APB_1_PCLK (APB_1_PCLK_in),
  .APB_1_PENABLE (APB_1_PENABLE_in),
  .APB_1_PRESET_N (APB_1_PRESET_N_in),
  .APB_1_PSEL (APB_1_PSEL_in),
  .APB_1_PWDATA (APB_1_PWDATA_in),
  .APB_1_PWRITE (APB_1_PWRITE_in),
  .AXI_00_ACLK (AXI_00_ACLK_in),
  .AXI_00_ARADDR (AXI_00_ARADDR_in),
  .AXI_00_ARBURST (AXI_00_ARBURST_in),
  .AXI_00_ARESET_N (AXI_00_ARESET_N_in),
  .AXI_00_ARID (AXI_00_ARID_in),
  .AXI_00_ARLEN (AXI_00_ARLEN_in),
  .AXI_00_ARSIZE (AXI_00_ARSIZE_in),
  .AXI_00_ARVALID (AXI_00_ARVALID_in),
  .AXI_00_AWADDR (AXI_00_AWADDR_in),
  .AXI_00_AWBURST (AXI_00_AWBURST_in),
  .AXI_00_AWID (AXI_00_AWID_in),
  .AXI_00_AWLEN (AXI_00_AWLEN_in),
  .AXI_00_AWSIZE (AXI_00_AWSIZE_in),
  .AXI_00_AWVALID (AXI_00_AWVALID_in),
  .AXI_00_BREADY (AXI_00_BREADY_in),
  .AXI_00_DFI_LP_PWR_X_REQ (AXI_00_DFI_LP_PWR_X_REQ_in),
  .AXI_00_RREADY (AXI_00_RREADY_in),
  .AXI_00_WDATA (AXI_00_WDATA_in),
  .AXI_00_WDATA_PARITY (AXI_00_WDATA_PARITY_in),
  .AXI_00_WLAST (AXI_00_WLAST_in),
  .AXI_00_WSTRB (AXI_00_WSTRB_in),
  .AXI_00_WVALID (AXI_00_WVALID_in),
  .AXI_01_ACLK (AXI_01_ACLK_in),
  .AXI_01_ARADDR (AXI_01_ARADDR_in),
  .AXI_01_ARBURST (AXI_01_ARBURST_in),
  .AXI_01_ARESET_N (AXI_01_ARESET_N_in),
  .AXI_01_ARID (AXI_01_ARID_in),
  .AXI_01_ARLEN (AXI_01_ARLEN_in),
  .AXI_01_ARSIZE (AXI_01_ARSIZE_in),
  .AXI_01_ARVALID (AXI_01_ARVALID_in),
  .AXI_01_AWADDR (AXI_01_AWADDR_in),
  .AXI_01_AWBURST (AXI_01_AWBURST_in),
  .AXI_01_AWID (AXI_01_AWID_in),
  .AXI_01_AWLEN (AXI_01_AWLEN_in),
  .AXI_01_AWSIZE (AXI_01_AWSIZE_in),
  .AXI_01_AWVALID (AXI_01_AWVALID_in),
  .AXI_01_BREADY (AXI_01_BREADY_in),
  .AXI_01_DFI_LP_PWR_X_REQ (AXI_01_DFI_LP_PWR_X_REQ_in),
  .AXI_01_RREADY (AXI_01_RREADY_in),
  .AXI_01_WDATA (AXI_01_WDATA_in),
  .AXI_01_WDATA_PARITY (AXI_01_WDATA_PARITY_in),
  .AXI_01_WLAST (AXI_01_WLAST_in),
  .AXI_01_WSTRB (AXI_01_WSTRB_in),
  .AXI_01_WVALID (AXI_01_WVALID_in),
  .AXI_02_ACLK (AXI_02_ACLK_in),
  .AXI_02_ARADDR (AXI_02_ARADDR_in),
  .AXI_02_ARBURST (AXI_02_ARBURST_in),
  .AXI_02_ARESET_N (AXI_02_ARESET_N_in),
  .AXI_02_ARID (AXI_02_ARID_in),
  .AXI_02_ARLEN (AXI_02_ARLEN_in),
  .AXI_02_ARSIZE (AXI_02_ARSIZE_in),
  .AXI_02_ARVALID (AXI_02_ARVALID_in),
  .AXI_02_AWADDR (AXI_02_AWADDR_in),
  .AXI_02_AWBURST (AXI_02_AWBURST_in),
  .AXI_02_AWID (AXI_02_AWID_in),
  .AXI_02_AWLEN (AXI_02_AWLEN_in),
  .AXI_02_AWSIZE (AXI_02_AWSIZE_in),
  .AXI_02_AWVALID (AXI_02_AWVALID_in),
  .AXI_02_BREADY (AXI_02_BREADY_in),
  .AXI_02_DFI_LP_PWR_X_REQ (AXI_02_DFI_LP_PWR_X_REQ_in),
  .AXI_02_RREADY (AXI_02_RREADY_in),
  .AXI_02_WDATA (AXI_02_WDATA_in),
  .AXI_02_WDATA_PARITY (AXI_02_WDATA_PARITY_in),
  .AXI_02_WLAST (AXI_02_WLAST_in),
  .AXI_02_WSTRB (AXI_02_WSTRB_in),
  .AXI_02_WVALID (AXI_02_WVALID_in),
  .AXI_03_ACLK (AXI_03_ACLK_in),
  .AXI_03_ARADDR (AXI_03_ARADDR_in),
  .AXI_03_ARBURST (AXI_03_ARBURST_in),
  .AXI_03_ARESET_N (AXI_03_ARESET_N_in),
  .AXI_03_ARID (AXI_03_ARID_in),
  .AXI_03_ARLEN (AXI_03_ARLEN_in),
  .AXI_03_ARSIZE (AXI_03_ARSIZE_in),
  .AXI_03_ARVALID (AXI_03_ARVALID_in),
  .AXI_03_AWADDR (AXI_03_AWADDR_in),
  .AXI_03_AWBURST (AXI_03_AWBURST_in),
  .AXI_03_AWID (AXI_03_AWID_in),
  .AXI_03_AWLEN (AXI_03_AWLEN_in),
  .AXI_03_AWSIZE (AXI_03_AWSIZE_in),
  .AXI_03_AWVALID (AXI_03_AWVALID_in),
  .AXI_03_BREADY (AXI_03_BREADY_in),
  .AXI_03_DFI_LP_PWR_X_REQ (AXI_03_DFI_LP_PWR_X_REQ_in),
  .AXI_03_RREADY (AXI_03_RREADY_in),
  .AXI_03_WDATA (AXI_03_WDATA_in),
  .AXI_03_WDATA_PARITY (AXI_03_WDATA_PARITY_in),
  .AXI_03_WLAST (AXI_03_WLAST_in),
  .AXI_03_WSTRB (AXI_03_WSTRB_in),
  .AXI_03_WVALID (AXI_03_WVALID_in),
  .AXI_04_ACLK (AXI_04_ACLK_in),
  .AXI_04_ARADDR (AXI_04_ARADDR_in),
  .AXI_04_ARBURST (AXI_04_ARBURST_in),
  .AXI_04_ARESET_N (AXI_04_ARESET_N_in),
  .AXI_04_ARID (AXI_04_ARID_in),
  .AXI_04_ARLEN (AXI_04_ARLEN_in),
  .AXI_04_ARSIZE (AXI_04_ARSIZE_in),
  .AXI_04_ARVALID (AXI_04_ARVALID_in),
  .AXI_04_AWADDR (AXI_04_AWADDR_in),
  .AXI_04_AWBURST (AXI_04_AWBURST_in),
  .AXI_04_AWID (AXI_04_AWID_in),
  .AXI_04_AWLEN (AXI_04_AWLEN_in),
  .AXI_04_AWSIZE (AXI_04_AWSIZE_in),
  .AXI_04_AWVALID (AXI_04_AWVALID_in),
  .AXI_04_BREADY (AXI_04_BREADY_in),
  .AXI_04_DFI_LP_PWR_X_REQ (AXI_04_DFI_LP_PWR_X_REQ_in),
  .AXI_04_RREADY (AXI_04_RREADY_in),
  .AXI_04_WDATA (AXI_04_WDATA_in),
  .AXI_04_WDATA_PARITY (AXI_04_WDATA_PARITY_in),
  .AXI_04_WLAST (AXI_04_WLAST_in),
  .AXI_04_WSTRB (AXI_04_WSTRB_in),
  .AXI_04_WVALID (AXI_04_WVALID_in),
  .AXI_05_ACLK (AXI_05_ACLK_in),
  .AXI_05_ARADDR (AXI_05_ARADDR_in),
  .AXI_05_ARBURST (AXI_05_ARBURST_in),
  .AXI_05_ARESET_N (AXI_05_ARESET_N_in),
  .AXI_05_ARID (AXI_05_ARID_in),
  .AXI_05_ARLEN (AXI_05_ARLEN_in),
  .AXI_05_ARSIZE (AXI_05_ARSIZE_in),
  .AXI_05_ARVALID (AXI_05_ARVALID_in),
  .AXI_05_AWADDR (AXI_05_AWADDR_in),
  .AXI_05_AWBURST (AXI_05_AWBURST_in),
  .AXI_05_AWID (AXI_05_AWID_in),
  .AXI_05_AWLEN (AXI_05_AWLEN_in),
  .AXI_05_AWSIZE (AXI_05_AWSIZE_in),
  .AXI_05_AWVALID (AXI_05_AWVALID_in),
  .AXI_05_BREADY (AXI_05_BREADY_in),
  .AXI_05_DFI_LP_PWR_X_REQ (AXI_05_DFI_LP_PWR_X_REQ_in),
  .AXI_05_RREADY (AXI_05_RREADY_in),
  .AXI_05_WDATA (AXI_05_WDATA_in),
  .AXI_05_WDATA_PARITY (AXI_05_WDATA_PARITY_in),
  .AXI_05_WLAST (AXI_05_WLAST_in),
  .AXI_05_WSTRB (AXI_05_WSTRB_in),
  .AXI_05_WVALID (AXI_05_WVALID_in),
  .AXI_06_ACLK (AXI_06_ACLK_in),
  .AXI_06_ARADDR (AXI_06_ARADDR_in),
  .AXI_06_ARBURST (AXI_06_ARBURST_in),
  .AXI_06_ARESET_N (AXI_06_ARESET_N_in),
  .AXI_06_ARID (AXI_06_ARID_in),
  .AXI_06_ARLEN (AXI_06_ARLEN_in),
  .AXI_06_ARSIZE (AXI_06_ARSIZE_in),
  .AXI_06_ARVALID (AXI_06_ARVALID_in),
  .AXI_06_AWADDR (AXI_06_AWADDR_in),
  .AXI_06_AWBURST (AXI_06_AWBURST_in),
  .AXI_06_AWID (AXI_06_AWID_in),
  .AXI_06_AWLEN (AXI_06_AWLEN_in),
  .AXI_06_AWSIZE (AXI_06_AWSIZE_in),
  .AXI_06_AWVALID (AXI_06_AWVALID_in),
  .AXI_06_BREADY (AXI_06_BREADY_in),
  .AXI_06_DFI_LP_PWR_X_REQ (AXI_06_DFI_LP_PWR_X_REQ_in),
  .AXI_06_RREADY (AXI_06_RREADY_in),
  .AXI_06_WDATA (AXI_06_WDATA_in),
  .AXI_06_WDATA_PARITY (AXI_06_WDATA_PARITY_in),
  .AXI_06_WLAST (AXI_06_WLAST_in),
  .AXI_06_WSTRB (AXI_06_WSTRB_in),
  .AXI_06_WVALID (AXI_06_WVALID_in),
  .AXI_07_ACLK (AXI_07_ACLK_in),
  .AXI_07_ARADDR (AXI_07_ARADDR_in),
  .AXI_07_ARBURST (AXI_07_ARBURST_in),
  .AXI_07_ARESET_N (AXI_07_ARESET_N_in),
  .AXI_07_ARID (AXI_07_ARID_in),
  .AXI_07_ARLEN (AXI_07_ARLEN_in),
  .AXI_07_ARSIZE (AXI_07_ARSIZE_in),
  .AXI_07_ARVALID (AXI_07_ARVALID_in),
  .AXI_07_AWADDR (AXI_07_AWADDR_in),
  .AXI_07_AWBURST (AXI_07_AWBURST_in),
  .AXI_07_AWID (AXI_07_AWID_in),
  .AXI_07_AWLEN (AXI_07_AWLEN_in),
  .AXI_07_AWSIZE (AXI_07_AWSIZE_in),
  .AXI_07_AWVALID (AXI_07_AWVALID_in),
  .AXI_07_BREADY (AXI_07_BREADY_in),
  .AXI_07_DFI_LP_PWR_X_REQ (AXI_07_DFI_LP_PWR_X_REQ_in),
  .AXI_07_RREADY (AXI_07_RREADY_in),
  .AXI_07_WDATA (AXI_07_WDATA_in),
  .AXI_07_WDATA_PARITY (AXI_07_WDATA_PARITY_in),
  .AXI_07_WLAST (AXI_07_WLAST_in),
  .AXI_07_WSTRB (AXI_07_WSTRB_in),
  .AXI_07_WVALID (AXI_07_WVALID_in),
  .AXI_08_ACLK (AXI_08_ACLK_in),
  .AXI_08_ARADDR (AXI_08_ARADDR_in),
  .AXI_08_ARBURST (AXI_08_ARBURST_in),
  .AXI_08_ARESET_N (AXI_08_ARESET_N_in),
  .AXI_08_ARID (AXI_08_ARID_in),
  .AXI_08_ARLEN (AXI_08_ARLEN_in),
  .AXI_08_ARSIZE (AXI_08_ARSIZE_in),
  .AXI_08_ARVALID (AXI_08_ARVALID_in),
  .AXI_08_AWADDR (AXI_08_AWADDR_in),
  .AXI_08_AWBURST (AXI_08_AWBURST_in),
  .AXI_08_AWID (AXI_08_AWID_in),
  .AXI_08_AWLEN (AXI_08_AWLEN_in),
  .AXI_08_AWSIZE (AXI_08_AWSIZE_in),
  .AXI_08_AWVALID (AXI_08_AWVALID_in),
  .AXI_08_BREADY (AXI_08_BREADY_in),
  .AXI_08_DFI_LP_PWR_X_REQ (AXI_08_DFI_LP_PWR_X_REQ_in),
  .AXI_08_RREADY (AXI_08_RREADY_in),
  .AXI_08_WDATA (AXI_08_WDATA_in),
  .AXI_08_WDATA_PARITY (AXI_08_WDATA_PARITY_in),
  .AXI_08_WLAST (AXI_08_WLAST_in),
  .AXI_08_WSTRB (AXI_08_WSTRB_in),
  .AXI_08_WVALID (AXI_08_WVALID_in),
  .AXI_09_ACLK (AXI_09_ACLK_in),
  .AXI_09_ARADDR (AXI_09_ARADDR_in),
  .AXI_09_ARBURST (AXI_09_ARBURST_in),
  .AXI_09_ARESET_N (AXI_09_ARESET_N_in),
  .AXI_09_ARID (AXI_09_ARID_in),
  .AXI_09_ARLEN (AXI_09_ARLEN_in),
  .AXI_09_ARSIZE (AXI_09_ARSIZE_in),
  .AXI_09_ARVALID (AXI_09_ARVALID_in),
  .AXI_09_AWADDR (AXI_09_AWADDR_in),
  .AXI_09_AWBURST (AXI_09_AWBURST_in),
  .AXI_09_AWID (AXI_09_AWID_in),
  .AXI_09_AWLEN (AXI_09_AWLEN_in),
  .AXI_09_AWSIZE (AXI_09_AWSIZE_in),
  .AXI_09_AWVALID (AXI_09_AWVALID_in),
  .AXI_09_BREADY (AXI_09_BREADY_in),
  .AXI_09_DFI_LP_PWR_X_REQ (AXI_09_DFI_LP_PWR_X_REQ_in),
  .AXI_09_RREADY (AXI_09_RREADY_in),
  .AXI_09_WDATA (AXI_09_WDATA_in),
  .AXI_09_WDATA_PARITY (AXI_09_WDATA_PARITY_in),
  .AXI_09_WLAST (AXI_09_WLAST_in),
  .AXI_09_WSTRB (AXI_09_WSTRB_in),
  .AXI_09_WVALID (AXI_09_WVALID_in),
  .AXI_10_ACLK (AXI_10_ACLK_in),
  .AXI_10_ARADDR (AXI_10_ARADDR_in),
  .AXI_10_ARBURST (AXI_10_ARBURST_in),
  .AXI_10_ARESET_N (AXI_10_ARESET_N_in),
  .AXI_10_ARID (AXI_10_ARID_in),
  .AXI_10_ARLEN (AXI_10_ARLEN_in),
  .AXI_10_ARSIZE (AXI_10_ARSIZE_in),
  .AXI_10_ARVALID (AXI_10_ARVALID_in),
  .AXI_10_AWADDR (AXI_10_AWADDR_in),
  .AXI_10_AWBURST (AXI_10_AWBURST_in),
  .AXI_10_AWID (AXI_10_AWID_in),
  .AXI_10_AWLEN (AXI_10_AWLEN_in),
  .AXI_10_AWSIZE (AXI_10_AWSIZE_in),
  .AXI_10_AWVALID (AXI_10_AWVALID_in),
  .AXI_10_BREADY (AXI_10_BREADY_in),
  .AXI_10_DFI_LP_PWR_X_REQ (AXI_10_DFI_LP_PWR_X_REQ_in),
  .AXI_10_RREADY (AXI_10_RREADY_in),
  .AXI_10_WDATA (AXI_10_WDATA_in),
  .AXI_10_WDATA_PARITY (AXI_10_WDATA_PARITY_in),
  .AXI_10_WLAST (AXI_10_WLAST_in),
  .AXI_10_WSTRB (AXI_10_WSTRB_in),
  .AXI_10_WVALID (AXI_10_WVALID_in),
  .AXI_11_ACLK (AXI_11_ACLK_in),
  .AXI_11_ARADDR (AXI_11_ARADDR_in),
  .AXI_11_ARBURST (AXI_11_ARBURST_in),
  .AXI_11_ARESET_N (AXI_11_ARESET_N_in),
  .AXI_11_ARID (AXI_11_ARID_in),
  .AXI_11_ARLEN (AXI_11_ARLEN_in),
  .AXI_11_ARSIZE (AXI_11_ARSIZE_in),
  .AXI_11_ARVALID (AXI_11_ARVALID_in),
  .AXI_11_AWADDR (AXI_11_AWADDR_in),
  .AXI_11_AWBURST (AXI_11_AWBURST_in),
  .AXI_11_AWID (AXI_11_AWID_in),
  .AXI_11_AWLEN (AXI_11_AWLEN_in),
  .AXI_11_AWSIZE (AXI_11_AWSIZE_in),
  .AXI_11_AWVALID (AXI_11_AWVALID_in),
  .AXI_11_BREADY (AXI_11_BREADY_in),
  .AXI_11_DFI_LP_PWR_X_REQ (AXI_11_DFI_LP_PWR_X_REQ_in),
  .AXI_11_RREADY (AXI_11_RREADY_in),
  .AXI_11_WDATA (AXI_11_WDATA_in),
  .AXI_11_WDATA_PARITY (AXI_11_WDATA_PARITY_in),
  .AXI_11_WLAST (AXI_11_WLAST_in),
  .AXI_11_WSTRB (AXI_11_WSTRB_in),
  .AXI_11_WVALID (AXI_11_WVALID_in),
  .AXI_12_ACLK (AXI_12_ACLK_in),
  .AXI_12_ARADDR (AXI_12_ARADDR_in),
  .AXI_12_ARBURST (AXI_12_ARBURST_in),
  .AXI_12_ARESET_N (AXI_12_ARESET_N_in),
  .AXI_12_ARID (AXI_12_ARID_in),
  .AXI_12_ARLEN (AXI_12_ARLEN_in),
  .AXI_12_ARSIZE (AXI_12_ARSIZE_in),
  .AXI_12_ARVALID (AXI_12_ARVALID_in),
  .AXI_12_AWADDR (AXI_12_AWADDR_in),
  .AXI_12_AWBURST (AXI_12_AWBURST_in),
  .AXI_12_AWID (AXI_12_AWID_in),
  .AXI_12_AWLEN (AXI_12_AWLEN_in),
  .AXI_12_AWSIZE (AXI_12_AWSIZE_in),
  .AXI_12_AWVALID (AXI_12_AWVALID_in),
  .AXI_12_BREADY (AXI_12_BREADY_in),
  .AXI_12_DFI_LP_PWR_X_REQ (AXI_12_DFI_LP_PWR_X_REQ_in),
  .AXI_12_RREADY (AXI_12_RREADY_in),
  .AXI_12_WDATA (AXI_12_WDATA_in),
  .AXI_12_WDATA_PARITY (AXI_12_WDATA_PARITY_in),
  .AXI_12_WLAST (AXI_12_WLAST_in),
  .AXI_12_WSTRB (AXI_12_WSTRB_in),
  .AXI_12_WVALID (AXI_12_WVALID_in),
  .AXI_13_ACLK (AXI_13_ACLK_in),
  .AXI_13_ARADDR (AXI_13_ARADDR_in),
  .AXI_13_ARBURST (AXI_13_ARBURST_in),
  .AXI_13_ARESET_N (AXI_13_ARESET_N_in),
  .AXI_13_ARID (AXI_13_ARID_in),
  .AXI_13_ARLEN (AXI_13_ARLEN_in),
  .AXI_13_ARSIZE (AXI_13_ARSIZE_in),
  .AXI_13_ARVALID (AXI_13_ARVALID_in),
  .AXI_13_AWADDR (AXI_13_AWADDR_in),
  .AXI_13_AWBURST (AXI_13_AWBURST_in),
  .AXI_13_AWID (AXI_13_AWID_in),
  .AXI_13_AWLEN (AXI_13_AWLEN_in),
  .AXI_13_AWSIZE (AXI_13_AWSIZE_in),
  .AXI_13_AWVALID (AXI_13_AWVALID_in),
  .AXI_13_BREADY (AXI_13_BREADY_in),
  .AXI_13_DFI_LP_PWR_X_REQ (AXI_13_DFI_LP_PWR_X_REQ_in),
  .AXI_13_RREADY (AXI_13_RREADY_in),
  .AXI_13_WDATA (AXI_13_WDATA_in),
  .AXI_13_WDATA_PARITY (AXI_13_WDATA_PARITY_in),
  .AXI_13_WLAST (AXI_13_WLAST_in),
  .AXI_13_WSTRB (AXI_13_WSTRB_in),
  .AXI_13_WVALID (AXI_13_WVALID_in),
  .AXI_14_ACLK (AXI_14_ACLK_in),
  .AXI_14_ARADDR (AXI_14_ARADDR_in),
  .AXI_14_ARBURST (AXI_14_ARBURST_in),
  .AXI_14_ARESET_N (AXI_14_ARESET_N_in),
  .AXI_14_ARID (AXI_14_ARID_in),
  .AXI_14_ARLEN (AXI_14_ARLEN_in),
  .AXI_14_ARSIZE (AXI_14_ARSIZE_in),
  .AXI_14_ARVALID (AXI_14_ARVALID_in),
  .AXI_14_AWADDR (AXI_14_AWADDR_in),
  .AXI_14_AWBURST (AXI_14_AWBURST_in),
  .AXI_14_AWID (AXI_14_AWID_in),
  .AXI_14_AWLEN (AXI_14_AWLEN_in),
  .AXI_14_AWSIZE (AXI_14_AWSIZE_in),
  .AXI_14_AWVALID (AXI_14_AWVALID_in),
  .AXI_14_BREADY (AXI_14_BREADY_in),
  .AXI_14_DFI_LP_PWR_X_REQ (AXI_14_DFI_LP_PWR_X_REQ_in),
  .AXI_14_RREADY (AXI_14_RREADY_in),
  .AXI_14_WDATA (AXI_14_WDATA_in),
  .AXI_14_WDATA_PARITY (AXI_14_WDATA_PARITY_in),
  .AXI_14_WLAST (AXI_14_WLAST_in),
  .AXI_14_WSTRB (AXI_14_WSTRB_in),
  .AXI_14_WVALID (AXI_14_WVALID_in),
  .AXI_15_ACLK (AXI_15_ACLK_in),
  .AXI_15_ARADDR (AXI_15_ARADDR_in),
  .AXI_15_ARBURST (AXI_15_ARBURST_in),
  .AXI_15_ARESET_N (AXI_15_ARESET_N_in),
  .AXI_15_ARID (AXI_15_ARID_in),
  .AXI_15_ARLEN (AXI_15_ARLEN_in),
  .AXI_15_ARSIZE (AXI_15_ARSIZE_in),
  .AXI_15_ARVALID (AXI_15_ARVALID_in),
  .AXI_15_AWADDR (AXI_15_AWADDR_in),
  .AXI_15_AWBURST (AXI_15_AWBURST_in),
  .AXI_15_AWID (AXI_15_AWID_in),
  .AXI_15_AWLEN (AXI_15_AWLEN_in),
  .AXI_15_AWSIZE (AXI_15_AWSIZE_in),
  .AXI_15_AWVALID (AXI_15_AWVALID_in),
  .AXI_15_BREADY (AXI_15_BREADY_in),
  .AXI_15_DFI_LP_PWR_X_REQ (AXI_15_DFI_LP_PWR_X_REQ_in),
  .AXI_15_RREADY (AXI_15_RREADY_in),
  .AXI_15_WDATA (AXI_15_WDATA_in),
  .AXI_15_WDATA_PARITY (AXI_15_WDATA_PARITY_in),
  .AXI_15_WLAST (AXI_15_WLAST_in),
  .AXI_15_WSTRB (AXI_15_WSTRB_in),
  .AXI_15_WVALID (AXI_15_WVALID_in),
  .AXI_16_ACLK (AXI_16_ACLK_in),
  .AXI_16_ARADDR (AXI_16_ARADDR_in),
  .AXI_16_ARBURST (AXI_16_ARBURST_in),
  .AXI_16_ARESET_N (AXI_16_ARESET_N_in),
  .AXI_16_ARID (AXI_16_ARID_in),
  .AXI_16_ARLEN (AXI_16_ARLEN_in),
  .AXI_16_ARSIZE (AXI_16_ARSIZE_in),
  .AXI_16_ARVALID (AXI_16_ARVALID_in),
  .AXI_16_AWADDR (AXI_16_AWADDR_in),
  .AXI_16_AWBURST (AXI_16_AWBURST_in),
  .AXI_16_AWID (AXI_16_AWID_in),
  .AXI_16_AWLEN (AXI_16_AWLEN_in),
  .AXI_16_AWSIZE (AXI_16_AWSIZE_in),
  .AXI_16_AWVALID (AXI_16_AWVALID_in),
  .AXI_16_BREADY (AXI_16_BREADY_in),
  .AXI_16_DFI_LP_PWR_X_REQ (AXI_16_DFI_LP_PWR_X_REQ_in),
  .AXI_16_RREADY (AXI_16_RREADY_in),
  .AXI_16_WDATA (AXI_16_WDATA_in),
  .AXI_16_WDATA_PARITY (AXI_16_WDATA_PARITY_in),
  .AXI_16_WLAST (AXI_16_WLAST_in),
  .AXI_16_WSTRB (AXI_16_WSTRB_in),
  .AXI_16_WVALID (AXI_16_WVALID_in),
  .AXI_17_ACLK (AXI_17_ACLK_in),
  .AXI_17_ARADDR (AXI_17_ARADDR_in),
  .AXI_17_ARBURST (AXI_17_ARBURST_in),
  .AXI_17_ARESET_N (AXI_17_ARESET_N_in),
  .AXI_17_ARID (AXI_17_ARID_in),
  .AXI_17_ARLEN (AXI_17_ARLEN_in),
  .AXI_17_ARSIZE (AXI_17_ARSIZE_in),
  .AXI_17_ARVALID (AXI_17_ARVALID_in),
  .AXI_17_AWADDR (AXI_17_AWADDR_in),
  .AXI_17_AWBURST (AXI_17_AWBURST_in),
  .AXI_17_AWID (AXI_17_AWID_in),
  .AXI_17_AWLEN (AXI_17_AWLEN_in),
  .AXI_17_AWSIZE (AXI_17_AWSIZE_in),
  .AXI_17_AWVALID (AXI_17_AWVALID_in),
  .AXI_17_BREADY (AXI_17_BREADY_in),
  .AXI_17_DFI_LP_PWR_X_REQ (AXI_17_DFI_LP_PWR_X_REQ_in),
  .AXI_17_RREADY (AXI_17_RREADY_in),
  .AXI_17_WDATA (AXI_17_WDATA_in),
  .AXI_17_WDATA_PARITY (AXI_17_WDATA_PARITY_in),
  .AXI_17_WLAST (AXI_17_WLAST_in),
  .AXI_17_WSTRB (AXI_17_WSTRB_in),
  .AXI_17_WVALID (AXI_17_WVALID_in),
  .AXI_18_ACLK (AXI_18_ACLK_in),
  .AXI_18_ARADDR (AXI_18_ARADDR_in),
  .AXI_18_ARBURST (AXI_18_ARBURST_in),
  .AXI_18_ARESET_N (AXI_18_ARESET_N_in),
  .AXI_18_ARID (AXI_18_ARID_in),
  .AXI_18_ARLEN (AXI_18_ARLEN_in),
  .AXI_18_ARSIZE (AXI_18_ARSIZE_in),
  .AXI_18_ARVALID (AXI_18_ARVALID_in),
  .AXI_18_AWADDR (AXI_18_AWADDR_in),
  .AXI_18_AWBURST (AXI_18_AWBURST_in),
  .AXI_18_AWID (AXI_18_AWID_in),
  .AXI_18_AWLEN (AXI_18_AWLEN_in),
  .AXI_18_AWSIZE (AXI_18_AWSIZE_in),
  .AXI_18_AWVALID (AXI_18_AWVALID_in),
  .AXI_18_BREADY (AXI_18_BREADY_in),
  .AXI_18_DFI_LP_PWR_X_REQ (AXI_18_DFI_LP_PWR_X_REQ_in),
  .AXI_18_RREADY (AXI_18_RREADY_in),
  .AXI_18_WDATA (AXI_18_WDATA_in),
  .AXI_18_WDATA_PARITY (AXI_18_WDATA_PARITY_in),
  .AXI_18_WLAST (AXI_18_WLAST_in),
  .AXI_18_WSTRB (AXI_18_WSTRB_in),
  .AXI_18_WVALID (AXI_18_WVALID_in),
  .AXI_19_ACLK (AXI_19_ACLK_in),
  .AXI_19_ARADDR (AXI_19_ARADDR_in),
  .AXI_19_ARBURST (AXI_19_ARBURST_in),
  .AXI_19_ARESET_N (AXI_19_ARESET_N_in),
  .AXI_19_ARID (AXI_19_ARID_in),
  .AXI_19_ARLEN (AXI_19_ARLEN_in),
  .AXI_19_ARSIZE (AXI_19_ARSIZE_in),
  .AXI_19_ARVALID (AXI_19_ARVALID_in),
  .AXI_19_AWADDR (AXI_19_AWADDR_in),
  .AXI_19_AWBURST (AXI_19_AWBURST_in),
  .AXI_19_AWID (AXI_19_AWID_in),
  .AXI_19_AWLEN (AXI_19_AWLEN_in),
  .AXI_19_AWSIZE (AXI_19_AWSIZE_in),
  .AXI_19_AWVALID (AXI_19_AWVALID_in),
  .AXI_19_BREADY (AXI_19_BREADY_in),
  .AXI_19_DFI_LP_PWR_X_REQ (AXI_19_DFI_LP_PWR_X_REQ_in),
  .AXI_19_RREADY (AXI_19_RREADY_in),
  .AXI_19_WDATA (AXI_19_WDATA_in),
  .AXI_19_WDATA_PARITY (AXI_19_WDATA_PARITY_in),
  .AXI_19_WLAST (AXI_19_WLAST_in),
  .AXI_19_WSTRB (AXI_19_WSTRB_in),
  .AXI_19_WVALID (AXI_19_WVALID_in),
  .AXI_20_ACLK (AXI_20_ACLK_in),
  .AXI_20_ARADDR (AXI_20_ARADDR_in),
  .AXI_20_ARBURST (AXI_20_ARBURST_in),
  .AXI_20_ARESET_N (AXI_20_ARESET_N_in),
  .AXI_20_ARID (AXI_20_ARID_in),
  .AXI_20_ARLEN (AXI_20_ARLEN_in),
  .AXI_20_ARSIZE (AXI_20_ARSIZE_in),
  .AXI_20_ARVALID (AXI_20_ARVALID_in),
  .AXI_20_AWADDR (AXI_20_AWADDR_in),
  .AXI_20_AWBURST (AXI_20_AWBURST_in),
  .AXI_20_AWID (AXI_20_AWID_in),
  .AXI_20_AWLEN (AXI_20_AWLEN_in),
  .AXI_20_AWSIZE (AXI_20_AWSIZE_in),
  .AXI_20_AWVALID (AXI_20_AWVALID_in),
  .AXI_20_BREADY (AXI_20_BREADY_in),
  .AXI_20_DFI_LP_PWR_X_REQ (AXI_20_DFI_LP_PWR_X_REQ_in),
  .AXI_20_RREADY (AXI_20_RREADY_in),
  .AXI_20_WDATA (AXI_20_WDATA_in),
  .AXI_20_WDATA_PARITY (AXI_20_WDATA_PARITY_in),
  .AXI_20_WLAST (AXI_20_WLAST_in),
  .AXI_20_WSTRB (AXI_20_WSTRB_in),
  .AXI_20_WVALID (AXI_20_WVALID_in),
  .AXI_21_ACLK (AXI_21_ACLK_in),
  .AXI_21_ARADDR (AXI_21_ARADDR_in),
  .AXI_21_ARBURST (AXI_21_ARBURST_in),
  .AXI_21_ARESET_N (AXI_21_ARESET_N_in),
  .AXI_21_ARID (AXI_21_ARID_in),
  .AXI_21_ARLEN (AXI_21_ARLEN_in),
  .AXI_21_ARSIZE (AXI_21_ARSIZE_in),
  .AXI_21_ARVALID (AXI_21_ARVALID_in),
  .AXI_21_AWADDR (AXI_21_AWADDR_in),
  .AXI_21_AWBURST (AXI_21_AWBURST_in),
  .AXI_21_AWID (AXI_21_AWID_in),
  .AXI_21_AWLEN (AXI_21_AWLEN_in),
  .AXI_21_AWSIZE (AXI_21_AWSIZE_in),
  .AXI_21_AWVALID (AXI_21_AWVALID_in),
  .AXI_21_BREADY (AXI_21_BREADY_in),
  .AXI_21_DFI_LP_PWR_X_REQ (AXI_21_DFI_LP_PWR_X_REQ_in),
  .AXI_21_RREADY (AXI_21_RREADY_in),
  .AXI_21_WDATA (AXI_21_WDATA_in),
  .AXI_21_WDATA_PARITY (AXI_21_WDATA_PARITY_in),
  .AXI_21_WLAST (AXI_21_WLAST_in),
  .AXI_21_WSTRB (AXI_21_WSTRB_in),
  .AXI_21_WVALID (AXI_21_WVALID_in),
  .AXI_22_ACLK (AXI_22_ACLK_in),
  .AXI_22_ARADDR (AXI_22_ARADDR_in),
  .AXI_22_ARBURST (AXI_22_ARBURST_in),
  .AXI_22_ARESET_N (AXI_22_ARESET_N_in),
  .AXI_22_ARID (AXI_22_ARID_in),
  .AXI_22_ARLEN (AXI_22_ARLEN_in),
  .AXI_22_ARSIZE (AXI_22_ARSIZE_in),
  .AXI_22_ARVALID (AXI_22_ARVALID_in),
  .AXI_22_AWADDR (AXI_22_AWADDR_in),
  .AXI_22_AWBURST (AXI_22_AWBURST_in),
  .AXI_22_AWID (AXI_22_AWID_in),
  .AXI_22_AWLEN (AXI_22_AWLEN_in),
  .AXI_22_AWSIZE (AXI_22_AWSIZE_in),
  .AXI_22_AWVALID (AXI_22_AWVALID_in),
  .AXI_22_BREADY (AXI_22_BREADY_in),
  .AXI_22_DFI_LP_PWR_X_REQ (AXI_22_DFI_LP_PWR_X_REQ_in),
  .AXI_22_RREADY (AXI_22_RREADY_in),
  .AXI_22_WDATA (AXI_22_WDATA_in),
  .AXI_22_WDATA_PARITY (AXI_22_WDATA_PARITY_in),
  .AXI_22_WLAST (AXI_22_WLAST_in),
  .AXI_22_WSTRB (AXI_22_WSTRB_in),
  .AXI_22_WVALID (AXI_22_WVALID_in),
  .AXI_23_ACLK (AXI_23_ACLK_in),
  .AXI_23_ARADDR (AXI_23_ARADDR_in),
  .AXI_23_ARBURST (AXI_23_ARBURST_in),
  .AXI_23_ARESET_N (AXI_23_ARESET_N_in),
  .AXI_23_ARID (AXI_23_ARID_in),
  .AXI_23_ARLEN (AXI_23_ARLEN_in),
  .AXI_23_ARSIZE (AXI_23_ARSIZE_in),
  .AXI_23_ARVALID (AXI_23_ARVALID_in),
  .AXI_23_AWADDR (AXI_23_AWADDR_in),
  .AXI_23_AWBURST (AXI_23_AWBURST_in),
  .AXI_23_AWID (AXI_23_AWID_in),
  .AXI_23_AWLEN (AXI_23_AWLEN_in),
  .AXI_23_AWSIZE (AXI_23_AWSIZE_in),
  .AXI_23_AWVALID (AXI_23_AWVALID_in),
  .AXI_23_BREADY (AXI_23_BREADY_in),
  .AXI_23_DFI_LP_PWR_X_REQ (AXI_23_DFI_LP_PWR_X_REQ_in),
  .AXI_23_RREADY (AXI_23_RREADY_in),
  .AXI_23_WDATA (AXI_23_WDATA_in),
  .AXI_23_WDATA_PARITY (AXI_23_WDATA_PARITY_in),
  .AXI_23_WLAST (AXI_23_WLAST_in),
  .AXI_23_WSTRB (AXI_23_WSTRB_in),
  .AXI_23_WVALID (AXI_23_WVALID_in),
  .AXI_24_ACLK (AXI_24_ACLK_in),
  .AXI_24_ARADDR (AXI_24_ARADDR_in),
  .AXI_24_ARBURST (AXI_24_ARBURST_in),
  .AXI_24_ARESET_N (AXI_24_ARESET_N_in),
  .AXI_24_ARID (AXI_24_ARID_in),
  .AXI_24_ARLEN (AXI_24_ARLEN_in),
  .AXI_24_ARSIZE (AXI_24_ARSIZE_in),
  .AXI_24_ARVALID (AXI_24_ARVALID_in),
  .AXI_24_AWADDR (AXI_24_AWADDR_in),
  .AXI_24_AWBURST (AXI_24_AWBURST_in),
  .AXI_24_AWID (AXI_24_AWID_in),
  .AXI_24_AWLEN (AXI_24_AWLEN_in),
  .AXI_24_AWSIZE (AXI_24_AWSIZE_in),
  .AXI_24_AWVALID (AXI_24_AWVALID_in),
  .AXI_24_BREADY (AXI_24_BREADY_in),
  .AXI_24_DFI_LP_PWR_X_REQ (AXI_24_DFI_LP_PWR_X_REQ_in),
  .AXI_24_RREADY (AXI_24_RREADY_in),
  .AXI_24_WDATA (AXI_24_WDATA_in),
  .AXI_24_WDATA_PARITY (AXI_24_WDATA_PARITY_in),
  .AXI_24_WLAST (AXI_24_WLAST_in),
  .AXI_24_WSTRB (AXI_24_WSTRB_in),
  .AXI_24_WVALID (AXI_24_WVALID_in),
  .AXI_25_ACLK (AXI_25_ACLK_in),
  .AXI_25_ARADDR (AXI_25_ARADDR_in),
  .AXI_25_ARBURST (AXI_25_ARBURST_in),
  .AXI_25_ARESET_N (AXI_25_ARESET_N_in),
  .AXI_25_ARID (AXI_25_ARID_in),
  .AXI_25_ARLEN (AXI_25_ARLEN_in),
  .AXI_25_ARSIZE (AXI_25_ARSIZE_in),
  .AXI_25_ARVALID (AXI_25_ARVALID_in),
  .AXI_25_AWADDR (AXI_25_AWADDR_in),
  .AXI_25_AWBURST (AXI_25_AWBURST_in),
  .AXI_25_AWID (AXI_25_AWID_in),
  .AXI_25_AWLEN (AXI_25_AWLEN_in),
  .AXI_25_AWSIZE (AXI_25_AWSIZE_in),
  .AXI_25_AWVALID (AXI_25_AWVALID_in),
  .AXI_25_BREADY (AXI_25_BREADY_in),
  .AXI_25_DFI_LP_PWR_X_REQ (AXI_25_DFI_LP_PWR_X_REQ_in),
  .AXI_25_RREADY (AXI_25_RREADY_in),
  .AXI_25_WDATA (AXI_25_WDATA_in),
  .AXI_25_WDATA_PARITY (AXI_25_WDATA_PARITY_in),
  .AXI_25_WLAST (AXI_25_WLAST_in),
  .AXI_25_WSTRB (AXI_25_WSTRB_in),
  .AXI_25_WVALID (AXI_25_WVALID_in),
  .AXI_26_ACLK (AXI_26_ACLK_in),
  .AXI_26_ARADDR (AXI_26_ARADDR_in),
  .AXI_26_ARBURST (AXI_26_ARBURST_in),
  .AXI_26_ARESET_N (AXI_26_ARESET_N_in),
  .AXI_26_ARID (AXI_26_ARID_in),
  .AXI_26_ARLEN (AXI_26_ARLEN_in),
  .AXI_26_ARSIZE (AXI_26_ARSIZE_in),
  .AXI_26_ARVALID (AXI_26_ARVALID_in),
  .AXI_26_AWADDR (AXI_26_AWADDR_in),
  .AXI_26_AWBURST (AXI_26_AWBURST_in),
  .AXI_26_AWID (AXI_26_AWID_in),
  .AXI_26_AWLEN (AXI_26_AWLEN_in),
  .AXI_26_AWSIZE (AXI_26_AWSIZE_in),
  .AXI_26_AWVALID (AXI_26_AWVALID_in),
  .AXI_26_BREADY (AXI_26_BREADY_in),
  .AXI_26_DFI_LP_PWR_X_REQ (AXI_26_DFI_LP_PWR_X_REQ_in),
  .AXI_26_RREADY (AXI_26_RREADY_in),
  .AXI_26_WDATA (AXI_26_WDATA_in),
  .AXI_26_WDATA_PARITY (AXI_26_WDATA_PARITY_in),
  .AXI_26_WLAST (AXI_26_WLAST_in),
  .AXI_26_WSTRB (AXI_26_WSTRB_in),
  .AXI_26_WVALID (AXI_26_WVALID_in),
  .AXI_27_ACLK (AXI_27_ACLK_in),
  .AXI_27_ARADDR (AXI_27_ARADDR_in),
  .AXI_27_ARBURST (AXI_27_ARBURST_in),
  .AXI_27_ARESET_N (AXI_27_ARESET_N_in),
  .AXI_27_ARID (AXI_27_ARID_in),
  .AXI_27_ARLEN (AXI_27_ARLEN_in),
  .AXI_27_ARSIZE (AXI_27_ARSIZE_in),
  .AXI_27_ARVALID (AXI_27_ARVALID_in),
  .AXI_27_AWADDR (AXI_27_AWADDR_in),
  .AXI_27_AWBURST (AXI_27_AWBURST_in),
  .AXI_27_AWID (AXI_27_AWID_in),
  .AXI_27_AWLEN (AXI_27_AWLEN_in),
  .AXI_27_AWSIZE (AXI_27_AWSIZE_in),
  .AXI_27_AWVALID (AXI_27_AWVALID_in),
  .AXI_27_BREADY (AXI_27_BREADY_in),
  .AXI_27_DFI_LP_PWR_X_REQ (AXI_27_DFI_LP_PWR_X_REQ_in),
  .AXI_27_RREADY (AXI_27_RREADY_in),
  .AXI_27_WDATA (AXI_27_WDATA_in),
  .AXI_27_WDATA_PARITY (AXI_27_WDATA_PARITY_in),
  .AXI_27_WLAST (AXI_27_WLAST_in),
  .AXI_27_WSTRB (AXI_27_WSTRB_in),
  .AXI_27_WVALID (AXI_27_WVALID_in),
  .AXI_28_ACLK (AXI_28_ACLK_in),
  .AXI_28_ARADDR (AXI_28_ARADDR_in),
  .AXI_28_ARBURST (AXI_28_ARBURST_in),
  .AXI_28_ARESET_N (AXI_28_ARESET_N_in),
  .AXI_28_ARID (AXI_28_ARID_in),
  .AXI_28_ARLEN (AXI_28_ARLEN_in),
  .AXI_28_ARSIZE (AXI_28_ARSIZE_in),
  .AXI_28_ARVALID (AXI_28_ARVALID_in),
  .AXI_28_AWADDR (AXI_28_AWADDR_in),
  .AXI_28_AWBURST (AXI_28_AWBURST_in),
  .AXI_28_AWID (AXI_28_AWID_in),
  .AXI_28_AWLEN (AXI_28_AWLEN_in),
  .AXI_28_AWSIZE (AXI_28_AWSIZE_in),
  .AXI_28_AWVALID (AXI_28_AWVALID_in),
  .AXI_28_BREADY (AXI_28_BREADY_in),
  .AXI_28_DFI_LP_PWR_X_REQ (AXI_28_DFI_LP_PWR_X_REQ_in),
  .AXI_28_RREADY (AXI_28_RREADY_in),
  .AXI_28_WDATA (AXI_28_WDATA_in),
  .AXI_28_WDATA_PARITY (AXI_28_WDATA_PARITY_in),
  .AXI_28_WLAST (AXI_28_WLAST_in),
  .AXI_28_WSTRB (AXI_28_WSTRB_in),
  .AXI_28_WVALID (AXI_28_WVALID_in),
  .AXI_29_ACLK (AXI_29_ACLK_in),
  .AXI_29_ARADDR (AXI_29_ARADDR_in),
  .AXI_29_ARBURST (AXI_29_ARBURST_in),
  .AXI_29_ARESET_N (AXI_29_ARESET_N_in),
  .AXI_29_ARID (AXI_29_ARID_in),
  .AXI_29_ARLEN (AXI_29_ARLEN_in),
  .AXI_29_ARSIZE (AXI_29_ARSIZE_in),
  .AXI_29_ARVALID (AXI_29_ARVALID_in),
  .AXI_29_AWADDR (AXI_29_AWADDR_in),
  .AXI_29_AWBURST (AXI_29_AWBURST_in),
  .AXI_29_AWID (AXI_29_AWID_in),
  .AXI_29_AWLEN (AXI_29_AWLEN_in),
  .AXI_29_AWSIZE (AXI_29_AWSIZE_in),
  .AXI_29_AWVALID (AXI_29_AWVALID_in),
  .AXI_29_BREADY (AXI_29_BREADY_in),
  .AXI_29_DFI_LP_PWR_X_REQ (AXI_29_DFI_LP_PWR_X_REQ_in),
  .AXI_29_RREADY (AXI_29_RREADY_in),
  .AXI_29_WDATA (AXI_29_WDATA_in),
  .AXI_29_WDATA_PARITY (AXI_29_WDATA_PARITY_in),
  .AXI_29_WLAST (AXI_29_WLAST_in),
  .AXI_29_WSTRB (AXI_29_WSTRB_in),
  .AXI_29_WVALID (AXI_29_WVALID_in),
  .AXI_30_ACLK (AXI_30_ACLK_in),
  .AXI_30_ARADDR (AXI_30_ARADDR_in),
  .AXI_30_ARBURST (AXI_30_ARBURST_in),
  .AXI_30_ARESET_N (AXI_30_ARESET_N_in),
  .AXI_30_ARID (AXI_30_ARID_in),
  .AXI_30_ARLEN (AXI_30_ARLEN_in),
  .AXI_30_ARSIZE (AXI_30_ARSIZE_in),
  .AXI_30_ARVALID (AXI_30_ARVALID_in),
  .AXI_30_AWADDR (AXI_30_AWADDR_in),
  .AXI_30_AWBURST (AXI_30_AWBURST_in),
  .AXI_30_AWID (AXI_30_AWID_in),
  .AXI_30_AWLEN (AXI_30_AWLEN_in),
  .AXI_30_AWSIZE (AXI_30_AWSIZE_in),
  .AXI_30_AWVALID (AXI_30_AWVALID_in),
  .AXI_30_BREADY (AXI_30_BREADY_in),
  .AXI_30_DFI_LP_PWR_X_REQ (AXI_30_DFI_LP_PWR_X_REQ_in),
  .AXI_30_RREADY (AXI_30_RREADY_in),
  .AXI_30_WDATA (AXI_30_WDATA_in),
  .AXI_30_WDATA_PARITY (AXI_30_WDATA_PARITY_in),
  .AXI_30_WLAST (AXI_30_WLAST_in),
  .AXI_30_WSTRB (AXI_30_WSTRB_in),
  .AXI_30_WVALID (AXI_30_WVALID_in),
  .AXI_31_ACLK (AXI_31_ACLK_in),
  .AXI_31_ARADDR (AXI_31_ARADDR_in),
  .AXI_31_ARBURST (AXI_31_ARBURST_in),
  .AXI_31_ARESET_N (AXI_31_ARESET_N_in),
  .AXI_31_ARID (AXI_31_ARID_in),
  .AXI_31_ARLEN (AXI_31_ARLEN_in),
  .AXI_31_ARSIZE (AXI_31_ARSIZE_in),
  .AXI_31_ARVALID (AXI_31_ARVALID_in),
  .AXI_31_AWADDR (AXI_31_AWADDR_in),
  .AXI_31_AWBURST (AXI_31_AWBURST_in),
  .AXI_31_AWID (AXI_31_AWID_in),
  .AXI_31_AWLEN (AXI_31_AWLEN_in),
  .AXI_31_AWSIZE (AXI_31_AWSIZE_in),
  .AXI_31_AWVALID (AXI_31_AWVALID_in),
  .AXI_31_BREADY (AXI_31_BREADY_in),
  .AXI_31_DFI_LP_PWR_X_REQ (AXI_31_DFI_LP_PWR_X_REQ_in),
  .AXI_31_RREADY (AXI_31_RREADY_in),
  .AXI_31_WDATA (AXI_31_WDATA_in),
  .AXI_31_WDATA_PARITY (AXI_31_WDATA_PARITY_in),
  .AXI_31_WLAST (AXI_31_WLAST_in),
  .AXI_31_WSTRB (AXI_31_WSTRB_in),
  .AXI_31_WVALID (AXI_31_WVALID_in),
  .BLI_SCAN_ENABLE_00 (BLI_SCAN_ENABLE_00_in),
  .BLI_SCAN_ENABLE_01 (BLI_SCAN_ENABLE_01_in),
  .BLI_SCAN_ENABLE_02 (BLI_SCAN_ENABLE_02_in),
  .BLI_SCAN_ENABLE_03 (BLI_SCAN_ENABLE_03_in),
  .BLI_SCAN_ENABLE_04 (BLI_SCAN_ENABLE_04_in),
  .BLI_SCAN_ENABLE_05 (BLI_SCAN_ENABLE_05_in),
  .BLI_SCAN_ENABLE_06 (BLI_SCAN_ENABLE_06_in),
  .BLI_SCAN_ENABLE_07 (BLI_SCAN_ENABLE_07_in),
  .BLI_SCAN_ENABLE_08 (BLI_SCAN_ENABLE_08_in),
  .BLI_SCAN_ENABLE_09 (BLI_SCAN_ENABLE_09_in),
  .BLI_SCAN_ENABLE_10 (BLI_SCAN_ENABLE_10_in),
  .BLI_SCAN_ENABLE_11 (BLI_SCAN_ENABLE_11_in),
  .BLI_SCAN_ENABLE_12 (BLI_SCAN_ENABLE_12_in),
  .BLI_SCAN_ENABLE_13 (BLI_SCAN_ENABLE_13_in),
  .BLI_SCAN_ENABLE_14 (BLI_SCAN_ENABLE_14_in),
  .BLI_SCAN_ENABLE_15 (BLI_SCAN_ENABLE_15_in),
  .BLI_SCAN_ENABLE_16 (BLI_SCAN_ENABLE_16_in),
  .BLI_SCAN_ENABLE_17 (BLI_SCAN_ENABLE_17_in),
  .BLI_SCAN_ENABLE_18 (BLI_SCAN_ENABLE_18_in),
  .BLI_SCAN_ENABLE_19 (BLI_SCAN_ENABLE_19_in),
  .BLI_SCAN_ENABLE_20 (BLI_SCAN_ENABLE_20_in),
  .BLI_SCAN_ENABLE_21 (BLI_SCAN_ENABLE_21_in),
  .BLI_SCAN_ENABLE_22 (BLI_SCAN_ENABLE_22_in),
  .BLI_SCAN_ENABLE_23 (BLI_SCAN_ENABLE_23_in),
  .BLI_SCAN_ENABLE_24 (BLI_SCAN_ENABLE_24_in),
  .BLI_SCAN_ENABLE_25 (BLI_SCAN_ENABLE_25_in),
  .BLI_SCAN_ENABLE_26 (BLI_SCAN_ENABLE_26_in),
  .BLI_SCAN_ENABLE_27 (BLI_SCAN_ENABLE_27_in),
  .BLI_SCAN_ENABLE_28 (BLI_SCAN_ENABLE_28_in),
  .BLI_SCAN_ENABLE_29 (BLI_SCAN_ENABLE_29_in),
  .BLI_SCAN_ENABLE_30 (BLI_SCAN_ENABLE_30_in),
  .BLI_SCAN_ENABLE_31 (BLI_SCAN_ENABLE_31_in),
  .BLI_SCAN_IN_00 (BLI_SCAN_IN_00_in),
  .BLI_SCAN_IN_01 (BLI_SCAN_IN_01_in),
  .BLI_SCAN_IN_02 (BLI_SCAN_IN_02_in),
  .BLI_SCAN_IN_03 (BLI_SCAN_IN_03_in),
  .BLI_SCAN_IN_04 (BLI_SCAN_IN_04_in),
  .BLI_SCAN_IN_05 (BLI_SCAN_IN_05_in),
  .BLI_SCAN_IN_06 (BLI_SCAN_IN_06_in),
  .BLI_SCAN_IN_07 (BLI_SCAN_IN_07_in),
  .BLI_SCAN_IN_08 (BLI_SCAN_IN_08_in),
  .BLI_SCAN_IN_09 (BLI_SCAN_IN_09_in),
  .BLI_SCAN_IN_10 (BLI_SCAN_IN_10_in),
  .BLI_SCAN_IN_11 (BLI_SCAN_IN_11_in),
  .BLI_SCAN_IN_12 (BLI_SCAN_IN_12_in),
  .BLI_SCAN_IN_13 (BLI_SCAN_IN_13_in),
  .BLI_SCAN_IN_14 (BLI_SCAN_IN_14_in),
  .BLI_SCAN_IN_15 (BLI_SCAN_IN_15_in),
  .BLI_SCAN_IN_16 (BLI_SCAN_IN_16_in),
  .BLI_SCAN_IN_17 (BLI_SCAN_IN_17_in),
  .BLI_SCAN_IN_18 (BLI_SCAN_IN_18_in),
  .BLI_SCAN_IN_19 (BLI_SCAN_IN_19_in),
  .BLI_SCAN_IN_20 (BLI_SCAN_IN_20_in),
  .BLI_SCAN_IN_21 (BLI_SCAN_IN_21_in),
  .BLI_SCAN_IN_22 (BLI_SCAN_IN_22_in),
  .BLI_SCAN_IN_23 (BLI_SCAN_IN_23_in),
  .BLI_SCAN_IN_24 (BLI_SCAN_IN_24_in),
  .BLI_SCAN_IN_25 (BLI_SCAN_IN_25_in),
  .BLI_SCAN_IN_26 (BLI_SCAN_IN_26_in),
  .BLI_SCAN_IN_27 (BLI_SCAN_IN_27_in),
  .BLI_SCAN_IN_28 (BLI_SCAN_IN_28_in),
  .BLI_SCAN_IN_29 (BLI_SCAN_IN_29_in),
  .BLI_SCAN_IN_30 (BLI_SCAN_IN_30_in),
  .BLI_SCAN_IN_31 (BLI_SCAN_IN_31_in),
  .BSCAN_DRCK_0 (BSCAN_DRCK_0_in),
  .BSCAN_DRCK_1 (BSCAN_DRCK_1_in),
  .BSCAN_TCK_0 (BSCAN_TCK_0_in),
  .BSCAN_TCK_1 (BSCAN_TCK_1_in),
  .DBG_IN_00 (DBG_IN_00_in),
  .DBG_IN_01 (DBG_IN_01_in),
  .DBG_IN_02 (DBG_IN_02_in),
  .DBG_IN_03 (DBG_IN_03_in),
  .DBG_IN_04 (DBG_IN_04_in),
  .DBG_IN_05 (DBG_IN_05_in),
  .DBG_IN_06 (DBG_IN_06_in),
  .DBG_IN_07 (DBG_IN_07_in),
  .DBG_IN_08 (DBG_IN_08_in),
  .DBG_IN_09 (DBG_IN_09_in),
  .DBG_IN_10 (DBG_IN_10_in),
  .DBG_IN_11 (DBG_IN_11_in),
  .DBG_IN_12 (DBG_IN_12_in),
  .DBG_IN_13 (DBG_IN_13_in),
  .DBG_IN_14 (DBG_IN_14_in),
  .DBG_IN_15 (DBG_IN_15_in),
  .DBG_IN_16 (DBG_IN_16_in),
  .DBG_IN_17 (DBG_IN_17_in),
  .DBG_IN_18 (DBG_IN_18_in),
  .DBG_IN_19 (DBG_IN_19_in),
  .DBG_IN_20 (DBG_IN_20_in),
  .DBG_IN_21 (DBG_IN_21_in),
  .DBG_IN_22 (DBG_IN_22_in),
  .DBG_IN_23 (DBG_IN_23_in),
  .DBG_IN_24 (DBG_IN_24_in),
  .DBG_IN_25 (DBG_IN_25_in),
  .DBG_IN_26 (DBG_IN_26_in),
  .DBG_IN_27 (DBG_IN_27_in),
  .DBG_IN_28 (DBG_IN_28_in),
  .DBG_IN_29 (DBG_IN_29_in),
  .DBG_IN_30 (DBG_IN_30_in),
  .DBG_IN_31 (DBG_IN_31_in),
  .DLL_SCAN_CK_00 (DLL_SCAN_CK_00_in),
  .DLL_SCAN_CK_01 (DLL_SCAN_CK_01_in),
  .DLL_SCAN_ENABLE_00 (DLL_SCAN_ENABLE_00_in),
  .DLL_SCAN_ENABLE_01 (DLL_SCAN_ENABLE_01_in),
  .DLL_SCAN_IN_00 (DLL_SCAN_IN_00_in),
  .DLL_SCAN_IN_01 (DLL_SCAN_IN_01_in),
  .DLL_SCAN_MODE_00 (DLL_SCAN_MODE_00_in),
  .DLL_SCAN_MODE_01 (DLL_SCAN_MODE_01_in),
  .DLL_SCAN_RST_N_00 (DLL_SCAN_RST_N_00_in),
  .DLL_SCAN_RST_N_01 (DLL_SCAN_RST_N_01_in),
  .HBM_REF_CLK_0 (HBM_REF_CLK_0_in),
  .HBM_REF_CLK_1 (HBM_REF_CLK_1_in),
  .IO_SCAN_CK_00 (IO_SCAN_CK_00_in),
  .IO_SCAN_CK_01 (IO_SCAN_CK_01_in),
  .IO_SCAN_ENABLE_00 (IO_SCAN_ENABLE_00_in),
  .IO_SCAN_ENABLE_01 (IO_SCAN_ENABLE_01_in),
  .IO_SCAN_IN_00 (IO_SCAN_IN_00_in),
  .IO_SCAN_IN_01 (IO_SCAN_IN_01_in),
  .IO_SCAN_MODE_00 (IO_SCAN_MODE_00_in),
  .IO_SCAN_MODE_01 (IO_SCAN_MODE_01_in),
  .IO_SCAN_RST_N_00 (IO_SCAN_RST_N_00_in),
  .IO_SCAN_RST_N_01 (IO_SCAN_RST_N_01_in),
  .MBIST_EN_00 (MBIST_EN_00_in),
  .MBIST_EN_01 (MBIST_EN_01_in),
  .MBIST_EN_02 (MBIST_EN_02_in),
  .MBIST_EN_03 (MBIST_EN_03_in),
  .MBIST_EN_04 (MBIST_EN_04_in),
  .MBIST_EN_05 (MBIST_EN_05_in),
  .MBIST_EN_06 (MBIST_EN_06_in),
  .MBIST_EN_07 (MBIST_EN_07_in),
  .MBIST_EN_08 (MBIST_EN_08_in),
  .MBIST_EN_09 (MBIST_EN_09_in),
  .MBIST_EN_10 (MBIST_EN_10_in),
  .MBIST_EN_11 (MBIST_EN_11_in),
  .MBIST_EN_12 (MBIST_EN_12_in),
  .MBIST_EN_13 (MBIST_EN_13_in),
  .MBIST_EN_14 (MBIST_EN_14_in),
  .MBIST_EN_15 (MBIST_EN_15_in),
  .MC_SCAN_CK_00 (MC_SCAN_CK_00_in),
  .MC_SCAN_CK_01 (MC_SCAN_CK_01_in),
  .MC_SCAN_CK_02 (MC_SCAN_CK_02_in),
  .MC_SCAN_CK_03 (MC_SCAN_CK_03_in),
  .MC_SCAN_CK_04 (MC_SCAN_CK_04_in),
  .MC_SCAN_CK_05 (MC_SCAN_CK_05_in),
  .MC_SCAN_CK_06 (MC_SCAN_CK_06_in),
  .MC_SCAN_CK_07 (MC_SCAN_CK_07_in),
  .MC_SCAN_CK_08 (MC_SCAN_CK_08_in),
  .MC_SCAN_CK_09 (MC_SCAN_CK_09_in),
  .MC_SCAN_CK_10 (MC_SCAN_CK_10_in),
  .MC_SCAN_CK_11 (MC_SCAN_CK_11_in),
  .MC_SCAN_CK_12 (MC_SCAN_CK_12_in),
  .MC_SCAN_CK_13 (MC_SCAN_CK_13_in),
  .MC_SCAN_CK_14 (MC_SCAN_CK_14_in),
  .MC_SCAN_CK_15 (MC_SCAN_CK_15_in),
  .MC_SCAN_ENABLE_00 (MC_SCAN_ENABLE_00_in),
  .MC_SCAN_ENABLE_01 (MC_SCAN_ENABLE_01_in),
  .MC_SCAN_ENABLE_02 (MC_SCAN_ENABLE_02_in),
  .MC_SCAN_ENABLE_03 (MC_SCAN_ENABLE_03_in),
  .MC_SCAN_ENABLE_04 (MC_SCAN_ENABLE_04_in),
  .MC_SCAN_ENABLE_05 (MC_SCAN_ENABLE_05_in),
  .MC_SCAN_ENABLE_06 (MC_SCAN_ENABLE_06_in),
  .MC_SCAN_ENABLE_07 (MC_SCAN_ENABLE_07_in),
  .MC_SCAN_ENABLE_08 (MC_SCAN_ENABLE_08_in),
  .MC_SCAN_ENABLE_09 (MC_SCAN_ENABLE_09_in),
  .MC_SCAN_ENABLE_10 (MC_SCAN_ENABLE_10_in),
  .MC_SCAN_ENABLE_11 (MC_SCAN_ENABLE_11_in),
  .MC_SCAN_ENABLE_12 (MC_SCAN_ENABLE_12_in),
  .MC_SCAN_ENABLE_13 (MC_SCAN_ENABLE_13_in),
  .MC_SCAN_ENABLE_14 (MC_SCAN_ENABLE_14_in),
  .MC_SCAN_ENABLE_15 (MC_SCAN_ENABLE_15_in),
  .MC_SCAN_IN_00 (MC_SCAN_IN_00_in),
  .MC_SCAN_IN_01 (MC_SCAN_IN_01_in),
  .MC_SCAN_IN_02 (MC_SCAN_IN_02_in),
  .MC_SCAN_IN_03 (MC_SCAN_IN_03_in),
  .MC_SCAN_IN_04 (MC_SCAN_IN_04_in),
  .MC_SCAN_IN_05 (MC_SCAN_IN_05_in),
  .MC_SCAN_IN_06 (MC_SCAN_IN_06_in),
  .MC_SCAN_IN_07 (MC_SCAN_IN_07_in),
  .MC_SCAN_IN_08 (MC_SCAN_IN_08_in),
  .MC_SCAN_IN_09 (MC_SCAN_IN_09_in),
  .MC_SCAN_IN_10 (MC_SCAN_IN_10_in),
  .MC_SCAN_IN_11 (MC_SCAN_IN_11_in),
  .MC_SCAN_IN_12 (MC_SCAN_IN_12_in),
  .MC_SCAN_IN_13 (MC_SCAN_IN_13_in),
  .MC_SCAN_IN_14 (MC_SCAN_IN_14_in),
  .MC_SCAN_IN_15 (MC_SCAN_IN_15_in),
  .MC_SCAN_MODE_00 (MC_SCAN_MODE_00_in),
  .MC_SCAN_MODE_01 (MC_SCAN_MODE_01_in),
  .MC_SCAN_MODE_02 (MC_SCAN_MODE_02_in),
  .MC_SCAN_MODE_03 (MC_SCAN_MODE_03_in),
  .MC_SCAN_MODE_04 (MC_SCAN_MODE_04_in),
  .MC_SCAN_MODE_05 (MC_SCAN_MODE_05_in),
  .MC_SCAN_MODE_06 (MC_SCAN_MODE_06_in),
  .MC_SCAN_MODE_07 (MC_SCAN_MODE_07_in),
  .MC_SCAN_MODE_08 (MC_SCAN_MODE_08_in),
  .MC_SCAN_MODE_09 (MC_SCAN_MODE_09_in),
  .MC_SCAN_MODE_10 (MC_SCAN_MODE_10_in),
  .MC_SCAN_MODE_11 (MC_SCAN_MODE_11_in),
  .MC_SCAN_MODE_12 (MC_SCAN_MODE_12_in),
  .MC_SCAN_MODE_13 (MC_SCAN_MODE_13_in),
  .MC_SCAN_MODE_14 (MC_SCAN_MODE_14_in),
  .MC_SCAN_MODE_15 (MC_SCAN_MODE_15_in),
  .MC_SCAN_RST_N_00 (MC_SCAN_RST_N_00_in),
  .MC_SCAN_RST_N_01 (MC_SCAN_RST_N_01_in),
  .MC_SCAN_RST_N_02 (MC_SCAN_RST_N_02_in),
  .MC_SCAN_RST_N_03 (MC_SCAN_RST_N_03_in),
  .MC_SCAN_RST_N_04 (MC_SCAN_RST_N_04_in),
  .MC_SCAN_RST_N_05 (MC_SCAN_RST_N_05_in),
  .MC_SCAN_RST_N_06 (MC_SCAN_RST_N_06_in),
  .MC_SCAN_RST_N_07 (MC_SCAN_RST_N_07_in),
  .MC_SCAN_RST_N_08 (MC_SCAN_RST_N_08_in),
  .MC_SCAN_RST_N_09 (MC_SCAN_RST_N_09_in),
  .MC_SCAN_RST_N_10 (MC_SCAN_RST_N_10_in),
  .MC_SCAN_RST_N_11 (MC_SCAN_RST_N_11_in),
  .MC_SCAN_RST_N_12 (MC_SCAN_RST_N_12_in),
  .MC_SCAN_RST_N_13 (MC_SCAN_RST_N_13_in),
  .MC_SCAN_RST_N_14 (MC_SCAN_RST_N_14_in),
  .MC_SCAN_RST_N_15 (MC_SCAN_RST_N_15_in),
  .PHY_SCAN_CK_00 (PHY_SCAN_CK_00_in),
  .PHY_SCAN_CK_01 (PHY_SCAN_CK_01_in),
  .PHY_SCAN_ENABLE_00 (PHY_SCAN_ENABLE_00_in),
  .PHY_SCAN_ENABLE_01 (PHY_SCAN_ENABLE_01_in),
  .PHY_SCAN_IN_00 (PHY_SCAN_IN_00_in),
  .PHY_SCAN_IN_01 (PHY_SCAN_IN_01_in),
  .PHY_SCAN_MODE_00 (PHY_SCAN_MODE_00_in),
  .PHY_SCAN_MODE_01 (PHY_SCAN_MODE_01_in),
  .PHY_SCAN_RST_N_00 (PHY_SCAN_RST_N_00_in),
  .PHY_SCAN_RST_N_01 (PHY_SCAN_RST_N_01_in),
  .SW_SCAN_CK_00 (SW_SCAN_CK_00_in),
  .SW_SCAN_CK_01 (SW_SCAN_CK_01_in),
  .SW_SCAN_ENABLE_00 (SW_SCAN_ENABLE_00_in),
  .SW_SCAN_ENABLE_01 (SW_SCAN_ENABLE_01_in),
  .SW_SCAN_IN_00 (SW_SCAN_IN_00_in),
  .SW_SCAN_IN_01 (SW_SCAN_IN_01_in),
  .SW_SCAN_IN_02 (SW_SCAN_IN_02_in),
  .SW_SCAN_IN_03 (SW_SCAN_IN_03_in),
  .SW_SCAN_IN_04 (SW_SCAN_IN_04_in),
  .SW_SCAN_IN_05 (SW_SCAN_IN_05_in),
  .SW_SCAN_IN_06 (SW_SCAN_IN_06_in),
  .SW_SCAN_IN_07 (SW_SCAN_IN_07_in),
  .SW_SCAN_MODE_00 (SW_SCAN_MODE_00_in),
  .SW_SCAN_MODE_01 (SW_SCAN_MODE_01_in),
  .SW_SCAN_RST_N_00 (SW_SCAN_RST_N_00_in),
  .SW_SCAN_RST_N_01 (SW_SCAN_RST_N_01_in),
  .GSR (glblGSR)
);

endmodule

`endcelldefine
