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
//  /   /                        HBM_ONE_STACK_INTF
// /___/   /\      Filename    : HBM_ONE_STACK_INTF.v
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

module HBM_ONE_STACK_INTF #(
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
  parameter integer DATARATE_00 = 1800,
  parameter integer DATARATE_01 = 1800,
  parameter integer DATARATE_02 = 1800,
  parameter integer DATARATE_03 = 1800,
  parameter integer DATARATE_04 = 1800,
  parameter integer DATARATE_05 = 1800,
  parameter integer DATARATE_06 = 1800,
  parameter integer DATARATE_07 = 1800,
  parameter DA_LOCKOUT = "FALSE",
  parameter [0:0] IS_APB_0_PCLK_INVERTED = 1'b0,
  parameter [0:0] IS_APB_0_PRESET_N_INVERTED = 1'b0,
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
  parameter MC_ENABLE_0 = "FALSE",
  parameter MC_ENABLE_1 = "FALSE",
  parameter MC_ENABLE_2 = "FALSE",
  parameter MC_ENABLE_3 = "FALSE",
  parameter MC_ENABLE_4 = "FALSE",
  parameter MC_ENABLE_5 = "FALSE",
  parameter MC_ENABLE_6 = "FALSE",
  parameter MC_ENABLE_7 = "FALSE",
  parameter MC_ENABLE_APB = "FALSE",
  parameter integer PAGEHIT_PERCENT_00 = 75,
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
  parameter PHY_ENABLE_APB = "FALSE",
  parameter PHY_PCLK_INVERT_01 = "FALSE",
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
  parameter SIM_DEVICE = "ULTRASCALE_PLUS",
  parameter integer STACK_LOCATION = 0,
  parameter SWITCH_ENABLE = "FALSE",
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
  parameter integer WRITE_PERCENT_15 = 50
)(
  output [31:0] APB_0_PRDATA,
  output APB_0_PREADY,
  output APB_0_PSLVERR,
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
  output DRAM_0_STAT_CATTRIP,
  output [2:0] DRAM_0_STAT_TEMP,

  input [21:0] APB_0_PADDR,
  input APB_0_PCLK,
  input APB_0_PENABLE,
  input APB_0_PRESET_N,
  input APB_0_PSEL,
  input [31:0] APB_0_PWDATA,
  input APB_0_PWRITE,
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
  input BSCAN_DRCK,
  input BSCAN_TCK,
  input HBM_REF_CLK,
  input MBIST_EN_00,
  input MBIST_EN_01,
  input MBIST_EN_02,
  input MBIST_EN_03,
  input MBIST_EN_04,
  input MBIST_EN_05,
  input MBIST_EN_06,
  input MBIST_EN_07
);

// define constants
  localparam MODULE_NAME = "HBM_ONE_STACK_INTF";
  
// Parameter encodings and registers
  localparam PHY_PCLK_INVERT_01_FALSE = 0;
  localparam PHY_PCLK_INVERT_01_TRUE = 1;

  reg trig_attr;
// include dynamic registers - XILINX test only
`ifdef XIL_DR
  `include "HBM_ONE_STACK_INTF_dr.v"
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
  localparam [10:0] DATARATE_00_REG = DATARATE_00;
  localparam [10:0] DATARATE_01_REG = DATARATE_01;
  localparam [10:0] DATARATE_02_REG = DATARATE_02;
  localparam [10:0] DATARATE_03_REG = DATARATE_03;
  localparam [10:0] DATARATE_04_REG = DATARATE_04;
  localparam [10:0] DATARATE_05_REG = DATARATE_05;
  localparam [10:0] DATARATE_06_REG = DATARATE_06;
  localparam [10:0] DATARATE_07_REG = DATARATE_07;
  localparam [40:1] DA_LOCKOUT_REG = DA_LOCKOUT;
  localparam [0:0] IS_APB_0_PCLK_INVERTED_REG = IS_APB_0_PCLK_INVERTED;
  localparam [0:0] IS_APB_0_PRESET_N_INVERTED_REG = IS_APB_0_PRESET_N_INVERTED;
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
  localparam [40:1] MC_ENABLE_0_REG = MC_ENABLE_0;
  localparam [40:1] MC_ENABLE_1_REG = MC_ENABLE_1;
  localparam [40:1] MC_ENABLE_2_REG = MC_ENABLE_2;
  localparam [40:1] MC_ENABLE_3_REG = MC_ENABLE_3;
  localparam [40:1] MC_ENABLE_4_REG = MC_ENABLE_4;
  localparam [40:1] MC_ENABLE_5_REG = MC_ENABLE_5;
  localparam [40:1] MC_ENABLE_6_REG = MC_ENABLE_6;
  localparam [40:1] MC_ENABLE_7_REG = MC_ENABLE_7;
  localparam [40:1] MC_ENABLE_APB_REG = MC_ENABLE_APB;
  localparam [6:0] PAGEHIT_PERCENT_00_REG = PAGEHIT_PERCENT_00;
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
  localparam [40:1] PHY_ENABLE_APB_REG = PHY_ENABLE_APB;
  localparam [40:1] PHY_PCLK_INVERT_01_REG = PHY_PCLK_INVERT_01;
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
  localparam [152:1] SIM_DEVICE_REG = SIM_DEVICE;
  localparam [0:0] STACK_LOCATION_REG = STACK_LOCATION;
  localparam [40:1] SWITCH_ENABLE_REG = SWITCH_ENABLE;
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
`endif

  localparam [7:0] ANALOG_MUX_SEL_0_REG = 8'h00;
  localparam [40:1] APB_BYPASS_EN_REG = "FALSE";
  localparam [40:1] AXI_BYPASS_EN_REG = "FALSE";
  localparam [40:1] BLI_TESTMODE_SEL_REG = "FALSE";
  localparam [51:0] DBG_BYPASS_VAL_REG = 52'hFFFFFFFFFFFFF;
  localparam [40:1] DEBUG_MODE_REG = "FALSE";
  localparam [51:0] DFI_BYPASS_VAL_REG = 52'h0000000000000;
  localparam [40:1] DLL_TESTMODE_SEL_0_REG = "FALSE";
  localparam [40:1] IO_TESTMODE_SEL_0_REG = "FALSE";
  localparam [40:1] MC_CSSD_SEL_0_REG = "FALSE";
  localparam [40:1] MC_CSSD_SEL_1_REG = "FALSE";
  localparam [40:1] MC_CSSD_SEL_2_REG = "FALSE";
  localparam [40:1] MC_CSSD_SEL_3_REG = "FALSE";
  localparam [40:1] MC_CSSD_SEL_4_REG = "FALSE";
  localparam [40:1] MC_CSSD_SEL_5_REG = "FALSE";
  localparam [40:1] MC_CSSD_SEL_6_REG = "FALSE";
  localparam [40:1] MC_CSSD_SEL_7_REG = "FALSE";
  localparam [40:1] MC_TESTMODE_SEL_0_REG = "FALSE";
  localparam [40:1] MC_TESTMODE_SEL_1_REG = "FALSE";
  localparam [40:1] MC_TESTMODE_SEL_2_REG = "FALSE";
  localparam [40:1] MC_TESTMODE_SEL_3_REG = "FALSE";
  localparam [40:1] MC_TESTMODE_SEL_4_REG = "FALSE";
  localparam [40:1] MC_TESTMODE_SEL_5_REG = "FALSE";
  localparam [40:1] MC_TESTMODE_SEL_6_REG = "FALSE";
  localparam [40:1] MC_TESTMODE_SEL_7_REG = "FALSE";
  localparam [40:1] PHY_CSSD_SEL_0_REG = "FALSE";
  localparam [40:1] PHY_TESTMODE_SEL_0_REG = "FALSE";
  localparam [40:1] SW_TESTMODE_SEL_0_REG = "FALSE";

`ifdef XIL_XECLIB
  wire PHY_PCLK_INVERT_01_BIN;
`else
  reg PHY_PCLK_INVERT_01_BIN;
`endif

  reg attr_test;
  reg attr_err;
  tri0 glblGSR = glbl.GSR;

  wire APB_0_PREADY_out;
  wire APB_0_PSLVERR_out;
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
  wire DRAM_0_STAT_CATTRIP_out;
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
  wire [1:0] DLL_SCAN_OUT_00_out;
  wire [1:0] IO_SCAN_OUT_00_out;
  wire [1:0] MC_SCAN_OUT_00_out;
  wire [1:0] MC_SCAN_OUT_01_out;
  wire [1:0] MC_SCAN_OUT_02_out;
  wire [1:0] MC_SCAN_OUT_03_out;
  wire [1:0] MC_SCAN_OUT_04_out;
  wire [1:0] MC_SCAN_OUT_05_out;
  wire [1:0] MC_SCAN_OUT_06_out;
  wire [1:0] MC_SCAN_OUT_07_out;
  wire [1:0] PHY_SCAN_OUT_00_out;
  wire [1:0] STATUS_00_out;
  wire [1:0] STATUS_01_out;
  wire [1:0] STATUS_02_out;
  wire [1:0] STATUS_03_out;
  wire [1:0] STATUS_04_out;
  wire [1:0] STATUS_05_out;
  wire [1:0] STATUS_06_out;
  wire [1:0] STATUS_07_out;
  wire [1:0] SW_SCAN_OUT_00_out;
  wire [1:0] SW_SCAN_OUT_01_out;
  wire [1:0] SW_SCAN_OUT_02_out;
  wire [1:0] SW_SCAN_OUT_03_out;
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
  wire [2:0] DRAM_0_STAT_TEMP_out;
  wire [31:0] APB_0_PRDATA_out;
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

  wire ANALOG_HBM_SEL_00_in;
  wire APB_0_PCLK_in;
  wire APB_0_PENABLE_in;
  wire APB_0_PRESET_N_in;
  wire APB_0_PSEL_in;
  wire APB_0_PWRITE_in;
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
  wire BSCAN_DRCK_in;
  wire BSCAN_TCK_in;
  wire DLL_SCAN_CK_00_in;
  wire DLL_SCAN_ENABLE_00_in;
  wire DLL_SCAN_MODE_00_in;
  wire DLL_SCAN_RST_N_00_in;
  wire HBM_REF_CLK_in;
  wire IO_SCAN_CK_00_in;
  wire IO_SCAN_ENABLE_00_in;
  wire IO_SCAN_MODE_00_in;
  wire IO_SCAN_RST_N_00_in;
  wire MBIST_EN_00_in;
  wire MBIST_EN_01_in;
  wire MBIST_EN_02_in;
  wire MBIST_EN_03_in;
  wire MBIST_EN_04_in;
  wire MBIST_EN_05_in;
  wire MBIST_EN_06_in;
  wire MBIST_EN_07_in;
  wire MC_SCAN_CK_00_in;
  wire MC_SCAN_CK_01_in;
  wire MC_SCAN_CK_02_in;
  wire MC_SCAN_CK_03_in;
  wire MC_SCAN_CK_04_in;
  wire MC_SCAN_CK_05_in;
  wire MC_SCAN_CK_06_in;
  wire MC_SCAN_CK_07_in;
  wire MC_SCAN_ENABLE_00_in;
  wire MC_SCAN_ENABLE_01_in;
  wire MC_SCAN_ENABLE_02_in;
  wire MC_SCAN_ENABLE_03_in;
  wire MC_SCAN_ENABLE_04_in;
  wire MC_SCAN_ENABLE_05_in;
  wire MC_SCAN_ENABLE_06_in;
  wire MC_SCAN_ENABLE_07_in;
  wire MC_SCAN_MODE_00_in;
  wire MC_SCAN_MODE_01_in;
  wire MC_SCAN_MODE_02_in;
  wire MC_SCAN_MODE_03_in;
  wire MC_SCAN_MODE_04_in;
  wire MC_SCAN_MODE_05_in;
  wire MC_SCAN_MODE_06_in;
  wire MC_SCAN_MODE_07_in;
  wire MC_SCAN_RST_N_00_in;
  wire MC_SCAN_RST_N_01_in;
  wire MC_SCAN_RST_N_02_in;
  wire MC_SCAN_RST_N_03_in;
  wire MC_SCAN_RST_N_04_in;
  wire MC_SCAN_RST_N_05_in;
  wire MC_SCAN_RST_N_06_in;
  wire MC_SCAN_RST_N_07_in;
  wire PHY_SCAN_CK_00_in;
  wire PHY_SCAN_ENABLE_00_in;
  wire PHY_SCAN_MODE_00_in;
  wire PHY_SCAN_RST_N_00_in;
  wire SW_SCAN_CK_00_in;
  wire SW_SCAN_ENABLE_00_in;
  wire SW_SCAN_MODE_00_in;
  wire SW_SCAN_RST_N_00_in;
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
  wire [1:0] DLL_SCAN_IN_00_in;
  wire [1:0] IO_SCAN_IN_00_in;
  wire [1:0] MC_SCAN_IN_00_in;
  wire [1:0] MC_SCAN_IN_01_in;
  wire [1:0] MC_SCAN_IN_02_in;
  wire [1:0] MC_SCAN_IN_03_in;
  wire [1:0] MC_SCAN_IN_04_in;
  wire [1:0] MC_SCAN_IN_05_in;
  wire [1:0] MC_SCAN_IN_06_in;
  wire [1:0] MC_SCAN_IN_07_in;
  wire [1:0] PHY_SCAN_IN_00_in;
  wire [1:0] SW_SCAN_IN_00_in;
  wire [1:0] SW_SCAN_IN_01_in;
  wire [1:0] SW_SCAN_IN_02_in;
  wire [1:0] SW_SCAN_IN_03_in;
  wire [21:0] APB_0_PADDR_in;
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
  wire [31:0] APB_0_PWDATA_in;
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

  assign APB_0_PRDATA = APB_0_PRDATA_out;
  assign APB_0_PREADY = APB_0_PREADY_out;
  assign APB_0_PSLVERR = APB_0_PSLVERR_out;
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
  assign DRAM_0_STAT_CATTRIP = DRAM_0_STAT_CATTRIP_out;
  assign DRAM_0_STAT_TEMP = DRAM_0_STAT_TEMP_out;

  assign APB_0_PADDR_in = APB_0_PADDR;
  assign APB_0_PCLK_in = APB_0_PCLK;
  assign APB_0_PENABLE_in = APB_0_PENABLE;
  assign APB_0_PRESET_N_in = APB_0_PRESET_N;
  assign APB_0_PSEL_in = APB_0_PSEL;
  assign APB_0_PWDATA_in = APB_0_PWDATA;
  assign APB_0_PWRITE_in = APB_0_PWRITE;
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
  assign BSCAN_DRCK_in = BSCAN_DRCK;
  assign BSCAN_TCK_in = BSCAN_TCK;
  assign HBM_REF_CLK_in = HBM_REF_CLK;
  assign MBIST_EN_00_in = MBIST_EN_00;
  assign MBIST_EN_01_in = MBIST_EN_01;
  assign MBIST_EN_02_in = MBIST_EN_02;
  assign MBIST_EN_03_in = MBIST_EN_03;
  assign MBIST_EN_04_in = MBIST_EN_04;
  assign MBIST_EN_05_in = MBIST_EN_05;
  assign MBIST_EN_06_in = MBIST_EN_06;
  assign MBIST_EN_07_in = MBIST_EN_07;

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
    $display("Error: [Unisim %s-105] CLK_SEL_00 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_00_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_01_REG != "FALSE") &&
       (CLK_SEL_01_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-106] CLK_SEL_01 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_01_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_02_REG != "FALSE") &&
       (CLK_SEL_02_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-107] CLK_SEL_02 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_02_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_03_REG != "FALSE") &&
       (CLK_SEL_03_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-108] CLK_SEL_03 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_03_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_04_REG != "FALSE") &&
       (CLK_SEL_04_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-109] CLK_SEL_04 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_04_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_05_REG != "FALSE") &&
       (CLK_SEL_05_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-110] CLK_SEL_05 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_05_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_06_REG != "FALSE") &&
       (CLK_SEL_06_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-111] CLK_SEL_06 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_06_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_07_REG != "FALSE") &&
       (CLK_SEL_07_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-112] CLK_SEL_07 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_07_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_08_REG != "FALSE") &&
       (CLK_SEL_08_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-113] CLK_SEL_08 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_08_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_09_REG != "FALSE") &&
       (CLK_SEL_09_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-114] CLK_SEL_09 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_09_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_10_REG != "FALSE") &&
       (CLK_SEL_10_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-115] CLK_SEL_10 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_10_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_11_REG != "FALSE") &&
       (CLK_SEL_11_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-116] CLK_SEL_11 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_11_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_12_REG != "FALSE") &&
       (CLK_SEL_12_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-117] CLK_SEL_12 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_12_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_13_REG != "FALSE") &&
       (CLK_SEL_13_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-118] CLK_SEL_13 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_13_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_14_REG != "FALSE") &&
       (CLK_SEL_14_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-119] CLK_SEL_14 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_14_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_15_REG != "FALSE") &&
       (CLK_SEL_15_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-120] CLK_SEL_15 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_15_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DATARATE_00_REG < 50) || (DATARATE_00_REG > 1800))) begin
    $display("Error: [Unisim %s-121] DATARATE_00 attribute is set to %d.  Legal values for this attribute are 50 to 1800. Instance: %m", MODULE_NAME, DATARATE_00_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DATARATE_01_REG < 50) || (DATARATE_01_REG > 1800))) begin
    $display("Error: [Unisim %s-122] DATARATE_01 attribute is set to %d.  Legal values for this attribute are 50 to 1800. Instance: %m", MODULE_NAME, DATARATE_01_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DATARATE_02_REG < 50) || (DATARATE_02_REG > 1800))) begin
    $display("Error: [Unisim %s-123] DATARATE_02 attribute is set to %d.  Legal values for this attribute are 50 to 1800. Instance: %m", MODULE_NAME, DATARATE_02_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DATARATE_03_REG < 50) || (DATARATE_03_REG > 1800))) begin
    $display("Error: [Unisim %s-124] DATARATE_03 attribute is set to %d.  Legal values for this attribute are 50 to 1800. Instance: %m", MODULE_NAME, DATARATE_03_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DATARATE_04_REG < 50) || (DATARATE_04_REG > 1800))) begin
    $display("Error: [Unisim %s-125] DATARATE_04 attribute is set to %d.  Legal values for this attribute are 50 to 1800. Instance: %m", MODULE_NAME, DATARATE_04_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DATARATE_05_REG < 50) || (DATARATE_05_REG > 1800))) begin
    $display("Error: [Unisim %s-126] DATARATE_05 attribute is set to %d.  Legal values for this attribute are 50 to 1800. Instance: %m", MODULE_NAME, DATARATE_05_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DATARATE_06_REG < 50) || (DATARATE_06_REG > 1800))) begin
    $display("Error: [Unisim %s-127] DATARATE_06 attribute is set to %d.  Legal values for this attribute are 50 to 1800. Instance: %m", MODULE_NAME, DATARATE_06_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DATARATE_07_REG < 50) || (DATARATE_07_REG > 1800))) begin
    $display("Error: [Unisim %s-128] DATARATE_07 attribute is set to %d.  Legal values for this attribute are 50 to 1800. Instance: %m", MODULE_NAME, DATARATE_07_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DA_LOCKOUT_REG != "FALSE") &&
       (DA_LOCKOUT_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-129] DA_LOCKOUT attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, DA_LOCKOUT_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((MC_ENABLE_0_REG != "FALSE") &&
       (MC_ENABLE_0_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-177] MC_ENABLE_0 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, MC_ENABLE_0_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((MC_ENABLE_1_REG != "FALSE") &&
       (MC_ENABLE_1_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-178] MC_ENABLE_1 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, MC_ENABLE_1_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((MC_ENABLE_2_REG != "FALSE") &&
       (MC_ENABLE_2_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-179] MC_ENABLE_2 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, MC_ENABLE_2_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((MC_ENABLE_3_REG != "FALSE") &&
       (MC_ENABLE_3_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-180] MC_ENABLE_3 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, MC_ENABLE_3_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((MC_ENABLE_4_REG != "FALSE") &&
       (MC_ENABLE_4_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-181] MC_ENABLE_4 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, MC_ENABLE_4_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((MC_ENABLE_5_REG != "FALSE") &&
       (MC_ENABLE_5_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-182] MC_ENABLE_5 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, MC_ENABLE_5_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((MC_ENABLE_6_REG != "FALSE") &&
       (MC_ENABLE_6_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-183] MC_ENABLE_6 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, MC_ENABLE_6_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((MC_ENABLE_7_REG != "FALSE") &&
       (MC_ENABLE_7_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-184] MC_ENABLE_7 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, MC_ENABLE_7_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((MC_ENABLE_APB_REG != "FALSE") &&
       (MC_ENABLE_APB_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-185] MC_ENABLE_APB attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, MC_ENABLE_APB_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PAGEHIT_PERCENT_00_REG < 0) || (PAGEHIT_PERCENT_00_REG > 100))) begin
    $display("Error: [Unisim %s-194] PAGEHIT_PERCENT_00 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, PAGEHIT_PERCENT_00_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_00_REG != "FALSE") &&
       (PHY_ENABLE_00_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-196] PHY_ENABLE_00 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_00_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_01_REG != "FALSE") &&
       (PHY_ENABLE_01_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-197] PHY_ENABLE_01 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_01_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_02_REG != "FALSE") &&
       (PHY_ENABLE_02_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-198] PHY_ENABLE_02 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_02_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_03_REG != "FALSE") &&
       (PHY_ENABLE_03_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-199] PHY_ENABLE_03 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_03_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_04_REG != "FALSE") &&
       (PHY_ENABLE_04_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-200] PHY_ENABLE_04 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_04_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_05_REG != "FALSE") &&
       (PHY_ENABLE_05_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-201] PHY_ENABLE_05 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_05_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_06_REG != "FALSE") &&
       (PHY_ENABLE_06_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-202] PHY_ENABLE_06 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_06_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_07_REG != "FALSE") &&
       (PHY_ENABLE_07_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-203] PHY_ENABLE_07 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_07_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_08_REG != "FALSE") &&
       (PHY_ENABLE_08_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-204] PHY_ENABLE_08 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_08_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_09_REG != "FALSE") &&
       (PHY_ENABLE_09_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-205] PHY_ENABLE_09 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_09_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_10_REG != "FALSE") &&
       (PHY_ENABLE_10_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-206] PHY_ENABLE_10 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_10_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_11_REG != "FALSE") &&
       (PHY_ENABLE_11_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-207] PHY_ENABLE_11 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_11_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_12_REG != "FALSE") &&
       (PHY_ENABLE_12_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-208] PHY_ENABLE_12 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_12_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_13_REG != "FALSE") &&
       (PHY_ENABLE_13_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-209] PHY_ENABLE_13 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_13_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_14_REG != "FALSE") &&
       (PHY_ENABLE_14_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-210] PHY_ENABLE_14 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_14_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_15_REG != "FALSE") &&
       (PHY_ENABLE_15_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-211] PHY_ENABLE_15 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_15_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_APB_REG != "FALSE") &&
       (PHY_ENABLE_APB_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-212] PHY_ENABLE_APB attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_APB_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_PCLK_INVERT_01_REG != "FALSE") &&
       (PHY_PCLK_INVERT_01_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-213] PHY_PCLK_INVERT_01 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_PCLK_INVERT_01_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_00_REG < 0) || (READ_PERCENT_00_REG > 100))) begin
    $display("Error: [Unisim %s-215] READ_PERCENT_00 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_00_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_01_REG < 0) || (READ_PERCENT_01_REG > 100))) begin
    $display("Error: [Unisim %s-216] READ_PERCENT_01 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_01_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_02_REG < 0) || (READ_PERCENT_02_REG > 100))) begin
    $display("Error: [Unisim %s-217] READ_PERCENT_02 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_02_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_03_REG < 0) || (READ_PERCENT_03_REG > 100))) begin
    $display("Error: [Unisim %s-218] READ_PERCENT_03 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_03_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_04_REG < 0) || (READ_PERCENT_04_REG > 100))) begin
    $display("Error: [Unisim %s-219] READ_PERCENT_04 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_04_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_05_REG < 0) || (READ_PERCENT_05_REG > 100))) begin
    $display("Error: [Unisim %s-220] READ_PERCENT_05 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_05_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_06_REG < 0) || (READ_PERCENT_06_REG > 100))) begin
    $display("Error: [Unisim %s-221] READ_PERCENT_06 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_06_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_07_REG < 0) || (READ_PERCENT_07_REG > 100))) begin
    $display("Error: [Unisim %s-222] READ_PERCENT_07 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_07_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_08_REG < 0) || (READ_PERCENT_08_REG > 100))) begin
    $display("Error: [Unisim %s-223] READ_PERCENT_08 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_08_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_09_REG < 0) || (READ_PERCENT_09_REG > 100))) begin
    $display("Error: [Unisim %s-224] READ_PERCENT_09 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_09_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_10_REG < 0) || (READ_PERCENT_10_REG > 100))) begin
    $display("Error: [Unisim %s-225] READ_PERCENT_10 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_10_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_11_REG < 0) || (READ_PERCENT_11_REG > 100))) begin
    $display("Error: [Unisim %s-226] READ_PERCENT_11 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_11_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_12_REG < 0) || (READ_PERCENT_12_REG > 100))) begin
    $display("Error: [Unisim %s-227] READ_PERCENT_12 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_12_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_13_REG < 0) || (READ_PERCENT_13_REG > 100))) begin
    $display("Error: [Unisim %s-228] READ_PERCENT_13 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_13_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_14_REG < 0) || (READ_PERCENT_14_REG > 100))) begin
    $display("Error: [Unisim %s-229] READ_PERCENT_14 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_14_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((READ_PERCENT_15_REG < 0) || (READ_PERCENT_15_REG > 100))) begin
    $display("Error: [Unisim %s-230] READ_PERCENT_15 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, READ_PERCENT_15_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
        ((SIM_DEVICE_REG != "ULTRASCALE_PLUS") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES1") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES2"))) begin
      $display("Error: [Unisim %s-231] SIM_DEVICE attribute is set to %s.  Legal values for this attribute are ULTRASCALE_PLUS, ULTRASCALE_PLUS_ES1 or ULTRASCALE_PLUS_ES2. Instance: %m", MODULE_NAME, SIM_DEVICE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
      ((STACK_LOCATION_REG != 0) &&
       (STACK_LOCATION_REG != 1))) begin
      $display("Error: [Unisim %s-232] STACK_LOCATION attribute is set to %d.  Legal values for this attribute are 0 or 1. Instance: %m", MODULE_NAME, STACK_LOCATION_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((SWITCH_ENABLE_REG != "FALSE") &&
       (SWITCH_ENABLE_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-233] SWITCH_ENABLE attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, SWITCH_ENABLE_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_00_REG < 0) || (WRITE_PERCENT_00_REG > 100))) begin
      $display("Error: [Unisim %s-235] WRITE_PERCENT_00 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_00_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_01_REG < 0) || (WRITE_PERCENT_01_REG > 100))) begin
      $display("Error: [Unisim %s-236] WRITE_PERCENT_01 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_01_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_02_REG < 0) || (WRITE_PERCENT_02_REG > 100))) begin
      $display("Error: [Unisim %s-237] WRITE_PERCENT_02 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_02_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_03_REG < 0) || (WRITE_PERCENT_03_REG > 100))) begin
      $display("Error: [Unisim %s-238] WRITE_PERCENT_03 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_03_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_04_REG < 0) || (WRITE_PERCENT_04_REG > 100))) begin
      $display("Error: [Unisim %s-239] WRITE_PERCENT_04 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_04_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_05_REG < 0) || (WRITE_PERCENT_05_REG > 100))) begin
      $display("Error: [Unisim %s-240] WRITE_PERCENT_05 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_05_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_06_REG < 0) || (WRITE_PERCENT_06_REG > 100))) begin
      $display("Error: [Unisim %s-241] WRITE_PERCENT_06 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_06_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_07_REG < 0) || (WRITE_PERCENT_07_REG > 100))) begin
      $display("Error: [Unisim %s-242] WRITE_PERCENT_07 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_07_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_08_REG < 0) || (WRITE_PERCENT_08_REG > 100))) begin
      $display("Error: [Unisim %s-243] WRITE_PERCENT_08 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_08_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_09_REG < 0) || (WRITE_PERCENT_09_REG > 100))) begin
      $display("Error: [Unisim %s-244] WRITE_PERCENT_09 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_09_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_10_REG < 0) || (WRITE_PERCENT_10_REG > 100))) begin
      $display("Error: [Unisim %s-245] WRITE_PERCENT_10 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_10_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_11_REG < 0) || (WRITE_PERCENT_11_REG > 100))) begin
      $display("Error: [Unisim %s-246] WRITE_PERCENT_11 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_11_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_12_REG < 0) || (WRITE_PERCENT_12_REG > 100))) begin
      $display("Error: [Unisim %s-247] WRITE_PERCENT_12 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_12_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_13_REG < 0) || (WRITE_PERCENT_13_REG > 100))) begin
      $display("Error: [Unisim %s-248] WRITE_PERCENT_13 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_13_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_14_REG < 0) || (WRITE_PERCENT_14_REG > 100))) begin
      $display("Error: [Unisim %s-249] WRITE_PERCENT_14 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_14_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((WRITE_PERCENT_15_REG < 0) || (WRITE_PERCENT_15_REG > 100))) begin
      $display("Error: [Unisim %s-250] WRITE_PERCENT_15 attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, WRITE_PERCENT_15_REG);
    attr_err = 1'b1;
  end
  
  if (attr_err == 1'b1) #1 $finish;
end
`endif



assign ANALOG_HBM_SEL_00_in = 1'b1; // tie off
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
assign DLL_SCAN_CK_00_in = 1'b1; // tie off
assign DLL_SCAN_ENABLE_00_in = 1'b1; // tie off
assign DLL_SCAN_IN_00_in = 2'b11; // tie off
assign DLL_SCAN_MODE_00_in = 1'b1; // tie off
assign DLL_SCAN_RST_N_00_in = 1'b1; // tie off
assign IO_SCAN_CK_00_in = 1'b1; // tie off
assign IO_SCAN_ENABLE_00_in = 1'b1; // tie off
assign IO_SCAN_IN_00_in = 2'b11; // tie off
assign IO_SCAN_MODE_00_in = 1'b1; // tie off
assign IO_SCAN_RST_N_00_in = 1'b1; // tie off
assign MC_SCAN_CK_00_in = 1'b1; // tie off
assign MC_SCAN_CK_01_in = 1'b1; // tie off
assign MC_SCAN_CK_02_in = 1'b1; // tie off
assign MC_SCAN_CK_03_in = 1'b1; // tie off
assign MC_SCAN_CK_04_in = 1'b1; // tie off
assign MC_SCAN_CK_05_in = 1'b1; // tie off
assign MC_SCAN_CK_06_in = 1'b1; // tie off
assign MC_SCAN_CK_07_in = 1'b1; // tie off
assign MC_SCAN_ENABLE_00_in = 1'b1; // tie off
assign MC_SCAN_ENABLE_01_in = 1'b1; // tie off
assign MC_SCAN_ENABLE_02_in = 1'b1; // tie off
assign MC_SCAN_ENABLE_03_in = 1'b1; // tie off
assign MC_SCAN_ENABLE_04_in = 1'b1; // tie off
assign MC_SCAN_ENABLE_05_in = 1'b1; // tie off
assign MC_SCAN_ENABLE_06_in = 1'b1; // tie off
assign MC_SCAN_ENABLE_07_in = 1'b1; // tie off
assign MC_SCAN_IN_00_in = 2'b11; // tie off
assign MC_SCAN_IN_01_in = 2'b11; // tie off
assign MC_SCAN_IN_02_in = 2'b11; // tie off
assign MC_SCAN_IN_03_in = 2'b11; // tie off
assign MC_SCAN_IN_04_in = 2'b11; // tie off
assign MC_SCAN_IN_05_in = 2'b11; // tie off
assign MC_SCAN_IN_06_in = 2'b11; // tie off
assign MC_SCAN_IN_07_in = 2'b11; // tie off
assign MC_SCAN_MODE_00_in = 1'b1; // tie off
assign MC_SCAN_MODE_01_in = 1'b1; // tie off
assign MC_SCAN_MODE_02_in = 1'b1; // tie off
assign MC_SCAN_MODE_03_in = 1'b1; // tie off
assign MC_SCAN_MODE_04_in = 1'b1; // tie off
assign MC_SCAN_MODE_05_in = 1'b1; // tie off
assign MC_SCAN_MODE_06_in = 1'b1; // tie off
assign MC_SCAN_MODE_07_in = 1'b1; // tie off
assign MC_SCAN_RST_N_00_in = 1'b1; // tie off
assign MC_SCAN_RST_N_01_in = 1'b1; // tie off
assign MC_SCAN_RST_N_02_in = 1'b1; // tie off
assign MC_SCAN_RST_N_03_in = 1'b1; // tie off
assign MC_SCAN_RST_N_04_in = 1'b1; // tie off
assign MC_SCAN_RST_N_05_in = 1'b1; // tie off
assign MC_SCAN_RST_N_06_in = 1'b1; // tie off
assign MC_SCAN_RST_N_07_in = 1'b1; // tie off
assign PHY_SCAN_CK_00_in = 1'b1; // tie off
assign PHY_SCAN_ENABLE_00_in = 1'b1; // tie off
assign PHY_SCAN_IN_00_in = 2'b11; // tie off
assign PHY_SCAN_MODE_00_in = 1'b1; // tie off
assign PHY_SCAN_RST_N_00_in = 1'b1; // tie off
assign SW_SCAN_CK_00_in = 1'b1; // tie off
assign SW_SCAN_ENABLE_00_in = 1'b1; // tie off
assign SW_SCAN_IN_00_in = 2'b11; // tie off
assign SW_SCAN_IN_01_in = 2'b11; // tie off
assign SW_SCAN_IN_02_in = 2'b11; // tie off
assign SW_SCAN_IN_03_in = 2'b11; // tie off
assign SW_SCAN_MODE_00_in = 1'b1; // tie off
assign SW_SCAN_RST_N_00_in = 1'b1; // tie off

SIP_HBM_ONE_STACK_INTF SIP_HBM_ONE_STACK_INTF_INST (
  .ANALOG_MUX_SEL_0 (ANALOG_MUX_SEL_0_REG),
  .APB_BYPASS_EN (APB_BYPASS_EN_REG),
  .AXI_BYPASS_EN (AXI_BYPASS_EN_REG),
  .BLI_TESTMODE_SEL (BLI_TESTMODE_SEL_REG),
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
  .DATARATE_00 (DATARATE_00_REG),
  .DATARATE_01 (DATARATE_01_REG),
  .DATARATE_02 (DATARATE_02_REG),
  .DATARATE_03 (DATARATE_03_REG),
  .DATARATE_04 (DATARATE_04_REG),
  .DATARATE_05 (DATARATE_05_REG),
  .DATARATE_06 (DATARATE_06_REG),
  .DATARATE_07 (DATARATE_07_REG),
  .DA_LOCKOUT (DA_LOCKOUT_REG),
  .DBG_BYPASS_VAL (DBG_BYPASS_VAL_REG),
  .DEBUG_MODE (DEBUG_MODE_REG),
  .DFI_BYPASS_VAL (DFI_BYPASS_VAL_REG),
  .DLL_TESTMODE_SEL_0 (DLL_TESTMODE_SEL_0_REG),
  .IO_TESTMODE_SEL_0 (IO_TESTMODE_SEL_0_REG),
  .IS_APB_0_PCLK_INVERTED (IS_APB_0_PCLK_INVERTED_REG),
  .IS_APB_0_PRESET_N_INVERTED (IS_APB_0_PRESET_N_INVERTED_REG),
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
  .MC_CSSD_SEL_0 (MC_CSSD_SEL_0_REG),
  .MC_CSSD_SEL_1 (MC_CSSD_SEL_1_REG),
  .MC_CSSD_SEL_2 (MC_CSSD_SEL_2_REG),
  .MC_CSSD_SEL_3 (MC_CSSD_SEL_3_REG),
  .MC_CSSD_SEL_4 (MC_CSSD_SEL_4_REG),
  .MC_CSSD_SEL_5 (MC_CSSD_SEL_5_REG),
  .MC_CSSD_SEL_6 (MC_CSSD_SEL_6_REG),
  .MC_CSSD_SEL_7 (MC_CSSD_SEL_7_REG),
  .MC_ENABLE_0 (MC_ENABLE_0_REG),
  .MC_ENABLE_1 (MC_ENABLE_1_REG),
  .MC_ENABLE_2 (MC_ENABLE_2_REG),
  .MC_ENABLE_3 (MC_ENABLE_3_REG),
  .MC_ENABLE_4 (MC_ENABLE_4_REG),
  .MC_ENABLE_5 (MC_ENABLE_5_REG),
  .MC_ENABLE_6 (MC_ENABLE_6_REG),
  .MC_ENABLE_7 (MC_ENABLE_7_REG),
  .MC_ENABLE_APB (MC_ENABLE_APB_REG),
  .MC_TESTMODE_SEL_0 (MC_TESTMODE_SEL_0_REG),
  .MC_TESTMODE_SEL_1 (MC_TESTMODE_SEL_1_REG),
  .MC_TESTMODE_SEL_2 (MC_TESTMODE_SEL_2_REG),
  .MC_TESTMODE_SEL_3 (MC_TESTMODE_SEL_3_REG),
  .MC_TESTMODE_SEL_4 (MC_TESTMODE_SEL_4_REG),
  .MC_TESTMODE_SEL_5 (MC_TESTMODE_SEL_5_REG),
  .MC_TESTMODE_SEL_6 (MC_TESTMODE_SEL_6_REG),
  .MC_TESTMODE_SEL_7 (MC_TESTMODE_SEL_7_REG),
  .PAGEHIT_PERCENT_00 (PAGEHIT_PERCENT_00_REG),
  .PHY_CSSD_SEL_0 (PHY_CSSD_SEL_0_REG),
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
  .PHY_ENABLE_APB (PHY_ENABLE_APB_REG),
  .PHY_PCLK_INVERT_01 (PHY_PCLK_INVERT_01_REG),
  .PHY_TESTMODE_SEL_0 (PHY_TESTMODE_SEL_0_REG),
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
  .STACK_LOCATION (STACK_LOCATION_REG),
  .SWITCH_ENABLE (SWITCH_ENABLE_REG),
  .SW_TESTMODE_SEL_0 (SW_TESTMODE_SEL_0_REG),
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
  .APB_0_PRDATA (APB_0_PRDATA_out),
  .APB_0_PREADY (APB_0_PREADY_out),
  .APB_0_PSLVERR (APB_0_PSLVERR_out),
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
  .DLL_SCAN_OUT_00 (DLL_SCAN_OUT_00_out),
  .DRAM_0_STAT_CATTRIP (DRAM_0_STAT_CATTRIP_out),
  .DRAM_0_STAT_TEMP (DRAM_0_STAT_TEMP_out),
  .IO_SCAN_OUT_00 (IO_SCAN_OUT_00_out),
  .MC_SCAN_OUT_00 (MC_SCAN_OUT_00_out),
  .MC_SCAN_OUT_01 (MC_SCAN_OUT_01_out),
  .MC_SCAN_OUT_02 (MC_SCAN_OUT_02_out),
  .MC_SCAN_OUT_03 (MC_SCAN_OUT_03_out),
  .MC_SCAN_OUT_04 (MC_SCAN_OUT_04_out),
  .MC_SCAN_OUT_05 (MC_SCAN_OUT_05_out),
  .MC_SCAN_OUT_06 (MC_SCAN_OUT_06_out),
  .MC_SCAN_OUT_07 (MC_SCAN_OUT_07_out),
  .PHY_SCAN_OUT_00 (PHY_SCAN_OUT_00_out),
  .STATUS_00 (STATUS_00_out),
  .STATUS_01 (STATUS_01_out),
  .STATUS_02 (STATUS_02_out),
  .STATUS_03 (STATUS_03_out),
  .STATUS_04 (STATUS_04_out),
  .STATUS_05 (STATUS_05_out),
  .STATUS_06 (STATUS_06_out),
  .STATUS_07 (STATUS_07_out),
  .SW_SCAN_OUT_00 (SW_SCAN_OUT_00_out),
  .SW_SCAN_OUT_01 (SW_SCAN_OUT_01_out),
  .SW_SCAN_OUT_02 (SW_SCAN_OUT_02_out),
  .SW_SCAN_OUT_03 (SW_SCAN_OUT_03_out),
  .ANALOG_HBM_SEL_00 (ANALOG_HBM_SEL_00_in),
  .APB_0_PADDR (APB_0_PADDR_in),
  .APB_0_PCLK (APB_0_PCLK_in),
  .APB_0_PENABLE (APB_0_PENABLE_in),
  .APB_0_PRESET_N (APB_0_PRESET_N_in),
  .APB_0_PSEL (APB_0_PSEL_in),
  .APB_0_PWDATA (APB_0_PWDATA_in),
  .APB_0_PWRITE (APB_0_PWRITE_in),
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
  .BSCAN_DRCK (BSCAN_DRCK_in),
  .BSCAN_TCK (BSCAN_TCK_in),
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
  .DLL_SCAN_CK_00 (DLL_SCAN_CK_00_in),
  .DLL_SCAN_ENABLE_00 (DLL_SCAN_ENABLE_00_in),
  .DLL_SCAN_IN_00 (DLL_SCAN_IN_00_in),
  .DLL_SCAN_MODE_00 (DLL_SCAN_MODE_00_in),
  .DLL_SCAN_RST_N_00 (DLL_SCAN_RST_N_00_in),
  .HBM_REF_CLK (HBM_REF_CLK_in),
  .IO_SCAN_CK_00 (IO_SCAN_CK_00_in),
  .IO_SCAN_ENABLE_00 (IO_SCAN_ENABLE_00_in),
  .IO_SCAN_IN_00 (IO_SCAN_IN_00_in),
  .IO_SCAN_MODE_00 (IO_SCAN_MODE_00_in),
  .IO_SCAN_RST_N_00 (IO_SCAN_RST_N_00_in),
  .MBIST_EN_00 (MBIST_EN_00_in),
  .MBIST_EN_01 (MBIST_EN_01_in),
  .MBIST_EN_02 (MBIST_EN_02_in),
  .MBIST_EN_03 (MBIST_EN_03_in),
  .MBIST_EN_04 (MBIST_EN_04_in),
  .MBIST_EN_05 (MBIST_EN_05_in),
  .MBIST_EN_06 (MBIST_EN_06_in),
  .MBIST_EN_07 (MBIST_EN_07_in),
  .MC_SCAN_CK_00 (MC_SCAN_CK_00_in),
  .MC_SCAN_CK_01 (MC_SCAN_CK_01_in),
  .MC_SCAN_CK_02 (MC_SCAN_CK_02_in),
  .MC_SCAN_CK_03 (MC_SCAN_CK_03_in),
  .MC_SCAN_CK_04 (MC_SCAN_CK_04_in),
  .MC_SCAN_CK_05 (MC_SCAN_CK_05_in),
  .MC_SCAN_CK_06 (MC_SCAN_CK_06_in),
  .MC_SCAN_CK_07 (MC_SCAN_CK_07_in),
  .MC_SCAN_ENABLE_00 (MC_SCAN_ENABLE_00_in),
  .MC_SCAN_ENABLE_01 (MC_SCAN_ENABLE_01_in),
  .MC_SCAN_ENABLE_02 (MC_SCAN_ENABLE_02_in),
  .MC_SCAN_ENABLE_03 (MC_SCAN_ENABLE_03_in),
  .MC_SCAN_ENABLE_04 (MC_SCAN_ENABLE_04_in),
  .MC_SCAN_ENABLE_05 (MC_SCAN_ENABLE_05_in),
  .MC_SCAN_ENABLE_06 (MC_SCAN_ENABLE_06_in),
  .MC_SCAN_ENABLE_07 (MC_SCAN_ENABLE_07_in),
  .MC_SCAN_IN_00 (MC_SCAN_IN_00_in),
  .MC_SCAN_IN_01 (MC_SCAN_IN_01_in),
  .MC_SCAN_IN_02 (MC_SCAN_IN_02_in),
  .MC_SCAN_IN_03 (MC_SCAN_IN_03_in),
  .MC_SCAN_IN_04 (MC_SCAN_IN_04_in),
  .MC_SCAN_IN_05 (MC_SCAN_IN_05_in),
  .MC_SCAN_IN_06 (MC_SCAN_IN_06_in),
  .MC_SCAN_IN_07 (MC_SCAN_IN_07_in),
  .MC_SCAN_MODE_00 (MC_SCAN_MODE_00_in),
  .MC_SCAN_MODE_01 (MC_SCAN_MODE_01_in),
  .MC_SCAN_MODE_02 (MC_SCAN_MODE_02_in),
  .MC_SCAN_MODE_03 (MC_SCAN_MODE_03_in),
  .MC_SCAN_MODE_04 (MC_SCAN_MODE_04_in),
  .MC_SCAN_MODE_05 (MC_SCAN_MODE_05_in),
  .MC_SCAN_MODE_06 (MC_SCAN_MODE_06_in),
  .MC_SCAN_MODE_07 (MC_SCAN_MODE_07_in),
  .MC_SCAN_RST_N_00 (MC_SCAN_RST_N_00_in),
  .MC_SCAN_RST_N_01 (MC_SCAN_RST_N_01_in),
  .MC_SCAN_RST_N_02 (MC_SCAN_RST_N_02_in),
  .MC_SCAN_RST_N_03 (MC_SCAN_RST_N_03_in),
  .MC_SCAN_RST_N_04 (MC_SCAN_RST_N_04_in),
  .MC_SCAN_RST_N_05 (MC_SCAN_RST_N_05_in),
  .MC_SCAN_RST_N_06 (MC_SCAN_RST_N_06_in),
  .MC_SCAN_RST_N_07 (MC_SCAN_RST_N_07_in),
  .PHY_SCAN_CK_00 (PHY_SCAN_CK_00_in),
  .PHY_SCAN_ENABLE_00 (PHY_SCAN_ENABLE_00_in),
  .PHY_SCAN_IN_00 (PHY_SCAN_IN_00_in),
  .PHY_SCAN_MODE_00 (PHY_SCAN_MODE_00_in),
  .PHY_SCAN_RST_N_00 (PHY_SCAN_RST_N_00_in),
  .SW_SCAN_CK_00 (SW_SCAN_CK_00_in),
  .SW_SCAN_ENABLE_00 (SW_SCAN_ENABLE_00_in),
  .SW_SCAN_IN_00 (SW_SCAN_IN_00_in),
  .SW_SCAN_IN_01 (SW_SCAN_IN_01_in),
  .SW_SCAN_IN_02 (SW_SCAN_IN_02_in),
  .SW_SCAN_IN_03 (SW_SCAN_IN_03_in),
  .SW_SCAN_MODE_00 (SW_SCAN_MODE_00_in),
  .SW_SCAN_RST_N_00 (SW_SCAN_RST_N_00_in),
  .GSR (glblGSR)
);

endmodule

`endcelldefine
