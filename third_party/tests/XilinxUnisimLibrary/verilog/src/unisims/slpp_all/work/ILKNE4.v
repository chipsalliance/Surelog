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
//  /   /                        Interlaken MAC
// /___/   /\      Filename    : ILKNE4.v
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


module ILKNE4 #(



  parameter BYPASS = "FALSE",
  parameter [1:0] CTL_RX_BURSTMAX = 2'h3,
  parameter [1:0] CTL_RX_CHAN_EXT = 2'h0,
  parameter [3:0] CTL_RX_LAST_LANE = 4'hB,
  parameter [15:0] CTL_RX_MFRAMELEN_MINUS1 = 16'h07FF,
  parameter CTL_RX_PACKET_MODE = "FALSE",
  parameter [2:0] CTL_RX_RETRANS_MULT = 3'h0,
  parameter [3:0] CTL_RX_RETRANS_RETRY = 4'h2,
  parameter [15:0] CTL_RX_RETRANS_TIMER1 = 16'h0009,
  parameter [15:0] CTL_RX_RETRANS_TIMER2 = 16'h0000,
  parameter [11:0] CTL_RX_RETRANS_WDOG = 12'h000,
  parameter [7:0] CTL_RX_RETRANS_WRAP_TIMER = 8'h00,
  parameter CTL_TEST_MODE_PIN_CHAR = "FALSE",
  parameter [1:0] CTL_TX_BURSTMAX = 2'h3,
  parameter [2:0] CTL_TX_BURSTSHORT = 3'h1,
  parameter [1:0] CTL_TX_CHAN_EXT = 2'h0,
  parameter CTL_TX_DISABLE_SKIPWORD = "FALSE",
  parameter [3:0] CTL_TX_FC_CALLEN = 4'hF,
  parameter [3:0] CTL_TX_LAST_LANE = 4'hB,
  parameter [15:0] CTL_TX_MFRAMELEN_MINUS1 = 16'h07FF,
  parameter [13:0] CTL_TX_RETRANS_DEPTH = 14'h0800,
  parameter [2:0] CTL_TX_RETRANS_MULT = 3'h0,
  parameter [1:0] CTL_TX_RETRANS_RAM_BANKS = 2'h3,
  parameter MODE = "TRUE",
  parameter SIM_DEVICE = "ULTRASCALE_PLUS",
  parameter TEST_MODE_PIN_CHAR = "FALSE"
)(
  output [15:0] DRP_DO,
  output DRP_RDY,
  output [65:0] RX_BYPASS_DATAOUT00,
  output [65:0] RX_BYPASS_DATAOUT01,
  output [65:0] RX_BYPASS_DATAOUT02,
  output [65:0] RX_BYPASS_DATAOUT03,
  output [65:0] RX_BYPASS_DATAOUT04,
  output [65:0] RX_BYPASS_DATAOUT05,
  output [65:0] RX_BYPASS_DATAOUT06,
  output [65:0] RX_BYPASS_DATAOUT07,
  output [65:0] RX_BYPASS_DATAOUT08,
  output [65:0] RX_BYPASS_DATAOUT09,
  output [65:0] RX_BYPASS_DATAOUT10,
  output [65:0] RX_BYPASS_DATAOUT11,
  output [11:0] RX_BYPASS_ENAOUT,
  output [11:0] RX_BYPASS_IS_AVAILOUT,
  output [11:0] RX_BYPASS_IS_BADLYFRAMEDOUT,
  output [11:0] RX_BYPASS_IS_OVERFLOWOUT,
  output [11:0] RX_BYPASS_IS_SYNCEDOUT,
  output [11:0] RX_BYPASS_IS_SYNCWORDOUT,
  output [10:0] RX_CHANOUT0,
  output [10:0] RX_CHANOUT1,
  output [10:0] RX_CHANOUT2,
  output [10:0] RX_CHANOUT3,
  output [127:0] RX_DATAOUT0,
  output [127:0] RX_DATAOUT1,
  output [127:0] RX_DATAOUT2,
  output [127:0] RX_DATAOUT3,
  output RX_ENAOUT0,
  output RX_ENAOUT1,
  output RX_ENAOUT2,
  output RX_ENAOUT3,
  output RX_EOPOUT0,
  output RX_EOPOUT1,
  output RX_EOPOUT2,
  output RX_EOPOUT3,
  output RX_ERROUT0,
  output RX_ERROUT1,
  output RX_ERROUT2,
  output RX_ERROUT3,
  output [3:0] RX_MTYOUT0,
  output [3:0] RX_MTYOUT1,
  output [3:0] RX_MTYOUT2,
  output [3:0] RX_MTYOUT3,
  output RX_OVFOUT,
  output RX_SOPOUT0,
  output RX_SOPOUT1,
  output RX_SOPOUT2,
  output RX_SOPOUT3,
  output STAT_RX_ALIGNED,
  output STAT_RX_ALIGNED_ERR,
  output [11:0] STAT_RX_BAD_TYPE_ERR,
  output STAT_RX_BURSTMAX_ERR,
  output STAT_RX_BURST_ERR,
  output STAT_RX_CRC24_ERR,
  output [11:0] STAT_RX_CRC32_ERR,
  output [11:0] STAT_RX_CRC32_VALID,
  output [11:0] STAT_RX_DESCRAM_ERR,
  output [11:0] STAT_RX_DIAGWORD_INTFSTAT,
  output [11:0] STAT_RX_DIAGWORD_LANESTAT,
  output [255:0] STAT_RX_FC_STAT,
  output [11:0] STAT_RX_FRAMING_ERR,
  output STAT_RX_MEOP_ERR,
  output [11:0] STAT_RX_MF_ERR,
  output [11:0] STAT_RX_MF_LEN_ERR,
  output [11:0] STAT_RX_MF_REPEAT_ERR,
  output STAT_RX_MISALIGNED,
  output STAT_RX_MSOP_ERR,
  output [7:0] STAT_RX_MUBITS,
  output STAT_RX_MUBITS_UPDATED,
  output STAT_RX_OVERFLOW_ERR,
  output STAT_RX_RETRANS_CRC24_ERR,
  output STAT_RX_RETRANS_DISC,
  output [15:0] STAT_RX_RETRANS_LATENCY,
  output STAT_RX_RETRANS_REQ,
  output STAT_RX_RETRANS_RETRY_ERR,
  output [7:0] STAT_RX_RETRANS_SEQ,
  output STAT_RX_RETRANS_SEQ_UPDATED,
  output [2:0] STAT_RX_RETRANS_STATE,
  output [4:0] STAT_RX_RETRANS_SUBSEQ,
  output STAT_RX_RETRANS_WDOG_ERR,
  output STAT_RX_RETRANS_WRAP_ERR,
  output [11:0] STAT_RX_SYNCED,
  output [11:0] STAT_RX_SYNCED_ERR,
  output [11:0] STAT_RX_WORD_SYNC,
  output STAT_TX_BURST_ERR,
  output STAT_TX_ERRINJ_BITERR_DONE,
  output STAT_TX_OVERFLOW_ERR,
  output STAT_TX_RETRANS_BURST_ERR,
  output STAT_TX_RETRANS_BUSY,
  output STAT_TX_RETRANS_RAM_PERROUT,
  output [8:0] STAT_TX_RETRANS_RAM_RADDR,
  output STAT_TX_RETRANS_RAM_RD_B0,
  output STAT_TX_RETRANS_RAM_RD_B1,
  output STAT_TX_RETRANS_RAM_RD_B2,
  output STAT_TX_RETRANS_RAM_RD_B3,
  output [1:0] STAT_TX_RETRANS_RAM_RSEL,
  output [8:0] STAT_TX_RETRANS_RAM_WADDR,
  output [643:0] STAT_TX_RETRANS_RAM_WDATA,
  output STAT_TX_RETRANS_RAM_WE_B0,
  output STAT_TX_RETRANS_RAM_WE_B1,
  output STAT_TX_RETRANS_RAM_WE_B2,
  output STAT_TX_RETRANS_RAM_WE_B3,
  output STAT_TX_UNDERFLOW_ERR,
  output TX_OVFOUT,
  output TX_RDYOUT,
  output [63:0] TX_SERDES_DATA00,
  output [63:0] TX_SERDES_DATA01,
  output [63:0] TX_SERDES_DATA02,
  output [63:0] TX_SERDES_DATA03,
  output [63:0] TX_SERDES_DATA04,
  output [63:0] TX_SERDES_DATA05,
  output [63:0] TX_SERDES_DATA06,
  output [63:0] TX_SERDES_DATA07,
  output [63:0] TX_SERDES_DATA08,
  output [63:0] TX_SERDES_DATA09,
  output [63:0] TX_SERDES_DATA10,
  output [63:0] TX_SERDES_DATA11,

  input CORE_CLK,
  input CTL_RX_FORCE_RESYNC,
  input CTL_RX_RETRANS_ACK,
  input CTL_RX_RETRANS_ENABLE,
  input CTL_RX_RETRANS_ERRIN,
  input CTL_RX_RETRANS_FORCE_REQ,
  input CTL_RX_RETRANS_RESET,
  input CTL_RX_RETRANS_RESET_MODE,
  input CTL_TX_DIAGWORD_INTFSTAT,
  input [11:0] CTL_TX_DIAGWORD_LANESTAT,
  input CTL_TX_ENABLE,
  input CTL_TX_ERRINJ_BITERR_GO,
  input [3:0] CTL_TX_ERRINJ_BITERR_LANE,
  input [255:0] CTL_TX_FC_STAT,
  input [7:0] CTL_TX_MUBITS,
  input CTL_TX_RETRANS_ENABLE,
  input CTL_TX_RETRANS_RAM_PERRIN,
  input [643:0] CTL_TX_RETRANS_RAM_RDATA,
  input CTL_TX_RETRANS_REQ,
  input CTL_TX_RETRANS_REQ_VALID,
  input [11:0] CTL_TX_RLIM_DELTA,
  input CTL_TX_RLIM_ENABLE,
  input [7:0] CTL_TX_RLIM_INTV,
  input [11:0] CTL_TX_RLIM_MAX,
  input [9:0] DRP_ADDR,
  input DRP_CLK,
  input [15:0] DRP_DI,
  input DRP_EN,
  input DRP_WE,
  input LBUS_CLK,
  input RX_BYPASS_FORCE_REALIGNIN,
  input RX_BYPASS_RDIN,
  input RX_RESET,
  input [11:0] RX_SERDES_CLK,
  input [63:0] RX_SERDES_DATA00,
  input [63:0] RX_SERDES_DATA01,
  input [63:0] RX_SERDES_DATA02,
  input [63:0] RX_SERDES_DATA03,
  input [63:0] RX_SERDES_DATA04,
  input [63:0] RX_SERDES_DATA05,
  input [63:0] RX_SERDES_DATA06,
  input [63:0] RX_SERDES_DATA07,
  input [63:0] RX_SERDES_DATA08,
  input [63:0] RX_SERDES_DATA09,
  input [63:0] RX_SERDES_DATA10,
  input [63:0] RX_SERDES_DATA11,
  input [11:0] RX_SERDES_RESET,
  input TX_BCTLIN0,
  input TX_BCTLIN1,
  input TX_BCTLIN2,
  input TX_BCTLIN3,
  input [11:0] TX_BYPASS_CTRLIN,
  input [63:0] TX_BYPASS_DATAIN00,
  input [63:0] TX_BYPASS_DATAIN01,
  input [63:0] TX_BYPASS_DATAIN02,
  input [63:0] TX_BYPASS_DATAIN03,
  input [63:0] TX_BYPASS_DATAIN04,
  input [63:0] TX_BYPASS_DATAIN05,
  input [63:0] TX_BYPASS_DATAIN06,
  input [63:0] TX_BYPASS_DATAIN07,
  input [63:0] TX_BYPASS_DATAIN08,
  input [63:0] TX_BYPASS_DATAIN09,
  input [63:0] TX_BYPASS_DATAIN10,
  input [63:0] TX_BYPASS_DATAIN11,
  input TX_BYPASS_ENAIN,
  input [7:0] TX_BYPASS_GEARBOX_SEQIN,
  input [3:0] TX_BYPASS_MFRAMER_STATEIN,
  input [10:0] TX_CHANIN0,
  input [10:0] TX_CHANIN1,
  input [10:0] TX_CHANIN2,
  input [10:0] TX_CHANIN3,
  input [127:0] TX_DATAIN0,
  input [127:0] TX_DATAIN1,
  input [127:0] TX_DATAIN2,
  input [127:0] TX_DATAIN3,
  input TX_ENAIN0,
  input TX_ENAIN1,
  input TX_ENAIN2,
  input TX_ENAIN3,
  input TX_EOPIN0,
  input TX_EOPIN1,
  input TX_EOPIN2,
  input TX_EOPIN3,
  input TX_ERRIN0,
  input TX_ERRIN1,
  input TX_ERRIN2,
  input TX_ERRIN3,
  input [3:0] TX_MTYIN0,
  input [3:0] TX_MTYIN1,
  input [3:0] TX_MTYIN2,
  input [3:0] TX_MTYIN3,
  input TX_RESET,
  input TX_SERDES_REFCLK,
  input TX_SERDES_REFCLK_RESET,
  input TX_SOPIN0,
  input TX_SOPIN1,
  input TX_SOPIN2,
  input TX_SOPIN3
);

// define constants
  localparam MODULE_NAME = "ILKNE4";
  
  reg trig_attr;
// include dynamic registers - XILINX test only



  reg [40:1] BYPASS_REG = BYPASS;
  reg [1:0] CTL_RX_BURSTMAX_REG = CTL_RX_BURSTMAX;
  reg [1:0] CTL_RX_CHAN_EXT_REG = CTL_RX_CHAN_EXT;
  reg [3:0] CTL_RX_LAST_LANE_REG = CTL_RX_LAST_LANE;
  reg [15:0] CTL_RX_MFRAMELEN_MINUS1_REG = CTL_RX_MFRAMELEN_MINUS1;
  reg [40:1] CTL_RX_PACKET_MODE_REG = CTL_RX_PACKET_MODE;
  reg [2:0] CTL_RX_RETRANS_MULT_REG = CTL_RX_RETRANS_MULT;
  reg [3:0] CTL_RX_RETRANS_RETRY_REG = CTL_RX_RETRANS_RETRY;
  reg [15:0] CTL_RX_RETRANS_TIMER1_REG = CTL_RX_RETRANS_TIMER1;
  reg [15:0] CTL_RX_RETRANS_TIMER2_REG = CTL_RX_RETRANS_TIMER2;
  reg [11:0] CTL_RX_RETRANS_WDOG_REG = CTL_RX_RETRANS_WDOG;
  reg [7:0] CTL_RX_RETRANS_WRAP_TIMER_REG = CTL_RX_RETRANS_WRAP_TIMER;
  reg [40:1] CTL_TEST_MODE_PIN_CHAR_REG = CTL_TEST_MODE_PIN_CHAR;
  reg [1:0] CTL_TX_BURSTMAX_REG = CTL_TX_BURSTMAX;
  reg [2:0] CTL_TX_BURSTSHORT_REG = CTL_TX_BURSTSHORT;
  reg [1:0] CTL_TX_CHAN_EXT_REG = CTL_TX_CHAN_EXT;
  reg [40:1] CTL_TX_DISABLE_SKIPWORD_REG = CTL_TX_DISABLE_SKIPWORD;
  reg [3:0] CTL_TX_FC_CALLEN_REG = CTL_TX_FC_CALLEN;
  reg [3:0] CTL_TX_LAST_LANE_REG = CTL_TX_LAST_LANE;
  reg [15:0] CTL_TX_MFRAMELEN_MINUS1_REG = CTL_TX_MFRAMELEN_MINUS1;
  reg [13:0] CTL_TX_RETRANS_DEPTH_REG = CTL_TX_RETRANS_DEPTH;
  reg [2:0] CTL_TX_RETRANS_MULT_REG = CTL_TX_RETRANS_MULT;
  reg [1:0] CTL_TX_RETRANS_RAM_BANKS_REG = CTL_TX_RETRANS_RAM_BANKS;
  reg [40:1] MODE_REG = MODE;
  reg [152:1] SIM_DEVICE_REG = SIM_DEVICE;
  reg [40:1] TEST_MODE_PIN_CHAR_REG = TEST_MODE_PIN_CHAR;


  reg [40:1] CTL_CSSD_EN_REG = "FALSE";
  reg [15:0] CTL_CSSD_MRKR_INIT_REG = 16'h0000;
  reg [14:0] CTL_CSSD_ROOT_CLK_DIS_REG = 15'h0000;
  reg [3:0] CTL_CSSD_ROOT_CLK_SEL_REG = 4'h0;
  reg [40:1] CTL_CSSD_SNGL_CHAIN_MD_REG = "FALSE";
  reg [15:0] CTL_CSSD_STOP_COUNT_0_REG = 16'h0FFF;
  reg [15:0] CTL_CSSD_STOP_COUNT_1_REG = 16'h0000;
  reg [15:0] CTL_CSSD_STOP_COUNT_2_REG = 16'h0000;




tri0 glblGSR = glbl.GSR;


  wire CFG_RESET_CSSD_out;
  wire CSSD_CLK_STOP_DONE_out;
  wire DRP_RDY_out;
  wire GRESTORE_CSSD_out;
  wire GWE_CSSD_out;
  wire RX_ENAOUT0_out;
  wire RX_ENAOUT1_out;
  wire RX_ENAOUT2_out;
  wire RX_ENAOUT3_out;
  wire RX_EOPOUT0_out;
  wire RX_EOPOUT1_out;
  wire RX_EOPOUT2_out;
  wire RX_EOPOUT3_out;
  wire RX_ERROUT0_out;
  wire RX_ERROUT1_out;
  wire RX_ERROUT2_out;
  wire RX_ERROUT3_out;
  wire RX_OVFOUT_out;
  wire RX_SOPOUT0_out;
  wire RX_SOPOUT1_out;
  wire RX_SOPOUT2_out;
  wire RX_SOPOUT3_out;
  wire STAT_RX_ALIGNED_ERR_out;
  wire STAT_RX_ALIGNED_out;
  wire STAT_RX_BURSTMAX_ERR_out;
  wire STAT_RX_BURST_ERR_out;
  wire STAT_RX_CRC24_ERR_out;
  wire STAT_RX_MEOP_ERR_out;
  wire STAT_RX_MISALIGNED_out;
  wire STAT_RX_MSOP_ERR_out;
  wire STAT_RX_MUBITS_UPDATED_out;
  wire STAT_RX_OVERFLOW_ERR_out;
  wire STAT_RX_RETRANS_CRC24_ERR_out;
  wire STAT_RX_RETRANS_DISC_out;
  wire STAT_RX_RETRANS_REQ_out;
  wire STAT_RX_RETRANS_RETRY_ERR_out;
  wire STAT_RX_RETRANS_SEQ_UPDATED_out;
  wire STAT_RX_RETRANS_WDOG_ERR_out;
  wire STAT_RX_RETRANS_WRAP_ERR_out;
  wire STAT_TX_BURST_ERR_out;
  wire STAT_TX_ERRINJ_BITERR_DONE_out;
  wire STAT_TX_OVERFLOW_ERR_out;
  wire STAT_TX_RETRANS_BURST_ERR_out;
  wire STAT_TX_RETRANS_BUSY_out;
  wire STAT_TX_RETRANS_RAM_PERROUT_out;
  wire STAT_TX_RETRANS_RAM_RD_B0_out;
  wire STAT_TX_RETRANS_RAM_RD_B1_out;
  wire STAT_TX_RETRANS_RAM_RD_B2_out;
  wire STAT_TX_RETRANS_RAM_RD_B3_out;
  wire STAT_TX_RETRANS_RAM_WE_B0_out;
  wire STAT_TX_RETRANS_RAM_WE_B1_out;
  wire STAT_TX_RETRANS_RAM_WE_B2_out;
  wire STAT_TX_RETRANS_RAM_WE_B3_out;
  wire STAT_TX_UNDERFLOW_ERR_out;
  wire TX_OVFOUT_out;
  wire TX_RDYOUT_out;
  wire [10:0] RX_CHANOUT0_out;
  wire [10:0] RX_CHANOUT1_out;
  wire [10:0] RX_CHANOUT2_out;
  wire [10:0] RX_CHANOUT3_out;
  wire [11:0] RX_BYPASS_ENAOUT_out;
  wire [11:0] RX_BYPASS_IS_AVAILOUT_out;
  wire [11:0] RX_BYPASS_IS_BADLYFRAMEDOUT_out;
  wire [11:0] RX_BYPASS_IS_OVERFLOWOUT_out;
  wire [11:0] RX_BYPASS_IS_SYNCEDOUT_out;
  wire [11:0] RX_BYPASS_IS_SYNCWORDOUT_out;
  wire [11:0] STAT_RX_BAD_TYPE_ERR_out;
  wire [11:0] STAT_RX_CRC32_ERR_out;
  wire [11:0] STAT_RX_CRC32_VALID_out;
  wire [11:0] STAT_RX_DESCRAM_ERR_out;
  wire [11:0] STAT_RX_DIAGWORD_INTFSTAT_out;
  wire [11:0] STAT_RX_DIAGWORD_LANESTAT_out;
  wire [11:0] STAT_RX_FRAMING_ERR_out;
  wire [11:0] STAT_RX_MF_ERR_out;
  wire [11:0] STAT_RX_MF_LEN_ERR_out;
  wire [11:0] STAT_RX_MF_REPEAT_ERR_out;
  wire [11:0] STAT_RX_SYNCED_ERR_out;
  wire [11:0] STAT_RX_SYNCED_out;
  wire [11:0] STAT_RX_WORD_SYNC_out;
  wire [127:0] RX_DATAOUT0_out;
  wire [127:0] RX_DATAOUT1_out;
  wire [127:0] RX_DATAOUT2_out;
  wire [127:0] RX_DATAOUT3_out;
  wire [15:0] DRP_DO_out;
  wire [15:0] STAT_RX_RETRANS_LATENCY_out;
  wire [1:0] STAT_TX_RETRANS_RAM_RSEL_out;
  wire [255:0] STAT_RX_FC_STAT_out;
  wire [264:0] SCAN_OUT_out;
  wire [2:0] STAT_RX_RETRANS_STATE_out;
  wire [3:0] RX_MTYOUT0_out;
  wire [3:0] RX_MTYOUT1_out;
  wire [3:0] RX_MTYOUT2_out;
  wire [3:0] RX_MTYOUT3_out;
  wire [4:0] STAT_RX_RETRANS_SUBSEQ_out;
  wire [63:0] TX_SERDES_DATA00_out;
  wire [63:0] TX_SERDES_DATA01_out;
  wire [63:0] TX_SERDES_DATA02_out;
  wire [63:0] TX_SERDES_DATA03_out;
  wire [63:0] TX_SERDES_DATA04_out;
  wire [63:0] TX_SERDES_DATA05_out;
  wire [63:0] TX_SERDES_DATA06_out;
  wire [63:0] TX_SERDES_DATA07_out;
  wire [63:0] TX_SERDES_DATA08_out;
  wire [63:0] TX_SERDES_DATA09_out;
  wire [63:0] TX_SERDES_DATA10_out;
  wire [63:0] TX_SERDES_DATA11_out;
  wire [643:0] STAT_TX_RETRANS_RAM_WDATA_out;
  wire [65:0] RX_BYPASS_DATAOUT00_out;
  wire [65:0] RX_BYPASS_DATAOUT01_out;
  wire [65:0] RX_BYPASS_DATAOUT02_out;
  wire [65:0] RX_BYPASS_DATAOUT03_out;
  wire [65:0] RX_BYPASS_DATAOUT04_out;
  wire [65:0] RX_BYPASS_DATAOUT05_out;
  wire [65:0] RX_BYPASS_DATAOUT06_out;
  wire [65:0] RX_BYPASS_DATAOUT07_out;
  wire [65:0] RX_BYPASS_DATAOUT08_out;
  wire [65:0] RX_BYPASS_DATAOUT09_out;
  wire [65:0] RX_BYPASS_DATAOUT10_out;
  wire [65:0] RX_BYPASS_DATAOUT11_out;
  wire [7:0] STAT_RX_MUBITS_out;
  wire [7:0] STAT_RX_RETRANS_SEQ_out;
  wire [8:0] STAT_TX_RETRANS_RAM_RADDR_out;
  wire [8:0] STAT_TX_RETRANS_RAM_WADDR_out;

  wire CORE_CLK_in;
  wire CSSD_CLK_STOP_EVENT_in;
  wire CSSD_RESETN_in;
  wire CTL_RX_FORCE_RESYNC_in;
  wire CTL_RX_RETRANS_ACK_in;
  wire CTL_RX_RETRANS_ENABLE_in;
  wire CTL_RX_RETRANS_ERRIN_in;
  wire CTL_RX_RETRANS_FORCE_REQ_in;
  wire CTL_RX_RETRANS_RESET_MODE_in;
  wire CTL_RX_RETRANS_RESET_in;
  wire CTL_TX_DIAGWORD_INTFSTAT_in;
  wire CTL_TX_ENABLE_in;
  wire CTL_TX_ERRINJ_BITERR_GO_in;
  wire CTL_TX_RETRANS_ENABLE_in;
  wire CTL_TX_RETRANS_RAM_PERRIN_in;
  wire CTL_TX_RETRANS_REQ_VALID_in;
  wire CTL_TX_RETRANS_REQ_in;
  wire CTL_TX_RLIM_ENABLE_in;
  wire DRP_CLK_in;
  wire DRP_EN_in;
  wire DRP_WE_in;
  wire LBUS_CLK_in;
  wire RX_BYPASS_FORCE_REALIGNIN_in;
  wire RX_BYPASS_RDIN_in;
  wire RX_RESET_in;
  wire SCAN_CLK_in;
  wire SCAN_EN_N_in;
  wire TEST_MODE_N_in;
  wire TEST_RESET_in;
  wire TX_BCTLIN0_in;
  wire TX_BCTLIN1_in;
  wire TX_BCTLIN2_in;
  wire TX_BCTLIN3_in;
  wire TX_BYPASS_ENAIN_in;
  wire TX_ENAIN0_in;
  wire TX_ENAIN1_in;
  wire TX_ENAIN2_in;
  wire TX_ENAIN3_in;
  wire TX_EOPIN0_in;
  wire TX_EOPIN1_in;
  wire TX_EOPIN2_in;
  wire TX_EOPIN3_in;
  wire TX_ERRIN0_in;
  wire TX_ERRIN1_in;
  wire TX_ERRIN2_in;
  wire TX_ERRIN3_in;
  wire TX_RESET_in;
  wire TX_SERDES_REFCLK_RESET_in;
  wire TX_SERDES_REFCLK_in;
  wire TX_SOPIN0_in;
  wire TX_SOPIN1_in;
  wire TX_SOPIN2_in;
  wire TX_SOPIN3_in;
  wire [10:0] TX_CHANIN0_in;
  wire [10:0] TX_CHANIN1_in;
  wire [10:0] TX_CHANIN2_in;
  wire [10:0] TX_CHANIN3_in;
  wire [11:0] CTL_TX_DIAGWORD_LANESTAT_in;
  wire [11:0] CTL_TX_RLIM_DELTA_in;
  wire [11:0] CTL_TX_RLIM_MAX_in;
  wire [11:0] RX_SERDES_CLK_in;
  wire [11:0] RX_SERDES_RESET_in;
  wire [11:0] TX_BYPASS_CTRLIN_in;
  wire [127:0] TX_DATAIN0_in;
  wire [127:0] TX_DATAIN1_in;
  wire [127:0] TX_DATAIN2_in;
  wire [127:0] TX_DATAIN3_in;
  wire [15:0] DRP_DI_in;
  wire [255:0] CTL_TX_FC_STAT_in;
  wire [264:0] SCAN_IN_in;
  wire [3:0] CTL_TX_ERRINJ_BITERR_LANE_in;
  wire [3:0] TX_BYPASS_MFRAMER_STATEIN_in;
  wire [3:0] TX_MTYIN0_in;
  wire [3:0] TX_MTYIN1_in;
  wire [3:0] TX_MTYIN2_in;
  wire [3:0] TX_MTYIN3_in;
  wire [63:0] RX_SERDES_DATA00_in;
  wire [63:0] RX_SERDES_DATA01_in;
  wire [63:0] RX_SERDES_DATA02_in;
  wire [63:0] RX_SERDES_DATA03_in;
  wire [63:0] RX_SERDES_DATA04_in;
  wire [63:0] RX_SERDES_DATA05_in;
  wire [63:0] RX_SERDES_DATA06_in;
  wire [63:0] RX_SERDES_DATA07_in;
  wire [63:0] RX_SERDES_DATA08_in;
  wire [63:0] RX_SERDES_DATA09_in;
  wire [63:0] RX_SERDES_DATA10_in;
  wire [63:0] RX_SERDES_DATA11_in;
  wire [63:0] TX_BYPASS_DATAIN00_in;
  wire [63:0] TX_BYPASS_DATAIN01_in;
  wire [63:0] TX_BYPASS_DATAIN02_in;
  wire [63:0] TX_BYPASS_DATAIN03_in;
  wire [63:0] TX_BYPASS_DATAIN04_in;
  wire [63:0] TX_BYPASS_DATAIN05_in;
  wire [63:0] TX_BYPASS_DATAIN06_in;
  wire [63:0] TX_BYPASS_DATAIN07_in;
  wire [63:0] TX_BYPASS_DATAIN08_in;
  wire [63:0] TX_BYPASS_DATAIN09_in;
  wire [63:0] TX_BYPASS_DATAIN10_in;
  wire [63:0] TX_BYPASS_DATAIN11_in;
  wire [643:0] CTL_TX_RETRANS_RAM_RDATA_in;
  wire [7:0] CTL_TX_MUBITS_in;
  wire [7:0] CTL_TX_RLIM_INTV_in;
  wire [7:0] TX_BYPASS_GEARBOX_SEQIN_in;
  wire [9:0] DRP_ADDR_in;






































































































  assign DRP_DO = DRP_DO_out;
  assign DRP_RDY = DRP_RDY_out;
  assign RX_BYPASS_DATAOUT00 = RX_BYPASS_DATAOUT00_out;
  assign RX_BYPASS_DATAOUT01 = RX_BYPASS_DATAOUT01_out;
  assign RX_BYPASS_DATAOUT02 = RX_BYPASS_DATAOUT02_out;
  assign RX_BYPASS_DATAOUT03 = RX_BYPASS_DATAOUT03_out;
  assign RX_BYPASS_DATAOUT04 = RX_BYPASS_DATAOUT04_out;
  assign RX_BYPASS_DATAOUT05 = RX_BYPASS_DATAOUT05_out;
  assign RX_BYPASS_DATAOUT06 = RX_BYPASS_DATAOUT06_out;
  assign RX_BYPASS_DATAOUT07 = RX_BYPASS_DATAOUT07_out;
  assign RX_BYPASS_DATAOUT08 = RX_BYPASS_DATAOUT08_out;
  assign RX_BYPASS_DATAOUT09 = RX_BYPASS_DATAOUT09_out;
  assign RX_BYPASS_DATAOUT10 = RX_BYPASS_DATAOUT10_out;
  assign RX_BYPASS_DATAOUT11 = RX_BYPASS_DATAOUT11_out;
  assign RX_BYPASS_ENAOUT = RX_BYPASS_ENAOUT_out;
  assign RX_BYPASS_IS_AVAILOUT = RX_BYPASS_IS_AVAILOUT_out;
  assign RX_BYPASS_IS_BADLYFRAMEDOUT = RX_BYPASS_IS_BADLYFRAMEDOUT_out;
  assign RX_BYPASS_IS_OVERFLOWOUT = RX_BYPASS_IS_OVERFLOWOUT_out;
  assign RX_BYPASS_IS_SYNCEDOUT = RX_BYPASS_IS_SYNCEDOUT_out;
  assign RX_BYPASS_IS_SYNCWORDOUT = RX_BYPASS_IS_SYNCWORDOUT_out;
  assign RX_CHANOUT0 = RX_CHANOUT0_out;
  assign RX_CHANOUT1 = RX_CHANOUT1_out;
  assign RX_CHANOUT2 = RX_CHANOUT2_out;
  assign RX_CHANOUT3 = RX_CHANOUT3_out;
  assign RX_DATAOUT0 = RX_DATAOUT0_out;
  assign RX_DATAOUT1 = RX_DATAOUT1_out;
  assign RX_DATAOUT2 = RX_DATAOUT2_out;
  assign RX_DATAOUT3 = RX_DATAOUT3_out;
  assign RX_ENAOUT0 = RX_ENAOUT0_out;
  assign RX_ENAOUT1 = RX_ENAOUT1_out;
  assign RX_ENAOUT2 = RX_ENAOUT2_out;
  assign RX_ENAOUT3 = RX_ENAOUT3_out;
  assign RX_EOPOUT0 = RX_EOPOUT0_out;
  assign RX_EOPOUT1 = RX_EOPOUT1_out;
  assign RX_EOPOUT2 = RX_EOPOUT2_out;
  assign RX_EOPOUT3 = RX_EOPOUT3_out;
  assign RX_ERROUT0 = RX_ERROUT0_out;
  assign RX_ERROUT1 = RX_ERROUT1_out;
  assign RX_ERROUT2 = RX_ERROUT2_out;
  assign RX_ERROUT3 = RX_ERROUT3_out;
  assign RX_MTYOUT0 = RX_MTYOUT0_out;
  assign RX_MTYOUT1 = RX_MTYOUT1_out;
  assign RX_MTYOUT2 = RX_MTYOUT2_out;
  assign RX_MTYOUT3 = RX_MTYOUT3_out;
  assign RX_OVFOUT = RX_OVFOUT_out;
  assign RX_SOPOUT0 = RX_SOPOUT0_out;
  assign RX_SOPOUT1 = RX_SOPOUT1_out;
  assign RX_SOPOUT2 = RX_SOPOUT2_out;
  assign RX_SOPOUT3 = RX_SOPOUT3_out;
  assign STAT_RX_ALIGNED = STAT_RX_ALIGNED_out;
  assign STAT_RX_ALIGNED_ERR = STAT_RX_ALIGNED_ERR_out;
  assign STAT_RX_BAD_TYPE_ERR = STAT_RX_BAD_TYPE_ERR_out;
  assign STAT_RX_BURSTMAX_ERR = STAT_RX_BURSTMAX_ERR_out;
  assign STAT_RX_BURST_ERR = STAT_RX_BURST_ERR_out;
  assign STAT_RX_CRC24_ERR = STAT_RX_CRC24_ERR_out;
  assign STAT_RX_CRC32_ERR = STAT_RX_CRC32_ERR_out;
  assign STAT_RX_CRC32_VALID = STAT_RX_CRC32_VALID_out;
  assign STAT_RX_DESCRAM_ERR = STAT_RX_DESCRAM_ERR_out;
  assign STAT_RX_DIAGWORD_INTFSTAT = STAT_RX_DIAGWORD_INTFSTAT_out;
  assign STAT_RX_DIAGWORD_LANESTAT = STAT_RX_DIAGWORD_LANESTAT_out;
  assign STAT_RX_FC_STAT = STAT_RX_FC_STAT_out;
  assign STAT_RX_FRAMING_ERR = STAT_RX_FRAMING_ERR_out;
  assign STAT_RX_MEOP_ERR = STAT_RX_MEOP_ERR_out;
  assign STAT_RX_MF_ERR = STAT_RX_MF_ERR_out;
  assign STAT_RX_MF_LEN_ERR = STAT_RX_MF_LEN_ERR_out;
  assign STAT_RX_MF_REPEAT_ERR = STAT_RX_MF_REPEAT_ERR_out;
  assign STAT_RX_MISALIGNED = STAT_RX_MISALIGNED_out;
  assign STAT_RX_MSOP_ERR = STAT_RX_MSOP_ERR_out;
  assign STAT_RX_MUBITS = STAT_RX_MUBITS_out;
  assign STAT_RX_MUBITS_UPDATED = STAT_RX_MUBITS_UPDATED_out;
  assign STAT_RX_OVERFLOW_ERR = STAT_RX_OVERFLOW_ERR_out;
  assign STAT_RX_RETRANS_CRC24_ERR = STAT_RX_RETRANS_CRC24_ERR_out;
  assign STAT_RX_RETRANS_DISC = STAT_RX_RETRANS_DISC_out;
  assign STAT_RX_RETRANS_LATENCY = STAT_RX_RETRANS_LATENCY_out;
  assign STAT_RX_RETRANS_REQ = STAT_RX_RETRANS_REQ_out;
  assign STAT_RX_RETRANS_RETRY_ERR = STAT_RX_RETRANS_RETRY_ERR_out;
  assign STAT_RX_RETRANS_SEQ = STAT_RX_RETRANS_SEQ_out;
  assign STAT_RX_RETRANS_SEQ_UPDATED = STAT_RX_RETRANS_SEQ_UPDATED_out;
  assign STAT_RX_RETRANS_STATE = STAT_RX_RETRANS_STATE_out;
  assign STAT_RX_RETRANS_SUBSEQ = STAT_RX_RETRANS_SUBSEQ_out;
  assign STAT_RX_RETRANS_WDOG_ERR = STAT_RX_RETRANS_WDOG_ERR_out;
  assign STAT_RX_RETRANS_WRAP_ERR = STAT_RX_RETRANS_WRAP_ERR_out;
  assign STAT_RX_SYNCED = STAT_RX_SYNCED_out;
  assign STAT_RX_SYNCED_ERR = STAT_RX_SYNCED_ERR_out;
  assign STAT_RX_WORD_SYNC = STAT_RX_WORD_SYNC_out;
  assign STAT_TX_BURST_ERR = STAT_TX_BURST_ERR_out;
  assign STAT_TX_ERRINJ_BITERR_DONE = STAT_TX_ERRINJ_BITERR_DONE_out;
  assign STAT_TX_OVERFLOW_ERR = STAT_TX_OVERFLOW_ERR_out;
  assign STAT_TX_RETRANS_BURST_ERR = STAT_TX_RETRANS_BURST_ERR_out;
  assign STAT_TX_RETRANS_BUSY = STAT_TX_RETRANS_BUSY_out;
  assign STAT_TX_RETRANS_RAM_PERROUT = STAT_TX_RETRANS_RAM_PERROUT_out;
  assign STAT_TX_RETRANS_RAM_RADDR = STAT_TX_RETRANS_RAM_RADDR_out;
  assign STAT_TX_RETRANS_RAM_RD_B0 = STAT_TX_RETRANS_RAM_RD_B0_out;
  assign STAT_TX_RETRANS_RAM_RD_B1 = STAT_TX_RETRANS_RAM_RD_B1_out;
  assign STAT_TX_RETRANS_RAM_RD_B2 = STAT_TX_RETRANS_RAM_RD_B2_out;
  assign STAT_TX_RETRANS_RAM_RD_B3 = STAT_TX_RETRANS_RAM_RD_B3_out;
  assign STAT_TX_RETRANS_RAM_RSEL = STAT_TX_RETRANS_RAM_RSEL_out;
  assign STAT_TX_RETRANS_RAM_WADDR = STAT_TX_RETRANS_RAM_WADDR_out;
  assign STAT_TX_RETRANS_RAM_WDATA = STAT_TX_RETRANS_RAM_WDATA_out;
  assign STAT_TX_RETRANS_RAM_WE_B0 = STAT_TX_RETRANS_RAM_WE_B0_out;
  assign STAT_TX_RETRANS_RAM_WE_B1 = STAT_TX_RETRANS_RAM_WE_B1_out;
  assign STAT_TX_RETRANS_RAM_WE_B2 = STAT_TX_RETRANS_RAM_WE_B2_out;
  assign STAT_TX_RETRANS_RAM_WE_B3 = STAT_TX_RETRANS_RAM_WE_B3_out;
  assign STAT_TX_UNDERFLOW_ERR = STAT_TX_UNDERFLOW_ERR_out;
  assign TX_OVFOUT = TX_OVFOUT_out;
  assign TX_RDYOUT = TX_RDYOUT_out;
  assign TX_SERDES_DATA00 = TX_SERDES_DATA00_out;
  assign TX_SERDES_DATA01 = TX_SERDES_DATA01_out;
  assign TX_SERDES_DATA02 = TX_SERDES_DATA02_out;
  assign TX_SERDES_DATA03 = TX_SERDES_DATA03_out;
  assign TX_SERDES_DATA04 = TX_SERDES_DATA04_out;
  assign TX_SERDES_DATA05 = TX_SERDES_DATA05_out;
  assign TX_SERDES_DATA06 = TX_SERDES_DATA06_out;
  assign TX_SERDES_DATA07 = TX_SERDES_DATA07_out;
  assign TX_SERDES_DATA08 = TX_SERDES_DATA08_out;
  assign TX_SERDES_DATA09 = TX_SERDES_DATA09_out;
  assign TX_SERDES_DATA10 = TX_SERDES_DATA10_out;
  assign TX_SERDES_DATA11 = TX_SERDES_DATA11_out;
















































































































  assign CORE_CLK_in = CORE_CLK;
  assign CTL_RX_FORCE_RESYNC_in = CTL_RX_FORCE_RESYNC;
  assign CTL_RX_RETRANS_ACK_in = CTL_RX_RETRANS_ACK;
  assign CTL_RX_RETRANS_ENABLE_in = CTL_RX_RETRANS_ENABLE;
  assign CTL_RX_RETRANS_ERRIN_in = CTL_RX_RETRANS_ERRIN;
  assign CTL_RX_RETRANS_FORCE_REQ_in = CTL_RX_RETRANS_FORCE_REQ;
  assign CTL_RX_RETRANS_RESET_MODE_in = CTL_RX_RETRANS_RESET_MODE;
  assign CTL_RX_RETRANS_RESET_in = CTL_RX_RETRANS_RESET;
  assign CTL_TX_DIAGWORD_INTFSTAT_in = CTL_TX_DIAGWORD_INTFSTAT;
  assign CTL_TX_DIAGWORD_LANESTAT_in = CTL_TX_DIAGWORD_LANESTAT;
  assign CTL_TX_ENABLE_in = CTL_TX_ENABLE;
  assign CTL_TX_ERRINJ_BITERR_GO_in = CTL_TX_ERRINJ_BITERR_GO;
  assign CTL_TX_ERRINJ_BITERR_LANE_in = CTL_TX_ERRINJ_BITERR_LANE;
  assign CTL_TX_FC_STAT_in = CTL_TX_FC_STAT;
  assign CTL_TX_MUBITS_in = CTL_TX_MUBITS;
  assign CTL_TX_RETRANS_ENABLE_in = CTL_TX_RETRANS_ENABLE;
  assign CTL_TX_RETRANS_RAM_PERRIN_in = CTL_TX_RETRANS_RAM_PERRIN;
  assign CTL_TX_RETRANS_RAM_RDATA_in = CTL_TX_RETRANS_RAM_RDATA;
  assign CTL_TX_RETRANS_REQ_VALID_in = CTL_TX_RETRANS_REQ_VALID;
  assign CTL_TX_RETRANS_REQ_in = CTL_TX_RETRANS_REQ;
  assign CTL_TX_RLIM_DELTA_in = CTL_TX_RLIM_DELTA;
  assign CTL_TX_RLIM_ENABLE_in = CTL_TX_RLIM_ENABLE;
  assign CTL_TX_RLIM_INTV_in = CTL_TX_RLIM_INTV;
  assign CTL_TX_RLIM_MAX_in = CTL_TX_RLIM_MAX;
  assign DRP_ADDR_in = DRP_ADDR;
  assign DRP_CLK_in = DRP_CLK;
  assign DRP_DI_in = DRP_DI;
  assign DRP_EN_in = DRP_EN;
  assign DRP_WE_in = DRP_WE;
  assign LBUS_CLK_in = LBUS_CLK;
  assign RX_BYPASS_FORCE_REALIGNIN_in = RX_BYPASS_FORCE_REALIGNIN;
  assign RX_BYPASS_RDIN_in = RX_BYPASS_RDIN;
  assign RX_RESET_in = RX_RESET;
  assign RX_SERDES_CLK_in[0] = RX_SERDES_CLK[0];
  assign RX_SERDES_CLK_in[10] = RX_SERDES_CLK[10];
  assign RX_SERDES_CLK_in[11] = RX_SERDES_CLK[11];
  assign RX_SERDES_CLK_in[1] = RX_SERDES_CLK[1];
  assign RX_SERDES_CLK_in[2] = RX_SERDES_CLK[2];
  assign RX_SERDES_CLK_in[3] = RX_SERDES_CLK[3];
  assign RX_SERDES_CLK_in[4] = RX_SERDES_CLK[4];
  assign RX_SERDES_CLK_in[5] = RX_SERDES_CLK[5];
  assign RX_SERDES_CLK_in[6] = RX_SERDES_CLK[6];
  assign RX_SERDES_CLK_in[7] = RX_SERDES_CLK[7];
  assign RX_SERDES_CLK_in[8] = RX_SERDES_CLK[8];
  assign RX_SERDES_CLK_in[9] = RX_SERDES_CLK[9];
  assign RX_SERDES_DATA00_in = RX_SERDES_DATA00;
  assign RX_SERDES_DATA01_in = RX_SERDES_DATA01;
  assign RX_SERDES_DATA02_in = RX_SERDES_DATA02;
  assign RX_SERDES_DATA03_in = RX_SERDES_DATA03;
  assign RX_SERDES_DATA04_in = RX_SERDES_DATA04;
  assign RX_SERDES_DATA05_in = RX_SERDES_DATA05;
  assign RX_SERDES_DATA06_in = RX_SERDES_DATA06;
  assign RX_SERDES_DATA07_in = RX_SERDES_DATA07;
  assign RX_SERDES_DATA08_in = RX_SERDES_DATA08;
  assign RX_SERDES_DATA09_in = RX_SERDES_DATA09;
  assign RX_SERDES_DATA10_in = RX_SERDES_DATA10;
  assign RX_SERDES_DATA11_in = RX_SERDES_DATA11;
  assign RX_SERDES_RESET_in = RX_SERDES_RESET;
  assign TX_BCTLIN0_in = TX_BCTLIN0;
  assign TX_BCTLIN1_in = TX_BCTLIN1;
  assign TX_BCTLIN2_in = TX_BCTLIN2;
  assign TX_BCTLIN3_in = TX_BCTLIN3;
  assign TX_BYPASS_CTRLIN_in = TX_BYPASS_CTRLIN;
  assign TX_BYPASS_DATAIN00_in = TX_BYPASS_DATAIN00;
  assign TX_BYPASS_DATAIN01_in = TX_BYPASS_DATAIN01;
  assign TX_BYPASS_DATAIN02_in = TX_BYPASS_DATAIN02;
  assign TX_BYPASS_DATAIN03_in = TX_BYPASS_DATAIN03;
  assign TX_BYPASS_DATAIN04_in = TX_BYPASS_DATAIN04;
  assign TX_BYPASS_DATAIN05_in = TX_BYPASS_DATAIN05;
  assign TX_BYPASS_DATAIN06_in = TX_BYPASS_DATAIN06;
  assign TX_BYPASS_DATAIN07_in = TX_BYPASS_DATAIN07;
  assign TX_BYPASS_DATAIN08_in = TX_BYPASS_DATAIN08;
  assign TX_BYPASS_DATAIN09_in = TX_BYPASS_DATAIN09;
  assign TX_BYPASS_DATAIN10_in = TX_BYPASS_DATAIN10;
  assign TX_BYPASS_DATAIN11_in = TX_BYPASS_DATAIN11;
  assign TX_BYPASS_ENAIN_in = TX_BYPASS_ENAIN;
  assign TX_BYPASS_GEARBOX_SEQIN_in = TX_BYPASS_GEARBOX_SEQIN;
  assign TX_BYPASS_MFRAMER_STATEIN_in = TX_BYPASS_MFRAMER_STATEIN;
  assign TX_CHANIN0_in = TX_CHANIN0;
  assign TX_CHANIN1_in = TX_CHANIN1;
  assign TX_CHANIN2_in = TX_CHANIN2;
  assign TX_CHANIN3_in = TX_CHANIN3;
  assign TX_DATAIN0_in = TX_DATAIN0;
  assign TX_DATAIN1_in = TX_DATAIN1;
  assign TX_DATAIN2_in = TX_DATAIN2;
  assign TX_DATAIN3_in = TX_DATAIN3;
  assign TX_ENAIN0_in = TX_ENAIN0;
  assign TX_ENAIN1_in = TX_ENAIN1;
  assign TX_ENAIN2_in = TX_ENAIN2;
  assign TX_ENAIN3_in = TX_ENAIN3;
  assign TX_EOPIN0_in = TX_EOPIN0;
  assign TX_EOPIN1_in = TX_EOPIN1;
  assign TX_EOPIN2_in = TX_EOPIN2;
  assign TX_EOPIN3_in = TX_EOPIN3;
  assign TX_ERRIN0_in = TX_ERRIN0;
  assign TX_ERRIN1_in = TX_ERRIN1;
  assign TX_ERRIN2_in = TX_ERRIN2;
  assign TX_ERRIN3_in = TX_ERRIN3;
  assign TX_MTYIN0_in = TX_MTYIN0;
  assign TX_MTYIN1_in = TX_MTYIN1;
  assign TX_MTYIN2_in = TX_MTYIN2;
  assign TX_MTYIN3_in = TX_MTYIN3;
  assign TX_RESET_in = TX_RESET;
  assign TX_SERDES_REFCLK_RESET_in = TX_SERDES_REFCLK_RESET;
  assign TX_SERDES_REFCLK_in = TX_SERDES_REFCLK;
  assign TX_SOPIN0_in = TX_SOPIN0;
  assign TX_SOPIN1_in = TX_SOPIN1;
  assign TX_SOPIN2_in = TX_SOPIN2;
  assign TX_SOPIN3_in = TX_SOPIN3;



  reg attr_test;
  reg attr_err;
  
  initial begin
  trig_attr = 1'b0;
  


    attr_test = 1'b0;
  
    attr_err = 1'b0;
    #1;
    trig_attr = ~trig_attr;
  end



  always @ (trig_attr) begin
    #1;
    if ((attr_test == 1'b1) ||
        ((BYPASS_REG != "FALSE") &&
         (BYPASS_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-101] BYPASS attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, BYPASS_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((CTL_RX_LAST_LANE_REG < 4'h0) || (CTL_RX_LAST_LANE_REG > 4'hB))) begin
        $display("Error: [Unisim %s-112] CTL_RX_LAST_LANE attribute is set to %h.  Legal values for this attribute are 4'h0 to 4'hB. Instance: %m", MODULE_NAME, CTL_RX_LAST_LANE_REG);
        attr_err = 1'b1;
      end
    
    if ((attr_test == 1'b1) ||
        ((CTL_RX_MFRAMELEN_MINUS1_REG < 16'h00FF) || (CTL_RX_MFRAMELEN_MINUS1_REG > 16'h1FFF))) begin
        $display("Error: [Unisim %s-113] CTL_RX_MFRAMELEN_MINUS1 attribute is set to %h.  Legal values for this attribute are 16'h00FF to 16'h1FFF. Instance: %m", MODULE_NAME, CTL_RX_MFRAMELEN_MINUS1_REG);
        attr_err = 1'b1;
      end
    
    if ((attr_test == 1'b1) ||
        ((CTL_RX_PACKET_MODE_REG != "FALSE") &&
         (CTL_RX_PACKET_MODE_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-114] CTL_RX_PACKET_MODE attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CTL_RX_PACKET_MODE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((CTL_RX_RETRANS_MULT_REG < 3'h0) || (CTL_RX_RETRANS_MULT_REG > 3'h5))) begin
        $display("Error: [Unisim %s-115] CTL_RX_RETRANS_MULT attribute is set to %h.  Legal values for this attribute are 3'h0 to 3'h5. Instance: %m", MODULE_NAME, CTL_RX_RETRANS_MULT_REG);
        attr_err = 1'b1;
      end
    
    if ((attr_test == 1'b1) ||
        ((CTL_TEST_MODE_PIN_CHAR_REG != "FALSE") &&
         (CTL_TEST_MODE_PIN_CHAR_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-121] CTL_TEST_MODE_PIN_CHAR attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CTL_TEST_MODE_PIN_CHAR_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((CTL_TX_BURSTSHORT_REG < 3'h1) || (CTL_TX_BURSTSHORT_REG > 3'h7))) begin
        $display("Error: [Unisim %s-123] CTL_TX_BURSTSHORT attribute is set to %h.  Legal values for this attribute are 3'h1 to 3'h7. Instance: %m", MODULE_NAME, CTL_TX_BURSTSHORT_REG);
        attr_err = 1'b1;
      end
    
    if ((attr_test == 1'b1) ||
        ((CTL_TX_DISABLE_SKIPWORD_REG != "FALSE") &&
         (CTL_TX_DISABLE_SKIPWORD_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-125] CTL_TX_DISABLE_SKIPWORD attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CTL_TX_DISABLE_SKIPWORD_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((CTL_TX_LAST_LANE_REG < 4'h0) || (CTL_TX_LAST_LANE_REG > 4'hB))) begin
        $display("Error: [Unisim %s-127] CTL_TX_LAST_LANE attribute is set to %h.  Legal values for this attribute are 4'h0 to 4'hB. Instance: %m", MODULE_NAME, CTL_TX_LAST_LANE_REG);
        attr_err = 1'b1;
      end
    
    if ((attr_test == 1'b1) ||
        ((CTL_TX_MFRAMELEN_MINUS1_REG < 16'h00FF) || (CTL_TX_MFRAMELEN_MINUS1_REG > 16'h1FFF))) begin
        $display("Error: [Unisim %s-128] CTL_TX_MFRAMELEN_MINUS1 attribute is set to %h.  Legal values for this attribute are 16'h00FF to 16'h1FFF. Instance: %m", MODULE_NAME, CTL_TX_MFRAMELEN_MINUS1_REG);
        attr_err = 1'b1;
      end
    
    if ((attr_test == 1'b1) ||
        ((CTL_TX_RETRANS_DEPTH_REG < 14'h0015) || (CTL_TX_RETRANS_DEPTH_REG > 14'h0800))) begin
        $display("Error: [Unisim %s-129] CTL_TX_RETRANS_DEPTH attribute is set to %h.  Legal values for this attribute are 14'h0015 to 14'h0800. Instance: %m", MODULE_NAME, CTL_TX_RETRANS_DEPTH_REG);
        attr_err = 1'b1;
      end
    
    if ((attr_test == 1'b1) ||
        ((CTL_TX_RETRANS_MULT_REG < 3'h0) || (CTL_TX_RETRANS_MULT_REG > 3'h5))) begin
        $display("Error: [Unisim %s-130] CTL_TX_RETRANS_MULT attribute is set to %h.  Legal values for this attribute are 3'h0 to 3'h5. Instance: %m", MODULE_NAME, CTL_TX_RETRANS_MULT_REG);
        attr_err = 1'b1;
      end
    
    if ((attr_test == 1'b1) ||
        ((MODE_REG != "TRUE") &&
         (MODE_REG != "FALSE"))) begin
      $display("Error: [Unisim %s-132] MODE attribute is set to %s.  Legal values for this attribute are TRUE or FALSE. Instance: %m", MODULE_NAME, MODE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((SIM_DEVICE_REG != "ULTRASCALE_PLUS") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES1") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES2"))) begin
      $display("Error: [Unisim %s-133] SIM_DEVICE attribute is set to %s.  Legal values for this attribute are ULTRASCALE_PLUS, ULTRASCALE_PLUS_ES1 or ULTRASCALE_PLUS_ES2. Instance: %m", MODULE_NAME, SIM_DEVICE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((TEST_MODE_PIN_CHAR_REG != "FALSE") &&
         (TEST_MODE_PIN_CHAR_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-134] TEST_MODE_PIN_CHAR attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, TEST_MODE_PIN_CHAR_REG);
      attr_err = 1'b1;
    end
    
    if (attr_err == 1'b1) #1 $finish;
  end




assign CSSD_CLK_STOP_EVENT_in = 1'b1; // tie off
assign CSSD_RESETN_in = 1'b1; // tie off
assign SCAN_CLK_in = 1'b1; // tie off
assign SCAN_EN_N_in = 1'b1; // tie off
assign SCAN_IN_in = 265'b1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111; // tie off
assign TEST_MODE_N_in = 1'b1; // tie off
assign TEST_RESET_in = 1'b1; // tie off

  SIP_ILKNE4 SIP_ILKNE4_INST (
    .BYPASS (BYPASS_REG),
    .CTL_CSSD_EN (CTL_CSSD_EN_REG),
    .CTL_CSSD_MRKR_INIT (CTL_CSSD_MRKR_INIT_REG),
    .CTL_CSSD_ROOT_CLK_DIS (CTL_CSSD_ROOT_CLK_DIS_REG),
    .CTL_CSSD_ROOT_CLK_SEL (CTL_CSSD_ROOT_CLK_SEL_REG),
    .CTL_CSSD_SNGL_CHAIN_MD (CTL_CSSD_SNGL_CHAIN_MD_REG),
    .CTL_CSSD_STOP_COUNT_0 (CTL_CSSD_STOP_COUNT_0_REG),
    .CTL_CSSD_STOP_COUNT_1 (CTL_CSSD_STOP_COUNT_1_REG),
    .CTL_CSSD_STOP_COUNT_2 (CTL_CSSD_STOP_COUNT_2_REG),
    .CTL_RX_BURSTMAX (CTL_RX_BURSTMAX_REG),
    .CTL_RX_CHAN_EXT (CTL_RX_CHAN_EXT_REG),
    .CTL_RX_LAST_LANE (CTL_RX_LAST_LANE_REG),
    .CTL_RX_MFRAMELEN_MINUS1 (CTL_RX_MFRAMELEN_MINUS1_REG),
    .CTL_RX_PACKET_MODE (CTL_RX_PACKET_MODE_REG),
    .CTL_RX_RETRANS_MULT (CTL_RX_RETRANS_MULT_REG),
    .CTL_RX_RETRANS_RETRY (CTL_RX_RETRANS_RETRY_REG),
    .CTL_RX_RETRANS_TIMER1 (CTL_RX_RETRANS_TIMER1_REG),
    .CTL_RX_RETRANS_TIMER2 (CTL_RX_RETRANS_TIMER2_REG),
    .CTL_RX_RETRANS_WDOG (CTL_RX_RETRANS_WDOG_REG),
    .CTL_RX_RETRANS_WRAP_TIMER (CTL_RX_RETRANS_WRAP_TIMER_REG),
    .CTL_TEST_MODE_PIN_CHAR (CTL_TEST_MODE_PIN_CHAR_REG),
    .CTL_TX_BURSTMAX (CTL_TX_BURSTMAX_REG),
    .CTL_TX_BURSTSHORT (CTL_TX_BURSTSHORT_REG),
    .CTL_TX_CHAN_EXT (CTL_TX_CHAN_EXT_REG),
    .CTL_TX_DISABLE_SKIPWORD (CTL_TX_DISABLE_SKIPWORD_REG),
    .CTL_TX_FC_CALLEN (CTL_TX_FC_CALLEN_REG),
    .CTL_TX_LAST_LANE (CTL_TX_LAST_LANE_REG),
    .CTL_TX_MFRAMELEN_MINUS1 (CTL_TX_MFRAMELEN_MINUS1_REG),
    .CTL_TX_RETRANS_DEPTH (CTL_TX_RETRANS_DEPTH_REG),
    .CTL_TX_RETRANS_MULT (CTL_TX_RETRANS_MULT_REG),
    .CTL_TX_RETRANS_RAM_BANKS (CTL_TX_RETRANS_RAM_BANKS_REG),
    .MODE (MODE_REG),
    .TEST_MODE_PIN_CHAR (TEST_MODE_PIN_CHAR_REG),
    .CFG_RESET_CSSD (CFG_RESET_CSSD_out),
    .CSSD_CLK_STOP_DONE (CSSD_CLK_STOP_DONE_out),
    .DRP_DO (DRP_DO_out),
    .DRP_RDY (DRP_RDY_out),
    .GRESTORE_CSSD (GRESTORE_CSSD_out),
    .GWE_CSSD (GWE_CSSD_out),
    .RX_BYPASS_DATAOUT00 (RX_BYPASS_DATAOUT00_out),
    .RX_BYPASS_DATAOUT01 (RX_BYPASS_DATAOUT01_out),
    .RX_BYPASS_DATAOUT02 (RX_BYPASS_DATAOUT02_out),
    .RX_BYPASS_DATAOUT03 (RX_BYPASS_DATAOUT03_out),
    .RX_BYPASS_DATAOUT04 (RX_BYPASS_DATAOUT04_out),
    .RX_BYPASS_DATAOUT05 (RX_BYPASS_DATAOUT05_out),
    .RX_BYPASS_DATAOUT06 (RX_BYPASS_DATAOUT06_out),
    .RX_BYPASS_DATAOUT07 (RX_BYPASS_DATAOUT07_out),
    .RX_BYPASS_DATAOUT08 (RX_BYPASS_DATAOUT08_out),
    .RX_BYPASS_DATAOUT09 (RX_BYPASS_DATAOUT09_out),
    .RX_BYPASS_DATAOUT10 (RX_BYPASS_DATAOUT10_out),
    .RX_BYPASS_DATAOUT11 (RX_BYPASS_DATAOUT11_out),
    .RX_BYPASS_ENAOUT (RX_BYPASS_ENAOUT_out),
    .RX_BYPASS_IS_AVAILOUT (RX_BYPASS_IS_AVAILOUT_out),
    .RX_BYPASS_IS_BADLYFRAMEDOUT (RX_BYPASS_IS_BADLYFRAMEDOUT_out),
    .RX_BYPASS_IS_OVERFLOWOUT (RX_BYPASS_IS_OVERFLOWOUT_out),
    .RX_BYPASS_IS_SYNCEDOUT (RX_BYPASS_IS_SYNCEDOUT_out),
    .RX_BYPASS_IS_SYNCWORDOUT (RX_BYPASS_IS_SYNCWORDOUT_out),
    .RX_CHANOUT0 (RX_CHANOUT0_out),
    .RX_CHANOUT1 (RX_CHANOUT1_out),
    .RX_CHANOUT2 (RX_CHANOUT2_out),
    .RX_CHANOUT3 (RX_CHANOUT3_out),
    .RX_DATAOUT0 (RX_DATAOUT0_out),
    .RX_DATAOUT1 (RX_DATAOUT1_out),
    .RX_DATAOUT2 (RX_DATAOUT2_out),
    .RX_DATAOUT3 (RX_DATAOUT3_out),
    .RX_ENAOUT0 (RX_ENAOUT0_out),
    .RX_ENAOUT1 (RX_ENAOUT1_out),
    .RX_ENAOUT2 (RX_ENAOUT2_out),
    .RX_ENAOUT3 (RX_ENAOUT3_out),
    .RX_EOPOUT0 (RX_EOPOUT0_out),
    .RX_EOPOUT1 (RX_EOPOUT1_out),
    .RX_EOPOUT2 (RX_EOPOUT2_out),
    .RX_EOPOUT3 (RX_EOPOUT3_out),
    .RX_ERROUT0 (RX_ERROUT0_out),
    .RX_ERROUT1 (RX_ERROUT1_out),
    .RX_ERROUT2 (RX_ERROUT2_out),
    .RX_ERROUT3 (RX_ERROUT3_out),
    .RX_MTYOUT0 (RX_MTYOUT0_out),
    .RX_MTYOUT1 (RX_MTYOUT1_out),
    .RX_MTYOUT2 (RX_MTYOUT2_out),
    .RX_MTYOUT3 (RX_MTYOUT3_out),
    .RX_OVFOUT (RX_OVFOUT_out),
    .RX_SOPOUT0 (RX_SOPOUT0_out),
    .RX_SOPOUT1 (RX_SOPOUT1_out),
    .RX_SOPOUT2 (RX_SOPOUT2_out),
    .RX_SOPOUT3 (RX_SOPOUT3_out),
    .SCAN_OUT (SCAN_OUT_out),
    .STAT_RX_ALIGNED (STAT_RX_ALIGNED_out),
    .STAT_RX_ALIGNED_ERR (STAT_RX_ALIGNED_ERR_out),
    .STAT_RX_BAD_TYPE_ERR (STAT_RX_BAD_TYPE_ERR_out),
    .STAT_RX_BURSTMAX_ERR (STAT_RX_BURSTMAX_ERR_out),
    .STAT_RX_BURST_ERR (STAT_RX_BURST_ERR_out),
    .STAT_RX_CRC24_ERR (STAT_RX_CRC24_ERR_out),
    .STAT_RX_CRC32_ERR (STAT_RX_CRC32_ERR_out),
    .STAT_RX_CRC32_VALID (STAT_RX_CRC32_VALID_out),
    .STAT_RX_DESCRAM_ERR (STAT_RX_DESCRAM_ERR_out),
    .STAT_RX_DIAGWORD_INTFSTAT (STAT_RX_DIAGWORD_INTFSTAT_out),
    .STAT_RX_DIAGWORD_LANESTAT (STAT_RX_DIAGWORD_LANESTAT_out),
    .STAT_RX_FC_STAT (STAT_RX_FC_STAT_out),
    .STAT_RX_FRAMING_ERR (STAT_RX_FRAMING_ERR_out),
    .STAT_RX_MEOP_ERR (STAT_RX_MEOP_ERR_out),
    .STAT_RX_MF_ERR (STAT_RX_MF_ERR_out),
    .STAT_RX_MF_LEN_ERR (STAT_RX_MF_LEN_ERR_out),
    .STAT_RX_MF_REPEAT_ERR (STAT_RX_MF_REPEAT_ERR_out),
    .STAT_RX_MISALIGNED (STAT_RX_MISALIGNED_out),
    .STAT_RX_MSOP_ERR (STAT_RX_MSOP_ERR_out),
    .STAT_RX_MUBITS (STAT_RX_MUBITS_out),
    .STAT_RX_MUBITS_UPDATED (STAT_RX_MUBITS_UPDATED_out),
    .STAT_RX_OVERFLOW_ERR (STAT_RX_OVERFLOW_ERR_out),
    .STAT_RX_RETRANS_CRC24_ERR (STAT_RX_RETRANS_CRC24_ERR_out),
    .STAT_RX_RETRANS_DISC (STAT_RX_RETRANS_DISC_out),
    .STAT_RX_RETRANS_LATENCY (STAT_RX_RETRANS_LATENCY_out),
    .STAT_RX_RETRANS_REQ (STAT_RX_RETRANS_REQ_out),
    .STAT_RX_RETRANS_RETRY_ERR (STAT_RX_RETRANS_RETRY_ERR_out),
    .STAT_RX_RETRANS_SEQ (STAT_RX_RETRANS_SEQ_out),
    .STAT_RX_RETRANS_SEQ_UPDATED (STAT_RX_RETRANS_SEQ_UPDATED_out),
    .STAT_RX_RETRANS_STATE (STAT_RX_RETRANS_STATE_out),
    .STAT_RX_RETRANS_SUBSEQ (STAT_RX_RETRANS_SUBSEQ_out),
    .STAT_RX_RETRANS_WDOG_ERR (STAT_RX_RETRANS_WDOG_ERR_out),
    .STAT_RX_RETRANS_WRAP_ERR (STAT_RX_RETRANS_WRAP_ERR_out),
    .STAT_RX_SYNCED (STAT_RX_SYNCED_out),
    .STAT_RX_SYNCED_ERR (STAT_RX_SYNCED_ERR_out),
    .STAT_RX_WORD_SYNC (STAT_RX_WORD_SYNC_out),
    .STAT_TX_BURST_ERR (STAT_TX_BURST_ERR_out),
    .STAT_TX_ERRINJ_BITERR_DONE (STAT_TX_ERRINJ_BITERR_DONE_out),
    .STAT_TX_OVERFLOW_ERR (STAT_TX_OVERFLOW_ERR_out),
    .STAT_TX_RETRANS_BURST_ERR (STAT_TX_RETRANS_BURST_ERR_out),
    .STAT_TX_RETRANS_BUSY (STAT_TX_RETRANS_BUSY_out),
    .STAT_TX_RETRANS_RAM_PERROUT (STAT_TX_RETRANS_RAM_PERROUT_out),
    .STAT_TX_RETRANS_RAM_RADDR (STAT_TX_RETRANS_RAM_RADDR_out),
    .STAT_TX_RETRANS_RAM_RD_B0 (STAT_TX_RETRANS_RAM_RD_B0_out),
    .STAT_TX_RETRANS_RAM_RD_B1 (STAT_TX_RETRANS_RAM_RD_B1_out),
    .STAT_TX_RETRANS_RAM_RD_B2 (STAT_TX_RETRANS_RAM_RD_B2_out),
    .STAT_TX_RETRANS_RAM_RD_B3 (STAT_TX_RETRANS_RAM_RD_B3_out),
    .STAT_TX_RETRANS_RAM_RSEL (STAT_TX_RETRANS_RAM_RSEL_out),
    .STAT_TX_RETRANS_RAM_WADDR (STAT_TX_RETRANS_RAM_WADDR_out),
    .STAT_TX_RETRANS_RAM_WDATA (STAT_TX_RETRANS_RAM_WDATA_out),
    .STAT_TX_RETRANS_RAM_WE_B0 (STAT_TX_RETRANS_RAM_WE_B0_out),
    .STAT_TX_RETRANS_RAM_WE_B1 (STAT_TX_RETRANS_RAM_WE_B1_out),
    .STAT_TX_RETRANS_RAM_WE_B2 (STAT_TX_RETRANS_RAM_WE_B2_out),
    .STAT_TX_RETRANS_RAM_WE_B3 (STAT_TX_RETRANS_RAM_WE_B3_out),
    .STAT_TX_UNDERFLOW_ERR (STAT_TX_UNDERFLOW_ERR_out),
    .TX_OVFOUT (TX_OVFOUT_out),
    .TX_RDYOUT (TX_RDYOUT_out),
    .TX_SERDES_DATA00 (TX_SERDES_DATA00_out),
    .TX_SERDES_DATA01 (TX_SERDES_DATA01_out),
    .TX_SERDES_DATA02 (TX_SERDES_DATA02_out),
    .TX_SERDES_DATA03 (TX_SERDES_DATA03_out),
    .TX_SERDES_DATA04 (TX_SERDES_DATA04_out),
    .TX_SERDES_DATA05 (TX_SERDES_DATA05_out),
    .TX_SERDES_DATA06 (TX_SERDES_DATA06_out),
    .TX_SERDES_DATA07 (TX_SERDES_DATA07_out),
    .TX_SERDES_DATA08 (TX_SERDES_DATA08_out),
    .TX_SERDES_DATA09 (TX_SERDES_DATA09_out),
    .TX_SERDES_DATA10 (TX_SERDES_DATA10_out),
    .TX_SERDES_DATA11 (TX_SERDES_DATA11_out),
    .CORE_CLK (CORE_CLK_in),
    .CSSD_CLK_STOP_EVENT (CSSD_CLK_STOP_EVENT_in),
    .CSSD_RESETN (CSSD_RESETN_in),
    .CTL_RX_FORCE_RESYNC (CTL_RX_FORCE_RESYNC_in),
    .CTL_RX_RETRANS_ACK (CTL_RX_RETRANS_ACK_in),
    .CTL_RX_RETRANS_ENABLE (CTL_RX_RETRANS_ENABLE_in),
    .CTL_RX_RETRANS_ERRIN (CTL_RX_RETRANS_ERRIN_in),
    .CTL_RX_RETRANS_FORCE_REQ (CTL_RX_RETRANS_FORCE_REQ_in),
    .CTL_RX_RETRANS_RESET (CTL_RX_RETRANS_RESET_in),
    .CTL_RX_RETRANS_RESET_MODE (CTL_RX_RETRANS_RESET_MODE_in),
    .CTL_TX_DIAGWORD_INTFSTAT (CTL_TX_DIAGWORD_INTFSTAT_in),
    .CTL_TX_DIAGWORD_LANESTAT (CTL_TX_DIAGWORD_LANESTAT_in),
    .CTL_TX_ENABLE (CTL_TX_ENABLE_in),
    .CTL_TX_ERRINJ_BITERR_GO (CTL_TX_ERRINJ_BITERR_GO_in),
    .CTL_TX_ERRINJ_BITERR_LANE (CTL_TX_ERRINJ_BITERR_LANE_in),
    .CTL_TX_FC_STAT (CTL_TX_FC_STAT_in),
    .CTL_TX_MUBITS (CTL_TX_MUBITS_in),
    .CTL_TX_RETRANS_ENABLE (CTL_TX_RETRANS_ENABLE_in),
    .CTL_TX_RETRANS_RAM_PERRIN (CTL_TX_RETRANS_RAM_PERRIN_in),
    .CTL_TX_RETRANS_RAM_RDATA (CTL_TX_RETRANS_RAM_RDATA_in),
    .CTL_TX_RETRANS_REQ (CTL_TX_RETRANS_REQ_in),
    .CTL_TX_RETRANS_REQ_VALID (CTL_TX_RETRANS_REQ_VALID_in),
    .CTL_TX_RLIM_DELTA (CTL_TX_RLIM_DELTA_in),
    .CTL_TX_RLIM_ENABLE (CTL_TX_RLIM_ENABLE_in),
    .CTL_TX_RLIM_INTV (CTL_TX_RLIM_INTV_in),
    .CTL_TX_RLIM_MAX (CTL_TX_RLIM_MAX_in),
    .DRP_ADDR (DRP_ADDR_in),
    .DRP_CLK (DRP_CLK_in),
    .DRP_DI (DRP_DI_in),
    .DRP_EN (DRP_EN_in),
    .DRP_WE (DRP_WE_in),
    .LBUS_CLK (LBUS_CLK_in),
    .RX_BYPASS_FORCE_REALIGNIN (RX_BYPASS_FORCE_REALIGNIN_in),
    .RX_BYPASS_RDIN (RX_BYPASS_RDIN_in),
    .RX_RESET (RX_RESET_in),
    .RX_SERDES_CLK (RX_SERDES_CLK_in),
    .RX_SERDES_DATA00 (RX_SERDES_DATA00_in),
    .RX_SERDES_DATA01 (RX_SERDES_DATA01_in),
    .RX_SERDES_DATA02 (RX_SERDES_DATA02_in),
    .RX_SERDES_DATA03 (RX_SERDES_DATA03_in),
    .RX_SERDES_DATA04 (RX_SERDES_DATA04_in),
    .RX_SERDES_DATA05 (RX_SERDES_DATA05_in),
    .RX_SERDES_DATA06 (RX_SERDES_DATA06_in),
    .RX_SERDES_DATA07 (RX_SERDES_DATA07_in),
    .RX_SERDES_DATA08 (RX_SERDES_DATA08_in),
    .RX_SERDES_DATA09 (RX_SERDES_DATA09_in),
    .RX_SERDES_DATA10 (RX_SERDES_DATA10_in),
    .RX_SERDES_DATA11 (RX_SERDES_DATA11_in),
    .RX_SERDES_RESET (RX_SERDES_RESET_in),
    .SCAN_CLK (SCAN_CLK_in),
    .SCAN_EN_N (SCAN_EN_N_in),
    .SCAN_IN (SCAN_IN_in),
    .TEST_MODE_N (TEST_MODE_N_in),
    .TEST_RESET (TEST_RESET_in),
    .TX_BCTLIN0 (TX_BCTLIN0_in),
    .TX_BCTLIN1 (TX_BCTLIN1_in),
    .TX_BCTLIN2 (TX_BCTLIN2_in),
    .TX_BCTLIN3 (TX_BCTLIN3_in),
    .TX_BYPASS_CTRLIN (TX_BYPASS_CTRLIN_in),
    .TX_BYPASS_DATAIN00 (TX_BYPASS_DATAIN00_in),
    .TX_BYPASS_DATAIN01 (TX_BYPASS_DATAIN01_in),
    .TX_BYPASS_DATAIN02 (TX_BYPASS_DATAIN02_in),
    .TX_BYPASS_DATAIN03 (TX_BYPASS_DATAIN03_in),
    .TX_BYPASS_DATAIN04 (TX_BYPASS_DATAIN04_in),
    .TX_BYPASS_DATAIN05 (TX_BYPASS_DATAIN05_in),
    .TX_BYPASS_DATAIN06 (TX_BYPASS_DATAIN06_in),
    .TX_BYPASS_DATAIN07 (TX_BYPASS_DATAIN07_in),
    .TX_BYPASS_DATAIN08 (TX_BYPASS_DATAIN08_in),
    .TX_BYPASS_DATAIN09 (TX_BYPASS_DATAIN09_in),
    .TX_BYPASS_DATAIN10 (TX_BYPASS_DATAIN10_in),
    .TX_BYPASS_DATAIN11 (TX_BYPASS_DATAIN11_in),
    .TX_BYPASS_ENAIN (TX_BYPASS_ENAIN_in),
    .TX_BYPASS_GEARBOX_SEQIN (TX_BYPASS_GEARBOX_SEQIN_in),
    .TX_BYPASS_MFRAMER_STATEIN (TX_BYPASS_MFRAMER_STATEIN_in),
    .TX_CHANIN0 (TX_CHANIN0_in),
    .TX_CHANIN1 (TX_CHANIN1_in),
    .TX_CHANIN2 (TX_CHANIN2_in),
    .TX_CHANIN3 (TX_CHANIN3_in),
    .TX_DATAIN0 (TX_DATAIN0_in),
    .TX_DATAIN1 (TX_DATAIN1_in),
    .TX_DATAIN2 (TX_DATAIN2_in),
    .TX_DATAIN3 (TX_DATAIN3_in),
    .TX_ENAIN0 (TX_ENAIN0_in),
    .TX_ENAIN1 (TX_ENAIN1_in),
    .TX_ENAIN2 (TX_ENAIN2_in),
    .TX_ENAIN3 (TX_ENAIN3_in),
    .TX_EOPIN0 (TX_EOPIN0_in),
    .TX_EOPIN1 (TX_EOPIN1_in),
    .TX_EOPIN2 (TX_EOPIN2_in),
    .TX_EOPIN3 (TX_EOPIN3_in),
    .TX_ERRIN0 (TX_ERRIN0_in),
    .TX_ERRIN1 (TX_ERRIN1_in),
    .TX_ERRIN2 (TX_ERRIN2_in),
    .TX_ERRIN3 (TX_ERRIN3_in),
    .TX_MTYIN0 (TX_MTYIN0_in),
    .TX_MTYIN1 (TX_MTYIN1_in),
    .TX_MTYIN2 (TX_MTYIN2_in),
    .TX_MTYIN3 (TX_MTYIN3_in),
    .TX_RESET (TX_RESET_in),
    .TX_SERDES_REFCLK (TX_SERDES_REFCLK_in),
    .TX_SERDES_REFCLK_RESET (TX_SERDES_REFCLK_RESET_in),
    .TX_SOPIN0 (TX_SOPIN0_in),
    .TX_SOPIN1 (TX_SOPIN1_in),
    .TX_SOPIN2 (TX_SOPIN2_in),
    .TX_SOPIN3 (TX_SOPIN3_in),
    .GSR (glblGSR)
  );






  specify
    (CORE_CLK => RX_BYPASS_DATAOUT00[0]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[10]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[11]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[12]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[13]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[14]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[15]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[16]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[17]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[18]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[19]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[1]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[20]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[21]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[22]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[23]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[24]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[25]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[26]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[27]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[28]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[29]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[2]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[30]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[31]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[32]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[33]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[34]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[35]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[36]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[37]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[38]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[39]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[3]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[40]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[41]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[42]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[43]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[44]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[45]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[46]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[47]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[48]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[49]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[4]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[50]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[51]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[52]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[53]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[54]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[55]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[56]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[57]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[58]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[59]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[5]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[60]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[61]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[62]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[63]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[64]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[65]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[6]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[7]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[8]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT00[9]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[0]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[10]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[11]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[12]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[13]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[14]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[15]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[16]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[17]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[18]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[19]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[1]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[20]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[21]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[22]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[23]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[24]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[25]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[26]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[27]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[28]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[29]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[2]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[30]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[31]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[32]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[33]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[34]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[35]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[36]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[37]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[38]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[39]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[3]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[40]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[41]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[42]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[43]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[44]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[45]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[46]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[47]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[48]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[49]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[4]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[50]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[51]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[52]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[53]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[54]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[55]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[56]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[57]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[58]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[59]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[5]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[60]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[61]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[62]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[63]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[64]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[65]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[6]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[7]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[8]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT01[9]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[0]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[10]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[11]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[12]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[13]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[14]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[15]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[16]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[17]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[18]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[19]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[1]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[20]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[21]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[22]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[23]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[24]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[25]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[26]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[27]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[28]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[29]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[2]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[30]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[31]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[32]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[33]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[34]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[35]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[36]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[37]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[38]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[39]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[3]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[40]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[41]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[42]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[43]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[44]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[45]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[46]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[47]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[48]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[49]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[4]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[50]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[51]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[52]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[53]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[54]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[55]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[56]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[57]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[58]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[59]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[5]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[60]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[61]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[62]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[63]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[64]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[65]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[6]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[7]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[8]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT02[9]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[0]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[10]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[11]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[12]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[13]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[14]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[15]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[16]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[17]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[18]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[19]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[1]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[20]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[21]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[22]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[23]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[24]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[25]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[26]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[27]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[28]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[29]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[2]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[30]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[31]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[32]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[33]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[34]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[35]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[36]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[37]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[38]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[39]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[3]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[40]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[41]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[42]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[43]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[44]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[45]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[46]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[47]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[48]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[49]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[4]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[50]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[51]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[52]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[53]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[54]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[55]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[56]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[57]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[58]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[59]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[5]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[60]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[61]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[62]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[63]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[64]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[65]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[6]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[7]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[8]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT03[9]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[0]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[10]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[11]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[12]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[13]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[14]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[15]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[16]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[17]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[18]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[19]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[1]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[20]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[21]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[22]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[23]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[24]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[25]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[26]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[27]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[28]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[29]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[2]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[30]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[31]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[32]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[33]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[34]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[35]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[36]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[37]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[38]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[39]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[3]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[40]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[41]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[42]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[43]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[44]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[45]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[46]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[47]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[48]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[49]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[4]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[50]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[51]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[52]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[53]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[54]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[55]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[56]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[57]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[58]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[59]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[5]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[60]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[61]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[62]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[63]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[64]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[65]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[6]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[7]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[8]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT04[9]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[0]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[10]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[11]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[12]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[13]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[14]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[15]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[16]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[17]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[18]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[19]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[1]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[20]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[21]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[22]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[23]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[24]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[25]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[26]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[27]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[28]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[29]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[2]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[30]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[31]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[32]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[33]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[34]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[35]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[36]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[37]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[38]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[39]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[3]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[40]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[41]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[42]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[43]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[44]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[45]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[46]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[47]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[48]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[49]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[4]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[50]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[51]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[52]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[53]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[54]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[55]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[56]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[57]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[58]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[59]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[5]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[60]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[61]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[62]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[63]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[64]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[65]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[6]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[7]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[8]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT05[9]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[0]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[10]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[11]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[12]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[13]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[14]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[15]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[16]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[17]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[18]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[19]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[1]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[20]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[21]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[22]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[23]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[24]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[25]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[26]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[27]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[28]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[29]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[2]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[30]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[31]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[32]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[33]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[34]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[35]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[36]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[37]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[38]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[39]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[3]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[40]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[41]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[42]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[43]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[44]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[45]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[46]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[47]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[48]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[49]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[4]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[50]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[51]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[52]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[53]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[54]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[55]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[56]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[57]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[58]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[59]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[5]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[60]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[61]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[62]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[63]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[64]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[65]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[6]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[7]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[8]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT06[9]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[0]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[10]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[11]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[12]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[13]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[14]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[15]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[16]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[17]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[18]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[19]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[1]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[20]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[21]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[22]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[23]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[24]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[25]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[26]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[27]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[28]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[29]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[2]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[30]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[31]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[32]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[33]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[34]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[35]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[36]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[37]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[38]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[39]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[3]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[40]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[41]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[42]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[43]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[44]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[45]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[46]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[47]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[48]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[49]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[4]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[50]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[51]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[52]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[53]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[54]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[55]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[56]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[57]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[58]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[59]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[5]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[60]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[61]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[62]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[63]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[64]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[65]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[6]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[7]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[8]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT07[9]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[0]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[10]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[11]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[12]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[13]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[14]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[15]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[16]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[17]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[18]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[19]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[1]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[20]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[21]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[22]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[23]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[24]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[25]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[26]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[27]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[28]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[29]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[2]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[30]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[31]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[32]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[33]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[34]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[35]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[36]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[37]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[38]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[39]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[3]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[40]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[41]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[42]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[43]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[44]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[45]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[46]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[47]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[48]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[49]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[4]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[50]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[51]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[52]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[53]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[54]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[55]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[56]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[57]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[58]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[59]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[5]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[60]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[61]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[62]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[63]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[64]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[65]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[6]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[7]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[8]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT08[9]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[0]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[10]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[11]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[12]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[13]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[14]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[15]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[16]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[17]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[18]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[19]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[1]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[20]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[21]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[22]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[23]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[24]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[25]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[26]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[27]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[28]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[29]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[2]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[30]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[31]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[32]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[33]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[34]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[35]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[36]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[37]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[38]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[39]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[3]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[40]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[41]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[42]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[43]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[44]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[45]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[46]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[47]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[48]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[49]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[4]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[50]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[51]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[52]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[53]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[54]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[55]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[56]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[57]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[58]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[59]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[5]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[60]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[61]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[62]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[63]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[64]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[65]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[6]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[7]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[8]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT09[9]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[0]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[10]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[11]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[12]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[13]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[14]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[15]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[16]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[17]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[18]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[19]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[1]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[20]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[21]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[22]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[23]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[24]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[25]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[26]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[27]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[28]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[29]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[2]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[30]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[31]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[32]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[33]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[34]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[35]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[36]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[37]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[38]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[39]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[3]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[40]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[41]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[42]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[43]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[44]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[45]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[46]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[47]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[48]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[49]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[4]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[50]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[51]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[52]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[53]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[54]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[55]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[56]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[57]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[58]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[59]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[5]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[60]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[61]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[62]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[63]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[64]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[65]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[6]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[7]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[8]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT10[9]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[0]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[10]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[11]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[12]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[13]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[14]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[15]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[16]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[17]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[18]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[19]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[1]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[20]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[21]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[22]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[23]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[24]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[25]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[26]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[27]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[28]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[29]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[2]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[30]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[31]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[32]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[33]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[34]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[35]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[36]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[37]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[38]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[39]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[3]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[40]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[41]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[42]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[43]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[44]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[45]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[46]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[47]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[48]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[49]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[4]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[50]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[51]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[52]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[53]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[54]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[55]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[56]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[57]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[58]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[59]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[5]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[60]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[61]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[62]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[63]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[64]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[65]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[6]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[7]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[8]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_DATAOUT11[9]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_ENAOUT[0]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_ENAOUT[10]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_ENAOUT[11]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_ENAOUT[1]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_ENAOUT[2]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_ENAOUT[3]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_ENAOUT[4]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_ENAOUT[5]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_ENAOUT[6]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_ENAOUT[7]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_ENAOUT[8]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_ENAOUT[9]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_AVAILOUT[0]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_AVAILOUT[10]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_AVAILOUT[11]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_AVAILOUT[1]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_AVAILOUT[2]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_AVAILOUT[3]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_AVAILOUT[4]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_AVAILOUT[5]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_AVAILOUT[6]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_AVAILOUT[7]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_AVAILOUT[8]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_AVAILOUT[9]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_BADLYFRAMEDOUT[0]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_BADLYFRAMEDOUT[10]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_BADLYFRAMEDOUT[11]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_BADLYFRAMEDOUT[1]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_BADLYFRAMEDOUT[2]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_BADLYFRAMEDOUT[3]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_BADLYFRAMEDOUT[4]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_BADLYFRAMEDOUT[5]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_BADLYFRAMEDOUT[6]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_BADLYFRAMEDOUT[7]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_BADLYFRAMEDOUT[8]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_BADLYFRAMEDOUT[9]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_OVERFLOWOUT[0]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_OVERFLOWOUT[10]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_OVERFLOWOUT[11]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_OVERFLOWOUT[1]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_OVERFLOWOUT[2]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_OVERFLOWOUT[3]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_OVERFLOWOUT[4]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_OVERFLOWOUT[5]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_OVERFLOWOUT[6]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_OVERFLOWOUT[7]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_OVERFLOWOUT[8]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_OVERFLOWOUT[9]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_SYNCEDOUT[0]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_SYNCEDOUT[10]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_SYNCEDOUT[11]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_SYNCEDOUT[1]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_SYNCEDOUT[2]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_SYNCEDOUT[3]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_SYNCEDOUT[4]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_SYNCEDOUT[5]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_SYNCEDOUT[6]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_SYNCEDOUT[7]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_SYNCEDOUT[8]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_SYNCEDOUT[9]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_SYNCWORDOUT[0]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_SYNCWORDOUT[10]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_SYNCWORDOUT[11]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_SYNCWORDOUT[1]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_SYNCWORDOUT[2]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_SYNCWORDOUT[3]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_SYNCWORDOUT[4]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_SYNCWORDOUT[5]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_SYNCWORDOUT[6]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_SYNCWORDOUT[7]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_SYNCWORDOUT[8]) = (100:100:100, 100:100:100);
    (CORE_CLK => RX_BYPASS_IS_SYNCWORDOUT[9]) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_MUBITS[0]) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_MUBITS[1]) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_MUBITS[2]) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_MUBITS[3]) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_MUBITS[4]) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_MUBITS[5]) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_MUBITS[6]) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_MUBITS[7]) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_MUBITS_UPDATED) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_RETRANS_CRC24_ERR) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_RETRANS_DISC) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_RETRANS_RETRY_ERR) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_RETRANS_SEQ[0]) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_RETRANS_SEQ[1]) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_RETRANS_SEQ[2]) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_RETRANS_SEQ[3]) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_RETRANS_SEQ[4]) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_RETRANS_SEQ[5]) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_RETRANS_SEQ[6]) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_RETRANS_SEQ[7]) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_RETRANS_SEQ_UPDATED) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_RETRANS_STATE[0]) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_RETRANS_STATE[1]) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_RETRANS_STATE[2]) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_RETRANS_SUBSEQ[0]) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_RETRANS_SUBSEQ[1]) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_RETRANS_SUBSEQ[2]) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_RETRANS_SUBSEQ[3]) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_RETRANS_SUBSEQ[4]) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_RETRANS_WDOG_ERR) = (100:100:100, 100:100:100);
    (CORE_CLK => STAT_RX_RETRANS_WRAP_ERR) = (100:100:100, 100:100:100);
    (DRP_CLK => DRP_DO[0]) = (100:100:100, 100:100:100);
    (DRP_CLK => DRP_DO[10]) = (100:100:100, 100:100:100);
    (DRP_CLK => DRP_DO[11]) = (100:100:100, 100:100:100);
    (DRP_CLK => DRP_DO[12]) = (100:100:100, 100:100:100);
    (DRP_CLK => DRP_DO[13]) = (100:100:100, 100:100:100);
    (DRP_CLK => DRP_DO[14]) = (100:100:100, 100:100:100);
    (DRP_CLK => DRP_DO[15]) = (100:100:100, 100:100:100);
    (DRP_CLK => DRP_DO[1]) = (100:100:100, 100:100:100);
    (DRP_CLK => DRP_DO[2]) = (100:100:100, 100:100:100);
    (DRP_CLK => DRP_DO[3]) = (100:100:100, 100:100:100);
    (DRP_CLK => DRP_DO[4]) = (100:100:100, 100:100:100);
    (DRP_CLK => DRP_DO[5]) = (100:100:100, 100:100:100);
    (DRP_CLK => DRP_DO[6]) = (100:100:100, 100:100:100);
    (DRP_CLK => DRP_DO[7]) = (100:100:100, 100:100:100);
    (DRP_CLK => DRP_DO[8]) = (100:100:100, 100:100:100);
    (DRP_CLK => DRP_DO[9]) = (100:100:100, 100:100:100);
    (DRP_CLK => DRP_RDY) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT0[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT0[10]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT0[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT0[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT0[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT0[4]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT0[5]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT0[6]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT0[7]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT0[8]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT0[9]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT1[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT1[10]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT1[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT1[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT1[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT1[4]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT1[5]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT1[6]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT1[7]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT1[8]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT1[9]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT2[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT2[10]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT2[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT2[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT2[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT2[4]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT2[5]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT2[6]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT2[7]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT2[8]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT2[9]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT3[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT3[10]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT3[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT3[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT3[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT3[4]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT3[5]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT3[6]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT3[7]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT3[8]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_CHANOUT3[9]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[100]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[101]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[102]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[103]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[104]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[105]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[106]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[107]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[108]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[109]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[10]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[110]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[111]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[112]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[113]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[114]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[115]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[116]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[117]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[118]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[119]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[11]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[120]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[121]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[122]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[123]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[124]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[125]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[126]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[127]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[12]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[13]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[14]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[15]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[16]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[17]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[18]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[19]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[20]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[21]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[22]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[23]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[24]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[25]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[26]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[27]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[28]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[29]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[30]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[31]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[32]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[33]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[34]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[35]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[36]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[37]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[38]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[39]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[40]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[41]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[42]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[43]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[44]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[45]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[46]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[47]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[48]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[49]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[4]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[50]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[51]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[52]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[53]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[54]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[55]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[56]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[57]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[58]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[59]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[5]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[60]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[61]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[62]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[63]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[64]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[65]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[66]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[67]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[68]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[69]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[6]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[70]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[71]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[72]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[73]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[74]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[75]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[76]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[77]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[78]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[79]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[7]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[80]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[81]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[82]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[83]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[84]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[85]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[86]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[87]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[88]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[89]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[8]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[90]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[91]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[92]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[93]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[94]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[95]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[96]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[97]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[98]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[99]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT0[9]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[100]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[101]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[102]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[103]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[104]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[105]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[106]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[107]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[108]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[109]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[10]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[110]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[111]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[112]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[113]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[114]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[115]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[116]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[117]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[118]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[119]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[11]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[120]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[121]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[122]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[123]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[124]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[125]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[126]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[127]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[12]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[13]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[14]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[15]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[16]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[17]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[18]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[19]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[20]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[21]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[22]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[23]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[24]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[25]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[26]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[27]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[28]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[29]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[30]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[31]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[32]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[33]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[34]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[35]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[36]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[37]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[38]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[39]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[40]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[41]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[42]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[43]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[44]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[45]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[46]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[47]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[48]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[49]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[4]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[50]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[51]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[52]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[53]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[54]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[55]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[56]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[57]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[58]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[59]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[5]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[60]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[61]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[62]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[63]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[64]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[65]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[66]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[67]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[68]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[69]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[6]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[70]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[71]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[72]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[73]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[74]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[75]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[76]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[77]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[78]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[79]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[7]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[80]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[81]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[82]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[83]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[84]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[85]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[86]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[87]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[88]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[89]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[8]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[90]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[91]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[92]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[93]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[94]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[95]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[96]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[97]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[98]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[99]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT1[9]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[100]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[101]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[102]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[103]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[104]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[105]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[106]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[107]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[108]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[109]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[10]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[110]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[111]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[112]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[113]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[114]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[115]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[116]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[117]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[118]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[119]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[11]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[120]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[121]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[122]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[123]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[124]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[125]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[126]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[127]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[12]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[13]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[14]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[15]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[16]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[17]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[18]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[19]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[20]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[21]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[22]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[23]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[24]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[25]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[26]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[27]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[28]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[29]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[30]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[31]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[32]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[33]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[34]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[35]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[36]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[37]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[38]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[39]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[40]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[41]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[42]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[43]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[44]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[45]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[46]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[47]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[48]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[49]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[4]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[50]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[51]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[52]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[53]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[54]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[55]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[56]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[57]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[58]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[59]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[5]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[60]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[61]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[62]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[63]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[64]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[65]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[66]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[67]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[68]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[69]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[6]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[70]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[71]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[72]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[73]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[74]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[75]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[76]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[77]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[78]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[79]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[7]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[80]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[81]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[82]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[83]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[84]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[85]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[86]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[87]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[88]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[89]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[8]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[90]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[91]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[92]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[93]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[94]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[95]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[96]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[97]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[98]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[99]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT2[9]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[100]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[101]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[102]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[103]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[104]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[105]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[106]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[107]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[108]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[109]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[10]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[110]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[111]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[112]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[113]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[114]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[115]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[116]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[117]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[118]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[119]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[11]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[120]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[121]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[122]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[123]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[124]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[125]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[126]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[127]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[12]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[13]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[14]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[15]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[16]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[17]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[18]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[19]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[20]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[21]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[22]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[23]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[24]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[25]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[26]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[27]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[28]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[29]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[30]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[31]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[32]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[33]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[34]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[35]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[36]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[37]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[38]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[39]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[40]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[41]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[42]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[43]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[44]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[45]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[46]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[47]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[48]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[49]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[4]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[50]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[51]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[52]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[53]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[54]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[55]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[56]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[57]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[58]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[59]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[5]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[60]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[61]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[62]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[63]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[64]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[65]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[66]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[67]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[68]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[69]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[6]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[70]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[71]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[72]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[73]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[74]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[75]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[76]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[77]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[78]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[79]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[7]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[80]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[81]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[82]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[83]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[84]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[85]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[86]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[87]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[88]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[89]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[8]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[90]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[91]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[92]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[93]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[94]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[95]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[96]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[97]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[98]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[99]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_DATAOUT3[9]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_ENAOUT0) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_ENAOUT1) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_ENAOUT2) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_ENAOUT3) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_EOPOUT0) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_EOPOUT1) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_EOPOUT2) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_EOPOUT3) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_ERROUT0) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_ERROUT1) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_ERROUT2) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_ERROUT3) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_MTYOUT0[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_MTYOUT0[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_MTYOUT0[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_MTYOUT0[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_MTYOUT1[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_MTYOUT1[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_MTYOUT1[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_MTYOUT1[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_MTYOUT2[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_MTYOUT2[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_MTYOUT2[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_MTYOUT2[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_MTYOUT3[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_MTYOUT3[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_MTYOUT3[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_MTYOUT3[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_OVFOUT) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_SOPOUT0) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_SOPOUT1) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_SOPOUT2) = (100:100:100, 100:100:100);
    (LBUS_CLK => RX_SOPOUT3) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_ALIGNED) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_ALIGNED_ERR) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_BAD_TYPE_ERR[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_BAD_TYPE_ERR[10]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_BAD_TYPE_ERR[11]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_BAD_TYPE_ERR[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_BAD_TYPE_ERR[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_BAD_TYPE_ERR[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_BAD_TYPE_ERR[4]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_BAD_TYPE_ERR[5]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_BAD_TYPE_ERR[6]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_BAD_TYPE_ERR[7]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_BAD_TYPE_ERR[8]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_BAD_TYPE_ERR[9]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_BURSTMAX_ERR) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_BURST_ERR) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_CRC24_ERR) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_CRC32_ERR[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_CRC32_ERR[10]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_CRC32_ERR[11]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_CRC32_ERR[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_CRC32_ERR[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_CRC32_ERR[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_CRC32_ERR[4]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_CRC32_ERR[5]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_CRC32_ERR[6]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_CRC32_ERR[7]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_CRC32_ERR[8]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_CRC32_ERR[9]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_CRC32_VALID[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_CRC32_VALID[10]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_CRC32_VALID[11]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_CRC32_VALID[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_CRC32_VALID[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_CRC32_VALID[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_CRC32_VALID[4]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_CRC32_VALID[5]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_CRC32_VALID[6]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_CRC32_VALID[7]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_CRC32_VALID[8]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_CRC32_VALID[9]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DESCRAM_ERR[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DESCRAM_ERR[10]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DESCRAM_ERR[11]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DESCRAM_ERR[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DESCRAM_ERR[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DESCRAM_ERR[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DESCRAM_ERR[4]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DESCRAM_ERR[5]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DESCRAM_ERR[6]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DESCRAM_ERR[7]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DESCRAM_ERR[8]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DESCRAM_ERR[9]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DIAGWORD_INTFSTAT[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DIAGWORD_INTFSTAT[10]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DIAGWORD_INTFSTAT[11]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DIAGWORD_INTFSTAT[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DIAGWORD_INTFSTAT[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DIAGWORD_INTFSTAT[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DIAGWORD_INTFSTAT[4]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DIAGWORD_INTFSTAT[5]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DIAGWORD_INTFSTAT[6]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DIAGWORD_INTFSTAT[7]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DIAGWORD_INTFSTAT[8]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DIAGWORD_INTFSTAT[9]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DIAGWORD_LANESTAT[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DIAGWORD_LANESTAT[10]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DIAGWORD_LANESTAT[11]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DIAGWORD_LANESTAT[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DIAGWORD_LANESTAT[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DIAGWORD_LANESTAT[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DIAGWORD_LANESTAT[4]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DIAGWORD_LANESTAT[5]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DIAGWORD_LANESTAT[6]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DIAGWORD_LANESTAT[7]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DIAGWORD_LANESTAT[8]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_DIAGWORD_LANESTAT[9]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[100]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[101]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[102]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[103]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[104]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[105]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[106]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[107]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[108]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[109]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[10]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[110]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[111]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[112]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[113]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[114]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[115]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[116]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[117]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[118]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[119]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[11]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[120]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[121]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[122]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[123]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[124]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[125]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[126]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[127]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[128]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[129]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[12]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[130]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[131]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[132]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[133]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[134]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[135]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[136]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[137]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[138]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[139]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[13]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[140]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[141]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[142]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[143]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[144]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[145]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[146]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[147]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[148]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[149]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[14]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[150]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[151]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[152]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[153]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[154]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[155]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[156]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[157]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[158]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[159]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[15]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[160]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[161]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[162]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[163]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[164]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[165]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[166]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[167]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[168]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[169]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[16]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[170]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[171]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[172]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[173]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[174]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[175]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[176]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[177]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[178]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[179]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[17]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[180]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[181]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[182]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[183]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[184]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[185]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[186]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[187]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[188]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[189]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[18]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[190]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[191]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[192]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[193]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[194]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[195]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[196]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[197]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[198]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[199]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[19]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[200]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[201]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[202]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[203]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[204]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[205]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[206]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[207]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[208]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[209]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[20]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[210]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[211]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[212]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[213]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[214]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[215]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[216]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[217]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[218]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[219]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[21]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[220]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[221]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[222]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[223]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[224]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[225]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[226]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[227]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[228]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[229]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[22]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[230]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[231]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[232]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[233]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[234]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[235]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[236]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[237]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[238]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[239]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[23]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[240]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[241]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[242]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[243]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[244]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[245]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[246]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[247]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[248]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[249]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[24]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[250]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[251]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[252]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[253]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[254]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[255]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[25]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[26]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[27]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[28]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[29]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[30]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[31]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[32]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[33]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[34]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[35]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[36]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[37]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[38]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[39]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[40]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[41]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[42]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[43]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[44]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[45]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[46]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[47]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[48]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[49]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[4]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[50]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[51]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[52]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[53]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[54]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[55]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[56]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[57]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[58]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[59]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[5]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[60]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[61]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[62]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[63]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[64]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[65]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[66]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[67]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[68]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[69]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[6]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[70]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[71]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[72]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[73]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[74]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[75]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[76]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[77]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[78]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[79]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[7]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[80]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[81]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[82]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[83]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[84]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[85]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[86]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[87]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[88]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[89]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[8]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[90]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[91]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[92]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[93]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[94]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[95]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[96]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[97]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[98]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[99]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FC_STAT[9]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FRAMING_ERR[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FRAMING_ERR[10]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FRAMING_ERR[11]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FRAMING_ERR[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FRAMING_ERR[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FRAMING_ERR[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FRAMING_ERR[4]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FRAMING_ERR[5]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FRAMING_ERR[6]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FRAMING_ERR[7]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FRAMING_ERR[8]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_FRAMING_ERR[9]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MEOP_ERR) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_ERR[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_ERR[10]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_ERR[11]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_ERR[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_ERR[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_ERR[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_ERR[4]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_ERR[5]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_ERR[6]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_ERR[7]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_ERR[8]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_ERR[9]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_LEN_ERR[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_LEN_ERR[10]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_LEN_ERR[11]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_LEN_ERR[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_LEN_ERR[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_LEN_ERR[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_LEN_ERR[4]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_LEN_ERR[5]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_LEN_ERR[6]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_LEN_ERR[7]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_LEN_ERR[8]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_LEN_ERR[9]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_REPEAT_ERR[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_REPEAT_ERR[10]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_REPEAT_ERR[11]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_REPEAT_ERR[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_REPEAT_ERR[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_REPEAT_ERR[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_REPEAT_ERR[4]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_REPEAT_ERR[5]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_REPEAT_ERR[6]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_REPEAT_ERR[7]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_REPEAT_ERR[8]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MF_REPEAT_ERR[9]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MISALIGNED) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MSOP_ERR) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MUBITS[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MUBITS[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MUBITS[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MUBITS[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MUBITS[4]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MUBITS[5]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MUBITS[6]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MUBITS[7]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_MUBITS_UPDATED) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_OVERFLOW_ERR) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_RETRANS_LATENCY[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_RETRANS_LATENCY[10]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_RETRANS_LATENCY[11]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_RETRANS_LATENCY[12]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_RETRANS_LATENCY[13]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_RETRANS_LATENCY[14]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_RETRANS_LATENCY[15]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_RETRANS_LATENCY[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_RETRANS_LATENCY[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_RETRANS_LATENCY[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_RETRANS_LATENCY[4]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_RETRANS_LATENCY[5]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_RETRANS_LATENCY[6]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_RETRANS_LATENCY[7]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_RETRANS_LATENCY[8]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_RETRANS_LATENCY[9]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_RETRANS_REQ) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_SYNCED[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_SYNCED[10]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_SYNCED[11]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_SYNCED[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_SYNCED[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_SYNCED[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_SYNCED[4]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_SYNCED[5]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_SYNCED[6]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_SYNCED[7]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_SYNCED[8]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_SYNCED[9]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_SYNCED_ERR[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_SYNCED_ERR[10]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_SYNCED_ERR[11]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_SYNCED_ERR[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_SYNCED_ERR[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_SYNCED_ERR[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_SYNCED_ERR[4]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_SYNCED_ERR[5]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_SYNCED_ERR[6]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_SYNCED_ERR[7]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_SYNCED_ERR[8]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_SYNCED_ERR[9]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_WORD_SYNC[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_WORD_SYNC[10]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_WORD_SYNC[11]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_WORD_SYNC[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_WORD_SYNC[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_WORD_SYNC[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_WORD_SYNC[4]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_WORD_SYNC[5]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_WORD_SYNC[6]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_WORD_SYNC[7]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_WORD_SYNC[8]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_RX_WORD_SYNC[9]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_BURST_ERR) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_ERRINJ_BITERR_DONE) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_OVERFLOW_ERR) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_BURST_ERR) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_BUSY) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_PERROUT) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_RADDR[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_RADDR[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_RADDR[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_RADDR[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_RADDR[4]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_RADDR[5]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_RADDR[6]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_RADDR[7]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_RADDR[8]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_RD_B0) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_RD_B1) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_RD_B2) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_RD_B3) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_RSEL[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_RSEL[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WADDR[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WADDR[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WADDR[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WADDR[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WADDR[4]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WADDR[5]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WADDR[6]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WADDR[7]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WADDR[8]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[0]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[100]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[101]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[102]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[103]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[104]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[105]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[106]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[107]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[108]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[109]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[10]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[110]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[111]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[112]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[113]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[114]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[115]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[116]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[117]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[118]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[119]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[11]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[120]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[121]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[122]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[123]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[124]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[125]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[126]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[127]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[128]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[129]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[12]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[130]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[131]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[132]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[133]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[134]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[135]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[136]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[137]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[138]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[139]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[13]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[140]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[141]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[142]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[143]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[144]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[145]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[146]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[147]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[148]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[149]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[14]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[150]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[151]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[152]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[153]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[154]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[155]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[156]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[157]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[158]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[159]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[15]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[160]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[161]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[162]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[163]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[164]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[165]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[166]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[167]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[168]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[169]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[16]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[170]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[171]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[172]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[173]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[174]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[175]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[176]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[177]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[178]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[179]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[17]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[180]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[181]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[182]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[183]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[184]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[185]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[186]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[187]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[188]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[189]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[18]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[190]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[191]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[192]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[193]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[194]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[195]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[196]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[197]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[198]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[199]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[19]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[1]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[200]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[201]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[202]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[203]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[204]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[205]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[206]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[207]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[208]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[209]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[20]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[210]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[211]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[212]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[213]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[214]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[215]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[216]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[217]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[218]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[219]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[21]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[220]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[221]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[222]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[223]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[224]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[225]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[226]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[227]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[228]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[229]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[22]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[230]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[231]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[232]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[233]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[234]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[235]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[236]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[237]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[238]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[239]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[23]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[240]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[241]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[242]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[243]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[244]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[245]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[246]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[247]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[248]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[249]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[24]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[250]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[251]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[252]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[253]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[254]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[255]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[256]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[257]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[258]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[259]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[25]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[260]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[261]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[262]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[263]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[264]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[265]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[266]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[267]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[268]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[269]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[26]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[270]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[271]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[272]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[273]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[274]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[275]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[276]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[277]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[278]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[279]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[27]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[280]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[281]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[282]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[283]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[284]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[285]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[286]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[287]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[288]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[289]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[28]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[290]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[291]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[292]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[293]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[294]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[295]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[296]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[297]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[298]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[299]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[29]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[2]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[300]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[301]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[302]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[303]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[304]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[305]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[306]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[307]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[308]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[309]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[30]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[310]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[311]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[312]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[313]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[314]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[315]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[316]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[317]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[318]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[319]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[31]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[320]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[321]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[322]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[323]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[324]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[325]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[326]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[327]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[328]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[329]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[32]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[330]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[331]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[332]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[333]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[334]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[335]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[336]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[337]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[338]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[339]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[33]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[340]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[341]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[342]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[343]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[344]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[345]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[346]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[347]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[348]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[349]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[34]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[350]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[351]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[352]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[353]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[354]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[355]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[356]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[357]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[358]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[359]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[35]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[360]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[361]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[362]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[363]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[364]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[365]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[366]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[367]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[368]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[369]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[36]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[370]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[371]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[372]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[373]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[374]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[375]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[376]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[377]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[378]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[379]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[37]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[380]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[381]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[382]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[383]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[384]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[385]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[386]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[387]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[388]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[389]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[38]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[390]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[391]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[392]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[393]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[394]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[395]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[396]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[397]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[398]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[399]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[39]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[3]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[400]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[401]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[402]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[403]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[404]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[405]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[406]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[407]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[408]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[409]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[40]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[410]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[411]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[412]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[413]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[414]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[415]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[416]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[417]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[418]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[419]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[41]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[420]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[421]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[422]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[423]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[424]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[425]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[426]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[427]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[428]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[429]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[42]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[430]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[431]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[432]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[433]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[434]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[435]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[436]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[437]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[438]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[439]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[43]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[440]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[441]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[442]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[443]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[444]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[445]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[446]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[447]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[448]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[449]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[44]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[450]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[451]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[452]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[453]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[454]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[455]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[456]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[457]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[458]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[459]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[45]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[460]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[461]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[462]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[463]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[464]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[465]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[466]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[467]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[468]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[469]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[46]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[470]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[471]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[472]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[473]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[474]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[475]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[476]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[477]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[478]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[479]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[47]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[480]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[481]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[482]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[483]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[484]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[485]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[486]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[487]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[488]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[489]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[48]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[490]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[491]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[492]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[493]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[494]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[495]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[496]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[497]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[498]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[499]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[49]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[4]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[500]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[501]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[502]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[503]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[504]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[505]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[506]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[507]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[508]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[509]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[50]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[510]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[511]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[512]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[513]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[514]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[515]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[516]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[517]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[518]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[519]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[51]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[520]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[521]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[522]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[523]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[524]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[525]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[526]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[527]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[528]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[529]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[52]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[530]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[531]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[532]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[533]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[534]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[535]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[536]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[537]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[538]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[539]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[53]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[540]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[541]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[542]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[543]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[544]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[545]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[546]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[547]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[548]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[549]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[54]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[550]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[551]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[552]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[553]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[554]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[555]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[556]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[557]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[558]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[559]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[55]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[560]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[561]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[562]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[563]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[564]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[565]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[566]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[567]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[568]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[569]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[56]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[570]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[571]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[572]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[573]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[574]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[575]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[576]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[577]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[578]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[579]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[57]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[580]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[581]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[582]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[583]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[584]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[585]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[586]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[587]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[588]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[589]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[58]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[590]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[591]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[592]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[593]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[594]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[595]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[596]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[597]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[598]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[599]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[59]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[5]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[600]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[601]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[602]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[603]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[604]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[605]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[606]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[607]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[608]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[609]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[60]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[610]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[611]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[612]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[613]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[614]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[615]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[616]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[617]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[618]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[619]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[61]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[620]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[621]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[622]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[623]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[624]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[625]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[626]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[627]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[628]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[629]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[62]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[630]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[631]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[632]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[633]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[634]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[635]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[636]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[637]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[638]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[639]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[63]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[640]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[641]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[642]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[643]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[64]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[65]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[66]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[67]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[68]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[69]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[6]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[70]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[71]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[72]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[73]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[74]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[75]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[76]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[77]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[78]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[79]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[7]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[80]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[81]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[82]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[83]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[84]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[85]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[86]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[87]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[88]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[89]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[8]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[90]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[91]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[92]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[93]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[94]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[95]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[96]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[97]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[98]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[99]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WDATA[9]) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WE_B0) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WE_B1) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WE_B2) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_RETRANS_RAM_WE_B3) = (100:100:100, 100:100:100);
    (LBUS_CLK => STAT_TX_UNDERFLOW_ERR) = (100:100:100, 100:100:100);
    (LBUS_CLK => TX_OVFOUT) = (100:100:100, 100:100:100);
    (LBUS_CLK => TX_RDYOUT) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[0]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[10]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[11]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[12]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[13]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[14]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[15]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[16]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[17]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[18]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[19]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[1]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[20]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[21]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[22]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[23]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[24]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[25]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[26]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[27]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[28]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[29]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[2]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[30]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[31]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[32]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[33]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[34]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[35]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[36]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[37]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[38]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[39]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[3]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[40]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[41]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[42]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[43]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[44]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[45]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[46]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[47]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[48]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[49]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[4]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[50]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[51]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[52]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[53]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[54]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[55]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[56]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[57]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[58]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[59]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[5]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[60]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[61]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[62]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[63]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[6]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[7]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[8]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA00[9]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[0]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[10]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[11]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[12]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[13]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[14]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[15]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[16]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[17]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[18]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[19]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[1]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[20]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[21]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[22]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[23]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[24]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[25]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[26]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[27]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[28]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[29]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[2]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[30]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[31]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[32]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[33]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[34]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[35]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[36]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[37]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[38]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[39]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[3]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[40]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[41]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[42]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[43]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[44]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[45]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[46]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[47]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[48]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[49]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[4]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[50]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[51]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[52]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[53]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[54]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[55]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[56]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[57]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[58]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[59]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[5]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[60]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[61]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[62]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[63]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[6]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[7]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[8]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA01[9]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[0]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[10]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[11]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[12]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[13]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[14]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[15]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[16]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[17]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[18]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[19]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[1]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[20]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[21]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[22]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[23]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[24]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[25]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[26]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[27]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[28]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[29]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[2]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[30]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[31]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[32]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[33]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[34]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[35]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[36]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[37]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[38]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[39]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[3]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[40]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[41]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[42]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[43]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[44]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[45]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[46]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[47]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[48]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[49]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[4]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[50]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[51]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[52]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[53]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[54]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[55]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[56]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[57]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[58]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[59]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[5]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[60]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[61]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[62]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[63]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[6]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[7]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[8]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA02[9]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[0]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[10]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[11]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[12]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[13]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[14]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[15]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[16]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[17]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[18]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[19]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[1]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[20]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[21]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[22]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[23]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[24]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[25]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[26]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[27]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[28]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[29]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[2]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[30]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[31]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[32]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[33]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[34]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[35]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[36]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[37]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[38]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[39]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[3]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[40]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[41]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[42]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[43]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[44]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[45]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[46]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[47]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[48]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[49]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[4]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[50]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[51]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[52]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[53]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[54]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[55]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[56]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[57]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[58]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[59]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[5]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[60]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[61]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[62]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[63]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[6]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[7]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[8]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA03[9]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[0]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[10]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[11]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[12]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[13]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[14]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[15]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[16]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[17]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[18]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[19]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[1]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[20]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[21]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[22]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[23]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[24]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[25]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[26]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[27]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[28]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[29]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[2]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[30]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[31]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[32]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[33]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[34]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[35]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[36]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[37]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[38]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[39]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[3]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[40]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[41]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[42]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[43]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[44]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[45]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[46]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[47]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[48]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[49]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[4]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[50]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[51]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[52]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[53]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[54]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[55]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[56]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[57]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[58]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[59]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[5]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[60]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[61]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[62]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[63]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[6]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[7]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[8]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA04[9]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[0]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[10]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[11]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[12]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[13]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[14]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[15]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[16]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[17]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[18]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[19]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[1]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[20]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[21]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[22]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[23]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[24]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[25]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[26]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[27]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[28]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[29]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[2]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[30]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[31]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[32]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[33]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[34]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[35]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[36]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[37]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[38]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[39]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[3]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[40]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[41]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[42]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[43]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[44]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[45]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[46]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[47]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[48]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[49]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[4]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[50]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[51]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[52]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[53]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[54]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[55]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[56]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[57]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[58]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[59]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[5]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[60]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[61]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[62]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[63]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[6]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[7]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[8]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA05[9]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[0]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[10]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[11]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[12]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[13]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[14]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[15]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[16]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[17]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[18]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[19]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[1]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[20]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[21]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[22]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[23]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[24]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[25]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[26]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[27]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[28]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[29]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[2]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[30]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[31]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[32]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[33]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[34]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[35]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[36]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[37]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[38]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[39]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[3]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[40]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[41]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[42]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[43]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[44]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[45]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[46]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[47]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[48]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[49]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[4]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[50]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[51]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[52]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[53]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[54]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[55]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[56]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[57]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[58]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[59]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[5]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[60]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[61]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[62]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[63]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[6]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[7]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[8]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA06[9]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[0]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[10]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[11]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[12]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[13]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[14]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[15]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[16]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[17]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[18]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[19]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[1]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[20]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[21]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[22]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[23]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[24]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[25]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[26]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[27]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[28]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[29]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[2]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[30]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[31]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[32]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[33]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[34]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[35]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[36]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[37]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[38]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[39]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[3]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[40]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[41]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[42]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[43]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[44]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[45]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[46]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[47]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[48]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[49]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[4]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[50]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[51]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[52]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[53]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[54]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[55]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[56]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[57]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[58]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[59]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[5]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[60]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[61]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[62]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[63]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[6]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[7]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[8]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA07[9]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[0]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[10]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[11]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[12]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[13]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[14]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[15]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[16]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[17]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[18]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[19]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[1]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[20]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[21]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[22]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[23]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[24]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[25]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[26]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[27]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[28]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[29]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[2]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[30]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[31]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[32]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[33]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[34]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[35]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[36]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[37]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[38]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[39]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[3]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[40]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[41]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[42]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[43]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[44]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[45]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[46]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[47]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[48]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[49]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[4]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[50]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[51]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[52]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[53]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[54]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[55]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[56]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[57]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[58]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[59]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[5]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[60]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[61]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[62]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[63]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[6]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[7]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[8]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA08[9]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[0]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[10]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[11]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[12]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[13]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[14]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[15]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[16]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[17]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[18]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[19]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[1]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[20]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[21]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[22]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[23]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[24]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[25]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[26]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[27]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[28]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[29]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[2]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[30]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[31]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[32]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[33]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[34]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[35]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[36]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[37]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[38]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[39]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[3]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[40]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[41]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[42]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[43]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[44]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[45]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[46]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[47]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[48]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[49]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[4]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[50]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[51]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[52]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[53]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[54]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[55]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[56]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[57]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[58]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[59]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[5]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[60]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[61]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[62]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[63]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[6]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[7]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[8]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA09[9]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[0]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[10]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[11]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[12]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[13]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[14]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[15]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[16]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[17]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[18]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[19]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[1]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[20]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[21]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[22]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[23]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[24]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[25]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[26]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[27]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[28]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[29]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[2]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[30]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[31]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[32]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[33]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[34]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[35]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[36]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[37]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[38]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[39]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[3]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[40]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[41]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[42]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[43]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[44]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[45]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[46]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[47]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[48]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[49]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[4]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[50]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[51]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[52]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[53]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[54]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[55]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[56]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[57]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[58]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[59]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[5]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[60]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[61]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[62]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[63]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[6]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[7]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[8]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA10[9]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[0]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[10]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[11]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[12]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[13]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[14]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[15]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[16]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[17]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[18]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[19]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[1]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[20]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[21]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[22]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[23]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[24]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[25]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[26]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[27]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[28]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[29]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[2]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[30]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[31]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[32]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[33]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[34]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[35]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[36]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[37]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[38]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[39]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[3]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[40]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[41]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[42]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[43]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[44]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[45]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[46]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[47]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[48]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[49]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[4]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[50]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[51]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[52]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[53]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[54]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[55]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[56]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[57]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[58]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[59]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[5]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[60]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[61]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[62]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[63]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[6]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[7]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[8]) = (100:100:100, 100:100:100);
    (TX_SERDES_REFCLK => TX_SERDES_DATA11[9]) = (100:100:100, 100:100:100);






























































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































    specparam PATHPULSE$ = 0;
  endspecify

endmodule

`endcelldefine

