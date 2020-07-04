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
//  /   /                        100G MAC Block
// /___/   /\      Filename    : CMAC.v
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

module CMAC #(



  parameter CTL_PTP_TRANSPCLK_MODE = "FALSE",
  parameter CTL_RX_CHECK_ACK = "TRUE",
  parameter CTL_RX_CHECK_PREAMBLE = "FALSE",
  parameter CTL_RX_CHECK_SFD = "FALSE",
  parameter CTL_RX_DELETE_FCS = "TRUE",
  parameter [15:0] CTL_RX_ETYPE_GCP = 16'h8808,
  parameter [15:0] CTL_RX_ETYPE_GPP = 16'h8808,
  parameter [15:0] CTL_RX_ETYPE_PCP = 16'h8808,
  parameter [15:0] CTL_RX_ETYPE_PPP = 16'h8808,
  parameter CTL_RX_FORWARD_CONTROL = "FALSE",
  parameter CTL_RX_IGNORE_FCS = "FALSE",
  parameter [14:0] CTL_RX_MAX_PACKET_LEN = 15'h2580,
  parameter [7:0] CTL_RX_MIN_PACKET_LEN = 8'h40,
  parameter [15:0] CTL_RX_OPCODE_GPP = 16'h0001,
  parameter [15:0] CTL_RX_OPCODE_MAX_GCP = 16'hFFFF,
  parameter [15:0] CTL_RX_OPCODE_MAX_PCP = 16'hFFFF,
  parameter [15:0] CTL_RX_OPCODE_MIN_GCP = 16'h0000,
  parameter [15:0] CTL_RX_OPCODE_MIN_PCP = 16'h0000,
  parameter [15:0] CTL_RX_OPCODE_PPP = 16'h0001,
  parameter [47:0] CTL_RX_PAUSE_DA_MCAST = 48'h0180C2000001,
  parameter [47:0] CTL_RX_PAUSE_DA_UCAST = 48'h000000000000,
  parameter [47:0] CTL_RX_PAUSE_SA = 48'h000000000000,
  parameter CTL_RX_PROCESS_LFI = "FALSE",
  parameter [15:0] CTL_RX_VL_LENGTH_MINUS1 = 16'h3FFF,
  parameter [63:0] CTL_RX_VL_MARKER_ID0 = 64'hC16821003E97DE00,
  parameter [63:0] CTL_RX_VL_MARKER_ID1 = 64'h9D718E00628E7100,
  parameter [63:0] CTL_RX_VL_MARKER_ID10 = 64'hFD6C990002936600,
  parameter [63:0] CTL_RX_VL_MARKER_ID11 = 64'hB9915500466EAA00,
  parameter [63:0] CTL_RX_VL_MARKER_ID12 = 64'h5CB9B200A3464D00,
  parameter [63:0] CTL_RX_VL_MARKER_ID13 = 64'h1AF8BD00E5074200,
  parameter [63:0] CTL_RX_VL_MARKER_ID14 = 64'h83C7CA007C383500,
  parameter [63:0] CTL_RX_VL_MARKER_ID15 = 64'h3536CD00CAC93200,
  parameter [63:0] CTL_RX_VL_MARKER_ID16 = 64'hC4314C003BCEB300,
  parameter [63:0] CTL_RX_VL_MARKER_ID17 = 64'hADD6B70052294800,
  parameter [63:0] CTL_RX_VL_MARKER_ID18 = 64'h5F662A00A099D500,
  parameter [63:0] CTL_RX_VL_MARKER_ID19 = 64'hC0F0E5003F0F1A00,
  parameter [63:0] CTL_RX_VL_MARKER_ID2 = 64'h594BE800A6B41700,
  parameter [63:0] CTL_RX_VL_MARKER_ID3 = 64'h4D957B00B26A8400,
  parameter [63:0] CTL_RX_VL_MARKER_ID4 = 64'hF50709000AF8F600,
  parameter [63:0] CTL_RX_VL_MARKER_ID5 = 64'hDD14C20022EB3D00,
  parameter [63:0] CTL_RX_VL_MARKER_ID6 = 64'h9A4A260065B5D900,
  parameter [63:0] CTL_RX_VL_MARKER_ID7 = 64'h7B45660084BA9900,
  parameter [63:0] CTL_RX_VL_MARKER_ID8 = 64'hA02476005FDB8900,
  parameter [63:0] CTL_RX_VL_MARKER_ID9 = 64'h68C9FB0097360400,
  parameter CTL_TEST_MODE_PIN_CHAR = "FALSE",
  parameter [47:0] CTL_TX_DA_GPP = 48'h0180C2000001,
  parameter [47:0] CTL_TX_DA_PPP = 48'h0180C2000001,
  parameter [15:0] CTL_TX_ETHERTYPE_GPP = 16'h8808,
  parameter [15:0] CTL_TX_ETHERTYPE_PPP = 16'h8808,
  parameter CTL_TX_FCS_INS_ENABLE = "TRUE",
  parameter CTL_TX_IGNORE_FCS = "FALSE",
  parameter [15:0] CTL_TX_OPCODE_GPP = 16'h0001,
  parameter [15:0] CTL_TX_OPCODE_PPP = 16'h0001,
  parameter CTL_TX_PTP_1STEP_ENABLE = "FALSE",
  parameter [10:0] CTL_TX_PTP_LATENCY_ADJUST = 11'h2C1,
  parameter [47:0] CTL_TX_SA_GPP = 48'h000000000000,
  parameter [47:0] CTL_TX_SA_PPP = 48'h000000000000,
  parameter [15:0] CTL_TX_VL_LENGTH_MINUS1 = 16'h3FFF,
  parameter [63:0] CTL_TX_VL_MARKER_ID0 = 64'hC16821003E97DE00,
  parameter [63:0] CTL_TX_VL_MARKER_ID1 = 64'h9D718E00628E7100,
  parameter [63:0] CTL_TX_VL_MARKER_ID10 = 64'hFD6C990002936600,
  parameter [63:0] CTL_TX_VL_MARKER_ID11 = 64'hB9915500466EAA00,
  parameter [63:0] CTL_TX_VL_MARKER_ID12 = 64'h5CB9B200A3464D00,
  parameter [63:0] CTL_TX_VL_MARKER_ID13 = 64'h1AF8BD00E5074200,
  parameter [63:0] CTL_TX_VL_MARKER_ID14 = 64'h83C7CA007C383500,
  parameter [63:0] CTL_TX_VL_MARKER_ID15 = 64'h3536CD00CAC93200,
  parameter [63:0] CTL_TX_VL_MARKER_ID16 = 64'hC4314C003BCEB300,
  parameter [63:0] CTL_TX_VL_MARKER_ID17 = 64'hADD6B70052294800,
  parameter [63:0] CTL_TX_VL_MARKER_ID18 = 64'h5F662A00A099D500,
  parameter [63:0] CTL_TX_VL_MARKER_ID19 = 64'hC0F0E5003F0F1A00,
  parameter [63:0] CTL_TX_VL_MARKER_ID2 = 64'h594BE800A6B41700,
  parameter [63:0] CTL_TX_VL_MARKER_ID3 = 64'h4D957B00B26A8400,
  parameter [63:0] CTL_TX_VL_MARKER_ID4 = 64'hF50709000AF8F600,
  parameter [63:0] CTL_TX_VL_MARKER_ID5 = 64'hDD14C20022EB3D00,
  parameter [63:0] CTL_TX_VL_MARKER_ID6 = 64'h9A4A260065B5D900,
  parameter [63:0] CTL_TX_VL_MARKER_ID7 = 64'h7B45660084BA9900,
  parameter [63:0] CTL_TX_VL_MARKER_ID8 = 64'hA02476005FDB8900,
  parameter [63:0] CTL_TX_VL_MARKER_ID9 = 64'h68C9FB0097360400,
  parameter SIM_VERSION = "2.0",
  parameter TEST_MODE_PIN_CHAR = "FALSE"
)(
  output [15:0] DRP_DO,
  output DRP_RDY,
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
  output [6:0] RX_LANE_ALIGNER_FILL_0,
  output [6:0] RX_LANE_ALIGNER_FILL_1,
  output [6:0] RX_LANE_ALIGNER_FILL_10,
  output [6:0] RX_LANE_ALIGNER_FILL_11,
  output [6:0] RX_LANE_ALIGNER_FILL_12,
  output [6:0] RX_LANE_ALIGNER_FILL_13,
  output [6:0] RX_LANE_ALIGNER_FILL_14,
  output [6:0] RX_LANE_ALIGNER_FILL_15,
  output [6:0] RX_LANE_ALIGNER_FILL_16,
  output [6:0] RX_LANE_ALIGNER_FILL_17,
  output [6:0] RX_LANE_ALIGNER_FILL_18,
  output [6:0] RX_LANE_ALIGNER_FILL_19,
  output [6:0] RX_LANE_ALIGNER_FILL_2,
  output [6:0] RX_LANE_ALIGNER_FILL_3,
  output [6:0] RX_LANE_ALIGNER_FILL_4,
  output [6:0] RX_LANE_ALIGNER_FILL_5,
  output [6:0] RX_LANE_ALIGNER_FILL_6,
  output [6:0] RX_LANE_ALIGNER_FILL_7,
  output [6:0] RX_LANE_ALIGNER_FILL_8,
  output [6:0] RX_LANE_ALIGNER_FILL_9,
  output [3:0] RX_MTYOUT0,
  output [3:0] RX_MTYOUT1,
  output [3:0] RX_MTYOUT2,
  output [3:0] RX_MTYOUT3,
  output [4:0] RX_PTP_PCSLANE_OUT,
  output [79:0] RX_PTP_TSTAMP_OUT,
  output RX_SOPOUT0,
  output RX_SOPOUT1,
  output RX_SOPOUT2,
  output RX_SOPOUT3,
  output STAT_RX_ALIGNED,
  output STAT_RX_ALIGNED_ERR,
  output [6:0] STAT_RX_BAD_CODE,
  output [3:0] STAT_RX_BAD_FCS,
  output STAT_RX_BAD_PREAMBLE,
  output STAT_RX_BAD_SFD,
  output STAT_RX_BIP_ERR_0,
  output STAT_RX_BIP_ERR_1,
  output STAT_RX_BIP_ERR_10,
  output STAT_RX_BIP_ERR_11,
  output STAT_RX_BIP_ERR_12,
  output STAT_RX_BIP_ERR_13,
  output STAT_RX_BIP_ERR_14,
  output STAT_RX_BIP_ERR_15,
  output STAT_RX_BIP_ERR_16,
  output STAT_RX_BIP_ERR_17,
  output STAT_RX_BIP_ERR_18,
  output STAT_RX_BIP_ERR_19,
  output STAT_RX_BIP_ERR_2,
  output STAT_RX_BIP_ERR_3,
  output STAT_RX_BIP_ERR_4,
  output STAT_RX_BIP_ERR_5,
  output STAT_RX_BIP_ERR_6,
  output STAT_RX_BIP_ERR_7,
  output STAT_RX_BIP_ERR_8,
  output STAT_RX_BIP_ERR_9,
  output [19:0] STAT_RX_BLOCK_LOCK,
  output STAT_RX_BROADCAST,
  output [3:0] STAT_RX_FRAGMENT,
  output [3:0] STAT_RX_FRAMING_ERR_0,
  output [3:0] STAT_RX_FRAMING_ERR_1,
  output [3:0] STAT_RX_FRAMING_ERR_10,
  output [3:0] STAT_RX_FRAMING_ERR_11,
  output [3:0] STAT_RX_FRAMING_ERR_12,
  output [3:0] STAT_RX_FRAMING_ERR_13,
  output [3:0] STAT_RX_FRAMING_ERR_14,
  output [3:0] STAT_RX_FRAMING_ERR_15,
  output [3:0] STAT_RX_FRAMING_ERR_16,
  output [3:0] STAT_RX_FRAMING_ERR_17,
  output [3:0] STAT_RX_FRAMING_ERR_18,
  output [3:0] STAT_RX_FRAMING_ERR_19,
  output [3:0] STAT_RX_FRAMING_ERR_2,
  output [3:0] STAT_RX_FRAMING_ERR_3,
  output [3:0] STAT_RX_FRAMING_ERR_4,
  output [3:0] STAT_RX_FRAMING_ERR_5,
  output [3:0] STAT_RX_FRAMING_ERR_6,
  output [3:0] STAT_RX_FRAMING_ERR_7,
  output [3:0] STAT_RX_FRAMING_ERR_8,
  output [3:0] STAT_RX_FRAMING_ERR_9,
  output STAT_RX_FRAMING_ERR_VALID_0,
  output STAT_RX_FRAMING_ERR_VALID_1,
  output STAT_RX_FRAMING_ERR_VALID_10,
  output STAT_RX_FRAMING_ERR_VALID_11,
  output STAT_RX_FRAMING_ERR_VALID_12,
  output STAT_RX_FRAMING_ERR_VALID_13,
  output STAT_RX_FRAMING_ERR_VALID_14,
  output STAT_RX_FRAMING_ERR_VALID_15,
  output STAT_RX_FRAMING_ERR_VALID_16,
  output STAT_RX_FRAMING_ERR_VALID_17,
  output STAT_RX_FRAMING_ERR_VALID_18,
  output STAT_RX_FRAMING_ERR_VALID_19,
  output STAT_RX_FRAMING_ERR_VALID_2,
  output STAT_RX_FRAMING_ERR_VALID_3,
  output STAT_RX_FRAMING_ERR_VALID_4,
  output STAT_RX_FRAMING_ERR_VALID_5,
  output STAT_RX_FRAMING_ERR_VALID_6,
  output STAT_RX_FRAMING_ERR_VALID_7,
  output STAT_RX_FRAMING_ERR_VALID_8,
  output STAT_RX_FRAMING_ERR_VALID_9,
  output STAT_RX_GOT_SIGNAL_OS,
  output STAT_RX_HI_BER,
  output STAT_RX_INRANGEERR,
  output STAT_RX_INTERNAL_LOCAL_FAULT,
  output STAT_RX_JABBER,
  output [7:0] STAT_RX_LANE0_VLM_BIP7,
  output STAT_RX_LANE0_VLM_BIP7_VALID,
  output STAT_RX_LOCAL_FAULT,
  output [19:0] STAT_RX_MF_ERR,
  output [19:0] STAT_RX_MF_LEN_ERR,
  output [19:0] STAT_RX_MF_REPEAT_ERR,
  output STAT_RX_MISALIGNED,
  output STAT_RX_MULTICAST,
  output STAT_RX_OVERSIZE,
  output STAT_RX_PACKET_1024_1518_BYTES,
  output STAT_RX_PACKET_128_255_BYTES,
  output STAT_RX_PACKET_1519_1522_BYTES,
  output STAT_RX_PACKET_1523_1548_BYTES,
  output STAT_RX_PACKET_1549_2047_BYTES,
  output STAT_RX_PACKET_2048_4095_BYTES,
  output STAT_RX_PACKET_256_511_BYTES,
  output STAT_RX_PACKET_4096_8191_BYTES,
  output STAT_RX_PACKET_512_1023_BYTES,
  output STAT_RX_PACKET_64_BYTES,
  output STAT_RX_PACKET_65_127_BYTES,
  output STAT_RX_PACKET_8192_9215_BYTES,
  output STAT_RX_PACKET_BAD_FCS,
  output STAT_RX_PACKET_LARGE,
  output [3:0] STAT_RX_PACKET_SMALL,
  output STAT_RX_PAUSE,
  output [15:0] STAT_RX_PAUSE_QUANTA0,
  output [15:0] STAT_RX_PAUSE_QUANTA1,
  output [15:0] STAT_RX_PAUSE_QUANTA2,
  output [15:0] STAT_RX_PAUSE_QUANTA3,
  output [15:0] STAT_RX_PAUSE_QUANTA4,
  output [15:0] STAT_RX_PAUSE_QUANTA5,
  output [15:0] STAT_RX_PAUSE_QUANTA6,
  output [15:0] STAT_RX_PAUSE_QUANTA7,
  output [15:0] STAT_RX_PAUSE_QUANTA8,
  output [8:0] STAT_RX_PAUSE_REQ,
  output [8:0] STAT_RX_PAUSE_VALID,
  output STAT_RX_RECEIVED_LOCAL_FAULT,
  output STAT_RX_REMOTE_FAULT,
  output STAT_RX_STATUS,
  output [3:0] STAT_RX_STOMPED_FCS,
  output [19:0] STAT_RX_SYNCED,
  output [19:0] STAT_RX_SYNCED_ERR,
  output [2:0] STAT_RX_TEST_PATTERN_MISMATCH,
  output STAT_RX_TOOLONG,
  output [7:0] STAT_RX_TOTAL_BYTES,
  output [13:0] STAT_RX_TOTAL_GOOD_BYTES,
  output STAT_RX_TOTAL_GOOD_PACKETS,
  output [3:0] STAT_RX_TOTAL_PACKETS,
  output STAT_RX_TRUNCATED,
  output [3:0] STAT_RX_UNDERSIZE,
  output STAT_RX_UNICAST,
  output STAT_RX_USER_PAUSE,
  output STAT_RX_VLAN,
  output [19:0] STAT_RX_VL_DEMUXED,
  output [4:0] STAT_RX_VL_NUMBER_0,
  output [4:0] STAT_RX_VL_NUMBER_1,
  output [4:0] STAT_RX_VL_NUMBER_10,
  output [4:0] STAT_RX_VL_NUMBER_11,
  output [4:0] STAT_RX_VL_NUMBER_12,
  output [4:0] STAT_RX_VL_NUMBER_13,
  output [4:0] STAT_RX_VL_NUMBER_14,
  output [4:0] STAT_RX_VL_NUMBER_15,
  output [4:0] STAT_RX_VL_NUMBER_16,
  output [4:0] STAT_RX_VL_NUMBER_17,
  output [4:0] STAT_RX_VL_NUMBER_18,
  output [4:0] STAT_RX_VL_NUMBER_19,
  output [4:0] STAT_RX_VL_NUMBER_2,
  output [4:0] STAT_RX_VL_NUMBER_3,
  output [4:0] STAT_RX_VL_NUMBER_4,
  output [4:0] STAT_RX_VL_NUMBER_5,
  output [4:0] STAT_RX_VL_NUMBER_6,
  output [4:0] STAT_RX_VL_NUMBER_7,
  output [4:0] STAT_RX_VL_NUMBER_8,
  output [4:0] STAT_RX_VL_NUMBER_9,
  output STAT_TX_BAD_FCS,
  output STAT_TX_BROADCAST,
  output STAT_TX_FRAME_ERROR,
  output STAT_TX_LOCAL_FAULT,
  output STAT_TX_MULTICAST,
  output STAT_TX_PACKET_1024_1518_BYTES,
  output STAT_TX_PACKET_128_255_BYTES,
  output STAT_TX_PACKET_1519_1522_BYTES,
  output STAT_TX_PACKET_1523_1548_BYTES,
  output STAT_TX_PACKET_1549_2047_BYTES,
  output STAT_TX_PACKET_2048_4095_BYTES,
  output STAT_TX_PACKET_256_511_BYTES,
  output STAT_TX_PACKET_4096_8191_BYTES,
  output STAT_TX_PACKET_512_1023_BYTES,
  output STAT_TX_PACKET_64_BYTES,
  output STAT_TX_PACKET_65_127_BYTES,
  output STAT_TX_PACKET_8192_9215_BYTES,
  output STAT_TX_PACKET_LARGE,
  output STAT_TX_PACKET_SMALL,
  output STAT_TX_PAUSE,
  output [8:0] STAT_TX_PAUSE_VALID,
  output STAT_TX_PTP_FIFO_READ_ERROR,
  output STAT_TX_PTP_FIFO_WRITE_ERROR,
  output [6:0] STAT_TX_TOTAL_BYTES,
  output [13:0] STAT_TX_TOTAL_GOOD_BYTES,
  output STAT_TX_TOTAL_GOOD_PACKETS,
  output STAT_TX_TOTAL_PACKETS,
  output STAT_TX_UNICAST,
  output STAT_TX_USER_PAUSE,
  output STAT_TX_VLAN,
  output TX_OVFOUT,
  output [4:0] TX_PTP_PCSLANE_OUT,
  output [79:0] TX_PTP_TSTAMP_OUT,
  output [15:0] TX_PTP_TSTAMP_TAG_OUT,
  output TX_PTP_TSTAMP_VALID_OUT,
  output TX_RDYOUT,
  output [15:0] TX_SERDES_ALT_DATA0,
  output [15:0] TX_SERDES_ALT_DATA1,
  output [15:0] TX_SERDES_ALT_DATA2,
  output [15:0] TX_SERDES_ALT_DATA3,
  output [63:0] TX_SERDES_DATA0,
  output [63:0] TX_SERDES_DATA1,
  output [63:0] TX_SERDES_DATA2,
  output [63:0] TX_SERDES_DATA3,
  output [31:0] TX_SERDES_DATA4,
  output [31:0] TX_SERDES_DATA5,
  output [31:0] TX_SERDES_DATA6,
  output [31:0] TX_SERDES_DATA7,
  output [31:0] TX_SERDES_DATA8,
  output [31:0] TX_SERDES_DATA9,
  output TX_UNFOUT,

  input CTL_CAUI4_MODE,
  input CTL_RX_CHECK_ETYPE_GCP,
  input CTL_RX_CHECK_ETYPE_GPP,
  input CTL_RX_CHECK_ETYPE_PCP,
  input CTL_RX_CHECK_ETYPE_PPP,
  input CTL_RX_CHECK_MCAST_GCP,
  input CTL_RX_CHECK_MCAST_GPP,
  input CTL_RX_CHECK_MCAST_PCP,
  input CTL_RX_CHECK_MCAST_PPP,
  input CTL_RX_CHECK_OPCODE_GCP,
  input CTL_RX_CHECK_OPCODE_GPP,
  input CTL_RX_CHECK_OPCODE_PCP,
  input CTL_RX_CHECK_OPCODE_PPP,
  input CTL_RX_CHECK_SA_GCP,
  input CTL_RX_CHECK_SA_GPP,
  input CTL_RX_CHECK_SA_PCP,
  input CTL_RX_CHECK_SA_PPP,
  input CTL_RX_CHECK_UCAST_GCP,
  input CTL_RX_CHECK_UCAST_GPP,
  input CTL_RX_CHECK_UCAST_PCP,
  input CTL_RX_CHECK_UCAST_PPP,
  input CTL_RX_ENABLE,
  input CTL_RX_ENABLE_GCP,
  input CTL_RX_ENABLE_GPP,
  input CTL_RX_ENABLE_PCP,
  input CTL_RX_ENABLE_PPP,
  input CTL_RX_FORCE_RESYNC,
  input [8:0] CTL_RX_PAUSE_ACK,
  input [8:0] CTL_RX_PAUSE_ENABLE,
  input [79:0] CTL_RX_SYSTEMTIMERIN,
  input CTL_RX_TEST_PATTERN,
  input CTL_TX_ENABLE,
  input CTL_TX_LANE0_VLM_BIP7_OVERRIDE,
  input [7:0] CTL_TX_LANE0_VLM_BIP7_OVERRIDE_VALUE,
  input [8:0] CTL_TX_PAUSE_ENABLE,
  input [15:0] CTL_TX_PAUSE_QUANTA0,
  input [15:0] CTL_TX_PAUSE_QUANTA1,
  input [15:0] CTL_TX_PAUSE_QUANTA2,
  input [15:0] CTL_TX_PAUSE_QUANTA3,
  input [15:0] CTL_TX_PAUSE_QUANTA4,
  input [15:0] CTL_TX_PAUSE_QUANTA5,
  input [15:0] CTL_TX_PAUSE_QUANTA6,
  input [15:0] CTL_TX_PAUSE_QUANTA7,
  input [15:0] CTL_TX_PAUSE_QUANTA8,
  input [15:0] CTL_TX_PAUSE_REFRESH_TIMER0,
  input [15:0] CTL_TX_PAUSE_REFRESH_TIMER1,
  input [15:0] CTL_TX_PAUSE_REFRESH_TIMER2,
  input [15:0] CTL_TX_PAUSE_REFRESH_TIMER3,
  input [15:0] CTL_TX_PAUSE_REFRESH_TIMER4,
  input [15:0] CTL_TX_PAUSE_REFRESH_TIMER5,
  input [15:0] CTL_TX_PAUSE_REFRESH_TIMER6,
  input [15:0] CTL_TX_PAUSE_REFRESH_TIMER7,
  input [15:0] CTL_TX_PAUSE_REFRESH_TIMER8,
  input [8:0] CTL_TX_PAUSE_REQ,
  input CTL_TX_PTP_VLANE_ADJUST_MODE,
  input CTL_TX_RESEND_PAUSE,
  input CTL_TX_SEND_IDLE,
  input CTL_TX_SEND_RFI,
  input [79:0] CTL_TX_SYSTEMTIMERIN,
  input CTL_TX_TEST_PATTERN,
  input [9:0] DRP_ADDR,
  input DRP_CLK,
  input [15:0] DRP_DI,
  input DRP_EN,
  input DRP_WE,
  input RX_CLK,
  input RX_RESET,
  input [15:0] RX_SERDES_ALT_DATA0,
  input [15:0] RX_SERDES_ALT_DATA1,
  input [15:0] RX_SERDES_ALT_DATA2,
  input [15:0] RX_SERDES_ALT_DATA3,
  input [9:0] RX_SERDES_CLK,
  input [63:0] RX_SERDES_DATA0,
  input [63:0] RX_SERDES_DATA1,
  input [63:0] RX_SERDES_DATA2,
  input [63:0] RX_SERDES_DATA3,
  input [31:0] RX_SERDES_DATA4,
  input [31:0] RX_SERDES_DATA5,
  input [31:0] RX_SERDES_DATA6,
  input [31:0] RX_SERDES_DATA7,
  input [31:0] RX_SERDES_DATA8,
  input [31:0] RX_SERDES_DATA9,
  input [9:0] RX_SERDES_RESET,
  input TX_CLK,
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
  input [1:0] TX_PTP_1588OP_IN,
  input [15:0] TX_PTP_CHKSUM_OFFSET_IN,
  input [63:0] TX_PTP_RXTSTAMP_IN,
  input [15:0] TX_PTP_TAG_FIELD_IN,
  input [15:0] TX_PTP_TSTAMP_OFFSET_IN,
  input TX_PTP_UPD_CHKSUM_IN,
  input TX_RESET,
  input TX_SOPIN0,
  input TX_SOPIN1,
  input TX_SOPIN2,
  input TX_SOPIN3
);

// define constants
  localparam MODULE_NAME = "CMAC";
  localparam in_delay    = 0;
  localparam out_delay   = 0;
  localparam inclk_delay    = 0;
  localparam outclk_delay   = 0;

  reg trig_attr = 1'b0;
// include dynamic registers - XILINX test only



  localparam [40:1] CTL_PTP_TRANSPCLK_MODE_REG = CTL_PTP_TRANSPCLK_MODE;
  localparam [40:1] CTL_RX_CHECK_ACK_REG = CTL_RX_CHECK_ACK;
  localparam [40:1] CTL_RX_CHECK_PREAMBLE_REG = CTL_RX_CHECK_PREAMBLE;
  localparam [40:1] CTL_RX_CHECK_SFD_REG = CTL_RX_CHECK_SFD;
  localparam [40:1] CTL_RX_DELETE_FCS_REG = CTL_RX_DELETE_FCS;
  localparam [15:0] CTL_RX_ETYPE_GCP_REG = CTL_RX_ETYPE_GCP;
  localparam [15:0] CTL_RX_ETYPE_GPP_REG = CTL_RX_ETYPE_GPP;
  localparam [15:0] CTL_RX_ETYPE_PCP_REG = CTL_RX_ETYPE_PCP;
  localparam [15:0] CTL_RX_ETYPE_PPP_REG = CTL_RX_ETYPE_PPP;
  localparam [40:1] CTL_RX_FORWARD_CONTROL_REG = CTL_RX_FORWARD_CONTROL;
  localparam [40:1] CTL_RX_IGNORE_FCS_REG = CTL_RX_IGNORE_FCS;
  localparam [14:0] CTL_RX_MAX_PACKET_LEN_REG = CTL_RX_MAX_PACKET_LEN;
  localparam [7:0] CTL_RX_MIN_PACKET_LEN_REG = CTL_RX_MIN_PACKET_LEN;
  localparam [15:0] CTL_RX_OPCODE_GPP_REG = CTL_RX_OPCODE_GPP;
  localparam [15:0] CTL_RX_OPCODE_MAX_GCP_REG = CTL_RX_OPCODE_MAX_GCP;
  localparam [15:0] CTL_RX_OPCODE_MAX_PCP_REG = CTL_RX_OPCODE_MAX_PCP;
  localparam [15:0] CTL_RX_OPCODE_MIN_GCP_REG = CTL_RX_OPCODE_MIN_GCP;
  localparam [15:0] CTL_RX_OPCODE_MIN_PCP_REG = CTL_RX_OPCODE_MIN_PCP;
  localparam [15:0] CTL_RX_OPCODE_PPP_REG = CTL_RX_OPCODE_PPP;
  localparam [47:0] CTL_RX_PAUSE_DA_MCAST_REG = CTL_RX_PAUSE_DA_MCAST;
  localparam [47:0] CTL_RX_PAUSE_DA_UCAST_REG = CTL_RX_PAUSE_DA_UCAST;
  localparam [47:0] CTL_RX_PAUSE_SA_REG = CTL_RX_PAUSE_SA;
  localparam [40:1] CTL_RX_PROCESS_LFI_REG = CTL_RX_PROCESS_LFI;
  localparam [15:0] CTL_RX_VL_LENGTH_MINUS1_REG = CTL_RX_VL_LENGTH_MINUS1;
  localparam [63:0] CTL_RX_VL_MARKER_ID0_REG = CTL_RX_VL_MARKER_ID0;
  localparam [63:0] CTL_RX_VL_MARKER_ID1_REG = CTL_RX_VL_MARKER_ID1;
  localparam [63:0] CTL_RX_VL_MARKER_ID10_REG = CTL_RX_VL_MARKER_ID10;
  localparam [63:0] CTL_RX_VL_MARKER_ID11_REG = CTL_RX_VL_MARKER_ID11;
  localparam [63:0] CTL_RX_VL_MARKER_ID12_REG = CTL_RX_VL_MARKER_ID12;
  localparam [63:0] CTL_RX_VL_MARKER_ID13_REG = CTL_RX_VL_MARKER_ID13;
  localparam [63:0] CTL_RX_VL_MARKER_ID14_REG = CTL_RX_VL_MARKER_ID14;
  localparam [63:0] CTL_RX_VL_MARKER_ID15_REG = CTL_RX_VL_MARKER_ID15;
  localparam [63:0] CTL_RX_VL_MARKER_ID16_REG = CTL_RX_VL_MARKER_ID16;
  localparam [63:0] CTL_RX_VL_MARKER_ID17_REG = CTL_RX_VL_MARKER_ID17;
  localparam [63:0] CTL_RX_VL_MARKER_ID18_REG = CTL_RX_VL_MARKER_ID18;
  localparam [63:0] CTL_RX_VL_MARKER_ID19_REG = CTL_RX_VL_MARKER_ID19;
  localparam [63:0] CTL_RX_VL_MARKER_ID2_REG = CTL_RX_VL_MARKER_ID2;
  localparam [63:0] CTL_RX_VL_MARKER_ID3_REG = CTL_RX_VL_MARKER_ID3;
  localparam [63:0] CTL_RX_VL_MARKER_ID4_REG = CTL_RX_VL_MARKER_ID4;
  localparam [63:0] CTL_RX_VL_MARKER_ID5_REG = CTL_RX_VL_MARKER_ID5;
  localparam [63:0] CTL_RX_VL_MARKER_ID6_REG = CTL_RX_VL_MARKER_ID6;
  localparam [63:0] CTL_RX_VL_MARKER_ID7_REG = CTL_RX_VL_MARKER_ID7;
  localparam [63:0] CTL_RX_VL_MARKER_ID8_REG = CTL_RX_VL_MARKER_ID8;
  localparam [63:0] CTL_RX_VL_MARKER_ID9_REG = CTL_RX_VL_MARKER_ID9;
  localparam [40:1] CTL_TEST_MODE_PIN_CHAR_REG = CTL_TEST_MODE_PIN_CHAR;
  localparam [47:0] CTL_TX_DA_GPP_REG = CTL_TX_DA_GPP;
  localparam [47:0] CTL_TX_DA_PPP_REG = CTL_TX_DA_PPP;
  localparam [15:0] CTL_TX_ETHERTYPE_GPP_REG = CTL_TX_ETHERTYPE_GPP;
  localparam [15:0] CTL_TX_ETHERTYPE_PPP_REG = CTL_TX_ETHERTYPE_PPP;
  localparam [40:1] CTL_TX_FCS_INS_ENABLE_REG = CTL_TX_FCS_INS_ENABLE;
  localparam [40:1] CTL_TX_IGNORE_FCS_REG = CTL_TX_IGNORE_FCS;
  localparam [15:0] CTL_TX_OPCODE_GPP_REG = CTL_TX_OPCODE_GPP;
  localparam [15:0] CTL_TX_OPCODE_PPP_REG = CTL_TX_OPCODE_PPP;
  localparam [40:1] CTL_TX_PTP_1STEP_ENABLE_REG = CTL_TX_PTP_1STEP_ENABLE;
  localparam [10:0] CTL_TX_PTP_LATENCY_ADJUST_REG = CTL_TX_PTP_LATENCY_ADJUST;
  localparam [47:0] CTL_TX_SA_GPP_REG = CTL_TX_SA_GPP;
  localparam [47:0] CTL_TX_SA_PPP_REG = CTL_TX_SA_PPP;
  localparam [15:0] CTL_TX_VL_LENGTH_MINUS1_REG = CTL_TX_VL_LENGTH_MINUS1;
  localparam [63:0] CTL_TX_VL_MARKER_ID0_REG = CTL_TX_VL_MARKER_ID0;
  localparam [63:0] CTL_TX_VL_MARKER_ID1_REG = CTL_TX_VL_MARKER_ID1;
  localparam [63:0] CTL_TX_VL_MARKER_ID10_REG = CTL_TX_VL_MARKER_ID10;
  localparam [63:0] CTL_TX_VL_MARKER_ID11_REG = CTL_TX_VL_MARKER_ID11;
  localparam [63:0] CTL_TX_VL_MARKER_ID12_REG = CTL_TX_VL_MARKER_ID12;
  localparam [63:0] CTL_TX_VL_MARKER_ID13_REG = CTL_TX_VL_MARKER_ID13;
  localparam [63:0] CTL_TX_VL_MARKER_ID14_REG = CTL_TX_VL_MARKER_ID14;
  localparam [63:0] CTL_TX_VL_MARKER_ID15_REG = CTL_TX_VL_MARKER_ID15;
  localparam [63:0] CTL_TX_VL_MARKER_ID16_REG = CTL_TX_VL_MARKER_ID16;
  localparam [63:0] CTL_TX_VL_MARKER_ID17_REG = CTL_TX_VL_MARKER_ID17;
  localparam [63:0] CTL_TX_VL_MARKER_ID18_REG = CTL_TX_VL_MARKER_ID18;
  localparam [63:0] CTL_TX_VL_MARKER_ID19_REG = CTL_TX_VL_MARKER_ID19;
  localparam [63:0] CTL_TX_VL_MARKER_ID2_REG = CTL_TX_VL_MARKER_ID2;
  localparam [63:0] CTL_TX_VL_MARKER_ID3_REG = CTL_TX_VL_MARKER_ID3;
  localparam [63:0] CTL_TX_VL_MARKER_ID4_REG = CTL_TX_VL_MARKER_ID4;
  localparam [63:0] CTL_TX_VL_MARKER_ID5_REG = CTL_TX_VL_MARKER_ID5;
  localparam [63:0] CTL_TX_VL_MARKER_ID6_REG = CTL_TX_VL_MARKER_ID6;
  localparam [63:0] CTL_TX_VL_MARKER_ID7_REG = CTL_TX_VL_MARKER_ID7;
  localparam [63:0] CTL_TX_VL_MARKER_ID8_REG = CTL_TX_VL_MARKER_ID8;
  localparam [63:0] CTL_TX_VL_MARKER_ID9_REG = CTL_TX_VL_MARKER_ID9;
  localparam [24:1] SIM_VERSION_REG = SIM_VERSION;
  localparam [40:1] TEST_MODE_PIN_CHAR_REG = TEST_MODE_PIN_CHAR;





  reg attr_test = 1'b0;

  reg attr_err = 1'b0;
  tri0 glblGSR = glbl.GSR;

  wire DRP_RDY_out;
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
  wire RX_SOPOUT0_out;
  wire RX_SOPOUT1_out;
  wire RX_SOPOUT2_out;
  wire RX_SOPOUT3_out;
  wire STAT_RX_ALIGNED_ERR_out;
  wire STAT_RX_ALIGNED_out;
  wire STAT_RX_BAD_PREAMBLE_out;
  wire STAT_RX_BAD_SFD_out;
  wire STAT_RX_BIP_ERR_0_out;
  wire STAT_RX_BIP_ERR_10_out;
  wire STAT_RX_BIP_ERR_11_out;
  wire STAT_RX_BIP_ERR_12_out;
  wire STAT_RX_BIP_ERR_13_out;
  wire STAT_RX_BIP_ERR_14_out;
  wire STAT_RX_BIP_ERR_15_out;
  wire STAT_RX_BIP_ERR_16_out;
  wire STAT_RX_BIP_ERR_17_out;
  wire STAT_RX_BIP_ERR_18_out;
  wire STAT_RX_BIP_ERR_19_out;
  wire STAT_RX_BIP_ERR_1_out;
  wire STAT_RX_BIP_ERR_2_out;
  wire STAT_RX_BIP_ERR_3_out;
  wire STAT_RX_BIP_ERR_4_out;
  wire STAT_RX_BIP_ERR_5_out;
  wire STAT_RX_BIP_ERR_6_out;
  wire STAT_RX_BIP_ERR_7_out;
  wire STAT_RX_BIP_ERR_8_out;
  wire STAT_RX_BIP_ERR_9_out;
  wire STAT_RX_BROADCAST_out;
  wire STAT_RX_FRAMING_ERR_VALID_0_out;
  wire STAT_RX_FRAMING_ERR_VALID_10_out;
  wire STAT_RX_FRAMING_ERR_VALID_11_out;
  wire STAT_RX_FRAMING_ERR_VALID_12_out;
  wire STAT_RX_FRAMING_ERR_VALID_13_out;
  wire STAT_RX_FRAMING_ERR_VALID_14_out;
  wire STAT_RX_FRAMING_ERR_VALID_15_out;
  wire STAT_RX_FRAMING_ERR_VALID_16_out;
  wire STAT_RX_FRAMING_ERR_VALID_17_out;
  wire STAT_RX_FRAMING_ERR_VALID_18_out;
  wire STAT_RX_FRAMING_ERR_VALID_19_out;
  wire STAT_RX_FRAMING_ERR_VALID_1_out;
  wire STAT_RX_FRAMING_ERR_VALID_2_out;
  wire STAT_RX_FRAMING_ERR_VALID_3_out;
  wire STAT_RX_FRAMING_ERR_VALID_4_out;
  wire STAT_RX_FRAMING_ERR_VALID_5_out;
  wire STAT_RX_FRAMING_ERR_VALID_6_out;
  wire STAT_RX_FRAMING_ERR_VALID_7_out;
  wire STAT_RX_FRAMING_ERR_VALID_8_out;
  wire STAT_RX_FRAMING_ERR_VALID_9_out;
  wire STAT_RX_GOT_SIGNAL_OS_out;
  wire STAT_RX_HI_BER_out;
  wire STAT_RX_INRANGEERR_out;
  wire STAT_RX_INTERNAL_LOCAL_FAULT_out;
  wire STAT_RX_JABBER_out;
  wire STAT_RX_LANE0_VLM_BIP7_VALID_out;
  wire STAT_RX_LOCAL_FAULT_out;
  wire STAT_RX_MISALIGNED_out;
  wire STAT_RX_MULTICAST_out;
  wire STAT_RX_OVERSIZE_out;
  wire STAT_RX_PACKET_1024_1518_BYTES_out;
  wire STAT_RX_PACKET_128_255_BYTES_out;
  wire STAT_RX_PACKET_1519_1522_BYTES_out;
  wire STAT_RX_PACKET_1523_1548_BYTES_out;
  wire STAT_RX_PACKET_1549_2047_BYTES_out;
  wire STAT_RX_PACKET_2048_4095_BYTES_out;
  wire STAT_RX_PACKET_256_511_BYTES_out;
  wire STAT_RX_PACKET_4096_8191_BYTES_out;
  wire STAT_RX_PACKET_512_1023_BYTES_out;
  wire STAT_RX_PACKET_64_BYTES_out;
  wire STAT_RX_PACKET_65_127_BYTES_out;
  wire STAT_RX_PACKET_8192_9215_BYTES_out;
  wire STAT_RX_PACKET_BAD_FCS_out;
  wire STAT_RX_PACKET_LARGE_out;
  wire STAT_RX_PAUSE_out;
  wire STAT_RX_RECEIVED_LOCAL_FAULT_out;
  wire STAT_RX_REMOTE_FAULT_out;
  wire STAT_RX_STATUS_out;
  wire STAT_RX_TOOLONG_out;
  wire STAT_RX_TOTAL_GOOD_PACKETS_out;
  wire STAT_RX_TRUNCATED_out;
  wire STAT_RX_UNICAST_out;
  wire STAT_RX_USER_PAUSE_out;
  wire STAT_RX_VLAN_out;
  wire STAT_TX_BAD_FCS_out;
  wire STAT_TX_BROADCAST_out;
  wire STAT_TX_FRAME_ERROR_out;
  wire STAT_TX_LOCAL_FAULT_out;
  wire STAT_TX_MULTICAST_out;
  wire STAT_TX_PACKET_1024_1518_BYTES_out;
  wire STAT_TX_PACKET_128_255_BYTES_out;
  wire STAT_TX_PACKET_1519_1522_BYTES_out;
  wire STAT_TX_PACKET_1523_1548_BYTES_out;
  wire STAT_TX_PACKET_1549_2047_BYTES_out;
  wire STAT_TX_PACKET_2048_4095_BYTES_out;
  wire STAT_TX_PACKET_256_511_BYTES_out;
  wire STAT_TX_PACKET_4096_8191_BYTES_out;
  wire STAT_TX_PACKET_512_1023_BYTES_out;
  wire STAT_TX_PACKET_64_BYTES_out;
  wire STAT_TX_PACKET_65_127_BYTES_out;
  wire STAT_TX_PACKET_8192_9215_BYTES_out;
  wire STAT_TX_PACKET_LARGE_out;
  wire STAT_TX_PACKET_SMALL_out;
  wire STAT_TX_PAUSE_out;
  wire STAT_TX_PTP_FIFO_READ_ERROR_out;
  wire STAT_TX_PTP_FIFO_WRITE_ERROR_out;
  wire STAT_TX_TOTAL_GOOD_PACKETS_out;
  wire STAT_TX_TOTAL_PACKETS_out;
  wire STAT_TX_UNICAST_out;
  wire STAT_TX_USER_PAUSE_out;
  wire STAT_TX_VLAN_out;
  wire TX_OVFOUT_out;
  wire TX_PTP_TSTAMP_VALID_OUT_out;
  wire TX_RDYOUT_out;
  wire TX_UNFOUT_out;
  wire [127:0] RX_DATAOUT0_out;
  wire [127:0] RX_DATAOUT1_out;
  wire [127:0] RX_DATAOUT2_out;
  wire [127:0] RX_DATAOUT3_out;
  wire [12:0] SCAN_OUT_DRPCTRL_out;
  wire [13:0] STAT_RX_TOTAL_GOOD_BYTES_out;
  wire [13:0] STAT_TX_TOTAL_GOOD_BYTES_out;
  wire [15:0] DRP_DO_out;
  wire [15:0] STAT_RX_PAUSE_QUANTA0_out;
  wire [15:0] STAT_RX_PAUSE_QUANTA1_out;
  wire [15:0] STAT_RX_PAUSE_QUANTA2_out;
  wire [15:0] STAT_RX_PAUSE_QUANTA3_out;
  wire [15:0] STAT_RX_PAUSE_QUANTA4_out;
  wire [15:0] STAT_RX_PAUSE_QUANTA5_out;
  wire [15:0] STAT_RX_PAUSE_QUANTA6_out;
  wire [15:0] STAT_RX_PAUSE_QUANTA7_out;
  wire [15:0] STAT_RX_PAUSE_QUANTA8_out;
  wire [15:0] TX_PTP_TSTAMP_TAG_OUT_out;
  wire [15:0] TX_SERDES_ALT_DATA0_out;
  wire [15:0] TX_SERDES_ALT_DATA1_out;
  wire [15:0] TX_SERDES_ALT_DATA2_out;
  wire [15:0] TX_SERDES_ALT_DATA3_out;
  wire [181:0] SCAN_OUT_CMAC_out;
  wire [19:0] STAT_RX_BLOCK_LOCK_out;
  wire [19:0] STAT_RX_MF_ERR_out;
  wire [19:0] STAT_RX_MF_LEN_ERR_out;
  wire [19:0] STAT_RX_MF_REPEAT_ERR_out;
  wire [19:0] STAT_RX_SYNCED_ERR_out;
  wire [19:0] STAT_RX_SYNCED_out;
  wire [19:0] STAT_RX_VL_DEMUXED_out;
  wire [2:0] STAT_RX_TEST_PATTERN_MISMATCH_out;
  wire [31:0] TX_SERDES_DATA4_out;
  wire [31:0] TX_SERDES_DATA5_out;
  wire [31:0] TX_SERDES_DATA6_out;
  wire [31:0] TX_SERDES_DATA7_out;
  wire [31:0] TX_SERDES_DATA8_out;
  wire [31:0] TX_SERDES_DATA9_out;
  wire [3:0] RX_MTYOUT0_out;
  wire [3:0] RX_MTYOUT1_out;
  wire [3:0] RX_MTYOUT2_out;
  wire [3:0] RX_MTYOUT3_out;
  wire [3:0] STAT_RX_BAD_FCS_out;
  wire [3:0] STAT_RX_FRAGMENT_out;
  wire [3:0] STAT_RX_FRAMING_ERR_0_out;
  wire [3:0] STAT_RX_FRAMING_ERR_10_out;
  wire [3:0] STAT_RX_FRAMING_ERR_11_out;
  wire [3:0] STAT_RX_FRAMING_ERR_12_out;
  wire [3:0] STAT_RX_FRAMING_ERR_13_out;
  wire [3:0] STAT_RX_FRAMING_ERR_14_out;
  wire [3:0] STAT_RX_FRAMING_ERR_15_out;
  wire [3:0] STAT_RX_FRAMING_ERR_16_out;
  wire [3:0] STAT_RX_FRAMING_ERR_17_out;
  wire [3:0] STAT_RX_FRAMING_ERR_18_out;
  wire [3:0] STAT_RX_FRAMING_ERR_19_out;
  wire [3:0] STAT_RX_FRAMING_ERR_1_out;
  wire [3:0] STAT_RX_FRAMING_ERR_2_out;
  wire [3:0] STAT_RX_FRAMING_ERR_3_out;
  wire [3:0] STAT_RX_FRAMING_ERR_4_out;
  wire [3:0] STAT_RX_FRAMING_ERR_5_out;
  wire [3:0] STAT_RX_FRAMING_ERR_6_out;
  wire [3:0] STAT_RX_FRAMING_ERR_7_out;
  wire [3:0] STAT_RX_FRAMING_ERR_8_out;
  wire [3:0] STAT_RX_FRAMING_ERR_9_out;
  wire [3:0] STAT_RX_PACKET_SMALL_out;
  wire [3:0] STAT_RX_STOMPED_FCS_out;
  wire [3:0] STAT_RX_TOTAL_PACKETS_out;
  wire [3:0] STAT_RX_UNDERSIZE_out;
  wire [4:0] RX_PTP_PCSLANE_OUT_out;
  wire [4:0] STAT_RX_VL_NUMBER_0_out;
  wire [4:0] STAT_RX_VL_NUMBER_10_out;
  wire [4:0] STAT_RX_VL_NUMBER_11_out;
  wire [4:0] STAT_RX_VL_NUMBER_12_out;
  wire [4:0] STAT_RX_VL_NUMBER_13_out;
  wire [4:0] STAT_RX_VL_NUMBER_14_out;
  wire [4:0] STAT_RX_VL_NUMBER_15_out;
  wire [4:0] STAT_RX_VL_NUMBER_16_out;
  wire [4:0] STAT_RX_VL_NUMBER_17_out;
  wire [4:0] STAT_RX_VL_NUMBER_18_out;
  wire [4:0] STAT_RX_VL_NUMBER_19_out;
  wire [4:0] STAT_RX_VL_NUMBER_1_out;
  wire [4:0] STAT_RX_VL_NUMBER_2_out;
  wire [4:0] STAT_RX_VL_NUMBER_3_out;
  wire [4:0] STAT_RX_VL_NUMBER_4_out;
  wire [4:0] STAT_RX_VL_NUMBER_5_out;
  wire [4:0] STAT_RX_VL_NUMBER_6_out;
  wire [4:0] STAT_RX_VL_NUMBER_7_out;
  wire [4:0] STAT_RX_VL_NUMBER_8_out;
  wire [4:0] STAT_RX_VL_NUMBER_9_out;
  wire [4:0] TX_PTP_PCSLANE_OUT_out;
  wire [63:0] TX_SERDES_DATA0_out;
  wire [63:0] TX_SERDES_DATA1_out;
  wire [63:0] TX_SERDES_DATA2_out;
  wire [63:0] TX_SERDES_DATA3_out;
  wire [6:0] RX_LANE_ALIGNER_FILL_0_out;
  wire [6:0] RX_LANE_ALIGNER_FILL_10_out;
  wire [6:0] RX_LANE_ALIGNER_FILL_11_out;
  wire [6:0] RX_LANE_ALIGNER_FILL_12_out;
  wire [6:0] RX_LANE_ALIGNER_FILL_13_out;
  wire [6:0] RX_LANE_ALIGNER_FILL_14_out;
  wire [6:0] RX_LANE_ALIGNER_FILL_15_out;
  wire [6:0] RX_LANE_ALIGNER_FILL_16_out;
  wire [6:0] RX_LANE_ALIGNER_FILL_17_out;
  wire [6:0] RX_LANE_ALIGNER_FILL_18_out;
  wire [6:0] RX_LANE_ALIGNER_FILL_19_out;
  wire [6:0] RX_LANE_ALIGNER_FILL_1_out;
  wire [6:0] RX_LANE_ALIGNER_FILL_2_out;
  wire [6:0] RX_LANE_ALIGNER_FILL_3_out;
  wire [6:0] RX_LANE_ALIGNER_FILL_4_out;
  wire [6:0] RX_LANE_ALIGNER_FILL_5_out;
  wire [6:0] RX_LANE_ALIGNER_FILL_6_out;
  wire [6:0] RX_LANE_ALIGNER_FILL_7_out;
  wire [6:0] RX_LANE_ALIGNER_FILL_8_out;
  wire [6:0] RX_LANE_ALIGNER_FILL_9_out;
  wire [6:0] STAT_RX_BAD_CODE_out;
  wire [6:0] STAT_TX_TOTAL_BYTES_out;
  wire [79:0] RX_PTP_TSTAMP_OUT_out;
  wire [79:0] TX_PTP_TSTAMP_OUT_out;
  wire [7:0] STAT_RX_LANE0_VLM_BIP7_out;
  wire [7:0] STAT_RX_TOTAL_BYTES_out;
  wire [8:0] STAT_RX_PAUSE_REQ_out;
  wire [8:0] STAT_RX_PAUSE_VALID_out;
  wire [8:0] STAT_TX_PAUSE_VALID_out;

  wire DRP_RDY_delay;
  wire RX_ENAOUT0_delay;
  wire RX_ENAOUT1_delay;
  wire RX_ENAOUT2_delay;
  wire RX_ENAOUT3_delay;
  wire RX_EOPOUT0_delay;
  wire RX_EOPOUT1_delay;
  wire RX_EOPOUT2_delay;
  wire RX_EOPOUT3_delay;
  wire RX_ERROUT0_delay;
  wire RX_ERROUT1_delay;
  wire RX_ERROUT2_delay;
  wire RX_ERROUT3_delay;
  wire RX_SOPOUT0_delay;
  wire RX_SOPOUT1_delay;
  wire RX_SOPOUT2_delay;
  wire RX_SOPOUT3_delay;
  wire STAT_RX_ALIGNED_ERR_delay;
  wire STAT_RX_ALIGNED_delay;
  wire STAT_RX_BAD_PREAMBLE_delay;
  wire STAT_RX_BAD_SFD_delay;
  wire STAT_RX_BIP_ERR_0_delay;
  wire STAT_RX_BIP_ERR_10_delay;
  wire STAT_RX_BIP_ERR_11_delay;
  wire STAT_RX_BIP_ERR_12_delay;
  wire STAT_RX_BIP_ERR_13_delay;
  wire STAT_RX_BIP_ERR_14_delay;
  wire STAT_RX_BIP_ERR_15_delay;
  wire STAT_RX_BIP_ERR_16_delay;
  wire STAT_RX_BIP_ERR_17_delay;
  wire STAT_RX_BIP_ERR_18_delay;
  wire STAT_RX_BIP_ERR_19_delay;
  wire STAT_RX_BIP_ERR_1_delay;
  wire STAT_RX_BIP_ERR_2_delay;
  wire STAT_RX_BIP_ERR_3_delay;
  wire STAT_RX_BIP_ERR_4_delay;
  wire STAT_RX_BIP_ERR_5_delay;
  wire STAT_RX_BIP_ERR_6_delay;
  wire STAT_RX_BIP_ERR_7_delay;
  wire STAT_RX_BIP_ERR_8_delay;
  wire STAT_RX_BIP_ERR_9_delay;
  wire STAT_RX_BROADCAST_delay;
  wire STAT_RX_FRAMING_ERR_VALID_0_delay;
  wire STAT_RX_FRAMING_ERR_VALID_10_delay;
  wire STAT_RX_FRAMING_ERR_VALID_11_delay;
  wire STAT_RX_FRAMING_ERR_VALID_12_delay;
  wire STAT_RX_FRAMING_ERR_VALID_13_delay;
  wire STAT_RX_FRAMING_ERR_VALID_14_delay;
  wire STAT_RX_FRAMING_ERR_VALID_15_delay;
  wire STAT_RX_FRAMING_ERR_VALID_16_delay;
  wire STAT_RX_FRAMING_ERR_VALID_17_delay;
  wire STAT_RX_FRAMING_ERR_VALID_18_delay;
  wire STAT_RX_FRAMING_ERR_VALID_19_delay;
  wire STAT_RX_FRAMING_ERR_VALID_1_delay;
  wire STAT_RX_FRAMING_ERR_VALID_2_delay;
  wire STAT_RX_FRAMING_ERR_VALID_3_delay;
  wire STAT_RX_FRAMING_ERR_VALID_4_delay;
  wire STAT_RX_FRAMING_ERR_VALID_5_delay;
  wire STAT_RX_FRAMING_ERR_VALID_6_delay;
  wire STAT_RX_FRAMING_ERR_VALID_7_delay;
  wire STAT_RX_FRAMING_ERR_VALID_8_delay;
  wire STAT_RX_FRAMING_ERR_VALID_9_delay;
  wire STAT_RX_GOT_SIGNAL_OS_delay;
  wire STAT_RX_HI_BER_delay;
  wire STAT_RX_INRANGEERR_delay;
  wire STAT_RX_INTERNAL_LOCAL_FAULT_delay;
  wire STAT_RX_JABBER_delay;
  wire STAT_RX_LANE0_VLM_BIP7_VALID_delay;
  wire STAT_RX_LOCAL_FAULT_delay;
  wire STAT_RX_MISALIGNED_delay;
  wire STAT_RX_MULTICAST_delay;
  wire STAT_RX_OVERSIZE_delay;
  wire STAT_RX_PACKET_1024_1518_BYTES_delay;
  wire STAT_RX_PACKET_128_255_BYTES_delay;
  wire STAT_RX_PACKET_1519_1522_BYTES_delay;
  wire STAT_RX_PACKET_1523_1548_BYTES_delay;
  wire STAT_RX_PACKET_1549_2047_BYTES_delay;
  wire STAT_RX_PACKET_2048_4095_BYTES_delay;
  wire STAT_RX_PACKET_256_511_BYTES_delay;
  wire STAT_RX_PACKET_4096_8191_BYTES_delay;
  wire STAT_RX_PACKET_512_1023_BYTES_delay;
  wire STAT_RX_PACKET_64_BYTES_delay;
  wire STAT_RX_PACKET_65_127_BYTES_delay;
  wire STAT_RX_PACKET_8192_9215_BYTES_delay;
  wire STAT_RX_PACKET_BAD_FCS_delay;
  wire STAT_RX_PACKET_LARGE_delay;
  wire STAT_RX_PAUSE_delay;
  wire STAT_RX_RECEIVED_LOCAL_FAULT_delay;
  wire STAT_RX_REMOTE_FAULT_delay;
  wire STAT_RX_STATUS_delay;
  wire STAT_RX_TOOLONG_delay;
  wire STAT_RX_TOTAL_GOOD_PACKETS_delay;
  wire STAT_RX_TRUNCATED_delay;
  wire STAT_RX_UNICAST_delay;
  wire STAT_RX_USER_PAUSE_delay;
  wire STAT_RX_VLAN_delay;
  wire STAT_TX_BAD_FCS_delay;
  wire STAT_TX_BROADCAST_delay;
  wire STAT_TX_FRAME_ERROR_delay;
  wire STAT_TX_LOCAL_FAULT_delay;
  wire STAT_TX_MULTICAST_delay;
  wire STAT_TX_PACKET_1024_1518_BYTES_delay;
  wire STAT_TX_PACKET_128_255_BYTES_delay;
  wire STAT_TX_PACKET_1519_1522_BYTES_delay;
  wire STAT_TX_PACKET_1523_1548_BYTES_delay;
  wire STAT_TX_PACKET_1549_2047_BYTES_delay;
  wire STAT_TX_PACKET_2048_4095_BYTES_delay;
  wire STAT_TX_PACKET_256_511_BYTES_delay;
  wire STAT_TX_PACKET_4096_8191_BYTES_delay;
  wire STAT_TX_PACKET_512_1023_BYTES_delay;
  wire STAT_TX_PACKET_64_BYTES_delay;
  wire STAT_TX_PACKET_65_127_BYTES_delay;
  wire STAT_TX_PACKET_8192_9215_BYTES_delay;
  wire STAT_TX_PACKET_LARGE_delay;
  wire STAT_TX_PACKET_SMALL_delay;
  wire STAT_TX_PAUSE_delay;
  wire STAT_TX_PTP_FIFO_READ_ERROR_delay;
  wire STAT_TX_PTP_FIFO_WRITE_ERROR_delay;
  wire STAT_TX_TOTAL_GOOD_PACKETS_delay;
  wire STAT_TX_TOTAL_PACKETS_delay;
  wire STAT_TX_UNICAST_delay;
  wire STAT_TX_USER_PAUSE_delay;
  wire STAT_TX_VLAN_delay;
  wire TX_OVFOUT_delay;
  wire TX_PTP_TSTAMP_VALID_OUT_delay;
  wire TX_RDYOUT_delay;
  wire TX_UNFOUT_delay;
  wire [127:0] RX_DATAOUT0_delay;
  wire [127:0] RX_DATAOUT1_delay;
  wire [127:0] RX_DATAOUT2_delay;
  wire [127:0] RX_DATAOUT3_delay;
  wire [13:0] STAT_RX_TOTAL_GOOD_BYTES_delay;
  wire [13:0] STAT_TX_TOTAL_GOOD_BYTES_delay;
  wire [15:0] DRP_DO_delay;
  wire [15:0] STAT_RX_PAUSE_QUANTA0_delay;
  wire [15:0] STAT_RX_PAUSE_QUANTA1_delay;
  wire [15:0] STAT_RX_PAUSE_QUANTA2_delay;
  wire [15:0] STAT_RX_PAUSE_QUANTA3_delay;
  wire [15:0] STAT_RX_PAUSE_QUANTA4_delay;
  wire [15:0] STAT_RX_PAUSE_QUANTA5_delay;
  wire [15:0] STAT_RX_PAUSE_QUANTA6_delay;
  wire [15:0] STAT_RX_PAUSE_QUANTA7_delay;
  wire [15:0] STAT_RX_PAUSE_QUANTA8_delay;
  wire [15:0] TX_PTP_TSTAMP_TAG_OUT_delay;
  wire [15:0] TX_SERDES_ALT_DATA0_delay;
  wire [15:0] TX_SERDES_ALT_DATA1_delay;
  wire [15:0] TX_SERDES_ALT_DATA2_delay;
  wire [15:0] TX_SERDES_ALT_DATA3_delay;
  wire [19:0] STAT_RX_BLOCK_LOCK_delay;
  wire [19:0] STAT_RX_MF_ERR_delay;
  wire [19:0] STAT_RX_MF_LEN_ERR_delay;
  wire [19:0] STAT_RX_MF_REPEAT_ERR_delay;
  wire [19:0] STAT_RX_SYNCED_ERR_delay;
  wire [19:0] STAT_RX_SYNCED_delay;
  wire [19:0] STAT_RX_VL_DEMUXED_delay;
  wire [2:0] STAT_RX_TEST_PATTERN_MISMATCH_delay;
  wire [31:0] TX_SERDES_DATA4_delay;
  wire [31:0] TX_SERDES_DATA5_delay;
  wire [31:0] TX_SERDES_DATA6_delay;
  wire [31:0] TX_SERDES_DATA7_delay;
  wire [31:0] TX_SERDES_DATA8_delay;
  wire [31:0] TX_SERDES_DATA9_delay;
  wire [3:0] RX_MTYOUT0_delay;
  wire [3:0] RX_MTYOUT1_delay;
  wire [3:0] RX_MTYOUT2_delay;
  wire [3:0] RX_MTYOUT3_delay;
  wire [3:0] STAT_RX_BAD_FCS_delay;
  wire [3:0] STAT_RX_FRAGMENT_delay;
  wire [3:0] STAT_RX_FRAMING_ERR_0_delay;
  wire [3:0] STAT_RX_FRAMING_ERR_10_delay;
  wire [3:0] STAT_RX_FRAMING_ERR_11_delay;
  wire [3:0] STAT_RX_FRAMING_ERR_12_delay;
  wire [3:0] STAT_RX_FRAMING_ERR_13_delay;
  wire [3:0] STAT_RX_FRAMING_ERR_14_delay;
  wire [3:0] STAT_RX_FRAMING_ERR_15_delay;
  wire [3:0] STAT_RX_FRAMING_ERR_16_delay;
  wire [3:0] STAT_RX_FRAMING_ERR_17_delay;
  wire [3:0] STAT_RX_FRAMING_ERR_18_delay;
  wire [3:0] STAT_RX_FRAMING_ERR_19_delay;
  wire [3:0] STAT_RX_FRAMING_ERR_1_delay;
  wire [3:0] STAT_RX_FRAMING_ERR_2_delay;
  wire [3:0] STAT_RX_FRAMING_ERR_3_delay;
  wire [3:0] STAT_RX_FRAMING_ERR_4_delay;
  wire [3:0] STAT_RX_FRAMING_ERR_5_delay;
  wire [3:0] STAT_RX_FRAMING_ERR_6_delay;
  wire [3:0] STAT_RX_FRAMING_ERR_7_delay;
  wire [3:0] STAT_RX_FRAMING_ERR_8_delay;
  wire [3:0] STAT_RX_FRAMING_ERR_9_delay;
  wire [3:0] STAT_RX_PACKET_SMALL_delay;
  wire [3:0] STAT_RX_STOMPED_FCS_delay;
  wire [3:0] STAT_RX_TOTAL_PACKETS_delay;
  wire [3:0] STAT_RX_UNDERSIZE_delay;
  wire [4:0] RX_PTP_PCSLANE_OUT_delay;
  wire [4:0] STAT_RX_VL_NUMBER_0_delay;
  wire [4:0] STAT_RX_VL_NUMBER_10_delay;
  wire [4:0] STAT_RX_VL_NUMBER_11_delay;
  wire [4:0] STAT_RX_VL_NUMBER_12_delay;
  wire [4:0] STAT_RX_VL_NUMBER_13_delay;
  wire [4:0] STAT_RX_VL_NUMBER_14_delay;
  wire [4:0] STAT_RX_VL_NUMBER_15_delay;
  wire [4:0] STAT_RX_VL_NUMBER_16_delay;
  wire [4:0] STAT_RX_VL_NUMBER_17_delay;
  wire [4:0] STAT_RX_VL_NUMBER_18_delay;
  wire [4:0] STAT_RX_VL_NUMBER_19_delay;
  wire [4:0] STAT_RX_VL_NUMBER_1_delay;
  wire [4:0] STAT_RX_VL_NUMBER_2_delay;
  wire [4:0] STAT_RX_VL_NUMBER_3_delay;
  wire [4:0] STAT_RX_VL_NUMBER_4_delay;
  wire [4:0] STAT_RX_VL_NUMBER_5_delay;
  wire [4:0] STAT_RX_VL_NUMBER_6_delay;
  wire [4:0] STAT_RX_VL_NUMBER_7_delay;
  wire [4:0] STAT_RX_VL_NUMBER_8_delay;
  wire [4:0] STAT_RX_VL_NUMBER_9_delay;
  wire [4:0] TX_PTP_PCSLANE_OUT_delay;
  wire [63:0] TX_SERDES_DATA0_delay;
  wire [63:0] TX_SERDES_DATA1_delay;
  wire [63:0] TX_SERDES_DATA2_delay;
  wire [63:0] TX_SERDES_DATA3_delay;
  wire [6:0] RX_LANE_ALIGNER_FILL_0_delay;
  wire [6:0] RX_LANE_ALIGNER_FILL_10_delay;
  wire [6:0] RX_LANE_ALIGNER_FILL_11_delay;
  wire [6:0] RX_LANE_ALIGNER_FILL_12_delay;
  wire [6:0] RX_LANE_ALIGNER_FILL_13_delay;
  wire [6:0] RX_LANE_ALIGNER_FILL_14_delay;
  wire [6:0] RX_LANE_ALIGNER_FILL_15_delay;
  wire [6:0] RX_LANE_ALIGNER_FILL_16_delay;
  wire [6:0] RX_LANE_ALIGNER_FILL_17_delay;
  wire [6:0] RX_LANE_ALIGNER_FILL_18_delay;
  wire [6:0] RX_LANE_ALIGNER_FILL_19_delay;
  wire [6:0] RX_LANE_ALIGNER_FILL_1_delay;
  wire [6:0] RX_LANE_ALIGNER_FILL_2_delay;
  wire [6:0] RX_LANE_ALIGNER_FILL_3_delay;
  wire [6:0] RX_LANE_ALIGNER_FILL_4_delay;
  wire [6:0] RX_LANE_ALIGNER_FILL_5_delay;
  wire [6:0] RX_LANE_ALIGNER_FILL_6_delay;
  wire [6:0] RX_LANE_ALIGNER_FILL_7_delay;
  wire [6:0] RX_LANE_ALIGNER_FILL_8_delay;
  wire [6:0] RX_LANE_ALIGNER_FILL_9_delay;
  wire [6:0] STAT_RX_BAD_CODE_delay;
  wire [6:0] STAT_TX_TOTAL_BYTES_delay;
  wire [79:0] RX_PTP_TSTAMP_OUT_delay;
  wire [79:0] TX_PTP_TSTAMP_OUT_delay;
  wire [7:0] STAT_RX_LANE0_VLM_BIP7_delay;
  wire [7:0] STAT_RX_TOTAL_BYTES_delay;
  wire [8:0] STAT_RX_PAUSE_REQ_delay;
  wire [8:0] STAT_RX_PAUSE_VALID_delay;
  wire [8:0] STAT_TX_PAUSE_VALID_delay;

  wire CTL_CAUI4_MODE_in;
  wire CTL_RX_CHECK_ETYPE_GCP_in;
  wire CTL_RX_CHECK_ETYPE_GPP_in;
  wire CTL_RX_CHECK_ETYPE_PCP_in;
  wire CTL_RX_CHECK_ETYPE_PPP_in;
  wire CTL_RX_CHECK_MCAST_GCP_in;
  wire CTL_RX_CHECK_MCAST_GPP_in;
  wire CTL_RX_CHECK_MCAST_PCP_in;
  wire CTL_RX_CHECK_MCAST_PPP_in;
  wire CTL_RX_CHECK_OPCODE_GCP_in;
  wire CTL_RX_CHECK_OPCODE_GPP_in;
  wire CTL_RX_CHECK_OPCODE_PCP_in;
  wire CTL_RX_CHECK_OPCODE_PPP_in;
  wire CTL_RX_CHECK_SA_GCP_in;
  wire CTL_RX_CHECK_SA_GPP_in;
  wire CTL_RX_CHECK_SA_PCP_in;
  wire CTL_RX_CHECK_SA_PPP_in;
  wire CTL_RX_CHECK_UCAST_GCP_in;
  wire CTL_RX_CHECK_UCAST_GPP_in;
  wire CTL_RX_CHECK_UCAST_PCP_in;
  wire CTL_RX_CHECK_UCAST_PPP_in;
  wire CTL_RX_ENABLE_GCP_in;
  wire CTL_RX_ENABLE_GPP_in;
  wire CTL_RX_ENABLE_PCP_in;
  wire CTL_RX_ENABLE_PPP_in;
  wire CTL_RX_ENABLE_in;
  wire CTL_RX_FORCE_RESYNC_in;
  wire CTL_RX_TEST_PATTERN_in;
  wire CTL_TX_ENABLE_in;
  wire CTL_TX_LANE0_VLM_BIP7_OVERRIDE_in;
  wire CTL_TX_PTP_VLANE_ADJUST_MODE_in;
  wire CTL_TX_RESEND_PAUSE_in;
  wire CTL_TX_SEND_IDLE_in;
  wire CTL_TX_SEND_RFI_in;
  wire CTL_TX_TEST_PATTERN_in;
  wire DRP_CLK_in;
  wire DRP_EN_in;
  wire DRP_WE_in;
  wire RX_CLK_in;
  wire RX_RESET_in;
  wire SCAN_EN_in;
  wire TEST_MODE_in;
  wire TEST_RESET_in;
  wire TX_CLK_in;
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
  wire TX_PTP_UPD_CHKSUM_IN_in;
  wire TX_RESET_in;
  wire TX_SOPIN0_in;
  wire TX_SOPIN1_in;
  wire TX_SOPIN2_in;
  wire TX_SOPIN3_in;
  wire [127:0] TX_DATAIN0_in;
  wire [127:0] TX_DATAIN1_in;
  wire [127:0] TX_DATAIN2_in;
  wire [127:0] TX_DATAIN3_in;
  wire [12:0] SCAN_IN_DRPCTRL_in;
  wire [15:0] CTL_TX_PAUSE_QUANTA0_in;
  wire [15:0] CTL_TX_PAUSE_QUANTA1_in;
  wire [15:0] CTL_TX_PAUSE_QUANTA2_in;
  wire [15:0] CTL_TX_PAUSE_QUANTA3_in;
  wire [15:0] CTL_TX_PAUSE_QUANTA4_in;
  wire [15:0] CTL_TX_PAUSE_QUANTA5_in;
  wire [15:0] CTL_TX_PAUSE_QUANTA6_in;
  wire [15:0] CTL_TX_PAUSE_QUANTA7_in;
  wire [15:0] CTL_TX_PAUSE_QUANTA8_in;
  wire [15:0] CTL_TX_PAUSE_REFRESH_TIMER0_in;
  wire [15:0] CTL_TX_PAUSE_REFRESH_TIMER1_in;
  wire [15:0] CTL_TX_PAUSE_REFRESH_TIMER2_in;
  wire [15:0] CTL_TX_PAUSE_REFRESH_TIMER3_in;
  wire [15:0] CTL_TX_PAUSE_REFRESH_TIMER4_in;
  wire [15:0] CTL_TX_PAUSE_REFRESH_TIMER5_in;
  wire [15:0] CTL_TX_PAUSE_REFRESH_TIMER6_in;
  wire [15:0] CTL_TX_PAUSE_REFRESH_TIMER7_in;
  wire [15:0] CTL_TX_PAUSE_REFRESH_TIMER8_in;
  wire [15:0] DRP_DI_in;
  wire [15:0] RX_SERDES_ALT_DATA0_in;
  wire [15:0] RX_SERDES_ALT_DATA1_in;
  wire [15:0] RX_SERDES_ALT_DATA2_in;
  wire [15:0] RX_SERDES_ALT_DATA3_in;
  wire [15:0] TX_PTP_CHKSUM_OFFSET_IN_in;
  wire [15:0] TX_PTP_TAG_FIELD_IN_in;
  wire [15:0] TX_PTP_TSTAMP_OFFSET_IN_in;
  wire [181:0] SCAN_IN_CMAC_in;
  wire [1:0] TX_PTP_1588OP_IN_in;
  wire [31:0] RX_SERDES_DATA4_in;
  wire [31:0] RX_SERDES_DATA5_in;
  wire [31:0] RX_SERDES_DATA6_in;
  wire [31:0] RX_SERDES_DATA7_in;
  wire [31:0] RX_SERDES_DATA8_in;
  wire [31:0] RX_SERDES_DATA9_in;
  wire [3:0] TX_MTYIN0_in;
  wire [3:0] TX_MTYIN1_in;
  wire [3:0] TX_MTYIN2_in;
  wire [3:0] TX_MTYIN3_in;
  wire [63:0] RX_SERDES_DATA0_in;
  wire [63:0] RX_SERDES_DATA1_in;
  wire [63:0] RX_SERDES_DATA2_in;
  wire [63:0] RX_SERDES_DATA3_in;
  wire [63:0] TX_PTP_RXTSTAMP_IN_in;
  wire [79:0] CTL_RX_SYSTEMTIMERIN_in;
  wire [79:0] CTL_TX_SYSTEMTIMERIN_in;
  wire [7:0] CTL_TX_LANE0_VLM_BIP7_OVERRIDE_VALUE_in;
  wire [8:0] CTL_RX_PAUSE_ACK_in;
  wire [8:0] CTL_RX_PAUSE_ENABLE_in;
  wire [8:0] CTL_TX_PAUSE_ENABLE_in;
  wire [8:0] CTL_TX_PAUSE_REQ_in;
  wire [9:0] DRP_ADDR_in;
  wire [9:0] RX_SERDES_CLK_in;
  wire [9:0] RX_SERDES_RESET_in;

  wire CTL_CAUI4_MODE_delay;
  wire CTL_RX_CHECK_ETYPE_GCP_delay;
  wire CTL_RX_CHECK_ETYPE_GPP_delay;
  wire CTL_RX_CHECK_ETYPE_PCP_delay;
  wire CTL_RX_CHECK_ETYPE_PPP_delay;
  wire CTL_RX_CHECK_MCAST_GCP_delay;
  wire CTL_RX_CHECK_MCAST_GPP_delay;
  wire CTL_RX_CHECK_MCAST_PCP_delay;
  wire CTL_RX_CHECK_MCAST_PPP_delay;
  wire CTL_RX_CHECK_OPCODE_GCP_delay;
  wire CTL_RX_CHECK_OPCODE_GPP_delay;
  wire CTL_RX_CHECK_OPCODE_PCP_delay;
  wire CTL_RX_CHECK_OPCODE_PPP_delay;
  wire CTL_RX_CHECK_SA_GCP_delay;
  wire CTL_RX_CHECK_SA_GPP_delay;
  wire CTL_RX_CHECK_SA_PCP_delay;
  wire CTL_RX_CHECK_SA_PPP_delay;
  wire CTL_RX_CHECK_UCAST_GCP_delay;
  wire CTL_RX_CHECK_UCAST_GPP_delay;
  wire CTL_RX_CHECK_UCAST_PCP_delay;
  wire CTL_RX_CHECK_UCAST_PPP_delay;
  wire CTL_RX_ENABLE_GCP_delay;
  wire CTL_RX_ENABLE_GPP_delay;
  wire CTL_RX_ENABLE_PCP_delay;
  wire CTL_RX_ENABLE_PPP_delay;
  wire CTL_RX_ENABLE_delay;
  wire CTL_RX_FORCE_RESYNC_delay;
  wire CTL_RX_TEST_PATTERN_delay;
  wire CTL_TX_ENABLE_delay;
  wire CTL_TX_LANE0_VLM_BIP7_OVERRIDE_delay;
  wire CTL_TX_PTP_VLANE_ADJUST_MODE_delay;
  wire CTL_TX_RESEND_PAUSE_delay;
  wire CTL_TX_SEND_IDLE_delay;
  wire CTL_TX_SEND_RFI_delay;
  wire CTL_TX_TEST_PATTERN_delay;
  wire DRP_CLK_delay;
  wire DRP_EN_delay;
  wire DRP_WE_delay;
  wire RX_CLK_delay;
  wire RX_RESET_delay;
  wire TX_CLK_delay;
  wire TX_ENAIN0_delay;
  wire TX_ENAIN1_delay;
  wire TX_ENAIN2_delay;
  wire TX_ENAIN3_delay;
  wire TX_EOPIN0_delay;
  wire TX_EOPIN1_delay;
  wire TX_EOPIN2_delay;
  wire TX_EOPIN3_delay;
  wire TX_ERRIN0_delay;
  wire TX_ERRIN1_delay;
  wire TX_ERRIN2_delay;
  wire TX_ERRIN3_delay;
  wire TX_PTP_UPD_CHKSUM_IN_delay;
  wire TX_RESET_delay;
  wire TX_SOPIN0_delay;
  wire TX_SOPIN1_delay;
  wire TX_SOPIN2_delay;
  wire TX_SOPIN3_delay;
  wire [127:0] TX_DATAIN0_delay;
  wire [127:0] TX_DATAIN1_delay;
  wire [127:0] TX_DATAIN2_delay;
  wire [127:0] TX_DATAIN3_delay;
  wire [15:0] CTL_TX_PAUSE_QUANTA0_delay;
  wire [15:0] CTL_TX_PAUSE_QUANTA1_delay;
  wire [15:0] CTL_TX_PAUSE_QUANTA2_delay;
  wire [15:0] CTL_TX_PAUSE_QUANTA3_delay;
  wire [15:0] CTL_TX_PAUSE_QUANTA4_delay;
  wire [15:0] CTL_TX_PAUSE_QUANTA5_delay;
  wire [15:0] CTL_TX_PAUSE_QUANTA6_delay;
  wire [15:0] CTL_TX_PAUSE_QUANTA7_delay;
  wire [15:0] CTL_TX_PAUSE_QUANTA8_delay;
  wire [15:0] CTL_TX_PAUSE_REFRESH_TIMER0_delay;
  wire [15:0] CTL_TX_PAUSE_REFRESH_TIMER1_delay;
  wire [15:0] CTL_TX_PAUSE_REFRESH_TIMER2_delay;
  wire [15:0] CTL_TX_PAUSE_REFRESH_TIMER3_delay;
  wire [15:0] CTL_TX_PAUSE_REFRESH_TIMER4_delay;
  wire [15:0] CTL_TX_PAUSE_REFRESH_TIMER5_delay;
  wire [15:0] CTL_TX_PAUSE_REFRESH_TIMER6_delay;
  wire [15:0] CTL_TX_PAUSE_REFRESH_TIMER7_delay;
  wire [15:0] CTL_TX_PAUSE_REFRESH_TIMER8_delay;
  wire [15:0] DRP_DI_delay;
  wire [15:0] RX_SERDES_ALT_DATA0_delay;
  wire [15:0] RX_SERDES_ALT_DATA1_delay;
  wire [15:0] RX_SERDES_ALT_DATA2_delay;
  wire [15:0] RX_SERDES_ALT_DATA3_delay;
  wire [15:0] TX_PTP_CHKSUM_OFFSET_IN_delay;
  wire [15:0] TX_PTP_TAG_FIELD_IN_delay;
  wire [15:0] TX_PTP_TSTAMP_OFFSET_IN_delay;
  wire [1:0] TX_PTP_1588OP_IN_delay;
  wire [31:0] RX_SERDES_DATA4_delay;
  wire [31:0] RX_SERDES_DATA5_delay;
  wire [31:0] RX_SERDES_DATA6_delay;
  wire [31:0] RX_SERDES_DATA7_delay;
  wire [31:0] RX_SERDES_DATA8_delay;
  wire [31:0] RX_SERDES_DATA9_delay;
  wire [3:0] TX_MTYIN0_delay;
  wire [3:0] TX_MTYIN1_delay;
  wire [3:0] TX_MTYIN2_delay;
  wire [3:0] TX_MTYIN3_delay;
  wire [63:0] RX_SERDES_DATA0_delay;
  wire [63:0] RX_SERDES_DATA1_delay;
  wire [63:0] RX_SERDES_DATA2_delay;
  wire [63:0] RX_SERDES_DATA3_delay;
  wire [63:0] TX_PTP_RXTSTAMP_IN_delay;
  wire [79:0] CTL_RX_SYSTEMTIMERIN_delay;
  wire [79:0] CTL_TX_SYSTEMTIMERIN_delay;
  wire [7:0] CTL_TX_LANE0_VLM_BIP7_OVERRIDE_VALUE_delay;
  wire [8:0] CTL_RX_PAUSE_ACK_delay;
  wire [8:0] CTL_RX_PAUSE_ENABLE_delay;
  wire [8:0] CTL_TX_PAUSE_ENABLE_delay;
  wire [8:0] CTL_TX_PAUSE_REQ_delay;
  wire [9:0] DRP_ADDR_delay;
  wire [9:0] RX_SERDES_CLK_delay;
  wire [9:0] RX_SERDES_RESET_delay;

  assign #(out_delay) DRP_DO = DRP_DO_delay;
  assign #(out_delay) DRP_RDY = DRP_RDY_delay;
  assign #(out_delay) RX_DATAOUT0 = RX_DATAOUT0_delay;
  assign #(out_delay) RX_DATAOUT1 = RX_DATAOUT1_delay;
  assign #(out_delay) RX_DATAOUT2 = RX_DATAOUT2_delay;
  assign #(out_delay) RX_DATAOUT3 = RX_DATAOUT3_delay;
  assign #(out_delay) RX_ENAOUT0 = RX_ENAOUT0_delay;
  assign #(out_delay) RX_ENAOUT1 = RX_ENAOUT1_delay;
  assign #(out_delay) RX_ENAOUT2 = RX_ENAOUT2_delay;
  assign #(out_delay) RX_ENAOUT3 = RX_ENAOUT3_delay;
  assign #(out_delay) RX_EOPOUT0 = RX_EOPOUT0_delay;
  assign #(out_delay) RX_EOPOUT1 = RX_EOPOUT1_delay;
  assign #(out_delay) RX_EOPOUT2 = RX_EOPOUT2_delay;
  assign #(out_delay) RX_EOPOUT3 = RX_EOPOUT3_delay;
  assign #(out_delay) RX_ERROUT0 = RX_ERROUT0_delay;
  assign #(out_delay) RX_ERROUT1 = RX_ERROUT1_delay;
  assign #(out_delay) RX_ERROUT2 = RX_ERROUT2_delay;
  assign #(out_delay) RX_ERROUT3 = RX_ERROUT3_delay;
  assign #(out_delay) RX_LANE_ALIGNER_FILL_0 = RX_LANE_ALIGNER_FILL_0_delay;
  assign #(out_delay) RX_LANE_ALIGNER_FILL_1 = RX_LANE_ALIGNER_FILL_1_delay;
  assign #(out_delay) RX_LANE_ALIGNER_FILL_10 = RX_LANE_ALIGNER_FILL_10_delay;
  assign #(out_delay) RX_LANE_ALIGNER_FILL_11 = RX_LANE_ALIGNER_FILL_11_delay;
  assign #(out_delay) RX_LANE_ALIGNER_FILL_12 = RX_LANE_ALIGNER_FILL_12_delay;
  assign #(out_delay) RX_LANE_ALIGNER_FILL_13 = RX_LANE_ALIGNER_FILL_13_delay;
  assign #(out_delay) RX_LANE_ALIGNER_FILL_14 = RX_LANE_ALIGNER_FILL_14_delay;
  assign #(out_delay) RX_LANE_ALIGNER_FILL_15 = RX_LANE_ALIGNER_FILL_15_delay;
  assign #(out_delay) RX_LANE_ALIGNER_FILL_16 = RX_LANE_ALIGNER_FILL_16_delay;
  assign #(out_delay) RX_LANE_ALIGNER_FILL_17 = RX_LANE_ALIGNER_FILL_17_delay;
  assign #(out_delay) RX_LANE_ALIGNER_FILL_18 = RX_LANE_ALIGNER_FILL_18_delay;
  assign #(out_delay) RX_LANE_ALIGNER_FILL_19 = RX_LANE_ALIGNER_FILL_19_delay;
  assign #(out_delay) RX_LANE_ALIGNER_FILL_2 = RX_LANE_ALIGNER_FILL_2_delay;
  assign #(out_delay) RX_LANE_ALIGNER_FILL_3 = RX_LANE_ALIGNER_FILL_3_delay;
  assign #(out_delay) RX_LANE_ALIGNER_FILL_4 = RX_LANE_ALIGNER_FILL_4_delay;
  assign #(out_delay) RX_LANE_ALIGNER_FILL_5 = RX_LANE_ALIGNER_FILL_5_delay;
  assign #(out_delay) RX_LANE_ALIGNER_FILL_6 = RX_LANE_ALIGNER_FILL_6_delay;
  assign #(out_delay) RX_LANE_ALIGNER_FILL_7 = RX_LANE_ALIGNER_FILL_7_delay;
  assign #(out_delay) RX_LANE_ALIGNER_FILL_8 = RX_LANE_ALIGNER_FILL_8_delay;
  assign #(out_delay) RX_LANE_ALIGNER_FILL_9 = RX_LANE_ALIGNER_FILL_9_delay;
  assign #(out_delay) RX_MTYOUT0 = RX_MTYOUT0_delay;
  assign #(out_delay) RX_MTYOUT1 = RX_MTYOUT1_delay;
  assign #(out_delay) RX_MTYOUT2 = RX_MTYOUT2_delay;
  assign #(out_delay) RX_MTYOUT3 = RX_MTYOUT3_delay;
  assign #(out_delay) RX_PTP_PCSLANE_OUT = RX_PTP_PCSLANE_OUT_delay;
  assign #(out_delay) RX_PTP_TSTAMP_OUT = RX_PTP_TSTAMP_OUT_delay;
  assign #(out_delay) RX_SOPOUT0 = RX_SOPOUT0_delay;
  assign #(out_delay) RX_SOPOUT1 = RX_SOPOUT1_delay;
  assign #(out_delay) RX_SOPOUT2 = RX_SOPOUT2_delay;
  assign #(out_delay) RX_SOPOUT3 = RX_SOPOUT3_delay;
  assign #(out_delay) STAT_RX_ALIGNED = STAT_RX_ALIGNED_delay;
  assign #(out_delay) STAT_RX_ALIGNED_ERR = STAT_RX_ALIGNED_ERR_delay;
  assign #(out_delay) STAT_RX_BAD_CODE = STAT_RX_BAD_CODE_delay;
  assign #(out_delay) STAT_RX_BAD_FCS = STAT_RX_BAD_FCS_delay;
  assign #(out_delay) STAT_RX_BAD_PREAMBLE = STAT_RX_BAD_PREAMBLE_delay;
  assign #(out_delay) STAT_RX_BAD_SFD = STAT_RX_BAD_SFD_delay;
  assign #(out_delay) STAT_RX_BIP_ERR_0 = STAT_RX_BIP_ERR_0_delay;
  assign #(out_delay) STAT_RX_BIP_ERR_1 = STAT_RX_BIP_ERR_1_delay;
  assign #(out_delay) STAT_RX_BIP_ERR_10 = STAT_RX_BIP_ERR_10_delay;
  assign #(out_delay) STAT_RX_BIP_ERR_11 = STAT_RX_BIP_ERR_11_delay;
  assign #(out_delay) STAT_RX_BIP_ERR_12 = STAT_RX_BIP_ERR_12_delay;
  assign #(out_delay) STAT_RX_BIP_ERR_13 = STAT_RX_BIP_ERR_13_delay;
  assign #(out_delay) STAT_RX_BIP_ERR_14 = STAT_RX_BIP_ERR_14_delay;
  assign #(out_delay) STAT_RX_BIP_ERR_15 = STAT_RX_BIP_ERR_15_delay;
  assign #(out_delay) STAT_RX_BIP_ERR_16 = STAT_RX_BIP_ERR_16_delay;
  assign #(out_delay) STAT_RX_BIP_ERR_17 = STAT_RX_BIP_ERR_17_delay;
  assign #(out_delay) STAT_RX_BIP_ERR_18 = STAT_RX_BIP_ERR_18_delay;
  assign #(out_delay) STAT_RX_BIP_ERR_19 = STAT_RX_BIP_ERR_19_delay;
  assign #(out_delay) STAT_RX_BIP_ERR_2 = STAT_RX_BIP_ERR_2_delay;
  assign #(out_delay) STAT_RX_BIP_ERR_3 = STAT_RX_BIP_ERR_3_delay;
  assign #(out_delay) STAT_RX_BIP_ERR_4 = STAT_RX_BIP_ERR_4_delay;
  assign #(out_delay) STAT_RX_BIP_ERR_5 = STAT_RX_BIP_ERR_5_delay;
  assign #(out_delay) STAT_RX_BIP_ERR_6 = STAT_RX_BIP_ERR_6_delay;
  assign #(out_delay) STAT_RX_BIP_ERR_7 = STAT_RX_BIP_ERR_7_delay;
  assign #(out_delay) STAT_RX_BIP_ERR_8 = STAT_RX_BIP_ERR_8_delay;
  assign #(out_delay) STAT_RX_BIP_ERR_9 = STAT_RX_BIP_ERR_9_delay;
  assign #(out_delay) STAT_RX_BLOCK_LOCK = STAT_RX_BLOCK_LOCK_delay;
  assign #(out_delay) STAT_RX_BROADCAST = STAT_RX_BROADCAST_delay;
  assign #(out_delay) STAT_RX_FRAGMENT = STAT_RX_FRAGMENT_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_0 = STAT_RX_FRAMING_ERR_0_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_1 = STAT_RX_FRAMING_ERR_1_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_10 = STAT_RX_FRAMING_ERR_10_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_11 = STAT_RX_FRAMING_ERR_11_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_12 = STAT_RX_FRAMING_ERR_12_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_13 = STAT_RX_FRAMING_ERR_13_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_14 = STAT_RX_FRAMING_ERR_14_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_15 = STAT_RX_FRAMING_ERR_15_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_16 = STAT_RX_FRAMING_ERR_16_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_17 = STAT_RX_FRAMING_ERR_17_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_18 = STAT_RX_FRAMING_ERR_18_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_19 = STAT_RX_FRAMING_ERR_19_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_2 = STAT_RX_FRAMING_ERR_2_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_3 = STAT_RX_FRAMING_ERR_3_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_4 = STAT_RX_FRAMING_ERR_4_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_5 = STAT_RX_FRAMING_ERR_5_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_6 = STAT_RX_FRAMING_ERR_6_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_7 = STAT_RX_FRAMING_ERR_7_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_8 = STAT_RX_FRAMING_ERR_8_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_9 = STAT_RX_FRAMING_ERR_9_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_VALID_0 = STAT_RX_FRAMING_ERR_VALID_0_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_VALID_1 = STAT_RX_FRAMING_ERR_VALID_1_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_VALID_10 = STAT_RX_FRAMING_ERR_VALID_10_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_VALID_11 = STAT_RX_FRAMING_ERR_VALID_11_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_VALID_12 = STAT_RX_FRAMING_ERR_VALID_12_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_VALID_13 = STAT_RX_FRAMING_ERR_VALID_13_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_VALID_14 = STAT_RX_FRAMING_ERR_VALID_14_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_VALID_15 = STAT_RX_FRAMING_ERR_VALID_15_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_VALID_16 = STAT_RX_FRAMING_ERR_VALID_16_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_VALID_17 = STAT_RX_FRAMING_ERR_VALID_17_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_VALID_18 = STAT_RX_FRAMING_ERR_VALID_18_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_VALID_19 = STAT_RX_FRAMING_ERR_VALID_19_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_VALID_2 = STAT_RX_FRAMING_ERR_VALID_2_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_VALID_3 = STAT_RX_FRAMING_ERR_VALID_3_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_VALID_4 = STAT_RX_FRAMING_ERR_VALID_4_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_VALID_5 = STAT_RX_FRAMING_ERR_VALID_5_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_VALID_6 = STAT_RX_FRAMING_ERR_VALID_6_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_VALID_7 = STAT_RX_FRAMING_ERR_VALID_7_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_VALID_8 = STAT_RX_FRAMING_ERR_VALID_8_delay;
  assign #(out_delay) STAT_RX_FRAMING_ERR_VALID_9 = STAT_RX_FRAMING_ERR_VALID_9_delay;
  assign #(out_delay) STAT_RX_GOT_SIGNAL_OS = STAT_RX_GOT_SIGNAL_OS_delay;
  assign #(out_delay) STAT_RX_HI_BER = STAT_RX_HI_BER_delay;
  assign #(out_delay) STAT_RX_INRANGEERR = STAT_RX_INRANGEERR_delay;
  assign #(out_delay) STAT_RX_INTERNAL_LOCAL_FAULT = STAT_RX_INTERNAL_LOCAL_FAULT_delay;
  assign #(out_delay) STAT_RX_JABBER = STAT_RX_JABBER_delay;
  assign #(out_delay) STAT_RX_LANE0_VLM_BIP7 = STAT_RX_LANE0_VLM_BIP7_delay;
  assign #(out_delay) STAT_RX_LANE0_VLM_BIP7_VALID = STAT_RX_LANE0_VLM_BIP7_VALID_delay;
  assign #(out_delay) STAT_RX_LOCAL_FAULT = STAT_RX_LOCAL_FAULT_delay;
  assign #(out_delay) STAT_RX_MF_ERR = STAT_RX_MF_ERR_delay;
  assign #(out_delay) STAT_RX_MF_LEN_ERR = STAT_RX_MF_LEN_ERR_delay;
  assign #(out_delay) STAT_RX_MF_REPEAT_ERR = STAT_RX_MF_REPEAT_ERR_delay;
  assign #(out_delay) STAT_RX_MISALIGNED = STAT_RX_MISALIGNED_delay;
  assign #(out_delay) STAT_RX_MULTICAST = STAT_RX_MULTICAST_delay;
  assign #(out_delay) STAT_RX_OVERSIZE = STAT_RX_OVERSIZE_delay;
  assign #(out_delay) STAT_RX_PACKET_1024_1518_BYTES = STAT_RX_PACKET_1024_1518_BYTES_delay;
  assign #(out_delay) STAT_RX_PACKET_128_255_BYTES = STAT_RX_PACKET_128_255_BYTES_delay;
  assign #(out_delay) STAT_RX_PACKET_1519_1522_BYTES = STAT_RX_PACKET_1519_1522_BYTES_delay;
  assign #(out_delay) STAT_RX_PACKET_1523_1548_BYTES = STAT_RX_PACKET_1523_1548_BYTES_delay;
  assign #(out_delay) STAT_RX_PACKET_1549_2047_BYTES = STAT_RX_PACKET_1549_2047_BYTES_delay;
  assign #(out_delay) STAT_RX_PACKET_2048_4095_BYTES = STAT_RX_PACKET_2048_4095_BYTES_delay;
  assign #(out_delay) STAT_RX_PACKET_256_511_BYTES = STAT_RX_PACKET_256_511_BYTES_delay;
  assign #(out_delay) STAT_RX_PACKET_4096_8191_BYTES = STAT_RX_PACKET_4096_8191_BYTES_delay;
  assign #(out_delay) STAT_RX_PACKET_512_1023_BYTES = STAT_RX_PACKET_512_1023_BYTES_delay;
  assign #(out_delay) STAT_RX_PACKET_64_BYTES = STAT_RX_PACKET_64_BYTES_delay;
  assign #(out_delay) STAT_RX_PACKET_65_127_BYTES = STAT_RX_PACKET_65_127_BYTES_delay;
  assign #(out_delay) STAT_RX_PACKET_8192_9215_BYTES = STAT_RX_PACKET_8192_9215_BYTES_delay;
  assign #(out_delay) STAT_RX_PACKET_BAD_FCS = STAT_RX_PACKET_BAD_FCS_delay;
  assign #(out_delay) STAT_RX_PACKET_LARGE = STAT_RX_PACKET_LARGE_delay;
  assign #(out_delay) STAT_RX_PACKET_SMALL = STAT_RX_PACKET_SMALL_delay;
  assign #(out_delay) STAT_RX_PAUSE = STAT_RX_PAUSE_delay;
  assign #(out_delay) STAT_RX_PAUSE_QUANTA0 = STAT_RX_PAUSE_QUANTA0_delay;
  assign #(out_delay) STAT_RX_PAUSE_QUANTA1 = STAT_RX_PAUSE_QUANTA1_delay;
  assign #(out_delay) STAT_RX_PAUSE_QUANTA2 = STAT_RX_PAUSE_QUANTA2_delay;
  assign #(out_delay) STAT_RX_PAUSE_QUANTA3 = STAT_RX_PAUSE_QUANTA3_delay;
  assign #(out_delay) STAT_RX_PAUSE_QUANTA4 = STAT_RX_PAUSE_QUANTA4_delay;
  assign #(out_delay) STAT_RX_PAUSE_QUANTA5 = STAT_RX_PAUSE_QUANTA5_delay;
  assign #(out_delay) STAT_RX_PAUSE_QUANTA6 = STAT_RX_PAUSE_QUANTA6_delay;
  assign #(out_delay) STAT_RX_PAUSE_QUANTA7 = STAT_RX_PAUSE_QUANTA7_delay;
  assign #(out_delay) STAT_RX_PAUSE_QUANTA8 = STAT_RX_PAUSE_QUANTA8_delay;
  assign #(out_delay) STAT_RX_PAUSE_REQ = STAT_RX_PAUSE_REQ_delay;
  assign #(out_delay) STAT_RX_PAUSE_VALID = STAT_RX_PAUSE_VALID_delay;
  assign #(out_delay) STAT_RX_RECEIVED_LOCAL_FAULT = STAT_RX_RECEIVED_LOCAL_FAULT_delay;
  assign #(out_delay) STAT_RX_REMOTE_FAULT = STAT_RX_REMOTE_FAULT_delay;
  assign #(out_delay) STAT_RX_STATUS = STAT_RX_STATUS_delay;
  assign #(out_delay) STAT_RX_STOMPED_FCS = STAT_RX_STOMPED_FCS_delay;
  assign #(out_delay) STAT_RX_SYNCED = STAT_RX_SYNCED_delay;
  assign #(out_delay) STAT_RX_SYNCED_ERR = STAT_RX_SYNCED_ERR_delay;
  assign #(out_delay) STAT_RX_TEST_PATTERN_MISMATCH = STAT_RX_TEST_PATTERN_MISMATCH_delay;
  assign #(out_delay) STAT_RX_TOOLONG = STAT_RX_TOOLONG_delay;
  assign #(out_delay) STAT_RX_TOTAL_BYTES = STAT_RX_TOTAL_BYTES_delay;
  assign #(out_delay) STAT_RX_TOTAL_GOOD_BYTES = STAT_RX_TOTAL_GOOD_BYTES_delay;
  assign #(out_delay) STAT_RX_TOTAL_GOOD_PACKETS = STAT_RX_TOTAL_GOOD_PACKETS_delay;
  assign #(out_delay) STAT_RX_TOTAL_PACKETS = STAT_RX_TOTAL_PACKETS_delay;
  assign #(out_delay) STAT_RX_TRUNCATED = STAT_RX_TRUNCATED_delay;
  assign #(out_delay) STAT_RX_UNDERSIZE = STAT_RX_UNDERSIZE_delay;
  assign #(out_delay) STAT_RX_UNICAST = STAT_RX_UNICAST_delay;
  assign #(out_delay) STAT_RX_USER_PAUSE = STAT_RX_USER_PAUSE_delay;
  assign #(out_delay) STAT_RX_VLAN = STAT_RX_VLAN_delay;
  assign #(out_delay) STAT_RX_VL_DEMUXED = STAT_RX_VL_DEMUXED_delay;
  assign #(out_delay) STAT_RX_VL_NUMBER_0 = STAT_RX_VL_NUMBER_0_delay;
  assign #(out_delay) STAT_RX_VL_NUMBER_1 = STAT_RX_VL_NUMBER_1_delay;
  assign #(out_delay) STAT_RX_VL_NUMBER_10 = STAT_RX_VL_NUMBER_10_delay;
  assign #(out_delay) STAT_RX_VL_NUMBER_11 = STAT_RX_VL_NUMBER_11_delay;
  assign #(out_delay) STAT_RX_VL_NUMBER_12 = STAT_RX_VL_NUMBER_12_delay;
  assign #(out_delay) STAT_RX_VL_NUMBER_13 = STAT_RX_VL_NUMBER_13_delay;
  assign #(out_delay) STAT_RX_VL_NUMBER_14 = STAT_RX_VL_NUMBER_14_delay;
  assign #(out_delay) STAT_RX_VL_NUMBER_15 = STAT_RX_VL_NUMBER_15_delay;
  assign #(out_delay) STAT_RX_VL_NUMBER_16 = STAT_RX_VL_NUMBER_16_delay;
  assign #(out_delay) STAT_RX_VL_NUMBER_17 = STAT_RX_VL_NUMBER_17_delay;
  assign #(out_delay) STAT_RX_VL_NUMBER_18 = STAT_RX_VL_NUMBER_18_delay;
  assign #(out_delay) STAT_RX_VL_NUMBER_19 = STAT_RX_VL_NUMBER_19_delay;
  assign #(out_delay) STAT_RX_VL_NUMBER_2 = STAT_RX_VL_NUMBER_2_delay;
  assign #(out_delay) STAT_RX_VL_NUMBER_3 = STAT_RX_VL_NUMBER_3_delay;
  assign #(out_delay) STAT_RX_VL_NUMBER_4 = STAT_RX_VL_NUMBER_4_delay;
  assign #(out_delay) STAT_RX_VL_NUMBER_5 = STAT_RX_VL_NUMBER_5_delay;
  assign #(out_delay) STAT_RX_VL_NUMBER_6 = STAT_RX_VL_NUMBER_6_delay;
  assign #(out_delay) STAT_RX_VL_NUMBER_7 = STAT_RX_VL_NUMBER_7_delay;
  assign #(out_delay) STAT_RX_VL_NUMBER_8 = STAT_RX_VL_NUMBER_8_delay;
  assign #(out_delay) STAT_RX_VL_NUMBER_9 = STAT_RX_VL_NUMBER_9_delay;
  assign #(out_delay) STAT_TX_BAD_FCS = STAT_TX_BAD_FCS_delay;
  assign #(out_delay) STAT_TX_BROADCAST = STAT_TX_BROADCAST_delay;
  assign #(out_delay) STAT_TX_FRAME_ERROR = STAT_TX_FRAME_ERROR_delay;
  assign #(out_delay) STAT_TX_LOCAL_FAULT = STAT_TX_LOCAL_FAULT_delay;
  assign #(out_delay) STAT_TX_MULTICAST = STAT_TX_MULTICAST_delay;
  assign #(out_delay) STAT_TX_PACKET_1024_1518_BYTES = STAT_TX_PACKET_1024_1518_BYTES_delay;
  assign #(out_delay) STAT_TX_PACKET_128_255_BYTES = STAT_TX_PACKET_128_255_BYTES_delay;
  assign #(out_delay) STAT_TX_PACKET_1519_1522_BYTES = STAT_TX_PACKET_1519_1522_BYTES_delay;
  assign #(out_delay) STAT_TX_PACKET_1523_1548_BYTES = STAT_TX_PACKET_1523_1548_BYTES_delay;
  assign #(out_delay) STAT_TX_PACKET_1549_2047_BYTES = STAT_TX_PACKET_1549_2047_BYTES_delay;
  assign #(out_delay) STAT_TX_PACKET_2048_4095_BYTES = STAT_TX_PACKET_2048_4095_BYTES_delay;
  assign #(out_delay) STAT_TX_PACKET_256_511_BYTES = STAT_TX_PACKET_256_511_BYTES_delay;
  assign #(out_delay) STAT_TX_PACKET_4096_8191_BYTES = STAT_TX_PACKET_4096_8191_BYTES_delay;
  assign #(out_delay) STAT_TX_PACKET_512_1023_BYTES = STAT_TX_PACKET_512_1023_BYTES_delay;
  assign #(out_delay) STAT_TX_PACKET_64_BYTES = STAT_TX_PACKET_64_BYTES_delay;
  assign #(out_delay) STAT_TX_PACKET_65_127_BYTES = STAT_TX_PACKET_65_127_BYTES_delay;
  assign #(out_delay) STAT_TX_PACKET_8192_9215_BYTES = STAT_TX_PACKET_8192_9215_BYTES_delay;
  assign #(out_delay) STAT_TX_PACKET_LARGE = STAT_TX_PACKET_LARGE_delay;
  assign #(out_delay) STAT_TX_PACKET_SMALL = STAT_TX_PACKET_SMALL_delay;
  assign #(out_delay) STAT_TX_PAUSE = STAT_TX_PAUSE_delay;
  assign #(out_delay) STAT_TX_PAUSE_VALID = STAT_TX_PAUSE_VALID_delay;
  assign #(out_delay) STAT_TX_PTP_FIFO_READ_ERROR = STAT_TX_PTP_FIFO_READ_ERROR_delay;
  assign #(out_delay) STAT_TX_PTP_FIFO_WRITE_ERROR = STAT_TX_PTP_FIFO_WRITE_ERROR_delay;
  assign #(out_delay) STAT_TX_TOTAL_BYTES = STAT_TX_TOTAL_BYTES_delay;
  assign #(out_delay) STAT_TX_TOTAL_GOOD_BYTES = STAT_TX_TOTAL_GOOD_BYTES_delay;
  assign #(out_delay) STAT_TX_TOTAL_GOOD_PACKETS = STAT_TX_TOTAL_GOOD_PACKETS_delay;
  assign #(out_delay) STAT_TX_TOTAL_PACKETS = STAT_TX_TOTAL_PACKETS_delay;
  assign #(out_delay) STAT_TX_UNICAST = STAT_TX_UNICAST_delay;
  assign #(out_delay) STAT_TX_USER_PAUSE = STAT_TX_USER_PAUSE_delay;
  assign #(out_delay) STAT_TX_VLAN = STAT_TX_VLAN_delay;
  assign #(out_delay) TX_OVFOUT = TX_OVFOUT_delay;
  assign #(out_delay) TX_PTP_PCSLANE_OUT = TX_PTP_PCSLANE_OUT_delay;
  assign #(out_delay) TX_PTP_TSTAMP_OUT = TX_PTP_TSTAMP_OUT_delay;
  assign #(out_delay) TX_PTP_TSTAMP_TAG_OUT = TX_PTP_TSTAMP_TAG_OUT_delay;
  assign #(out_delay) TX_PTP_TSTAMP_VALID_OUT = TX_PTP_TSTAMP_VALID_OUT_delay;
  assign #(out_delay) TX_RDYOUT = TX_RDYOUT_delay;
  assign #(out_delay) TX_SERDES_ALT_DATA0 = TX_SERDES_ALT_DATA0_delay;
  assign #(out_delay) TX_SERDES_ALT_DATA1 = TX_SERDES_ALT_DATA1_delay;
  assign #(out_delay) TX_SERDES_ALT_DATA2 = TX_SERDES_ALT_DATA2_delay;
  assign #(out_delay) TX_SERDES_ALT_DATA3 = TX_SERDES_ALT_DATA3_delay;
  assign #(out_delay) TX_SERDES_DATA0 = TX_SERDES_DATA0_delay;
  assign #(out_delay) TX_SERDES_DATA1 = TX_SERDES_DATA1_delay;
  assign #(out_delay) TX_SERDES_DATA2 = TX_SERDES_DATA2_delay;
  assign #(out_delay) TX_SERDES_DATA3 = TX_SERDES_DATA3_delay;
  assign #(out_delay) TX_SERDES_DATA4 = TX_SERDES_DATA4_delay;
  assign #(out_delay) TX_SERDES_DATA5 = TX_SERDES_DATA5_delay;
  assign #(out_delay) TX_SERDES_DATA6 = TX_SERDES_DATA6_delay;
  assign #(out_delay) TX_SERDES_DATA7 = TX_SERDES_DATA7_delay;
  assign #(out_delay) TX_SERDES_DATA8 = TX_SERDES_DATA8_delay;
  assign #(out_delay) TX_SERDES_DATA9 = TX_SERDES_DATA9_delay;
  assign #(out_delay) TX_UNFOUT = TX_UNFOUT_delay;





 // inputs with timing checks
  assign #(inclk_delay) DRP_CLK_delay = DRP_CLK;
  assign #(inclk_delay) RX_CLK_delay = RX_CLK;
  assign #(inclk_delay) TX_CLK_delay = TX_CLK;

  assign #(in_delay) CTL_CAUI4_MODE_delay = CTL_CAUI4_MODE;
  assign #(in_delay) CTL_RX_CHECK_ETYPE_GCP_delay = CTL_RX_CHECK_ETYPE_GCP;
  assign #(in_delay) CTL_RX_CHECK_ETYPE_GPP_delay = CTL_RX_CHECK_ETYPE_GPP;
  assign #(in_delay) CTL_RX_CHECK_ETYPE_PCP_delay = CTL_RX_CHECK_ETYPE_PCP;
  assign #(in_delay) CTL_RX_CHECK_ETYPE_PPP_delay = CTL_RX_CHECK_ETYPE_PPP;
  assign #(in_delay) CTL_RX_CHECK_MCAST_GCP_delay = CTL_RX_CHECK_MCAST_GCP;
  assign #(in_delay) CTL_RX_CHECK_MCAST_GPP_delay = CTL_RX_CHECK_MCAST_GPP;
  assign #(in_delay) CTL_RX_CHECK_MCAST_PCP_delay = CTL_RX_CHECK_MCAST_PCP;
  assign #(in_delay) CTL_RX_CHECK_MCAST_PPP_delay = CTL_RX_CHECK_MCAST_PPP;
  assign #(in_delay) CTL_RX_CHECK_OPCODE_GCP_delay = CTL_RX_CHECK_OPCODE_GCP;
  assign #(in_delay) CTL_RX_CHECK_OPCODE_GPP_delay = CTL_RX_CHECK_OPCODE_GPP;
  assign #(in_delay) CTL_RX_CHECK_OPCODE_PCP_delay = CTL_RX_CHECK_OPCODE_PCP;
  assign #(in_delay) CTL_RX_CHECK_OPCODE_PPP_delay = CTL_RX_CHECK_OPCODE_PPP;
  assign #(in_delay) CTL_RX_CHECK_SA_GCP_delay = CTL_RX_CHECK_SA_GCP;
  assign #(in_delay) CTL_RX_CHECK_SA_GPP_delay = CTL_RX_CHECK_SA_GPP;
  assign #(in_delay) CTL_RX_CHECK_SA_PCP_delay = CTL_RX_CHECK_SA_PCP;
  assign #(in_delay) CTL_RX_CHECK_SA_PPP_delay = CTL_RX_CHECK_SA_PPP;
  assign #(in_delay) CTL_RX_CHECK_UCAST_GCP_delay = CTL_RX_CHECK_UCAST_GCP;
  assign #(in_delay) CTL_RX_CHECK_UCAST_GPP_delay = CTL_RX_CHECK_UCAST_GPP;
  assign #(in_delay) CTL_RX_CHECK_UCAST_PCP_delay = CTL_RX_CHECK_UCAST_PCP;
  assign #(in_delay) CTL_RX_CHECK_UCAST_PPP_delay = CTL_RX_CHECK_UCAST_PPP;
  assign #(in_delay) CTL_RX_ENABLE_GCP_delay = CTL_RX_ENABLE_GCP;
  assign #(in_delay) CTL_RX_ENABLE_GPP_delay = CTL_RX_ENABLE_GPP;
  assign #(in_delay) CTL_RX_ENABLE_PCP_delay = CTL_RX_ENABLE_PCP;
  assign #(in_delay) CTL_RX_ENABLE_PPP_delay = CTL_RX_ENABLE_PPP;
  assign #(in_delay) CTL_RX_ENABLE_delay = CTL_RX_ENABLE;
  assign #(in_delay) CTL_RX_FORCE_RESYNC_delay = CTL_RX_FORCE_RESYNC;
  assign #(in_delay) CTL_RX_PAUSE_ACK_delay = CTL_RX_PAUSE_ACK;
  assign #(in_delay) CTL_RX_PAUSE_ENABLE_delay = CTL_RX_PAUSE_ENABLE;
  assign #(in_delay) CTL_RX_SYSTEMTIMERIN_delay = CTL_RX_SYSTEMTIMERIN;
  assign #(in_delay) CTL_RX_TEST_PATTERN_delay = CTL_RX_TEST_PATTERN;
  assign #(in_delay) CTL_TX_ENABLE_delay = CTL_TX_ENABLE;
  assign #(in_delay) CTL_TX_LANE0_VLM_BIP7_OVERRIDE_VALUE_delay = CTL_TX_LANE0_VLM_BIP7_OVERRIDE_VALUE;
  assign #(in_delay) CTL_TX_LANE0_VLM_BIP7_OVERRIDE_delay = CTL_TX_LANE0_VLM_BIP7_OVERRIDE;
  assign #(in_delay) CTL_TX_PAUSE_ENABLE_delay = CTL_TX_PAUSE_ENABLE;
  assign #(in_delay) CTL_TX_PAUSE_QUANTA0_delay = CTL_TX_PAUSE_QUANTA0;
  assign #(in_delay) CTL_TX_PAUSE_QUANTA1_delay = CTL_TX_PAUSE_QUANTA1;
  assign #(in_delay) CTL_TX_PAUSE_QUANTA2_delay = CTL_TX_PAUSE_QUANTA2;
  assign #(in_delay) CTL_TX_PAUSE_QUANTA3_delay = CTL_TX_PAUSE_QUANTA3;
  assign #(in_delay) CTL_TX_PAUSE_QUANTA4_delay = CTL_TX_PAUSE_QUANTA4;
  assign #(in_delay) CTL_TX_PAUSE_QUANTA5_delay = CTL_TX_PAUSE_QUANTA5;
  assign #(in_delay) CTL_TX_PAUSE_QUANTA6_delay = CTL_TX_PAUSE_QUANTA6;
  assign #(in_delay) CTL_TX_PAUSE_QUANTA7_delay = CTL_TX_PAUSE_QUANTA7;
  assign #(in_delay) CTL_TX_PAUSE_QUANTA8_delay = CTL_TX_PAUSE_QUANTA8;
  assign #(in_delay) CTL_TX_PAUSE_REFRESH_TIMER0_delay = CTL_TX_PAUSE_REFRESH_TIMER0;
  assign #(in_delay) CTL_TX_PAUSE_REFRESH_TIMER1_delay = CTL_TX_PAUSE_REFRESH_TIMER1;
  assign #(in_delay) CTL_TX_PAUSE_REFRESH_TIMER2_delay = CTL_TX_PAUSE_REFRESH_TIMER2;
  assign #(in_delay) CTL_TX_PAUSE_REFRESH_TIMER3_delay = CTL_TX_PAUSE_REFRESH_TIMER3;
  assign #(in_delay) CTL_TX_PAUSE_REFRESH_TIMER4_delay = CTL_TX_PAUSE_REFRESH_TIMER4;
  assign #(in_delay) CTL_TX_PAUSE_REFRESH_TIMER5_delay = CTL_TX_PAUSE_REFRESH_TIMER5;
  assign #(in_delay) CTL_TX_PAUSE_REFRESH_TIMER6_delay = CTL_TX_PAUSE_REFRESH_TIMER6;
  assign #(in_delay) CTL_TX_PAUSE_REFRESH_TIMER7_delay = CTL_TX_PAUSE_REFRESH_TIMER7;
  assign #(in_delay) CTL_TX_PAUSE_REFRESH_TIMER8_delay = CTL_TX_PAUSE_REFRESH_TIMER8;
  assign #(in_delay) CTL_TX_PAUSE_REQ_delay = CTL_TX_PAUSE_REQ;
  assign #(in_delay) CTL_TX_PTP_VLANE_ADJUST_MODE_delay = CTL_TX_PTP_VLANE_ADJUST_MODE;
  assign #(in_delay) CTL_TX_RESEND_PAUSE_delay = CTL_TX_RESEND_PAUSE;
  assign #(in_delay) CTL_TX_SEND_IDLE_delay = CTL_TX_SEND_IDLE;
  assign #(in_delay) CTL_TX_SEND_RFI_delay = CTL_TX_SEND_RFI;
  assign #(in_delay) CTL_TX_SYSTEMTIMERIN_delay = CTL_TX_SYSTEMTIMERIN;
  assign #(in_delay) CTL_TX_TEST_PATTERN_delay = CTL_TX_TEST_PATTERN;
  assign #(in_delay) DRP_ADDR_delay = DRP_ADDR;
  assign #(in_delay) DRP_DI_delay = DRP_DI;
  assign #(in_delay) DRP_EN_delay = DRP_EN;
  assign #(in_delay) DRP_WE_delay = DRP_WE;
  assign #(in_delay) RX_RESET_delay = RX_RESET;
  assign #(in_delay) RX_SERDES_ALT_DATA0_delay = RX_SERDES_ALT_DATA0;
  assign #(in_delay) RX_SERDES_ALT_DATA1_delay = RX_SERDES_ALT_DATA1;
  assign #(in_delay) RX_SERDES_ALT_DATA2_delay = RX_SERDES_ALT_DATA2;
  assign #(in_delay) RX_SERDES_ALT_DATA3_delay = RX_SERDES_ALT_DATA3;
  assign #(in_delay) RX_SERDES_DATA0_delay = RX_SERDES_DATA0;
  assign #(in_delay) RX_SERDES_DATA1_delay = RX_SERDES_DATA1;
  assign #(in_delay) RX_SERDES_DATA2_delay = RX_SERDES_DATA2;
  assign #(in_delay) RX_SERDES_DATA3_delay = RX_SERDES_DATA3;
  assign #(in_delay) RX_SERDES_DATA4_delay = RX_SERDES_DATA4;
  assign #(in_delay) RX_SERDES_DATA5_delay = RX_SERDES_DATA5;
  assign #(in_delay) RX_SERDES_DATA6_delay = RX_SERDES_DATA6;
  assign #(in_delay) RX_SERDES_DATA7_delay = RX_SERDES_DATA7;
  assign #(in_delay) RX_SERDES_DATA8_delay = RX_SERDES_DATA8;
  assign #(in_delay) RX_SERDES_DATA9_delay = RX_SERDES_DATA9;
  assign #(in_delay) RX_SERDES_RESET_delay = RX_SERDES_RESET;
  assign #(in_delay) TX_DATAIN0_delay = TX_DATAIN0;
  assign #(in_delay) TX_DATAIN1_delay = TX_DATAIN1;
  assign #(in_delay) TX_DATAIN2_delay = TX_DATAIN2;
  assign #(in_delay) TX_DATAIN3_delay = TX_DATAIN3;
  assign #(in_delay) TX_ENAIN0_delay = TX_ENAIN0;
  assign #(in_delay) TX_ENAIN1_delay = TX_ENAIN1;
  assign #(in_delay) TX_ENAIN2_delay = TX_ENAIN2;
  assign #(in_delay) TX_ENAIN3_delay = TX_ENAIN3;
  assign #(in_delay) TX_EOPIN0_delay = TX_EOPIN0;
  assign #(in_delay) TX_EOPIN1_delay = TX_EOPIN1;
  assign #(in_delay) TX_EOPIN2_delay = TX_EOPIN2;
  assign #(in_delay) TX_EOPIN3_delay = TX_EOPIN3;
  assign #(in_delay) TX_ERRIN0_delay = TX_ERRIN0;
  assign #(in_delay) TX_ERRIN1_delay = TX_ERRIN1;
  assign #(in_delay) TX_ERRIN2_delay = TX_ERRIN2;
  assign #(in_delay) TX_ERRIN3_delay = TX_ERRIN3;
  assign #(in_delay) TX_MTYIN0_delay = TX_MTYIN0;
  assign #(in_delay) TX_MTYIN1_delay = TX_MTYIN1;
  assign #(in_delay) TX_MTYIN2_delay = TX_MTYIN2;
  assign #(in_delay) TX_MTYIN3_delay = TX_MTYIN3;
  assign #(in_delay) TX_PTP_1588OP_IN_delay = TX_PTP_1588OP_IN;
  assign #(in_delay) TX_PTP_CHKSUM_OFFSET_IN_delay = TX_PTP_CHKSUM_OFFSET_IN;
  assign #(in_delay) TX_PTP_RXTSTAMP_IN_delay = TX_PTP_RXTSTAMP_IN;
  assign #(in_delay) TX_PTP_TAG_FIELD_IN_delay = TX_PTP_TAG_FIELD_IN;
  assign #(in_delay) TX_PTP_TSTAMP_OFFSET_IN_delay = TX_PTP_TSTAMP_OFFSET_IN;
  assign #(in_delay) TX_PTP_UPD_CHKSUM_IN_delay = TX_PTP_UPD_CHKSUM_IN;
  assign #(in_delay) TX_RESET_delay = TX_RESET;
  assign #(in_delay) TX_SOPIN0_delay = TX_SOPIN0;
  assign #(in_delay) TX_SOPIN1_delay = TX_SOPIN1;
  assign #(in_delay) TX_SOPIN2_delay = TX_SOPIN2;
  assign #(in_delay) TX_SOPIN3_delay = TX_SOPIN3;
  assign #(inclk_delay) RX_SERDES_CLK_delay = RX_SERDES_CLK;


// inputs with no timing checks
  //assign #(inclk_delay) RX_SERDES_CLK_delay = RX_SERDES_CLK;


  assign DRP_DO_delay = DRP_DO_out;
  assign DRP_RDY_delay = DRP_RDY_out;
  assign RX_DATAOUT0_delay = RX_DATAOUT0_out;
  assign RX_DATAOUT1_delay = RX_DATAOUT1_out;
  assign RX_DATAOUT2_delay = RX_DATAOUT2_out;
  assign RX_DATAOUT3_delay = RX_DATAOUT3_out;
  assign RX_ENAOUT0_delay = RX_ENAOUT0_out;
  assign RX_ENAOUT1_delay = RX_ENAOUT1_out;
  assign RX_ENAOUT2_delay = RX_ENAOUT2_out;
  assign RX_ENAOUT3_delay = RX_ENAOUT3_out;
  assign RX_EOPOUT0_delay = RX_EOPOUT0_out;
  assign RX_EOPOUT1_delay = RX_EOPOUT1_out;
  assign RX_EOPOUT2_delay = RX_EOPOUT2_out;
  assign RX_EOPOUT3_delay = RX_EOPOUT3_out;
  assign RX_ERROUT0_delay = RX_ERROUT0_out;
  assign RX_ERROUT1_delay = RX_ERROUT1_out;
  assign RX_ERROUT2_delay = RX_ERROUT2_out;
  assign RX_ERROUT3_delay = RX_ERROUT3_out;
  assign RX_LANE_ALIGNER_FILL_0_delay = RX_LANE_ALIGNER_FILL_0_out;
  assign RX_LANE_ALIGNER_FILL_10_delay = RX_LANE_ALIGNER_FILL_10_out;
  assign RX_LANE_ALIGNER_FILL_11_delay = RX_LANE_ALIGNER_FILL_11_out;
  assign RX_LANE_ALIGNER_FILL_12_delay = RX_LANE_ALIGNER_FILL_12_out;
  assign RX_LANE_ALIGNER_FILL_13_delay = RX_LANE_ALIGNER_FILL_13_out;
  assign RX_LANE_ALIGNER_FILL_14_delay = RX_LANE_ALIGNER_FILL_14_out;
  assign RX_LANE_ALIGNER_FILL_15_delay = RX_LANE_ALIGNER_FILL_15_out;
  assign RX_LANE_ALIGNER_FILL_16_delay = RX_LANE_ALIGNER_FILL_16_out;
  assign RX_LANE_ALIGNER_FILL_17_delay = RX_LANE_ALIGNER_FILL_17_out;
  assign RX_LANE_ALIGNER_FILL_18_delay = RX_LANE_ALIGNER_FILL_18_out;
  assign RX_LANE_ALIGNER_FILL_19_delay = RX_LANE_ALIGNER_FILL_19_out;
  assign RX_LANE_ALIGNER_FILL_1_delay = RX_LANE_ALIGNER_FILL_1_out;
  assign RX_LANE_ALIGNER_FILL_2_delay = RX_LANE_ALIGNER_FILL_2_out;
  assign RX_LANE_ALIGNER_FILL_3_delay = RX_LANE_ALIGNER_FILL_3_out;
  assign RX_LANE_ALIGNER_FILL_4_delay = RX_LANE_ALIGNER_FILL_4_out;
  assign RX_LANE_ALIGNER_FILL_5_delay = RX_LANE_ALIGNER_FILL_5_out;
  assign RX_LANE_ALIGNER_FILL_6_delay = RX_LANE_ALIGNER_FILL_6_out;
  assign RX_LANE_ALIGNER_FILL_7_delay = RX_LANE_ALIGNER_FILL_7_out;
  assign RX_LANE_ALIGNER_FILL_8_delay = RX_LANE_ALIGNER_FILL_8_out;
  assign RX_LANE_ALIGNER_FILL_9_delay = RX_LANE_ALIGNER_FILL_9_out;
  assign RX_MTYOUT0_delay = RX_MTYOUT0_out;
  assign RX_MTYOUT1_delay = RX_MTYOUT1_out;
  assign RX_MTYOUT2_delay = RX_MTYOUT2_out;
  assign RX_MTYOUT3_delay = RX_MTYOUT3_out;
  assign RX_PTP_PCSLANE_OUT_delay = RX_PTP_PCSLANE_OUT_out;
  assign RX_PTP_TSTAMP_OUT_delay = RX_PTP_TSTAMP_OUT_out;
  assign RX_SOPOUT0_delay = RX_SOPOUT0_out;
  assign RX_SOPOUT1_delay = RX_SOPOUT1_out;
  assign RX_SOPOUT2_delay = RX_SOPOUT2_out;
  assign RX_SOPOUT3_delay = RX_SOPOUT3_out;
  assign STAT_RX_ALIGNED_ERR_delay = STAT_RX_ALIGNED_ERR_out;
  assign STAT_RX_ALIGNED_delay = STAT_RX_ALIGNED_out;
  assign STAT_RX_BAD_CODE_delay = STAT_RX_BAD_CODE_out;
  assign STAT_RX_BAD_FCS_delay = STAT_RX_BAD_FCS_out;
  assign STAT_RX_BAD_PREAMBLE_delay = STAT_RX_BAD_PREAMBLE_out;
  assign STAT_RX_BAD_SFD_delay = STAT_RX_BAD_SFD_out;
  assign STAT_RX_BIP_ERR_0_delay = STAT_RX_BIP_ERR_0_out;
  assign STAT_RX_BIP_ERR_10_delay = STAT_RX_BIP_ERR_10_out;
  assign STAT_RX_BIP_ERR_11_delay = STAT_RX_BIP_ERR_11_out;
  assign STAT_RX_BIP_ERR_12_delay = STAT_RX_BIP_ERR_12_out;
  assign STAT_RX_BIP_ERR_13_delay = STAT_RX_BIP_ERR_13_out;
  assign STAT_RX_BIP_ERR_14_delay = STAT_RX_BIP_ERR_14_out;
  assign STAT_RX_BIP_ERR_15_delay = STAT_RX_BIP_ERR_15_out;
  assign STAT_RX_BIP_ERR_16_delay = STAT_RX_BIP_ERR_16_out;
  assign STAT_RX_BIP_ERR_17_delay = STAT_RX_BIP_ERR_17_out;
  assign STAT_RX_BIP_ERR_18_delay = STAT_RX_BIP_ERR_18_out;
  assign STAT_RX_BIP_ERR_19_delay = STAT_RX_BIP_ERR_19_out;
  assign STAT_RX_BIP_ERR_1_delay = STAT_RX_BIP_ERR_1_out;
  assign STAT_RX_BIP_ERR_2_delay = STAT_RX_BIP_ERR_2_out;
  assign STAT_RX_BIP_ERR_3_delay = STAT_RX_BIP_ERR_3_out;
  assign STAT_RX_BIP_ERR_4_delay = STAT_RX_BIP_ERR_4_out;
  assign STAT_RX_BIP_ERR_5_delay = STAT_RX_BIP_ERR_5_out;
  assign STAT_RX_BIP_ERR_6_delay = STAT_RX_BIP_ERR_6_out;
  assign STAT_RX_BIP_ERR_7_delay = STAT_RX_BIP_ERR_7_out;
  assign STAT_RX_BIP_ERR_8_delay = STAT_RX_BIP_ERR_8_out;
  assign STAT_RX_BIP_ERR_9_delay = STAT_RX_BIP_ERR_9_out;
  assign STAT_RX_BLOCK_LOCK_delay = STAT_RX_BLOCK_LOCK_out;
  assign STAT_RX_BROADCAST_delay = STAT_RX_BROADCAST_out;
  assign STAT_RX_FRAGMENT_delay = STAT_RX_FRAGMENT_out;
  assign STAT_RX_FRAMING_ERR_0_delay = STAT_RX_FRAMING_ERR_0_out;
  assign STAT_RX_FRAMING_ERR_10_delay = STAT_RX_FRAMING_ERR_10_out;
  assign STAT_RX_FRAMING_ERR_11_delay = STAT_RX_FRAMING_ERR_11_out;
  assign STAT_RX_FRAMING_ERR_12_delay = STAT_RX_FRAMING_ERR_12_out;
  assign STAT_RX_FRAMING_ERR_13_delay = STAT_RX_FRAMING_ERR_13_out;
  assign STAT_RX_FRAMING_ERR_14_delay = STAT_RX_FRAMING_ERR_14_out;
  assign STAT_RX_FRAMING_ERR_15_delay = STAT_RX_FRAMING_ERR_15_out;
  assign STAT_RX_FRAMING_ERR_16_delay = STAT_RX_FRAMING_ERR_16_out;
  assign STAT_RX_FRAMING_ERR_17_delay = STAT_RX_FRAMING_ERR_17_out;
  assign STAT_RX_FRAMING_ERR_18_delay = STAT_RX_FRAMING_ERR_18_out;
  assign STAT_RX_FRAMING_ERR_19_delay = STAT_RX_FRAMING_ERR_19_out;
  assign STAT_RX_FRAMING_ERR_1_delay = STAT_RX_FRAMING_ERR_1_out;
  assign STAT_RX_FRAMING_ERR_2_delay = STAT_RX_FRAMING_ERR_2_out;
  assign STAT_RX_FRAMING_ERR_3_delay = STAT_RX_FRAMING_ERR_3_out;
  assign STAT_RX_FRAMING_ERR_4_delay = STAT_RX_FRAMING_ERR_4_out;
  assign STAT_RX_FRAMING_ERR_5_delay = STAT_RX_FRAMING_ERR_5_out;
  assign STAT_RX_FRAMING_ERR_6_delay = STAT_RX_FRAMING_ERR_6_out;
  assign STAT_RX_FRAMING_ERR_7_delay = STAT_RX_FRAMING_ERR_7_out;
  assign STAT_RX_FRAMING_ERR_8_delay = STAT_RX_FRAMING_ERR_8_out;
  assign STAT_RX_FRAMING_ERR_9_delay = STAT_RX_FRAMING_ERR_9_out;
  assign STAT_RX_FRAMING_ERR_VALID_0_delay = STAT_RX_FRAMING_ERR_VALID_0_out;
  assign STAT_RX_FRAMING_ERR_VALID_10_delay = STAT_RX_FRAMING_ERR_VALID_10_out;
  assign STAT_RX_FRAMING_ERR_VALID_11_delay = STAT_RX_FRAMING_ERR_VALID_11_out;
  assign STAT_RX_FRAMING_ERR_VALID_12_delay = STAT_RX_FRAMING_ERR_VALID_12_out;
  assign STAT_RX_FRAMING_ERR_VALID_13_delay = STAT_RX_FRAMING_ERR_VALID_13_out;
  assign STAT_RX_FRAMING_ERR_VALID_14_delay = STAT_RX_FRAMING_ERR_VALID_14_out;
  assign STAT_RX_FRAMING_ERR_VALID_15_delay = STAT_RX_FRAMING_ERR_VALID_15_out;
  assign STAT_RX_FRAMING_ERR_VALID_16_delay = STAT_RX_FRAMING_ERR_VALID_16_out;
  assign STAT_RX_FRAMING_ERR_VALID_17_delay = STAT_RX_FRAMING_ERR_VALID_17_out;
  assign STAT_RX_FRAMING_ERR_VALID_18_delay = STAT_RX_FRAMING_ERR_VALID_18_out;
  assign STAT_RX_FRAMING_ERR_VALID_19_delay = STAT_RX_FRAMING_ERR_VALID_19_out;
  assign STAT_RX_FRAMING_ERR_VALID_1_delay = STAT_RX_FRAMING_ERR_VALID_1_out;
  assign STAT_RX_FRAMING_ERR_VALID_2_delay = STAT_RX_FRAMING_ERR_VALID_2_out;
  assign STAT_RX_FRAMING_ERR_VALID_3_delay = STAT_RX_FRAMING_ERR_VALID_3_out;
  assign STAT_RX_FRAMING_ERR_VALID_4_delay = STAT_RX_FRAMING_ERR_VALID_4_out;
  assign STAT_RX_FRAMING_ERR_VALID_5_delay = STAT_RX_FRAMING_ERR_VALID_5_out;
  assign STAT_RX_FRAMING_ERR_VALID_6_delay = STAT_RX_FRAMING_ERR_VALID_6_out;
  assign STAT_RX_FRAMING_ERR_VALID_7_delay = STAT_RX_FRAMING_ERR_VALID_7_out;
  assign STAT_RX_FRAMING_ERR_VALID_8_delay = STAT_RX_FRAMING_ERR_VALID_8_out;
  assign STAT_RX_FRAMING_ERR_VALID_9_delay = STAT_RX_FRAMING_ERR_VALID_9_out;
  assign STAT_RX_GOT_SIGNAL_OS_delay = STAT_RX_GOT_SIGNAL_OS_out;
  assign STAT_RX_HI_BER_delay = STAT_RX_HI_BER_out;
  assign STAT_RX_INRANGEERR_delay = STAT_RX_INRANGEERR_out;
  assign STAT_RX_INTERNAL_LOCAL_FAULT_delay = STAT_RX_INTERNAL_LOCAL_FAULT_out;
  assign STAT_RX_JABBER_delay = STAT_RX_JABBER_out;
  assign STAT_RX_LANE0_VLM_BIP7_VALID_delay = STAT_RX_LANE0_VLM_BIP7_VALID_out;
  assign STAT_RX_LANE0_VLM_BIP7_delay = STAT_RX_LANE0_VLM_BIP7_out;
  assign STAT_RX_LOCAL_FAULT_delay = STAT_RX_LOCAL_FAULT_out;
  assign STAT_RX_MF_ERR_delay = STAT_RX_MF_ERR_out;
  assign STAT_RX_MF_LEN_ERR_delay = STAT_RX_MF_LEN_ERR_out;
  assign STAT_RX_MF_REPEAT_ERR_delay = STAT_RX_MF_REPEAT_ERR_out;
  assign STAT_RX_MISALIGNED_delay = STAT_RX_MISALIGNED_out;
  assign STAT_RX_MULTICAST_delay = STAT_RX_MULTICAST_out;
  assign STAT_RX_OVERSIZE_delay = STAT_RX_OVERSIZE_out;
  assign STAT_RX_PACKET_1024_1518_BYTES_delay = STAT_RX_PACKET_1024_1518_BYTES_out;
  assign STAT_RX_PACKET_128_255_BYTES_delay = STAT_RX_PACKET_128_255_BYTES_out;
  assign STAT_RX_PACKET_1519_1522_BYTES_delay = STAT_RX_PACKET_1519_1522_BYTES_out;
  assign STAT_RX_PACKET_1523_1548_BYTES_delay = STAT_RX_PACKET_1523_1548_BYTES_out;
  assign STAT_RX_PACKET_1549_2047_BYTES_delay = STAT_RX_PACKET_1549_2047_BYTES_out;
  assign STAT_RX_PACKET_2048_4095_BYTES_delay = STAT_RX_PACKET_2048_4095_BYTES_out;
  assign STAT_RX_PACKET_256_511_BYTES_delay = STAT_RX_PACKET_256_511_BYTES_out;
  assign STAT_RX_PACKET_4096_8191_BYTES_delay = STAT_RX_PACKET_4096_8191_BYTES_out;
  assign STAT_RX_PACKET_512_1023_BYTES_delay = STAT_RX_PACKET_512_1023_BYTES_out;
  assign STAT_RX_PACKET_64_BYTES_delay = STAT_RX_PACKET_64_BYTES_out;
  assign STAT_RX_PACKET_65_127_BYTES_delay = STAT_RX_PACKET_65_127_BYTES_out;
  assign STAT_RX_PACKET_8192_9215_BYTES_delay = STAT_RX_PACKET_8192_9215_BYTES_out;
  assign STAT_RX_PACKET_BAD_FCS_delay = STAT_RX_PACKET_BAD_FCS_out;
  assign STAT_RX_PACKET_LARGE_delay = STAT_RX_PACKET_LARGE_out;
  assign STAT_RX_PACKET_SMALL_delay = STAT_RX_PACKET_SMALL_out;
  assign STAT_RX_PAUSE_QUANTA0_delay = STAT_RX_PAUSE_QUANTA0_out;
  assign STAT_RX_PAUSE_QUANTA1_delay = STAT_RX_PAUSE_QUANTA1_out;
  assign STAT_RX_PAUSE_QUANTA2_delay = STAT_RX_PAUSE_QUANTA2_out;
  assign STAT_RX_PAUSE_QUANTA3_delay = STAT_RX_PAUSE_QUANTA3_out;
  assign STAT_RX_PAUSE_QUANTA4_delay = STAT_RX_PAUSE_QUANTA4_out;
  assign STAT_RX_PAUSE_QUANTA5_delay = STAT_RX_PAUSE_QUANTA5_out;
  assign STAT_RX_PAUSE_QUANTA6_delay = STAT_RX_PAUSE_QUANTA6_out;
  assign STAT_RX_PAUSE_QUANTA7_delay = STAT_RX_PAUSE_QUANTA7_out;
  assign STAT_RX_PAUSE_QUANTA8_delay = STAT_RX_PAUSE_QUANTA8_out;
  assign STAT_RX_PAUSE_REQ_delay = STAT_RX_PAUSE_REQ_out;
  assign STAT_RX_PAUSE_VALID_delay = STAT_RX_PAUSE_VALID_out;
  assign STAT_RX_PAUSE_delay = STAT_RX_PAUSE_out;
  assign STAT_RX_RECEIVED_LOCAL_FAULT_delay = STAT_RX_RECEIVED_LOCAL_FAULT_out;
  assign STAT_RX_REMOTE_FAULT_delay = STAT_RX_REMOTE_FAULT_out;
  assign STAT_RX_STATUS_delay = STAT_RX_STATUS_out;
  assign STAT_RX_STOMPED_FCS_delay = STAT_RX_STOMPED_FCS_out;
  assign STAT_RX_SYNCED_ERR_delay = STAT_RX_SYNCED_ERR_out;
  assign STAT_RX_SYNCED_delay = STAT_RX_SYNCED_out;
  assign STAT_RX_TEST_PATTERN_MISMATCH_delay = STAT_RX_TEST_PATTERN_MISMATCH_out;
  assign STAT_RX_TOOLONG_delay = STAT_RX_TOOLONG_out;
  assign STAT_RX_TOTAL_BYTES_delay = STAT_RX_TOTAL_BYTES_out;
  assign STAT_RX_TOTAL_GOOD_BYTES_delay = STAT_RX_TOTAL_GOOD_BYTES_out;
  assign STAT_RX_TOTAL_GOOD_PACKETS_delay = STAT_RX_TOTAL_GOOD_PACKETS_out;
  assign STAT_RX_TOTAL_PACKETS_delay = STAT_RX_TOTAL_PACKETS_out;
  assign STAT_RX_TRUNCATED_delay = STAT_RX_TRUNCATED_out;
  assign STAT_RX_UNDERSIZE_delay = STAT_RX_UNDERSIZE_out;
  assign STAT_RX_UNICAST_delay = STAT_RX_UNICAST_out;
  assign STAT_RX_USER_PAUSE_delay = STAT_RX_USER_PAUSE_out;
  assign STAT_RX_VLAN_delay = STAT_RX_VLAN_out;
  assign STAT_RX_VL_DEMUXED_delay = STAT_RX_VL_DEMUXED_out;
  assign STAT_RX_VL_NUMBER_0_delay = STAT_RX_VL_NUMBER_0_out;
  assign STAT_RX_VL_NUMBER_10_delay = STAT_RX_VL_NUMBER_10_out;
  assign STAT_RX_VL_NUMBER_11_delay = STAT_RX_VL_NUMBER_11_out;
  assign STAT_RX_VL_NUMBER_12_delay = STAT_RX_VL_NUMBER_12_out;
  assign STAT_RX_VL_NUMBER_13_delay = STAT_RX_VL_NUMBER_13_out;
  assign STAT_RX_VL_NUMBER_14_delay = STAT_RX_VL_NUMBER_14_out;
  assign STAT_RX_VL_NUMBER_15_delay = STAT_RX_VL_NUMBER_15_out;
  assign STAT_RX_VL_NUMBER_16_delay = STAT_RX_VL_NUMBER_16_out;
  assign STAT_RX_VL_NUMBER_17_delay = STAT_RX_VL_NUMBER_17_out;
  assign STAT_RX_VL_NUMBER_18_delay = STAT_RX_VL_NUMBER_18_out;
  assign STAT_RX_VL_NUMBER_19_delay = STAT_RX_VL_NUMBER_19_out;
  assign STAT_RX_VL_NUMBER_1_delay = STAT_RX_VL_NUMBER_1_out;
  assign STAT_RX_VL_NUMBER_2_delay = STAT_RX_VL_NUMBER_2_out;
  assign STAT_RX_VL_NUMBER_3_delay = STAT_RX_VL_NUMBER_3_out;
  assign STAT_RX_VL_NUMBER_4_delay = STAT_RX_VL_NUMBER_4_out;
  assign STAT_RX_VL_NUMBER_5_delay = STAT_RX_VL_NUMBER_5_out;
  assign STAT_RX_VL_NUMBER_6_delay = STAT_RX_VL_NUMBER_6_out;
  assign STAT_RX_VL_NUMBER_7_delay = STAT_RX_VL_NUMBER_7_out;
  assign STAT_RX_VL_NUMBER_8_delay = STAT_RX_VL_NUMBER_8_out;
  assign STAT_RX_VL_NUMBER_9_delay = STAT_RX_VL_NUMBER_9_out;
  assign STAT_TX_BAD_FCS_delay = STAT_TX_BAD_FCS_out;
  assign STAT_TX_BROADCAST_delay = STAT_TX_BROADCAST_out;
  assign STAT_TX_FRAME_ERROR_delay = STAT_TX_FRAME_ERROR_out;
  assign STAT_TX_LOCAL_FAULT_delay = STAT_TX_LOCAL_FAULT_out;
  assign STAT_TX_MULTICAST_delay = STAT_TX_MULTICAST_out;
  assign STAT_TX_PACKET_1024_1518_BYTES_delay = STAT_TX_PACKET_1024_1518_BYTES_out;
  assign STAT_TX_PACKET_128_255_BYTES_delay = STAT_TX_PACKET_128_255_BYTES_out;
  assign STAT_TX_PACKET_1519_1522_BYTES_delay = STAT_TX_PACKET_1519_1522_BYTES_out;
  assign STAT_TX_PACKET_1523_1548_BYTES_delay = STAT_TX_PACKET_1523_1548_BYTES_out;
  assign STAT_TX_PACKET_1549_2047_BYTES_delay = STAT_TX_PACKET_1549_2047_BYTES_out;
  assign STAT_TX_PACKET_2048_4095_BYTES_delay = STAT_TX_PACKET_2048_4095_BYTES_out;
  assign STAT_TX_PACKET_256_511_BYTES_delay = STAT_TX_PACKET_256_511_BYTES_out;
  assign STAT_TX_PACKET_4096_8191_BYTES_delay = STAT_TX_PACKET_4096_8191_BYTES_out;
  assign STAT_TX_PACKET_512_1023_BYTES_delay = STAT_TX_PACKET_512_1023_BYTES_out;
  assign STAT_TX_PACKET_64_BYTES_delay = STAT_TX_PACKET_64_BYTES_out;
  assign STAT_TX_PACKET_65_127_BYTES_delay = STAT_TX_PACKET_65_127_BYTES_out;
  assign STAT_TX_PACKET_8192_9215_BYTES_delay = STAT_TX_PACKET_8192_9215_BYTES_out;
  assign STAT_TX_PACKET_LARGE_delay = STAT_TX_PACKET_LARGE_out;
  assign STAT_TX_PACKET_SMALL_delay = STAT_TX_PACKET_SMALL_out;
  assign STAT_TX_PAUSE_VALID_delay = STAT_TX_PAUSE_VALID_out;
  assign STAT_TX_PAUSE_delay = STAT_TX_PAUSE_out;
  assign STAT_TX_PTP_FIFO_READ_ERROR_delay = STAT_TX_PTP_FIFO_READ_ERROR_out;
  assign STAT_TX_PTP_FIFO_WRITE_ERROR_delay = STAT_TX_PTP_FIFO_WRITE_ERROR_out;
  assign STAT_TX_TOTAL_BYTES_delay = STAT_TX_TOTAL_BYTES_out;
  assign STAT_TX_TOTAL_GOOD_BYTES_delay = STAT_TX_TOTAL_GOOD_BYTES_out;
  assign STAT_TX_TOTAL_GOOD_PACKETS_delay = STAT_TX_TOTAL_GOOD_PACKETS_out;
  assign STAT_TX_TOTAL_PACKETS_delay = STAT_TX_TOTAL_PACKETS_out;
  assign STAT_TX_UNICAST_delay = STAT_TX_UNICAST_out;
  assign STAT_TX_USER_PAUSE_delay = STAT_TX_USER_PAUSE_out;
  assign STAT_TX_VLAN_delay = STAT_TX_VLAN_out;
  assign TX_OVFOUT_delay = TX_OVFOUT_out;
  assign TX_PTP_PCSLANE_OUT_delay = TX_PTP_PCSLANE_OUT_out;
  assign TX_PTP_TSTAMP_OUT_delay = TX_PTP_TSTAMP_OUT_out;
  assign TX_PTP_TSTAMP_TAG_OUT_delay = TX_PTP_TSTAMP_TAG_OUT_out;
  assign TX_PTP_TSTAMP_VALID_OUT_delay = TX_PTP_TSTAMP_VALID_OUT_out;
  assign TX_RDYOUT_delay = TX_RDYOUT_out;
  assign TX_SERDES_ALT_DATA0_delay = TX_SERDES_ALT_DATA0_out;
  assign TX_SERDES_ALT_DATA1_delay = TX_SERDES_ALT_DATA1_out;
  assign TX_SERDES_ALT_DATA2_delay = TX_SERDES_ALT_DATA2_out;
  assign TX_SERDES_ALT_DATA3_delay = TX_SERDES_ALT_DATA3_out;
  assign TX_SERDES_DATA0_delay = TX_SERDES_DATA0_out;
  assign TX_SERDES_DATA1_delay = TX_SERDES_DATA1_out;
  assign TX_SERDES_DATA2_delay = TX_SERDES_DATA2_out;
  assign TX_SERDES_DATA3_delay = TX_SERDES_DATA3_out;
  assign TX_SERDES_DATA4_delay = TX_SERDES_DATA4_out;
  assign TX_SERDES_DATA5_delay = TX_SERDES_DATA5_out;
  assign TX_SERDES_DATA6_delay = TX_SERDES_DATA6_out;
  assign TX_SERDES_DATA7_delay = TX_SERDES_DATA7_out;
  assign TX_SERDES_DATA8_delay = TX_SERDES_DATA8_out;
  assign TX_SERDES_DATA9_delay = TX_SERDES_DATA9_out;
  assign TX_UNFOUT_delay = TX_UNFOUT_out;

  assign CTL_CAUI4_MODE_in = CTL_CAUI4_MODE_delay;
  assign CTL_RX_CHECK_ETYPE_GCP_in = CTL_RX_CHECK_ETYPE_GCP_delay;
  assign CTL_RX_CHECK_ETYPE_GPP_in = CTL_RX_CHECK_ETYPE_GPP_delay;
  assign CTL_RX_CHECK_ETYPE_PCP_in = CTL_RX_CHECK_ETYPE_PCP_delay;
  assign CTL_RX_CHECK_ETYPE_PPP_in = CTL_RX_CHECK_ETYPE_PPP_delay;
  assign CTL_RX_CHECK_MCAST_GCP_in = CTL_RX_CHECK_MCAST_GCP_delay;
  assign CTL_RX_CHECK_MCAST_GPP_in = CTL_RX_CHECK_MCAST_GPP_delay;
  assign CTL_RX_CHECK_MCAST_PCP_in = CTL_RX_CHECK_MCAST_PCP_delay;
  assign CTL_RX_CHECK_MCAST_PPP_in = CTL_RX_CHECK_MCAST_PPP_delay;
  assign CTL_RX_CHECK_OPCODE_GCP_in = CTL_RX_CHECK_OPCODE_GCP_delay;
  assign CTL_RX_CHECK_OPCODE_GPP_in = CTL_RX_CHECK_OPCODE_GPP_delay;
  assign CTL_RX_CHECK_OPCODE_PCP_in = CTL_RX_CHECK_OPCODE_PCP_delay;
  assign CTL_RX_CHECK_OPCODE_PPP_in = CTL_RX_CHECK_OPCODE_PPP_delay;
  assign CTL_RX_CHECK_SA_GCP_in = CTL_RX_CHECK_SA_GCP_delay;
  assign CTL_RX_CHECK_SA_GPP_in = CTL_RX_CHECK_SA_GPP_delay;
  assign CTL_RX_CHECK_SA_PCP_in = CTL_RX_CHECK_SA_PCP_delay;
  assign CTL_RX_CHECK_SA_PPP_in = CTL_RX_CHECK_SA_PPP_delay;
  assign CTL_RX_CHECK_UCAST_GCP_in = CTL_RX_CHECK_UCAST_GCP_delay;
  assign CTL_RX_CHECK_UCAST_GPP_in = CTL_RX_CHECK_UCAST_GPP_delay;
  assign CTL_RX_CHECK_UCAST_PCP_in = CTL_RX_CHECK_UCAST_PCP_delay;
  assign CTL_RX_CHECK_UCAST_PPP_in = CTL_RX_CHECK_UCAST_PPP_delay;
  assign CTL_RX_ENABLE_GCP_in = CTL_RX_ENABLE_GCP_delay;
  assign CTL_RX_ENABLE_GPP_in = CTL_RX_ENABLE_GPP_delay;
  assign CTL_RX_ENABLE_PCP_in = CTL_RX_ENABLE_PCP_delay;
  assign CTL_RX_ENABLE_PPP_in = CTL_RX_ENABLE_PPP_delay;
  assign CTL_RX_ENABLE_in = CTL_RX_ENABLE_delay;
  assign CTL_RX_FORCE_RESYNC_in = CTL_RX_FORCE_RESYNC_delay;
  assign CTL_RX_PAUSE_ACK_in = CTL_RX_PAUSE_ACK_delay;
  assign CTL_RX_PAUSE_ENABLE_in = CTL_RX_PAUSE_ENABLE_delay;
  assign CTL_RX_SYSTEMTIMERIN_in = CTL_RX_SYSTEMTIMERIN_delay;
  assign CTL_RX_TEST_PATTERN_in = CTL_RX_TEST_PATTERN_delay;
  assign CTL_TX_ENABLE_in = CTL_TX_ENABLE_delay;
  assign CTL_TX_LANE0_VLM_BIP7_OVERRIDE_VALUE_in = CTL_TX_LANE0_VLM_BIP7_OVERRIDE_VALUE_delay;
  assign CTL_TX_LANE0_VLM_BIP7_OVERRIDE_in = CTL_TX_LANE0_VLM_BIP7_OVERRIDE_delay;
  assign CTL_TX_PAUSE_ENABLE_in = CTL_TX_PAUSE_ENABLE_delay;
  assign CTL_TX_PAUSE_QUANTA0_in = CTL_TX_PAUSE_QUANTA0_delay;
  assign CTL_TX_PAUSE_QUANTA1_in = CTL_TX_PAUSE_QUANTA1_delay;
  assign CTL_TX_PAUSE_QUANTA2_in = CTL_TX_PAUSE_QUANTA2_delay;
  assign CTL_TX_PAUSE_QUANTA3_in = CTL_TX_PAUSE_QUANTA3_delay;
  assign CTL_TX_PAUSE_QUANTA4_in = CTL_TX_PAUSE_QUANTA4_delay;
  assign CTL_TX_PAUSE_QUANTA5_in = CTL_TX_PAUSE_QUANTA5_delay;
  assign CTL_TX_PAUSE_QUANTA6_in = CTL_TX_PAUSE_QUANTA6_delay;
  assign CTL_TX_PAUSE_QUANTA7_in = CTL_TX_PAUSE_QUANTA7_delay;
  assign CTL_TX_PAUSE_QUANTA8_in = CTL_TX_PAUSE_QUANTA8_delay;
  assign CTL_TX_PAUSE_REFRESH_TIMER0_in = CTL_TX_PAUSE_REFRESH_TIMER0_delay;
  assign CTL_TX_PAUSE_REFRESH_TIMER1_in = CTL_TX_PAUSE_REFRESH_TIMER1_delay;
  assign CTL_TX_PAUSE_REFRESH_TIMER2_in = CTL_TX_PAUSE_REFRESH_TIMER2_delay;
  assign CTL_TX_PAUSE_REFRESH_TIMER3_in = CTL_TX_PAUSE_REFRESH_TIMER3_delay;
  assign CTL_TX_PAUSE_REFRESH_TIMER4_in = CTL_TX_PAUSE_REFRESH_TIMER4_delay;
  assign CTL_TX_PAUSE_REFRESH_TIMER5_in = CTL_TX_PAUSE_REFRESH_TIMER5_delay;
  assign CTL_TX_PAUSE_REFRESH_TIMER6_in = CTL_TX_PAUSE_REFRESH_TIMER6_delay;
  assign CTL_TX_PAUSE_REFRESH_TIMER7_in = CTL_TX_PAUSE_REFRESH_TIMER7_delay;
  assign CTL_TX_PAUSE_REFRESH_TIMER8_in = CTL_TX_PAUSE_REFRESH_TIMER8_delay;
  assign CTL_TX_PAUSE_REQ_in = CTL_TX_PAUSE_REQ_delay;
  assign CTL_TX_PTP_VLANE_ADJUST_MODE_in = CTL_TX_PTP_VLANE_ADJUST_MODE_delay;
  assign CTL_TX_RESEND_PAUSE_in = CTL_TX_RESEND_PAUSE_delay;
  assign CTL_TX_SEND_IDLE_in = CTL_TX_SEND_IDLE_delay;
  assign CTL_TX_SEND_RFI_in = CTL_TX_SEND_RFI_delay;
  assign CTL_TX_SYSTEMTIMERIN_in = CTL_TX_SYSTEMTIMERIN_delay;
  assign CTL_TX_TEST_PATTERN_in = CTL_TX_TEST_PATTERN_delay;
  assign DRP_ADDR_in = DRP_ADDR_delay;
  assign DRP_CLK_in = DRP_CLK_delay;
  assign DRP_DI_in = DRP_DI_delay;
  assign DRP_EN_in = DRP_EN_delay;
  assign DRP_WE_in = DRP_WE_delay;
  assign RX_CLK_in = RX_CLK_delay;
  assign RX_RESET_in = RX_RESET_delay;
  assign RX_SERDES_ALT_DATA0_in = RX_SERDES_ALT_DATA0_delay;
  assign RX_SERDES_ALT_DATA1_in = RX_SERDES_ALT_DATA1_delay;
  assign RX_SERDES_ALT_DATA2_in = RX_SERDES_ALT_DATA2_delay;
  assign RX_SERDES_ALT_DATA3_in = RX_SERDES_ALT_DATA3_delay;
  assign RX_SERDES_CLK_in = RX_SERDES_CLK_delay;
  assign RX_SERDES_DATA0_in = RX_SERDES_DATA0_delay;
  assign RX_SERDES_DATA1_in = RX_SERDES_DATA1_delay;
  assign RX_SERDES_DATA2_in = RX_SERDES_DATA2_delay;
  assign RX_SERDES_DATA3_in = RX_SERDES_DATA3_delay;
  assign RX_SERDES_DATA4_in = RX_SERDES_DATA4_delay;
  assign RX_SERDES_DATA5_in = RX_SERDES_DATA5_delay;
  assign RX_SERDES_DATA6_in = RX_SERDES_DATA6_delay;
  assign RX_SERDES_DATA7_in = RX_SERDES_DATA7_delay;
  assign RX_SERDES_DATA8_in = RX_SERDES_DATA8_delay;
  assign RX_SERDES_DATA9_in = RX_SERDES_DATA9_delay;
  assign RX_SERDES_RESET_in = RX_SERDES_RESET_delay;
  assign TX_CLK_in = TX_CLK_delay;
  assign TX_DATAIN0_in = TX_DATAIN0_delay;
  assign TX_DATAIN1_in = TX_DATAIN1_delay;
  assign TX_DATAIN2_in = TX_DATAIN2_delay;
  assign TX_DATAIN3_in = TX_DATAIN3_delay;
  assign TX_ENAIN0_in = TX_ENAIN0_delay;
  assign TX_ENAIN1_in = TX_ENAIN1_delay;
  assign TX_ENAIN2_in = TX_ENAIN2_delay;
  assign TX_ENAIN3_in = TX_ENAIN3_delay;
  assign TX_EOPIN0_in = TX_EOPIN0_delay;
  assign TX_EOPIN1_in = TX_EOPIN1_delay;
  assign TX_EOPIN2_in = TX_EOPIN2_delay;
  assign TX_EOPIN3_in = TX_EOPIN3_delay;
  assign TX_ERRIN0_in = TX_ERRIN0_delay;
  assign TX_ERRIN1_in = TX_ERRIN1_delay;
  assign TX_ERRIN2_in = TX_ERRIN2_delay;
  assign TX_ERRIN3_in = TX_ERRIN3_delay;
  assign TX_MTYIN0_in = TX_MTYIN0_delay;
  assign TX_MTYIN1_in = TX_MTYIN1_delay;
  assign TX_MTYIN2_in = TX_MTYIN2_delay;
  assign TX_MTYIN3_in = TX_MTYIN3_delay;
  assign TX_PTP_1588OP_IN_in = TX_PTP_1588OP_IN_delay;
  assign TX_PTP_CHKSUM_OFFSET_IN_in = TX_PTP_CHKSUM_OFFSET_IN_delay;
  assign TX_PTP_RXTSTAMP_IN_in = TX_PTP_RXTSTAMP_IN_delay;
  assign TX_PTP_TAG_FIELD_IN_in = TX_PTP_TAG_FIELD_IN_delay;
  assign TX_PTP_TSTAMP_OFFSET_IN_in = TX_PTP_TSTAMP_OFFSET_IN_delay;
  assign TX_PTP_UPD_CHKSUM_IN_in = TX_PTP_UPD_CHKSUM_IN_delay;
  assign TX_RESET_in = TX_RESET_delay;
  assign TX_SOPIN0_in = TX_SOPIN0_delay;
  assign TX_SOPIN1_in = TX_SOPIN1_delay;
  assign TX_SOPIN2_in = TX_SOPIN2_delay;
  assign TX_SOPIN3_in = TX_SOPIN3_delay;

  initial begin
    #1;
    trig_attr = ~trig_attr;
  end
  
  always @ (trig_attr) begin
    #1;
    if ((attr_test == 1'b1) ||
        ((CTL_PTP_TRANSPCLK_MODE_REG != "FALSE") &&
         (CTL_PTP_TRANSPCLK_MODE_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-101] CTL_PTP_TRANSPCLK_MODE attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CTL_PTP_TRANSPCLK_MODE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((CTL_RX_CHECK_ACK_REG != "TRUE") &&
         (CTL_RX_CHECK_ACK_REG != "FALSE"))) begin
      $display("Error: [Unisim %s-102] CTL_RX_CHECK_ACK attribute is set to %s.  Legal values for this attribute are TRUE or FALSE. Instance: %m", MODULE_NAME, CTL_RX_CHECK_ACK_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((CTL_RX_CHECK_PREAMBLE_REG != "FALSE") &&
         (CTL_RX_CHECK_PREAMBLE_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-103] CTL_RX_CHECK_PREAMBLE attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CTL_RX_CHECK_PREAMBLE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((CTL_RX_CHECK_SFD_REG != "FALSE") &&
         (CTL_RX_CHECK_SFD_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-104] CTL_RX_CHECK_SFD attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CTL_RX_CHECK_SFD_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((CTL_RX_DELETE_FCS_REG != "TRUE") &&
         (CTL_RX_DELETE_FCS_REG != "FALSE"))) begin
      $display("Error: [Unisim %s-105] CTL_RX_DELETE_FCS attribute is set to %s.  Legal values for this attribute are TRUE or FALSE. Instance: %m", MODULE_NAME, CTL_RX_DELETE_FCS_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((CTL_RX_FORWARD_CONTROL_REG != "FALSE") &&
         (CTL_RX_FORWARD_CONTROL_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-110] CTL_RX_FORWARD_CONTROL attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CTL_RX_FORWARD_CONTROL_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((CTL_RX_IGNORE_FCS_REG != "FALSE") &&
         (CTL_RX_IGNORE_FCS_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-111] CTL_RX_IGNORE_FCS attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CTL_RX_IGNORE_FCS_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((CTL_RX_MAX_PACKET_LEN_REG < 15'h0000) || (CTL_RX_MAX_PACKET_LEN_REG > 15'h3FFF))) begin
        $display("Error: [Unisim %s-112] CTL_RX_MAX_PACKET_LEN attribute is set to %h.  Legal values for this attribute are 15'h0000 to 15'h3FFF. Instance: %m", MODULE_NAME, CTL_RX_MAX_PACKET_LEN_REG);
        attr_err = 1'b1;
      end
    
    if ((attr_test == 1'b1) ||
        ((CTL_RX_PROCESS_LFI_REG != "FALSE") &&
         (CTL_RX_PROCESS_LFI_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-123] CTL_RX_PROCESS_LFI attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CTL_RX_PROCESS_LFI_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((CTL_TEST_MODE_PIN_CHAR_REG != "FALSE") &&
         (CTL_TEST_MODE_PIN_CHAR_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-145] CTL_TEST_MODE_PIN_CHAR attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CTL_TEST_MODE_PIN_CHAR_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((CTL_TX_FCS_INS_ENABLE_REG != "TRUE") &&
         (CTL_TX_FCS_INS_ENABLE_REG != "FALSE"))) begin
      $display("Error: [Unisim %s-150] CTL_TX_FCS_INS_ENABLE attribute is set to %s.  Legal values for this attribute are TRUE or FALSE. Instance: %m", MODULE_NAME, CTL_TX_FCS_INS_ENABLE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((CTL_TX_IGNORE_FCS_REG != "FALSE") &&
         (CTL_TX_IGNORE_FCS_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-151] CTL_TX_IGNORE_FCS attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CTL_TX_IGNORE_FCS_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((CTL_TX_PTP_1STEP_ENABLE_REG != "FALSE") &&
         (CTL_TX_PTP_1STEP_ENABLE_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-154] CTL_TX_PTP_1STEP_ENABLE attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CTL_TX_PTP_1STEP_ENABLE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((SIM_VERSION_REG != "2.0") &&
         (SIM_VERSION_REG != "1.0"))) begin
      $display("Error: [Unisim %s-179] SIM_VERSION attribute is set to %s.  Legal values for this attribute are 2.0 or 1.0. Instance: %m", MODULE_NAME, SIM_VERSION_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((TEST_MODE_PIN_CHAR_REG != "FALSE") &&
         (TEST_MODE_PIN_CHAR_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-180] TEST_MODE_PIN_CHAR attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, TEST_MODE_PIN_CHAR_REG);
      attr_err = 1'b1;
    end
    
    if (attr_err == 1'b1) #1 $finish;
  end


  assign SCAN_EN_in = 1'b0; //manual tie off
  assign SCAN_IN_CMAC_in = 182'b11111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111; // tie off
  assign SCAN_IN_DRPCTRL_in = 13'b1111111111111; // tie off
  assign TEST_MODE_in = 1'b0; //manual tie off
  assign TEST_RESET_in = 1'b1; // tie off

generate
if (SIM_VERSION == "2.0" ) begin : generate_block1
  SIP_CMAC_ES2 SIP_CMAC_INST (
    .CTL_PTP_TRANSPCLK_MODE (CTL_PTP_TRANSPCLK_MODE_REG),
    .CTL_RX_CHECK_ACK (CTL_RX_CHECK_ACK_REG),
    .CTL_RX_CHECK_PREAMBLE (CTL_RX_CHECK_PREAMBLE_REG),
    .CTL_RX_CHECK_SFD (CTL_RX_CHECK_SFD_REG),
    .CTL_RX_DELETE_FCS (CTL_RX_DELETE_FCS_REG),
    .CTL_RX_ETYPE_GCP (CTL_RX_ETYPE_GCP_REG),
    .CTL_RX_ETYPE_GPP (CTL_RX_ETYPE_GPP_REG),
    .CTL_RX_ETYPE_PCP (CTL_RX_ETYPE_PCP_REG),
    .CTL_RX_ETYPE_PPP (CTL_RX_ETYPE_PPP_REG),
    .CTL_RX_FORWARD_CONTROL (CTL_RX_FORWARD_CONTROL_REG),
    .CTL_RX_IGNORE_FCS (CTL_RX_IGNORE_FCS_REG),
    .CTL_RX_MAX_PACKET_LEN (CTL_RX_MAX_PACKET_LEN_REG),
    .CTL_RX_MIN_PACKET_LEN (CTL_RX_MIN_PACKET_LEN_REG),
    .CTL_RX_OPCODE_GPP (CTL_RX_OPCODE_GPP_REG),
    .CTL_RX_OPCODE_MAX_GCP (CTL_RX_OPCODE_MAX_GCP_REG),
    .CTL_RX_OPCODE_MAX_PCP (CTL_RX_OPCODE_MAX_PCP_REG),
    .CTL_RX_OPCODE_MIN_GCP (CTL_RX_OPCODE_MIN_GCP_REG),
    .CTL_RX_OPCODE_MIN_PCP (CTL_RX_OPCODE_MIN_PCP_REG),
    .CTL_RX_OPCODE_PPP (CTL_RX_OPCODE_PPP_REG),
    .CTL_RX_PAUSE_DA_MCAST (CTL_RX_PAUSE_DA_MCAST_REG),
    .CTL_RX_PAUSE_DA_UCAST (CTL_RX_PAUSE_DA_UCAST_REG),
    .CTL_RX_PAUSE_SA (CTL_RX_PAUSE_SA_REG),
    .CTL_RX_PROCESS_LFI (CTL_RX_PROCESS_LFI_REG),
    .CTL_RX_VL_LENGTH_MINUS1 (CTL_RX_VL_LENGTH_MINUS1_REG),
    .CTL_RX_VL_MARKER_ID0 (CTL_RX_VL_MARKER_ID0_REG),
    .CTL_RX_VL_MARKER_ID1 (CTL_RX_VL_MARKER_ID1_REG),
    .CTL_RX_VL_MARKER_ID10 (CTL_RX_VL_MARKER_ID10_REG),
    .CTL_RX_VL_MARKER_ID11 (CTL_RX_VL_MARKER_ID11_REG),
    .CTL_RX_VL_MARKER_ID12 (CTL_RX_VL_MARKER_ID12_REG),
    .CTL_RX_VL_MARKER_ID13 (CTL_RX_VL_MARKER_ID13_REG),
    .CTL_RX_VL_MARKER_ID14 (CTL_RX_VL_MARKER_ID14_REG),
    .CTL_RX_VL_MARKER_ID15 (CTL_RX_VL_MARKER_ID15_REG),
    .CTL_RX_VL_MARKER_ID16 (CTL_RX_VL_MARKER_ID16_REG),
    .CTL_RX_VL_MARKER_ID17 (CTL_RX_VL_MARKER_ID17_REG),
    .CTL_RX_VL_MARKER_ID18 (CTL_RX_VL_MARKER_ID18_REG),
    .CTL_RX_VL_MARKER_ID19 (CTL_RX_VL_MARKER_ID19_REG),
    .CTL_RX_VL_MARKER_ID2 (CTL_RX_VL_MARKER_ID2_REG),
    .CTL_RX_VL_MARKER_ID3 (CTL_RX_VL_MARKER_ID3_REG),
    .CTL_RX_VL_MARKER_ID4 (CTL_RX_VL_MARKER_ID4_REG),
    .CTL_RX_VL_MARKER_ID5 (CTL_RX_VL_MARKER_ID5_REG),
    .CTL_RX_VL_MARKER_ID6 (CTL_RX_VL_MARKER_ID6_REG),
    .CTL_RX_VL_MARKER_ID7 (CTL_RX_VL_MARKER_ID7_REG),
    .CTL_RX_VL_MARKER_ID8 (CTL_RX_VL_MARKER_ID8_REG),
    .CTL_RX_VL_MARKER_ID9 (CTL_RX_VL_MARKER_ID9_REG),
    .CTL_TEST_MODE_PIN_CHAR (CTL_TEST_MODE_PIN_CHAR_REG),
    .CTL_TX_DA_GPP (CTL_TX_DA_GPP_REG),
    .CTL_TX_DA_PPP (CTL_TX_DA_PPP_REG),
    .CTL_TX_ETHERTYPE_GPP (CTL_TX_ETHERTYPE_GPP_REG),
    .CTL_TX_ETHERTYPE_PPP (CTL_TX_ETHERTYPE_PPP_REG),
    .CTL_TX_FCS_INS_ENABLE (CTL_TX_FCS_INS_ENABLE_REG),
    .CTL_TX_IGNORE_FCS (CTL_TX_IGNORE_FCS_REG),
    .CTL_TX_OPCODE_GPP (CTL_TX_OPCODE_GPP_REG),
    .CTL_TX_OPCODE_PPP (CTL_TX_OPCODE_PPP_REG),
    .CTL_TX_PTP_1STEP_ENABLE (CTL_TX_PTP_1STEP_ENABLE_REG),
    .CTL_TX_PTP_LATENCY_ADJUST (CTL_TX_PTP_LATENCY_ADJUST_REG),
    .CTL_TX_SA_GPP (CTL_TX_SA_GPP_REG),
    .CTL_TX_SA_PPP (CTL_TX_SA_PPP_REG),
    .CTL_TX_VL_LENGTH_MINUS1 (CTL_TX_VL_LENGTH_MINUS1_REG),
    .CTL_TX_VL_MARKER_ID0 (CTL_TX_VL_MARKER_ID0_REG),
    .CTL_TX_VL_MARKER_ID1 (CTL_TX_VL_MARKER_ID1_REG),
    .CTL_TX_VL_MARKER_ID10 (CTL_TX_VL_MARKER_ID10_REG),
    .CTL_TX_VL_MARKER_ID11 (CTL_TX_VL_MARKER_ID11_REG),
    .CTL_TX_VL_MARKER_ID12 (CTL_TX_VL_MARKER_ID12_REG),
    .CTL_TX_VL_MARKER_ID13 (CTL_TX_VL_MARKER_ID13_REG),
    .CTL_TX_VL_MARKER_ID14 (CTL_TX_VL_MARKER_ID14_REG),
    .CTL_TX_VL_MARKER_ID15 (CTL_TX_VL_MARKER_ID15_REG),
    .CTL_TX_VL_MARKER_ID16 (CTL_TX_VL_MARKER_ID16_REG),
    .CTL_TX_VL_MARKER_ID17 (CTL_TX_VL_MARKER_ID17_REG),
    .CTL_TX_VL_MARKER_ID18 (CTL_TX_VL_MARKER_ID18_REG),
    .CTL_TX_VL_MARKER_ID19 (CTL_TX_VL_MARKER_ID19_REG),
    .CTL_TX_VL_MARKER_ID2 (CTL_TX_VL_MARKER_ID2_REG),
    .CTL_TX_VL_MARKER_ID3 (CTL_TX_VL_MARKER_ID3_REG),
    .CTL_TX_VL_MARKER_ID4 (CTL_TX_VL_MARKER_ID4_REG),
    .CTL_TX_VL_MARKER_ID5 (CTL_TX_VL_MARKER_ID5_REG),
    .CTL_TX_VL_MARKER_ID6 (CTL_TX_VL_MARKER_ID6_REG),
    .CTL_TX_VL_MARKER_ID7 (CTL_TX_VL_MARKER_ID7_REG),
    .CTL_TX_VL_MARKER_ID8 (CTL_TX_VL_MARKER_ID8_REG),
    .CTL_TX_VL_MARKER_ID9 (CTL_TX_VL_MARKER_ID9_REG),
    .TEST_MODE_PIN_CHAR (TEST_MODE_PIN_CHAR_REG),
    .DRP_DO (DRP_DO_out),
    .DRP_RDY (DRP_RDY_out),
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
    .RX_LANE_ALIGNER_FILL_0 (RX_LANE_ALIGNER_FILL_0_out),
    .RX_LANE_ALIGNER_FILL_1 (RX_LANE_ALIGNER_FILL_1_out),
    .RX_LANE_ALIGNER_FILL_10 (RX_LANE_ALIGNER_FILL_10_out),
    .RX_LANE_ALIGNER_FILL_11 (RX_LANE_ALIGNER_FILL_11_out),
    .RX_LANE_ALIGNER_FILL_12 (RX_LANE_ALIGNER_FILL_12_out),
    .RX_LANE_ALIGNER_FILL_13 (RX_LANE_ALIGNER_FILL_13_out),
    .RX_LANE_ALIGNER_FILL_14 (RX_LANE_ALIGNER_FILL_14_out),
    .RX_LANE_ALIGNER_FILL_15 (RX_LANE_ALIGNER_FILL_15_out),
    .RX_LANE_ALIGNER_FILL_16 (RX_LANE_ALIGNER_FILL_16_out),
    .RX_LANE_ALIGNER_FILL_17 (RX_LANE_ALIGNER_FILL_17_out),
    .RX_LANE_ALIGNER_FILL_18 (RX_LANE_ALIGNER_FILL_18_out),
    .RX_LANE_ALIGNER_FILL_19 (RX_LANE_ALIGNER_FILL_19_out),
    .RX_LANE_ALIGNER_FILL_2 (RX_LANE_ALIGNER_FILL_2_out),
    .RX_LANE_ALIGNER_FILL_3 (RX_LANE_ALIGNER_FILL_3_out),
    .RX_LANE_ALIGNER_FILL_4 (RX_LANE_ALIGNER_FILL_4_out),
    .RX_LANE_ALIGNER_FILL_5 (RX_LANE_ALIGNER_FILL_5_out),
    .RX_LANE_ALIGNER_FILL_6 (RX_LANE_ALIGNER_FILL_6_out),
    .RX_LANE_ALIGNER_FILL_7 (RX_LANE_ALIGNER_FILL_7_out),
    .RX_LANE_ALIGNER_FILL_8 (RX_LANE_ALIGNER_FILL_8_out),
    .RX_LANE_ALIGNER_FILL_9 (RX_LANE_ALIGNER_FILL_9_out),
    .RX_MTYOUT0 (RX_MTYOUT0_out),
    .RX_MTYOUT1 (RX_MTYOUT1_out),
    .RX_MTYOUT2 (RX_MTYOUT2_out),
    .RX_MTYOUT3 (RX_MTYOUT3_out),
    .RX_PTP_PCSLANE_OUT (RX_PTP_PCSLANE_OUT_out),
    .RX_PTP_TSTAMP_OUT (RX_PTP_TSTAMP_OUT_out),
    .RX_SOPOUT0 (RX_SOPOUT0_out),
    .RX_SOPOUT1 (RX_SOPOUT1_out),
    .RX_SOPOUT2 (RX_SOPOUT2_out),
    .RX_SOPOUT3 (RX_SOPOUT3_out),
    .SCAN_OUT_CMAC (SCAN_OUT_CMAC_out),
    .SCAN_OUT_DRPCTRL (SCAN_OUT_DRPCTRL_out),
    .STAT_RX_ALIGNED (STAT_RX_ALIGNED_out),
    .STAT_RX_ALIGNED_ERR (STAT_RX_ALIGNED_ERR_out),
    .STAT_RX_BAD_CODE (STAT_RX_BAD_CODE_out),
    .STAT_RX_BAD_FCS (STAT_RX_BAD_FCS_out),
    .STAT_RX_BAD_PREAMBLE (STAT_RX_BAD_PREAMBLE_out),
    .STAT_RX_BAD_SFD (STAT_RX_BAD_SFD_out),
    .STAT_RX_BIP_ERR_0 (STAT_RX_BIP_ERR_0_out),
    .STAT_RX_BIP_ERR_1 (STAT_RX_BIP_ERR_1_out),
    .STAT_RX_BIP_ERR_10 (STAT_RX_BIP_ERR_10_out),
    .STAT_RX_BIP_ERR_11 (STAT_RX_BIP_ERR_11_out),
    .STAT_RX_BIP_ERR_12 (STAT_RX_BIP_ERR_12_out),
    .STAT_RX_BIP_ERR_13 (STAT_RX_BIP_ERR_13_out),
    .STAT_RX_BIP_ERR_14 (STAT_RX_BIP_ERR_14_out),
    .STAT_RX_BIP_ERR_15 (STAT_RX_BIP_ERR_15_out),
    .STAT_RX_BIP_ERR_16 (STAT_RX_BIP_ERR_16_out),
    .STAT_RX_BIP_ERR_17 (STAT_RX_BIP_ERR_17_out),
    .STAT_RX_BIP_ERR_18 (STAT_RX_BIP_ERR_18_out),
    .STAT_RX_BIP_ERR_19 (STAT_RX_BIP_ERR_19_out),
    .STAT_RX_BIP_ERR_2 (STAT_RX_BIP_ERR_2_out),
    .STAT_RX_BIP_ERR_3 (STAT_RX_BIP_ERR_3_out),
    .STAT_RX_BIP_ERR_4 (STAT_RX_BIP_ERR_4_out),
    .STAT_RX_BIP_ERR_5 (STAT_RX_BIP_ERR_5_out),
    .STAT_RX_BIP_ERR_6 (STAT_RX_BIP_ERR_6_out),
    .STAT_RX_BIP_ERR_7 (STAT_RX_BIP_ERR_7_out),
    .STAT_RX_BIP_ERR_8 (STAT_RX_BIP_ERR_8_out),
    .STAT_RX_BIP_ERR_9 (STAT_RX_BIP_ERR_9_out),
    .STAT_RX_BLOCK_LOCK (STAT_RX_BLOCK_LOCK_out),
    .STAT_RX_BROADCAST (STAT_RX_BROADCAST_out),
    .STAT_RX_FRAGMENT (STAT_RX_FRAGMENT_out),
    .STAT_RX_FRAMING_ERR_0 (STAT_RX_FRAMING_ERR_0_out),
    .STAT_RX_FRAMING_ERR_1 (STAT_RX_FRAMING_ERR_1_out),
    .STAT_RX_FRAMING_ERR_10 (STAT_RX_FRAMING_ERR_10_out),
    .STAT_RX_FRAMING_ERR_11 (STAT_RX_FRAMING_ERR_11_out),
    .STAT_RX_FRAMING_ERR_12 (STAT_RX_FRAMING_ERR_12_out),
    .STAT_RX_FRAMING_ERR_13 (STAT_RX_FRAMING_ERR_13_out),
    .STAT_RX_FRAMING_ERR_14 (STAT_RX_FRAMING_ERR_14_out),
    .STAT_RX_FRAMING_ERR_15 (STAT_RX_FRAMING_ERR_15_out),
    .STAT_RX_FRAMING_ERR_16 (STAT_RX_FRAMING_ERR_16_out),
    .STAT_RX_FRAMING_ERR_17 (STAT_RX_FRAMING_ERR_17_out),
    .STAT_RX_FRAMING_ERR_18 (STAT_RX_FRAMING_ERR_18_out),
    .STAT_RX_FRAMING_ERR_19 (STAT_RX_FRAMING_ERR_19_out),
    .STAT_RX_FRAMING_ERR_2 (STAT_RX_FRAMING_ERR_2_out),
    .STAT_RX_FRAMING_ERR_3 (STAT_RX_FRAMING_ERR_3_out),
    .STAT_RX_FRAMING_ERR_4 (STAT_RX_FRAMING_ERR_4_out),
    .STAT_RX_FRAMING_ERR_5 (STAT_RX_FRAMING_ERR_5_out),
    .STAT_RX_FRAMING_ERR_6 (STAT_RX_FRAMING_ERR_6_out),
    .STAT_RX_FRAMING_ERR_7 (STAT_RX_FRAMING_ERR_7_out),
    .STAT_RX_FRAMING_ERR_8 (STAT_RX_FRAMING_ERR_8_out),
    .STAT_RX_FRAMING_ERR_9 (STAT_RX_FRAMING_ERR_9_out),
    .STAT_RX_FRAMING_ERR_VALID_0 (STAT_RX_FRAMING_ERR_VALID_0_out),
    .STAT_RX_FRAMING_ERR_VALID_1 (STAT_RX_FRAMING_ERR_VALID_1_out),
    .STAT_RX_FRAMING_ERR_VALID_10 (STAT_RX_FRAMING_ERR_VALID_10_out),
    .STAT_RX_FRAMING_ERR_VALID_11 (STAT_RX_FRAMING_ERR_VALID_11_out),
    .STAT_RX_FRAMING_ERR_VALID_12 (STAT_RX_FRAMING_ERR_VALID_12_out),
    .STAT_RX_FRAMING_ERR_VALID_13 (STAT_RX_FRAMING_ERR_VALID_13_out),
    .STAT_RX_FRAMING_ERR_VALID_14 (STAT_RX_FRAMING_ERR_VALID_14_out),
    .STAT_RX_FRAMING_ERR_VALID_15 (STAT_RX_FRAMING_ERR_VALID_15_out),
    .STAT_RX_FRAMING_ERR_VALID_16 (STAT_RX_FRAMING_ERR_VALID_16_out),
    .STAT_RX_FRAMING_ERR_VALID_17 (STAT_RX_FRAMING_ERR_VALID_17_out),
    .STAT_RX_FRAMING_ERR_VALID_18 (STAT_RX_FRAMING_ERR_VALID_18_out),
    .STAT_RX_FRAMING_ERR_VALID_19 (STAT_RX_FRAMING_ERR_VALID_19_out),
    .STAT_RX_FRAMING_ERR_VALID_2 (STAT_RX_FRAMING_ERR_VALID_2_out),
    .STAT_RX_FRAMING_ERR_VALID_3 (STAT_RX_FRAMING_ERR_VALID_3_out),
    .STAT_RX_FRAMING_ERR_VALID_4 (STAT_RX_FRAMING_ERR_VALID_4_out),
    .STAT_RX_FRAMING_ERR_VALID_5 (STAT_RX_FRAMING_ERR_VALID_5_out),
    .STAT_RX_FRAMING_ERR_VALID_6 (STAT_RX_FRAMING_ERR_VALID_6_out),
    .STAT_RX_FRAMING_ERR_VALID_7 (STAT_RX_FRAMING_ERR_VALID_7_out),
    .STAT_RX_FRAMING_ERR_VALID_8 (STAT_RX_FRAMING_ERR_VALID_8_out),
    .STAT_RX_FRAMING_ERR_VALID_9 (STAT_RX_FRAMING_ERR_VALID_9_out),
    .STAT_RX_GOT_SIGNAL_OS (STAT_RX_GOT_SIGNAL_OS_out),
    .STAT_RX_HI_BER (STAT_RX_HI_BER_out),
    .STAT_RX_INRANGEERR (STAT_RX_INRANGEERR_out),
    .STAT_RX_INTERNAL_LOCAL_FAULT (STAT_RX_INTERNAL_LOCAL_FAULT_out),
    .STAT_RX_JABBER (STAT_RX_JABBER_out),
    .STAT_RX_LANE0_VLM_BIP7 (STAT_RX_LANE0_VLM_BIP7_out),
    .STAT_RX_LANE0_VLM_BIP7_VALID (STAT_RX_LANE0_VLM_BIP7_VALID_out),
    .STAT_RX_LOCAL_FAULT (STAT_RX_LOCAL_FAULT_out),
    .STAT_RX_MF_ERR (STAT_RX_MF_ERR_out),
    .STAT_RX_MF_LEN_ERR (STAT_RX_MF_LEN_ERR_out),
    .STAT_RX_MF_REPEAT_ERR (STAT_RX_MF_REPEAT_ERR_out),
    .STAT_RX_MISALIGNED (STAT_RX_MISALIGNED_out),
    .STAT_RX_MULTICAST (STAT_RX_MULTICAST_out),
    .STAT_RX_OVERSIZE (STAT_RX_OVERSIZE_out),
    .STAT_RX_PACKET_1024_1518_BYTES (STAT_RX_PACKET_1024_1518_BYTES_out),
    .STAT_RX_PACKET_128_255_BYTES (STAT_RX_PACKET_128_255_BYTES_out),
    .STAT_RX_PACKET_1519_1522_BYTES (STAT_RX_PACKET_1519_1522_BYTES_out),
    .STAT_RX_PACKET_1523_1548_BYTES (STAT_RX_PACKET_1523_1548_BYTES_out),
    .STAT_RX_PACKET_1549_2047_BYTES (STAT_RX_PACKET_1549_2047_BYTES_out),
    .STAT_RX_PACKET_2048_4095_BYTES (STAT_RX_PACKET_2048_4095_BYTES_out),
    .STAT_RX_PACKET_256_511_BYTES (STAT_RX_PACKET_256_511_BYTES_out),
    .STAT_RX_PACKET_4096_8191_BYTES (STAT_RX_PACKET_4096_8191_BYTES_out),
    .STAT_RX_PACKET_512_1023_BYTES (STAT_RX_PACKET_512_1023_BYTES_out),
    .STAT_RX_PACKET_64_BYTES (STAT_RX_PACKET_64_BYTES_out),
    .STAT_RX_PACKET_65_127_BYTES (STAT_RX_PACKET_65_127_BYTES_out),
    .STAT_RX_PACKET_8192_9215_BYTES (STAT_RX_PACKET_8192_9215_BYTES_out),
    .STAT_RX_PACKET_BAD_FCS (STAT_RX_PACKET_BAD_FCS_out),
    .STAT_RX_PACKET_LARGE (STAT_RX_PACKET_LARGE_out),
    .STAT_RX_PACKET_SMALL (STAT_RX_PACKET_SMALL_out),
    .STAT_RX_PAUSE (STAT_RX_PAUSE_out),
    .STAT_RX_PAUSE_QUANTA0 (STAT_RX_PAUSE_QUANTA0_out),
    .STAT_RX_PAUSE_QUANTA1 (STAT_RX_PAUSE_QUANTA1_out),
    .STAT_RX_PAUSE_QUANTA2 (STAT_RX_PAUSE_QUANTA2_out),
    .STAT_RX_PAUSE_QUANTA3 (STAT_RX_PAUSE_QUANTA3_out),
    .STAT_RX_PAUSE_QUANTA4 (STAT_RX_PAUSE_QUANTA4_out),
    .STAT_RX_PAUSE_QUANTA5 (STAT_RX_PAUSE_QUANTA5_out),
    .STAT_RX_PAUSE_QUANTA6 (STAT_RX_PAUSE_QUANTA6_out),
    .STAT_RX_PAUSE_QUANTA7 (STAT_RX_PAUSE_QUANTA7_out),
    .STAT_RX_PAUSE_QUANTA8 (STAT_RX_PAUSE_QUANTA8_out),
    .STAT_RX_PAUSE_REQ (STAT_RX_PAUSE_REQ_out),
    .STAT_RX_PAUSE_VALID (STAT_RX_PAUSE_VALID_out),
    .STAT_RX_RECEIVED_LOCAL_FAULT (STAT_RX_RECEIVED_LOCAL_FAULT_out),
    .STAT_RX_REMOTE_FAULT (STAT_RX_REMOTE_FAULT_out),
    .STAT_RX_STATUS (STAT_RX_STATUS_out),
    .STAT_RX_STOMPED_FCS (STAT_RX_STOMPED_FCS_out),
    .STAT_RX_SYNCED (STAT_RX_SYNCED_out),
    .STAT_RX_SYNCED_ERR (STAT_RX_SYNCED_ERR_out),
    .STAT_RX_TEST_PATTERN_MISMATCH (STAT_RX_TEST_PATTERN_MISMATCH_out),
    .STAT_RX_TOOLONG (STAT_RX_TOOLONG_out),
    .STAT_RX_TOTAL_BYTES (STAT_RX_TOTAL_BYTES_out),
    .STAT_RX_TOTAL_GOOD_BYTES (STAT_RX_TOTAL_GOOD_BYTES_out),
    .STAT_RX_TOTAL_GOOD_PACKETS (STAT_RX_TOTAL_GOOD_PACKETS_out),
    .STAT_RX_TOTAL_PACKETS (STAT_RX_TOTAL_PACKETS_out),
    .STAT_RX_TRUNCATED (STAT_RX_TRUNCATED_out),
    .STAT_RX_UNDERSIZE (STAT_RX_UNDERSIZE_out),
    .STAT_RX_UNICAST (STAT_RX_UNICAST_out),
    .STAT_RX_USER_PAUSE (STAT_RX_USER_PAUSE_out),
    .STAT_RX_VLAN (STAT_RX_VLAN_out),
    .STAT_RX_VL_DEMUXED (STAT_RX_VL_DEMUXED_out),
    .STAT_RX_VL_NUMBER_0 (STAT_RX_VL_NUMBER_0_out),
    .STAT_RX_VL_NUMBER_1 (STAT_RX_VL_NUMBER_1_out),
    .STAT_RX_VL_NUMBER_10 (STAT_RX_VL_NUMBER_10_out),
    .STAT_RX_VL_NUMBER_11 (STAT_RX_VL_NUMBER_11_out),
    .STAT_RX_VL_NUMBER_12 (STAT_RX_VL_NUMBER_12_out),
    .STAT_RX_VL_NUMBER_13 (STAT_RX_VL_NUMBER_13_out),
    .STAT_RX_VL_NUMBER_14 (STAT_RX_VL_NUMBER_14_out),
    .STAT_RX_VL_NUMBER_15 (STAT_RX_VL_NUMBER_15_out),
    .STAT_RX_VL_NUMBER_16 (STAT_RX_VL_NUMBER_16_out),
    .STAT_RX_VL_NUMBER_17 (STAT_RX_VL_NUMBER_17_out),
    .STAT_RX_VL_NUMBER_18 (STAT_RX_VL_NUMBER_18_out),
    .STAT_RX_VL_NUMBER_19 (STAT_RX_VL_NUMBER_19_out),
    .STAT_RX_VL_NUMBER_2 (STAT_RX_VL_NUMBER_2_out),
    .STAT_RX_VL_NUMBER_3 (STAT_RX_VL_NUMBER_3_out),
    .STAT_RX_VL_NUMBER_4 (STAT_RX_VL_NUMBER_4_out),
    .STAT_RX_VL_NUMBER_5 (STAT_RX_VL_NUMBER_5_out),
    .STAT_RX_VL_NUMBER_6 (STAT_RX_VL_NUMBER_6_out),
    .STAT_RX_VL_NUMBER_7 (STAT_RX_VL_NUMBER_7_out),
    .STAT_RX_VL_NUMBER_8 (STAT_RX_VL_NUMBER_8_out),
    .STAT_RX_VL_NUMBER_9 (STAT_RX_VL_NUMBER_9_out),
    .STAT_TX_BAD_FCS (STAT_TX_BAD_FCS_out),
    .STAT_TX_BROADCAST (STAT_TX_BROADCAST_out),
    .STAT_TX_FRAME_ERROR (STAT_TX_FRAME_ERROR_out),
    .STAT_TX_LOCAL_FAULT (STAT_TX_LOCAL_FAULT_out),
    .STAT_TX_MULTICAST (STAT_TX_MULTICAST_out),
    .STAT_TX_PACKET_1024_1518_BYTES (STAT_TX_PACKET_1024_1518_BYTES_out),
    .STAT_TX_PACKET_128_255_BYTES (STAT_TX_PACKET_128_255_BYTES_out),
    .STAT_TX_PACKET_1519_1522_BYTES (STAT_TX_PACKET_1519_1522_BYTES_out),
    .STAT_TX_PACKET_1523_1548_BYTES (STAT_TX_PACKET_1523_1548_BYTES_out),
    .STAT_TX_PACKET_1549_2047_BYTES (STAT_TX_PACKET_1549_2047_BYTES_out),
    .STAT_TX_PACKET_2048_4095_BYTES (STAT_TX_PACKET_2048_4095_BYTES_out),
    .STAT_TX_PACKET_256_511_BYTES (STAT_TX_PACKET_256_511_BYTES_out),
    .STAT_TX_PACKET_4096_8191_BYTES (STAT_TX_PACKET_4096_8191_BYTES_out),
    .STAT_TX_PACKET_512_1023_BYTES (STAT_TX_PACKET_512_1023_BYTES_out),
    .STAT_TX_PACKET_64_BYTES (STAT_TX_PACKET_64_BYTES_out),
    .STAT_TX_PACKET_65_127_BYTES (STAT_TX_PACKET_65_127_BYTES_out),
    .STAT_TX_PACKET_8192_9215_BYTES (STAT_TX_PACKET_8192_9215_BYTES_out),
    .STAT_TX_PACKET_LARGE (STAT_TX_PACKET_LARGE_out),
    .STAT_TX_PACKET_SMALL (STAT_TX_PACKET_SMALL_out),
    .STAT_TX_PAUSE (STAT_TX_PAUSE_out),
    .STAT_TX_PAUSE_VALID (STAT_TX_PAUSE_VALID_out),
    .STAT_TX_PTP_FIFO_READ_ERROR (STAT_TX_PTP_FIFO_READ_ERROR_out),
    .STAT_TX_PTP_FIFO_WRITE_ERROR (STAT_TX_PTP_FIFO_WRITE_ERROR_out),
    .STAT_TX_TOTAL_BYTES (STAT_TX_TOTAL_BYTES_out),
    .STAT_TX_TOTAL_GOOD_BYTES (STAT_TX_TOTAL_GOOD_BYTES_out),
    .STAT_TX_TOTAL_GOOD_PACKETS (STAT_TX_TOTAL_GOOD_PACKETS_out),
    .STAT_TX_TOTAL_PACKETS (STAT_TX_TOTAL_PACKETS_out),
    .STAT_TX_UNICAST (STAT_TX_UNICAST_out),
    .STAT_TX_USER_PAUSE (STAT_TX_USER_PAUSE_out),
    .STAT_TX_VLAN (STAT_TX_VLAN_out),
    .TX_OVFOUT (TX_OVFOUT_out),
    .TX_PTP_PCSLANE_OUT (TX_PTP_PCSLANE_OUT_out),
    .TX_PTP_TSTAMP_OUT (TX_PTP_TSTAMP_OUT_out),
    .TX_PTP_TSTAMP_TAG_OUT (TX_PTP_TSTAMP_TAG_OUT_out),
    .TX_PTP_TSTAMP_VALID_OUT (TX_PTP_TSTAMP_VALID_OUT_out),
    .TX_RDYOUT (TX_RDYOUT_out),
    .TX_SERDES_ALT_DATA0 (TX_SERDES_ALT_DATA0_out),
    .TX_SERDES_ALT_DATA1 (TX_SERDES_ALT_DATA1_out),
    .TX_SERDES_ALT_DATA2 (TX_SERDES_ALT_DATA2_out),
    .TX_SERDES_ALT_DATA3 (TX_SERDES_ALT_DATA3_out),
    .TX_SERDES_DATA0 (TX_SERDES_DATA0_out),
    .TX_SERDES_DATA1 (TX_SERDES_DATA1_out),
    .TX_SERDES_DATA2 (TX_SERDES_DATA2_out),
    .TX_SERDES_DATA3 (TX_SERDES_DATA3_out),
    .TX_SERDES_DATA4 (TX_SERDES_DATA4_out),
    .TX_SERDES_DATA5 (TX_SERDES_DATA5_out),
    .TX_SERDES_DATA6 (TX_SERDES_DATA6_out),
    .TX_SERDES_DATA7 (TX_SERDES_DATA7_out),
    .TX_SERDES_DATA8 (TX_SERDES_DATA8_out),
    .TX_SERDES_DATA9 (TX_SERDES_DATA9_out),
    .TX_UNFOUT (TX_UNFOUT_out),
    .CTL_CAUI4_MODE (CTL_CAUI4_MODE_in),
    .CTL_RX_CHECK_ETYPE_GCP (CTL_RX_CHECK_ETYPE_GCP_in),
    .CTL_RX_CHECK_ETYPE_GPP (CTL_RX_CHECK_ETYPE_GPP_in),
    .CTL_RX_CHECK_ETYPE_PCP (CTL_RX_CHECK_ETYPE_PCP_in),
    .CTL_RX_CHECK_ETYPE_PPP (CTL_RX_CHECK_ETYPE_PPP_in),
    .CTL_RX_CHECK_MCAST_GCP (CTL_RX_CHECK_MCAST_GCP_in),
    .CTL_RX_CHECK_MCAST_GPP (CTL_RX_CHECK_MCAST_GPP_in),
    .CTL_RX_CHECK_MCAST_PCP (CTL_RX_CHECK_MCAST_PCP_in),
    .CTL_RX_CHECK_MCAST_PPP (CTL_RX_CHECK_MCAST_PPP_in),
    .CTL_RX_CHECK_OPCODE_GCP (CTL_RX_CHECK_OPCODE_GCP_in),
    .CTL_RX_CHECK_OPCODE_GPP (CTL_RX_CHECK_OPCODE_GPP_in),
    .CTL_RX_CHECK_OPCODE_PCP (CTL_RX_CHECK_OPCODE_PCP_in),
    .CTL_RX_CHECK_OPCODE_PPP (CTL_RX_CHECK_OPCODE_PPP_in),
    .CTL_RX_CHECK_SA_GCP (CTL_RX_CHECK_SA_GCP_in),
    .CTL_RX_CHECK_SA_GPP (CTL_RX_CHECK_SA_GPP_in),
    .CTL_RX_CHECK_SA_PCP (CTL_RX_CHECK_SA_PCP_in),
    .CTL_RX_CHECK_SA_PPP (CTL_RX_CHECK_SA_PPP_in),
    .CTL_RX_CHECK_UCAST_GCP (CTL_RX_CHECK_UCAST_GCP_in),
    .CTL_RX_CHECK_UCAST_GPP (CTL_RX_CHECK_UCAST_GPP_in),
    .CTL_RX_CHECK_UCAST_PCP (CTL_RX_CHECK_UCAST_PCP_in),
    .CTL_RX_CHECK_UCAST_PPP (CTL_RX_CHECK_UCAST_PPP_in),
    .CTL_RX_ENABLE (CTL_RX_ENABLE_in),
    .CTL_RX_ENABLE_GCP (CTL_RX_ENABLE_GCP_in),
    .CTL_RX_ENABLE_GPP (CTL_RX_ENABLE_GPP_in),
    .CTL_RX_ENABLE_PCP (CTL_RX_ENABLE_PCP_in),
    .CTL_RX_ENABLE_PPP (CTL_RX_ENABLE_PPP_in),
    .CTL_RX_FORCE_RESYNC (CTL_RX_FORCE_RESYNC_in),
    .CTL_RX_PAUSE_ACK (CTL_RX_PAUSE_ACK_in),
    .CTL_RX_PAUSE_ENABLE (CTL_RX_PAUSE_ENABLE_in),
    .CTL_RX_SYSTEMTIMERIN (CTL_RX_SYSTEMTIMERIN_in),
    .CTL_RX_TEST_PATTERN (CTL_RX_TEST_PATTERN_in),
    .CTL_TX_ENABLE (CTL_TX_ENABLE_in),
    .CTL_TX_LANE0_VLM_BIP7_OVERRIDE (CTL_TX_LANE0_VLM_BIP7_OVERRIDE_in),
    .CTL_TX_LANE0_VLM_BIP7_OVERRIDE_VALUE (CTL_TX_LANE0_VLM_BIP7_OVERRIDE_VALUE_in),
    .CTL_TX_PAUSE_ENABLE (CTL_TX_PAUSE_ENABLE_in),
    .CTL_TX_PAUSE_QUANTA0 (CTL_TX_PAUSE_QUANTA0_in),
    .CTL_TX_PAUSE_QUANTA1 (CTL_TX_PAUSE_QUANTA1_in),
    .CTL_TX_PAUSE_QUANTA2 (CTL_TX_PAUSE_QUANTA2_in),
    .CTL_TX_PAUSE_QUANTA3 (CTL_TX_PAUSE_QUANTA3_in),
    .CTL_TX_PAUSE_QUANTA4 (CTL_TX_PAUSE_QUANTA4_in),
    .CTL_TX_PAUSE_QUANTA5 (CTL_TX_PAUSE_QUANTA5_in),
    .CTL_TX_PAUSE_QUANTA6 (CTL_TX_PAUSE_QUANTA6_in),
    .CTL_TX_PAUSE_QUANTA7 (CTL_TX_PAUSE_QUANTA7_in),
    .CTL_TX_PAUSE_QUANTA8 (CTL_TX_PAUSE_QUANTA8_in),
    .CTL_TX_PAUSE_REFRESH_TIMER0 (CTL_TX_PAUSE_REFRESH_TIMER0_in),
    .CTL_TX_PAUSE_REFRESH_TIMER1 (CTL_TX_PAUSE_REFRESH_TIMER1_in),
    .CTL_TX_PAUSE_REFRESH_TIMER2 (CTL_TX_PAUSE_REFRESH_TIMER2_in),
    .CTL_TX_PAUSE_REFRESH_TIMER3 (CTL_TX_PAUSE_REFRESH_TIMER3_in),
    .CTL_TX_PAUSE_REFRESH_TIMER4 (CTL_TX_PAUSE_REFRESH_TIMER4_in),
    .CTL_TX_PAUSE_REFRESH_TIMER5 (CTL_TX_PAUSE_REFRESH_TIMER5_in),
    .CTL_TX_PAUSE_REFRESH_TIMER6 (CTL_TX_PAUSE_REFRESH_TIMER6_in),
    .CTL_TX_PAUSE_REFRESH_TIMER7 (CTL_TX_PAUSE_REFRESH_TIMER7_in),
    .CTL_TX_PAUSE_REFRESH_TIMER8 (CTL_TX_PAUSE_REFRESH_TIMER8_in),
    .CTL_TX_PAUSE_REQ (CTL_TX_PAUSE_REQ_in),
    .CTL_TX_PTP_VLANE_ADJUST_MODE (CTL_TX_PTP_VLANE_ADJUST_MODE_in),
    .CTL_TX_RESEND_PAUSE (CTL_TX_RESEND_PAUSE_in),
    .CTL_TX_SEND_IDLE (CTL_TX_SEND_IDLE_in),
    .CTL_TX_SEND_RFI (CTL_TX_SEND_RFI_in),
    .CTL_TX_SYSTEMTIMERIN (CTL_TX_SYSTEMTIMERIN_in),
    .CTL_TX_TEST_PATTERN (CTL_TX_TEST_PATTERN_in),
    .DRP_ADDR (DRP_ADDR_in),
    .DRP_CLK (DRP_CLK_in),
    .DRP_DI (DRP_DI_in),
    .DRP_EN (DRP_EN_in),
    .DRP_WE (DRP_WE_in),
    .RX_CLK (RX_CLK_in),
    .RX_RESET (RX_RESET_in),
    .RX_SERDES_ALT_DATA0 (RX_SERDES_ALT_DATA0_in),
    .RX_SERDES_ALT_DATA1 (RX_SERDES_ALT_DATA1_in),
    .RX_SERDES_ALT_DATA2 (RX_SERDES_ALT_DATA2_in),
    .RX_SERDES_ALT_DATA3 (RX_SERDES_ALT_DATA3_in),
    .RX_SERDES_CLK (RX_SERDES_CLK_in),
    .RX_SERDES_DATA0 (RX_SERDES_DATA0_in),
    .RX_SERDES_DATA1 (RX_SERDES_DATA1_in),
    .RX_SERDES_DATA2 (RX_SERDES_DATA2_in),
    .RX_SERDES_DATA3 (RX_SERDES_DATA3_in),
    .RX_SERDES_DATA4 (RX_SERDES_DATA4_in),
    .RX_SERDES_DATA5 (RX_SERDES_DATA5_in),
    .RX_SERDES_DATA6 (RX_SERDES_DATA6_in),
    .RX_SERDES_DATA7 (RX_SERDES_DATA7_in),
    .RX_SERDES_DATA8 (RX_SERDES_DATA8_in),
    .RX_SERDES_DATA9 (RX_SERDES_DATA9_in),
    .RX_SERDES_RESET (RX_SERDES_RESET_in),
    .SCAN_EN (SCAN_EN_in),
    .SCAN_IN_CMAC (SCAN_IN_CMAC_in),
    .SCAN_IN_DRPCTRL (SCAN_IN_DRPCTRL_in),
    .TEST_MODE (TEST_MODE_in),
    .TEST_RESET (TEST_RESET_in),
    .TX_CLK (TX_CLK_in),
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
    .TX_PTP_1588OP_IN (TX_PTP_1588OP_IN_in),
    .TX_PTP_CHKSUM_OFFSET_IN (TX_PTP_CHKSUM_OFFSET_IN_in),
    .TX_PTP_RXTSTAMP_IN (TX_PTP_RXTSTAMP_IN_in),
    .TX_PTP_TAG_FIELD_IN (TX_PTP_TAG_FIELD_IN_in),
    .TX_PTP_TSTAMP_OFFSET_IN (TX_PTP_TSTAMP_OFFSET_IN_in),
    .TX_PTP_UPD_CHKSUM_IN (TX_PTP_UPD_CHKSUM_IN_in),
    .TX_RESET (TX_RESET_in),
    .TX_SOPIN0 (TX_SOPIN0_in),
    .TX_SOPIN1 (TX_SOPIN1_in),
    .TX_SOPIN2 (TX_SOPIN2_in),
    .TX_SOPIN3 (TX_SOPIN3_in),
    .GSR (glblGSR)
  );
end else begin : generate_block1
  SIP_CMAC SIP_CMAC_INST (
    .CTL_PTP_TRANSPCLK_MODE (CTL_PTP_TRANSPCLK_MODE_REG),
    .CTL_RX_CHECK_ACK (CTL_RX_CHECK_ACK_REG),
    .CTL_RX_CHECK_PREAMBLE (CTL_RX_CHECK_PREAMBLE_REG),
    .CTL_RX_CHECK_SFD (CTL_RX_CHECK_SFD_REG),
    .CTL_RX_DELETE_FCS (CTL_RX_DELETE_FCS_REG),
    .CTL_RX_ETYPE_GCP (CTL_RX_ETYPE_GCP_REG),
    .CTL_RX_ETYPE_GPP (CTL_RX_ETYPE_GPP_REG),
    .CTL_RX_ETYPE_PCP (CTL_RX_ETYPE_PCP_REG),
    .CTL_RX_ETYPE_PPP (CTL_RX_ETYPE_PPP_REG),
    .CTL_RX_FORWARD_CONTROL (CTL_RX_FORWARD_CONTROL_REG),
    .CTL_RX_IGNORE_FCS (CTL_RX_IGNORE_FCS_REG),
    .CTL_RX_MAX_PACKET_LEN (CTL_RX_MAX_PACKET_LEN_REG),
    .CTL_RX_MIN_PACKET_LEN (CTL_RX_MIN_PACKET_LEN_REG),
    .CTL_RX_OPCODE_GPP (CTL_RX_OPCODE_GPP_REG),
    .CTL_RX_OPCODE_MAX_GCP (CTL_RX_OPCODE_MAX_GCP_REG),
    .CTL_RX_OPCODE_MAX_PCP (CTL_RX_OPCODE_MAX_PCP_REG),
    .CTL_RX_OPCODE_MIN_GCP (CTL_RX_OPCODE_MIN_GCP_REG),
    .CTL_RX_OPCODE_MIN_PCP (CTL_RX_OPCODE_MIN_PCP_REG),
    .CTL_RX_OPCODE_PPP (CTL_RX_OPCODE_PPP_REG),
    .CTL_RX_PAUSE_DA_MCAST (CTL_RX_PAUSE_DA_MCAST_REG),
    .CTL_RX_PAUSE_DA_UCAST (CTL_RX_PAUSE_DA_UCAST_REG),
    .CTL_RX_PAUSE_SA (CTL_RX_PAUSE_SA_REG),
    .CTL_RX_PROCESS_LFI (CTL_RX_PROCESS_LFI_REG),
    .CTL_RX_VL_LENGTH_MINUS1 (CTL_RX_VL_LENGTH_MINUS1_REG),
    .CTL_RX_VL_MARKER_ID0 (CTL_RX_VL_MARKER_ID0_REG),
    .CTL_RX_VL_MARKER_ID1 (CTL_RX_VL_MARKER_ID1_REG),
    .CTL_RX_VL_MARKER_ID10 (CTL_RX_VL_MARKER_ID10_REG),
    .CTL_RX_VL_MARKER_ID11 (CTL_RX_VL_MARKER_ID11_REG),
    .CTL_RX_VL_MARKER_ID12 (CTL_RX_VL_MARKER_ID12_REG),
    .CTL_RX_VL_MARKER_ID13 (CTL_RX_VL_MARKER_ID13_REG),
    .CTL_RX_VL_MARKER_ID14 (CTL_RX_VL_MARKER_ID14_REG),
    .CTL_RX_VL_MARKER_ID15 (CTL_RX_VL_MARKER_ID15_REG),
    .CTL_RX_VL_MARKER_ID16 (CTL_RX_VL_MARKER_ID16_REG),
    .CTL_RX_VL_MARKER_ID17 (CTL_RX_VL_MARKER_ID17_REG),
    .CTL_RX_VL_MARKER_ID18 (CTL_RX_VL_MARKER_ID18_REG),
    .CTL_RX_VL_MARKER_ID19 (CTL_RX_VL_MARKER_ID19_REG),
    .CTL_RX_VL_MARKER_ID2 (CTL_RX_VL_MARKER_ID2_REG),
    .CTL_RX_VL_MARKER_ID3 (CTL_RX_VL_MARKER_ID3_REG),
    .CTL_RX_VL_MARKER_ID4 (CTL_RX_VL_MARKER_ID4_REG),
    .CTL_RX_VL_MARKER_ID5 (CTL_RX_VL_MARKER_ID5_REG),
    .CTL_RX_VL_MARKER_ID6 (CTL_RX_VL_MARKER_ID6_REG),
    .CTL_RX_VL_MARKER_ID7 (CTL_RX_VL_MARKER_ID7_REG),
    .CTL_RX_VL_MARKER_ID8 (CTL_RX_VL_MARKER_ID8_REG),
    .CTL_RX_VL_MARKER_ID9 (CTL_RX_VL_MARKER_ID9_REG),
    .CTL_TEST_MODE_PIN_CHAR (CTL_TEST_MODE_PIN_CHAR_REG),
    .CTL_TX_DA_GPP (CTL_TX_DA_GPP_REG),
    .CTL_TX_DA_PPP (CTL_TX_DA_PPP_REG),
    .CTL_TX_ETHERTYPE_GPP (CTL_TX_ETHERTYPE_GPP_REG),
    .CTL_TX_ETHERTYPE_PPP (CTL_TX_ETHERTYPE_PPP_REG),
    .CTL_TX_FCS_INS_ENABLE (CTL_TX_FCS_INS_ENABLE_REG),
    .CTL_TX_IGNORE_FCS (CTL_TX_IGNORE_FCS_REG),
    .CTL_TX_OPCODE_GPP (CTL_TX_OPCODE_GPP_REG),
    .CTL_TX_OPCODE_PPP (CTL_TX_OPCODE_PPP_REG),
    .CTL_TX_PTP_1STEP_ENABLE (CTL_TX_PTP_1STEP_ENABLE_REG),
    .CTL_TX_PTP_LATENCY_ADJUST (CTL_TX_PTP_LATENCY_ADJUST_REG),
    .CTL_TX_SA_GPP (CTL_TX_SA_GPP_REG),
    .CTL_TX_SA_PPP (CTL_TX_SA_PPP_REG),
    .CTL_TX_VL_LENGTH_MINUS1 (CTL_TX_VL_LENGTH_MINUS1_REG),
    .CTL_TX_VL_MARKER_ID0 (CTL_TX_VL_MARKER_ID0_REG),
    .CTL_TX_VL_MARKER_ID1 (CTL_TX_VL_MARKER_ID1_REG),
    .CTL_TX_VL_MARKER_ID10 (CTL_TX_VL_MARKER_ID10_REG),
    .CTL_TX_VL_MARKER_ID11 (CTL_TX_VL_MARKER_ID11_REG),
    .CTL_TX_VL_MARKER_ID12 (CTL_TX_VL_MARKER_ID12_REG),
    .CTL_TX_VL_MARKER_ID13 (CTL_TX_VL_MARKER_ID13_REG),
    .CTL_TX_VL_MARKER_ID14 (CTL_TX_VL_MARKER_ID14_REG),
    .CTL_TX_VL_MARKER_ID15 (CTL_TX_VL_MARKER_ID15_REG),
    .CTL_TX_VL_MARKER_ID16 (CTL_TX_VL_MARKER_ID16_REG),
    .CTL_TX_VL_MARKER_ID17 (CTL_TX_VL_MARKER_ID17_REG),
    .CTL_TX_VL_MARKER_ID18 (CTL_TX_VL_MARKER_ID18_REG),
    .CTL_TX_VL_MARKER_ID19 (CTL_TX_VL_MARKER_ID19_REG),
    .CTL_TX_VL_MARKER_ID2 (CTL_TX_VL_MARKER_ID2_REG),
    .CTL_TX_VL_MARKER_ID3 (CTL_TX_VL_MARKER_ID3_REG),
    .CTL_TX_VL_MARKER_ID4 (CTL_TX_VL_MARKER_ID4_REG),
    .CTL_TX_VL_MARKER_ID5 (CTL_TX_VL_MARKER_ID5_REG),
    .CTL_TX_VL_MARKER_ID6 (CTL_TX_VL_MARKER_ID6_REG),
    .CTL_TX_VL_MARKER_ID7 (CTL_TX_VL_MARKER_ID7_REG),
    .CTL_TX_VL_MARKER_ID8 (CTL_TX_VL_MARKER_ID8_REG),
    .CTL_TX_VL_MARKER_ID9 (CTL_TX_VL_MARKER_ID9_REG),
    .TEST_MODE_PIN_CHAR (TEST_MODE_PIN_CHAR_REG),
    .DRP_DO (DRP_DO_out),
    .DRP_RDY (DRP_RDY_out),
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
    .RX_LANE_ALIGNER_FILL_0 (RX_LANE_ALIGNER_FILL_0_out),
    .RX_LANE_ALIGNER_FILL_1 (RX_LANE_ALIGNER_FILL_1_out),
    .RX_LANE_ALIGNER_FILL_10 (RX_LANE_ALIGNER_FILL_10_out),
    .RX_LANE_ALIGNER_FILL_11 (RX_LANE_ALIGNER_FILL_11_out),
    .RX_LANE_ALIGNER_FILL_12 (RX_LANE_ALIGNER_FILL_12_out),
    .RX_LANE_ALIGNER_FILL_13 (RX_LANE_ALIGNER_FILL_13_out),
    .RX_LANE_ALIGNER_FILL_14 (RX_LANE_ALIGNER_FILL_14_out),
    .RX_LANE_ALIGNER_FILL_15 (RX_LANE_ALIGNER_FILL_15_out),
    .RX_LANE_ALIGNER_FILL_16 (RX_LANE_ALIGNER_FILL_16_out),
    .RX_LANE_ALIGNER_FILL_17 (RX_LANE_ALIGNER_FILL_17_out),
    .RX_LANE_ALIGNER_FILL_18 (RX_LANE_ALIGNER_FILL_18_out),
    .RX_LANE_ALIGNER_FILL_19 (RX_LANE_ALIGNER_FILL_19_out),
    .RX_LANE_ALIGNER_FILL_2 (RX_LANE_ALIGNER_FILL_2_out),
    .RX_LANE_ALIGNER_FILL_3 (RX_LANE_ALIGNER_FILL_3_out),
    .RX_LANE_ALIGNER_FILL_4 (RX_LANE_ALIGNER_FILL_4_out),
    .RX_LANE_ALIGNER_FILL_5 (RX_LANE_ALIGNER_FILL_5_out),
    .RX_LANE_ALIGNER_FILL_6 (RX_LANE_ALIGNER_FILL_6_out),
    .RX_LANE_ALIGNER_FILL_7 (RX_LANE_ALIGNER_FILL_7_out),
    .RX_LANE_ALIGNER_FILL_8 (RX_LANE_ALIGNER_FILL_8_out),
    .RX_LANE_ALIGNER_FILL_9 (RX_LANE_ALIGNER_FILL_9_out),
    .RX_MTYOUT0 (RX_MTYOUT0_out),
    .RX_MTYOUT1 (RX_MTYOUT1_out),
    .RX_MTYOUT2 (RX_MTYOUT2_out),
    .RX_MTYOUT3 (RX_MTYOUT3_out),
    .RX_PTP_PCSLANE_OUT (RX_PTP_PCSLANE_OUT_out),
    .RX_PTP_TSTAMP_OUT (RX_PTP_TSTAMP_OUT_out),
    .RX_SOPOUT0 (RX_SOPOUT0_out),
    .RX_SOPOUT1 (RX_SOPOUT1_out),
    .RX_SOPOUT2 (RX_SOPOUT2_out),
    .RX_SOPOUT3 (RX_SOPOUT3_out),
    .SCAN_OUT_CMAC (SCAN_OUT_CMAC_out),
    .SCAN_OUT_DRPCTRL (SCAN_OUT_DRPCTRL_out),
    .STAT_RX_ALIGNED (STAT_RX_ALIGNED_out),
    .STAT_RX_ALIGNED_ERR (STAT_RX_ALIGNED_ERR_out),
    .STAT_RX_BAD_CODE (STAT_RX_BAD_CODE_out),
    .STAT_RX_BAD_FCS (STAT_RX_BAD_FCS_out),
    .STAT_RX_BAD_PREAMBLE (STAT_RX_BAD_PREAMBLE_out),
    .STAT_RX_BAD_SFD (STAT_RX_BAD_SFD_out),
    .STAT_RX_BIP_ERR_0 (STAT_RX_BIP_ERR_0_out),
    .STAT_RX_BIP_ERR_1 (STAT_RX_BIP_ERR_1_out),
    .STAT_RX_BIP_ERR_10 (STAT_RX_BIP_ERR_10_out),
    .STAT_RX_BIP_ERR_11 (STAT_RX_BIP_ERR_11_out),
    .STAT_RX_BIP_ERR_12 (STAT_RX_BIP_ERR_12_out),
    .STAT_RX_BIP_ERR_13 (STAT_RX_BIP_ERR_13_out),
    .STAT_RX_BIP_ERR_14 (STAT_RX_BIP_ERR_14_out),
    .STAT_RX_BIP_ERR_15 (STAT_RX_BIP_ERR_15_out),
    .STAT_RX_BIP_ERR_16 (STAT_RX_BIP_ERR_16_out),
    .STAT_RX_BIP_ERR_17 (STAT_RX_BIP_ERR_17_out),
    .STAT_RX_BIP_ERR_18 (STAT_RX_BIP_ERR_18_out),
    .STAT_RX_BIP_ERR_19 (STAT_RX_BIP_ERR_19_out),
    .STAT_RX_BIP_ERR_2 (STAT_RX_BIP_ERR_2_out),
    .STAT_RX_BIP_ERR_3 (STAT_RX_BIP_ERR_3_out),
    .STAT_RX_BIP_ERR_4 (STAT_RX_BIP_ERR_4_out),
    .STAT_RX_BIP_ERR_5 (STAT_RX_BIP_ERR_5_out),
    .STAT_RX_BIP_ERR_6 (STAT_RX_BIP_ERR_6_out),
    .STAT_RX_BIP_ERR_7 (STAT_RX_BIP_ERR_7_out),
    .STAT_RX_BIP_ERR_8 (STAT_RX_BIP_ERR_8_out),
    .STAT_RX_BIP_ERR_9 (STAT_RX_BIP_ERR_9_out),
    .STAT_RX_BLOCK_LOCK (STAT_RX_BLOCK_LOCK_out),
    .STAT_RX_BROADCAST (STAT_RX_BROADCAST_out),
    .STAT_RX_FRAGMENT (STAT_RX_FRAGMENT_out),
    .STAT_RX_FRAMING_ERR_0 (STAT_RX_FRAMING_ERR_0_out),
    .STAT_RX_FRAMING_ERR_1 (STAT_RX_FRAMING_ERR_1_out),
    .STAT_RX_FRAMING_ERR_10 (STAT_RX_FRAMING_ERR_10_out),
    .STAT_RX_FRAMING_ERR_11 (STAT_RX_FRAMING_ERR_11_out),
    .STAT_RX_FRAMING_ERR_12 (STAT_RX_FRAMING_ERR_12_out),
    .STAT_RX_FRAMING_ERR_13 (STAT_RX_FRAMING_ERR_13_out),
    .STAT_RX_FRAMING_ERR_14 (STAT_RX_FRAMING_ERR_14_out),
    .STAT_RX_FRAMING_ERR_15 (STAT_RX_FRAMING_ERR_15_out),
    .STAT_RX_FRAMING_ERR_16 (STAT_RX_FRAMING_ERR_16_out),
    .STAT_RX_FRAMING_ERR_17 (STAT_RX_FRAMING_ERR_17_out),
    .STAT_RX_FRAMING_ERR_18 (STAT_RX_FRAMING_ERR_18_out),
    .STAT_RX_FRAMING_ERR_19 (STAT_RX_FRAMING_ERR_19_out),
    .STAT_RX_FRAMING_ERR_2 (STAT_RX_FRAMING_ERR_2_out),
    .STAT_RX_FRAMING_ERR_3 (STAT_RX_FRAMING_ERR_3_out),
    .STAT_RX_FRAMING_ERR_4 (STAT_RX_FRAMING_ERR_4_out),
    .STAT_RX_FRAMING_ERR_5 (STAT_RX_FRAMING_ERR_5_out),
    .STAT_RX_FRAMING_ERR_6 (STAT_RX_FRAMING_ERR_6_out),
    .STAT_RX_FRAMING_ERR_7 (STAT_RX_FRAMING_ERR_7_out),
    .STAT_RX_FRAMING_ERR_8 (STAT_RX_FRAMING_ERR_8_out),
    .STAT_RX_FRAMING_ERR_9 (STAT_RX_FRAMING_ERR_9_out),
    .STAT_RX_FRAMING_ERR_VALID_0 (STAT_RX_FRAMING_ERR_VALID_0_out),
    .STAT_RX_FRAMING_ERR_VALID_1 (STAT_RX_FRAMING_ERR_VALID_1_out),
    .STAT_RX_FRAMING_ERR_VALID_10 (STAT_RX_FRAMING_ERR_VALID_10_out),
    .STAT_RX_FRAMING_ERR_VALID_11 (STAT_RX_FRAMING_ERR_VALID_11_out),
    .STAT_RX_FRAMING_ERR_VALID_12 (STAT_RX_FRAMING_ERR_VALID_12_out),
    .STAT_RX_FRAMING_ERR_VALID_13 (STAT_RX_FRAMING_ERR_VALID_13_out),
    .STAT_RX_FRAMING_ERR_VALID_14 (STAT_RX_FRAMING_ERR_VALID_14_out),
    .STAT_RX_FRAMING_ERR_VALID_15 (STAT_RX_FRAMING_ERR_VALID_15_out),
    .STAT_RX_FRAMING_ERR_VALID_16 (STAT_RX_FRAMING_ERR_VALID_16_out),
    .STAT_RX_FRAMING_ERR_VALID_17 (STAT_RX_FRAMING_ERR_VALID_17_out),
    .STAT_RX_FRAMING_ERR_VALID_18 (STAT_RX_FRAMING_ERR_VALID_18_out),
    .STAT_RX_FRAMING_ERR_VALID_19 (STAT_RX_FRAMING_ERR_VALID_19_out),
    .STAT_RX_FRAMING_ERR_VALID_2 (STAT_RX_FRAMING_ERR_VALID_2_out),
    .STAT_RX_FRAMING_ERR_VALID_3 (STAT_RX_FRAMING_ERR_VALID_3_out),
    .STAT_RX_FRAMING_ERR_VALID_4 (STAT_RX_FRAMING_ERR_VALID_4_out),
    .STAT_RX_FRAMING_ERR_VALID_5 (STAT_RX_FRAMING_ERR_VALID_5_out),
    .STAT_RX_FRAMING_ERR_VALID_6 (STAT_RX_FRAMING_ERR_VALID_6_out),
    .STAT_RX_FRAMING_ERR_VALID_7 (STAT_RX_FRAMING_ERR_VALID_7_out),
    .STAT_RX_FRAMING_ERR_VALID_8 (STAT_RX_FRAMING_ERR_VALID_8_out),
    .STAT_RX_FRAMING_ERR_VALID_9 (STAT_RX_FRAMING_ERR_VALID_9_out),
    .STAT_RX_GOT_SIGNAL_OS (STAT_RX_GOT_SIGNAL_OS_out),
    .STAT_RX_HI_BER (STAT_RX_HI_BER_out),
    .STAT_RX_INRANGEERR (STAT_RX_INRANGEERR_out),
    .STAT_RX_INTERNAL_LOCAL_FAULT (STAT_RX_INTERNAL_LOCAL_FAULT_out),
    .STAT_RX_JABBER (STAT_RX_JABBER_out),
    .STAT_RX_LANE0_VLM_BIP7 (STAT_RX_LANE0_VLM_BIP7_out),
    .STAT_RX_LANE0_VLM_BIP7_VALID (STAT_RX_LANE0_VLM_BIP7_VALID_out),
    .STAT_RX_LOCAL_FAULT (STAT_RX_LOCAL_FAULT_out),
    .STAT_RX_MF_ERR (STAT_RX_MF_ERR_out),
    .STAT_RX_MF_LEN_ERR (STAT_RX_MF_LEN_ERR_out),
    .STAT_RX_MF_REPEAT_ERR (STAT_RX_MF_REPEAT_ERR_out),
    .STAT_RX_MISALIGNED (STAT_RX_MISALIGNED_out),
    .STAT_RX_MULTICAST (STAT_RX_MULTICAST_out),
    .STAT_RX_OVERSIZE (STAT_RX_OVERSIZE_out),
    .STAT_RX_PACKET_1024_1518_BYTES (STAT_RX_PACKET_1024_1518_BYTES_out),
    .STAT_RX_PACKET_128_255_BYTES (STAT_RX_PACKET_128_255_BYTES_out),
    .STAT_RX_PACKET_1519_1522_BYTES (STAT_RX_PACKET_1519_1522_BYTES_out),
    .STAT_RX_PACKET_1523_1548_BYTES (STAT_RX_PACKET_1523_1548_BYTES_out),
    .STAT_RX_PACKET_1549_2047_BYTES (STAT_RX_PACKET_1549_2047_BYTES_out),
    .STAT_RX_PACKET_2048_4095_BYTES (STAT_RX_PACKET_2048_4095_BYTES_out),
    .STAT_RX_PACKET_256_511_BYTES (STAT_RX_PACKET_256_511_BYTES_out),
    .STAT_RX_PACKET_4096_8191_BYTES (STAT_RX_PACKET_4096_8191_BYTES_out),
    .STAT_RX_PACKET_512_1023_BYTES (STAT_RX_PACKET_512_1023_BYTES_out),
    .STAT_RX_PACKET_64_BYTES (STAT_RX_PACKET_64_BYTES_out),
    .STAT_RX_PACKET_65_127_BYTES (STAT_RX_PACKET_65_127_BYTES_out),
    .STAT_RX_PACKET_8192_9215_BYTES (STAT_RX_PACKET_8192_9215_BYTES_out),
    .STAT_RX_PACKET_BAD_FCS (STAT_RX_PACKET_BAD_FCS_out),
    .STAT_RX_PACKET_LARGE (STAT_RX_PACKET_LARGE_out),
    .STAT_RX_PACKET_SMALL (STAT_RX_PACKET_SMALL_out),
    .STAT_RX_PAUSE (STAT_RX_PAUSE_out),
    .STAT_RX_PAUSE_QUANTA0 (STAT_RX_PAUSE_QUANTA0_out),
    .STAT_RX_PAUSE_QUANTA1 (STAT_RX_PAUSE_QUANTA1_out),
    .STAT_RX_PAUSE_QUANTA2 (STAT_RX_PAUSE_QUANTA2_out),
    .STAT_RX_PAUSE_QUANTA3 (STAT_RX_PAUSE_QUANTA3_out),
    .STAT_RX_PAUSE_QUANTA4 (STAT_RX_PAUSE_QUANTA4_out),
    .STAT_RX_PAUSE_QUANTA5 (STAT_RX_PAUSE_QUANTA5_out),
    .STAT_RX_PAUSE_QUANTA6 (STAT_RX_PAUSE_QUANTA6_out),
    .STAT_RX_PAUSE_QUANTA7 (STAT_RX_PAUSE_QUANTA7_out),
    .STAT_RX_PAUSE_QUANTA8 (STAT_RX_PAUSE_QUANTA8_out),
    .STAT_RX_PAUSE_REQ (STAT_RX_PAUSE_REQ_out),
    .STAT_RX_PAUSE_VALID (STAT_RX_PAUSE_VALID_out),
    .STAT_RX_RECEIVED_LOCAL_FAULT (STAT_RX_RECEIVED_LOCAL_FAULT_out),
    .STAT_RX_REMOTE_FAULT (STAT_RX_REMOTE_FAULT_out),
    .STAT_RX_STATUS (STAT_RX_STATUS_out),
    .STAT_RX_STOMPED_FCS (STAT_RX_STOMPED_FCS_out),
    .STAT_RX_SYNCED (STAT_RX_SYNCED_out),
    .STAT_RX_SYNCED_ERR (STAT_RX_SYNCED_ERR_out),
    .STAT_RX_TEST_PATTERN_MISMATCH (STAT_RX_TEST_PATTERN_MISMATCH_out),
    .STAT_RX_TOOLONG (STAT_RX_TOOLONG_out),
    .STAT_RX_TOTAL_BYTES (STAT_RX_TOTAL_BYTES_out),
    .STAT_RX_TOTAL_GOOD_BYTES (STAT_RX_TOTAL_GOOD_BYTES_out),
    .STAT_RX_TOTAL_GOOD_PACKETS (STAT_RX_TOTAL_GOOD_PACKETS_out),
    .STAT_RX_TOTAL_PACKETS (STAT_RX_TOTAL_PACKETS_out),
    .STAT_RX_TRUNCATED (STAT_RX_TRUNCATED_out),
    .STAT_RX_UNDERSIZE (STAT_RX_UNDERSIZE_out),
    .STAT_RX_UNICAST (STAT_RX_UNICAST_out),
    .STAT_RX_USER_PAUSE (STAT_RX_USER_PAUSE_out),
    .STAT_RX_VLAN (STAT_RX_VLAN_out),
    .STAT_RX_VL_DEMUXED (STAT_RX_VL_DEMUXED_out),
    .STAT_RX_VL_NUMBER_0 (STAT_RX_VL_NUMBER_0_out),
    .STAT_RX_VL_NUMBER_1 (STAT_RX_VL_NUMBER_1_out),
    .STAT_RX_VL_NUMBER_10 (STAT_RX_VL_NUMBER_10_out),
    .STAT_RX_VL_NUMBER_11 (STAT_RX_VL_NUMBER_11_out),
    .STAT_RX_VL_NUMBER_12 (STAT_RX_VL_NUMBER_12_out),
    .STAT_RX_VL_NUMBER_13 (STAT_RX_VL_NUMBER_13_out),
    .STAT_RX_VL_NUMBER_14 (STAT_RX_VL_NUMBER_14_out),
    .STAT_RX_VL_NUMBER_15 (STAT_RX_VL_NUMBER_15_out),
    .STAT_RX_VL_NUMBER_16 (STAT_RX_VL_NUMBER_16_out),
    .STAT_RX_VL_NUMBER_17 (STAT_RX_VL_NUMBER_17_out),
    .STAT_RX_VL_NUMBER_18 (STAT_RX_VL_NUMBER_18_out),
    .STAT_RX_VL_NUMBER_19 (STAT_RX_VL_NUMBER_19_out),
    .STAT_RX_VL_NUMBER_2 (STAT_RX_VL_NUMBER_2_out),
    .STAT_RX_VL_NUMBER_3 (STAT_RX_VL_NUMBER_3_out),
    .STAT_RX_VL_NUMBER_4 (STAT_RX_VL_NUMBER_4_out),
    .STAT_RX_VL_NUMBER_5 (STAT_RX_VL_NUMBER_5_out),
    .STAT_RX_VL_NUMBER_6 (STAT_RX_VL_NUMBER_6_out),
    .STAT_RX_VL_NUMBER_7 (STAT_RX_VL_NUMBER_7_out),
    .STAT_RX_VL_NUMBER_8 (STAT_RX_VL_NUMBER_8_out),
    .STAT_RX_VL_NUMBER_9 (STAT_RX_VL_NUMBER_9_out),
    .STAT_TX_BAD_FCS (STAT_TX_BAD_FCS_out),
    .STAT_TX_BROADCAST (STAT_TX_BROADCAST_out),
    .STAT_TX_FRAME_ERROR (STAT_TX_FRAME_ERROR_out),
    .STAT_TX_LOCAL_FAULT (STAT_TX_LOCAL_FAULT_out),
    .STAT_TX_MULTICAST (STAT_TX_MULTICAST_out),
    .STAT_TX_PACKET_1024_1518_BYTES (STAT_TX_PACKET_1024_1518_BYTES_out),
    .STAT_TX_PACKET_128_255_BYTES (STAT_TX_PACKET_128_255_BYTES_out),
    .STAT_TX_PACKET_1519_1522_BYTES (STAT_TX_PACKET_1519_1522_BYTES_out),
    .STAT_TX_PACKET_1523_1548_BYTES (STAT_TX_PACKET_1523_1548_BYTES_out),
    .STAT_TX_PACKET_1549_2047_BYTES (STAT_TX_PACKET_1549_2047_BYTES_out),
    .STAT_TX_PACKET_2048_4095_BYTES (STAT_TX_PACKET_2048_4095_BYTES_out),
    .STAT_TX_PACKET_256_511_BYTES (STAT_TX_PACKET_256_511_BYTES_out),
    .STAT_TX_PACKET_4096_8191_BYTES (STAT_TX_PACKET_4096_8191_BYTES_out),
    .STAT_TX_PACKET_512_1023_BYTES (STAT_TX_PACKET_512_1023_BYTES_out),
    .STAT_TX_PACKET_64_BYTES (STAT_TX_PACKET_64_BYTES_out),
    .STAT_TX_PACKET_65_127_BYTES (STAT_TX_PACKET_65_127_BYTES_out),
    .STAT_TX_PACKET_8192_9215_BYTES (STAT_TX_PACKET_8192_9215_BYTES_out),
    .STAT_TX_PACKET_LARGE (STAT_TX_PACKET_LARGE_out),
    .STAT_TX_PACKET_SMALL (STAT_TX_PACKET_SMALL_out),
    .STAT_TX_PAUSE (STAT_TX_PAUSE_out),
    .STAT_TX_PAUSE_VALID (STAT_TX_PAUSE_VALID_out),
    .STAT_TX_PTP_FIFO_READ_ERROR (STAT_TX_PTP_FIFO_READ_ERROR_out),
    .STAT_TX_PTP_FIFO_WRITE_ERROR (STAT_TX_PTP_FIFO_WRITE_ERROR_out),
    .STAT_TX_TOTAL_BYTES (STAT_TX_TOTAL_BYTES_out),
    .STAT_TX_TOTAL_GOOD_BYTES (STAT_TX_TOTAL_GOOD_BYTES_out),
    .STAT_TX_TOTAL_GOOD_PACKETS (STAT_TX_TOTAL_GOOD_PACKETS_out),
    .STAT_TX_TOTAL_PACKETS (STAT_TX_TOTAL_PACKETS_out),
    .STAT_TX_UNICAST (STAT_TX_UNICAST_out),
    .STAT_TX_USER_PAUSE (STAT_TX_USER_PAUSE_out),
    .STAT_TX_VLAN (STAT_TX_VLAN_out),
    .TX_OVFOUT (TX_OVFOUT_out),
    .TX_PTP_PCSLANE_OUT (TX_PTP_PCSLANE_OUT_out),
    .TX_PTP_TSTAMP_OUT (TX_PTP_TSTAMP_OUT_out),
    .TX_PTP_TSTAMP_TAG_OUT (TX_PTP_TSTAMP_TAG_OUT_out),
    .TX_PTP_TSTAMP_VALID_OUT (TX_PTP_TSTAMP_VALID_OUT_out),
    .TX_RDYOUT (TX_RDYOUT_out),
    .TX_SERDES_ALT_DATA0 (TX_SERDES_ALT_DATA0_out),
    .TX_SERDES_ALT_DATA1 (TX_SERDES_ALT_DATA1_out),
    .TX_SERDES_ALT_DATA2 (TX_SERDES_ALT_DATA2_out),
    .TX_SERDES_ALT_DATA3 (TX_SERDES_ALT_DATA3_out),
    .TX_SERDES_DATA0 (TX_SERDES_DATA0_out),
    .TX_SERDES_DATA1 (TX_SERDES_DATA1_out),
    .TX_SERDES_DATA2 (TX_SERDES_DATA2_out),
    .TX_SERDES_DATA3 (TX_SERDES_DATA3_out),
    .TX_SERDES_DATA4 (TX_SERDES_DATA4_out),
    .TX_SERDES_DATA5 (TX_SERDES_DATA5_out),
    .TX_SERDES_DATA6 (TX_SERDES_DATA6_out),
    .TX_SERDES_DATA7 (TX_SERDES_DATA7_out),
    .TX_SERDES_DATA8 (TX_SERDES_DATA8_out),
    .TX_SERDES_DATA9 (TX_SERDES_DATA9_out),
    .TX_UNFOUT (TX_UNFOUT_out),
    .CTL_CAUI4_MODE (CTL_CAUI4_MODE_in),
    .CTL_RX_CHECK_ETYPE_GCP (CTL_RX_CHECK_ETYPE_GCP_in),
    .CTL_RX_CHECK_ETYPE_GPP (CTL_RX_CHECK_ETYPE_GPP_in),
    .CTL_RX_CHECK_ETYPE_PCP (CTL_RX_CHECK_ETYPE_PCP_in),
    .CTL_RX_CHECK_ETYPE_PPP (CTL_RX_CHECK_ETYPE_PPP_in),
    .CTL_RX_CHECK_MCAST_GCP (CTL_RX_CHECK_MCAST_GCP_in),
    .CTL_RX_CHECK_MCAST_GPP (CTL_RX_CHECK_MCAST_GPP_in),
    .CTL_RX_CHECK_MCAST_PCP (CTL_RX_CHECK_MCAST_PCP_in),
    .CTL_RX_CHECK_MCAST_PPP (CTL_RX_CHECK_MCAST_PPP_in),
    .CTL_RX_CHECK_OPCODE_GCP (CTL_RX_CHECK_OPCODE_GCP_in),
    .CTL_RX_CHECK_OPCODE_GPP (CTL_RX_CHECK_OPCODE_GPP_in),
    .CTL_RX_CHECK_OPCODE_PCP (CTL_RX_CHECK_OPCODE_PCP_in),
    .CTL_RX_CHECK_OPCODE_PPP (CTL_RX_CHECK_OPCODE_PPP_in),
    .CTL_RX_CHECK_SA_GCP (CTL_RX_CHECK_SA_GCP_in),
    .CTL_RX_CHECK_SA_GPP (CTL_RX_CHECK_SA_GPP_in),
    .CTL_RX_CHECK_SA_PCP (CTL_RX_CHECK_SA_PCP_in),
    .CTL_RX_CHECK_SA_PPP (CTL_RX_CHECK_SA_PPP_in),
    .CTL_RX_CHECK_UCAST_GCP (CTL_RX_CHECK_UCAST_GCP_in),
    .CTL_RX_CHECK_UCAST_GPP (CTL_RX_CHECK_UCAST_GPP_in),
    .CTL_RX_CHECK_UCAST_PCP (CTL_RX_CHECK_UCAST_PCP_in),
    .CTL_RX_CHECK_UCAST_PPP (CTL_RX_CHECK_UCAST_PPP_in),
    .CTL_RX_ENABLE (CTL_RX_ENABLE_in),
    .CTL_RX_ENABLE_GCP (CTL_RX_ENABLE_GCP_in),
    .CTL_RX_ENABLE_GPP (CTL_RX_ENABLE_GPP_in),
    .CTL_RX_ENABLE_PCP (CTL_RX_ENABLE_PCP_in),
    .CTL_RX_ENABLE_PPP (CTL_RX_ENABLE_PPP_in),
    .CTL_RX_FORCE_RESYNC (CTL_RX_FORCE_RESYNC_in),
    .CTL_RX_PAUSE_ACK (CTL_RX_PAUSE_ACK_in),
    .CTL_RX_PAUSE_ENABLE (CTL_RX_PAUSE_ENABLE_in),
    .CTL_RX_SYSTEMTIMERIN (CTL_RX_SYSTEMTIMERIN_in),
    .CTL_RX_TEST_PATTERN (CTL_RX_TEST_PATTERN_in),
    .CTL_TX_ENABLE (CTL_TX_ENABLE_in),
    .CTL_TX_LANE0_VLM_BIP7_OVERRIDE (CTL_TX_LANE0_VLM_BIP7_OVERRIDE_in),
    .CTL_TX_LANE0_VLM_BIP7_OVERRIDE_VALUE (CTL_TX_LANE0_VLM_BIP7_OVERRIDE_VALUE_in),
    .CTL_TX_PAUSE_ENABLE (CTL_TX_PAUSE_ENABLE_in),
    .CTL_TX_PAUSE_QUANTA0 (CTL_TX_PAUSE_QUANTA0_in),
    .CTL_TX_PAUSE_QUANTA1 (CTL_TX_PAUSE_QUANTA1_in),
    .CTL_TX_PAUSE_QUANTA2 (CTL_TX_PAUSE_QUANTA2_in),
    .CTL_TX_PAUSE_QUANTA3 (CTL_TX_PAUSE_QUANTA3_in),
    .CTL_TX_PAUSE_QUANTA4 (CTL_TX_PAUSE_QUANTA4_in),
    .CTL_TX_PAUSE_QUANTA5 (CTL_TX_PAUSE_QUANTA5_in),
    .CTL_TX_PAUSE_QUANTA6 (CTL_TX_PAUSE_QUANTA6_in),
    .CTL_TX_PAUSE_QUANTA7 (CTL_TX_PAUSE_QUANTA7_in),
    .CTL_TX_PAUSE_QUANTA8 (CTL_TX_PAUSE_QUANTA8_in),
    .CTL_TX_PAUSE_REFRESH_TIMER0 (CTL_TX_PAUSE_REFRESH_TIMER0_in),
    .CTL_TX_PAUSE_REFRESH_TIMER1 (CTL_TX_PAUSE_REFRESH_TIMER1_in),
    .CTL_TX_PAUSE_REFRESH_TIMER2 (CTL_TX_PAUSE_REFRESH_TIMER2_in),
    .CTL_TX_PAUSE_REFRESH_TIMER3 (CTL_TX_PAUSE_REFRESH_TIMER3_in),
    .CTL_TX_PAUSE_REFRESH_TIMER4 (CTL_TX_PAUSE_REFRESH_TIMER4_in),
    .CTL_TX_PAUSE_REFRESH_TIMER5 (CTL_TX_PAUSE_REFRESH_TIMER5_in),
    .CTL_TX_PAUSE_REFRESH_TIMER6 (CTL_TX_PAUSE_REFRESH_TIMER6_in),
    .CTL_TX_PAUSE_REFRESH_TIMER7 (CTL_TX_PAUSE_REFRESH_TIMER7_in),
    .CTL_TX_PAUSE_REFRESH_TIMER8 (CTL_TX_PAUSE_REFRESH_TIMER8_in),
    .CTL_TX_PAUSE_REQ (CTL_TX_PAUSE_REQ_in),
    .CTL_TX_PTP_VLANE_ADJUST_MODE (CTL_TX_PTP_VLANE_ADJUST_MODE_in),
    .CTL_TX_RESEND_PAUSE (CTL_TX_RESEND_PAUSE_in),
    .CTL_TX_SEND_IDLE (CTL_TX_SEND_IDLE_in),
    .CTL_TX_SEND_RFI (CTL_TX_SEND_RFI_in),
    .CTL_TX_SYSTEMTIMERIN (CTL_TX_SYSTEMTIMERIN_in),
    .CTL_TX_TEST_PATTERN (CTL_TX_TEST_PATTERN_in),
    .DRP_ADDR (DRP_ADDR_in),
    .DRP_CLK (DRP_CLK_in),
    .DRP_DI (DRP_DI_in),
    .DRP_EN (DRP_EN_in),
    .DRP_WE (DRP_WE_in),
    .RX_CLK (RX_CLK_in),
    .RX_RESET (RX_RESET_in),
    .RX_SERDES_ALT_DATA0 (RX_SERDES_ALT_DATA0_in),
    .RX_SERDES_ALT_DATA1 (RX_SERDES_ALT_DATA1_in),
    .RX_SERDES_ALT_DATA2 (RX_SERDES_ALT_DATA2_in),
    .RX_SERDES_ALT_DATA3 (RX_SERDES_ALT_DATA3_in),
    .RX_SERDES_CLK (RX_SERDES_CLK_in),
    .RX_SERDES_DATA0 (RX_SERDES_DATA0_in),
    .RX_SERDES_DATA1 (RX_SERDES_DATA1_in),
    .RX_SERDES_DATA2 (RX_SERDES_DATA2_in),
    .RX_SERDES_DATA3 (RX_SERDES_DATA3_in),
    .RX_SERDES_DATA4 (RX_SERDES_DATA4_in),
    .RX_SERDES_DATA5 (RX_SERDES_DATA5_in),
    .RX_SERDES_DATA6 (RX_SERDES_DATA6_in),
    .RX_SERDES_DATA7 (RX_SERDES_DATA7_in),
    .RX_SERDES_DATA8 (RX_SERDES_DATA8_in),
    .RX_SERDES_DATA9 (RX_SERDES_DATA9_in),
    .RX_SERDES_RESET (RX_SERDES_RESET_in),
    .SCAN_EN (SCAN_EN_in),
    .SCAN_IN_CMAC (SCAN_IN_CMAC_in),
    .SCAN_IN_DRPCTRL (SCAN_IN_DRPCTRL_in),
    .TEST_MODE (TEST_MODE_in),
    .TEST_RESET (TEST_RESET_in),
    .TX_CLK (TX_CLK_in),
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
    .TX_PTP_1588OP_IN (TX_PTP_1588OP_IN_in),
    .TX_PTP_CHKSUM_OFFSET_IN (TX_PTP_CHKSUM_OFFSET_IN_in),
    .TX_PTP_RXTSTAMP_IN (TX_PTP_RXTSTAMP_IN_in),
    .TX_PTP_TAG_FIELD_IN (TX_PTP_TAG_FIELD_IN_in),
    .TX_PTP_TSTAMP_OFFSET_IN (TX_PTP_TSTAMP_OFFSET_IN_in),
    .TX_PTP_UPD_CHKSUM_IN (TX_PTP_UPD_CHKSUM_IN_in),
    .TX_RESET (TX_RESET_in),
    .TX_SOPIN0 (TX_SOPIN0_in),
    .TX_SOPIN1 (TX_SOPIN1_in),
    .TX_SOPIN2 (TX_SOPIN2_in),
    .TX_SOPIN3 (TX_SOPIN3_in),
    .GSR (glblGSR)
  );
 end
 endgenerate

  specify
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
    (RX_CLK => RX_DATAOUT0[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[100]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[101]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[102]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[103]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[104]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[105]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[106]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[107]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[108]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[109]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[10]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[110]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[111]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[112]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[113]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[114]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[115]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[116]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[117]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[118]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[119]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[11]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[120]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[121]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[122]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[123]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[124]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[125]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[126]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[127]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[12]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[13]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[14]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[15]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[16]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[17]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[18]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[19]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[20]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[21]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[22]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[23]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[24]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[25]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[26]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[27]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[28]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[29]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[30]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[31]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[32]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[33]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[34]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[35]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[36]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[37]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[38]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[39]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[40]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[41]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[42]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[43]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[44]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[45]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[46]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[47]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[48]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[49]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[4]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[50]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[51]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[52]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[53]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[54]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[55]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[56]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[57]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[58]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[59]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[5]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[60]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[61]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[62]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[63]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[64]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[65]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[66]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[67]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[68]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[69]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[6]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[70]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[71]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[72]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[73]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[74]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[75]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[76]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[77]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[78]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[79]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[7]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[80]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[81]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[82]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[83]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[84]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[85]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[86]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[87]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[88]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[89]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[8]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[90]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[91]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[92]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[93]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[94]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[95]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[96]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[97]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[98]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[99]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT0[9]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[100]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[101]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[102]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[103]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[104]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[105]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[106]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[107]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[108]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[109]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[10]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[110]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[111]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[112]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[113]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[114]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[115]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[116]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[117]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[118]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[119]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[11]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[120]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[121]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[122]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[123]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[124]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[125]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[126]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[127]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[12]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[13]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[14]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[15]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[16]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[17]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[18]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[19]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[20]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[21]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[22]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[23]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[24]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[25]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[26]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[27]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[28]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[29]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[30]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[31]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[32]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[33]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[34]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[35]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[36]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[37]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[38]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[39]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[40]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[41]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[42]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[43]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[44]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[45]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[46]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[47]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[48]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[49]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[4]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[50]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[51]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[52]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[53]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[54]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[55]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[56]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[57]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[58]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[59]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[5]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[60]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[61]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[62]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[63]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[64]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[65]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[66]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[67]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[68]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[69]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[6]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[70]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[71]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[72]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[73]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[74]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[75]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[76]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[77]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[78]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[79]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[7]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[80]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[81]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[82]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[83]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[84]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[85]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[86]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[87]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[88]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[89]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[8]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[90]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[91]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[92]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[93]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[94]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[95]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[96]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[97]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[98]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[99]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT1[9]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[100]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[101]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[102]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[103]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[104]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[105]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[106]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[107]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[108]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[109]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[10]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[110]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[111]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[112]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[113]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[114]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[115]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[116]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[117]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[118]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[119]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[11]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[120]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[121]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[122]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[123]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[124]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[125]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[126]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[127]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[12]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[13]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[14]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[15]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[16]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[17]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[18]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[19]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[20]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[21]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[22]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[23]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[24]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[25]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[26]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[27]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[28]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[29]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[30]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[31]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[32]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[33]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[34]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[35]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[36]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[37]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[38]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[39]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[40]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[41]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[42]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[43]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[44]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[45]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[46]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[47]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[48]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[49]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[4]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[50]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[51]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[52]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[53]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[54]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[55]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[56]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[57]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[58]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[59]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[5]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[60]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[61]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[62]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[63]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[64]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[65]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[66]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[67]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[68]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[69]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[6]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[70]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[71]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[72]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[73]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[74]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[75]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[76]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[77]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[78]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[79]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[7]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[80]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[81]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[82]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[83]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[84]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[85]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[86]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[87]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[88]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[89]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[8]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[90]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[91]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[92]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[93]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[94]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[95]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[96]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[97]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[98]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[99]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT2[9]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[100]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[101]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[102]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[103]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[104]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[105]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[106]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[107]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[108]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[109]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[10]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[110]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[111]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[112]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[113]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[114]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[115]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[116]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[117]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[118]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[119]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[11]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[120]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[121]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[122]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[123]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[124]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[125]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[126]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[127]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[12]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[13]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[14]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[15]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[16]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[17]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[18]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[19]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[20]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[21]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[22]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[23]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[24]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[25]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[26]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[27]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[28]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[29]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[30]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[31]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[32]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[33]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[34]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[35]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[36]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[37]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[38]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[39]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[40]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[41]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[42]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[43]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[44]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[45]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[46]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[47]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[48]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[49]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[4]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[50]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[51]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[52]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[53]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[54]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[55]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[56]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[57]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[58]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[59]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[5]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[60]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[61]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[62]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[63]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[64]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[65]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[66]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[67]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[68]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[69]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[6]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[70]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[71]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[72]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[73]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[74]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[75]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[76]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[77]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[78]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[79]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[7]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[80]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[81]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[82]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[83]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[84]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[85]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[86]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[87]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[88]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[89]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[8]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[90]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[91]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[92]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[93]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[94]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[95]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[96]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[97]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[98]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[99]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_DATAOUT3[9]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_ENAOUT0) = (100:100:100, 100:100:100);
    (RX_CLK => RX_ENAOUT1) = (100:100:100, 100:100:100);
    (RX_CLK => RX_ENAOUT2) = (100:100:100, 100:100:100);
    (RX_CLK => RX_ENAOUT3) = (100:100:100, 100:100:100);
    (RX_CLK => RX_EOPOUT0) = (100:100:100, 100:100:100);
    (RX_CLK => RX_EOPOUT1) = (100:100:100, 100:100:100);
    (RX_CLK => RX_EOPOUT2) = (100:100:100, 100:100:100);
    (RX_CLK => RX_EOPOUT3) = (100:100:100, 100:100:100);
    (RX_CLK => RX_ERROUT0) = (100:100:100, 100:100:100);
    (RX_CLK => RX_ERROUT1) = (100:100:100, 100:100:100);
    (RX_CLK => RX_ERROUT2) = (100:100:100, 100:100:100);
    (RX_CLK => RX_ERROUT3) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_0[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_0[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_0[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_0[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_0[4]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_0[5]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_0[6]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_10[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_10[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_10[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_10[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_10[4]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_10[5]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_10[6]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_11[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_11[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_11[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_11[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_11[4]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_11[5]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_11[6]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_12[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_12[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_12[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_12[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_12[4]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_12[5]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_12[6]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_13[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_13[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_13[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_13[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_13[4]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_13[5]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_13[6]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_14[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_14[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_14[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_14[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_14[4]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_14[5]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_14[6]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_15[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_15[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_15[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_15[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_15[4]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_15[5]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_15[6]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_16[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_16[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_16[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_16[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_16[4]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_16[5]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_16[6]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_17[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_17[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_17[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_17[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_17[4]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_17[5]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_17[6]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_18[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_18[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_18[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_18[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_18[4]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_18[5]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_18[6]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_19[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_19[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_19[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_19[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_19[4]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_19[5]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_19[6]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_1[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_1[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_1[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_1[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_1[4]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_1[5]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_1[6]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_2[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_2[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_2[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_2[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_2[4]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_2[5]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_2[6]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_3[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_3[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_3[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_3[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_3[4]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_3[5]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_3[6]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_4[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_4[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_4[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_4[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_4[4]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_4[5]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_4[6]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_5[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_5[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_5[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_5[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_5[4]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_5[5]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_5[6]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_6[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_6[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_6[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_6[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_6[4]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_6[5]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_6[6]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_7[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_7[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_7[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_7[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_7[4]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_7[5]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_7[6]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_8[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_8[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_8[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_8[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_8[4]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_8[5]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_8[6]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_9[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_9[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_9[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_9[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_9[4]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_9[5]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_LANE_ALIGNER_FILL_9[6]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_MTYOUT0[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_MTYOUT0[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_MTYOUT0[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_MTYOUT0[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_MTYOUT1[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_MTYOUT1[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_MTYOUT1[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_MTYOUT1[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_MTYOUT2[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_MTYOUT2[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_MTYOUT2[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_MTYOUT2[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_MTYOUT3[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_MTYOUT3[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_MTYOUT3[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_MTYOUT3[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_PCSLANE_OUT[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_PCSLANE_OUT[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_PCSLANE_OUT[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_PCSLANE_OUT[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_PCSLANE_OUT[4]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[10]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[11]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[12]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[13]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[14]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[15]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[16]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[17]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[18]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[19]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[20]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[21]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[22]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[23]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[24]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[25]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[26]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[27]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[28]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[29]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[30]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[31]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[32]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[33]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[34]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[35]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[36]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[37]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[38]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[39]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[40]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[41]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[42]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[43]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[44]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[45]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[46]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[47]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[48]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[49]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[4]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[50]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[51]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[52]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[53]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[54]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[55]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[56]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[57]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[58]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[59]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[5]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[60]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[61]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[62]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[63]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[64]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[65]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[66]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[67]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[68]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[69]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[6]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[70]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[71]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[72]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[73]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[74]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[75]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[76]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[77]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[78]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[79]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[7]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[8]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_PTP_TSTAMP_OUT[9]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_SOPOUT0) = (100:100:100, 100:100:100);
    (RX_CLK => RX_SOPOUT1) = (100:100:100, 100:100:100);
    (RX_CLK => RX_SOPOUT2) = (100:100:100, 100:100:100);
    (RX_CLK => RX_SOPOUT3) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_ALIGNED) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_ALIGNED_ERR) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BAD_CODE[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BAD_CODE[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BAD_CODE[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BAD_FCS[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BAD_FCS[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BAD_FCS[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BAD_FCS[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BAD_PREAMBLE) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BAD_SFD) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BIP_ERR_0) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BIP_ERR_1) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BIP_ERR_10) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BIP_ERR_11) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BIP_ERR_12) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BIP_ERR_13) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BIP_ERR_14) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BIP_ERR_15) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BIP_ERR_16) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BIP_ERR_17) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BIP_ERR_18) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BIP_ERR_19) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BIP_ERR_2) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BIP_ERR_3) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BIP_ERR_4) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BIP_ERR_5) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BIP_ERR_6) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BIP_ERR_7) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BIP_ERR_8) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BIP_ERR_9) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BLOCK_LOCK[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BLOCK_LOCK[10]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BLOCK_LOCK[11]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BLOCK_LOCK[12]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BLOCK_LOCK[13]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BLOCK_LOCK[14]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BLOCK_LOCK[15]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BLOCK_LOCK[16]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BLOCK_LOCK[17]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BLOCK_LOCK[18]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BLOCK_LOCK[19]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BLOCK_LOCK[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BLOCK_LOCK[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BLOCK_LOCK[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BLOCK_LOCK[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BLOCK_LOCK[5]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BLOCK_LOCK[6]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BLOCK_LOCK[7]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BLOCK_LOCK[8]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BLOCK_LOCK[9]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_BROADCAST) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAGMENT[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAGMENT[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAGMENT[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAGMENT[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_0[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_0[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_0[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_0[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_10[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_10[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_10[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_10[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_11[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_11[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_11[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_11[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_12[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_12[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_12[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_12[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_13[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_13[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_13[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_13[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_14[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_14[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_14[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_14[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_15[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_15[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_15[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_15[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_16[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_16[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_16[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_16[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_17[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_17[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_17[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_17[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_18[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_18[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_18[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_18[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_19[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_19[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_19[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_19[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_1[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_1[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_1[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_1[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_2[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_2[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_2[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_2[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_3[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_3[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_3[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_3[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_4[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_4[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_4[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_4[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_5[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_5[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_5[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_5[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_6[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_6[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_6[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_6[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_7[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_7[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_7[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_7[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_8[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_8[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_8[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_8[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_9[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_9[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_9[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_9[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_VALID_0) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_VALID_1) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_VALID_10) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_VALID_11) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_VALID_12) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_VALID_13) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_VALID_14) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_VALID_15) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_VALID_16) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_VALID_17) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_VALID_18) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_VALID_19) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_VALID_2) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_VALID_3) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_VALID_4) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_VALID_5) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_VALID_6) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_VALID_7) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_VALID_8) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_FRAMING_ERR_VALID_9) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_GOT_SIGNAL_OS) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_HI_BER) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_INRANGEERR) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_INTERNAL_LOCAL_FAULT) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_JABBER) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_LANE0_VLM_BIP7[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_LANE0_VLM_BIP7[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_LANE0_VLM_BIP7[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_LANE0_VLM_BIP7[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_LANE0_VLM_BIP7[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_LANE0_VLM_BIP7[5]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_LANE0_VLM_BIP7[6]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_LANE0_VLM_BIP7[7]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_LANE0_VLM_BIP7_VALID) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_LOCAL_FAULT) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_ERR[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_ERR[10]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_ERR[11]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_ERR[12]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_ERR[13]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_ERR[14]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_ERR[15]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_ERR[16]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_ERR[17]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_ERR[18]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_ERR[19]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_ERR[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_ERR[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_ERR[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_ERR[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_ERR[5]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_ERR[6]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_ERR[7]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_ERR[8]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_ERR[9]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_LEN_ERR[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_LEN_ERR[10]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_LEN_ERR[11]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_LEN_ERR[12]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_LEN_ERR[13]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_LEN_ERR[14]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_LEN_ERR[15]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_LEN_ERR[16]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_LEN_ERR[17]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_LEN_ERR[18]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_LEN_ERR[19]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_LEN_ERR[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_LEN_ERR[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_LEN_ERR[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_LEN_ERR[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_LEN_ERR[5]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_LEN_ERR[6]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_LEN_ERR[7]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_LEN_ERR[8]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_LEN_ERR[9]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_REPEAT_ERR[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_REPEAT_ERR[10]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_REPEAT_ERR[11]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_REPEAT_ERR[12]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_REPEAT_ERR[13]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_REPEAT_ERR[14]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_REPEAT_ERR[15]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_REPEAT_ERR[16]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_REPEAT_ERR[17]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_REPEAT_ERR[18]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_REPEAT_ERR[19]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_REPEAT_ERR[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_REPEAT_ERR[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_REPEAT_ERR[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_REPEAT_ERR[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_REPEAT_ERR[5]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_REPEAT_ERR[6]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_REPEAT_ERR[7]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_REPEAT_ERR[8]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MF_REPEAT_ERR[9]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MISALIGNED) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_MULTICAST) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_OVERSIZE) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PACKET_1024_1518_BYTES) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PACKET_128_255_BYTES) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PACKET_1519_1522_BYTES) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PACKET_1523_1548_BYTES) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PACKET_1549_2047_BYTES) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PACKET_2048_4095_BYTES) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PACKET_256_511_BYTES) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PACKET_4096_8191_BYTES) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PACKET_512_1023_BYTES) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PACKET_64_BYTES) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PACKET_65_127_BYTES) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PACKET_8192_9215_BYTES) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PACKET_BAD_FCS) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PACKET_LARGE) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PACKET_SMALL[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PACKET_SMALL[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PACKET_SMALL[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PACKET_SMALL[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA0[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA0[10]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA0[11]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA0[12]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA0[13]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA0[14]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA0[15]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA0[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA0[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA0[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA0[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA0[5]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA0[6]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA0[7]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA0[8]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA0[9]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA1[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA1[10]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA1[11]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA1[12]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA1[13]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA1[14]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA1[15]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA1[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA1[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA1[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA1[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA1[5]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA1[6]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA1[7]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA1[8]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA1[9]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA2[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA2[10]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA2[11]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA2[12]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA2[13]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA2[14]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA2[15]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA2[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA2[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA2[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA2[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA2[5]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA2[6]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA2[7]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA2[8]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA2[9]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA3[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA3[10]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA3[11]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA3[12]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA3[13]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA3[14]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA3[15]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA3[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA3[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA3[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA3[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA3[5]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA3[6]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA3[7]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA3[8]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA3[9]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA4[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA4[10]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA4[11]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA4[12]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA4[13]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA4[14]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA4[15]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA4[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA4[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA4[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA4[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA4[5]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA4[6]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA4[7]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA4[8]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA4[9]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA5[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA5[10]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA5[11]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA5[12]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA5[13]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA5[14]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA5[15]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA5[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA5[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA5[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA5[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA5[5]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA5[6]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA5[7]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA5[8]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA5[9]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA6[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA6[10]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA6[11]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA6[12]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA6[13]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA6[14]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA6[15]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA6[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA6[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA6[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA6[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA6[5]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA6[6]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA6[7]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA6[8]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA6[9]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA7[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA7[10]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA7[11]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA7[12]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA7[13]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA7[14]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA7[15]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA7[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA7[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA7[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA7[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA7[5]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA7[6]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA7[7]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA7[8]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA7[9]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA8[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA8[10]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA8[11]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA8[12]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA8[13]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA8[14]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA8[15]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA8[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA8[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA8[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA8[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA8[5]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA8[6]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA8[7]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA8[8]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_QUANTA8[9]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_REQ[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_REQ[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_REQ[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_REQ[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_REQ[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_REQ[5]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_REQ[6]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_REQ[7]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_REQ[8]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_VALID[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_VALID[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_VALID[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_VALID[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_VALID[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_VALID[5]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_VALID[6]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_VALID[7]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_PAUSE_VALID[8]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_RECEIVED_LOCAL_FAULT) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_REMOTE_FAULT) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_STATUS) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_STOMPED_FCS[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_STOMPED_FCS[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_STOMPED_FCS[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_STOMPED_FCS[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED[10]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED[11]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED[12]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED[13]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED[14]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED[15]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED[16]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED[17]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED[18]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED[19]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED[5]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED[6]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED[7]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED[8]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED[9]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED_ERR[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED_ERR[10]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED_ERR[11]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED_ERR[12]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED_ERR[13]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED_ERR[14]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED_ERR[15]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED_ERR[16]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED_ERR[17]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED_ERR[18]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED_ERR[19]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED_ERR[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED_ERR[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED_ERR[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED_ERR[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED_ERR[5]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED_ERR[6]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED_ERR[7]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED_ERR[8]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_SYNCED_ERR[9]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TEST_PATTERN_MISMATCH[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TEST_PATTERN_MISMATCH[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TEST_PATTERN_MISMATCH[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TOOLONG) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TOTAL_BYTES[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TOTAL_BYTES[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TOTAL_BYTES[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TOTAL_BYTES[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TOTAL_BYTES[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TOTAL_BYTES[5]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TOTAL_BYTES[6]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TOTAL_BYTES[7]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TOTAL_GOOD_BYTES[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TOTAL_GOOD_BYTES[10]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TOTAL_GOOD_BYTES[11]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TOTAL_GOOD_BYTES[12]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TOTAL_GOOD_BYTES[13]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TOTAL_GOOD_BYTES[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TOTAL_GOOD_BYTES[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TOTAL_GOOD_BYTES[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TOTAL_GOOD_BYTES[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TOTAL_GOOD_BYTES[5]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TOTAL_GOOD_BYTES[6]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TOTAL_GOOD_BYTES[7]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TOTAL_GOOD_BYTES[8]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TOTAL_GOOD_BYTES[9]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TOTAL_GOOD_PACKETS) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TOTAL_PACKETS[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TOTAL_PACKETS[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TOTAL_PACKETS[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TOTAL_PACKETS[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_TRUNCATED) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_UNDERSIZE[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_UNDERSIZE[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_UNDERSIZE[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_UNDERSIZE[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_UNICAST) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_USER_PAUSE) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VLAN) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_DEMUXED[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_DEMUXED[10]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_DEMUXED[11]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_DEMUXED[12]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_DEMUXED[13]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_DEMUXED[14]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_DEMUXED[15]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_DEMUXED[16]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_DEMUXED[17]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_DEMUXED[18]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_DEMUXED[19]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_DEMUXED[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_DEMUXED[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_DEMUXED[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_DEMUXED[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_DEMUXED[5]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_DEMUXED[6]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_DEMUXED[7]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_DEMUXED[8]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_DEMUXED[9]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_0[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_0[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_0[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_0[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_0[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_10[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_10[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_10[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_10[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_10[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_11[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_11[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_11[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_11[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_11[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_12[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_12[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_12[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_12[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_12[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_13[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_13[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_13[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_13[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_13[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_14[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_14[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_14[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_14[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_14[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_15[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_15[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_15[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_15[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_15[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_16[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_16[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_16[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_16[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_16[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_17[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_17[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_17[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_17[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_17[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_18[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_18[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_18[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_18[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_18[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_19[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_19[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_19[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_19[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_19[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_1[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_1[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_1[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_1[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_1[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_2[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_2[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_2[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_2[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_2[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_3[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_3[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_3[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_3[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_3[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_4[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_4[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_4[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_4[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_4[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_5[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_5[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_5[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_5[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_5[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_6[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_6[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_6[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_6[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_6[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_7[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_7[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_7[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_7[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_7[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_8[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_8[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_8[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_8[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_8[4]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_9[0]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_9[1]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_9[2]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_9[3]) = (100:100:100, 100:100:100);
    (RX_CLK => STAT_RX_VL_NUMBER_9[4]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_BAD_FCS) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_BROADCAST) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_FRAME_ERROR) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_LOCAL_FAULT) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_MULTICAST) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_PACKET_1024_1518_BYTES) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_PACKET_128_255_BYTES) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_PACKET_1519_1522_BYTES) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_PACKET_1523_1548_BYTES) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_PACKET_1549_2047_BYTES) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_PACKET_2048_4095_BYTES) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_PACKET_256_511_BYTES) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_PACKET_4096_8191_BYTES) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_PACKET_512_1023_BYTES) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_PACKET_64_BYTES) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_PACKET_65_127_BYTES) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_PACKET_8192_9215_BYTES) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_PACKET_LARGE) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_PACKET_SMALL) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_PAUSE) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_PAUSE_VALID[0]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_PAUSE_VALID[1]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_PAUSE_VALID[2]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_PAUSE_VALID[3]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_PAUSE_VALID[4]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_PAUSE_VALID[5]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_PAUSE_VALID[6]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_PAUSE_VALID[7]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_PAUSE_VALID[8]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_PTP_FIFO_READ_ERROR) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_PTP_FIFO_WRITE_ERROR) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_TOTAL_BYTES[0]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_TOTAL_BYTES[1]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_TOTAL_BYTES[2]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_TOTAL_BYTES[3]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_TOTAL_BYTES[4]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_TOTAL_BYTES[5]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_TOTAL_BYTES[6]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_TOTAL_GOOD_BYTES[0]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_TOTAL_GOOD_BYTES[10]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_TOTAL_GOOD_BYTES[11]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_TOTAL_GOOD_BYTES[12]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_TOTAL_GOOD_BYTES[13]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_TOTAL_GOOD_BYTES[1]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_TOTAL_GOOD_BYTES[2]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_TOTAL_GOOD_BYTES[3]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_TOTAL_GOOD_BYTES[4]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_TOTAL_GOOD_BYTES[5]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_TOTAL_GOOD_BYTES[6]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_TOTAL_GOOD_BYTES[7]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_TOTAL_GOOD_BYTES[8]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_TOTAL_GOOD_BYTES[9]) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_TOTAL_GOOD_PACKETS) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_TOTAL_PACKETS) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_UNICAST) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_USER_PAUSE) = (100:100:100, 100:100:100);
    (TX_CLK => STAT_TX_VLAN) = (100:100:100, 100:100:100);
    (TX_CLK => TX_OVFOUT) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_PCSLANE_OUT[0]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_PCSLANE_OUT[1]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_PCSLANE_OUT[2]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_PCSLANE_OUT[3]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_PCSLANE_OUT[4]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[0]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[10]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[11]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[12]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[13]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[14]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[15]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[16]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[17]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[18]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[19]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[1]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[20]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[21]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[22]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[23]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[24]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[25]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[26]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[27]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[28]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[29]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[2]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[30]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[31]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[32]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[33]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[34]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[35]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[36]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[37]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[38]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[39]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[3]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[40]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[41]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[42]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[43]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[44]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[45]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[46]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[47]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[48]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[49]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[4]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[50]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[51]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[52]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[53]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[54]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[55]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[56]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[57]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[58]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[59]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[5]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[60]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[61]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[62]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[63]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[64]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[65]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[66]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[67]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[68]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[69]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[6]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[70]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[71]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[72]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[73]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[74]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[75]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[76]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[77]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[78]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[79]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[7]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[8]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_OUT[9]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_TAG_OUT[0]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_TAG_OUT[10]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_TAG_OUT[11]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_TAG_OUT[12]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_TAG_OUT[13]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_TAG_OUT[14]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_TAG_OUT[15]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_TAG_OUT[1]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_TAG_OUT[2]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_TAG_OUT[3]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_TAG_OUT[4]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_TAG_OUT[5]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_TAG_OUT[6]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_TAG_OUT[7]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_TAG_OUT[8]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_TAG_OUT[9]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_PTP_TSTAMP_VALID_OUT) = (100:100:100, 100:100:100);
    (TX_CLK => TX_RDYOUT) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA0[0]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA0[10]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA0[11]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA0[12]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA0[13]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA0[14]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA0[15]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA0[1]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA0[2]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA0[3]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA0[4]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA0[5]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA0[6]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA0[7]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA0[8]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA0[9]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA1[0]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA1[10]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA1[11]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA1[12]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA1[13]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA1[14]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA1[15]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA1[1]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA1[2]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA1[3]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA1[4]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA1[5]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA1[6]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA1[7]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA1[8]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA1[9]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA2[0]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA2[10]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA2[11]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA2[12]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA2[13]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA2[14]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA2[15]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA2[1]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA2[2]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA2[3]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA2[4]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA2[5]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA2[6]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA2[7]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA2[8]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA2[9]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA3[0]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA3[10]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA3[11]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA3[12]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA3[13]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA3[14]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA3[15]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA3[1]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA3[2]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA3[3]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA3[4]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA3[5]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA3[6]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA3[7]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA3[8]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_ALT_DATA3[9]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[0]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[10]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[11]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[12]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[13]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[14]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[15]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[16]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[17]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[18]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[19]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[1]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[20]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[21]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[22]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[23]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[24]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[25]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[26]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[27]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[28]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[29]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[2]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[30]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[31]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[32]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[33]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[34]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[35]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[36]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[37]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[38]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[39]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[3]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[40]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[41]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[42]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[43]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[44]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[45]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[46]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[47]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[48]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[49]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[4]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[50]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[51]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[52]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[53]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[54]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[55]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[56]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[57]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[58]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[59]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[5]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[60]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[61]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[62]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[63]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[6]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[7]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[8]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA0[9]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[0]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[10]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[11]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[12]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[13]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[14]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[15]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[16]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[17]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[18]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[19]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[1]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[20]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[21]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[22]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[23]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[24]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[25]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[26]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[27]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[28]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[29]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[2]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[30]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[31]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[32]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[33]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[34]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[35]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[36]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[37]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[38]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[39]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[3]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[40]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[41]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[42]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[43]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[44]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[45]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[46]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[47]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[48]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[49]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[4]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[50]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[51]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[52]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[53]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[54]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[55]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[56]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[57]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[58]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[59]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[5]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[60]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[61]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[62]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[63]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[6]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[7]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[8]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA1[9]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[0]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[10]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[11]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[12]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[13]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[14]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[15]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[16]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[17]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[18]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[19]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[1]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[20]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[21]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[22]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[23]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[24]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[25]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[26]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[27]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[28]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[29]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[2]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[30]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[31]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[32]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[33]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[34]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[35]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[36]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[37]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[38]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[39]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[3]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[40]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[41]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[42]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[43]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[44]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[45]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[46]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[47]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[48]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[49]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[4]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[50]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[51]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[52]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[53]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[54]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[55]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[56]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[57]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[58]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[59]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[5]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[60]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[61]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[62]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[63]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[6]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[7]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[8]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA2[9]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[0]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[10]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[11]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[12]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[13]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[14]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[15]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[16]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[17]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[18]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[19]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[1]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[20]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[21]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[22]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[23]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[24]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[25]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[26]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[27]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[28]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[29]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[2]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[30]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[31]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[32]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[33]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[34]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[35]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[36]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[37]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[38]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[39]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[3]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[40]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[41]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[42]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[43]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[44]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[45]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[46]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[47]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[48]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[49]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[4]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[50]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[51]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[52]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[53]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[54]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[55]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[56]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[57]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[58]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[59]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[5]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[60]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[61]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[62]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[63]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[6]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[7]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[8]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA3[9]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[0]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[10]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[11]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[12]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[13]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[14]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[15]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[16]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[17]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[18]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[19]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[1]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[20]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[21]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[22]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[23]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[24]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[25]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[26]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[27]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[28]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[29]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[2]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[30]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[31]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[3]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[4]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[5]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[6]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[7]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[8]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA4[9]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[0]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[10]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[11]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[12]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[13]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[14]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[15]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[16]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[17]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[18]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[19]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[1]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[20]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[21]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[22]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[23]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[24]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[25]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[26]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[27]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[28]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[29]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[2]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[30]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[31]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[3]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[4]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[5]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[6]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[7]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[8]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA5[9]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[0]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[10]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[11]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[12]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[13]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[14]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[15]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[16]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[17]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[18]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[19]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[1]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[20]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[21]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[22]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[23]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[24]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[25]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[26]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[27]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[28]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[29]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[2]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[30]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[31]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[3]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[4]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[5]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[6]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[7]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[8]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA6[9]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[0]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[10]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[11]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[12]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[13]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[14]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[15]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[16]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[17]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[18]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[19]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[1]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[20]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[21]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[22]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[23]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[24]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[25]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[26]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[27]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[28]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[29]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[2]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[30]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[31]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[3]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[4]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[5]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[6]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[7]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[8]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA7[9]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[0]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[10]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[11]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[12]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[13]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[14]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[15]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[16]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[17]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[18]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[19]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[1]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[20]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[21]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[22]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[23]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[24]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[25]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[26]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[27]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[28]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[29]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[2]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[30]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[31]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[3]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[4]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[5]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[6]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[7]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[8]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA8[9]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[0]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[10]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[11]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[12]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[13]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[14]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[15]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[16]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[17]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[18]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[19]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[1]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[20]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[21]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[22]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[23]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[24]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[25]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[26]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[27]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[28]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[29]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[2]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[30]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[31]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[3]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[4]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[5]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[6]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[7]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[8]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_SERDES_DATA9[9]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_UNFOUT) = (100:100:100, 100:100:100);














































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































    specparam PATHPULSE$ = 0;
  endspecify

endmodule

`endcelldefine
