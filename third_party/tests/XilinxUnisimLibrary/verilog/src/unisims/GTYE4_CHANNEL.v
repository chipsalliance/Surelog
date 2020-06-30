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
// \   \   \/      Version     : 2017.1
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        Gigabit Transceiver for UltraScale+ devices
// /___/   /\      Filename    : GTYE4_CHANNEL.v
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

module GTYE4_CHANNEL #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter [0:0] ACJTAG_DEBUG_MODE = 1'b0,
  parameter [0:0] ACJTAG_MODE = 1'b0,
  parameter [0:0] ACJTAG_RESET = 1'b0,
  parameter [15:0] ADAPT_CFG0 = 16'h9200,
  parameter [15:0] ADAPT_CFG1 = 16'h801C,
  parameter [15:0] ADAPT_CFG2 = 16'h0000,
  parameter ALIGN_COMMA_DOUBLE = "FALSE",
  parameter [9:0] ALIGN_COMMA_ENABLE = 10'b0001111111,
  parameter integer ALIGN_COMMA_WORD = 1,
  parameter ALIGN_MCOMMA_DET = "TRUE",
  parameter [9:0] ALIGN_MCOMMA_VALUE = 10'b1010000011,
  parameter ALIGN_PCOMMA_DET = "TRUE",
  parameter [9:0] ALIGN_PCOMMA_VALUE = 10'b0101111100,
  parameter [0:0] A_RXOSCALRESET = 1'b0,
  parameter [0:0] A_RXPROGDIVRESET = 1'b0,
  parameter [0:0] A_RXTERMINATION = 1'b1,
  parameter [4:0] A_TXDIFFCTRL = 5'b01100,
  parameter [0:0] A_TXPROGDIVRESET = 1'b0,
  parameter CBCC_DATA_SOURCE_SEL = "DECODED",
  parameter [0:0] CDR_SWAP_MODE_EN = 1'b0,
  parameter [0:0] CFOK_PWRSVE_EN = 1'b1,
  parameter CHAN_BOND_KEEP_ALIGN = "FALSE",
  parameter integer CHAN_BOND_MAX_SKEW = 7,
  parameter [9:0] CHAN_BOND_SEQ_1_1 = 10'b0101111100,
  parameter [9:0] CHAN_BOND_SEQ_1_2 = 10'b0000000000,
  parameter [9:0] CHAN_BOND_SEQ_1_3 = 10'b0000000000,
  parameter [9:0] CHAN_BOND_SEQ_1_4 = 10'b0000000000,
  parameter [3:0] CHAN_BOND_SEQ_1_ENABLE = 4'b1111,
  parameter [9:0] CHAN_BOND_SEQ_2_1 = 10'b0100000000,
  parameter [9:0] CHAN_BOND_SEQ_2_2 = 10'b0100000000,
  parameter [9:0] CHAN_BOND_SEQ_2_3 = 10'b0100000000,
  parameter [9:0] CHAN_BOND_SEQ_2_4 = 10'b0100000000,
  parameter [3:0] CHAN_BOND_SEQ_2_ENABLE = 4'b1111,
  parameter CHAN_BOND_SEQ_2_USE = "FALSE",
  parameter integer CHAN_BOND_SEQ_LEN = 2,
  parameter [15:0] CH_HSPMUX = 16'h2424,
  parameter [15:0] CKCAL1_CFG_0 = 16'b1100000011000000,
  parameter [15:0] CKCAL1_CFG_1 = 16'b0101000011000000,
  parameter [15:0] CKCAL1_CFG_2 = 16'b0000000000000000,
  parameter [15:0] CKCAL1_CFG_3 = 16'b0000000000000000,
  parameter [15:0] CKCAL2_CFG_0 = 16'b1100000011000000,
  parameter [15:0] CKCAL2_CFG_1 = 16'b1000000011000000,
  parameter [15:0] CKCAL2_CFG_2 = 16'b0000000000000000,
  parameter [15:0] CKCAL2_CFG_3 = 16'b0000000000000000,
  parameter [15:0] CKCAL2_CFG_4 = 16'b0000000000000000,
  parameter CLK_CORRECT_USE = "TRUE",
  parameter CLK_COR_KEEP_IDLE = "FALSE",
  parameter integer CLK_COR_MAX_LAT = 20,
  parameter integer CLK_COR_MIN_LAT = 18,
  parameter CLK_COR_PRECEDENCE = "TRUE",
  parameter integer CLK_COR_REPEAT_WAIT = 0,
  parameter [9:0] CLK_COR_SEQ_1_1 = 10'b0100011100,
  parameter [9:0] CLK_COR_SEQ_1_2 = 10'b0000000000,
  parameter [9:0] CLK_COR_SEQ_1_3 = 10'b0000000000,
  parameter [9:0] CLK_COR_SEQ_1_4 = 10'b0000000000,
  parameter [3:0] CLK_COR_SEQ_1_ENABLE = 4'b1111,
  parameter [9:0] CLK_COR_SEQ_2_1 = 10'b0100000000,
  parameter [9:0] CLK_COR_SEQ_2_2 = 10'b0100000000,
  parameter [9:0] CLK_COR_SEQ_2_3 = 10'b0100000000,
  parameter [9:0] CLK_COR_SEQ_2_4 = 10'b0100000000,
  parameter [3:0] CLK_COR_SEQ_2_ENABLE = 4'b1111,
  parameter CLK_COR_SEQ_2_USE = "FALSE",
  parameter integer CLK_COR_SEQ_LEN = 2,
  parameter [15:0] CPLL_CFG0 = 16'h01FA,
  parameter [15:0] CPLL_CFG1 = 16'h24A9,
  parameter [15:0] CPLL_CFG2 = 16'h6807,
  parameter [15:0] CPLL_CFG3 = 16'h0000,
  parameter integer CPLL_FBDIV = 4,
  parameter integer CPLL_FBDIV_45 = 4,
  parameter [15:0] CPLL_INIT_CFG0 = 16'h001E,
  parameter [15:0] CPLL_LOCK_CFG = 16'h01E8,
  parameter integer CPLL_REFCLK_DIV = 1,
  parameter [2:0] CTLE3_OCAP_EXT_CTRL = 3'b000,
  parameter [0:0] CTLE3_OCAP_EXT_EN = 1'b0,
  parameter [1:0] DDI_CTRL = 2'b00,
  parameter integer DDI_REALIGN_WAIT = 15,
  parameter DEC_MCOMMA_DETECT = "TRUE",
  parameter DEC_PCOMMA_DETECT = "TRUE",
  parameter DEC_VALID_COMMA_ONLY = "TRUE",
  parameter [0:0] DELAY_ELEC = 1'b0,
  parameter [9:0] DMONITOR_CFG0 = 10'h000,
  parameter [7:0] DMONITOR_CFG1 = 8'h00,
  parameter [0:0] ES_CLK_PHASE_SEL = 1'b0,
  parameter [5:0] ES_CONTROL = 6'b000000,
  parameter ES_ERRDET_EN = "FALSE",
  parameter ES_EYE_SCAN_EN = "FALSE",
  parameter [11:0] ES_HORZ_OFFSET = 12'h800,
  parameter [4:0] ES_PRESCALE = 5'b00000,
  parameter [15:0] ES_QUALIFIER0 = 16'h0000,
  parameter [15:0] ES_QUALIFIER1 = 16'h0000,
  parameter [15:0] ES_QUALIFIER2 = 16'h0000,
  parameter [15:0] ES_QUALIFIER3 = 16'h0000,
  parameter [15:0] ES_QUALIFIER4 = 16'h0000,
  parameter [15:0] ES_QUALIFIER5 = 16'h0000,
  parameter [15:0] ES_QUALIFIER6 = 16'h0000,
  parameter [15:0] ES_QUALIFIER7 = 16'h0000,
  parameter [15:0] ES_QUALIFIER8 = 16'h0000,
  parameter [15:0] ES_QUALIFIER9 = 16'h0000,
  parameter [15:0] ES_QUAL_MASK0 = 16'h0000,
  parameter [15:0] ES_QUAL_MASK1 = 16'h0000,
  parameter [15:0] ES_QUAL_MASK2 = 16'h0000,
  parameter [15:0] ES_QUAL_MASK3 = 16'h0000,
  parameter [15:0] ES_QUAL_MASK4 = 16'h0000,
  parameter [15:0] ES_QUAL_MASK5 = 16'h0000,
  parameter [15:0] ES_QUAL_MASK6 = 16'h0000,
  parameter [15:0] ES_QUAL_MASK7 = 16'h0000,
  parameter [15:0] ES_QUAL_MASK8 = 16'h0000,
  parameter [15:0] ES_QUAL_MASK9 = 16'h0000,
  parameter [15:0] ES_SDATA_MASK0 = 16'h0000,
  parameter [15:0] ES_SDATA_MASK1 = 16'h0000,
  parameter [15:0] ES_SDATA_MASK2 = 16'h0000,
  parameter [15:0] ES_SDATA_MASK3 = 16'h0000,
  parameter [15:0] ES_SDATA_MASK4 = 16'h0000,
  parameter [15:0] ES_SDATA_MASK5 = 16'h0000,
  parameter [15:0] ES_SDATA_MASK6 = 16'h0000,
  parameter [15:0] ES_SDATA_MASK7 = 16'h0000,
  parameter [15:0] ES_SDATA_MASK8 = 16'h0000,
  parameter [15:0] ES_SDATA_MASK9 = 16'h0000,
  parameter integer EYESCAN_VP_RANGE = 0,
  parameter [0:0] EYE_SCAN_SWAP_EN = 1'b0,
  parameter [3:0] FTS_DESKEW_SEQ_ENABLE = 4'b1111,
  parameter [3:0] FTS_LANE_DESKEW_CFG = 4'b1111,
  parameter FTS_LANE_DESKEW_EN = "FALSE",
  parameter [4:0] GEARBOX_MODE = 5'b00000,
  parameter [0:0] ISCAN_CK_PH_SEL2 = 1'b0,
  parameter [0:0] LOCAL_MASTER = 1'b0,
  parameter integer LPBK_BIAS_CTRL = 4,
  parameter [0:0] LPBK_EN_RCAL_B = 1'b0,
  parameter [3:0] LPBK_EXT_RCAL = 4'b0000,
  parameter integer LPBK_IND_CTRL0 = 5,
  parameter integer LPBK_IND_CTRL1 = 5,
  parameter integer LPBK_IND_CTRL2 = 5,
  parameter integer LPBK_RG_CTRL = 2,
  parameter [1:0] OOBDIVCTL = 2'b00,
  parameter [0:0] OOB_PWRUP = 1'b0,
  parameter PCI3_AUTO_REALIGN = "FRST_SMPL",
  parameter [0:0] PCI3_PIPE_RX_ELECIDLE = 1'b1,
  parameter [1:0] PCI3_RX_ASYNC_EBUF_BYPASS = 2'b00,
  parameter [0:0] PCI3_RX_ELECIDLE_EI2_ENABLE = 1'b0,
  parameter [5:0] PCI3_RX_ELECIDLE_H2L_COUNT = 6'b000000,
  parameter [2:0] PCI3_RX_ELECIDLE_H2L_DISABLE = 3'b000,
  parameter [5:0] PCI3_RX_ELECIDLE_HI_COUNT = 6'b000000,
  parameter [0:0] PCI3_RX_ELECIDLE_LP4_DISABLE = 1'b0,
  parameter [0:0] PCI3_RX_FIFO_DISABLE = 1'b0,
  parameter [4:0] PCIE3_CLK_COR_EMPTY_THRSH = 5'b00000,
  parameter [5:0] PCIE3_CLK_COR_FULL_THRSH = 6'b010000,
  parameter [4:0] PCIE3_CLK_COR_MAX_LAT = 5'b01000,
  parameter [4:0] PCIE3_CLK_COR_MIN_LAT = 5'b00100,
  parameter [5:0] PCIE3_CLK_COR_THRSH_TIMER = 6'b001000,
  parameter PCIE_64B_DYN_CLKSW_DIS = "FALSE",
  parameter [15:0] PCIE_BUFG_DIV_CTRL = 16'h0000,
  parameter PCIE_GEN4_64BIT_INT_EN = "FALSE",
  parameter [1:0] PCIE_PLL_SEL_MODE_GEN12 = 2'h0,
  parameter [1:0] PCIE_PLL_SEL_MODE_GEN3 = 2'h0,
  parameter [1:0] PCIE_PLL_SEL_MODE_GEN4 = 2'h0,
  parameter [15:0] PCIE_RXPCS_CFG_GEN3 = 16'h0000,
  parameter [15:0] PCIE_RXPMA_CFG = 16'h0000,
  parameter [15:0] PCIE_TXPCS_CFG_GEN3 = 16'h0000,
  parameter [15:0] PCIE_TXPMA_CFG = 16'h0000,
  parameter PCS_PCIE_EN = "FALSE",
  parameter [15:0] PCS_RSVD0 = 16'h0000,
  parameter [11:0] PD_TRANS_TIME_FROM_P2 = 12'h03C,
  parameter [7:0] PD_TRANS_TIME_NONE_P2 = 8'h19,
  parameter [7:0] PD_TRANS_TIME_TO_P2 = 8'h64,
  parameter integer PREIQ_FREQ_BST = 0,
  parameter [0:0] RATE_SW_USE_DRP = 1'b0,
  parameter [0:0] RCLK_SIPO_DLY_ENB = 1'b0,
  parameter [0:0] RCLK_SIPO_INV_EN = 1'b0,
  parameter [2:0] RTX_BUF_CML_CTRL = 3'b010,
  parameter [1:0] RTX_BUF_TERM_CTRL = 2'b00,
  parameter [4:0] RXBUFRESET_TIME = 5'b00001,
  parameter RXBUF_ADDR_MODE = "FULL",
  parameter [3:0] RXBUF_EIDLE_HI_CNT = 4'b1000,
  parameter [3:0] RXBUF_EIDLE_LO_CNT = 4'b0000,
  parameter RXBUF_EN = "TRUE",
  parameter RXBUF_RESET_ON_CB_CHANGE = "TRUE",
  parameter RXBUF_RESET_ON_COMMAALIGN = "FALSE",
  parameter RXBUF_RESET_ON_EIDLE = "FALSE",
  parameter RXBUF_RESET_ON_RATE_CHANGE = "TRUE",
  parameter integer RXBUF_THRESH_OVFLW = 0,
  parameter RXBUF_THRESH_OVRD = "FALSE",
  parameter integer RXBUF_THRESH_UNDFLW = 4,
  parameter [4:0] RXCDRFREQRESET_TIME = 5'b10000,
  parameter [4:0] RXCDRPHRESET_TIME = 5'b00001,
  parameter [15:0] RXCDR_CFG0 = 16'h0003,
  parameter [15:0] RXCDR_CFG0_GEN3 = 16'h0003,
  parameter [15:0] RXCDR_CFG1 = 16'h0000,
  parameter [15:0] RXCDR_CFG1_GEN3 = 16'h0000,
  parameter [15:0] RXCDR_CFG2 = 16'h0164,
  parameter [9:0] RXCDR_CFG2_GEN2 = 10'h164,
  parameter [15:0] RXCDR_CFG2_GEN3 = 16'h0034,
  parameter [15:0] RXCDR_CFG2_GEN4 = 16'h0034,
  parameter [15:0] RXCDR_CFG3 = 16'h0024,
  parameter [5:0] RXCDR_CFG3_GEN2 = 6'h24,
  parameter [15:0] RXCDR_CFG3_GEN3 = 16'h0024,
  parameter [15:0] RXCDR_CFG3_GEN4 = 16'h0024,
  parameter [15:0] RXCDR_CFG4 = 16'h5CF6,
  parameter [15:0] RXCDR_CFG4_GEN3 = 16'h5CF6,
  parameter [15:0] RXCDR_CFG5 = 16'hB46B,
  parameter [15:0] RXCDR_CFG5_GEN3 = 16'h146B,
  parameter [0:0] RXCDR_FR_RESET_ON_EIDLE = 1'b0,
  parameter [0:0] RXCDR_HOLD_DURING_EIDLE = 1'b0,
  parameter [15:0] RXCDR_LOCK_CFG0 = 16'h0040,
  parameter [15:0] RXCDR_LOCK_CFG1 = 16'h8000,
  parameter [15:0] RXCDR_LOCK_CFG2 = 16'h0000,
  parameter [15:0] RXCDR_LOCK_CFG3 = 16'h0000,
  parameter [15:0] RXCDR_LOCK_CFG4 = 16'h0000,
  parameter [0:0] RXCDR_PH_RESET_ON_EIDLE = 1'b0,
  parameter [15:0] RXCFOK_CFG0 = 16'h0000,
  parameter [15:0] RXCFOK_CFG1 = 16'h0002,
  parameter [15:0] RXCFOK_CFG2 = 16'h002D,
  parameter [15:0] RXCKCAL1_IQ_LOOP_RST_CFG = 16'h0000,
  parameter [15:0] RXCKCAL1_I_LOOP_RST_CFG = 16'h0000,
  parameter [15:0] RXCKCAL1_Q_LOOP_RST_CFG = 16'h0000,
  parameter [15:0] RXCKCAL2_DX_LOOP_RST_CFG = 16'h0000,
  parameter [15:0] RXCKCAL2_D_LOOP_RST_CFG = 16'h0000,
  parameter [15:0] RXCKCAL2_S_LOOP_RST_CFG = 16'h0000,
  parameter [15:0] RXCKCAL2_X_LOOP_RST_CFG = 16'h0000,
  parameter [6:0] RXDFELPMRESET_TIME = 7'b0001111,
  parameter [15:0] RXDFELPM_KL_CFG0 = 16'h0000,
  parameter [15:0] RXDFELPM_KL_CFG1 = 16'h0022,
  parameter [15:0] RXDFELPM_KL_CFG2 = 16'h0100,
  parameter [15:0] RXDFE_CFG0 = 16'h4000,
  parameter [15:0] RXDFE_CFG1 = 16'h0000,
  parameter [15:0] RXDFE_GC_CFG0 = 16'h0000,
  parameter [15:0] RXDFE_GC_CFG1 = 16'h0000,
  parameter [15:0] RXDFE_GC_CFG2 = 16'h0000,
  parameter [15:0] RXDFE_H2_CFG0 = 16'h0000,
  parameter [15:0] RXDFE_H2_CFG1 = 16'h0002,
  parameter [15:0] RXDFE_H3_CFG0 = 16'h0000,
  parameter [15:0] RXDFE_H3_CFG1 = 16'h0002,
  parameter [15:0] RXDFE_H4_CFG0 = 16'h0000,
  parameter [15:0] RXDFE_H4_CFG1 = 16'h0003,
  parameter [15:0] RXDFE_H5_CFG0 = 16'h0000,
  parameter [15:0] RXDFE_H5_CFG1 = 16'h0002,
  parameter [15:0] RXDFE_H6_CFG0 = 16'h0000,
  parameter [15:0] RXDFE_H6_CFG1 = 16'h0002,
  parameter [15:0] RXDFE_H7_CFG0 = 16'h0000,
  parameter [15:0] RXDFE_H7_CFG1 = 16'h0002,
  parameter [15:0] RXDFE_H8_CFG0 = 16'h0000,
  parameter [15:0] RXDFE_H8_CFG1 = 16'h0002,
  parameter [15:0] RXDFE_H9_CFG0 = 16'h0000,
  parameter [15:0] RXDFE_H9_CFG1 = 16'h0002,
  parameter [15:0] RXDFE_HA_CFG0 = 16'h0000,
  parameter [15:0] RXDFE_HA_CFG1 = 16'h0002,
  parameter [15:0] RXDFE_HB_CFG0 = 16'h0000,
  parameter [15:0] RXDFE_HB_CFG1 = 16'h0002,
  parameter [15:0] RXDFE_HC_CFG0 = 16'h0000,
  parameter [15:0] RXDFE_HC_CFG1 = 16'h0002,
  parameter [15:0] RXDFE_HD_CFG0 = 16'h0000,
  parameter [15:0] RXDFE_HD_CFG1 = 16'h0002,
  parameter [15:0] RXDFE_HE_CFG0 = 16'h0000,
  parameter [15:0] RXDFE_HE_CFG1 = 16'h0002,
  parameter [15:0] RXDFE_HF_CFG0 = 16'h0000,
  parameter [15:0] RXDFE_HF_CFG1 = 16'h0002,
  parameter [15:0] RXDFE_KH_CFG0 = 16'h0000,
  parameter [15:0] RXDFE_KH_CFG1 = 16'h0000,
  parameter [15:0] RXDFE_KH_CFG2 = 16'h0000,
  parameter [15:0] RXDFE_KH_CFG3 = 16'h2000,
  parameter [15:0] RXDFE_OS_CFG0 = 16'h0000,
  parameter [15:0] RXDFE_OS_CFG1 = 16'h0000,
  parameter [15:0] RXDFE_UT_CFG0 = 16'h0000,
  parameter [15:0] RXDFE_UT_CFG1 = 16'h0002,
  parameter [15:0] RXDFE_UT_CFG2 = 16'h0000,
  parameter [15:0] RXDFE_VP_CFG0 = 16'h0000,
  parameter [15:0] RXDFE_VP_CFG1 = 16'h0022,
  parameter [15:0] RXDLY_CFG = 16'h0010,
  parameter [15:0] RXDLY_LCFG = 16'h0030,
  parameter RXELECIDLE_CFG = "SIGCFG_4",
  parameter integer RXGBOX_FIFO_INIT_RD_ADDR = 4,
  parameter RXGEARBOX_EN = "FALSE",
  parameter [4:0] RXISCANRESET_TIME = 5'b00001,
  parameter [15:0] RXLPM_CFG = 16'h0000,
  parameter [15:0] RXLPM_GC_CFG = 16'h1000,
  parameter [15:0] RXLPM_KH_CFG0 = 16'h0000,
  parameter [15:0] RXLPM_KH_CFG1 = 16'h0002,
  parameter [15:0] RXLPM_OS_CFG0 = 16'h0000,
  parameter [15:0] RXLPM_OS_CFG1 = 16'h0000,
  parameter [8:0] RXOOB_CFG = 9'b000110000,
  parameter RXOOB_CLK_CFG = "PMA",
  parameter [4:0] RXOSCALRESET_TIME = 5'b00011,
  parameter integer RXOUT_DIV = 4,
  parameter [4:0] RXPCSRESET_TIME = 5'b00001,
  parameter [15:0] RXPHBEACON_CFG = 16'h0000,
  parameter [15:0] RXPHDLY_CFG = 16'h2020,
  parameter [15:0] RXPHSAMP_CFG = 16'h2100,
  parameter [15:0] RXPHSLIP_CFG = 16'h9933,
  parameter [4:0] RXPH_MONITOR_SEL = 5'b00000,
  parameter [15:0] RXPI_CFG0 = 16'h0102,
  parameter [15:0] RXPI_CFG1 = 16'b0000000001010100,
  parameter RXPMACLK_SEL = "DATA",
  parameter [4:0] RXPMARESET_TIME = 5'b00001,
  parameter [0:0] RXPRBS_ERR_LOOPBACK = 1'b0,
  parameter integer RXPRBS_LINKACQ_CNT = 15,
  parameter [0:0] RXREFCLKDIV2_SEL = 1'b0,
  parameter integer RXSLIDE_AUTO_WAIT = 7,
  parameter RXSLIDE_MODE = "OFF",
  parameter [0:0] RXSYNC_MULTILANE = 1'b0,
  parameter [0:0] RXSYNC_OVRD = 1'b0,
  parameter [0:0] RXSYNC_SKIP_DA = 1'b0,
  parameter [0:0] RX_AFE_CM_EN = 1'b0,
  parameter [15:0] RX_BIAS_CFG0 = 16'h12B0,
  parameter [5:0] RX_BUFFER_CFG = 6'b000000,
  parameter [0:0] RX_CAPFF_SARC_ENB = 1'b0,
  parameter integer RX_CLK25_DIV = 8,
  parameter [0:0] RX_CLKMUX_EN = 1'b1,
  parameter [4:0] RX_CLK_SLIP_OVRD = 5'b00000,
  parameter [3:0] RX_CM_BUF_CFG = 4'b1010,
  parameter [0:0] RX_CM_BUF_PD = 1'b0,
  parameter integer RX_CM_SEL = 2,
  parameter integer RX_CM_TRIM = 12,
  parameter [0:0] RX_CTLE_PWR_SAVING = 1'b0,
  parameter [3:0] RX_CTLE_RES_CTRL = 4'b0000,
  parameter integer RX_DATA_WIDTH = 20,
  parameter [5:0] RX_DDI_SEL = 6'b000000,
  parameter RX_DEFER_RESET_BUF_EN = "TRUE",
  parameter [2:0] RX_DEGEN_CTRL = 3'b100,
  parameter integer RX_DFELPM_CFG0 = 10,
  parameter [0:0] RX_DFELPM_CFG1 = 1'b1,
  parameter [0:0] RX_DFELPM_KLKH_AGC_STUP_EN = 1'b1,
  parameter integer RX_DFE_AGC_CFG1 = 4,
  parameter integer RX_DFE_KL_LPM_KH_CFG0 = 1,
  parameter integer RX_DFE_KL_LPM_KH_CFG1 = 2,
  parameter [1:0] RX_DFE_KL_LPM_KL_CFG0 = 2'b01,
  parameter integer RX_DFE_KL_LPM_KL_CFG1 = 4,
  parameter [0:0] RX_DFE_LPM_HOLD_DURING_EIDLE = 1'b0,
  parameter RX_DISPERR_SEQ_MATCH = "TRUE",
  parameter [4:0] RX_DIVRESET_TIME = 5'b00001,
  parameter [0:0] RX_EN_CTLE_RCAL_B = 1'b0,
  parameter integer RX_EN_SUM_RCAL_B = 0,
  parameter [6:0] RX_EYESCAN_VS_CODE = 7'b0000000,
  parameter [0:0] RX_EYESCAN_VS_NEG_DIR = 1'b0,
  parameter [1:0] RX_EYESCAN_VS_RANGE = 2'b10,
  parameter [0:0] RX_EYESCAN_VS_UT_SIGN = 1'b0,
  parameter [0:0] RX_FABINT_USRCLK_FLOP = 1'b0,
  parameter [0:0] RX_I2V_FILTER_EN = 1'b1,
  parameter integer RX_INT_DATAWIDTH = 1,
  parameter [0:0] RX_PMA_POWER_SAVE = 1'b0,
  parameter [15:0] RX_PMA_RSV0 = 16'h002F,
  parameter real RX_PROGDIV_CFG = 0.0,
  parameter [15:0] RX_PROGDIV_RATE = 16'h0001,
  parameter [3:0] RX_RESLOAD_CTRL = 4'b0000,
  parameter [0:0] RX_RESLOAD_OVRD = 1'b0,
  parameter [2:0] RX_SAMPLE_PERIOD = 3'b101,
  parameter integer RX_SIG_VALID_DLY = 11,
  parameter integer RX_SUM_DEGEN_AVTT_OVERITE = 0,
  parameter [0:0] RX_SUM_DFETAPREP_EN = 1'b0,
  parameter [3:0] RX_SUM_IREF_TUNE = 4'b0000,
  parameter integer RX_SUM_PWR_SAVING = 0,
  parameter [3:0] RX_SUM_RES_CTRL = 4'b0000,
  parameter [3:0] RX_SUM_VCMTUNE = 4'b0011,
  parameter [0:0] RX_SUM_VCM_BIAS_TUNE_EN = 1'b1,
  parameter [0:0] RX_SUM_VCM_OVWR = 1'b0,
  parameter [2:0] RX_SUM_VREF_TUNE = 3'b100,
  parameter [1:0] RX_TUNE_AFE_OS = 2'b00,
  parameter [2:0] RX_VREG_CTRL = 3'b010,
  parameter [0:0] RX_VREG_PDB = 1'b1,
  parameter [1:0] RX_WIDEMODE_CDR = 2'b01,
  parameter [1:0] RX_WIDEMODE_CDR_GEN3 = 2'b01,
  parameter [1:0] RX_WIDEMODE_CDR_GEN4 = 2'b01,
  parameter RX_XCLK_SEL = "RXDES",
  parameter [0:0] RX_XMODE_SEL = 1'b0,
  parameter [0:0] SAMPLE_CLK_PHASE = 1'b0,
  parameter [0:0] SAS_12G_MODE = 1'b0,
  parameter [3:0] SATA_BURST_SEQ_LEN = 4'b1111,
  parameter [2:0] SATA_BURST_VAL = 3'b100,
  parameter SATA_CPLL_CFG = "VCO_3000MHZ",
  parameter [2:0] SATA_EIDLE_VAL = 3'b100,
  parameter SHOW_REALIGN_COMMA = "TRUE",
  parameter SIM_DEVICE = "ULTRASCALE_PLUS",
  parameter SIM_MODE = "FAST",
  parameter SIM_RECEIVER_DETECT_PASS = "TRUE",
  parameter SIM_RESET_SPEEDUP = "TRUE",
  parameter SIM_TX_EIDLE_DRIVE_LEVEL = "Z",
  parameter [0:0] SRSTMODE = 1'b0,
  parameter [1:0] TAPDLY_SET_TX = 2'h0,
  parameter [14:0] TERM_RCAL_CFG = 15'b100001000010000,
  parameter [2:0] TERM_RCAL_OVRD = 3'b000,
  parameter [7:0] TRANS_TIME_RATE = 8'h0E,
  parameter [7:0] TST_RSV0 = 8'h00,
  parameter [7:0] TST_RSV1 = 8'h00,
  parameter TXBUF_EN = "TRUE",
  parameter TXBUF_RESET_ON_RATE_CHANGE = "FALSE",
  parameter [15:0] TXDLY_CFG = 16'h0010,
  parameter [15:0] TXDLY_LCFG = 16'h0030,
  parameter integer TXDRV_FREQBAND = 0,
  parameter [15:0] TXFE_CFG0 = 16'b0000000000000000,
  parameter [15:0] TXFE_CFG1 = 16'b0000000000000000,
  parameter [15:0] TXFE_CFG2 = 16'b0000000000000000,
  parameter [15:0] TXFE_CFG3 = 16'b0000000000000000,
  parameter TXFIFO_ADDR_CFG = "LOW",
  parameter integer TXGBOX_FIFO_INIT_RD_ADDR = 4,
  parameter TXGEARBOX_EN = "FALSE",
  parameter integer TXOUT_DIV = 4,
  parameter [4:0] TXPCSRESET_TIME = 5'b00001,
  parameter [15:0] TXPHDLY_CFG0 = 16'h6020,
  parameter [15:0] TXPHDLY_CFG1 = 16'h0002,
  parameter [15:0] TXPH_CFG = 16'h0123,
  parameter [15:0] TXPH_CFG2 = 16'h0000,
  parameter [4:0] TXPH_MONITOR_SEL = 5'b00000,
  parameter [15:0] TXPI_CFG0 = 16'b0000000100000000,
  parameter [15:0] TXPI_CFG1 = 16'b0000000000000000,
  parameter [0:0] TXPI_GRAY_SEL = 1'b0,
  parameter [0:0] TXPI_INVSTROBE_SEL = 1'b0,
  parameter [0:0] TXPI_PPM = 1'b0,
  parameter [7:0] TXPI_PPM_CFG = 8'b00000000,
  parameter [2:0] TXPI_SYNFREQ_PPM = 3'b000,
  parameter [4:0] TXPMARESET_TIME = 5'b00001,
  parameter [0:0] TXREFCLKDIV2_SEL = 1'b0,
  parameter integer TXSWBST_BST = 1,
  parameter integer TXSWBST_EN = 0,
  parameter integer TXSWBST_MAG = 6,
  parameter [0:0] TXSYNC_MULTILANE = 1'b0,
  parameter [0:0] TXSYNC_OVRD = 1'b0,
  parameter [0:0] TXSYNC_SKIP_DA = 1'b0,
  parameter integer TX_CLK25_DIV = 8,
  parameter [0:0] TX_CLKMUX_EN = 1'b1,
  parameter integer TX_DATA_WIDTH = 20,
  parameter [15:0] TX_DCC_LOOP_RST_CFG = 16'h0000,
  parameter [5:0] TX_DEEMPH0 = 6'b000000,
  parameter [5:0] TX_DEEMPH1 = 6'b000000,
  parameter [5:0] TX_DEEMPH2 = 6'b000000,
  parameter [5:0] TX_DEEMPH3 = 6'b000000,
  parameter [4:0] TX_DIVRESET_TIME = 5'b00001,
  parameter TX_DRIVE_MODE = "DIRECT",
  parameter [2:0] TX_EIDLE_ASSERT_DELAY = 3'b110,
  parameter [2:0] TX_EIDLE_DEASSERT_DELAY = 3'b100,
  parameter [0:0] TX_FABINT_USRCLK_FLOP = 1'b0,
  parameter [0:0] TX_FIFO_BYP_EN = 1'b0,
  parameter [0:0] TX_IDLE_DATA_ZERO = 1'b0,
  parameter integer TX_INT_DATAWIDTH = 1,
  parameter TX_LOOPBACK_DRIVE_HIZ = "FALSE",
  parameter [0:0] TX_MAINCURSOR_SEL = 1'b0,
  parameter [6:0] TX_MARGIN_FULL_0 = 7'b1001110,
  parameter [6:0] TX_MARGIN_FULL_1 = 7'b1001001,
  parameter [6:0] TX_MARGIN_FULL_2 = 7'b1000101,
  parameter [6:0] TX_MARGIN_FULL_3 = 7'b1000010,
  parameter [6:0] TX_MARGIN_FULL_4 = 7'b1000000,
  parameter [6:0] TX_MARGIN_LOW_0 = 7'b1000110,
  parameter [6:0] TX_MARGIN_LOW_1 = 7'b1000100,
  parameter [6:0] TX_MARGIN_LOW_2 = 7'b1000010,
  parameter [6:0] TX_MARGIN_LOW_3 = 7'b1000000,
  parameter [6:0] TX_MARGIN_LOW_4 = 7'b1000000,
  parameter [15:0] TX_PHICAL_CFG0 = 16'h0000,
  parameter [15:0] TX_PHICAL_CFG1 = 16'h003F,
  parameter integer TX_PI_BIASSET = 0,
  parameter [0:0] TX_PMADATA_OPT = 1'b0,
  parameter [0:0] TX_PMA_POWER_SAVE = 1'b0,
  parameter [15:0] TX_PMA_RSV0 = 16'h0000,
  parameter [15:0] TX_PMA_RSV1 = 16'h0000,
  parameter TX_PROGCLK_SEL = "POSTPI",
  parameter real TX_PROGDIV_CFG = 0.0,
  parameter [15:0] TX_PROGDIV_RATE = 16'h0001,
  parameter [13:0] TX_RXDETECT_CFG = 14'h0032,
  parameter integer TX_RXDETECT_REF = 3,
  parameter [2:0] TX_SAMPLE_PERIOD = 3'b101,
  parameter [1:0] TX_SW_MEAS = 2'b00,
  parameter [2:0] TX_VREG_CTRL = 3'b000,
  parameter [0:0] TX_VREG_PDB = 1'b0,
  parameter [1:0] TX_VREG_VREFSEL = 2'b00,
  parameter TX_XCLK_SEL = "TXOUT",
  parameter [0:0] USB_BOTH_BURST_IDLE = 1'b0,
  parameter [6:0] USB_BURSTMAX_U3WAKE = 7'b1111111,
  parameter [6:0] USB_BURSTMIN_U3WAKE = 7'b1100011,
  parameter [0:0] USB_CLK_COR_EQ_EN = 1'b0,
  parameter [0:0] USB_EXT_CNTL = 1'b1,
  parameter [9:0] USB_IDLEMAX_POLLING = 10'b1010111011,
  parameter [9:0] USB_IDLEMIN_POLLING = 10'b0100101011,
  parameter [8:0] USB_LFPSPING_BURST = 9'b000000101,
  parameter [8:0] USB_LFPSPOLLING_BURST = 9'b000110001,
  parameter [8:0] USB_LFPSPOLLING_IDLE_MS = 9'b000000100,
  parameter [8:0] USB_LFPSU1EXIT_BURST = 9'b000011101,
  parameter [8:0] USB_LFPSU2LPEXIT_BURST_MS = 9'b001100011,
  parameter [8:0] USB_LFPSU3WAKE_BURST_MS = 9'b111110011,
  parameter [3:0] USB_LFPS_TPERIOD = 4'b0011,
  parameter [0:0] USB_LFPS_TPERIOD_ACCURATE = 1'b1,
  parameter [0:0] USB_MODE = 1'b0,
  parameter [0:0] USB_PCIE_ERR_REP_DIS = 1'b0,
  parameter integer USB_PING_SATA_MAX_INIT = 21,
  parameter integer USB_PING_SATA_MIN_INIT = 12,
  parameter integer USB_POLL_SATA_MAX_BURST = 8,
  parameter integer USB_POLL_SATA_MIN_BURST = 4,
  parameter [0:0] USB_RAW_ELEC = 1'b0,
  parameter [0:0] USB_RXIDLE_P0_CTRL = 1'b1,
  parameter [0:0] USB_TXIDLE_TUNE_ENABLE = 1'b1,
  parameter integer USB_U1_SATA_MAX_WAKE = 7,
  parameter integer USB_U1_SATA_MIN_WAKE = 4,
  parameter integer USB_U2_SAS_MAX_COM = 64,
  parameter integer USB_U2_SAS_MIN_COM = 36,
  parameter [0:0] USE_PCS_CLK_PHASE_SEL = 1'b0,
  parameter [0:0] Y_ALL_MODE = 1'b0
)(
  output BUFGTCE,
  output [2:0] BUFGTCEMASK,
  output [8:0] BUFGTDIV,
  output BUFGTRESET,
  output [2:0] BUFGTRSTMASK,
  output CPLLFBCLKLOST,
  output CPLLLOCK,
  output CPLLREFCLKLOST,
  output [15:0] DMONITOROUT,
  output DMONITOROUTCLK,
  output [15:0] DRPDO,
  output DRPRDY,
  output EYESCANDATAERROR,
  output GTPOWERGOOD,
  output GTREFCLKMONITOR,
  output GTYTXN,
  output GTYTXP,
  output PCIERATEGEN3,
  output PCIERATEIDLE,
  output [1:0] PCIERATEQPLLPD,
  output [1:0] PCIERATEQPLLRESET,
  output PCIESYNCTXSYNCDONE,
  output PCIEUSERGEN3RDY,
  output PCIEUSERPHYSTATUSRST,
  output PCIEUSERRATESTART,
  output [15:0] PCSRSVDOUT,
  output PHYSTATUS,
  output [15:0] PINRSRVDAS,
  output POWERPRESENT,
  output RESETEXCEPTION,
  output [2:0] RXBUFSTATUS,
  output RXBYTEISALIGNED,
  output RXBYTEREALIGN,
  output RXCDRLOCK,
  output RXCDRPHDONE,
  output RXCHANBONDSEQ,
  output RXCHANISALIGNED,
  output RXCHANREALIGN,
  output [4:0] RXCHBONDO,
  output RXCKCALDONE,
  output [1:0] RXCLKCORCNT,
  output RXCOMINITDET,
  output RXCOMMADET,
  output RXCOMSASDET,
  output RXCOMWAKEDET,
  output [15:0] RXCTRL0,
  output [15:0] RXCTRL1,
  output [7:0] RXCTRL2,
  output [7:0] RXCTRL3,
  output [127:0] RXDATA,
  output [7:0] RXDATAEXTENDRSVD,
  output [1:0] RXDATAVALID,
  output RXDLYSRESETDONE,
  output RXELECIDLE,
  output [5:0] RXHEADER,
  output [1:0] RXHEADERVALID,
  output RXLFPSTRESETDET,
  output RXLFPSU2LPEXITDET,
  output RXLFPSU3WAKEDET,
  output [7:0] RXMONITOROUT,
  output RXOSINTDONE,
  output RXOSINTSTARTED,
  output RXOSINTSTROBEDONE,
  output RXOSINTSTROBESTARTED,
  output RXOUTCLK,
  output RXOUTCLKFABRIC,
  output RXOUTCLKPCS,
  output RXPHALIGNDONE,
  output RXPHALIGNERR,
  output RXPMARESETDONE,
  output RXPRBSERR,
  output RXPRBSLOCKED,
  output RXPRGDIVRESETDONE,
  output RXRATEDONE,
  output RXRECCLKOUT,
  output RXRESETDONE,
  output RXSLIDERDY,
  output RXSLIPDONE,
  output RXSLIPOUTCLKRDY,
  output RXSLIPPMARDY,
  output [1:0] RXSTARTOFSEQ,
  output [2:0] RXSTATUS,
  output RXSYNCDONE,
  output RXSYNCOUT,
  output RXVALID,
  output [1:0] TXBUFSTATUS,
  output TXCOMFINISH,
  output TXDCCDONE,
  output TXDLYSRESETDONE,
  output TXOUTCLK,
  output TXOUTCLKFABRIC,
  output TXOUTCLKPCS,
  output TXPHALIGNDONE,
  output TXPHINITDONE,
  output TXPMARESETDONE,
  output TXPRGDIVRESETDONE,
  output TXRATEDONE,
  output TXRESETDONE,
  output TXSYNCDONE,
  output TXSYNCOUT,

  input CDRSTEPDIR,
  input CDRSTEPSQ,
  input CDRSTEPSX,
  input CFGRESET,
  input CLKRSVD0,
  input CLKRSVD1,
  input CPLLFREQLOCK,
  input CPLLLOCKDETCLK,
  input CPLLLOCKEN,
  input CPLLPD,
  input [2:0] CPLLREFCLKSEL,
  input CPLLRESET,
  input DMONFIFORESET,
  input DMONITORCLK,
  input [9:0] DRPADDR,
  input DRPCLK,
  input [15:0] DRPDI,
  input DRPEN,
  input DRPRST,
  input DRPWE,
  input EYESCANRESET,
  input EYESCANTRIGGER,
  input FREQOS,
  input GTGREFCLK,
  input GTNORTHREFCLK0,
  input GTNORTHREFCLK1,
  input GTREFCLK0,
  input GTREFCLK1,
  input [15:0] GTRSVD,
  input GTRXRESET,
  input GTRXRESETSEL,
  input GTSOUTHREFCLK0,
  input GTSOUTHREFCLK1,
  input GTTXRESET,
  input GTTXRESETSEL,
  input GTYRXN,
  input GTYRXP,
  input INCPCTRL,
  input [2:0] LOOPBACK,
  input PCIEEQRXEQADAPTDONE,
  input PCIERSTIDLE,
  input PCIERSTTXSYNCSTART,
  input PCIEUSERRATEDONE,
  input [15:0] PCSRSVDIN,
  input QPLL0CLK,
  input QPLL0FREQLOCK,
  input QPLL0REFCLK,
  input QPLL1CLK,
  input QPLL1FREQLOCK,
  input QPLL1REFCLK,
  input RESETOVRD,
  input RX8B10BEN,
  input RXAFECFOKEN,
  input RXBUFRESET,
  input RXCDRFREQRESET,
  input RXCDRHOLD,
  input RXCDROVRDEN,
  input RXCDRRESET,
  input RXCHBONDEN,
  input [4:0] RXCHBONDI,
  input [2:0] RXCHBONDLEVEL,
  input RXCHBONDMASTER,
  input RXCHBONDSLAVE,
  input RXCKCALRESET,
  input [6:0] RXCKCALSTART,
  input RXCOMMADETEN,
  input RXDFEAGCHOLD,
  input RXDFEAGCOVRDEN,
  input [3:0] RXDFECFOKFCNUM,
  input RXDFECFOKFEN,
  input RXDFECFOKFPULSE,
  input RXDFECFOKHOLD,
  input RXDFECFOKOVREN,
  input RXDFEKHHOLD,
  input RXDFEKHOVRDEN,
  input RXDFELFHOLD,
  input RXDFELFOVRDEN,
  input RXDFELPMRESET,
  input RXDFETAP10HOLD,
  input RXDFETAP10OVRDEN,
  input RXDFETAP11HOLD,
  input RXDFETAP11OVRDEN,
  input RXDFETAP12HOLD,
  input RXDFETAP12OVRDEN,
  input RXDFETAP13HOLD,
  input RXDFETAP13OVRDEN,
  input RXDFETAP14HOLD,
  input RXDFETAP14OVRDEN,
  input RXDFETAP15HOLD,
  input RXDFETAP15OVRDEN,
  input RXDFETAP2HOLD,
  input RXDFETAP2OVRDEN,
  input RXDFETAP3HOLD,
  input RXDFETAP3OVRDEN,
  input RXDFETAP4HOLD,
  input RXDFETAP4OVRDEN,
  input RXDFETAP5HOLD,
  input RXDFETAP5OVRDEN,
  input RXDFETAP6HOLD,
  input RXDFETAP6OVRDEN,
  input RXDFETAP7HOLD,
  input RXDFETAP7OVRDEN,
  input RXDFETAP8HOLD,
  input RXDFETAP8OVRDEN,
  input RXDFETAP9HOLD,
  input RXDFETAP9OVRDEN,
  input RXDFEUTHOLD,
  input RXDFEUTOVRDEN,
  input RXDFEVPHOLD,
  input RXDFEVPOVRDEN,
  input RXDFEXYDEN,
  input RXDLYBYPASS,
  input RXDLYEN,
  input RXDLYOVRDEN,
  input RXDLYSRESET,
  input [1:0] RXELECIDLEMODE,
  input RXEQTRAINING,
  input RXGEARBOXSLIP,
  input RXLATCLK,
  input RXLPMEN,
  input RXLPMGCHOLD,
  input RXLPMGCOVRDEN,
  input RXLPMHFHOLD,
  input RXLPMHFOVRDEN,
  input RXLPMLFHOLD,
  input RXLPMLFKLOVRDEN,
  input RXLPMOSHOLD,
  input RXLPMOSOVRDEN,
  input RXMCOMMAALIGNEN,
  input [1:0] RXMONITORSEL,
  input RXOOBRESET,
  input RXOSCALRESET,
  input RXOSHOLD,
  input RXOSOVRDEN,
  input [2:0] RXOUTCLKSEL,
  input RXPCOMMAALIGNEN,
  input RXPCSRESET,
  input [1:0] RXPD,
  input RXPHALIGN,
  input RXPHALIGNEN,
  input RXPHDLYPD,
  input RXPHDLYRESET,
  input [1:0] RXPLLCLKSEL,
  input RXPMARESET,
  input RXPOLARITY,
  input RXPRBSCNTRESET,
  input [3:0] RXPRBSSEL,
  input RXPROGDIVRESET,
  input [2:0] RXRATE,
  input RXRATEMODE,
  input RXSLIDE,
  input RXSLIPOUTCLK,
  input RXSLIPPMA,
  input RXSYNCALLIN,
  input RXSYNCIN,
  input RXSYNCMODE,
  input [1:0] RXSYSCLKSEL,
  input RXTERMINATION,
  input RXUSERRDY,
  input RXUSRCLK,
  input RXUSRCLK2,
  input SIGVALIDCLK,
  input [19:0] TSTIN,
  input [7:0] TX8B10BBYPASS,
  input TX8B10BEN,
  input TXCOMINIT,
  input TXCOMSAS,
  input TXCOMWAKE,
  input [15:0] TXCTRL0,
  input [15:0] TXCTRL1,
  input [7:0] TXCTRL2,
  input [127:0] TXDATA,
  input [7:0] TXDATAEXTENDRSVD,
  input TXDCCFORCESTART,
  input TXDCCRESET,
  input [1:0] TXDEEMPH,
  input TXDETECTRX,
  input [4:0] TXDIFFCTRL,
  input TXDLYBYPASS,
  input TXDLYEN,
  input TXDLYHOLD,
  input TXDLYOVRDEN,
  input TXDLYSRESET,
  input TXDLYUPDOWN,
  input TXELECIDLE,
  input [5:0] TXHEADER,
  input TXINHIBIT,
  input TXLATCLK,
  input TXLFPSTRESET,
  input TXLFPSU2LPEXIT,
  input TXLFPSU3WAKE,
  input [6:0] TXMAINCURSOR,
  input [2:0] TXMARGIN,
  input TXMUXDCDEXHOLD,
  input TXMUXDCDORWREN,
  input TXONESZEROS,
  input [2:0] TXOUTCLKSEL,
  input TXPCSRESET,
  input [1:0] TXPD,
  input TXPDELECIDLEMODE,
  input TXPHALIGN,
  input TXPHALIGNEN,
  input TXPHDLYPD,
  input TXPHDLYRESET,
  input TXPHDLYTSTCLK,
  input TXPHINIT,
  input TXPHOVRDEN,
  input TXPIPPMEN,
  input TXPIPPMOVRDEN,
  input TXPIPPMPD,
  input TXPIPPMSEL,
  input [4:0] TXPIPPMSTEPSIZE,
  input TXPISOPD,
  input [1:0] TXPLLCLKSEL,
  input TXPMARESET,
  input TXPOLARITY,
  input [4:0] TXPOSTCURSOR,
  input TXPRBSFORCEERR,
  input [3:0] TXPRBSSEL,
  input [4:0] TXPRECURSOR,
  input TXPROGDIVRESET,
  input [2:0] TXRATE,
  input TXRATEMODE,
  input [6:0] TXSEQUENCE,
  input TXSWING,
  input TXSYNCALLIN,
  input TXSYNCIN,
  input TXSYNCMODE,
  input [1:0] TXSYSCLKSEL,
  input TXUSERRDY,
  input TXUSRCLK,
  input TXUSRCLK2
);

// define constants
  localparam MODULE_NAME = "GTYE4_CHANNEL";
  
  reg trig_attr = 1'b0;
// include dynamic registers - XILINX test only
`ifdef XIL_DR
  `include "GTYE4_CHANNEL_dr.v"
`else
  reg [0:0] ACJTAG_DEBUG_MODE_REG = ACJTAG_DEBUG_MODE;
  reg [0:0] ACJTAG_MODE_REG = ACJTAG_MODE;
  reg [0:0] ACJTAG_RESET_REG = ACJTAG_RESET;
  reg [15:0] ADAPT_CFG0_REG = ADAPT_CFG0;
  reg [15:0] ADAPT_CFG1_REG = ADAPT_CFG1;
  reg [15:0] ADAPT_CFG2_REG = ADAPT_CFG2;
  reg [40:1] ALIGN_COMMA_DOUBLE_REG = ALIGN_COMMA_DOUBLE;
  reg [9:0] ALIGN_COMMA_ENABLE_REG = ALIGN_COMMA_ENABLE;
  reg [2:0] ALIGN_COMMA_WORD_REG = ALIGN_COMMA_WORD;
  reg [40:1] ALIGN_MCOMMA_DET_REG = ALIGN_MCOMMA_DET;
  reg [9:0] ALIGN_MCOMMA_VALUE_REG = ALIGN_MCOMMA_VALUE;
  reg [40:1] ALIGN_PCOMMA_DET_REG = ALIGN_PCOMMA_DET;
  reg [9:0] ALIGN_PCOMMA_VALUE_REG = ALIGN_PCOMMA_VALUE;
  reg [0:0] A_RXOSCALRESET_REG = A_RXOSCALRESET;
  reg [0:0] A_RXPROGDIVRESET_REG = A_RXPROGDIVRESET;
  reg [0:0] A_RXTERMINATION_REG = A_RXTERMINATION;
  reg [4:0] A_TXDIFFCTRL_REG = A_TXDIFFCTRL;
  reg [0:0] A_TXPROGDIVRESET_REG = A_TXPROGDIVRESET;
  reg [56:1] CBCC_DATA_SOURCE_SEL_REG = CBCC_DATA_SOURCE_SEL;
  reg [0:0] CDR_SWAP_MODE_EN_REG = CDR_SWAP_MODE_EN;
  reg [0:0] CFOK_PWRSVE_EN_REG = CFOK_PWRSVE_EN;
  reg [40:1] CHAN_BOND_KEEP_ALIGN_REG = CHAN_BOND_KEEP_ALIGN;
  reg [3:0] CHAN_BOND_MAX_SKEW_REG = CHAN_BOND_MAX_SKEW;
  reg [9:0] CHAN_BOND_SEQ_1_1_REG = CHAN_BOND_SEQ_1_1;
  reg [9:0] CHAN_BOND_SEQ_1_2_REG = CHAN_BOND_SEQ_1_2;
  reg [9:0] CHAN_BOND_SEQ_1_3_REG = CHAN_BOND_SEQ_1_3;
  reg [9:0] CHAN_BOND_SEQ_1_4_REG = CHAN_BOND_SEQ_1_4;
  reg [3:0] CHAN_BOND_SEQ_1_ENABLE_REG = CHAN_BOND_SEQ_1_ENABLE;
  reg [9:0] CHAN_BOND_SEQ_2_1_REG = CHAN_BOND_SEQ_2_1;
  reg [9:0] CHAN_BOND_SEQ_2_2_REG = CHAN_BOND_SEQ_2_2;
  reg [9:0] CHAN_BOND_SEQ_2_3_REG = CHAN_BOND_SEQ_2_3;
  reg [9:0] CHAN_BOND_SEQ_2_4_REG = CHAN_BOND_SEQ_2_4;
  reg [3:0] CHAN_BOND_SEQ_2_ENABLE_REG = CHAN_BOND_SEQ_2_ENABLE;
  reg [40:1] CHAN_BOND_SEQ_2_USE_REG = CHAN_BOND_SEQ_2_USE;
  reg [2:0] CHAN_BOND_SEQ_LEN_REG = CHAN_BOND_SEQ_LEN;
  reg [15:0] CH_HSPMUX_REG = CH_HSPMUX;
  reg [15:0] CKCAL1_CFG_0_REG = CKCAL1_CFG_0;
  reg [15:0] CKCAL1_CFG_1_REG = CKCAL1_CFG_1;
  reg [15:0] CKCAL1_CFG_2_REG = CKCAL1_CFG_2;
  reg [15:0] CKCAL1_CFG_3_REG = CKCAL1_CFG_3;
  reg [15:0] CKCAL2_CFG_0_REG = CKCAL2_CFG_0;
  reg [15:0] CKCAL2_CFG_1_REG = CKCAL2_CFG_1;
  reg [15:0] CKCAL2_CFG_2_REG = CKCAL2_CFG_2;
  reg [15:0] CKCAL2_CFG_3_REG = CKCAL2_CFG_3;
  reg [15:0] CKCAL2_CFG_4_REG = CKCAL2_CFG_4;
  reg [40:1] CLK_CORRECT_USE_REG = CLK_CORRECT_USE;
  reg [40:1] CLK_COR_KEEP_IDLE_REG = CLK_COR_KEEP_IDLE;
  reg [5:0] CLK_COR_MAX_LAT_REG = CLK_COR_MAX_LAT;
  reg [5:0] CLK_COR_MIN_LAT_REG = CLK_COR_MIN_LAT;
  reg [40:1] CLK_COR_PRECEDENCE_REG = CLK_COR_PRECEDENCE;
  reg [4:0] CLK_COR_REPEAT_WAIT_REG = CLK_COR_REPEAT_WAIT;
  reg [9:0] CLK_COR_SEQ_1_1_REG = CLK_COR_SEQ_1_1;
  reg [9:0] CLK_COR_SEQ_1_2_REG = CLK_COR_SEQ_1_2;
  reg [9:0] CLK_COR_SEQ_1_3_REG = CLK_COR_SEQ_1_3;
  reg [9:0] CLK_COR_SEQ_1_4_REG = CLK_COR_SEQ_1_4;
  reg [3:0] CLK_COR_SEQ_1_ENABLE_REG = CLK_COR_SEQ_1_ENABLE;
  reg [9:0] CLK_COR_SEQ_2_1_REG = CLK_COR_SEQ_2_1;
  reg [9:0] CLK_COR_SEQ_2_2_REG = CLK_COR_SEQ_2_2;
  reg [9:0] CLK_COR_SEQ_2_3_REG = CLK_COR_SEQ_2_3;
  reg [9:0] CLK_COR_SEQ_2_4_REG = CLK_COR_SEQ_2_4;
  reg [3:0] CLK_COR_SEQ_2_ENABLE_REG = CLK_COR_SEQ_2_ENABLE;
  reg [40:1] CLK_COR_SEQ_2_USE_REG = CLK_COR_SEQ_2_USE;
  reg [2:0] CLK_COR_SEQ_LEN_REG = CLK_COR_SEQ_LEN;
  reg [15:0] CPLL_CFG0_REG = CPLL_CFG0;
  reg [15:0] CPLL_CFG1_REG = CPLL_CFG1;
  reg [15:0] CPLL_CFG2_REG = CPLL_CFG2;
  reg [15:0] CPLL_CFG3_REG = CPLL_CFG3;
  reg [4:0] CPLL_FBDIV_REG = CPLL_FBDIV;
  reg [2:0] CPLL_FBDIV_45_REG = CPLL_FBDIV_45;
  reg [15:0] CPLL_INIT_CFG0_REG = CPLL_INIT_CFG0;
  reg [15:0] CPLL_LOCK_CFG_REG = CPLL_LOCK_CFG;
  reg [4:0] CPLL_REFCLK_DIV_REG = CPLL_REFCLK_DIV;
  reg [2:0] CTLE3_OCAP_EXT_CTRL_REG = CTLE3_OCAP_EXT_CTRL;
  reg [0:0] CTLE3_OCAP_EXT_EN_REG = CTLE3_OCAP_EXT_EN;
  reg [1:0] DDI_CTRL_REG = DDI_CTRL;
  reg [4:0] DDI_REALIGN_WAIT_REG = DDI_REALIGN_WAIT;
  reg [40:1] DEC_MCOMMA_DETECT_REG = DEC_MCOMMA_DETECT;
  reg [40:1] DEC_PCOMMA_DETECT_REG = DEC_PCOMMA_DETECT;
  reg [40:1] DEC_VALID_COMMA_ONLY_REG = DEC_VALID_COMMA_ONLY;
  reg [0:0] DELAY_ELEC_REG = DELAY_ELEC;
  reg [9:0] DMONITOR_CFG0_REG = DMONITOR_CFG0;
  reg [7:0] DMONITOR_CFG1_REG = DMONITOR_CFG1;
  reg [0:0] ES_CLK_PHASE_SEL_REG = ES_CLK_PHASE_SEL;
  reg [5:0] ES_CONTROL_REG = ES_CONTROL;
  reg [40:1] ES_ERRDET_EN_REG = ES_ERRDET_EN;
  reg [40:1] ES_EYE_SCAN_EN_REG = ES_EYE_SCAN_EN;
  reg [11:0] ES_HORZ_OFFSET_REG = ES_HORZ_OFFSET;
  reg [4:0] ES_PRESCALE_REG = ES_PRESCALE;
  reg [15:0] ES_QUALIFIER0_REG = ES_QUALIFIER0;
  reg [15:0] ES_QUALIFIER1_REG = ES_QUALIFIER1;
  reg [15:0] ES_QUALIFIER2_REG = ES_QUALIFIER2;
  reg [15:0] ES_QUALIFIER3_REG = ES_QUALIFIER3;
  reg [15:0] ES_QUALIFIER4_REG = ES_QUALIFIER4;
  reg [15:0] ES_QUALIFIER5_REG = ES_QUALIFIER5;
  reg [15:0] ES_QUALIFIER6_REG = ES_QUALIFIER6;
  reg [15:0] ES_QUALIFIER7_REG = ES_QUALIFIER7;
  reg [15:0] ES_QUALIFIER8_REG = ES_QUALIFIER8;
  reg [15:0] ES_QUALIFIER9_REG = ES_QUALIFIER9;
  reg [15:0] ES_QUAL_MASK0_REG = ES_QUAL_MASK0;
  reg [15:0] ES_QUAL_MASK1_REG = ES_QUAL_MASK1;
  reg [15:0] ES_QUAL_MASK2_REG = ES_QUAL_MASK2;
  reg [15:0] ES_QUAL_MASK3_REG = ES_QUAL_MASK3;
  reg [15:0] ES_QUAL_MASK4_REG = ES_QUAL_MASK4;
  reg [15:0] ES_QUAL_MASK5_REG = ES_QUAL_MASK5;
  reg [15:0] ES_QUAL_MASK6_REG = ES_QUAL_MASK6;
  reg [15:0] ES_QUAL_MASK7_REG = ES_QUAL_MASK7;
  reg [15:0] ES_QUAL_MASK8_REG = ES_QUAL_MASK8;
  reg [15:0] ES_QUAL_MASK9_REG = ES_QUAL_MASK9;
  reg [15:0] ES_SDATA_MASK0_REG = ES_SDATA_MASK0;
  reg [15:0] ES_SDATA_MASK1_REG = ES_SDATA_MASK1;
  reg [15:0] ES_SDATA_MASK2_REG = ES_SDATA_MASK2;
  reg [15:0] ES_SDATA_MASK3_REG = ES_SDATA_MASK3;
  reg [15:0] ES_SDATA_MASK4_REG = ES_SDATA_MASK4;
  reg [15:0] ES_SDATA_MASK5_REG = ES_SDATA_MASK5;
  reg [15:0] ES_SDATA_MASK6_REG = ES_SDATA_MASK6;
  reg [15:0] ES_SDATA_MASK7_REG = ES_SDATA_MASK7;
  reg [15:0] ES_SDATA_MASK8_REG = ES_SDATA_MASK8;
  reg [15:0] ES_SDATA_MASK9_REG = ES_SDATA_MASK9;
  reg [1:0] EYESCAN_VP_RANGE_REG = EYESCAN_VP_RANGE;
  reg [0:0] EYE_SCAN_SWAP_EN_REG = EYE_SCAN_SWAP_EN;
  reg [3:0] FTS_DESKEW_SEQ_ENABLE_REG = FTS_DESKEW_SEQ_ENABLE;
  reg [3:0] FTS_LANE_DESKEW_CFG_REG = FTS_LANE_DESKEW_CFG;
  reg [40:1] FTS_LANE_DESKEW_EN_REG = FTS_LANE_DESKEW_EN;
  reg [4:0] GEARBOX_MODE_REG = GEARBOX_MODE;
  reg [0:0] ISCAN_CK_PH_SEL2_REG = ISCAN_CK_PH_SEL2;
  reg [0:0] LOCAL_MASTER_REG = LOCAL_MASTER;
  reg [2:0] LPBK_BIAS_CTRL_REG = LPBK_BIAS_CTRL;
  reg [0:0] LPBK_EN_RCAL_B_REG = LPBK_EN_RCAL_B;
  reg [3:0] LPBK_EXT_RCAL_REG = LPBK_EXT_RCAL;
  reg [2:0] LPBK_IND_CTRL0_REG = LPBK_IND_CTRL0;
  reg [2:0] LPBK_IND_CTRL1_REG = LPBK_IND_CTRL1;
  reg [2:0] LPBK_IND_CTRL2_REG = LPBK_IND_CTRL2;
  reg [1:0] LPBK_RG_CTRL_REG = LPBK_RG_CTRL;
  reg [1:0] OOBDIVCTL_REG = OOBDIVCTL;
  reg [0:0] OOB_PWRUP_REG = OOB_PWRUP;
  reg [80:1] PCI3_AUTO_REALIGN_REG = PCI3_AUTO_REALIGN;
  reg [0:0] PCI3_PIPE_RX_ELECIDLE_REG = PCI3_PIPE_RX_ELECIDLE;
  reg [1:0] PCI3_RX_ASYNC_EBUF_BYPASS_REG = PCI3_RX_ASYNC_EBUF_BYPASS;
  reg [0:0] PCI3_RX_ELECIDLE_EI2_ENABLE_REG = PCI3_RX_ELECIDLE_EI2_ENABLE;
  reg [5:0] PCI3_RX_ELECIDLE_H2L_COUNT_REG = PCI3_RX_ELECIDLE_H2L_COUNT;
  reg [2:0] PCI3_RX_ELECIDLE_H2L_DISABLE_REG = PCI3_RX_ELECIDLE_H2L_DISABLE;
  reg [5:0] PCI3_RX_ELECIDLE_HI_COUNT_REG = PCI3_RX_ELECIDLE_HI_COUNT;
  reg [0:0] PCI3_RX_ELECIDLE_LP4_DISABLE_REG = PCI3_RX_ELECIDLE_LP4_DISABLE;
  reg [0:0] PCI3_RX_FIFO_DISABLE_REG = PCI3_RX_FIFO_DISABLE;
  reg [4:0] PCIE3_CLK_COR_EMPTY_THRSH_REG = PCIE3_CLK_COR_EMPTY_THRSH;
  reg [5:0] PCIE3_CLK_COR_FULL_THRSH_REG = PCIE3_CLK_COR_FULL_THRSH;
  reg [4:0] PCIE3_CLK_COR_MAX_LAT_REG = PCIE3_CLK_COR_MAX_LAT;
  reg [4:0] PCIE3_CLK_COR_MIN_LAT_REG = PCIE3_CLK_COR_MIN_LAT;
  reg [5:0] PCIE3_CLK_COR_THRSH_TIMER_REG = PCIE3_CLK_COR_THRSH_TIMER;
  reg [40:1] PCIE_64B_DYN_CLKSW_DIS_REG = PCIE_64B_DYN_CLKSW_DIS;
  reg [15:0] PCIE_BUFG_DIV_CTRL_REG = PCIE_BUFG_DIV_CTRL;
  reg [40:1] PCIE_GEN4_64BIT_INT_EN_REG = PCIE_GEN4_64BIT_INT_EN;
  reg [1:0] PCIE_PLL_SEL_MODE_GEN12_REG = PCIE_PLL_SEL_MODE_GEN12;
  reg [1:0] PCIE_PLL_SEL_MODE_GEN3_REG = PCIE_PLL_SEL_MODE_GEN3;
  reg [1:0] PCIE_PLL_SEL_MODE_GEN4_REG = PCIE_PLL_SEL_MODE_GEN4;
  reg [15:0] PCIE_RXPCS_CFG_GEN3_REG = PCIE_RXPCS_CFG_GEN3;
  reg [15:0] PCIE_RXPMA_CFG_REG = PCIE_RXPMA_CFG;
  reg [15:0] PCIE_TXPCS_CFG_GEN3_REG = PCIE_TXPCS_CFG_GEN3;
  reg [15:0] PCIE_TXPMA_CFG_REG = PCIE_TXPMA_CFG;
  reg [40:1] PCS_PCIE_EN_REG = PCS_PCIE_EN;
  reg [15:0] PCS_RSVD0_REG = PCS_RSVD0;
  reg [11:0] PD_TRANS_TIME_FROM_P2_REG = PD_TRANS_TIME_FROM_P2;
  reg [7:0] PD_TRANS_TIME_NONE_P2_REG = PD_TRANS_TIME_NONE_P2;
  reg [7:0] PD_TRANS_TIME_TO_P2_REG = PD_TRANS_TIME_TO_P2;
  reg [1:0] PREIQ_FREQ_BST_REG = PREIQ_FREQ_BST;
  reg [0:0] RATE_SW_USE_DRP_REG = RATE_SW_USE_DRP;
  reg [0:0] RCLK_SIPO_DLY_ENB_REG = RCLK_SIPO_DLY_ENB;
  reg [0:0] RCLK_SIPO_INV_EN_REG = RCLK_SIPO_INV_EN;
  reg [2:0] RTX_BUF_CML_CTRL_REG = RTX_BUF_CML_CTRL;
  reg [1:0] RTX_BUF_TERM_CTRL_REG = RTX_BUF_TERM_CTRL;
  reg [4:0] RXBUFRESET_TIME_REG = RXBUFRESET_TIME;
  reg [32:1] RXBUF_ADDR_MODE_REG = RXBUF_ADDR_MODE;
  reg [3:0] RXBUF_EIDLE_HI_CNT_REG = RXBUF_EIDLE_HI_CNT;
  reg [3:0] RXBUF_EIDLE_LO_CNT_REG = RXBUF_EIDLE_LO_CNT;
  reg [40:1] RXBUF_EN_REG = RXBUF_EN;
  reg [40:1] RXBUF_RESET_ON_CB_CHANGE_REG = RXBUF_RESET_ON_CB_CHANGE;
  reg [40:1] RXBUF_RESET_ON_COMMAALIGN_REG = RXBUF_RESET_ON_COMMAALIGN;
  reg [40:1] RXBUF_RESET_ON_EIDLE_REG = RXBUF_RESET_ON_EIDLE;
  reg [40:1] RXBUF_RESET_ON_RATE_CHANGE_REG = RXBUF_RESET_ON_RATE_CHANGE;
  reg [5:0] RXBUF_THRESH_OVFLW_REG = RXBUF_THRESH_OVFLW;
  reg [40:1] RXBUF_THRESH_OVRD_REG = RXBUF_THRESH_OVRD;
  reg [5:0] RXBUF_THRESH_UNDFLW_REG = RXBUF_THRESH_UNDFLW;
  reg [4:0] RXCDRFREQRESET_TIME_REG = RXCDRFREQRESET_TIME;
  reg [4:0] RXCDRPHRESET_TIME_REG = RXCDRPHRESET_TIME;
  reg [15:0] RXCDR_CFG0_REG = RXCDR_CFG0;
  reg [15:0] RXCDR_CFG0_GEN3_REG = RXCDR_CFG0_GEN3;
  reg [15:0] RXCDR_CFG1_REG = RXCDR_CFG1;
  reg [15:0] RXCDR_CFG1_GEN3_REG = RXCDR_CFG1_GEN3;
  reg [15:0] RXCDR_CFG2_REG = RXCDR_CFG2;
  reg [9:0] RXCDR_CFG2_GEN2_REG = RXCDR_CFG2_GEN2;
  reg [15:0] RXCDR_CFG2_GEN3_REG = RXCDR_CFG2_GEN3;
  reg [15:0] RXCDR_CFG2_GEN4_REG = RXCDR_CFG2_GEN4;
  reg [15:0] RXCDR_CFG3_REG = RXCDR_CFG3;
  reg [5:0] RXCDR_CFG3_GEN2_REG = RXCDR_CFG3_GEN2;
  reg [15:0] RXCDR_CFG3_GEN3_REG = RXCDR_CFG3_GEN3;
  reg [15:0] RXCDR_CFG3_GEN4_REG = RXCDR_CFG3_GEN4;
  reg [15:0] RXCDR_CFG4_REG = RXCDR_CFG4;
  reg [15:0] RXCDR_CFG4_GEN3_REG = RXCDR_CFG4_GEN3;
  reg [15:0] RXCDR_CFG5_REG = RXCDR_CFG5;
  reg [15:0] RXCDR_CFG5_GEN3_REG = RXCDR_CFG5_GEN3;
  reg [0:0] RXCDR_FR_RESET_ON_EIDLE_REG = RXCDR_FR_RESET_ON_EIDLE;
  reg [0:0] RXCDR_HOLD_DURING_EIDLE_REG = RXCDR_HOLD_DURING_EIDLE;
  reg [15:0] RXCDR_LOCK_CFG0_REG = RXCDR_LOCK_CFG0;
  reg [15:0] RXCDR_LOCK_CFG1_REG = RXCDR_LOCK_CFG1;
  reg [15:0] RXCDR_LOCK_CFG2_REG = RXCDR_LOCK_CFG2;
  reg [15:0] RXCDR_LOCK_CFG3_REG = RXCDR_LOCK_CFG3;
  reg [15:0] RXCDR_LOCK_CFG4_REG = RXCDR_LOCK_CFG4;
  reg [0:0] RXCDR_PH_RESET_ON_EIDLE_REG = RXCDR_PH_RESET_ON_EIDLE;
  reg [15:0] RXCFOK_CFG0_REG = RXCFOK_CFG0;
  reg [15:0] RXCFOK_CFG1_REG = RXCFOK_CFG1;
  reg [15:0] RXCFOK_CFG2_REG = RXCFOK_CFG2;
  reg [15:0] RXCKCAL1_IQ_LOOP_RST_CFG_REG = RXCKCAL1_IQ_LOOP_RST_CFG;
  reg [15:0] RXCKCAL1_I_LOOP_RST_CFG_REG = RXCKCAL1_I_LOOP_RST_CFG;
  reg [15:0] RXCKCAL1_Q_LOOP_RST_CFG_REG = RXCKCAL1_Q_LOOP_RST_CFG;
  reg [15:0] RXCKCAL2_DX_LOOP_RST_CFG_REG = RXCKCAL2_DX_LOOP_RST_CFG;
  reg [15:0] RXCKCAL2_D_LOOP_RST_CFG_REG = RXCKCAL2_D_LOOP_RST_CFG;
  reg [15:0] RXCKCAL2_S_LOOP_RST_CFG_REG = RXCKCAL2_S_LOOP_RST_CFG;
  reg [15:0] RXCKCAL2_X_LOOP_RST_CFG_REG = RXCKCAL2_X_LOOP_RST_CFG;
  reg [6:0] RXDFELPMRESET_TIME_REG = RXDFELPMRESET_TIME;
  reg [15:0] RXDFELPM_KL_CFG0_REG = RXDFELPM_KL_CFG0;
  reg [15:0] RXDFELPM_KL_CFG1_REG = RXDFELPM_KL_CFG1;
  reg [15:0] RXDFELPM_KL_CFG2_REG = RXDFELPM_KL_CFG2;
  reg [15:0] RXDFE_CFG0_REG = RXDFE_CFG0;
  reg [15:0] RXDFE_CFG1_REG = RXDFE_CFG1;
  reg [15:0] RXDFE_GC_CFG0_REG = RXDFE_GC_CFG0;
  reg [15:0] RXDFE_GC_CFG1_REG = RXDFE_GC_CFG1;
  reg [15:0] RXDFE_GC_CFG2_REG = RXDFE_GC_CFG2;
  reg [15:0] RXDFE_H2_CFG0_REG = RXDFE_H2_CFG0;
  reg [15:0] RXDFE_H2_CFG1_REG = RXDFE_H2_CFG1;
  reg [15:0] RXDFE_H3_CFG0_REG = RXDFE_H3_CFG0;
  reg [15:0] RXDFE_H3_CFG1_REG = RXDFE_H3_CFG1;
  reg [15:0] RXDFE_H4_CFG0_REG = RXDFE_H4_CFG0;
  reg [15:0] RXDFE_H4_CFG1_REG = RXDFE_H4_CFG1;
  reg [15:0] RXDFE_H5_CFG0_REG = RXDFE_H5_CFG0;
  reg [15:0] RXDFE_H5_CFG1_REG = RXDFE_H5_CFG1;
  reg [15:0] RXDFE_H6_CFG0_REG = RXDFE_H6_CFG0;
  reg [15:0] RXDFE_H6_CFG1_REG = RXDFE_H6_CFG1;
  reg [15:0] RXDFE_H7_CFG0_REG = RXDFE_H7_CFG0;
  reg [15:0] RXDFE_H7_CFG1_REG = RXDFE_H7_CFG1;
  reg [15:0] RXDFE_H8_CFG0_REG = RXDFE_H8_CFG0;
  reg [15:0] RXDFE_H8_CFG1_REG = RXDFE_H8_CFG1;
  reg [15:0] RXDFE_H9_CFG0_REG = RXDFE_H9_CFG0;
  reg [15:0] RXDFE_H9_CFG1_REG = RXDFE_H9_CFG1;
  reg [15:0] RXDFE_HA_CFG0_REG = RXDFE_HA_CFG0;
  reg [15:0] RXDFE_HA_CFG1_REG = RXDFE_HA_CFG1;
  reg [15:0] RXDFE_HB_CFG0_REG = RXDFE_HB_CFG0;
  reg [15:0] RXDFE_HB_CFG1_REG = RXDFE_HB_CFG1;
  reg [15:0] RXDFE_HC_CFG0_REG = RXDFE_HC_CFG0;
  reg [15:0] RXDFE_HC_CFG1_REG = RXDFE_HC_CFG1;
  reg [15:0] RXDFE_HD_CFG0_REG = RXDFE_HD_CFG0;
  reg [15:0] RXDFE_HD_CFG1_REG = RXDFE_HD_CFG1;
  reg [15:0] RXDFE_HE_CFG0_REG = RXDFE_HE_CFG0;
  reg [15:0] RXDFE_HE_CFG1_REG = RXDFE_HE_CFG1;
  reg [15:0] RXDFE_HF_CFG0_REG = RXDFE_HF_CFG0;
  reg [15:0] RXDFE_HF_CFG1_REG = RXDFE_HF_CFG1;
  reg [15:0] RXDFE_KH_CFG0_REG = RXDFE_KH_CFG0;
  reg [15:0] RXDFE_KH_CFG1_REG = RXDFE_KH_CFG1;
  reg [15:0] RXDFE_KH_CFG2_REG = RXDFE_KH_CFG2;
  reg [15:0] RXDFE_KH_CFG3_REG = RXDFE_KH_CFG3;
  reg [15:0] RXDFE_OS_CFG0_REG = RXDFE_OS_CFG0;
  reg [15:0] RXDFE_OS_CFG1_REG = RXDFE_OS_CFG1;
  reg [15:0] RXDFE_UT_CFG0_REG = RXDFE_UT_CFG0;
  reg [15:0] RXDFE_UT_CFG1_REG = RXDFE_UT_CFG1;
  reg [15:0] RXDFE_UT_CFG2_REG = RXDFE_UT_CFG2;
  reg [15:0] RXDFE_VP_CFG0_REG = RXDFE_VP_CFG0;
  reg [15:0] RXDFE_VP_CFG1_REG = RXDFE_VP_CFG1;
  reg [15:0] RXDLY_CFG_REG = RXDLY_CFG;
  reg [15:0] RXDLY_LCFG_REG = RXDLY_LCFG;
  reg [72:1] RXELECIDLE_CFG_REG = RXELECIDLE_CFG;
  reg [2:0] RXGBOX_FIFO_INIT_RD_ADDR_REG = RXGBOX_FIFO_INIT_RD_ADDR;
  reg [40:1] RXGEARBOX_EN_REG = RXGEARBOX_EN;
  reg [4:0] RXISCANRESET_TIME_REG = RXISCANRESET_TIME;
  reg [15:0] RXLPM_CFG_REG = RXLPM_CFG;
  reg [15:0] RXLPM_GC_CFG_REG = RXLPM_GC_CFG;
  reg [15:0] RXLPM_KH_CFG0_REG = RXLPM_KH_CFG0;
  reg [15:0] RXLPM_KH_CFG1_REG = RXLPM_KH_CFG1;
  reg [15:0] RXLPM_OS_CFG0_REG = RXLPM_OS_CFG0;
  reg [15:0] RXLPM_OS_CFG1_REG = RXLPM_OS_CFG1;
  reg [8:0] RXOOB_CFG_REG = RXOOB_CFG;
  reg [48:1] RXOOB_CLK_CFG_REG = RXOOB_CLK_CFG;
  reg [4:0] RXOSCALRESET_TIME_REG = RXOSCALRESET_TIME;
  reg [5:0] RXOUT_DIV_REG = RXOUT_DIV;
  reg [4:0] RXPCSRESET_TIME_REG = RXPCSRESET_TIME;
  reg [15:0] RXPHBEACON_CFG_REG = RXPHBEACON_CFG;
  reg [15:0] RXPHDLY_CFG_REG = RXPHDLY_CFG;
  reg [15:0] RXPHSAMP_CFG_REG = RXPHSAMP_CFG;
  reg [15:0] RXPHSLIP_CFG_REG = RXPHSLIP_CFG;
  reg [4:0] RXPH_MONITOR_SEL_REG = RXPH_MONITOR_SEL;
  reg [15:0] RXPI_CFG0_REG = RXPI_CFG0;
  reg [15:0] RXPI_CFG1_REG = RXPI_CFG1;
  reg [64:1] RXPMACLK_SEL_REG = RXPMACLK_SEL;
  reg [4:0] RXPMARESET_TIME_REG = RXPMARESET_TIME;
  reg [0:0] RXPRBS_ERR_LOOPBACK_REG = RXPRBS_ERR_LOOPBACK;
  reg [7:0] RXPRBS_LINKACQ_CNT_REG = RXPRBS_LINKACQ_CNT;
  reg [0:0] RXREFCLKDIV2_SEL_REG = RXREFCLKDIV2_SEL;
  reg [3:0] RXSLIDE_AUTO_WAIT_REG = RXSLIDE_AUTO_WAIT;
  reg [32:1] RXSLIDE_MODE_REG = RXSLIDE_MODE;
  reg [0:0] RXSYNC_MULTILANE_REG = RXSYNC_MULTILANE;
  reg [0:0] RXSYNC_OVRD_REG = RXSYNC_OVRD;
  reg [0:0] RXSYNC_SKIP_DA_REG = RXSYNC_SKIP_DA;
  reg [0:0] RX_AFE_CM_EN_REG = RX_AFE_CM_EN;
  reg [15:0] RX_BIAS_CFG0_REG = RX_BIAS_CFG0;
  reg [5:0] RX_BUFFER_CFG_REG = RX_BUFFER_CFG;
  reg [0:0] RX_CAPFF_SARC_ENB_REG = RX_CAPFF_SARC_ENB;
  reg [5:0] RX_CLK25_DIV_REG = RX_CLK25_DIV;
  reg [0:0] RX_CLKMUX_EN_REG = RX_CLKMUX_EN;
  reg [4:0] RX_CLK_SLIP_OVRD_REG = RX_CLK_SLIP_OVRD;
  reg [3:0] RX_CM_BUF_CFG_REG = RX_CM_BUF_CFG;
  reg [0:0] RX_CM_BUF_PD_REG = RX_CM_BUF_PD;
  reg [1:0] RX_CM_SEL_REG = RX_CM_SEL;
  reg [3:0] RX_CM_TRIM_REG = RX_CM_TRIM;
  reg [0:0] RX_CTLE_PWR_SAVING_REG = RX_CTLE_PWR_SAVING;
  reg [3:0] RX_CTLE_RES_CTRL_REG = RX_CTLE_RES_CTRL;
  reg [7:0] RX_DATA_WIDTH_REG = RX_DATA_WIDTH;
  reg [5:0] RX_DDI_SEL_REG = RX_DDI_SEL;
  reg [40:1] RX_DEFER_RESET_BUF_EN_REG = RX_DEFER_RESET_BUF_EN;
  reg [2:0] RX_DEGEN_CTRL_REG = RX_DEGEN_CTRL;
  reg [3:0] RX_DFELPM_CFG0_REG = RX_DFELPM_CFG0;
  reg [0:0] RX_DFELPM_CFG1_REG = RX_DFELPM_CFG1;
  reg [0:0] RX_DFELPM_KLKH_AGC_STUP_EN_REG = RX_DFELPM_KLKH_AGC_STUP_EN;
  reg [2:0] RX_DFE_AGC_CFG1_REG = RX_DFE_AGC_CFG1;
  reg [1:0] RX_DFE_KL_LPM_KH_CFG0_REG = RX_DFE_KL_LPM_KH_CFG0;
  reg [2:0] RX_DFE_KL_LPM_KH_CFG1_REG = RX_DFE_KL_LPM_KH_CFG1;
  reg [1:0] RX_DFE_KL_LPM_KL_CFG0_REG = RX_DFE_KL_LPM_KL_CFG0;
  reg [2:0] RX_DFE_KL_LPM_KL_CFG1_REG = RX_DFE_KL_LPM_KL_CFG1;
  reg [0:0] RX_DFE_LPM_HOLD_DURING_EIDLE_REG = RX_DFE_LPM_HOLD_DURING_EIDLE;
  reg [40:1] RX_DISPERR_SEQ_MATCH_REG = RX_DISPERR_SEQ_MATCH;
  reg [4:0] RX_DIVRESET_TIME_REG = RX_DIVRESET_TIME;
  reg [0:0] RX_EN_CTLE_RCAL_B_REG = RX_EN_CTLE_RCAL_B;
  reg [0:0] RX_EN_SUM_RCAL_B_REG = RX_EN_SUM_RCAL_B;
  reg [6:0] RX_EYESCAN_VS_CODE_REG = RX_EYESCAN_VS_CODE;
  reg [0:0] RX_EYESCAN_VS_NEG_DIR_REG = RX_EYESCAN_VS_NEG_DIR;
  reg [1:0] RX_EYESCAN_VS_RANGE_REG = RX_EYESCAN_VS_RANGE;
  reg [0:0] RX_EYESCAN_VS_UT_SIGN_REG = RX_EYESCAN_VS_UT_SIGN;
  reg [0:0] RX_FABINT_USRCLK_FLOP_REG = RX_FABINT_USRCLK_FLOP;
  reg [0:0] RX_I2V_FILTER_EN_REG = RX_I2V_FILTER_EN;
  reg [1:0] RX_INT_DATAWIDTH_REG = RX_INT_DATAWIDTH;
  reg [0:0] RX_PMA_POWER_SAVE_REG = RX_PMA_POWER_SAVE;
  reg [15:0] RX_PMA_RSV0_REG = RX_PMA_RSV0;
  real RX_PROGDIV_CFG_REG = RX_PROGDIV_CFG;
  reg [15:0] RX_PROGDIV_RATE_REG = RX_PROGDIV_RATE;
  reg [3:0] RX_RESLOAD_CTRL_REG = RX_RESLOAD_CTRL;
  reg [0:0] RX_RESLOAD_OVRD_REG = RX_RESLOAD_OVRD;
  reg [2:0] RX_SAMPLE_PERIOD_REG = RX_SAMPLE_PERIOD;
  reg [5:0] RX_SIG_VALID_DLY_REG = RX_SIG_VALID_DLY;
  reg [0:0] RX_SUM_DEGEN_AVTT_OVERITE_REG = RX_SUM_DEGEN_AVTT_OVERITE;
  reg [0:0] RX_SUM_DFETAPREP_EN_REG = RX_SUM_DFETAPREP_EN;
  reg [3:0] RX_SUM_IREF_TUNE_REG = RX_SUM_IREF_TUNE;
  reg [0:0] RX_SUM_PWR_SAVING_REG = RX_SUM_PWR_SAVING;
  reg [3:0] RX_SUM_RES_CTRL_REG = RX_SUM_RES_CTRL;
  reg [3:0] RX_SUM_VCMTUNE_REG = RX_SUM_VCMTUNE;
  reg [0:0] RX_SUM_VCM_BIAS_TUNE_EN_REG = RX_SUM_VCM_BIAS_TUNE_EN;
  reg [0:0] RX_SUM_VCM_OVWR_REG = RX_SUM_VCM_OVWR;
  reg [2:0] RX_SUM_VREF_TUNE_REG = RX_SUM_VREF_TUNE;
  reg [1:0] RX_TUNE_AFE_OS_REG = RX_TUNE_AFE_OS;
  reg [2:0] RX_VREG_CTRL_REG = RX_VREG_CTRL;
  reg [0:0] RX_VREG_PDB_REG = RX_VREG_PDB;
  reg [1:0] RX_WIDEMODE_CDR_REG = RX_WIDEMODE_CDR;
  reg [1:0] RX_WIDEMODE_CDR_GEN3_REG = RX_WIDEMODE_CDR_GEN3;
  reg [1:0] RX_WIDEMODE_CDR_GEN4_REG = RX_WIDEMODE_CDR_GEN4;
  reg [40:1] RX_XCLK_SEL_REG = RX_XCLK_SEL;
  reg [0:0] RX_XMODE_SEL_REG = RX_XMODE_SEL;
  reg [0:0] SAMPLE_CLK_PHASE_REG = SAMPLE_CLK_PHASE;
  reg [0:0] SAS_12G_MODE_REG = SAS_12G_MODE;
  reg [3:0] SATA_BURST_SEQ_LEN_REG = SATA_BURST_SEQ_LEN;
  reg [2:0] SATA_BURST_VAL_REG = SATA_BURST_VAL;
  reg [88:1] SATA_CPLL_CFG_REG = SATA_CPLL_CFG;
  reg [2:0] SATA_EIDLE_VAL_REG = SATA_EIDLE_VAL;
  reg [40:1] SHOW_REALIGN_COMMA_REG = SHOW_REALIGN_COMMA;
  reg [160:1] SIM_DEVICE_REG = SIM_DEVICE;
  reg [48:1] SIM_MODE_REG = SIM_MODE;
  reg [40:1] SIM_RECEIVER_DETECT_PASS_REG = SIM_RECEIVER_DETECT_PASS;
  reg [40:1] SIM_RESET_SPEEDUP_REG = SIM_RESET_SPEEDUP;
  reg [32:1] SIM_TX_EIDLE_DRIVE_LEVEL_REG = SIM_TX_EIDLE_DRIVE_LEVEL;
  reg [0:0] SRSTMODE_REG = SRSTMODE;
  reg [1:0] TAPDLY_SET_TX_REG = TAPDLY_SET_TX;
  reg [14:0] TERM_RCAL_CFG_REG = TERM_RCAL_CFG;
  reg [2:0] TERM_RCAL_OVRD_REG = TERM_RCAL_OVRD;
  reg [7:0] TRANS_TIME_RATE_REG = TRANS_TIME_RATE;
  reg [7:0] TST_RSV0_REG = TST_RSV0;
  reg [7:0] TST_RSV1_REG = TST_RSV1;
  reg [40:1] TXBUF_EN_REG = TXBUF_EN;
  reg [40:1] TXBUF_RESET_ON_RATE_CHANGE_REG = TXBUF_RESET_ON_RATE_CHANGE;
  reg [15:0] TXDLY_CFG_REG = TXDLY_CFG;
  reg [15:0] TXDLY_LCFG_REG = TXDLY_LCFG;
  reg [1:0] TXDRV_FREQBAND_REG = TXDRV_FREQBAND;
  reg [15:0] TXFE_CFG0_REG = TXFE_CFG0;
  reg [15:0] TXFE_CFG1_REG = TXFE_CFG1;
  reg [15:0] TXFE_CFG2_REG = TXFE_CFG2;
  reg [15:0] TXFE_CFG3_REG = TXFE_CFG3;
  reg [32:1] TXFIFO_ADDR_CFG_REG = TXFIFO_ADDR_CFG;
  reg [2:0] TXGBOX_FIFO_INIT_RD_ADDR_REG = TXGBOX_FIFO_INIT_RD_ADDR;
  reg [40:1] TXGEARBOX_EN_REG = TXGEARBOX_EN;
  reg [5:0] TXOUT_DIV_REG = TXOUT_DIV;
  reg [4:0] TXPCSRESET_TIME_REG = TXPCSRESET_TIME;
  reg [15:0] TXPHDLY_CFG0_REG = TXPHDLY_CFG0;
  reg [15:0] TXPHDLY_CFG1_REG = TXPHDLY_CFG1;
  reg [15:0] TXPH_CFG_REG = TXPH_CFG;
  reg [15:0] TXPH_CFG2_REG = TXPH_CFG2;
  reg [4:0] TXPH_MONITOR_SEL_REG = TXPH_MONITOR_SEL;
  reg [15:0] TXPI_CFG0_REG = TXPI_CFG0;
  reg [15:0] TXPI_CFG1_REG = TXPI_CFG1;
  reg [0:0] TXPI_GRAY_SEL_REG = TXPI_GRAY_SEL;
  reg [0:0] TXPI_INVSTROBE_SEL_REG = TXPI_INVSTROBE_SEL;
  reg [0:0] TXPI_PPM_REG = TXPI_PPM;
  reg [7:0] TXPI_PPM_CFG_REG = TXPI_PPM_CFG;
  reg [2:0] TXPI_SYNFREQ_PPM_REG = TXPI_SYNFREQ_PPM;
  reg [4:0] TXPMARESET_TIME_REG = TXPMARESET_TIME;
  reg [0:0] TXREFCLKDIV2_SEL_REG = TXREFCLKDIV2_SEL;
  reg [1:0] TXSWBST_BST_REG = TXSWBST_BST;
  reg [0:0] TXSWBST_EN_REG = TXSWBST_EN;
  reg [2:0] TXSWBST_MAG_REG = TXSWBST_MAG;
  reg [0:0] TXSYNC_MULTILANE_REG = TXSYNC_MULTILANE;
  reg [0:0] TXSYNC_OVRD_REG = TXSYNC_OVRD;
  reg [0:0] TXSYNC_SKIP_DA_REG = TXSYNC_SKIP_DA;
  reg [5:0] TX_CLK25_DIV_REG = TX_CLK25_DIV;
  reg [0:0] TX_CLKMUX_EN_REG = TX_CLKMUX_EN;
  reg [7:0] TX_DATA_WIDTH_REG = TX_DATA_WIDTH;
  reg [15:0] TX_DCC_LOOP_RST_CFG_REG = TX_DCC_LOOP_RST_CFG;
  reg [5:0] TX_DEEMPH0_REG = TX_DEEMPH0;
  reg [5:0] TX_DEEMPH1_REG = TX_DEEMPH1;
  reg [5:0] TX_DEEMPH2_REG = TX_DEEMPH2;
  reg [5:0] TX_DEEMPH3_REG = TX_DEEMPH3;
  reg [4:0] TX_DIVRESET_TIME_REG = TX_DIVRESET_TIME;
  reg [64:1] TX_DRIVE_MODE_REG = TX_DRIVE_MODE;
  reg [2:0] TX_EIDLE_ASSERT_DELAY_REG = TX_EIDLE_ASSERT_DELAY;
  reg [2:0] TX_EIDLE_DEASSERT_DELAY_REG = TX_EIDLE_DEASSERT_DELAY;
  reg [0:0] TX_FABINT_USRCLK_FLOP_REG = TX_FABINT_USRCLK_FLOP;
  reg [0:0] TX_FIFO_BYP_EN_REG = TX_FIFO_BYP_EN;
  reg [0:0] TX_IDLE_DATA_ZERO_REG = TX_IDLE_DATA_ZERO;
  reg [1:0] TX_INT_DATAWIDTH_REG = TX_INT_DATAWIDTH;
  reg [40:1] TX_LOOPBACK_DRIVE_HIZ_REG = TX_LOOPBACK_DRIVE_HIZ;
  reg [0:0] TX_MAINCURSOR_SEL_REG = TX_MAINCURSOR_SEL;
  reg [6:0] TX_MARGIN_FULL_0_REG = TX_MARGIN_FULL_0;
  reg [6:0] TX_MARGIN_FULL_1_REG = TX_MARGIN_FULL_1;
  reg [6:0] TX_MARGIN_FULL_2_REG = TX_MARGIN_FULL_2;
  reg [6:0] TX_MARGIN_FULL_3_REG = TX_MARGIN_FULL_3;
  reg [6:0] TX_MARGIN_FULL_4_REG = TX_MARGIN_FULL_4;
  reg [6:0] TX_MARGIN_LOW_0_REG = TX_MARGIN_LOW_0;
  reg [6:0] TX_MARGIN_LOW_1_REG = TX_MARGIN_LOW_1;
  reg [6:0] TX_MARGIN_LOW_2_REG = TX_MARGIN_LOW_2;
  reg [6:0] TX_MARGIN_LOW_3_REG = TX_MARGIN_LOW_3;
  reg [6:0] TX_MARGIN_LOW_4_REG = TX_MARGIN_LOW_4;
  reg [15:0] TX_PHICAL_CFG0_REG = TX_PHICAL_CFG0;
  reg [15:0] TX_PHICAL_CFG1_REG = TX_PHICAL_CFG1;
  reg [1:0] TX_PI_BIASSET_REG = TX_PI_BIASSET;
  reg [0:0] TX_PMADATA_OPT_REG = TX_PMADATA_OPT;
  reg [0:0] TX_PMA_POWER_SAVE_REG = TX_PMA_POWER_SAVE;
  reg [15:0] TX_PMA_RSV0_REG = TX_PMA_RSV0;
  reg [15:0] TX_PMA_RSV1_REG = TX_PMA_RSV1;
  reg [48:1] TX_PROGCLK_SEL_REG = TX_PROGCLK_SEL;
  real TX_PROGDIV_CFG_REG = TX_PROGDIV_CFG;
  reg [15:0] TX_PROGDIV_RATE_REG = TX_PROGDIV_RATE;
  reg [13:0] TX_RXDETECT_CFG_REG = TX_RXDETECT_CFG;
  reg [2:0] TX_RXDETECT_REF_REG = TX_RXDETECT_REF;
  reg [2:0] TX_SAMPLE_PERIOD_REG = TX_SAMPLE_PERIOD;
  reg [1:0] TX_SW_MEAS_REG = TX_SW_MEAS;
  reg [2:0] TX_VREG_CTRL_REG = TX_VREG_CTRL;
  reg [0:0] TX_VREG_PDB_REG = TX_VREG_PDB;
  reg [1:0] TX_VREG_VREFSEL_REG = TX_VREG_VREFSEL;
  reg [40:1] TX_XCLK_SEL_REG = TX_XCLK_SEL;
  reg [0:0] USB_BOTH_BURST_IDLE_REG = USB_BOTH_BURST_IDLE;
  reg [6:0] USB_BURSTMAX_U3WAKE_REG = USB_BURSTMAX_U3WAKE;
  reg [6:0] USB_BURSTMIN_U3WAKE_REG = USB_BURSTMIN_U3WAKE;
  reg [0:0] USB_CLK_COR_EQ_EN_REG = USB_CLK_COR_EQ_EN;
  reg [0:0] USB_EXT_CNTL_REG = USB_EXT_CNTL;
  reg [9:0] USB_IDLEMAX_POLLING_REG = USB_IDLEMAX_POLLING;
  reg [9:0] USB_IDLEMIN_POLLING_REG = USB_IDLEMIN_POLLING;
  reg [8:0] USB_LFPSPING_BURST_REG = USB_LFPSPING_BURST;
  reg [8:0] USB_LFPSPOLLING_BURST_REG = USB_LFPSPOLLING_BURST;
  reg [8:0] USB_LFPSPOLLING_IDLE_MS_REG = USB_LFPSPOLLING_IDLE_MS;
  reg [8:0] USB_LFPSU1EXIT_BURST_REG = USB_LFPSU1EXIT_BURST;
  reg [8:0] USB_LFPSU2LPEXIT_BURST_MS_REG = USB_LFPSU2LPEXIT_BURST_MS;
  reg [8:0] USB_LFPSU3WAKE_BURST_MS_REG = USB_LFPSU3WAKE_BURST_MS;
  reg [3:0] USB_LFPS_TPERIOD_REG = USB_LFPS_TPERIOD;
  reg [0:0] USB_LFPS_TPERIOD_ACCURATE_REG = USB_LFPS_TPERIOD_ACCURATE;
  reg [0:0] USB_MODE_REG = USB_MODE;
  reg [0:0] USB_PCIE_ERR_REP_DIS_REG = USB_PCIE_ERR_REP_DIS;
  reg [5:0] USB_PING_SATA_MAX_INIT_REG = USB_PING_SATA_MAX_INIT;
  reg [5:0] USB_PING_SATA_MIN_INIT_REG = USB_PING_SATA_MIN_INIT;
  reg [5:0] USB_POLL_SATA_MAX_BURST_REG = USB_POLL_SATA_MAX_BURST;
  reg [5:0] USB_POLL_SATA_MIN_BURST_REG = USB_POLL_SATA_MIN_BURST;
  reg [0:0] USB_RAW_ELEC_REG = USB_RAW_ELEC;
  reg [0:0] USB_RXIDLE_P0_CTRL_REG = USB_RXIDLE_P0_CTRL;
  reg [0:0] USB_TXIDLE_TUNE_ENABLE_REG = USB_TXIDLE_TUNE_ENABLE;
  reg [5:0] USB_U1_SATA_MAX_WAKE_REG = USB_U1_SATA_MAX_WAKE;
  reg [5:0] USB_U1_SATA_MIN_WAKE_REG = USB_U1_SATA_MIN_WAKE;
  reg [6:0] USB_U2_SAS_MAX_COM_REG = USB_U2_SAS_MAX_COM;
  reg [5:0] USB_U2_SAS_MIN_COM_REG = USB_U2_SAS_MIN_COM;
  reg [0:0] USE_PCS_CLK_PHASE_SEL_REG = USE_PCS_CLK_PHASE_SEL;
  reg [0:0] Y_ALL_MODE_REG = Y_ALL_MODE;
`endif

  reg [0:0] AEN_CDRSTEPSEL_REG = 1'b0;
  reg [0:0] AEN_CPLL_REG = 1'b0;
  reg [0:0] AEN_LOOPBACK_REG = 1'b0;
  reg [0:0] AEN_MASTER_REG = 1'b0;
  reg [0:0] AEN_PD_AND_EIDLE_REG = 1'b0;
  reg [0:0] AEN_POLARITY_REG = 1'b0;
  reg [0:0] AEN_PRBS_REG = 1'b0;
  reg [0:0] AEN_RESET_REG = 1'b0;
  reg [0:0] AEN_RXCDR_REG = 1'b0;
  reg [0:0] AEN_RXDFE_REG = 1'b0;
  reg [0:0] AEN_RXDFELPM_REG = 1'b0;
  reg [0:0] AEN_RXOUTCLK_SEL_REG = 1'b0;
  reg [0:0] AEN_RXPHDLY_REG = 1'b0;
  reg [0:0] AEN_RXPLLCLK_SEL_REG = 1'b0;
  reg [0:0] AEN_RXSYSCLK_SEL_REG = 1'b0;
  reg [0:0] AEN_TXMUXDCD_REG = 1'b0;
  reg [0:0] AEN_TXOUTCLK_SEL_REG = 1'b0;
  reg [0:0] AEN_TXPHDLY_REG = 1'b0;
  reg [0:0] AEN_TXPI_PPM_REG = 1'b0;
  reg [0:0] AEN_TXPLLCLK_SEL_REG = 1'b0;
  reg [0:0] AEN_TXSYSCLK_SEL_REG = 1'b0;
  reg [0:0] AEN_TX_DRIVE_MODE_REG = 1'b0;
  reg [15:0] AMONITOR_CFG_REG = 16'h0FC0;
  reg [0:0] A_CPLLLOCKEN_REG = 1'b0;
  reg [0:0] A_CPLLPD_REG = 1'b0;
  reg [0:0] A_CPLLRESET_REG = 1'b0;
  reg [0:0] A_EYESCANRESET_REG = 1'b0;
  reg [0:0] A_GTRESETSEL_REG = 1'b0;
  reg [0:0] A_GTRXRESET_REG = 1'b0;
  reg [0:0] A_GTTXRESET_REG = 1'b0;
  reg [80:1] A_LOOPBACK_REG = "NOLOOPBACK";
  reg [0:0] A_RXAFECFOKEN_REG = 1'b1;
  reg [0:0] A_RXBUFRESET_REG = 1'b0;
  reg [0:0] A_RXCDRFREQRESET_REG = 1'b0;
  reg [0:0] A_RXCDRHOLD_REG = 1'b0;
  reg [0:0] A_RXCDROVRDEN_REG = 1'b0;
  reg [0:0] A_RXCDRRESET_REG = 1'b0;
  reg [0:0] A_RXCKCALRESET_REG = 1'b0;
  reg [0:0] A_RXDFEAGCHOLD_REG = 1'b0;
  reg [0:0] A_RXDFEAGCOVRDEN_REG = 1'b0;
  reg [3:0] A_RXDFECFOKFCNUM_REG = 4'b0000;
  reg [0:0] A_RXDFECFOKFEN_REG = 1'b0;
  reg [0:0] A_RXDFECFOKFPULSE_REG = 1'b0;
  reg [0:0] A_RXDFECFOKHOLD_REG = 1'b0;
  reg [0:0] A_RXDFECFOKOVREN_REG = 1'b0;
  reg [0:0] A_RXDFEKHHOLD_REG = 0;
  reg [0:0] A_RXDFEKHOVRDEN_REG = 1'b0;
  reg [0:0] A_RXDFELFHOLD_REG = 1'b0;
  reg [0:0] A_RXDFELFOVRDEN_REG = 1'b0;
  reg [0:0] A_RXDFELPMRESET_REG = 1'b0;
  reg [0:0] A_RXDFETAP10HOLD_REG = 1'b0;
  reg [0:0] A_RXDFETAP10OVRDEN_REG = 1'b0;
  reg [0:0] A_RXDFETAP11HOLD_REG = 1'b0;
  reg [0:0] A_RXDFETAP11OVRDEN_REG = 1'b0;
  reg [0:0] A_RXDFETAP12HOLD_REG = 1'b0;
  reg [0:0] A_RXDFETAP12OVRDEN_REG = 1'b0;
  reg [0:0] A_RXDFETAP13HOLD_REG = 1'b0;
  reg [0:0] A_RXDFETAP13OVRDEN_REG = 1'b0;
  reg [0:0] A_RXDFETAP14HOLD_REG = 1'b0;
  reg [0:0] A_RXDFETAP14OVRDEN_REG = 1'b0;
  reg [0:0] A_RXDFETAP15HOLD_REG = 1'b0;
  reg [0:0] A_RXDFETAP15OVRDEN_REG = 1'b0;
  reg [0:0] A_RXDFETAP2HOLD_REG = 1'b0;
  reg [0:0] A_RXDFETAP2OVRDEN_REG = 1'b0;
  reg [0:0] A_RXDFETAP3HOLD_REG = 1'b0;
  reg [0:0] A_RXDFETAP3OVRDEN_REG = 1'b0;
  reg [0:0] A_RXDFETAP4HOLD_REG = 1'b0;
  reg [0:0] A_RXDFETAP4OVRDEN_REG = 1'b0;
  reg [0:0] A_RXDFETAP5HOLD_REG = 1'b0;
  reg [0:0] A_RXDFETAP5OVRDEN_REG = 1'b0;
  reg [0:0] A_RXDFETAP6HOLD_REG = 1'b0;
  reg [0:0] A_RXDFETAP6OVRDEN_REG = 1'b0;
  reg [0:0] A_RXDFETAP7HOLD_REG = 1'b0;
  reg [0:0] A_RXDFETAP7OVRDEN_REG = 1'b0;
  reg [0:0] A_RXDFETAP8HOLD_REG = 1'b0;
  reg [0:0] A_RXDFETAP8OVRDEN_REG = 1'b0;
  reg [0:0] A_RXDFETAP9HOLD_REG = 1'b0;
  reg [0:0] A_RXDFETAP9OVRDEN_REG = 1'b0;
  reg [0:0] A_RXDFEUTHOLD_REG = 1'b0;
  reg [0:0] A_RXDFEUTOVRDEN_REG = 1'b0;
  reg [0:0] A_RXDFEVPHOLD_REG = 1'b0;
  reg [0:0] A_RXDFEVPOVRDEN_REG = 1'b0;
  reg [0:0] A_RXDFEXYDEN_REG = 1'b0;
  reg [0:0] A_RXDLYBYPASS_REG = 1'b0;
  reg [0:0] A_RXDLYEN_REG = 1'b0;
  reg [0:0] A_RXDLYOVRDEN_REG = 1'b0;
  reg [0:0] A_RXDLYSRESET_REG = 1'b0;
  reg [0:0] A_RXLPMEN_REG = 1'b0;
  reg [0:0] A_RXLPMGCHOLD_REG = 1'b0;
  reg [0:0] A_RXLPMGCOVRDEN_REG = 1'b0;
  reg [0:0] A_RXLPMHFHOLD_REG = 1'b0;
  reg [0:0] A_RXLPMHFOVRDEN_REG = 1'b0;
  reg [0:0] A_RXLPMLFHOLD_REG = 1'b0;
  reg [0:0] A_RXLPMLFKLOVRDEN_REG = 1'b0;
  reg [0:0] A_RXLPMOSHOLD_REG = 1'b0;
  reg [0:0] A_RXLPMOSOVRDEN_REG = 1'b0;
  reg [1:0] A_RXMONITORSEL_REG = 2'b00;
  reg [0:0] A_RXOOBRESET_REG = 1'b0;
  reg [0:0] A_RXOSHOLD_REG = 1'b0;
  reg [0:0] A_RXOSOVRDEN_REG = 1'b0;
  reg [128:1] A_RXOUTCLKSEL_REG = "DISABLED";
  reg [0:0] A_RXPCSRESET_REG = 1'b0;
  reg [24:1] A_RXPD_REG = "P0";
  reg [0:0] A_RXPHALIGN_REG = 1'b0;
  reg [0:0] A_RXPHALIGNEN_REG = 1'b0;
  reg [0:0] A_RXPHDLYPD_REG = 1'b0;
  reg [0:0] A_RXPHDLYRESET_REG = 1'b0;
  reg [64:1] A_RXPLLCLKSEL_REG = "QPLLCLK1";
  reg [0:0] A_RXPMARESET_REG = 1'b0;
  reg [0:0] A_RXPOLARITY_REG = 1'b0;
  reg [0:0] A_RXPRBSCNTRESET_REG = 1'b0;
  reg [48:1] A_RXPRBSSEL_REG = "PRBS7";
  reg [88:1] A_RXSYSCLKSEL_REG = "CPLLREFCLK";
  reg [2:0] A_TXBUFDIFFCTRL_REG = 3'b100;
  reg [0:0] A_TXDCCRESET_REG = 1'b0;
  reg [1:0] A_TXDEEMPH_REG = 2'b00;
  reg [0:0] A_TXDLYBYPASS_REG = 1'b0;
  reg [0:0] A_TXDLYEN_REG = 1'b0;
  reg [0:0] A_TXDLYOVRDEN_REG = 1'b0;
  reg [0:0] A_TXDLYSRESET_REG = 1'b0;
  reg [0:0] A_TXELECIDLE_REG = 1'b0;
  reg [0:0] A_TXINHIBIT_REG = 1'b0;
  reg [6:0] A_TXMAINCURSOR_REG = 7'b0000000;
  reg [2:0] A_TXMARGIN_REG = 3'b000;
  reg [0:0] A_TXMUXDCDEXHOLD_REG = 1'b0;
  reg [0:0] A_TXMUXDCDORWREN_REG = 1'b0;
  reg [128:1] A_TXOUTCLKSEL_REG = "DISABLED";
  reg [0:0] A_TXPCSRESET_REG = 1'b0;
  reg [24:1] A_TXPD_REG = "P0";
  reg [0:0] A_TXPHALIGN_REG = 1'b0;
  reg [0:0] A_TXPHALIGNEN_REG = 1'b0;
  reg [0:0] A_TXPHDLYPD_REG = 1'b0;
  reg [0:0] A_TXPHDLYRESET_REG = 1'b0;
  reg [0:0] A_TXPHINIT_REG = 1'b0;
  reg [0:0] A_TXPHOVRDEN_REG = 1'b0;
  reg [0:0] A_TXPIPPMOVRDEN_REG = 1'b0;
  reg [0:0] A_TXPIPPMPD_REG = 1'b0;
  reg [0:0] A_TXPIPPMSEL_REG = 1'b0;
  reg [64:1] A_TXPLLCLKSEL_REG = "QPLLCLK1";
  reg [0:0] A_TXPMARESET_REG = 1'b0;
  reg [0:0] A_TXPOLARITY_REG = 1'b0;
  reg [4:0] A_TXPOSTCURSOR_REG = 5'b00000;
  reg [0:0] A_TXPRBSFORCEERR_REG = 1'b0;
  reg [96:1] A_TXPRBSSEL_REG = "PRBS7";
  reg [4:0] A_TXPRECURSOR_REG = 5'b00000;
  reg [0:0] A_TXRESETSEL_REG = 1'b0;
  reg [0:0] A_TXSWING_REG = 1'b0;
  reg [88:1] A_TXSYSCLKSEL_REG = "CPLLREFCLK";
  reg [1:0] BSR_ENABLE_REG = 2'b00;
  reg [15:0] CSSD_CLK_MASK0_REG = 16'b0000000000000000;
  reg [15:0] CSSD_CLK_MASK1_REG = 16'b0000000000000000;
  reg [15:0] CSSD_REG0_REG = 16'b0000000000000000;
  reg [15:0] CSSD_REG1_REG = 16'b0000000000000000;
  reg [15:0] CSSD_REG10_REG = 16'b0000000000000000;
  reg [15:0] CSSD_REG2_REG = 16'b0000000000000000;
  reg [15:0] CSSD_REG3_REG = 16'b0000000000000000;
  reg [15:0] CSSD_REG4_REG = 16'b0000000000000000;
  reg [15:0] CSSD_REG5_REG = 16'b0000000000000000;
  reg [15:0] CSSD_REG6_REG = 16'b0000000000000000;
  reg [15:0] CSSD_REG7_REG = 16'b0000000000000000;
  reg [15:0] CSSD_REG8_REG = 16'b0000000000000000;
  reg [15:0] CSSD_REG9_REG = 16'b0000000000000000;
  reg [40:1] GEN_RXUSRCLK_REG = "TRUE";
  reg [40:1] GEN_TXUSRCLK_REG = "TRUE";
  reg [0:0] GT_INSTANTIATED_REG = 1'b1;
  reg [15:0] INT_MASK_CFG0_REG = 16'b0000000000000000;
  reg [15:0] INT_MASK_CFG1_REG = 16'b0000000000000000;
  reg [5:0] RX_DFECFOKFCDAC_REG = 6'b000000;
  reg [1:0] RX_VREG_VREFSEL_REG = 2'b01;
  reg [0:0] TXOUTCLKPCS_SEL_REG = 1'b0;
  reg [9:0] TX_USERPATTERN_DATA0_REG = 10'b0101111100;
  reg [9:0] TX_USERPATTERN_DATA1_REG = 10'b0101010101;
  reg [9:0] TX_USERPATTERN_DATA2_REG = 10'b1010000011;
  reg [9:0] TX_USERPATTERN_DATA3_REG = 10'b1010101010;
  reg [9:0] TX_USERPATTERN_DATA4_REG = 10'b0101111100;
  reg [9:0] TX_USERPATTERN_DATA5_REG = 10'b0101010101;
  reg [9:0] TX_USERPATTERN_DATA6_REG = 10'b1010000011;
  reg [9:0] TX_USERPATTERN_DATA7_REG = 10'b1010101010;

`ifdef XIL_XECLIB
  wire [63:0] RX_PROGDIV_CFG_BIN;
  wire [63:0] TX_PROGDIV_CFG_BIN;
`else
  reg [63:0] RX_PROGDIV_CFG_BIN;
  reg [63:0] TX_PROGDIV_CFG_BIN;
`endif

`ifdef XIL_ATTR_TEST
  reg attr_test = 1'b1;
`else
  reg attr_test = 1'b0;
`endif

  reg attr_err = 1'b0;
  tri0 glblGSR = glbl.GSR;

  wire BUFGTCE_out;
  wire BUFGTRESET_out;
  wire CPLLFBCLKLOST_out;
  wire CPLLLOCK_out;
  wire CPLLREFCLKLOST_out;
  wire CSSDSTOPCLKDONE_out;
  wire DMONITOROUTCLK_out;
  wire DRPRDY_out;
  wire EYESCANDATAERROR_out;
  wire GTPOWERGOOD_out;
  wire GTREFCLKMONITOR_out;
  wire GTYTXN_out;
  wire GTYTXP_out;
  wire PCIERATEGEN3_out;
  wire PCIERATEIDLE_out;
  wire PCIESYNCTXSYNCDONE_out;
  wire PCIEUSERGEN3RDY_out;
  wire PCIEUSERPHYSTATUSRST_out;
  wire PCIEUSERRATESTART_out;
  wire PHYSTATUS_out;
  wire POWERPRESENT_out;
  wire RESETEXCEPTION_out;
  wire RXBYTEISALIGNED_out;
  wire RXBYTEREALIGN_out;
  wire RXCDRLOCK_out;
  wire RXCDRPHDONE_out;
  wire RXCHANBONDSEQ_out;
  wire RXCHANISALIGNED_out;
  wire RXCHANREALIGN_out;
  wire RXCKCALDONE_out;
  wire RXCOMINITDET_out;
  wire RXCOMMADET_out;
  wire RXCOMSASDET_out;
  wire RXCOMWAKEDET_out;
  wire RXDLYSRESETDONE_out;
  wire RXELECIDLE_out;
  wire RXLFPSTRESETDET_out;
  wire RXLFPSU2LPEXITDET_out;
  wire RXLFPSU3WAKEDET_out;
  wire RXOSINTDONE_out;
  wire RXOSINTSTARTED_out;
  wire RXOSINTSTROBEDONE_out;
  wire RXOSINTSTROBESTARTED_out;
  wire RXOUTCLKFABRIC_out;
  wire RXOUTCLKPCS_out;
  wire RXOUTCLK_out;
  wire RXPHALIGNDONE_out;
  wire RXPHALIGNERR_out;
  wire RXPMARESETDONE_out;
  wire RXPRBSERR_out;
  wire RXPRBSLOCKED_out;
  wire RXPRGDIVRESETDONE_out;
  wire RXRATEDONE_out;
  wire RXRECCLKOUT_out;
  wire RXRESETDONE_out;
  wire RXSLIDERDY_out;
  wire RXSLIPDONE_out;
  wire RXSLIPOUTCLKRDY_out;
  wire RXSLIPPMARDY_out;
  wire RXSYNCDONE_out;
  wire RXSYNCOUT_out;
  wire RXVALID_out;
  wire TXCOMFINISH_out;
  wire TXDCCDONE_out;
  wire TXDLYSRESETDONE_out;
  wire TXOUTCLKFABRIC_out;
  wire TXOUTCLKPCS_out;
  wire TXOUTCLK_out;
  wire TXPHALIGNDONE_out;
  wire TXPHINITDONE_out;
  wire TXPMARESETDONE_out;
  wire TXPRGDIVRESETDONE_out;
  wire TXRATEDONE_out;
  wire TXRESETDONE_out;
  wire TXSYNCDONE_out;
  wire TXSYNCOUT_out;
  wire [127:0] RXDATA_out;
  wire [15:0] DMONITOROUT_out;
  wire [15:0] DRPDO_out;
  wire [15:0] PCSRSVDOUT_out;
  wire [15:0] PINRSRVDAS_out;
  wire [15:0] RXCTRL0_out;
  wire [15:0] RXCTRL1_out;
  wire [17:0] PMASCANOUT_out;
  wire [18:0] SCANOUT_out;
  wire [1:0] PCIERATEQPLLPD_out;
  wire [1:0] PCIERATEQPLLRESET_out;
  wire [1:0] RXCLKCORCNT_out;
  wire [1:0] RXDATAVALID_out;
  wire [1:0] RXHEADERVALID_out;
  wire [1:0] RXSTARTOFSEQ_out;
  wire [1:0] TXBUFSTATUS_out;
  wire [2:0] BUFGTCEMASK_out;
  wire [2:0] BUFGTRSTMASK_out;
  wire [2:0] RXBUFSTATUS_out;
  wire [2:0] RXSTATUS_out;
  wire [4:0] RXCHBONDO_out;
  wire [5:0] RXHEADER_out;
  wire [7:0] RXCTRL2_out;
  wire [7:0] RXCTRL3_out;
  wire [7:0] RXDATAEXTENDRSVD_out;
  wire [7:0] RXMONITOROUT_out;
  wire [8:0] BUFGTDIV_out;

  wire BSR_SERIAL_in;
  wire CDRSTEPDIR_in;
  wire CDRSTEPSQ_in;
  wire CDRSTEPSX_in;
  wire CFGRESET_in;
  wire CLKRSVD0_in;
  wire CLKRSVD1_in;
  wire CPLLFREQLOCK_in;
  wire CPLLLOCKDETCLK_in;
  wire CPLLLOCKEN_in;
  wire CPLLPD_in;
  wire CPLLRESET_in;
  wire CSSDRSTB_in;
  wire CSSDSTOPCLK_in;
  wire DMONFIFORESET_in;
  wire DMONITORCLK_in;
  wire DRPCLK_in;
  wire DRPEN_in;
  wire DRPRST_in;
  wire DRPWE_in;
  wire EYESCANRESET_in;
  wire EYESCANTRIGGER_in;
  wire FREQOS_in;
  wire GTGREFCLK_in;
  wire GTNORTHREFCLK0_in;
  wire GTNORTHREFCLK1_in;
  wire GTREFCLK0_in;
  wire GTREFCLK1_in;
  wire GTRXRESETSEL_in;
  wire GTRXRESET_in;
  wire GTSOUTHREFCLK0_in;
  wire GTSOUTHREFCLK1_in;
  wire GTTXRESETSEL_in;
  wire GTTXRESET_in;
  wire GTYRXN_in;
  wire GTYRXP_in;
  wire INCPCTRL_in;
  wire PCIEEQRXEQADAPTDONE_in;
  wire PCIERSTIDLE_in;
  wire PCIERSTTXSYNCSTART_in;
  wire PCIEUSERRATEDONE_in;
  wire PMASCANCLK0_in;
  wire PMASCANCLK1_in;
  wire PMASCANCLK2_in;
  wire PMASCANCLK3_in;
  wire PMASCANCLK4_in;
  wire PMASCANCLK5_in;
  wire PMASCANCLK6_in;
  wire PMASCANCLK7_in;
  wire PMASCANCLK8_in;
  wire PMASCANENB_in;
  wire PMASCANMODEB_in;
  wire PMASCANRSTEN_in;
  wire QPLL0CLK_in;
  wire QPLL0FREQLOCK_in;
  wire QPLL0REFCLK_in;
  wire QPLL1CLK_in;
  wire QPLL1FREQLOCK_in;
  wire QPLL1REFCLK_in;
  wire RESETOVRD_in;
  wire RX8B10BEN_in;
  wire RXAFECFOKEN_in;
  wire RXBUFRESET_in;
  wire RXCDRFREQRESET_in;
  wire RXCDRHOLD_in;
  wire RXCDROVRDEN_in;
  wire RXCDRRESET_in;
  wire RXCHBONDEN_in;
  wire RXCHBONDMASTER_in;
  wire RXCHBONDSLAVE_in;
  wire RXCKCALRESET_in;
  wire RXCOMMADETEN_in;
  wire RXDFEAGCHOLD_in;
  wire RXDFEAGCOVRDEN_in;
  wire RXDFECFOKFEN_in;
  wire RXDFECFOKFPULSE_in;
  wire RXDFECFOKHOLD_in;
  wire RXDFECFOKOVREN_in;
  wire RXDFEKHHOLD_in;
  wire RXDFEKHOVRDEN_in;
  wire RXDFELFHOLD_in;
  wire RXDFELFOVRDEN_in;
  wire RXDFELPMRESET_in;
  wire RXDFETAP10HOLD_in;
  wire RXDFETAP10OVRDEN_in;
  wire RXDFETAP11HOLD_in;
  wire RXDFETAP11OVRDEN_in;
  wire RXDFETAP12HOLD_in;
  wire RXDFETAP12OVRDEN_in;
  wire RXDFETAP13HOLD_in;
  wire RXDFETAP13OVRDEN_in;
  wire RXDFETAP14HOLD_in;
  wire RXDFETAP14OVRDEN_in;
  wire RXDFETAP15HOLD_in;
  wire RXDFETAP15OVRDEN_in;
  wire RXDFETAP2HOLD_in;
  wire RXDFETAP2OVRDEN_in;
  wire RXDFETAP3HOLD_in;
  wire RXDFETAP3OVRDEN_in;
  wire RXDFETAP4HOLD_in;
  wire RXDFETAP4OVRDEN_in;
  wire RXDFETAP5HOLD_in;
  wire RXDFETAP5OVRDEN_in;
  wire RXDFETAP6HOLD_in;
  wire RXDFETAP6OVRDEN_in;
  wire RXDFETAP7HOLD_in;
  wire RXDFETAP7OVRDEN_in;
  wire RXDFETAP8HOLD_in;
  wire RXDFETAP8OVRDEN_in;
  wire RXDFETAP9HOLD_in;
  wire RXDFETAP9OVRDEN_in;
  wire RXDFEUTHOLD_in;
  wire RXDFEUTOVRDEN_in;
  wire RXDFEVPHOLD_in;
  wire RXDFEVPOVRDEN_in;
  wire RXDFEXYDEN_in;
  wire RXDLYBYPASS_in;
  wire RXDLYEN_in;
  wire RXDLYOVRDEN_in;
  wire RXDLYSRESET_in;
  wire RXEQTRAINING_in;
  wire RXGEARBOXSLIP_in;
  wire RXLATCLK_in;
  wire RXLPMEN_in;
  wire RXLPMGCHOLD_in;
  wire RXLPMGCOVRDEN_in;
  wire RXLPMHFHOLD_in;
  wire RXLPMHFOVRDEN_in;
  wire RXLPMLFHOLD_in;
  wire RXLPMLFKLOVRDEN_in;
  wire RXLPMOSHOLD_in;
  wire RXLPMOSOVRDEN_in;
  wire RXMCOMMAALIGNEN_in;
  wire RXOOBRESET_in;
  wire RXOSCALRESET_in;
  wire RXOSHOLD_in;
  wire RXOSOVRDEN_in;
  wire RXPCOMMAALIGNEN_in;
  wire RXPCSRESET_in;
  wire RXPHALIGNEN_in;
  wire RXPHALIGN_in;
  wire RXPHDLYPD_in;
  wire RXPHDLYRESET_in;
  wire RXPMARESET_in;
  wire RXPOLARITY_in;
  wire RXPRBSCNTRESET_in;
  wire RXPROGDIVRESET_in;
  wire RXRATEMODE_in;
  wire RXSLIDE_in;
  wire RXSLIPOUTCLK_in;
  wire RXSLIPPMA_in;
  wire RXSYNCALLIN_in;
  wire RXSYNCIN_in;
  wire RXSYNCMODE_in;
  wire RXTERMINATION_in;
  wire RXUSERRDY_in;
  wire RXUSRCLK2_in;
  wire RXUSRCLK_in;
  wire SARCCLK_in;
  wire SCANCLK_in;
  wire SCANENB_in;
  wire SCANMODEB_in;
  wire SCANRSTB_in;
  wire SCANRSTEN_in;
  wire SIGVALIDCLK_in;
  wire TSTCLK0_in;
  wire TSTCLK1_in;
  wire TSTPDOVRDB_in;
  wire TX8B10BEN_in;
  wire TXCOMINIT_in;
  wire TXCOMSAS_in;
  wire TXCOMWAKE_in;
  wire TXDCCFORCESTART_in;
  wire TXDCCRESET_in;
  wire TXDETECTRX_in;
  wire TXDLYBYPASS_in;
  wire TXDLYEN_in;
  wire TXDLYHOLD_in;
  wire TXDLYOVRDEN_in;
  wire TXDLYSRESET_in;
  wire TXDLYUPDOWN_in;
  wire TXELECIDLE_in;
  wire TXINHIBIT_in;
  wire TXLATCLK_in;
  wire TXLFPSTRESET_in;
  wire TXLFPSU2LPEXIT_in;
  wire TXLFPSU3WAKE_in;
  wire TXMUXDCDEXHOLD_in;
  wire TXMUXDCDORWREN_in;
  wire TXONESZEROS_in;
  wire TXPCSRESET_in;
  wire TXPDELECIDLEMODE_in;
  wire TXPHALIGNEN_in;
  wire TXPHALIGN_in;
  wire TXPHDLYPD_in;
  wire TXPHDLYRESET_in;
  wire TXPHDLYTSTCLK_in;
  wire TXPHINIT_in;
  wire TXPHOVRDEN_in;
  wire TXPIPPMEN_in;
  wire TXPIPPMOVRDEN_in;
  wire TXPIPPMPD_in;
  wire TXPIPPMSEL_in;
  wire TXPISOPD_in;
  wire TXPMARESET_in;
  wire TXPOLARITY_in;
  wire TXPRBSFORCEERR_in;
  wire TXPROGDIVRESET_in;
  wire TXRATEMODE_in;
  wire TXSWING_in;
  wire TXSYNCALLIN_in;
  wire TXSYNCIN_in;
  wire TXSYNCMODE_in;
  wire TXUSERRDY_in;
  wire TXUSRCLK2_in;
  wire TXUSRCLK_in;
  wire [127:0] TXDATA_in;
  wire [15:0] DRPDI_in;
  wire [15:0] GTRSVD_in;
  wire [15:0] PCSRSVDIN_in;
  wire [15:0] TXCTRL0_in;
  wire [15:0] TXCTRL1_in;
  wire [17:0] PMASCANIN_in;
  wire [18:0] SCANIN_in;
  wire [19:0] TSTIN_in;
  wire [1:0] RXELECIDLEMODE_in;
  wire [1:0] RXMONITORSEL_in;
  wire [1:0] RXPD_in;
  wire [1:0] RXPLLCLKSEL_in;
  wire [1:0] RXSYSCLKSEL_in;
  wire [1:0] TXDEEMPH_in;
  wire [1:0] TXPD_in;
  wire [1:0] TXPLLCLKSEL_in;
  wire [1:0] TXSYSCLKSEL_in;
  wire [2:0] CPLLREFCLKSEL_in;
  wire [2:0] LOOPBACK_in;
  wire [2:0] RXCHBONDLEVEL_in;
  wire [2:0] RXOUTCLKSEL_in;
  wire [2:0] RXRATE_in;
  wire [2:0] TXMARGIN_in;
  wire [2:0] TXOUTCLKSEL_in;
  wire [2:0] TXRATE_in;
  wire [3:0] RXDFECFOKFCNUM_in;
  wire [3:0] RXPRBSSEL_in;
  wire [3:0] TXPRBSSEL_in;
  wire [4:0] RXCHBONDI_in;
  wire [4:0] TSTPD_in;
  wire [4:0] TXDIFFCTRL_in;
  wire [4:0] TXPIPPMSTEPSIZE_in;
  wire [4:0] TXPOSTCURSOR_in;
  wire [4:0] TXPRECURSOR_in;
  wire [5:0] TXHEADER_in;
  wire [6:0] RXCKCALSTART_in;
  wire [6:0] TXMAINCURSOR_in;
  wire [6:0] TXSEQUENCE_in;
  wire [7:0] TX8B10BBYPASS_in;
  wire [7:0] TXCTRL2_in;
  wire [7:0] TXDATAEXTENDRSVD_in;
  wire [9:0] DRPADDR_in;

  wire gt_intclk; 
  reg gt_clk_int;
  
`ifdef XIL_TIMING
  wire DRPCLK_delay;
  wire DRPEN_delay;
  wire DRPWE_delay;
  wire RX8B10BEN_delay;
  wire RXCHBONDEN_delay;
  wire RXCHBONDMASTER_delay;
  wire RXCHBONDSLAVE_delay;
  wire RXCOMMADETEN_delay;
  wire RXGEARBOXSLIP_delay;
  wire RXMCOMMAALIGNEN_delay;
  wire RXPCOMMAALIGNEN_delay;
  wire RXPOLARITY_delay;
  wire RXPRBSCNTRESET_delay;
  wire RXSLIDE_delay;
  wire RXSLIPOUTCLK_delay;
  wire RXSLIPPMA_delay;
  wire RXUSRCLK2_delay;
  wire RXUSRCLK_delay;
  wire TX8B10BEN_delay;
  wire TXCOMINIT_delay;
  wire TXCOMSAS_delay;
  wire TXCOMWAKE_delay;
  wire TXDETECTRX_delay;
  wire TXELECIDLE_delay;
  wire TXINHIBIT_delay;
  wire TXPOLARITY_delay;
  wire TXPRBSFORCEERR_delay;
  wire TXUSRCLK2_delay;
  wire [127:0] TXDATA_delay;
  wire [15:0] DRPDI_delay;
  wire [15:0] TXCTRL0_delay;
  wire [15:0] TXCTRL1_delay;
  wire [1:0] TXPD_delay;
  wire [2:0] RXCHBONDLEVEL_delay;
  wire [2:0] RXRATE_delay;
  wire [2:0] TXRATE_delay;
  wire [3:0] RXPRBSSEL_delay;
  wire [3:0] TXPRBSSEL_delay;
  wire [4:0] RXCHBONDI_delay;
  wire [5:0] TXHEADER_delay;
  wire [6:0] TXSEQUENCE_delay;
  wire [7:0] TX8B10BBYPASS_delay;
  wire [7:0] TXCTRL2_delay;
  wire [9:0] DRPADDR_delay;
`endif

  assign BUFGTCE = BUFGTCE_out;
  assign BUFGTCEMASK = BUFGTCEMASK_out;
  assign BUFGTDIV = BUFGTDIV_out;
  assign BUFGTRESET = BUFGTRESET_out;
  assign BUFGTRSTMASK = BUFGTRSTMASK_out;
  assign CPLLFBCLKLOST = CPLLFBCLKLOST_out;
  assign CPLLLOCK = CPLLLOCK_out;
  assign CPLLREFCLKLOST = CPLLREFCLKLOST_out;
  assign DMONITOROUT = DMONITOROUT_out;
  assign DMONITOROUTCLK = DMONITOROUTCLK_out;
  assign DRPDO = DRPDO_out;
  assign DRPRDY = DRPRDY_out;
  assign EYESCANDATAERROR = EYESCANDATAERROR_out;
  assign GTPOWERGOOD = GTPOWERGOOD_out;
  assign GTREFCLKMONITOR = GTREFCLKMONITOR_out;
  assign GTYTXN = GTYTXN_out;
  assign GTYTXP = GTYTXP_out;
  assign PCIERATEGEN3 = PCIERATEGEN3_out;
  assign PCIERATEIDLE = PCIERATEIDLE_out;
  assign PCIERATEQPLLPD = PCIERATEQPLLPD_out;
  assign PCIERATEQPLLRESET = PCIERATEQPLLRESET_out;
  assign PCIESYNCTXSYNCDONE = PCIESYNCTXSYNCDONE_out;
  assign PCIEUSERGEN3RDY = PCIEUSERGEN3RDY_out;
  assign PCIEUSERPHYSTATUSRST = PCIEUSERPHYSTATUSRST_out;
  assign PCIEUSERRATESTART = PCIEUSERRATESTART_out;
  assign PCSRSVDOUT = PCSRSVDOUT_out;
  assign PHYSTATUS = PHYSTATUS_out;
  assign PINRSRVDAS = PINRSRVDAS_out;
  assign POWERPRESENT = POWERPRESENT_out;
  assign RESETEXCEPTION = RESETEXCEPTION_out;
  assign RXBUFSTATUS = RXBUFSTATUS_out;
  assign RXBYTEISALIGNED = RXBYTEISALIGNED_out;
  assign RXBYTEREALIGN = RXBYTEREALIGN_out;
  assign RXCDRLOCK = RXCDRLOCK_out;
  assign RXCDRPHDONE = RXCDRPHDONE_out;
  assign RXCHANBONDSEQ = RXCHANBONDSEQ_out;
  assign RXCHANISALIGNED = RXCHANISALIGNED_out;
  assign RXCHANREALIGN = RXCHANREALIGN_out;
  assign RXCHBONDO = RXCHBONDO_out;
  assign RXCKCALDONE = RXCKCALDONE_out;
  assign RXCLKCORCNT = RXCLKCORCNT_out;
  assign RXCOMINITDET = RXCOMINITDET_out;
  assign RXCOMMADET = RXCOMMADET_out;
  assign RXCOMSASDET = RXCOMSASDET_out;
  assign RXCOMWAKEDET = RXCOMWAKEDET_out;
  assign RXCTRL0 = RXCTRL0_out;
  assign RXCTRL1 = RXCTRL1_out;
  assign RXCTRL2 = RXCTRL2_out;
  assign RXCTRL3 = RXCTRL3_out;
  assign RXDATA = RXDATA_out;
  assign RXDATAEXTENDRSVD = RXDATAEXTENDRSVD_out;
  assign RXDATAVALID = RXDATAVALID_out;
  assign RXDLYSRESETDONE = RXDLYSRESETDONE_out;
  assign RXELECIDLE = RXELECIDLE_out;
  assign RXHEADER = RXHEADER_out;
  assign RXHEADERVALID = RXHEADERVALID_out;
  assign RXLFPSTRESETDET = RXLFPSTRESETDET_out;
  assign RXLFPSU2LPEXITDET = RXLFPSU2LPEXITDET_out;
  assign RXLFPSU3WAKEDET = RXLFPSU3WAKEDET_out;
  assign RXMONITOROUT = RXMONITOROUT_out;
  assign RXOSINTDONE = RXOSINTDONE_out;
  assign RXOSINTSTARTED = RXOSINTSTARTED_out;
  assign RXOSINTSTROBEDONE = RXOSINTSTROBEDONE_out;
  assign RXOSINTSTROBESTARTED = RXOSINTSTROBESTARTED_out;
  assign RXOUTCLK = RXOUTCLK_out;
  assign RXOUTCLKFABRIC = RXOUTCLKFABRIC_out;

  //EL 
  //assign RXOUTCLKPCS = RXOUTCLKPCS_out;
  assign RXOUTCLKPCS = (RXPD_in == 2'b11) ? gt_intclk : RXOUTCLKPCS_out;

  assign RXPHALIGNDONE = RXPHALIGNDONE_out;
  assign RXPHALIGNERR = RXPHALIGNERR_out;
  assign RXPMARESETDONE = RXPMARESETDONE_out;
  assign RXPRBSERR = RXPRBSERR_out;
  assign RXPRBSLOCKED = RXPRBSLOCKED_out;
  assign RXPRGDIVRESETDONE = RXPRGDIVRESETDONE_out;
  assign RXRATEDONE = RXRATEDONE_out;
  assign RXRECCLKOUT = RXRECCLKOUT_out;
  assign RXRESETDONE = RXRESETDONE_out;
  assign RXSLIDERDY = RXSLIDERDY_out;
  assign RXSLIPDONE = RXSLIPDONE_out;
  assign RXSLIPOUTCLKRDY = RXSLIPOUTCLKRDY_out;
  assign RXSLIPPMARDY = RXSLIPPMARDY_out;
  assign RXSTARTOFSEQ = RXSTARTOFSEQ_out;
  assign RXSTATUS = RXSTATUS_out;
  assign RXSYNCDONE = RXSYNCDONE_out;
  assign RXSYNCOUT = RXSYNCOUT_out;
  assign RXVALID = RXVALID_out;
  assign TXBUFSTATUS = TXBUFSTATUS_out;
  assign TXCOMFINISH = TXCOMFINISH_out;
  assign TXDCCDONE = TXDCCDONE_out;
  assign TXDLYSRESETDONE = TXDLYSRESETDONE_out;

  //EL
  //assign TXOUTCLK = TXOUTCLK_out;
  assign TXOUTCLK = (TXPISOPD_in && TXOUTCLKSEL_in == 3'b101) ? gt_intclk : TXOUTCLK_out;

  assign TXOUTCLKFABRIC = TXOUTCLKFABRIC_out;
  assign TXOUTCLKPCS = TXPISOPD_in ? gt_intclk : TXOUTCLKPCS_out;
  assign TXPHALIGNDONE = TXPHALIGNDONE_out;
  assign TXPHINITDONE = TXPHINITDONE_out;
  assign TXPMARESETDONE = TXPMARESETDONE_out;
  assign TXPRGDIVRESETDONE = TXPRGDIVRESETDONE_out;
  assign TXRATEDONE = TXRATEDONE_out;
  assign TXRESETDONE = TXRESETDONE_out;
  assign TXSYNCDONE = TXSYNCDONE_out;
  assign TXSYNCOUT = TXSYNCOUT_out;

`ifdef XIL_TIMING
  assign DRPADDR_in[0] = (DRPADDR[0] !== 1'bz) && DRPADDR_delay[0]; // rv 0
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
  assign RX8B10BEN_in = (RX8B10BEN !== 1'bz) && RX8B10BEN_delay; // rv 0
  assign RXCHBONDEN_in = (RXCHBONDEN !== 1'bz) && RXCHBONDEN_delay; // rv 0
  assign RXCHBONDI_in[0] = (RXCHBONDI[0] !== 1'bz) && RXCHBONDI_delay[0]; // rv 0
  assign RXCHBONDI_in[1] = (RXCHBONDI[1] !== 1'bz) && RXCHBONDI_delay[1]; // rv 0
  assign RXCHBONDI_in[2] = (RXCHBONDI[2] !== 1'bz) && RXCHBONDI_delay[2]; // rv 0
  assign RXCHBONDI_in[3] = (RXCHBONDI[3] !== 1'bz) && RXCHBONDI_delay[3]; // rv 0
  assign RXCHBONDI_in[4] = (RXCHBONDI[4] !== 1'bz) && RXCHBONDI_delay[4]; // rv 0
  assign RXCHBONDLEVEL_in[0] = (RXCHBONDLEVEL[0] !== 1'bz) && RXCHBONDLEVEL_delay[0]; // rv 0
  assign RXCHBONDLEVEL_in[1] = (RXCHBONDLEVEL[1] !== 1'bz) && RXCHBONDLEVEL_delay[1]; // rv 0
  assign RXCHBONDLEVEL_in[2] = (RXCHBONDLEVEL[2] !== 1'bz) && RXCHBONDLEVEL_delay[2]; // rv 0
  assign RXCHBONDMASTER_in = (RXCHBONDMASTER !== 1'bz) && RXCHBONDMASTER_delay; // rv 0
  assign RXCHBONDSLAVE_in = (RXCHBONDSLAVE !== 1'bz) && RXCHBONDSLAVE_delay; // rv 0
  assign RXCOMMADETEN_in = (RXCOMMADETEN !== 1'bz) && RXCOMMADETEN_delay; // rv 0
  assign RXGEARBOXSLIP_in = (RXGEARBOXSLIP !== 1'bz) && RXGEARBOXSLIP_delay; // rv 0
  assign RXMCOMMAALIGNEN_in = (RXMCOMMAALIGNEN !== 1'bz) && RXMCOMMAALIGNEN_delay; // rv 0
  assign RXPCOMMAALIGNEN_in = (RXPCOMMAALIGNEN !== 1'bz) && RXPCOMMAALIGNEN_delay; // rv 0
  assign RXPOLARITY_in = (RXPOLARITY !== 1'bz) && RXPOLARITY_delay; // rv 0
  assign RXPRBSCNTRESET_in = (RXPRBSCNTRESET !== 1'bz) && RXPRBSCNTRESET_delay; // rv 0
  assign RXPRBSSEL_in[0] = (RXPRBSSEL[0] !== 1'bz) && RXPRBSSEL_delay[0]; // rv 0
  assign RXPRBSSEL_in[1] = (RXPRBSSEL[1] !== 1'bz) && RXPRBSSEL_delay[1]; // rv 0
  assign RXPRBSSEL_in[2] = (RXPRBSSEL[2] !== 1'bz) && RXPRBSSEL_delay[2]; // rv 0
  assign RXPRBSSEL_in[3] = (RXPRBSSEL[3] !== 1'bz) && RXPRBSSEL_delay[3]; // rv 0
  assign RXRATE_in[0] = (RXRATE[0] !== 1'bz) && RXRATE_delay[0]; // rv 0
  assign RXRATE_in[1] = (RXRATE[1] !== 1'bz) && RXRATE_delay[1]; // rv 0
  assign RXRATE_in[2] = (RXRATE[2] !== 1'bz) && RXRATE_delay[2]; // rv 0
  assign RXSLIDE_in = (RXSLIDE !== 1'bz) && RXSLIDE_delay; // rv 0
  assign RXSLIPOUTCLK_in = (RXSLIPOUTCLK !== 1'bz) && RXSLIPOUTCLK_delay; // rv 0
  assign RXSLIPPMA_in = (RXSLIPPMA !== 1'bz) && RXSLIPPMA_delay; // rv 0
  assign RXUSRCLK2_in = (RXUSRCLK2 !== 1'bz) && RXUSRCLK2_delay; // rv 0
  assign RXUSRCLK_in = (RXUSRCLK !== 1'bz) && RXUSRCLK_delay; // rv 0
  assign TX8B10BBYPASS_in[0] = (TX8B10BBYPASS[0] !== 1'bz) && TX8B10BBYPASS_delay[0]; // rv 0
  assign TX8B10BBYPASS_in[1] = (TX8B10BBYPASS[1] !== 1'bz) && TX8B10BBYPASS_delay[1]; // rv 0
  assign TX8B10BBYPASS_in[2] = (TX8B10BBYPASS[2] !== 1'bz) && TX8B10BBYPASS_delay[2]; // rv 0
  assign TX8B10BBYPASS_in[3] = (TX8B10BBYPASS[3] !== 1'bz) && TX8B10BBYPASS_delay[3]; // rv 0
  assign TX8B10BBYPASS_in[4] = (TX8B10BBYPASS[4] !== 1'bz) && TX8B10BBYPASS_delay[4]; // rv 0
  assign TX8B10BBYPASS_in[5] = (TX8B10BBYPASS[5] !== 1'bz) && TX8B10BBYPASS_delay[5]; // rv 0
  assign TX8B10BBYPASS_in[6] = (TX8B10BBYPASS[6] !== 1'bz) && TX8B10BBYPASS_delay[6]; // rv 0
  assign TX8B10BBYPASS_in[7] = (TX8B10BBYPASS[7] !== 1'bz) && TX8B10BBYPASS_delay[7]; // rv 0
  assign TX8B10BEN_in = (TX8B10BEN !== 1'bz) && TX8B10BEN_delay; // rv 0
  assign TXCOMINIT_in = (TXCOMINIT !== 1'bz) && TXCOMINIT_delay; // rv 0
  assign TXCOMSAS_in = (TXCOMSAS !== 1'bz) && TXCOMSAS_delay; // rv 0
  assign TXCOMWAKE_in = (TXCOMWAKE !== 1'bz) && TXCOMWAKE_delay; // rv 0
  assign TXCTRL0_in[0] = (TXCTRL0[0] !== 1'bz) && TXCTRL0_delay[0]; // rv 0
  assign TXCTRL0_in[10] = (TXCTRL0[10] !== 1'bz) && TXCTRL0_delay[10]; // rv 0
  assign TXCTRL0_in[11] = (TXCTRL0[11] !== 1'bz) && TXCTRL0_delay[11]; // rv 0
  assign TXCTRL0_in[12] = (TXCTRL0[12] !== 1'bz) && TXCTRL0_delay[12]; // rv 0
  assign TXCTRL0_in[13] = (TXCTRL0[13] !== 1'bz) && TXCTRL0_delay[13]; // rv 0
  assign TXCTRL0_in[14] = (TXCTRL0[14] !== 1'bz) && TXCTRL0_delay[14]; // rv 0
  assign TXCTRL0_in[15] = (TXCTRL0[15] !== 1'bz) && TXCTRL0_delay[15]; // rv 0
  assign TXCTRL0_in[1] = (TXCTRL0[1] !== 1'bz) && TXCTRL0_delay[1]; // rv 0
  assign TXCTRL0_in[2] = (TXCTRL0[2] !== 1'bz) && TXCTRL0_delay[2]; // rv 0
  assign TXCTRL0_in[3] = (TXCTRL0[3] !== 1'bz) && TXCTRL0_delay[3]; // rv 0
  assign TXCTRL0_in[4] = (TXCTRL0[4] !== 1'bz) && TXCTRL0_delay[4]; // rv 0
  assign TXCTRL0_in[5] = (TXCTRL0[5] !== 1'bz) && TXCTRL0_delay[5]; // rv 0
  assign TXCTRL0_in[6] = (TXCTRL0[6] !== 1'bz) && TXCTRL0_delay[6]; // rv 0
  assign TXCTRL0_in[7] = (TXCTRL0[7] !== 1'bz) && TXCTRL0_delay[7]; // rv 0
  assign TXCTRL0_in[8] = (TXCTRL0[8] !== 1'bz) && TXCTRL0_delay[8]; // rv 0
  assign TXCTRL0_in[9] = (TXCTRL0[9] !== 1'bz) && TXCTRL0_delay[9]; // rv 0
  assign TXCTRL1_in[0] = (TXCTRL1[0] !== 1'bz) && TXCTRL1_delay[0]; // rv 0
  assign TXCTRL1_in[10] = (TXCTRL1[10] !== 1'bz) && TXCTRL1_delay[10]; // rv 0
  assign TXCTRL1_in[11] = (TXCTRL1[11] !== 1'bz) && TXCTRL1_delay[11]; // rv 0
  assign TXCTRL1_in[12] = (TXCTRL1[12] !== 1'bz) && TXCTRL1_delay[12]; // rv 0
  assign TXCTRL1_in[13] = (TXCTRL1[13] !== 1'bz) && TXCTRL1_delay[13]; // rv 0
  assign TXCTRL1_in[14] = (TXCTRL1[14] !== 1'bz) && TXCTRL1_delay[14]; // rv 0
  assign TXCTRL1_in[15] = (TXCTRL1[15] !== 1'bz) && TXCTRL1_delay[15]; // rv 0
  assign TXCTRL1_in[1] = (TXCTRL1[1] !== 1'bz) && TXCTRL1_delay[1]; // rv 0
  assign TXCTRL1_in[2] = (TXCTRL1[2] !== 1'bz) && TXCTRL1_delay[2]; // rv 0
  assign TXCTRL1_in[3] = (TXCTRL1[3] !== 1'bz) && TXCTRL1_delay[3]; // rv 0
  assign TXCTRL1_in[4] = (TXCTRL1[4] !== 1'bz) && TXCTRL1_delay[4]; // rv 0
  assign TXCTRL1_in[5] = (TXCTRL1[5] !== 1'bz) && TXCTRL1_delay[5]; // rv 0
  assign TXCTRL1_in[6] = (TXCTRL1[6] !== 1'bz) && TXCTRL1_delay[6]; // rv 0
  assign TXCTRL1_in[7] = (TXCTRL1[7] !== 1'bz) && TXCTRL1_delay[7]; // rv 0
  assign TXCTRL1_in[8] = (TXCTRL1[8] !== 1'bz) && TXCTRL1_delay[8]; // rv 0
  assign TXCTRL1_in[9] = (TXCTRL1[9] !== 1'bz) && TXCTRL1_delay[9]; // rv 0
  assign TXCTRL2_in[0] = (TXCTRL2[0] !== 1'bz) && TXCTRL2_delay[0]; // rv 0
  assign TXCTRL2_in[1] = (TXCTRL2[1] !== 1'bz) && TXCTRL2_delay[1]; // rv 0
  assign TXCTRL2_in[2] = (TXCTRL2[2] !== 1'bz) && TXCTRL2_delay[2]; // rv 0
  assign TXCTRL2_in[3] = (TXCTRL2[3] !== 1'bz) && TXCTRL2_delay[3]; // rv 0
  assign TXCTRL2_in[4] = (TXCTRL2[4] !== 1'bz) && TXCTRL2_delay[4]; // rv 0
  assign TXCTRL2_in[5] = (TXCTRL2[5] !== 1'bz) && TXCTRL2_delay[5]; // rv 0
  assign TXCTRL2_in[6] = (TXCTRL2[6] !== 1'bz) && TXCTRL2_delay[6]; // rv 0
  assign TXCTRL2_in[7] = (TXCTRL2[7] !== 1'bz) && TXCTRL2_delay[7]; // rv 0
  assign TXDATA_in[0] = (TXDATA[0] !== 1'bz) && TXDATA_delay[0]; // rv 0
  assign TXDATA_in[100] = (TXDATA[100] !== 1'bz) && TXDATA_delay[100]; // rv 0
  assign TXDATA_in[101] = (TXDATA[101] !== 1'bz) && TXDATA_delay[101]; // rv 0
  assign TXDATA_in[102] = (TXDATA[102] !== 1'bz) && TXDATA_delay[102]; // rv 0
  assign TXDATA_in[103] = (TXDATA[103] !== 1'bz) && TXDATA_delay[103]; // rv 0
  assign TXDATA_in[104] = (TXDATA[104] !== 1'bz) && TXDATA_delay[104]; // rv 0
  assign TXDATA_in[105] = (TXDATA[105] !== 1'bz) && TXDATA_delay[105]; // rv 0
  assign TXDATA_in[106] = (TXDATA[106] !== 1'bz) && TXDATA_delay[106]; // rv 0
  assign TXDATA_in[107] = (TXDATA[107] !== 1'bz) && TXDATA_delay[107]; // rv 0
  assign TXDATA_in[108] = (TXDATA[108] !== 1'bz) && TXDATA_delay[108]; // rv 0
  assign TXDATA_in[109] = (TXDATA[109] !== 1'bz) && TXDATA_delay[109]; // rv 0
  assign TXDATA_in[10] = (TXDATA[10] !== 1'bz) && TXDATA_delay[10]; // rv 0
  assign TXDATA_in[110] = (TXDATA[110] !== 1'bz) && TXDATA_delay[110]; // rv 0
  assign TXDATA_in[111] = (TXDATA[111] !== 1'bz) && TXDATA_delay[111]; // rv 0
  assign TXDATA_in[112] = (TXDATA[112] !== 1'bz) && TXDATA_delay[112]; // rv 0
  assign TXDATA_in[113] = (TXDATA[113] !== 1'bz) && TXDATA_delay[113]; // rv 0
  assign TXDATA_in[114] = (TXDATA[114] !== 1'bz) && TXDATA_delay[114]; // rv 0
  assign TXDATA_in[115] = (TXDATA[115] !== 1'bz) && TXDATA_delay[115]; // rv 0
  assign TXDATA_in[116] = (TXDATA[116] !== 1'bz) && TXDATA_delay[116]; // rv 0
  assign TXDATA_in[117] = (TXDATA[117] !== 1'bz) && TXDATA_delay[117]; // rv 0
  assign TXDATA_in[118] = (TXDATA[118] !== 1'bz) && TXDATA_delay[118]; // rv 0
  assign TXDATA_in[119] = (TXDATA[119] !== 1'bz) && TXDATA_delay[119]; // rv 0
  assign TXDATA_in[11] = (TXDATA[11] !== 1'bz) && TXDATA_delay[11]; // rv 0
  assign TXDATA_in[120] = (TXDATA[120] !== 1'bz) && TXDATA_delay[120]; // rv 0
  assign TXDATA_in[121] = (TXDATA[121] !== 1'bz) && TXDATA_delay[121]; // rv 0
  assign TXDATA_in[122] = (TXDATA[122] !== 1'bz) && TXDATA_delay[122]; // rv 0
  assign TXDATA_in[123] = (TXDATA[123] !== 1'bz) && TXDATA_delay[123]; // rv 0
  assign TXDATA_in[124] = (TXDATA[124] !== 1'bz) && TXDATA_delay[124]; // rv 0
  assign TXDATA_in[125] = (TXDATA[125] !== 1'bz) && TXDATA_delay[125]; // rv 0
  assign TXDATA_in[126] = (TXDATA[126] !== 1'bz) && TXDATA_delay[126]; // rv 0
  assign TXDATA_in[127] = (TXDATA[127] !== 1'bz) && TXDATA_delay[127]; // rv 0
  assign TXDATA_in[12] = (TXDATA[12] !== 1'bz) && TXDATA_delay[12]; // rv 0
  assign TXDATA_in[13] = (TXDATA[13] !== 1'bz) && TXDATA_delay[13]; // rv 0
  assign TXDATA_in[14] = (TXDATA[14] !== 1'bz) && TXDATA_delay[14]; // rv 0
  assign TXDATA_in[15] = (TXDATA[15] !== 1'bz) && TXDATA_delay[15]; // rv 0
  assign TXDATA_in[16] = (TXDATA[16] !== 1'bz) && TXDATA_delay[16]; // rv 0
  assign TXDATA_in[17] = (TXDATA[17] !== 1'bz) && TXDATA_delay[17]; // rv 0
  assign TXDATA_in[18] = (TXDATA[18] !== 1'bz) && TXDATA_delay[18]; // rv 0
  assign TXDATA_in[19] = (TXDATA[19] !== 1'bz) && TXDATA_delay[19]; // rv 0
  assign TXDATA_in[1] = (TXDATA[1] !== 1'bz) && TXDATA_delay[1]; // rv 0
  assign TXDATA_in[20] = (TXDATA[20] !== 1'bz) && TXDATA_delay[20]; // rv 0
  assign TXDATA_in[21] = (TXDATA[21] !== 1'bz) && TXDATA_delay[21]; // rv 0
  assign TXDATA_in[22] = (TXDATA[22] !== 1'bz) && TXDATA_delay[22]; // rv 0
  assign TXDATA_in[23] = (TXDATA[23] !== 1'bz) && TXDATA_delay[23]; // rv 0
  assign TXDATA_in[24] = (TXDATA[24] !== 1'bz) && TXDATA_delay[24]; // rv 0
  assign TXDATA_in[25] = (TXDATA[25] !== 1'bz) && TXDATA_delay[25]; // rv 0
  assign TXDATA_in[26] = (TXDATA[26] !== 1'bz) && TXDATA_delay[26]; // rv 0
  assign TXDATA_in[27] = (TXDATA[27] !== 1'bz) && TXDATA_delay[27]; // rv 0
  assign TXDATA_in[28] = (TXDATA[28] !== 1'bz) && TXDATA_delay[28]; // rv 0
  assign TXDATA_in[29] = (TXDATA[29] !== 1'bz) && TXDATA_delay[29]; // rv 0
  assign TXDATA_in[2] = (TXDATA[2] !== 1'bz) && TXDATA_delay[2]; // rv 0
  assign TXDATA_in[30] = (TXDATA[30] !== 1'bz) && TXDATA_delay[30]; // rv 0
  assign TXDATA_in[31] = (TXDATA[31] !== 1'bz) && TXDATA_delay[31]; // rv 0
  assign TXDATA_in[32] = (TXDATA[32] !== 1'bz) && TXDATA_delay[32]; // rv 0
  assign TXDATA_in[33] = (TXDATA[33] !== 1'bz) && TXDATA_delay[33]; // rv 0
  assign TXDATA_in[34] = (TXDATA[34] !== 1'bz) && TXDATA_delay[34]; // rv 0
  assign TXDATA_in[35] = (TXDATA[35] !== 1'bz) && TXDATA_delay[35]; // rv 0
  assign TXDATA_in[36] = (TXDATA[36] !== 1'bz) && TXDATA_delay[36]; // rv 0
  assign TXDATA_in[37] = (TXDATA[37] !== 1'bz) && TXDATA_delay[37]; // rv 0
  assign TXDATA_in[38] = (TXDATA[38] !== 1'bz) && TXDATA_delay[38]; // rv 0
  assign TXDATA_in[39] = (TXDATA[39] !== 1'bz) && TXDATA_delay[39]; // rv 0
  assign TXDATA_in[3] = (TXDATA[3] !== 1'bz) && TXDATA_delay[3]; // rv 0
  assign TXDATA_in[40] = (TXDATA[40] !== 1'bz) && TXDATA_delay[40]; // rv 0
  assign TXDATA_in[41] = (TXDATA[41] !== 1'bz) && TXDATA_delay[41]; // rv 0
  assign TXDATA_in[42] = (TXDATA[42] !== 1'bz) && TXDATA_delay[42]; // rv 0
  assign TXDATA_in[43] = (TXDATA[43] !== 1'bz) && TXDATA_delay[43]; // rv 0
  assign TXDATA_in[44] = (TXDATA[44] !== 1'bz) && TXDATA_delay[44]; // rv 0
  assign TXDATA_in[45] = (TXDATA[45] !== 1'bz) && TXDATA_delay[45]; // rv 0
  assign TXDATA_in[46] = (TXDATA[46] !== 1'bz) && TXDATA_delay[46]; // rv 0
  assign TXDATA_in[47] = (TXDATA[47] !== 1'bz) && TXDATA_delay[47]; // rv 0
  assign TXDATA_in[48] = (TXDATA[48] !== 1'bz) && TXDATA_delay[48]; // rv 0
  assign TXDATA_in[49] = (TXDATA[49] !== 1'bz) && TXDATA_delay[49]; // rv 0
  assign TXDATA_in[4] = (TXDATA[4] !== 1'bz) && TXDATA_delay[4]; // rv 0
  assign TXDATA_in[50] = (TXDATA[50] !== 1'bz) && TXDATA_delay[50]; // rv 0
  assign TXDATA_in[51] = (TXDATA[51] !== 1'bz) && TXDATA_delay[51]; // rv 0
  assign TXDATA_in[52] = (TXDATA[52] !== 1'bz) && TXDATA_delay[52]; // rv 0
  assign TXDATA_in[53] = (TXDATA[53] !== 1'bz) && TXDATA_delay[53]; // rv 0
  assign TXDATA_in[54] = (TXDATA[54] !== 1'bz) && TXDATA_delay[54]; // rv 0
  assign TXDATA_in[55] = (TXDATA[55] !== 1'bz) && TXDATA_delay[55]; // rv 0
  assign TXDATA_in[56] = (TXDATA[56] !== 1'bz) && TXDATA_delay[56]; // rv 0
  assign TXDATA_in[57] = (TXDATA[57] !== 1'bz) && TXDATA_delay[57]; // rv 0
  assign TXDATA_in[58] = (TXDATA[58] !== 1'bz) && TXDATA_delay[58]; // rv 0
  assign TXDATA_in[59] = (TXDATA[59] !== 1'bz) && TXDATA_delay[59]; // rv 0
  assign TXDATA_in[5] = (TXDATA[5] !== 1'bz) && TXDATA_delay[5]; // rv 0
  assign TXDATA_in[60] = (TXDATA[60] !== 1'bz) && TXDATA_delay[60]; // rv 0
  assign TXDATA_in[61] = (TXDATA[61] !== 1'bz) && TXDATA_delay[61]; // rv 0
  assign TXDATA_in[62] = (TXDATA[62] !== 1'bz) && TXDATA_delay[62]; // rv 0
  assign TXDATA_in[63] = (TXDATA[63] !== 1'bz) && TXDATA_delay[63]; // rv 0
  assign TXDATA_in[64] = (TXDATA[64] !== 1'bz) && TXDATA_delay[64]; // rv 0
  assign TXDATA_in[65] = (TXDATA[65] !== 1'bz) && TXDATA_delay[65]; // rv 0
  assign TXDATA_in[66] = (TXDATA[66] !== 1'bz) && TXDATA_delay[66]; // rv 0
  assign TXDATA_in[67] = (TXDATA[67] !== 1'bz) && TXDATA_delay[67]; // rv 0
  assign TXDATA_in[68] = (TXDATA[68] !== 1'bz) && TXDATA_delay[68]; // rv 0
  assign TXDATA_in[69] = (TXDATA[69] !== 1'bz) && TXDATA_delay[69]; // rv 0
  assign TXDATA_in[6] = (TXDATA[6] !== 1'bz) && TXDATA_delay[6]; // rv 0
  assign TXDATA_in[70] = (TXDATA[70] !== 1'bz) && TXDATA_delay[70]; // rv 0
  assign TXDATA_in[71] = (TXDATA[71] !== 1'bz) && TXDATA_delay[71]; // rv 0
  assign TXDATA_in[72] = (TXDATA[72] !== 1'bz) && TXDATA_delay[72]; // rv 0
  assign TXDATA_in[73] = (TXDATA[73] !== 1'bz) && TXDATA_delay[73]; // rv 0
  assign TXDATA_in[74] = (TXDATA[74] !== 1'bz) && TXDATA_delay[74]; // rv 0
  assign TXDATA_in[75] = (TXDATA[75] !== 1'bz) && TXDATA_delay[75]; // rv 0
  assign TXDATA_in[76] = (TXDATA[76] !== 1'bz) && TXDATA_delay[76]; // rv 0
  assign TXDATA_in[77] = (TXDATA[77] !== 1'bz) && TXDATA_delay[77]; // rv 0
  assign TXDATA_in[78] = (TXDATA[78] !== 1'bz) && TXDATA_delay[78]; // rv 0
  assign TXDATA_in[79] = (TXDATA[79] !== 1'bz) && TXDATA_delay[79]; // rv 0
  assign TXDATA_in[7] = (TXDATA[7] !== 1'bz) && TXDATA_delay[7]; // rv 0
  assign TXDATA_in[80] = (TXDATA[80] !== 1'bz) && TXDATA_delay[80]; // rv 0
  assign TXDATA_in[81] = (TXDATA[81] !== 1'bz) && TXDATA_delay[81]; // rv 0
  assign TXDATA_in[82] = (TXDATA[82] !== 1'bz) && TXDATA_delay[82]; // rv 0
  assign TXDATA_in[83] = (TXDATA[83] !== 1'bz) && TXDATA_delay[83]; // rv 0
  assign TXDATA_in[84] = (TXDATA[84] !== 1'bz) && TXDATA_delay[84]; // rv 0
  assign TXDATA_in[85] = (TXDATA[85] !== 1'bz) && TXDATA_delay[85]; // rv 0
  assign TXDATA_in[86] = (TXDATA[86] !== 1'bz) && TXDATA_delay[86]; // rv 0
  assign TXDATA_in[87] = (TXDATA[87] !== 1'bz) && TXDATA_delay[87]; // rv 0
  assign TXDATA_in[88] = (TXDATA[88] !== 1'bz) && TXDATA_delay[88]; // rv 0
  assign TXDATA_in[89] = (TXDATA[89] !== 1'bz) && TXDATA_delay[89]; // rv 0
  assign TXDATA_in[8] = (TXDATA[8] !== 1'bz) && TXDATA_delay[8]; // rv 0
  assign TXDATA_in[90] = (TXDATA[90] !== 1'bz) && TXDATA_delay[90]; // rv 0
  assign TXDATA_in[91] = (TXDATA[91] !== 1'bz) && TXDATA_delay[91]; // rv 0
  assign TXDATA_in[92] = (TXDATA[92] !== 1'bz) && TXDATA_delay[92]; // rv 0
  assign TXDATA_in[93] = (TXDATA[93] !== 1'bz) && TXDATA_delay[93]; // rv 0
  assign TXDATA_in[94] = (TXDATA[94] !== 1'bz) && TXDATA_delay[94]; // rv 0
  assign TXDATA_in[95] = (TXDATA[95] !== 1'bz) && TXDATA_delay[95]; // rv 0
  assign TXDATA_in[96] = (TXDATA[96] !== 1'bz) && TXDATA_delay[96]; // rv 0
  assign TXDATA_in[97] = (TXDATA[97] !== 1'bz) && TXDATA_delay[97]; // rv 0
  assign TXDATA_in[98] = (TXDATA[98] !== 1'bz) && TXDATA_delay[98]; // rv 0
  assign TXDATA_in[99] = (TXDATA[99] !== 1'bz) && TXDATA_delay[99]; // rv 0
  assign TXDATA_in[9] = (TXDATA[9] !== 1'bz) && TXDATA_delay[9]; // rv 0
  assign TXDETECTRX_in = (TXDETECTRX !== 1'bz) && TXDETECTRX_delay; // rv 0
  assign TXELECIDLE_in = (TXELECIDLE !== 1'bz) && TXELECIDLE_delay; // rv 0
  assign TXHEADER_in[0] = (TXHEADER[0] !== 1'bz) && TXHEADER_delay[0]; // rv 0
  assign TXHEADER_in[1] = (TXHEADER[1] !== 1'bz) && TXHEADER_delay[1]; // rv 0
  assign TXHEADER_in[2] = (TXHEADER[2] !== 1'bz) && TXHEADER_delay[2]; // rv 0
  assign TXHEADER_in[3] = (TXHEADER[3] !== 1'bz) && TXHEADER_delay[3]; // rv 0
  assign TXHEADER_in[4] = (TXHEADER[4] !== 1'bz) && TXHEADER_delay[4]; // rv 0
  assign TXHEADER_in[5] = (TXHEADER[5] !== 1'bz) && TXHEADER_delay[5]; // rv 0
  assign TXINHIBIT_in = (TXINHIBIT !== 1'bz) && TXINHIBIT_delay; // rv 0
  assign TXPD_in[0] = (TXPD[0] !== 1'bz) && TXPD_delay[0]; // rv 0
  assign TXPD_in[1] = (TXPD[1] !== 1'bz) && TXPD_delay[1]; // rv 0
  assign TXPOLARITY_in = (TXPOLARITY !== 1'bz) && TXPOLARITY_delay; // rv 0
  assign TXPRBSFORCEERR_in = (TXPRBSFORCEERR !== 1'bz) && TXPRBSFORCEERR_delay; // rv 0
  assign TXPRBSSEL_in[0] = (TXPRBSSEL[0] !== 1'bz) && TXPRBSSEL_delay[0]; // rv 0
  assign TXPRBSSEL_in[1] = (TXPRBSSEL[1] !== 1'bz) && TXPRBSSEL_delay[1]; // rv 0
  assign TXPRBSSEL_in[2] = (TXPRBSSEL[2] !== 1'bz) && TXPRBSSEL_delay[2]; // rv 0
  assign TXPRBSSEL_in[3] = (TXPRBSSEL[3] !== 1'bz) && TXPRBSSEL_delay[3]; // rv 0
  assign TXRATE_in[0] = (TXRATE[0] !== 1'bz) && TXRATE_delay[0]; // rv 0
  assign TXRATE_in[1] = (TXRATE[1] !== 1'bz) && TXRATE_delay[1]; // rv 0
  assign TXRATE_in[2] = (TXRATE[2] !== 1'bz) && TXRATE_delay[2]; // rv 0
  assign TXSEQUENCE_in[0] = (TXSEQUENCE[0] !== 1'bz) && TXSEQUENCE_delay[0]; // rv 0
  assign TXSEQUENCE_in[1] = (TXSEQUENCE[1] !== 1'bz) && TXSEQUENCE_delay[1]; // rv 0
  assign TXSEQUENCE_in[2] = (TXSEQUENCE[2] !== 1'bz) && TXSEQUENCE_delay[2]; // rv 0
  assign TXSEQUENCE_in[3] = (TXSEQUENCE[3] !== 1'bz) && TXSEQUENCE_delay[3]; // rv 0
  assign TXSEQUENCE_in[4] = (TXSEQUENCE[4] !== 1'bz) && TXSEQUENCE_delay[4]; // rv 0
  assign TXSEQUENCE_in[5] = (TXSEQUENCE[5] !== 1'bz) && TXSEQUENCE_delay[5]; // rv 0
  assign TXSEQUENCE_in[6] = (TXSEQUENCE[6] !== 1'bz) && TXSEQUENCE_delay[6]; // rv 0
  assign TXUSRCLK2_in = (TXUSRCLK2 !== 1'bz) && TXUSRCLK2_delay; // rv 0
`else
  assign DRPADDR_in[0] = (DRPADDR[0] !== 1'bz) && DRPADDR[0]; // rv 0
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
  assign RX8B10BEN_in = (RX8B10BEN !== 1'bz) && RX8B10BEN; // rv 0
  assign RXCHBONDEN_in = (RXCHBONDEN !== 1'bz) && RXCHBONDEN; // rv 0
  assign RXCHBONDI_in[0] = (RXCHBONDI[0] !== 1'bz) && RXCHBONDI[0]; // rv 0
  assign RXCHBONDI_in[1] = (RXCHBONDI[1] !== 1'bz) && RXCHBONDI[1]; // rv 0
  assign RXCHBONDI_in[2] = (RXCHBONDI[2] !== 1'bz) && RXCHBONDI[2]; // rv 0
  assign RXCHBONDI_in[3] = (RXCHBONDI[3] !== 1'bz) && RXCHBONDI[3]; // rv 0
  assign RXCHBONDI_in[4] = (RXCHBONDI[4] !== 1'bz) && RXCHBONDI[4]; // rv 0
  assign RXCHBONDLEVEL_in[0] = (RXCHBONDLEVEL[0] !== 1'bz) && RXCHBONDLEVEL[0]; // rv 0
  assign RXCHBONDLEVEL_in[1] = (RXCHBONDLEVEL[1] !== 1'bz) && RXCHBONDLEVEL[1]; // rv 0
  assign RXCHBONDLEVEL_in[2] = (RXCHBONDLEVEL[2] !== 1'bz) && RXCHBONDLEVEL[2]; // rv 0
  assign RXCHBONDMASTER_in = (RXCHBONDMASTER !== 1'bz) && RXCHBONDMASTER; // rv 0
  assign RXCHBONDSLAVE_in = (RXCHBONDSLAVE !== 1'bz) && RXCHBONDSLAVE; // rv 0
  assign RXCOMMADETEN_in = (RXCOMMADETEN !== 1'bz) && RXCOMMADETEN; // rv 0
  assign RXGEARBOXSLIP_in = (RXGEARBOXSLIP !== 1'bz) && RXGEARBOXSLIP; // rv 0
  assign RXMCOMMAALIGNEN_in = (RXMCOMMAALIGNEN !== 1'bz) && RXMCOMMAALIGNEN; // rv 0
  assign RXPCOMMAALIGNEN_in = (RXPCOMMAALIGNEN !== 1'bz) && RXPCOMMAALIGNEN; // rv 0
  assign RXPOLARITY_in = (RXPOLARITY !== 1'bz) && RXPOLARITY; // rv 0
  assign RXPRBSCNTRESET_in = (RXPRBSCNTRESET !== 1'bz) && RXPRBSCNTRESET; // rv 0
  assign RXPRBSSEL_in[0] = (RXPRBSSEL[0] !== 1'bz) && RXPRBSSEL[0]; // rv 0
  assign RXPRBSSEL_in[1] = (RXPRBSSEL[1] !== 1'bz) && RXPRBSSEL[1]; // rv 0
  assign RXPRBSSEL_in[2] = (RXPRBSSEL[2] !== 1'bz) && RXPRBSSEL[2]; // rv 0
  assign RXPRBSSEL_in[3] = (RXPRBSSEL[3] !== 1'bz) && RXPRBSSEL[3]; // rv 0
  assign RXRATE_in[0] = (RXRATE[0] !== 1'bz) && RXRATE[0]; // rv 0
  assign RXRATE_in[1] = (RXRATE[1] !== 1'bz) && RXRATE[1]; // rv 0
  assign RXRATE_in[2] = (RXRATE[2] !== 1'bz) && RXRATE[2]; // rv 0
  assign RXSLIDE_in = (RXSLIDE !== 1'bz) && RXSLIDE; // rv 0
  assign RXSLIPOUTCLK_in = (RXSLIPOUTCLK !== 1'bz) && RXSLIPOUTCLK; // rv 0
  assign RXSLIPPMA_in = (RXSLIPPMA !== 1'bz) && RXSLIPPMA; // rv 0
  assign RXUSRCLK2_in = (RXUSRCLK2 !== 1'bz) && RXUSRCLK2; // rv 0
  assign RXUSRCLK_in = (RXUSRCLK !== 1'bz) && RXUSRCLK; // rv 0
  assign TX8B10BBYPASS_in[0] = (TX8B10BBYPASS[0] !== 1'bz) && TX8B10BBYPASS[0]; // rv 0
  assign TX8B10BBYPASS_in[1] = (TX8B10BBYPASS[1] !== 1'bz) && TX8B10BBYPASS[1]; // rv 0
  assign TX8B10BBYPASS_in[2] = (TX8B10BBYPASS[2] !== 1'bz) && TX8B10BBYPASS[2]; // rv 0
  assign TX8B10BBYPASS_in[3] = (TX8B10BBYPASS[3] !== 1'bz) && TX8B10BBYPASS[3]; // rv 0
  assign TX8B10BBYPASS_in[4] = (TX8B10BBYPASS[4] !== 1'bz) && TX8B10BBYPASS[4]; // rv 0
  assign TX8B10BBYPASS_in[5] = (TX8B10BBYPASS[5] !== 1'bz) && TX8B10BBYPASS[5]; // rv 0
  assign TX8B10BBYPASS_in[6] = (TX8B10BBYPASS[6] !== 1'bz) && TX8B10BBYPASS[6]; // rv 0
  assign TX8B10BBYPASS_in[7] = (TX8B10BBYPASS[7] !== 1'bz) && TX8B10BBYPASS[7]; // rv 0
  assign TX8B10BEN_in = (TX8B10BEN !== 1'bz) && TX8B10BEN; // rv 0
  assign TXCOMINIT_in = (TXCOMINIT !== 1'bz) && TXCOMINIT; // rv 0
  assign TXCOMSAS_in = (TXCOMSAS !== 1'bz) && TXCOMSAS; // rv 0
  assign TXCOMWAKE_in = (TXCOMWAKE !== 1'bz) && TXCOMWAKE; // rv 0
  assign TXCTRL0_in[0] = (TXCTRL0[0] !== 1'bz) && TXCTRL0[0]; // rv 0
  assign TXCTRL0_in[10] = (TXCTRL0[10] !== 1'bz) && TXCTRL0[10]; // rv 0
  assign TXCTRL0_in[11] = (TXCTRL0[11] !== 1'bz) && TXCTRL0[11]; // rv 0
  assign TXCTRL0_in[12] = (TXCTRL0[12] !== 1'bz) && TXCTRL0[12]; // rv 0
  assign TXCTRL0_in[13] = (TXCTRL0[13] !== 1'bz) && TXCTRL0[13]; // rv 0
  assign TXCTRL0_in[14] = (TXCTRL0[14] !== 1'bz) && TXCTRL0[14]; // rv 0
  assign TXCTRL0_in[15] = (TXCTRL0[15] !== 1'bz) && TXCTRL0[15]; // rv 0
  assign TXCTRL0_in[1] = (TXCTRL0[1] !== 1'bz) && TXCTRL0[1]; // rv 0
  assign TXCTRL0_in[2] = (TXCTRL0[2] !== 1'bz) && TXCTRL0[2]; // rv 0
  assign TXCTRL0_in[3] = (TXCTRL0[3] !== 1'bz) && TXCTRL0[3]; // rv 0
  assign TXCTRL0_in[4] = (TXCTRL0[4] !== 1'bz) && TXCTRL0[4]; // rv 0
  assign TXCTRL0_in[5] = (TXCTRL0[5] !== 1'bz) && TXCTRL0[5]; // rv 0
  assign TXCTRL0_in[6] = (TXCTRL0[6] !== 1'bz) && TXCTRL0[6]; // rv 0
  assign TXCTRL0_in[7] = (TXCTRL0[7] !== 1'bz) && TXCTRL0[7]; // rv 0
  assign TXCTRL0_in[8] = (TXCTRL0[8] !== 1'bz) && TXCTRL0[8]; // rv 0
  assign TXCTRL0_in[9] = (TXCTRL0[9] !== 1'bz) && TXCTRL0[9]; // rv 0
  assign TXCTRL1_in[0] = (TXCTRL1[0] !== 1'bz) && TXCTRL1[0]; // rv 0
  assign TXCTRL1_in[10] = (TXCTRL1[10] !== 1'bz) && TXCTRL1[10]; // rv 0
  assign TXCTRL1_in[11] = (TXCTRL1[11] !== 1'bz) && TXCTRL1[11]; // rv 0
  assign TXCTRL1_in[12] = (TXCTRL1[12] !== 1'bz) && TXCTRL1[12]; // rv 0
  assign TXCTRL1_in[13] = (TXCTRL1[13] !== 1'bz) && TXCTRL1[13]; // rv 0
  assign TXCTRL1_in[14] = (TXCTRL1[14] !== 1'bz) && TXCTRL1[14]; // rv 0
  assign TXCTRL1_in[15] = (TXCTRL1[15] !== 1'bz) && TXCTRL1[15]; // rv 0
  assign TXCTRL1_in[1] = (TXCTRL1[1] !== 1'bz) && TXCTRL1[1]; // rv 0
  assign TXCTRL1_in[2] = (TXCTRL1[2] !== 1'bz) && TXCTRL1[2]; // rv 0
  assign TXCTRL1_in[3] = (TXCTRL1[3] !== 1'bz) && TXCTRL1[3]; // rv 0
  assign TXCTRL1_in[4] = (TXCTRL1[4] !== 1'bz) && TXCTRL1[4]; // rv 0
  assign TXCTRL1_in[5] = (TXCTRL1[5] !== 1'bz) && TXCTRL1[5]; // rv 0
  assign TXCTRL1_in[6] = (TXCTRL1[6] !== 1'bz) && TXCTRL1[6]; // rv 0
  assign TXCTRL1_in[7] = (TXCTRL1[7] !== 1'bz) && TXCTRL1[7]; // rv 0
  assign TXCTRL1_in[8] = (TXCTRL1[8] !== 1'bz) && TXCTRL1[8]; // rv 0
  assign TXCTRL1_in[9] = (TXCTRL1[9] !== 1'bz) && TXCTRL1[9]; // rv 0
  assign TXCTRL2_in[0] = (TXCTRL2[0] !== 1'bz) && TXCTRL2[0]; // rv 0
  assign TXCTRL2_in[1] = (TXCTRL2[1] !== 1'bz) && TXCTRL2[1]; // rv 0
  assign TXCTRL2_in[2] = (TXCTRL2[2] !== 1'bz) && TXCTRL2[2]; // rv 0
  assign TXCTRL2_in[3] = (TXCTRL2[3] !== 1'bz) && TXCTRL2[3]; // rv 0
  assign TXCTRL2_in[4] = (TXCTRL2[4] !== 1'bz) && TXCTRL2[4]; // rv 0
  assign TXCTRL2_in[5] = (TXCTRL2[5] !== 1'bz) && TXCTRL2[5]; // rv 0
  assign TXCTRL2_in[6] = (TXCTRL2[6] !== 1'bz) && TXCTRL2[6]; // rv 0
  assign TXCTRL2_in[7] = (TXCTRL2[7] !== 1'bz) && TXCTRL2[7]; // rv 0
  assign TXDATA_in[0] = (TXDATA[0] !== 1'bz) && TXDATA[0]; // rv 0
  assign TXDATA_in[100] = (TXDATA[100] !== 1'bz) && TXDATA[100]; // rv 0
  assign TXDATA_in[101] = (TXDATA[101] !== 1'bz) && TXDATA[101]; // rv 0
  assign TXDATA_in[102] = (TXDATA[102] !== 1'bz) && TXDATA[102]; // rv 0
  assign TXDATA_in[103] = (TXDATA[103] !== 1'bz) && TXDATA[103]; // rv 0
  assign TXDATA_in[104] = (TXDATA[104] !== 1'bz) && TXDATA[104]; // rv 0
  assign TXDATA_in[105] = (TXDATA[105] !== 1'bz) && TXDATA[105]; // rv 0
  assign TXDATA_in[106] = (TXDATA[106] !== 1'bz) && TXDATA[106]; // rv 0
  assign TXDATA_in[107] = (TXDATA[107] !== 1'bz) && TXDATA[107]; // rv 0
  assign TXDATA_in[108] = (TXDATA[108] !== 1'bz) && TXDATA[108]; // rv 0
  assign TXDATA_in[109] = (TXDATA[109] !== 1'bz) && TXDATA[109]; // rv 0
  assign TXDATA_in[10] = (TXDATA[10] !== 1'bz) && TXDATA[10]; // rv 0
  assign TXDATA_in[110] = (TXDATA[110] !== 1'bz) && TXDATA[110]; // rv 0
  assign TXDATA_in[111] = (TXDATA[111] !== 1'bz) && TXDATA[111]; // rv 0
  assign TXDATA_in[112] = (TXDATA[112] !== 1'bz) && TXDATA[112]; // rv 0
  assign TXDATA_in[113] = (TXDATA[113] !== 1'bz) && TXDATA[113]; // rv 0
  assign TXDATA_in[114] = (TXDATA[114] !== 1'bz) && TXDATA[114]; // rv 0
  assign TXDATA_in[115] = (TXDATA[115] !== 1'bz) && TXDATA[115]; // rv 0
  assign TXDATA_in[116] = (TXDATA[116] !== 1'bz) && TXDATA[116]; // rv 0
  assign TXDATA_in[117] = (TXDATA[117] !== 1'bz) && TXDATA[117]; // rv 0
  assign TXDATA_in[118] = (TXDATA[118] !== 1'bz) && TXDATA[118]; // rv 0
  assign TXDATA_in[119] = (TXDATA[119] !== 1'bz) && TXDATA[119]; // rv 0
  assign TXDATA_in[11] = (TXDATA[11] !== 1'bz) && TXDATA[11]; // rv 0
  assign TXDATA_in[120] = (TXDATA[120] !== 1'bz) && TXDATA[120]; // rv 0
  assign TXDATA_in[121] = (TXDATA[121] !== 1'bz) && TXDATA[121]; // rv 0
  assign TXDATA_in[122] = (TXDATA[122] !== 1'bz) && TXDATA[122]; // rv 0
  assign TXDATA_in[123] = (TXDATA[123] !== 1'bz) && TXDATA[123]; // rv 0
  assign TXDATA_in[124] = (TXDATA[124] !== 1'bz) && TXDATA[124]; // rv 0
  assign TXDATA_in[125] = (TXDATA[125] !== 1'bz) && TXDATA[125]; // rv 0
  assign TXDATA_in[126] = (TXDATA[126] !== 1'bz) && TXDATA[126]; // rv 0
  assign TXDATA_in[127] = (TXDATA[127] !== 1'bz) && TXDATA[127]; // rv 0
  assign TXDATA_in[12] = (TXDATA[12] !== 1'bz) && TXDATA[12]; // rv 0
  assign TXDATA_in[13] = (TXDATA[13] !== 1'bz) && TXDATA[13]; // rv 0
  assign TXDATA_in[14] = (TXDATA[14] !== 1'bz) && TXDATA[14]; // rv 0
  assign TXDATA_in[15] = (TXDATA[15] !== 1'bz) && TXDATA[15]; // rv 0
  assign TXDATA_in[16] = (TXDATA[16] !== 1'bz) && TXDATA[16]; // rv 0
  assign TXDATA_in[17] = (TXDATA[17] !== 1'bz) && TXDATA[17]; // rv 0
  assign TXDATA_in[18] = (TXDATA[18] !== 1'bz) && TXDATA[18]; // rv 0
  assign TXDATA_in[19] = (TXDATA[19] !== 1'bz) && TXDATA[19]; // rv 0
  assign TXDATA_in[1] = (TXDATA[1] !== 1'bz) && TXDATA[1]; // rv 0
  assign TXDATA_in[20] = (TXDATA[20] !== 1'bz) && TXDATA[20]; // rv 0
  assign TXDATA_in[21] = (TXDATA[21] !== 1'bz) && TXDATA[21]; // rv 0
  assign TXDATA_in[22] = (TXDATA[22] !== 1'bz) && TXDATA[22]; // rv 0
  assign TXDATA_in[23] = (TXDATA[23] !== 1'bz) && TXDATA[23]; // rv 0
  assign TXDATA_in[24] = (TXDATA[24] !== 1'bz) && TXDATA[24]; // rv 0
  assign TXDATA_in[25] = (TXDATA[25] !== 1'bz) && TXDATA[25]; // rv 0
  assign TXDATA_in[26] = (TXDATA[26] !== 1'bz) && TXDATA[26]; // rv 0
  assign TXDATA_in[27] = (TXDATA[27] !== 1'bz) && TXDATA[27]; // rv 0
  assign TXDATA_in[28] = (TXDATA[28] !== 1'bz) && TXDATA[28]; // rv 0
  assign TXDATA_in[29] = (TXDATA[29] !== 1'bz) && TXDATA[29]; // rv 0
  assign TXDATA_in[2] = (TXDATA[2] !== 1'bz) && TXDATA[2]; // rv 0
  assign TXDATA_in[30] = (TXDATA[30] !== 1'bz) && TXDATA[30]; // rv 0
  assign TXDATA_in[31] = (TXDATA[31] !== 1'bz) && TXDATA[31]; // rv 0
  assign TXDATA_in[32] = (TXDATA[32] !== 1'bz) && TXDATA[32]; // rv 0
  assign TXDATA_in[33] = (TXDATA[33] !== 1'bz) && TXDATA[33]; // rv 0
  assign TXDATA_in[34] = (TXDATA[34] !== 1'bz) && TXDATA[34]; // rv 0
  assign TXDATA_in[35] = (TXDATA[35] !== 1'bz) && TXDATA[35]; // rv 0
  assign TXDATA_in[36] = (TXDATA[36] !== 1'bz) && TXDATA[36]; // rv 0
  assign TXDATA_in[37] = (TXDATA[37] !== 1'bz) && TXDATA[37]; // rv 0
  assign TXDATA_in[38] = (TXDATA[38] !== 1'bz) && TXDATA[38]; // rv 0
  assign TXDATA_in[39] = (TXDATA[39] !== 1'bz) && TXDATA[39]; // rv 0
  assign TXDATA_in[3] = (TXDATA[3] !== 1'bz) && TXDATA[3]; // rv 0
  assign TXDATA_in[40] = (TXDATA[40] !== 1'bz) && TXDATA[40]; // rv 0
  assign TXDATA_in[41] = (TXDATA[41] !== 1'bz) && TXDATA[41]; // rv 0
  assign TXDATA_in[42] = (TXDATA[42] !== 1'bz) && TXDATA[42]; // rv 0
  assign TXDATA_in[43] = (TXDATA[43] !== 1'bz) && TXDATA[43]; // rv 0
  assign TXDATA_in[44] = (TXDATA[44] !== 1'bz) && TXDATA[44]; // rv 0
  assign TXDATA_in[45] = (TXDATA[45] !== 1'bz) && TXDATA[45]; // rv 0
  assign TXDATA_in[46] = (TXDATA[46] !== 1'bz) && TXDATA[46]; // rv 0
  assign TXDATA_in[47] = (TXDATA[47] !== 1'bz) && TXDATA[47]; // rv 0
  assign TXDATA_in[48] = (TXDATA[48] !== 1'bz) && TXDATA[48]; // rv 0
  assign TXDATA_in[49] = (TXDATA[49] !== 1'bz) && TXDATA[49]; // rv 0
  assign TXDATA_in[4] = (TXDATA[4] !== 1'bz) && TXDATA[4]; // rv 0
  assign TXDATA_in[50] = (TXDATA[50] !== 1'bz) && TXDATA[50]; // rv 0
  assign TXDATA_in[51] = (TXDATA[51] !== 1'bz) && TXDATA[51]; // rv 0
  assign TXDATA_in[52] = (TXDATA[52] !== 1'bz) && TXDATA[52]; // rv 0
  assign TXDATA_in[53] = (TXDATA[53] !== 1'bz) && TXDATA[53]; // rv 0
  assign TXDATA_in[54] = (TXDATA[54] !== 1'bz) && TXDATA[54]; // rv 0
  assign TXDATA_in[55] = (TXDATA[55] !== 1'bz) && TXDATA[55]; // rv 0
  assign TXDATA_in[56] = (TXDATA[56] !== 1'bz) && TXDATA[56]; // rv 0
  assign TXDATA_in[57] = (TXDATA[57] !== 1'bz) && TXDATA[57]; // rv 0
  assign TXDATA_in[58] = (TXDATA[58] !== 1'bz) && TXDATA[58]; // rv 0
  assign TXDATA_in[59] = (TXDATA[59] !== 1'bz) && TXDATA[59]; // rv 0
  assign TXDATA_in[5] = (TXDATA[5] !== 1'bz) && TXDATA[5]; // rv 0
  assign TXDATA_in[60] = (TXDATA[60] !== 1'bz) && TXDATA[60]; // rv 0
  assign TXDATA_in[61] = (TXDATA[61] !== 1'bz) && TXDATA[61]; // rv 0
  assign TXDATA_in[62] = (TXDATA[62] !== 1'bz) && TXDATA[62]; // rv 0
  assign TXDATA_in[63] = (TXDATA[63] !== 1'bz) && TXDATA[63]; // rv 0
  assign TXDATA_in[64] = (TXDATA[64] !== 1'bz) && TXDATA[64]; // rv 0
  assign TXDATA_in[65] = (TXDATA[65] !== 1'bz) && TXDATA[65]; // rv 0
  assign TXDATA_in[66] = (TXDATA[66] !== 1'bz) && TXDATA[66]; // rv 0
  assign TXDATA_in[67] = (TXDATA[67] !== 1'bz) && TXDATA[67]; // rv 0
  assign TXDATA_in[68] = (TXDATA[68] !== 1'bz) && TXDATA[68]; // rv 0
  assign TXDATA_in[69] = (TXDATA[69] !== 1'bz) && TXDATA[69]; // rv 0
  assign TXDATA_in[6] = (TXDATA[6] !== 1'bz) && TXDATA[6]; // rv 0
  assign TXDATA_in[70] = (TXDATA[70] !== 1'bz) && TXDATA[70]; // rv 0
  assign TXDATA_in[71] = (TXDATA[71] !== 1'bz) && TXDATA[71]; // rv 0
  assign TXDATA_in[72] = (TXDATA[72] !== 1'bz) && TXDATA[72]; // rv 0
  assign TXDATA_in[73] = (TXDATA[73] !== 1'bz) && TXDATA[73]; // rv 0
  assign TXDATA_in[74] = (TXDATA[74] !== 1'bz) && TXDATA[74]; // rv 0
  assign TXDATA_in[75] = (TXDATA[75] !== 1'bz) && TXDATA[75]; // rv 0
  assign TXDATA_in[76] = (TXDATA[76] !== 1'bz) && TXDATA[76]; // rv 0
  assign TXDATA_in[77] = (TXDATA[77] !== 1'bz) && TXDATA[77]; // rv 0
  assign TXDATA_in[78] = (TXDATA[78] !== 1'bz) && TXDATA[78]; // rv 0
  assign TXDATA_in[79] = (TXDATA[79] !== 1'bz) && TXDATA[79]; // rv 0
  assign TXDATA_in[7] = (TXDATA[7] !== 1'bz) && TXDATA[7]; // rv 0
  assign TXDATA_in[80] = (TXDATA[80] !== 1'bz) && TXDATA[80]; // rv 0
  assign TXDATA_in[81] = (TXDATA[81] !== 1'bz) && TXDATA[81]; // rv 0
  assign TXDATA_in[82] = (TXDATA[82] !== 1'bz) && TXDATA[82]; // rv 0
  assign TXDATA_in[83] = (TXDATA[83] !== 1'bz) && TXDATA[83]; // rv 0
  assign TXDATA_in[84] = (TXDATA[84] !== 1'bz) && TXDATA[84]; // rv 0
  assign TXDATA_in[85] = (TXDATA[85] !== 1'bz) && TXDATA[85]; // rv 0
  assign TXDATA_in[86] = (TXDATA[86] !== 1'bz) && TXDATA[86]; // rv 0
  assign TXDATA_in[87] = (TXDATA[87] !== 1'bz) && TXDATA[87]; // rv 0
  assign TXDATA_in[88] = (TXDATA[88] !== 1'bz) && TXDATA[88]; // rv 0
  assign TXDATA_in[89] = (TXDATA[89] !== 1'bz) && TXDATA[89]; // rv 0
  assign TXDATA_in[8] = (TXDATA[8] !== 1'bz) && TXDATA[8]; // rv 0
  assign TXDATA_in[90] = (TXDATA[90] !== 1'bz) && TXDATA[90]; // rv 0
  assign TXDATA_in[91] = (TXDATA[91] !== 1'bz) && TXDATA[91]; // rv 0
  assign TXDATA_in[92] = (TXDATA[92] !== 1'bz) && TXDATA[92]; // rv 0
  assign TXDATA_in[93] = (TXDATA[93] !== 1'bz) && TXDATA[93]; // rv 0
  assign TXDATA_in[94] = (TXDATA[94] !== 1'bz) && TXDATA[94]; // rv 0
  assign TXDATA_in[95] = (TXDATA[95] !== 1'bz) && TXDATA[95]; // rv 0
  assign TXDATA_in[96] = (TXDATA[96] !== 1'bz) && TXDATA[96]; // rv 0
  assign TXDATA_in[97] = (TXDATA[97] !== 1'bz) && TXDATA[97]; // rv 0
  assign TXDATA_in[98] = (TXDATA[98] !== 1'bz) && TXDATA[98]; // rv 0
  assign TXDATA_in[99] = (TXDATA[99] !== 1'bz) && TXDATA[99]; // rv 0
  assign TXDATA_in[9] = (TXDATA[9] !== 1'bz) && TXDATA[9]; // rv 0
  assign TXDETECTRX_in = (TXDETECTRX !== 1'bz) && TXDETECTRX; // rv 0
  assign TXELECIDLE_in = (TXELECIDLE !== 1'bz) && TXELECIDLE; // rv 0
  assign TXHEADER_in[0] = (TXHEADER[0] !== 1'bz) && TXHEADER[0]; // rv 0
  assign TXHEADER_in[1] = (TXHEADER[1] !== 1'bz) && TXHEADER[1]; // rv 0
  assign TXHEADER_in[2] = (TXHEADER[2] !== 1'bz) && TXHEADER[2]; // rv 0
  assign TXHEADER_in[3] = (TXHEADER[3] !== 1'bz) && TXHEADER[3]; // rv 0
  assign TXHEADER_in[4] = (TXHEADER[4] !== 1'bz) && TXHEADER[4]; // rv 0
  assign TXHEADER_in[5] = (TXHEADER[5] !== 1'bz) && TXHEADER[5]; // rv 0
  assign TXINHIBIT_in = (TXINHIBIT !== 1'bz) && TXINHIBIT; // rv 0
  assign TXPD_in[0] = (TXPD[0] !== 1'bz) && TXPD[0]; // rv 0
  assign TXPD_in[1] = (TXPD[1] !== 1'bz) && TXPD[1]; // rv 0
  assign TXPOLARITY_in = (TXPOLARITY !== 1'bz) && TXPOLARITY; // rv 0
  assign TXPRBSFORCEERR_in = (TXPRBSFORCEERR !== 1'bz) && TXPRBSFORCEERR; // rv 0
  assign TXPRBSSEL_in[0] = (TXPRBSSEL[0] !== 1'bz) && TXPRBSSEL[0]; // rv 0
  assign TXPRBSSEL_in[1] = (TXPRBSSEL[1] !== 1'bz) && TXPRBSSEL[1]; // rv 0
  assign TXPRBSSEL_in[2] = (TXPRBSSEL[2] !== 1'bz) && TXPRBSSEL[2]; // rv 0
  assign TXPRBSSEL_in[3] = (TXPRBSSEL[3] !== 1'bz) && TXPRBSSEL[3]; // rv 0
  assign TXRATE_in[0] = (TXRATE[0] !== 1'bz) && TXRATE[0]; // rv 0
  assign TXRATE_in[1] = (TXRATE[1] !== 1'bz) && TXRATE[1]; // rv 0
  assign TXRATE_in[2] = (TXRATE[2] !== 1'bz) && TXRATE[2]; // rv 0
  assign TXSEQUENCE_in[0] = (TXSEQUENCE[0] !== 1'bz) && TXSEQUENCE[0]; // rv 0
  assign TXSEQUENCE_in[1] = (TXSEQUENCE[1] !== 1'bz) && TXSEQUENCE[1]; // rv 0
  assign TXSEQUENCE_in[2] = (TXSEQUENCE[2] !== 1'bz) && TXSEQUENCE[2]; // rv 0
  assign TXSEQUENCE_in[3] = (TXSEQUENCE[3] !== 1'bz) && TXSEQUENCE[3]; // rv 0
  assign TXSEQUENCE_in[4] = (TXSEQUENCE[4] !== 1'bz) && TXSEQUENCE[4]; // rv 0
  assign TXSEQUENCE_in[5] = (TXSEQUENCE[5] !== 1'bz) && TXSEQUENCE[5]; // rv 0
  assign TXSEQUENCE_in[6] = (TXSEQUENCE[6] !== 1'bz) && TXSEQUENCE[6]; // rv 0
  assign TXUSRCLK2_in = (TXUSRCLK2 !== 1'bz) && TXUSRCLK2; // rv 0
`endif

  assign CDRSTEPDIR_in = (CDRSTEPDIR !== 1'bz) && CDRSTEPDIR; // rv 0
  assign CDRSTEPSQ_in = (CDRSTEPSQ !== 1'bz) && CDRSTEPSQ; // rv 0
  assign CDRSTEPSX_in = (CDRSTEPSX !== 1'bz) && CDRSTEPSX; // rv 0
  assign CFGRESET_in = (CFGRESET !== 1'bz) && CFGRESET; // rv 0
  assign CLKRSVD0_in = (CLKRSVD0 !== 1'bz) && CLKRSVD0; // rv 0
  assign CLKRSVD1_in = (CLKRSVD1 !== 1'bz) && CLKRSVD1; // rv 0
  assign CPLLFREQLOCK_in = (CPLLFREQLOCK !== 1'bz) && CPLLFREQLOCK; // rv 0
  assign CPLLLOCKDETCLK_in = (CPLLLOCKDETCLK !== 1'bz) && CPLLLOCKDETCLK; // rv 0
  assign CPLLLOCKEN_in = (CPLLLOCKEN !== 1'bz) && CPLLLOCKEN; // rv 0
  assign CPLLPD_in = (CPLLPD !== 1'bz) && CPLLPD; // rv 0
  assign CPLLREFCLKSEL_in[0] = (CPLLREFCLKSEL[0] === 1'bz) || CPLLREFCLKSEL[0]; // rv 1
  assign CPLLREFCLKSEL_in[1] = (CPLLREFCLKSEL[1] !== 1'bz) && CPLLREFCLKSEL[1]; // rv 0
  assign CPLLREFCLKSEL_in[2] = (CPLLREFCLKSEL[2] !== 1'bz) && CPLLREFCLKSEL[2]; // rv 0
  assign CPLLRESET_in = (CPLLRESET !== 1'bz) && CPLLRESET; // rv 0
  assign DMONFIFORESET_in = (DMONFIFORESET !== 1'bz) && DMONFIFORESET; // rv 0
  assign DMONITORCLK_in = (DMONITORCLK !== 1'bz) && DMONITORCLK; // rv 0
  assign DRPRST_in = (DRPRST === 1'bz) || DRPRST; // rv 1
  assign EYESCANRESET_in = (EYESCANRESET !== 1'bz) && EYESCANRESET; // rv 0
  assign EYESCANTRIGGER_in = (EYESCANTRIGGER !== 1'bz) && EYESCANTRIGGER; // rv 0
  assign FREQOS_in = (FREQOS !== 1'bz) && FREQOS; // rv 0
  assign GTGREFCLK_in = GTGREFCLK;
  assign GTNORTHREFCLK0_in = GTNORTHREFCLK0;
  assign GTNORTHREFCLK1_in = GTNORTHREFCLK1;
  assign GTREFCLK0_in = GTREFCLK0;
  assign GTREFCLK1_in = GTREFCLK1;
  assign GTRSVD_in[0] = (GTRSVD[0] !== 1'bz) && GTRSVD[0]; // rv 0
  assign GTRSVD_in[10] = (GTRSVD[10] !== 1'bz) && GTRSVD[10]; // rv 0
  assign GTRSVD_in[11] = (GTRSVD[11] !== 1'bz) && GTRSVD[11]; // rv 0
  assign GTRSVD_in[12] = (GTRSVD[12] !== 1'bz) && GTRSVD[12]; // rv 0
  assign GTRSVD_in[13] = (GTRSVD[13] !== 1'bz) && GTRSVD[13]; // rv 0
  assign GTRSVD_in[14] = (GTRSVD[14] !== 1'bz) && GTRSVD[14]; // rv 0
  assign GTRSVD_in[15] = (GTRSVD[15] !== 1'bz) && GTRSVD[15]; // rv 0
  assign GTRSVD_in[1] = (GTRSVD[1] !== 1'bz) && GTRSVD[1]; // rv 0
  assign GTRSVD_in[2] = (GTRSVD[2] !== 1'bz) && GTRSVD[2]; // rv 0
  assign GTRSVD_in[3] = (GTRSVD[3] !== 1'bz) && GTRSVD[3]; // rv 0
  assign GTRSVD_in[4] = (GTRSVD[4] !== 1'bz) && GTRSVD[4]; // rv 0
  assign GTRSVD_in[5] = (GTRSVD[5] !== 1'bz) && GTRSVD[5]; // rv 0
  assign GTRSVD_in[6] = (GTRSVD[6] !== 1'bz) && GTRSVD[6]; // rv 0
  assign GTRSVD_in[7] = (GTRSVD[7] !== 1'bz) && GTRSVD[7]; // rv 0
  assign GTRSVD_in[8] = (GTRSVD[8] !== 1'bz) && GTRSVD[8]; // rv 0
  assign GTRSVD_in[9] = (GTRSVD[9] !== 1'bz) && GTRSVD[9]; // rv 0
  assign GTRXRESETSEL_in = (GTRXRESETSEL !== 1'bz) && GTRXRESETSEL; // rv 0
  assign GTRXRESET_in = (GTRXRESET !== 1'bz) && GTRXRESET; // rv 0
  assign GTSOUTHREFCLK0_in = GTSOUTHREFCLK0;
  assign GTSOUTHREFCLK1_in = GTSOUTHREFCLK1;
  assign GTTXRESETSEL_in = (GTTXRESETSEL !== 1'bz) && GTTXRESETSEL; // rv 0
  assign GTTXRESET_in = (GTTXRESET !== 1'bz) && GTTXRESET; // rv 0
  assign GTYRXN_in = GTYRXN;
  assign GTYRXP_in = GTYRXP;
  assign INCPCTRL_in = (INCPCTRL !== 1'bz) && INCPCTRL; // rv 0
  assign LOOPBACK_in[0] = (LOOPBACK[0] !== 1'bz) && LOOPBACK[0]; // rv 0
  assign LOOPBACK_in[1] = (LOOPBACK[1] !== 1'bz) && LOOPBACK[1]; // rv 0
  assign LOOPBACK_in[2] = (LOOPBACK[2] !== 1'bz) && LOOPBACK[2]; // rv 0
  assign PCIEEQRXEQADAPTDONE_in = (PCIEEQRXEQADAPTDONE !== 1'bz) && PCIEEQRXEQADAPTDONE; // rv 0
  assign PCIERSTIDLE_in = (PCIERSTIDLE !== 1'bz) && PCIERSTIDLE; // rv 0
  assign PCIERSTTXSYNCSTART_in = (PCIERSTTXSYNCSTART !== 1'bz) && PCIERSTTXSYNCSTART; // rv 0
  assign PCIEUSERRATEDONE_in = (PCIEUSERRATEDONE !== 1'bz) && PCIEUSERRATEDONE; // rv 0
  assign PCSRSVDIN_in[0] = (PCSRSVDIN[0] === 1'bz) || PCSRSVDIN[0]; // rv 1
  assign PCSRSVDIN_in[10] = (PCSRSVDIN[10] !== 1'bz) && PCSRSVDIN[10]; // rv 0
  assign PCSRSVDIN_in[11] = (PCSRSVDIN[11] !== 1'bz) && PCSRSVDIN[11]; // rv 0
  assign PCSRSVDIN_in[12] = (PCSRSVDIN[12] !== 1'bz) && PCSRSVDIN[12]; // rv 0
  assign PCSRSVDIN_in[13] = (PCSRSVDIN[13] !== 1'bz) && PCSRSVDIN[13]; // rv 0
  assign PCSRSVDIN_in[14] = (PCSRSVDIN[14] !== 1'bz) && PCSRSVDIN[14]; // rv 0
  assign PCSRSVDIN_in[15] = (PCSRSVDIN[15] !== 1'bz) && PCSRSVDIN[15]; // rv 0
  assign PCSRSVDIN_in[1] = (PCSRSVDIN[1] !== 1'bz) && PCSRSVDIN[1]; // rv 0
  assign PCSRSVDIN_in[2] = (PCSRSVDIN[2] !== 1'bz) && PCSRSVDIN[2]; // rv 0
  assign PCSRSVDIN_in[3] = (PCSRSVDIN[3] !== 1'bz) && PCSRSVDIN[3]; // rv 0
  assign PCSRSVDIN_in[4] = (PCSRSVDIN[4] !== 1'bz) && PCSRSVDIN[4]; // rv 0
  assign PCSRSVDIN_in[5] = (PCSRSVDIN[5] !== 1'bz) && PCSRSVDIN[5]; // rv 0
  assign PCSRSVDIN_in[6] = (PCSRSVDIN[6] !== 1'bz) && PCSRSVDIN[6]; // rv 0
  assign PCSRSVDIN_in[7] = (PCSRSVDIN[7] !== 1'bz) && PCSRSVDIN[7]; // rv 0
  assign PCSRSVDIN_in[8] = (PCSRSVDIN[8] !== 1'bz) && PCSRSVDIN[8]; // rv 0
  assign PCSRSVDIN_in[9] = (PCSRSVDIN[9] !== 1'bz) && PCSRSVDIN[9]; // rv 0
  assign QPLL0CLK_in = QPLL0CLK;
  assign QPLL0FREQLOCK_in = (QPLL0FREQLOCK !== 1'bz) && QPLL0FREQLOCK; // rv 0
  assign QPLL0REFCLK_in = QPLL0REFCLK;
  assign QPLL1CLK_in = QPLL1CLK;
  assign QPLL1FREQLOCK_in = (QPLL1FREQLOCK !== 1'bz) && QPLL1FREQLOCK; // rv 0
  assign QPLL1REFCLK_in = QPLL1REFCLK;
  assign RESETOVRD_in = (RESETOVRD !== 1'bz) && RESETOVRD; // rv 0
  assign RXAFECFOKEN_in = (RXAFECFOKEN === 1'bz) || RXAFECFOKEN; // rv 1
  assign RXBUFRESET_in = (RXBUFRESET !== 1'bz) && RXBUFRESET; // rv 0
  assign RXCDRFREQRESET_in = (RXCDRFREQRESET !== 1'bz) && RXCDRFREQRESET; // rv 0
  assign RXCDRHOLD_in = (RXCDRHOLD !== 1'bz) && RXCDRHOLD; // rv 0
  assign RXCDROVRDEN_in = (RXCDROVRDEN !== 1'bz) && RXCDROVRDEN; // rv 0
  assign RXCDRRESET_in = (RXCDRRESET !== 1'bz) && RXCDRRESET; // rv 0
  assign RXCKCALRESET_in = (RXCKCALRESET !== 1'bz) && RXCKCALRESET; // rv 0
  assign RXCKCALSTART_in[0] = (RXCKCALSTART[0] !== 1'bz) && RXCKCALSTART[0]; // rv 0
  assign RXCKCALSTART_in[1] = (RXCKCALSTART[1] !== 1'bz) && RXCKCALSTART[1]; // rv 0
  assign RXCKCALSTART_in[2] = (RXCKCALSTART[2] !== 1'bz) && RXCKCALSTART[2]; // rv 0
  assign RXCKCALSTART_in[3] = (RXCKCALSTART[3] !== 1'bz) && RXCKCALSTART[3]; // rv 0
  assign RXCKCALSTART_in[4] = (RXCKCALSTART[4] !== 1'bz) && RXCKCALSTART[4]; // rv 0
  assign RXCKCALSTART_in[5] = (RXCKCALSTART[5] !== 1'bz) && RXCKCALSTART[5]; // rv 0
  assign RXCKCALSTART_in[6] = (RXCKCALSTART[6] !== 1'bz) && RXCKCALSTART[6]; // rv 0
  assign RXDFEAGCHOLD_in = (RXDFEAGCHOLD !== 1'bz) && RXDFEAGCHOLD; // rv 0
  assign RXDFEAGCOVRDEN_in = (RXDFEAGCOVRDEN !== 1'bz) && RXDFEAGCOVRDEN; // rv 0
  assign RXDFECFOKFCNUM_in[0] = (RXDFECFOKFCNUM[0] !== 1'bz) && RXDFECFOKFCNUM[0]; // rv 0
  assign RXDFECFOKFCNUM_in[1] = (RXDFECFOKFCNUM[1] === 1'bz) || RXDFECFOKFCNUM[1]; // rv 1
  assign RXDFECFOKFCNUM_in[2] = (RXDFECFOKFCNUM[2] === 1'bz) || RXDFECFOKFCNUM[2]; // rv 1
  assign RXDFECFOKFCNUM_in[3] = (RXDFECFOKFCNUM[3] !== 1'bz) && RXDFECFOKFCNUM[3]; // rv 0
  assign RXDFECFOKFEN_in = (RXDFECFOKFEN !== 1'bz) && RXDFECFOKFEN; // rv 0
  assign RXDFECFOKFPULSE_in = (RXDFECFOKFPULSE !== 1'bz) && RXDFECFOKFPULSE; // rv 0
  assign RXDFECFOKHOLD_in = (RXDFECFOKHOLD !== 1'bz) && RXDFECFOKHOLD; // rv 0
  assign RXDFECFOKOVREN_in = (RXDFECFOKOVREN !== 1'bz) && RXDFECFOKOVREN; // rv 0
  assign RXDFEKHHOLD_in = (RXDFEKHHOLD !== 1'bz) && RXDFEKHHOLD; // rv 0
  assign RXDFEKHOVRDEN_in = (RXDFEKHOVRDEN !== 1'bz) && RXDFEKHOVRDEN; // rv 0
  assign RXDFELFHOLD_in = (RXDFELFHOLD !== 1'bz) && RXDFELFHOLD; // rv 0
  assign RXDFELFOVRDEN_in = (RXDFELFOVRDEN !== 1'bz) && RXDFELFOVRDEN; // rv 0
  assign RXDFELPMRESET_in = (RXDFELPMRESET !== 1'bz) && RXDFELPMRESET; // rv 0
  assign RXDFETAP10HOLD_in = (RXDFETAP10HOLD !== 1'bz) && RXDFETAP10HOLD; // rv 0
  assign RXDFETAP10OVRDEN_in = (RXDFETAP10OVRDEN !== 1'bz) && RXDFETAP10OVRDEN; // rv 0
  assign RXDFETAP11HOLD_in = (RXDFETAP11HOLD !== 1'bz) && RXDFETAP11HOLD; // rv 0
  assign RXDFETAP11OVRDEN_in = (RXDFETAP11OVRDEN !== 1'bz) && RXDFETAP11OVRDEN; // rv 0
  assign RXDFETAP12HOLD_in = (RXDFETAP12HOLD !== 1'bz) && RXDFETAP12HOLD; // rv 0
  assign RXDFETAP12OVRDEN_in = (RXDFETAP12OVRDEN !== 1'bz) && RXDFETAP12OVRDEN; // rv 0
  assign RXDFETAP13HOLD_in = (RXDFETAP13HOLD !== 1'bz) && RXDFETAP13HOLD; // rv 0
  assign RXDFETAP13OVRDEN_in = (RXDFETAP13OVRDEN !== 1'bz) && RXDFETAP13OVRDEN; // rv 0
  assign RXDFETAP14HOLD_in = (RXDFETAP14HOLD !== 1'bz) && RXDFETAP14HOLD; // rv 0
  assign RXDFETAP14OVRDEN_in = (RXDFETAP14OVRDEN !== 1'bz) && RXDFETAP14OVRDEN; // rv 0
  assign RXDFETAP15HOLD_in = (RXDFETAP15HOLD !== 1'bz) && RXDFETAP15HOLD; // rv 0
  assign RXDFETAP15OVRDEN_in = (RXDFETAP15OVRDEN !== 1'bz) && RXDFETAP15OVRDEN; // rv 0
  assign RXDFETAP2HOLD_in = (RXDFETAP2HOLD !== 1'bz) && RXDFETAP2HOLD; // rv 0
  assign RXDFETAP2OVRDEN_in = (RXDFETAP2OVRDEN !== 1'bz) && RXDFETAP2OVRDEN; // rv 0
  assign RXDFETAP3HOLD_in = (RXDFETAP3HOLD !== 1'bz) && RXDFETAP3HOLD; // rv 0
  assign RXDFETAP3OVRDEN_in = (RXDFETAP3OVRDEN !== 1'bz) && RXDFETAP3OVRDEN; // rv 0
  assign RXDFETAP4HOLD_in = (RXDFETAP4HOLD !== 1'bz) && RXDFETAP4HOLD; // rv 0
  assign RXDFETAP4OVRDEN_in = (RXDFETAP4OVRDEN !== 1'bz) && RXDFETAP4OVRDEN; // rv 0
  assign RXDFETAP5HOLD_in = (RXDFETAP5HOLD !== 1'bz) && RXDFETAP5HOLD; // rv 0
  assign RXDFETAP5OVRDEN_in = (RXDFETAP5OVRDEN !== 1'bz) && RXDFETAP5OVRDEN; // rv 0
  assign RXDFETAP6HOLD_in = (RXDFETAP6HOLD !== 1'bz) && RXDFETAP6HOLD; // rv 0
  assign RXDFETAP6OVRDEN_in = (RXDFETAP6OVRDEN !== 1'bz) && RXDFETAP6OVRDEN; // rv 0
  assign RXDFETAP7HOLD_in = (RXDFETAP7HOLD !== 1'bz) && RXDFETAP7HOLD; // rv 0
  assign RXDFETAP7OVRDEN_in = (RXDFETAP7OVRDEN !== 1'bz) && RXDFETAP7OVRDEN; // rv 0
  assign RXDFETAP8HOLD_in = (RXDFETAP8HOLD !== 1'bz) && RXDFETAP8HOLD; // rv 0
  assign RXDFETAP8OVRDEN_in = (RXDFETAP8OVRDEN !== 1'bz) && RXDFETAP8OVRDEN; // rv 0
  assign RXDFETAP9HOLD_in = (RXDFETAP9HOLD !== 1'bz) && RXDFETAP9HOLD; // rv 0
  assign RXDFETAP9OVRDEN_in = (RXDFETAP9OVRDEN !== 1'bz) && RXDFETAP9OVRDEN; // rv 0
  assign RXDFEUTHOLD_in = (RXDFEUTHOLD !== 1'bz) && RXDFEUTHOLD; // rv 0
  assign RXDFEUTOVRDEN_in = (RXDFEUTOVRDEN !== 1'bz) && RXDFEUTOVRDEN; // rv 0
  assign RXDFEVPHOLD_in = (RXDFEVPHOLD !== 1'bz) && RXDFEVPHOLD; // rv 0
  assign RXDFEVPOVRDEN_in = (RXDFEVPOVRDEN !== 1'bz) && RXDFEVPOVRDEN; // rv 0
  assign RXDFEXYDEN_in = (RXDFEXYDEN !== 1'bz) && RXDFEXYDEN; // rv 0
  assign RXDLYBYPASS_in = (RXDLYBYPASS !== 1'bz) && RXDLYBYPASS; // rv 0
  assign RXDLYEN_in = (RXDLYEN !== 1'bz) && RXDLYEN; // rv 0
  assign RXDLYOVRDEN_in = (RXDLYOVRDEN !== 1'bz) && RXDLYOVRDEN; // rv 0
  assign RXDLYSRESET_in = (RXDLYSRESET !== 1'bz) && RXDLYSRESET; // rv 0
  assign RXELECIDLEMODE_in[0] = (RXELECIDLEMODE[0] !== 1'bz) && RXELECIDLEMODE[0]; // rv 0
  assign RXELECIDLEMODE_in[1] = (RXELECIDLEMODE[1] !== 1'bz) && RXELECIDLEMODE[1]; // rv 0
  assign RXEQTRAINING_in = (RXEQTRAINING !== 1'bz) && RXEQTRAINING; // rv 0
  assign RXLATCLK_in = (RXLATCLK !== 1'bz) && RXLATCLK; // rv 0
  assign RXLPMEN_in = (RXLPMEN !== 1'bz) && RXLPMEN; // rv 0
  assign RXLPMGCHOLD_in = (RXLPMGCHOLD !== 1'bz) && RXLPMGCHOLD; // rv 0
  assign RXLPMGCOVRDEN_in = (RXLPMGCOVRDEN !== 1'bz) && RXLPMGCOVRDEN; // rv 0
  assign RXLPMHFHOLD_in = (RXLPMHFHOLD !== 1'bz) && RXLPMHFHOLD; // rv 0
  assign RXLPMHFOVRDEN_in = (RXLPMHFOVRDEN !== 1'bz) && RXLPMHFOVRDEN; // rv 0
  assign RXLPMLFHOLD_in = (RXLPMLFHOLD !== 1'bz) && RXLPMLFHOLD; // rv 0
  assign RXLPMLFKLOVRDEN_in = (RXLPMLFKLOVRDEN !== 1'bz) && RXLPMLFKLOVRDEN; // rv 0
  assign RXLPMOSHOLD_in = (RXLPMOSHOLD !== 1'bz) && RXLPMOSHOLD; // rv 0
  assign RXLPMOSOVRDEN_in = (RXLPMOSOVRDEN !== 1'bz) && RXLPMOSOVRDEN; // rv 0
  assign RXMONITORSEL_in[0] = (RXMONITORSEL[0] !== 1'bz) && RXMONITORSEL[0]; // rv 0
  assign RXMONITORSEL_in[1] = (RXMONITORSEL[1] !== 1'bz) && RXMONITORSEL[1]; // rv 0
  assign RXOOBRESET_in = (RXOOBRESET !== 1'bz) && RXOOBRESET; // rv 0
  assign RXOSCALRESET_in = (RXOSCALRESET !== 1'bz) && RXOSCALRESET; // rv 0
  assign RXOSHOLD_in = (RXOSHOLD !== 1'bz) && RXOSHOLD; // rv 0
  assign RXOSOVRDEN_in = (RXOSOVRDEN !== 1'bz) && RXOSOVRDEN; // rv 0
  assign RXOUTCLKSEL_in[0] = (RXOUTCLKSEL[0] !== 1'bz) && RXOUTCLKSEL[0]; // rv 0
  assign RXOUTCLKSEL_in[1] = (RXOUTCLKSEL[1] !== 1'bz) && RXOUTCLKSEL[1]; // rv 0
  assign RXOUTCLKSEL_in[2] = (RXOUTCLKSEL[2] !== 1'bz) && RXOUTCLKSEL[2]; // rv 0
  assign RXPCSRESET_in = (RXPCSRESET !== 1'bz) && RXPCSRESET; // rv 0
  assign RXPD_in[0] = (RXPD[0] !== 1'bz) && RXPD[0]; // rv 0
  assign RXPD_in[1] = (RXPD[1] !== 1'bz) && RXPD[1]; // rv 0
  assign RXPHALIGNEN_in = (RXPHALIGNEN !== 1'bz) && RXPHALIGNEN; // rv 0
  assign RXPHALIGN_in = (RXPHALIGN !== 1'bz) && RXPHALIGN; // rv 0
  assign RXPHDLYPD_in = (RXPHDLYPD !== 1'bz) && RXPHDLYPD; // rv 0
  assign RXPHDLYRESET_in = (RXPHDLYRESET !== 1'bz) && RXPHDLYRESET; // rv 0
  assign RXPLLCLKSEL_in[0] = (RXPLLCLKSEL[0] !== 1'bz) && RXPLLCLKSEL[0]; // rv 0
  assign RXPLLCLKSEL_in[1] = (RXPLLCLKSEL[1] !== 1'bz) && RXPLLCLKSEL[1]; // rv 0
  assign RXPMARESET_in = (RXPMARESET !== 1'bz) && RXPMARESET; // rv 0
  assign RXPROGDIVRESET_in = (RXPROGDIVRESET !== 1'bz) && RXPROGDIVRESET; // rv 0
  assign RXRATEMODE_in = (RXRATEMODE !== 1'bz) && RXRATEMODE; // rv 0
  assign RXSYNCALLIN_in = (RXSYNCALLIN !== 1'bz) && RXSYNCALLIN; // rv 0
  assign RXSYNCIN_in = (RXSYNCIN !== 1'bz) && RXSYNCIN; // rv 0
  assign RXSYNCMODE_in = (RXSYNCMODE === 1'bz) || RXSYNCMODE; // rv 1
  assign RXSYSCLKSEL_in[0] = (RXSYSCLKSEL[0] !== 1'bz) && RXSYSCLKSEL[0]; // rv 0
  assign RXSYSCLKSEL_in[1] = (RXSYSCLKSEL[1] !== 1'bz) && RXSYSCLKSEL[1]; // rv 0
  assign RXTERMINATION_in = (RXTERMINATION !== 1'bz) && RXTERMINATION; // rv 0
  assign RXUSERRDY_in = (RXUSERRDY !== 1'bz) && RXUSERRDY; // rv 0
  assign SIGVALIDCLK_in = (SIGVALIDCLK !== 1'bz) && SIGVALIDCLK; // rv 0
  assign TSTIN_in[0] = (TSTIN[0] !== 1'bz) && TSTIN[0]; // rv 0
  assign TSTIN_in[10] = (TSTIN[10] !== 1'bz) && TSTIN[10]; // rv 0
  assign TSTIN_in[11] = (TSTIN[11] !== 1'bz) && TSTIN[11]; // rv 0
  assign TSTIN_in[12] = (TSTIN[12] !== 1'bz) && TSTIN[12]; // rv 0
  assign TSTIN_in[13] = (TSTIN[13] !== 1'bz) && TSTIN[13]; // rv 0
  assign TSTIN_in[14] = (TSTIN[14] !== 1'bz) && TSTIN[14]; // rv 0
  assign TSTIN_in[15] = (TSTIN[15] !== 1'bz) && TSTIN[15]; // rv 0
  assign TSTIN_in[16] = (TSTIN[16] !== 1'bz) && TSTIN[16]; // rv 0
  assign TSTIN_in[17] = (TSTIN[17] !== 1'bz) && TSTIN[17]; // rv 0
  assign TSTIN_in[18] = (TSTIN[18] !== 1'bz) && TSTIN[18]; // rv 0
  assign TSTIN_in[19] = (TSTIN[19] !== 1'bz) && TSTIN[19]; // rv 0
  assign TSTIN_in[1] = (TSTIN[1] !== 1'bz) && TSTIN[1]; // rv 0
  assign TSTIN_in[2] = (TSTIN[2] !== 1'bz) && TSTIN[2]; // rv 0
  assign TSTIN_in[3] = (TSTIN[3] !== 1'bz) && TSTIN[3]; // rv 0
  assign TSTIN_in[4] = (TSTIN[4] !== 1'bz) && TSTIN[4]; // rv 0
  assign TSTIN_in[5] = (TSTIN[5] !== 1'bz) && TSTIN[5]; // rv 0
  assign TSTIN_in[6] = (TSTIN[6] !== 1'bz) && TSTIN[6]; // rv 0
  assign TSTIN_in[7] = (TSTIN[7] !== 1'bz) && TSTIN[7]; // rv 0
  assign TSTIN_in[8] = (TSTIN[8] !== 1'bz) && TSTIN[8]; // rv 0
  assign TSTIN_in[9] = (TSTIN[9] !== 1'bz) && TSTIN[9]; // rv 0
  assign TXDATAEXTENDRSVD_in[0] = (TXDATAEXTENDRSVD[0] !== 1'bz) && TXDATAEXTENDRSVD[0]; // rv 0
  assign TXDATAEXTENDRSVD_in[1] = (TXDATAEXTENDRSVD[1] !== 1'bz) && TXDATAEXTENDRSVD[1]; // rv 0
  assign TXDATAEXTENDRSVD_in[2] = (TXDATAEXTENDRSVD[2] !== 1'bz) && TXDATAEXTENDRSVD[2]; // rv 0
  assign TXDATAEXTENDRSVD_in[3] = (TXDATAEXTENDRSVD[3] !== 1'bz) && TXDATAEXTENDRSVD[3]; // rv 0
  assign TXDATAEXTENDRSVD_in[4] = (TXDATAEXTENDRSVD[4] !== 1'bz) && TXDATAEXTENDRSVD[4]; // rv 0
  assign TXDATAEXTENDRSVD_in[5] = (TXDATAEXTENDRSVD[5] !== 1'bz) && TXDATAEXTENDRSVD[5]; // rv 0
  assign TXDATAEXTENDRSVD_in[6] = (TXDATAEXTENDRSVD[6] !== 1'bz) && TXDATAEXTENDRSVD[6]; // rv 0
  assign TXDATAEXTENDRSVD_in[7] = (TXDATAEXTENDRSVD[7] !== 1'bz) && TXDATAEXTENDRSVD[7]; // rv 0
  assign TXDCCFORCESTART_in = (TXDCCFORCESTART !== 1'bz) && TXDCCFORCESTART; // rv 0
  assign TXDCCRESET_in = (TXDCCRESET !== 1'bz) && TXDCCRESET; // rv 0
  assign TXDEEMPH_in[0] = (TXDEEMPH[0] !== 1'bz) && TXDEEMPH[0]; // rv 0
  assign TXDEEMPH_in[1] = (TXDEEMPH[1] !== 1'bz) && TXDEEMPH[1]; // rv 0
  assign TXDIFFCTRL_in[0] = (TXDIFFCTRL[0] !== 1'bz) && TXDIFFCTRL[0]; // rv 0
  assign TXDIFFCTRL_in[1] = (TXDIFFCTRL[1] !== 1'bz) && TXDIFFCTRL[1]; // rv 0
  assign TXDIFFCTRL_in[2] = (TXDIFFCTRL[2] !== 1'bz) && TXDIFFCTRL[2]; // rv 0
  assign TXDIFFCTRL_in[3] = (TXDIFFCTRL[3] !== 1'bz) && TXDIFFCTRL[3]; // rv 0
  assign TXDIFFCTRL_in[4] = (TXDIFFCTRL[4] !== 1'bz) && TXDIFFCTRL[4]; // rv 0
  assign TXDLYBYPASS_in = (TXDLYBYPASS !== 1'bz) && TXDLYBYPASS; // rv 0
  assign TXDLYEN_in = (TXDLYEN !== 1'bz) && TXDLYEN; // rv 0
  assign TXDLYHOLD_in = (TXDLYHOLD !== 1'bz) && TXDLYHOLD; // rv 0
  assign TXDLYOVRDEN_in = (TXDLYOVRDEN !== 1'bz) && TXDLYOVRDEN; // rv 0
  assign TXDLYSRESET_in = (TXDLYSRESET !== 1'bz) && TXDLYSRESET; // rv 0
  assign TXDLYUPDOWN_in = (TXDLYUPDOWN !== 1'bz) && TXDLYUPDOWN; // rv 0
  assign TXLATCLK_in = (TXLATCLK !== 1'bz) && TXLATCLK; // rv 0
  assign TXLFPSTRESET_in = (TXLFPSTRESET !== 1'bz) && TXLFPSTRESET; // rv 0
  assign TXLFPSU2LPEXIT_in = (TXLFPSU2LPEXIT !== 1'bz) && TXLFPSU2LPEXIT; // rv 0
  assign TXLFPSU3WAKE_in = (TXLFPSU3WAKE !== 1'bz) && TXLFPSU3WAKE; // rv 0
  assign TXMAINCURSOR_in[0] = (TXMAINCURSOR[0] !== 1'bz) && TXMAINCURSOR[0]; // rv 0
  assign TXMAINCURSOR_in[1] = (TXMAINCURSOR[1] !== 1'bz) && TXMAINCURSOR[1]; // rv 0
  assign TXMAINCURSOR_in[2] = (TXMAINCURSOR[2] !== 1'bz) && TXMAINCURSOR[2]; // rv 0
  assign TXMAINCURSOR_in[3] = (TXMAINCURSOR[3] !== 1'bz) && TXMAINCURSOR[3]; // rv 0
  assign TXMAINCURSOR_in[4] = (TXMAINCURSOR[4] !== 1'bz) && TXMAINCURSOR[4]; // rv 0
  assign TXMAINCURSOR_in[5] = (TXMAINCURSOR[5] !== 1'bz) && TXMAINCURSOR[5]; // rv 0
  assign TXMAINCURSOR_in[6] = (TXMAINCURSOR[6] !== 1'bz) && TXMAINCURSOR[6]; // rv 0
  assign TXMARGIN_in[0] = (TXMARGIN[0] !== 1'bz) && TXMARGIN[0]; // rv 0
  assign TXMARGIN_in[1] = (TXMARGIN[1] !== 1'bz) && TXMARGIN[1]; // rv 0
  assign TXMARGIN_in[2] = (TXMARGIN[2] !== 1'bz) && TXMARGIN[2]; // rv 0
  assign TXMUXDCDEXHOLD_in = (TXMUXDCDEXHOLD !== 1'bz) && TXMUXDCDEXHOLD; // rv 0
  assign TXMUXDCDORWREN_in = (TXMUXDCDORWREN !== 1'bz) && TXMUXDCDORWREN; // rv 0
  assign TXONESZEROS_in = (TXONESZEROS !== 1'bz) && TXONESZEROS; // rv 0
  assign TXOUTCLKSEL_in[0] = (TXOUTCLKSEL[0] !== 1'bz) && TXOUTCLKSEL[0]; // rv 0
  assign TXOUTCLKSEL_in[1] = (TXOUTCLKSEL[1] !== 1'bz) && TXOUTCLKSEL[1]; // rv 0
  assign TXOUTCLKSEL_in[2] = (TXOUTCLKSEL[2] !== 1'bz) && TXOUTCLKSEL[2]; // rv 0
  assign TXPCSRESET_in = (TXPCSRESET !== 1'bz) && TXPCSRESET; // rv 0
  assign TXPDELECIDLEMODE_in = (TXPDELECIDLEMODE !== 1'bz) && TXPDELECIDLEMODE; // rv 0
  assign TXPHALIGNEN_in = (TXPHALIGNEN !== 1'bz) && TXPHALIGNEN; // rv 0
  assign TXPHALIGN_in = (TXPHALIGN !== 1'bz) && TXPHALIGN; // rv 0
  assign TXPHDLYPD_in = (TXPHDLYPD !== 1'bz) && TXPHDLYPD; // rv 0
  assign TXPHDLYRESET_in = (TXPHDLYRESET !== 1'bz) && TXPHDLYRESET; // rv 0
  assign TXPHDLYTSTCLK_in = (TXPHDLYTSTCLK !== 1'bz) && TXPHDLYTSTCLK; // rv 0
  assign TXPHINIT_in = (TXPHINIT !== 1'bz) && TXPHINIT; // rv 0
  assign TXPHOVRDEN_in = (TXPHOVRDEN !== 1'bz) && TXPHOVRDEN; // rv 0
  assign TXPIPPMEN_in = (TXPIPPMEN !== 1'bz) && TXPIPPMEN; // rv 0
  assign TXPIPPMOVRDEN_in = (TXPIPPMOVRDEN !== 1'bz) && TXPIPPMOVRDEN; // rv 0
  assign TXPIPPMPD_in = (TXPIPPMPD !== 1'bz) && TXPIPPMPD; // rv 0
  assign TXPIPPMSEL_in = (TXPIPPMSEL !== 1'bz) && TXPIPPMSEL; // rv 0
  assign TXPIPPMSTEPSIZE_in[0] = (TXPIPPMSTEPSIZE[0] !== 1'bz) && TXPIPPMSTEPSIZE[0]; // rv 0
  assign TXPIPPMSTEPSIZE_in[1] = (TXPIPPMSTEPSIZE[1] !== 1'bz) && TXPIPPMSTEPSIZE[1]; // rv 0
  assign TXPIPPMSTEPSIZE_in[2] = (TXPIPPMSTEPSIZE[2] !== 1'bz) && TXPIPPMSTEPSIZE[2]; // rv 0
  assign TXPIPPMSTEPSIZE_in[3] = (TXPIPPMSTEPSIZE[3] !== 1'bz) && TXPIPPMSTEPSIZE[3]; // rv 0
  assign TXPIPPMSTEPSIZE_in[4] = (TXPIPPMSTEPSIZE[4] !== 1'bz) && TXPIPPMSTEPSIZE[4]; // rv 0
  assign TXPISOPD_in = (TXPISOPD !== 1'bz) && TXPISOPD; // rv 0
  assign TXPLLCLKSEL_in[0] = (TXPLLCLKSEL[0] !== 1'bz) && TXPLLCLKSEL[0]; // rv 0
  assign TXPLLCLKSEL_in[1] = (TXPLLCLKSEL[1] !== 1'bz) && TXPLLCLKSEL[1]; // rv 0
  assign TXPMARESET_in = (TXPMARESET !== 1'bz) && TXPMARESET; // rv 0
  assign TXPOSTCURSOR_in[0] = (TXPOSTCURSOR[0] !== 1'bz) && TXPOSTCURSOR[0]; // rv 0
  assign TXPOSTCURSOR_in[1] = (TXPOSTCURSOR[1] !== 1'bz) && TXPOSTCURSOR[1]; // rv 0
  assign TXPOSTCURSOR_in[2] = (TXPOSTCURSOR[2] !== 1'bz) && TXPOSTCURSOR[2]; // rv 0
  assign TXPOSTCURSOR_in[3] = (TXPOSTCURSOR[3] !== 1'bz) && TXPOSTCURSOR[3]; // rv 0
  assign TXPOSTCURSOR_in[4] = (TXPOSTCURSOR[4] !== 1'bz) && TXPOSTCURSOR[4]; // rv 0
  assign TXPRECURSOR_in[0] = (TXPRECURSOR[0] !== 1'bz) && TXPRECURSOR[0]; // rv 0
  assign TXPRECURSOR_in[1] = (TXPRECURSOR[1] !== 1'bz) && TXPRECURSOR[1]; // rv 0
  assign TXPRECURSOR_in[2] = (TXPRECURSOR[2] !== 1'bz) && TXPRECURSOR[2]; // rv 0
  assign TXPRECURSOR_in[3] = (TXPRECURSOR[3] !== 1'bz) && TXPRECURSOR[3]; // rv 0
  assign TXPRECURSOR_in[4] = (TXPRECURSOR[4] !== 1'bz) && TXPRECURSOR[4]; // rv 0
  assign TXPROGDIVRESET_in = (TXPROGDIVRESET !== 1'bz) && TXPROGDIVRESET; // rv 0
  assign TXRATEMODE_in = (TXRATEMODE !== 1'bz) && TXRATEMODE; // rv 0
  assign TXSWING_in = (TXSWING !== 1'bz) && TXSWING; // rv 0
  assign TXSYNCALLIN_in = (TXSYNCALLIN !== 1'bz) && TXSYNCALLIN; // rv 0
  assign TXSYNCIN_in = (TXSYNCIN !== 1'bz) && TXSYNCIN; // rv 0
  assign TXSYNCMODE_in = (TXSYNCMODE === 1'bz) || TXSYNCMODE; // rv 1
  assign TXSYSCLKSEL_in[0] = (TXSYSCLKSEL[0] !== 1'bz) && TXSYSCLKSEL[0]; // rv 0
  assign TXSYSCLKSEL_in[1] = (TXSYSCLKSEL[1] !== 1'bz) && TXSYSCLKSEL[1]; // rv 0
  assign TXUSERRDY_in = (TXUSERRDY !== 1'bz) && TXUSERRDY; // rv 0
  assign TXUSRCLK_in = (TXUSRCLK !== 1'bz) && TXUSRCLK; // rv 0


  assign gt_intclk = gt_clk_int;

  initial begin

	#1;
  trig_attr = ~trig_attr;
	
	gt_clk_int = 1'b0;
  forever #10000 gt_clk_int = ~gt_clk_int;

  end 


`ifdef XIL_XECLIB
  assign RX_PROGDIV_CFG_BIN = RX_PROGDIV_CFG_REG * 1000;
  
  assign TX_PROGDIV_CFG_BIN = TX_PROGDIV_CFG_REG * 1000;
  
`else
  always @ (trig_attr) begin
  #1;
  RX_PROGDIV_CFG_BIN = RX_PROGDIV_CFG_REG * 1000;
  
  TX_PROGDIV_CFG_BIN = TX_PROGDIV_CFG_REG * 1000;
  
  end
`endif


`ifndef XIL_XECLIB
always @ (trig_attr) begin
  #1;
  if ((attr_test == 1'b1) ||
      ((ALIGN_COMMA_DOUBLE_REG != "FALSE") &&
       (ALIGN_COMMA_DOUBLE_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-129] ALIGN_COMMA_DOUBLE attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, ALIGN_COMMA_DOUBLE_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((ALIGN_COMMA_WORD_REG != 1) &&
       (ALIGN_COMMA_WORD_REG != 2) &&
       (ALIGN_COMMA_WORD_REG != 4))) begin
    $display("Error: [Unisim %s-131] ALIGN_COMMA_WORD attribute is set to %d.  Legal values for this attribute are 1, 2 or 4. Instance: %m", MODULE_NAME, ALIGN_COMMA_WORD_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((ALIGN_MCOMMA_DET_REG != "TRUE") &&
       (ALIGN_MCOMMA_DET_REG != "FALSE"))) begin
    $display("Error: [Unisim %s-132] ALIGN_MCOMMA_DET attribute is set to %s.  Legal values for this attribute are TRUE or FALSE. Instance: %m", MODULE_NAME, ALIGN_MCOMMA_DET_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((ALIGN_PCOMMA_DET_REG != "TRUE") &&
       (ALIGN_PCOMMA_DET_REG != "FALSE"))) begin
    $display("Error: [Unisim %s-134] ALIGN_PCOMMA_DET attribute is set to %s.  Legal values for this attribute are TRUE or FALSE. Instance: %m", MODULE_NAME, ALIGN_PCOMMA_DET_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CBCC_DATA_SOURCE_SEL_REG != "DECODED") &&
       (CBCC_DATA_SOURCE_SEL_REG != "ENCODED"))) begin
    $display("Error: [Unisim %s-268] CBCC_DATA_SOURCE_SEL attribute is set to %s.  Legal values for this attribute are DECODED or ENCODED. Instance: %m", MODULE_NAME, CBCC_DATA_SOURCE_SEL_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CHAN_BOND_KEEP_ALIGN_REG != "FALSE") &&
       (CHAN_BOND_KEEP_ALIGN_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-271] CHAN_BOND_KEEP_ALIGN attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CHAN_BOND_KEEP_ALIGN_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CHAN_BOND_MAX_SKEW_REG != 7) &&
       (CHAN_BOND_MAX_SKEW_REG != 1) &&
       (CHAN_BOND_MAX_SKEW_REG != 2) &&
       (CHAN_BOND_MAX_SKEW_REG != 3) &&
       (CHAN_BOND_MAX_SKEW_REG != 4) &&
       (CHAN_BOND_MAX_SKEW_REG != 5) &&
       (CHAN_BOND_MAX_SKEW_REG != 6) &&
       (CHAN_BOND_MAX_SKEW_REG != 8) &&
       (CHAN_BOND_MAX_SKEW_REG != 9) &&
       (CHAN_BOND_MAX_SKEW_REG != 10) &&
       (CHAN_BOND_MAX_SKEW_REG != 11) &&
       (CHAN_BOND_MAX_SKEW_REG != 12) &&
       (CHAN_BOND_MAX_SKEW_REG != 13) &&
       (CHAN_BOND_MAX_SKEW_REG != 14))) begin
    $display("Error: [Unisim %s-272] CHAN_BOND_MAX_SKEW attribute is set to %d.  Legal values for this attribute are 7, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13 or 14. Instance: %m", MODULE_NAME, CHAN_BOND_MAX_SKEW_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CHAN_BOND_SEQ_2_USE_REG != "FALSE") &&
       (CHAN_BOND_SEQ_2_USE_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-283] CHAN_BOND_SEQ_2_USE attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CHAN_BOND_SEQ_2_USE_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CHAN_BOND_SEQ_LEN_REG != 2) &&
       (CHAN_BOND_SEQ_LEN_REG != 1) &&
       (CHAN_BOND_SEQ_LEN_REG != 3) &&
       (CHAN_BOND_SEQ_LEN_REG != 4))) begin
    $display("Error: [Unisim %s-284] CHAN_BOND_SEQ_LEN attribute is set to %d.  Legal values for this attribute are 2, 1, 3 or 4. Instance: %m", MODULE_NAME, CHAN_BOND_SEQ_LEN_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_CORRECT_USE_REG != "TRUE") &&
       (CLK_CORRECT_USE_REG != "FALSE"))) begin
    $display("Error: [Unisim %s-295] CLK_CORRECT_USE attribute is set to %s.  Legal values for this attribute are TRUE or FALSE. Instance: %m", MODULE_NAME, CLK_CORRECT_USE_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_COR_KEEP_IDLE_REG != "FALSE") &&
       (CLK_COR_KEEP_IDLE_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-296] CLK_COR_KEEP_IDLE attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_COR_KEEP_IDLE_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_COR_MAX_LAT_REG < 3) || (CLK_COR_MAX_LAT_REG > 60))) begin
    $display("Error: [Unisim %s-297] CLK_COR_MAX_LAT attribute is set to %d.  Legal values for this attribute are 3 to 60. Instance: %m", MODULE_NAME, CLK_COR_MAX_LAT_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_COR_MIN_LAT_REG < 3) || (CLK_COR_MIN_LAT_REG > 63))) begin
    $display("Error: [Unisim %s-298] CLK_COR_MIN_LAT attribute is set to %d.  Legal values for this attribute are 3 to 63. Instance: %m", MODULE_NAME, CLK_COR_MIN_LAT_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_COR_PRECEDENCE_REG != "TRUE") &&
       (CLK_COR_PRECEDENCE_REG != "FALSE"))) begin
    $display("Error: [Unisim %s-299] CLK_COR_PRECEDENCE attribute is set to %s.  Legal values for this attribute are TRUE or FALSE. Instance: %m", MODULE_NAME, CLK_COR_PRECEDENCE_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_COR_REPEAT_WAIT_REG < 0) || (CLK_COR_REPEAT_WAIT_REG > 31))) begin
    $display("Error: [Unisim %s-300] CLK_COR_REPEAT_WAIT attribute is set to %d.  Legal values for this attribute are 0 to 31. Instance: %m", MODULE_NAME, CLK_COR_REPEAT_WAIT_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_COR_SEQ_2_USE_REG != "FALSE") &&
       (CLK_COR_SEQ_2_USE_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-311] CLK_COR_SEQ_2_USE attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_COR_SEQ_2_USE_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CLK_COR_SEQ_LEN_REG != 2) &&
       (CLK_COR_SEQ_LEN_REG != 1) &&
       (CLK_COR_SEQ_LEN_REG != 3) &&
       (CLK_COR_SEQ_LEN_REG != 4))) begin
    $display("Error: [Unisim %s-312] CLK_COR_SEQ_LEN attribute is set to %d.  Legal values for this attribute are 2, 1, 3 or 4. Instance: %m", MODULE_NAME, CLK_COR_SEQ_LEN_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CPLL_FBDIV_REG != 4) &&
       (CPLL_FBDIV_REG != 1) &&
       (CPLL_FBDIV_REG != 2) &&
       (CPLL_FBDIV_REG != 3) &&
       (CPLL_FBDIV_REG != 5) &&
       (CPLL_FBDIV_REG != 6) &&
       (CPLL_FBDIV_REG != 8) &&
       (CPLL_FBDIV_REG != 10) &&
       (CPLL_FBDIV_REG != 12) &&
       (CPLL_FBDIV_REG != 16) &&
       (CPLL_FBDIV_REG != 20))) begin
    $display("Error: [Unisim %s-317] CPLL_FBDIV attribute is set to %d.  Legal values for this attribute are 4, 1, 2, 3, 5, 6, 8, 10, 12, 16 or 20. Instance: %m", MODULE_NAME, CPLL_FBDIV_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CPLL_FBDIV_45_REG != 4) &&
       (CPLL_FBDIV_45_REG != 5))) begin
    $display("Error: [Unisim %s-318] CPLL_FBDIV_45 attribute is set to %d.  Legal values for this attribute are 4 or 5. Instance: %m", MODULE_NAME, CPLL_FBDIV_45_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((CPLL_REFCLK_DIV_REG != 1) &&
       (CPLL_REFCLK_DIV_REG != 2) &&
       (CPLL_REFCLK_DIV_REG != 3) &&
       (CPLL_REFCLK_DIV_REG != 4) &&
       (CPLL_REFCLK_DIV_REG != 5) &&
       (CPLL_REFCLK_DIV_REG != 6) &&
       (CPLL_REFCLK_DIV_REG != 8) &&
       (CPLL_REFCLK_DIV_REG != 10) &&
       (CPLL_REFCLK_DIV_REG != 12) &&
       (CPLL_REFCLK_DIV_REG != 16) &&
       (CPLL_REFCLK_DIV_REG != 20))) begin
    $display("Error: [Unisim %s-321] CPLL_REFCLK_DIV attribute is set to %d.  Legal values for this attribute are 1, 2, 3, 4, 5, 6, 8, 10, 12, 16 or 20. Instance: %m", MODULE_NAME, CPLL_REFCLK_DIV_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DDI_REALIGN_WAIT_REG < 0) || (DDI_REALIGN_WAIT_REG > 31))) begin
    $display("Error: [Unisim %s-338] DDI_REALIGN_WAIT attribute is set to %d.  Legal values for this attribute are 0 to 31. Instance: %m", MODULE_NAME, DDI_REALIGN_WAIT_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DEC_MCOMMA_DETECT_REG != "TRUE") &&
       (DEC_MCOMMA_DETECT_REG != "FALSE"))) begin
    $display("Error: [Unisim %s-339] DEC_MCOMMA_DETECT attribute is set to %s.  Legal values for this attribute are TRUE or FALSE. Instance: %m", MODULE_NAME, DEC_MCOMMA_DETECT_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DEC_PCOMMA_DETECT_REG != "TRUE") &&
       (DEC_PCOMMA_DETECT_REG != "FALSE"))) begin
    $display("Error: [Unisim %s-340] DEC_PCOMMA_DETECT attribute is set to %s.  Legal values for this attribute are TRUE or FALSE. Instance: %m", MODULE_NAME, DEC_PCOMMA_DETECT_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((DEC_VALID_COMMA_ONLY_REG != "TRUE") &&
       (DEC_VALID_COMMA_ONLY_REG != "FALSE"))) begin
    $display("Error: [Unisim %s-341] DEC_VALID_COMMA_ONLY attribute is set to %s.  Legal values for this attribute are TRUE or FALSE. Instance: %m", MODULE_NAME, DEC_VALID_COMMA_ONLY_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((ES_ERRDET_EN_REG != "FALSE") &&
       (ES_ERRDET_EN_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-347] ES_ERRDET_EN attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, ES_ERRDET_EN_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((ES_EYE_SCAN_EN_REG != "FALSE") &&
       (ES_EYE_SCAN_EN_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-348] ES_EYE_SCAN_EN attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, ES_EYE_SCAN_EN_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((EYESCAN_VP_RANGE_REG != 0) &&
       (EYESCAN_VP_RANGE_REG != 1) &&
       (EYESCAN_VP_RANGE_REG != 2) &&
       (EYESCAN_VP_RANGE_REG != 3))) begin
    $display("Error: [Unisim %s-381] EYESCAN_VP_RANGE attribute is set to %d.  Legal values for this attribute are 0, 1, 2 or 3. Instance: %m", MODULE_NAME, EYESCAN_VP_RANGE_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((FTS_LANE_DESKEW_EN_REG != "FALSE") &&
       (FTS_LANE_DESKEW_EN_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-385] FTS_LANE_DESKEW_EN attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, FTS_LANE_DESKEW_EN_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((LPBK_BIAS_CTRL_REG != 4) &&
       (LPBK_BIAS_CTRL_REG != 0) &&
       (LPBK_BIAS_CTRL_REG != 1) &&
       (LPBK_BIAS_CTRL_REG != 2) &&
       (LPBK_BIAS_CTRL_REG != 3) &&
       (LPBK_BIAS_CTRL_REG != 5) &&
       (LPBK_BIAS_CTRL_REG != 6) &&
       (LPBK_BIAS_CTRL_REG != 7))) begin
    $display("Error: [Unisim %s-394] LPBK_BIAS_CTRL attribute is set to %d.  Legal values for this attribute are 4, 0, 1, 2, 3, 5, 6 or 7. Instance: %m", MODULE_NAME, LPBK_BIAS_CTRL_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((LPBK_IND_CTRL0_REG != 5) &&
       (LPBK_IND_CTRL0_REG != 0) &&
       (LPBK_IND_CTRL0_REG != 1) &&
       (LPBK_IND_CTRL0_REG != 2) &&
       (LPBK_IND_CTRL0_REG != 3) &&
       (LPBK_IND_CTRL0_REG != 4) &&
       (LPBK_IND_CTRL0_REG != 6) &&
       (LPBK_IND_CTRL0_REG != 7))) begin
    $display("Error: [Unisim %s-397] LPBK_IND_CTRL0 attribute is set to %d.  Legal values for this attribute are 5, 0, 1, 2, 3, 4, 6 or 7. Instance: %m", MODULE_NAME, LPBK_IND_CTRL0_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((LPBK_IND_CTRL1_REG != 5) &&
       (LPBK_IND_CTRL1_REG != 0) &&
       (LPBK_IND_CTRL1_REG != 1) &&
       (LPBK_IND_CTRL1_REG != 2) &&
       (LPBK_IND_CTRL1_REG != 3) &&
       (LPBK_IND_CTRL1_REG != 4) &&
       (LPBK_IND_CTRL1_REG != 6) &&
       (LPBK_IND_CTRL1_REG != 7))) begin
    $display("Error: [Unisim %s-398] LPBK_IND_CTRL1 attribute is set to %d.  Legal values for this attribute are 5, 0, 1, 2, 3, 4, 6 or 7. Instance: %m", MODULE_NAME, LPBK_IND_CTRL1_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((LPBK_IND_CTRL2_REG != 5) &&
       (LPBK_IND_CTRL2_REG != 0) &&
       (LPBK_IND_CTRL2_REG != 1) &&
       (LPBK_IND_CTRL2_REG != 2) &&
       (LPBK_IND_CTRL2_REG != 3) &&
       (LPBK_IND_CTRL2_REG != 4) &&
       (LPBK_IND_CTRL2_REG != 6) &&
       (LPBK_IND_CTRL2_REG != 7))) begin
    $display("Error: [Unisim %s-399] LPBK_IND_CTRL2 attribute is set to %d.  Legal values for this attribute are 5, 0, 1, 2, 3, 4, 6 or 7. Instance: %m", MODULE_NAME, LPBK_IND_CTRL2_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((LPBK_RG_CTRL_REG != 2) &&
       (LPBK_RG_CTRL_REG != 0) &&
       (LPBK_RG_CTRL_REG != 1) &&
       (LPBK_RG_CTRL_REG != 3))) begin
    $display("Error: [Unisim %s-400] LPBK_RG_CTRL attribute is set to %d.  Legal values for this attribute are 2, 0, 1 or 3. Instance: %m", MODULE_NAME, LPBK_RG_CTRL_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PCI3_AUTO_REALIGN_REG != "FRST_SMPL") &&
       (PCI3_AUTO_REALIGN_REG != "OVR_1K_BLK") &&
       (PCI3_AUTO_REALIGN_REG != "OVR_8_BLK") &&
       (PCI3_AUTO_REALIGN_REG != "OVR_64_BLK"))) begin
    $display("Error: [Unisim %s-403] PCI3_AUTO_REALIGN attribute is set to %s.  Legal values for this attribute are FRST_SMPL, OVR_1K_BLK, OVR_8_BLK or OVR_64_BLK. Instance: %m", MODULE_NAME, PCI3_AUTO_REALIGN_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PCIE_64B_DYN_CLKSW_DIS_REG != "FALSE") &&
       (PCIE_64B_DYN_CLKSW_DIS_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-417] PCIE_64B_DYN_CLKSW_DIS attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PCIE_64B_DYN_CLKSW_DIS_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PCIE_GEN4_64BIT_INT_EN_REG != "FALSE") &&
       (PCIE_GEN4_64BIT_INT_EN_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-419] PCIE_GEN4_64BIT_INT_EN attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PCIE_GEN4_64BIT_INT_EN_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PCS_PCIE_EN_REG != "FALSE") &&
       (PCS_PCIE_EN_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-427] PCS_PCIE_EN attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PCS_PCIE_EN_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PREIQ_FREQ_BST_REG != 0) &&
       (PREIQ_FREQ_BST_REG != 1) &&
       (PREIQ_FREQ_BST_REG != 2) &&
       (PREIQ_FREQ_BST_REG != 3))) begin
    $display("Error: [Unisim %s-432] PREIQ_FREQ_BST attribute is set to %d.  Legal values for this attribute are 0, 1, 2 or 3. Instance: %m", MODULE_NAME, PREIQ_FREQ_BST_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RXBUF_ADDR_MODE_REG != "FULL") &&
       (RXBUF_ADDR_MODE_REG != "FAST"))) begin
    $display("Error: [Unisim %s-439] RXBUF_ADDR_MODE attribute is set to %s.  Legal values for this attribute are FULL or FAST. Instance: %m", MODULE_NAME, RXBUF_ADDR_MODE_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RXBUF_EN_REG != "TRUE") &&
       (RXBUF_EN_REG != "FALSE"))) begin
    $display("Error: [Unisim %s-442] RXBUF_EN attribute is set to %s.  Legal values for this attribute are TRUE or FALSE. Instance: %m", MODULE_NAME, RXBUF_EN_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RXBUF_RESET_ON_CB_CHANGE_REG != "TRUE") &&
       (RXBUF_RESET_ON_CB_CHANGE_REG != "FALSE"))) begin
    $display("Error: [Unisim %s-443] RXBUF_RESET_ON_CB_CHANGE attribute is set to %s.  Legal values for this attribute are TRUE or FALSE. Instance: %m", MODULE_NAME, RXBUF_RESET_ON_CB_CHANGE_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RXBUF_RESET_ON_COMMAALIGN_REG != "FALSE") &&
       (RXBUF_RESET_ON_COMMAALIGN_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-444] RXBUF_RESET_ON_COMMAALIGN attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, RXBUF_RESET_ON_COMMAALIGN_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RXBUF_RESET_ON_EIDLE_REG != "FALSE") &&
       (RXBUF_RESET_ON_EIDLE_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-445] RXBUF_RESET_ON_EIDLE attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, RXBUF_RESET_ON_EIDLE_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RXBUF_RESET_ON_RATE_CHANGE_REG != "TRUE") &&
       (RXBUF_RESET_ON_RATE_CHANGE_REG != "FALSE"))) begin
    $display("Error: [Unisim %s-446] RXBUF_RESET_ON_RATE_CHANGE attribute is set to %s.  Legal values for this attribute are TRUE or FALSE. Instance: %m", MODULE_NAME, RXBUF_RESET_ON_RATE_CHANGE_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RXBUF_THRESH_OVFLW_REG < 0) || (RXBUF_THRESH_OVFLW_REG > 63))) begin
    $display("Error: [Unisim %s-447] RXBUF_THRESH_OVFLW attribute is set to %d.  Legal values for this attribute are 0 to 63. Instance: %m", MODULE_NAME, RXBUF_THRESH_OVFLW_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RXBUF_THRESH_OVRD_REG != "FALSE") &&
       (RXBUF_THRESH_OVRD_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-448] RXBUF_THRESH_OVRD attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, RXBUF_THRESH_OVRD_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RXBUF_THRESH_UNDFLW_REG < 0) || (RXBUF_THRESH_UNDFLW_REG > 63))) begin
    $display("Error: [Unisim %s-449] RXBUF_THRESH_UNDFLW attribute is set to %d.  Legal values for this attribute are 0 to 63. Instance: %m", MODULE_NAME, RXBUF_THRESH_UNDFLW_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RXELECIDLE_CFG_REG != "SIGCFG_4") &&
       (RXELECIDLE_CFG_REG != "SIGCFG_1") &&
       (RXELECIDLE_CFG_REG != "SIGCFG_2") &&
       (RXELECIDLE_CFG_REG != "SIGCFG_3") &&
       (RXELECIDLE_CFG_REG != "SIGCFG_6") &&
       (RXELECIDLE_CFG_REG != "SIGCFG_8") &&
       (RXELECIDLE_CFG_REG != "SIGCFG_12") &&
       (RXELECIDLE_CFG_REG != "SIGCFG_16"))) begin
    $display("Error: [Unisim %s-536] RXELECIDLE_CFG attribute is set to %s.  Legal values for this attribute are SIGCFG_4, SIGCFG_1, SIGCFG_2, SIGCFG_3, SIGCFG_6, SIGCFG_8, SIGCFG_12 or SIGCFG_16. Instance: %m", MODULE_NAME, RXELECIDLE_CFG_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RXGBOX_FIFO_INIT_RD_ADDR_REG != 4) &&
       (RXGBOX_FIFO_INIT_RD_ADDR_REG != 2) &&
       (RXGBOX_FIFO_INIT_RD_ADDR_REG != 3) &&
       (RXGBOX_FIFO_INIT_RD_ADDR_REG != 5))) begin
    $display("Error: [Unisim %s-537] RXGBOX_FIFO_INIT_RD_ADDR attribute is set to %d.  Legal values for this attribute are 4, 2, 3 or 5. Instance: %m", MODULE_NAME, RXGBOX_FIFO_INIT_RD_ADDR_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RXGEARBOX_EN_REG != "FALSE") &&
       (RXGEARBOX_EN_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-538] RXGEARBOX_EN attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, RXGEARBOX_EN_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RXOOB_CLK_CFG_REG != "PMA") &&
       (RXOOB_CLK_CFG_REG != "FABRIC"))) begin
    $display("Error: [Unisim %s-547] RXOOB_CLK_CFG attribute is set to %s.  Legal values for this attribute are PMA or FABRIC. Instance: %m", MODULE_NAME, RXOOB_CLK_CFG_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RXOUT_DIV_REG != 4) &&
       (RXOUT_DIV_REG != 1) &&
       (RXOUT_DIV_REG != 2) &&
       (RXOUT_DIV_REG != 8) &&
       (RXOUT_DIV_REG != 16) &&
       (RXOUT_DIV_REG != 32))) begin
    $display("Error: [Unisim %s-549] RXOUT_DIV attribute is set to %d.  Legal values for this attribute are 4, 1, 2, 8, 16 or 32. Instance: %m", MODULE_NAME, RXOUT_DIV_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RXPMACLK_SEL_REG != "DATA") &&
       (RXPMACLK_SEL_REG != "CROSSING") &&
       (RXPMACLK_SEL_REG != "EYESCAN"))) begin
    $display("Error: [Unisim %s-558] RXPMACLK_SEL attribute is set to %s.  Legal values for this attribute are DATA, CROSSING or EYESCAN. Instance: %m", MODULE_NAME, RXPMACLK_SEL_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RXPRBS_LINKACQ_CNT_REG < 15) || (RXPRBS_LINKACQ_CNT_REG > 255))) begin
    $display("Error: [Unisim %s-561] RXPRBS_LINKACQ_CNT attribute is set to %d.  Legal values for this attribute are 15 to 255. Instance: %m", MODULE_NAME, RXPRBS_LINKACQ_CNT_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RXSLIDE_AUTO_WAIT_REG != 7) &&
       (RXSLIDE_AUTO_WAIT_REG != 1) &&
       (RXSLIDE_AUTO_WAIT_REG != 2) &&
       (RXSLIDE_AUTO_WAIT_REG != 3) &&
       (RXSLIDE_AUTO_WAIT_REG != 4) &&
       (RXSLIDE_AUTO_WAIT_REG != 5) &&
       (RXSLIDE_AUTO_WAIT_REG != 6) &&
       (RXSLIDE_AUTO_WAIT_REG != 8) &&
       (RXSLIDE_AUTO_WAIT_REG != 9) &&
       (RXSLIDE_AUTO_WAIT_REG != 10) &&
       (RXSLIDE_AUTO_WAIT_REG != 11) &&
       (RXSLIDE_AUTO_WAIT_REG != 12) &&
       (RXSLIDE_AUTO_WAIT_REG != 13) &&
       (RXSLIDE_AUTO_WAIT_REG != 14) &&
       (RXSLIDE_AUTO_WAIT_REG != 15))) begin
    $display("Error: [Unisim %s-563] RXSLIDE_AUTO_WAIT attribute is set to %d.  Legal values for this attribute are 7, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14 or 15. Instance: %m", MODULE_NAME, RXSLIDE_AUTO_WAIT_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RXSLIDE_MODE_REG != "OFF") &&
       (RXSLIDE_MODE_REG != "AUTO") &&
       (RXSLIDE_MODE_REG != "PCS") &&
       (RXSLIDE_MODE_REG != "PMA"))) begin
    $display("Error: [Unisim %s-564] RXSLIDE_MODE attribute is set to %s.  Legal values for this attribute are OFF, AUTO, PCS or PMA. Instance: %m", MODULE_NAME, RXSLIDE_MODE_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RX_CLK25_DIV_REG < 1) || (RX_CLK25_DIV_REG > 32))) begin
    $display("Error: [Unisim %s-572] RX_CLK25_DIV attribute is set to %d.  Legal values for this attribute are 1 to 32. Instance: %m", MODULE_NAME, RX_CLK25_DIV_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RX_CM_SEL_REG != 2) &&
       (RX_CM_SEL_REG != 0) &&
       (RX_CM_SEL_REG != 1) &&
       (RX_CM_SEL_REG != 3))) begin
    $display("Error: [Unisim %s-577] RX_CM_SEL attribute is set to %d.  Legal values for this attribute are 2, 0, 1 or 3. Instance: %m", MODULE_NAME, RX_CM_SEL_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RX_CM_TRIM_REG != 12) &&
       (RX_CM_TRIM_REG != 0) &&
       (RX_CM_TRIM_REG != 1) &&
       (RX_CM_TRIM_REG != 2) &&
       (RX_CM_TRIM_REG != 3) &&
       (RX_CM_TRIM_REG != 4) &&
       (RX_CM_TRIM_REG != 5) &&
       (RX_CM_TRIM_REG != 6) &&
       (RX_CM_TRIM_REG != 7) &&
       (RX_CM_TRIM_REG != 8) &&
       (RX_CM_TRIM_REG != 9) &&
       (RX_CM_TRIM_REG != 10) &&
       (RX_CM_TRIM_REG != 11) &&
       (RX_CM_TRIM_REG != 13) &&
       (RX_CM_TRIM_REG != 14) &&
       (RX_CM_TRIM_REG != 15))) begin
    $display("Error: [Unisim %s-578] RX_CM_TRIM attribute is set to %d.  Legal values for this attribute are 12, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14 or 15. Instance: %m", MODULE_NAME, RX_CM_TRIM_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RX_DATA_WIDTH_REG != 20) &&
       (RX_DATA_WIDTH_REG != 16) &&
       (RX_DATA_WIDTH_REG != 32) &&
       (RX_DATA_WIDTH_REG != 40) &&
       (RX_DATA_WIDTH_REG != 64) &&
       (RX_DATA_WIDTH_REG != 80) &&
       (RX_DATA_WIDTH_REG != 128) &&
       (RX_DATA_WIDTH_REG != 160))) begin
    $display("Error: [Unisim %s-581] RX_DATA_WIDTH attribute is set to %d.  Legal values for this attribute are 20, 16, 32, 40, 64, 80, 128 or 160. Instance: %m", MODULE_NAME, RX_DATA_WIDTH_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RX_DEFER_RESET_BUF_EN_REG != "TRUE") &&
       (RX_DEFER_RESET_BUF_EN_REG != "FALSE"))) begin
    $display("Error: [Unisim %s-583] RX_DEFER_RESET_BUF_EN attribute is set to %s.  Legal values for this attribute are TRUE or FALSE. Instance: %m", MODULE_NAME, RX_DEFER_RESET_BUF_EN_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RX_DFELPM_CFG0_REG != 10) &&
       (RX_DFELPM_CFG0_REG != 0) &&
       (RX_DFELPM_CFG0_REG != 1) &&
       (RX_DFELPM_CFG0_REG != 11) &&
       (RX_DFELPM_CFG0_REG != 12) &&
       (RX_DFELPM_CFG0_REG != 13) &&
       (RX_DFELPM_CFG0_REG != 14) &&
       (RX_DFELPM_CFG0_REG != 15))) begin
    $display("Error: [Unisim %s-586] RX_DFELPM_CFG0 attribute is set to %d.  Legal values for this attribute are 10, 0, 1, 11, 12, 13, 14 or 15. Instance: %m", MODULE_NAME, RX_DFELPM_CFG0_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RX_DFE_AGC_CFG1_REG != 4) &&
       (RX_DFE_AGC_CFG1_REG != 0) &&
       (RX_DFE_AGC_CFG1_REG != 1) &&
       (RX_DFE_AGC_CFG1_REG != 2) &&
       (RX_DFE_AGC_CFG1_REG != 3) &&
       (RX_DFE_AGC_CFG1_REG != 5) &&
       (RX_DFE_AGC_CFG1_REG != 6) &&
       (RX_DFE_AGC_CFG1_REG != 7))) begin
    $display("Error: [Unisim %s-589] RX_DFE_AGC_CFG1 attribute is set to %d.  Legal values for this attribute are 4, 0, 1, 2, 3, 5, 6 or 7. Instance: %m", MODULE_NAME, RX_DFE_AGC_CFG1_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RX_DFE_KL_LPM_KH_CFG0_REG != 1) &&
       (RX_DFE_KL_LPM_KH_CFG0_REG != 0) &&
       (RX_DFE_KL_LPM_KH_CFG0_REG != 2) &&
       (RX_DFE_KL_LPM_KH_CFG0_REG != 3))) begin
    $display("Error: [Unisim %s-590] RX_DFE_KL_LPM_KH_CFG0 attribute is set to %d.  Legal values for this attribute are 1, 0, 2 or 3. Instance: %m", MODULE_NAME, RX_DFE_KL_LPM_KH_CFG0_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RX_DFE_KL_LPM_KH_CFG1_REG != 2) &&
       (RX_DFE_KL_LPM_KH_CFG1_REG != 0) &&
       (RX_DFE_KL_LPM_KH_CFG1_REG != 1) &&
       (RX_DFE_KL_LPM_KH_CFG1_REG != 3) &&
       (RX_DFE_KL_LPM_KH_CFG1_REG != 4) &&
       (RX_DFE_KL_LPM_KH_CFG1_REG != 5) &&
       (RX_DFE_KL_LPM_KH_CFG1_REG != 6) &&
       (RX_DFE_KL_LPM_KH_CFG1_REG != 7))) begin
    $display("Error: [Unisim %s-591] RX_DFE_KL_LPM_KH_CFG1 attribute is set to %d.  Legal values for this attribute are 2, 0, 1, 3, 4, 5, 6 or 7. Instance: %m", MODULE_NAME, RX_DFE_KL_LPM_KH_CFG1_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RX_DFE_KL_LPM_KL_CFG1_REG != 4) &&
       (RX_DFE_KL_LPM_KL_CFG1_REG != 0) &&
       (RX_DFE_KL_LPM_KL_CFG1_REG != 1) &&
       (RX_DFE_KL_LPM_KL_CFG1_REG != 2) &&
       (RX_DFE_KL_LPM_KL_CFG1_REG != 3) &&
       (RX_DFE_KL_LPM_KL_CFG1_REG != 5) &&
       (RX_DFE_KL_LPM_KL_CFG1_REG != 6) &&
       (RX_DFE_KL_LPM_KL_CFG1_REG != 7))) begin
    $display("Error: [Unisim %s-593] RX_DFE_KL_LPM_KL_CFG1 attribute is set to %d.  Legal values for this attribute are 4, 0, 1, 2, 3, 5, 6 or 7. Instance: %m", MODULE_NAME, RX_DFE_KL_LPM_KL_CFG1_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RX_DISPERR_SEQ_MATCH_REG != "TRUE") &&
       (RX_DISPERR_SEQ_MATCH_REG != "FALSE"))) begin
    $display("Error: [Unisim %s-595] RX_DISPERR_SEQ_MATCH attribute is set to %s.  Legal values for this attribute are TRUE or FALSE. Instance: %m", MODULE_NAME, RX_DISPERR_SEQ_MATCH_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RX_EN_SUM_RCAL_B_REG != 0) &&
       (RX_EN_SUM_RCAL_B_REG != 1))) begin
    $display("Error: [Unisim %s-598] RX_EN_SUM_RCAL_B attribute is set to %d.  Legal values for this attribute are 0 or 1. Instance: %m", MODULE_NAME, RX_EN_SUM_RCAL_B_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RX_INT_DATAWIDTH_REG != 1) &&
       (RX_INT_DATAWIDTH_REG != 0) &&
       (RX_INT_DATAWIDTH_REG != 2))) begin
    $display("Error: [Unisim %s-605] RX_INT_DATAWIDTH attribute is set to %d.  Legal values for this attribute are 1, 0 or 2. Instance: %m", MODULE_NAME, RX_INT_DATAWIDTH_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
     ((RX_PROGDIV_CFG_REG != 0.0) &&
      (RX_PROGDIV_CFG_REG != 4.0) &&
      (RX_PROGDIV_CFG_REG != 5.0) &&
      (RX_PROGDIV_CFG_REG != 8.0) &&
      (RX_PROGDIV_CFG_REG != 10.0) &&
      (RX_PROGDIV_CFG_REG != 16.0) &&
      (RX_PROGDIV_CFG_REG != 16.5) &&
      (RX_PROGDIV_CFG_REG != 20.0) &&
      (RX_PROGDIV_CFG_REG != 32.0) &&
      (RX_PROGDIV_CFG_REG != 33.0) &&
      (RX_PROGDIV_CFG_REG != 40.0) &&
      (RX_PROGDIV_CFG_REG != 64.0) &&
      (RX_PROGDIV_CFG_REG != 66.0) &&
      (RX_PROGDIV_CFG_REG != 80.0) &&
      (RX_PROGDIV_CFG_REG != 100.0) &&
      (RX_PROGDIV_CFG_REG != 128.0) &&
      (RX_PROGDIV_CFG_REG != 132.0))) begin
    $display("Error: [Unisim %s-608] RX_PROGDIV_CFG attribute is set to %f.  Legal values for this attribute are 0.0, 4.0, 5.0, 8.0, 10.0, 16.0, 16.5, 20.0, 32.0, 33.0, 40.0, 64.0, 66.0, 80.0, 100.0, 128.0 or 132.0. Instance: %m", MODULE_NAME, RX_PROGDIV_CFG_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RX_SIG_VALID_DLY_REG < 1) || (RX_SIG_VALID_DLY_REG > 32))) begin
    $display("Error: [Unisim %s-613] RX_SIG_VALID_DLY attribute is set to %d.  Legal values for this attribute are 1 to 32. Instance: %m", MODULE_NAME, RX_SIG_VALID_DLY_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RX_SUM_DEGEN_AVTT_OVERITE_REG != 0) &&
       (RX_SUM_DEGEN_AVTT_OVERITE_REG != 1))) begin
    $display("Error: [Unisim %s-614] RX_SUM_DEGEN_AVTT_OVERITE attribute is set to %d.  Legal values for this attribute are 0 or 1. Instance: %m", MODULE_NAME, RX_SUM_DEGEN_AVTT_OVERITE_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RX_SUM_PWR_SAVING_REG != 0) &&
       (RX_SUM_PWR_SAVING_REG != 1))) begin
    $display("Error: [Unisim %s-617] RX_SUM_PWR_SAVING attribute is set to %d.  Legal values for this attribute are 0 or 1. Instance: %m", MODULE_NAME, RX_SUM_PWR_SAVING_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((RX_XCLK_SEL_REG != "RXDES") &&
       (RX_XCLK_SEL_REG != "RXPMA") &&
       (RX_XCLK_SEL_REG != "RXUSR"))) begin
    $display("Error: [Unisim %s-630] RX_XCLK_SEL attribute is set to %s.  Legal values for this attribute are RXDES, RXPMA or RXUSR. Instance: %m", MODULE_NAME, RX_XCLK_SEL_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((SATA_CPLL_CFG_REG != "VCO_3000MHZ") &&
       (SATA_CPLL_CFG_REG != "VCO_750MHZ") &&
       (SATA_CPLL_CFG_REG != "VCO_1500MHZ") &&
       (SATA_CPLL_CFG_REG != "VCO_6000MHZ"))) begin
    $display("Error: [Unisim %s-636] SATA_CPLL_CFG attribute is set to %s.  Legal values for this attribute are VCO_3000MHZ, VCO_750MHZ, VCO_1500MHZ or VCO_6000MHZ. Instance: %m", MODULE_NAME, SATA_CPLL_CFG_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((SHOW_REALIGN_COMMA_REG != "TRUE") &&
       (SHOW_REALIGN_COMMA_REG != "FALSE"))) begin
    $display("Error: [Unisim %s-638] SHOW_REALIGN_COMMA attribute is set to %s.  Legal values for this attribute are TRUE or FALSE. Instance: %m", MODULE_NAME, SHOW_REALIGN_COMMA_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((SIM_DEVICE_REG != "ULTRASCALE_PLUS") &&
       (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES1") &&
       (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES1p") &&
       (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES2"))) begin
    $display("Error: [Unisim %s-639] SIM_DEVICE attribute is set to %s.  Legal values for this attribute are ULTRASCALE_PLUS, ULTRASCALE_PLUS_ES1, ULTRASCALE_PLUS_ES1p or ULTRASCALE_PLUS_ES2. Instance: %m", MODULE_NAME, SIM_DEVICE_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((SIM_MODE_REG != "FAST") &&
       (SIM_MODE_REG != "LEGACY"))) begin
    $display("Error: [Unisim %s-640] SIM_MODE attribute is set to %s.  Legal values for this attribute are FAST or LEGACY. Instance: %m", MODULE_NAME, SIM_MODE_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((SIM_RECEIVER_DETECT_PASS_REG != "TRUE") &&
       (SIM_RECEIVER_DETECT_PASS_REG != "FALSE"))) begin
    $display("Error: [Unisim %s-641] SIM_RECEIVER_DETECT_PASS attribute is set to %s.  Legal values for this attribute are TRUE or FALSE. Instance: %m", MODULE_NAME, SIM_RECEIVER_DETECT_PASS_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((SIM_RESET_SPEEDUP_REG != "TRUE") &&
       (SIM_RESET_SPEEDUP_REG != "FALSE"))) begin
    $display("Error: [Unisim %s-642] SIM_RESET_SPEEDUP attribute is set to %s.  Legal values for this attribute are TRUE or FALSE. Instance: %m", MODULE_NAME, SIM_RESET_SPEEDUP_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((SIM_TX_EIDLE_DRIVE_LEVEL_REG != "Z") &&
       (SIM_TX_EIDLE_DRIVE_LEVEL_REG != "HIGH") &&
       (SIM_TX_EIDLE_DRIVE_LEVEL_REG != "LOW") &&
       (SIM_TX_EIDLE_DRIVE_LEVEL_REG != "X"))) begin
    $display("Error: [Unisim %s-643] SIM_TX_EIDLE_DRIVE_LEVEL attribute is set to %s.  Legal values for this attribute are Z, HIGH, LOW or X. Instance: %m", MODULE_NAME, SIM_TX_EIDLE_DRIVE_LEVEL_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((TXBUF_EN_REG != "TRUE") &&
       (TXBUF_EN_REG != "FALSE"))) begin
    $display("Error: [Unisim %s-651] TXBUF_EN attribute is set to %s.  Legal values for this attribute are TRUE or FALSE. Instance: %m", MODULE_NAME, TXBUF_EN_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((TXBUF_RESET_ON_RATE_CHANGE_REG != "FALSE") &&
       (TXBUF_RESET_ON_RATE_CHANGE_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-652] TXBUF_RESET_ON_RATE_CHANGE attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, TXBUF_RESET_ON_RATE_CHANGE_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((TXDRV_FREQBAND_REG != 0) &&
       (TXDRV_FREQBAND_REG != 1) &&
       (TXDRV_FREQBAND_REG != 2) &&
       (TXDRV_FREQBAND_REG != 3))) begin
    $display("Error: [Unisim %s-655] TXDRV_FREQBAND attribute is set to %d.  Legal values for this attribute are 0, 1, 2 or 3. Instance: %m", MODULE_NAME, TXDRV_FREQBAND_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((TXFIFO_ADDR_CFG_REG != "LOW") &&
       (TXFIFO_ADDR_CFG_REG != "HIGH"))) begin
    $display("Error: [Unisim %s-660] TXFIFO_ADDR_CFG attribute is set to %s.  Legal values for this attribute are LOW or HIGH. Instance: %m", MODULE_NAME, TXFIFO_ADDR_CFG_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((TXGBOX_FIFO_INIT_RD_ADDR_REG != 4) &&
       (TXGBOX_FIFO_INIT_RD_ADDR_REG != 2) &&
       (TXGBOX_FIFO_INIT_RD_ADDR_REG != 3) &&
       (TXGBOX_FIFO_INIT_RD_ADDR_REG != 5) &&
       (TXGBOX_FIFO_INIT_RD_ADDR_REG != 6))) begin
    $display("Error: [Unisim %s-661] TXGBOX_FIFO_INIT_RD_ADDR attribute is set to %d.  Legal values for this attribute are 4, 2, 3, 5 or 6. Instance: %m", MODULE_NAME, TXGBOX_FIFO_INIT_RD_ADDR_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((TXGEARBOX_EN_REG != "FALSE") &&
       (TXGEARBOX_EN_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-662] TXGEARBOX_EN attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, TXGEARBOX_EN_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((TXOUT_DIV_REG != 4) &&
       (TXOUT_DIV_REG != 1) &&
       (TXOUT_DIV_REG != 2) &&
       (TXOUT_DIV_REG != 8) &&
       (TXOUT_DIV_REG != 16) &&
       (TXOUT_DIV_REG != 32))) begin
    $display("Error: [Unisim %s-664] TXOUT_DIV attribute is set to %d.  Legal values for this attribute are 4, 1, 2, 8, 16 or 32. Instance: %m", MODULE_NAME, TXOUT_DIV_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((TXSWBST_BST_REG != 1) &&
       (TXSWBST_BST_REG != 0) &&
       (TXSWBST_BST_REG != 2) &&
       (TXSWBST_BST_REG != 3))) begin
    $display("Error: [Unisim %s-680] TXSWBST_BST attribute is set to %d.  Legal values for this attribute are 1, 0, 2 or 3. Instance: %m", MODULE_NAME, TXSWBST_BST_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((TXSWBST_EN_REG != 0) &&
       (TXSWBST_EN_REG != 1))) begin
    $display("Error: [Unisim %s-681] TXSWBST_EN attribute is set to %d.  Legal values for this attribute are 0 or 1. Instance: %m", MODULE_NAME, TXSWBST_EN_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((TXSWBST_MAG_REG != 6) &&
       (TXSWBST_MAG_REG != 0) &&
       (TXSWBST_MAG_REG != 1) &&
       (TXSWBST_MAG_REG != 2) &&
       (TXSWBST_MAG_REG != 3) &&
       (TXSWBST_MAG_REG != 4) &&
       (TXSWBST_MAG_REG != 5) &&
       (TXSWBST_MAG_REG != 7))) begin
    $display("Error: [Unisim %s-682] TXSWBST_MAG attribute is set to %d.  Legal values for this attribute are 6, 0, 1, 2, 3, 4, 5 or 7. Instance: %m", MODULE_NAME, TXSWBST_MAG_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((TX_CLK25_DIV_REG < 1) || (TX_CLK25_DIV_REG > 32))) begin
    $display("Error: [Unisim %s-686] TX_CLK25_DIV attribute is set to %d.  Legal values for this attribute are 1 to 32. Instance: %m", MODULE_NAME, TX_CLK25_DIV_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((TX_DATA_WIDTH_REG != 20) &&
       (TX_DATA_WIDTH_REG != 16) &&
       (TX_DATA_WIDTH_REG != 32) &&
       (TX_DATA_WIDTH_REG != 40) &&
       (TX_DATA_WIDTH_REG != 64) &&
       (TX_DATA_WIDTH_REG != 80) &&
       (TX_DATA_WIDTH_REG != 128) &&
       (TX_DATA_WIDTH_REG != 160))) begin
    $display("Error: [Unisim %s-688] TX_DATA_WIDTH attribute is set to %d.  Legal values for this attribute are 20, 16, 32, 40, 64, 80, 128 or 160. Instance: %m", MODULE_NAME, TX_DATA_WIDTH_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((TX_DRIVE_MODE_REG != "DIRECT") &&
       (TX_DRIVE_MODE_REG != "PIPE") &&
       (TX_DRIVE_MODE_REG != "PIPEGEN3"))) begin
    $display("Error: [Unisim %s-695] TX_DRIVE_MODE attribute is set to %s.  Legal values for this attribute are DIRECT, PIPE or PIPEGEN3. Instance: %m", MODULE_NAME, TX_DRIVE_MODE_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((TX_INT_DATAWIDTH_REG != 1) &&
       (TX_INT_DATAWIDTH_REG != 0) &&
       (TX_INT_DATAWIDTH_REG != 2))) begin
    $display("Error: [Unisim %s-701] TX_INT_DATAWIDTH attribute is set to %d.  Legal values for this attribute are 1, 0 or 2. Instance: %m", MODULE_NAME, TX_INT_DATAWIDTH_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((TX_LOOPBACK_DRIVE_HIZ_REG != "FALSE") &&
       (TX_LOOPBACK_DRIVE_HIZ_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-702] TX_LOOPBACK_DRIVE_HIZ attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, TX_LOOPBACK_DRIVE_HIZ_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((TX_PI_BIASSET_REG != 0) &&
       (TX_PI_BIASSET_REG != 1) &&
       (TX_PI_BIASSET_REG != 2) &&
       (TX_PI_BIASSET_REG != 3))) begin
    $display("Error: [Unisim %s-716] TX_PI_BIASSET attribute is set to %d.  Legal values for this attribute are 0, 1, 2 or 3. Instance: %m", MODULE_NAME, TX_PI_BIASSET_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((TX_PROGCLK_SEL_REG != "POSTPI") &&
       (TX_PROGCLK_SEL_REG != "CPLL") &&
       (TX_PROGCLK_SEL_REG != "PREPI"))) begin
    $display("Error: [Unisim %s-721] TX_PROGCLK_SEL attribute is set to %s.  Legal values for this attribute are POSTPI, CPLL or PREPI. Instance: %m", MODULE_NAME, TX_PROGCLK_SEL_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
     ((TX_PROGDIV_CFG_REG != 0.0) &&
      (TX_PROGDIV_CFG_REG != 4.0) &&
      (TX_PROGDIV_CFG_REG != 5.0) &&
      (TX_PROGDIV_CFG_REG != 8.0) &&
      (TX_PROGDIV_CFG_REG != 10.0) &&
      (TX_PROGDIV_CFG_REG != 16.0) &&
      (TX_PROGDIV_CFG_REG != 16.5) &&
      (TX_PROGDIV_CFG_REG != 20.0) &&
      (TX_PROGDIV_CFG_REG != 32.0) &&
      (TX_PROGDIV_CFG_REG != 33.0) &&
      (TX_PROGDIV_CFG_REG != 40.0) &&
      (TX_PROGDIV_CFG_REG != 64.0) &&
      (TX_PROGDIV_CFG_REG != 66.0) &&
      (TX_PROGDIV_CFG_REG != 80.0) &&
      (TX_PROGDIV_CFG_REG != 100.0) &&
      (TX_PROGDIV_CFG_REG != 128.0) &&
      (TX_PROGDIV_CFG_REG != 132.0))) begin
    $display("Error: [Unisim %s-722] TX_PROGDIV_CFG attribute is set to %f.  Legal values for this attribute are 0.0, 4.0, 5.0, 8.0, 10.0, 16.0, 16.5, 20.0, 32.0, 33.0, 40.0, 64.0, 66.0, 80.0, 100.0, 128.0 or 132.0. Instance: %m", MODULE_NAME, TX_PROGDIV_CFG_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((TX_RXDETECT_REF_REG != 3) &&
       (TX_RXDETECT_REF_REG != 0) &&
       (TX_RXDETECT_REF_REG != 1) &&
       (TX_RXDETECT_REF_REG != 2) &&
       (TX_RXDETECT_REF_REG != 4) &&
       (TX_RXDETECT_REF_REG != 5) &&
       (TX_RXDETECT_REF_REG != 6) &&
       (TX_RXDETECT_REF_REG != 7))) begin
    $display("Error: [Unisim %s-725] TX_RXDETECT_REF attribute is set to %d.  Legal values for this attribute are 3, 0, 1, 2, 4, 5, 6 or 7. Instance: %m", MODULE_NAME, TX_RXDETECT_REF_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((TX_XCLK_SEL_REG != "TXOUT") &&
       (TX_XCLK_SEL_REG != "TXUSR"))) begin
    $display("Error: [Unisim %s-739] TX_XCLK_SEL attribute is set to %s.  Legal values for this attribute are TXOUT or TXUSR. Instance: %m", MODULE_NAME, TX_XCLK_SEL_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((USB_PING_SATA_MAX_INIT_REG < 1) || (USB_PING_SATA_MAX_INIT_REG > 63))) begin
    $display("Error: [Unisim %s-757] USB_PING_SATA_MAX_INIT attribute is set to %d.  Legal values for this attribute are 1 to 63. Instance: %m", MODULE_NAME, USB_PING_SATA_MAX_INIT_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((USB_PING_SATA_MIN_INIT_REG < 1) || (USB_PING_SATA_MIN_INIT_REG > 63))) begin
    $display("Error: [Unisim %s-758] USB_PING_SATA_MIN_INIT attribute is set to %d.  Legal values for this attribute are 1 to 63. Instance: %m", MODULE_NAME, USB_PING_SATA_MIN_INIT_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((USB_POLL_SATA_MAX_BURST_REG < 1) || (USB_POLL_SATA_MAX_BURST_REG > 63))) begin
    $display("Error: [Unisim %s-759] USB_POLL_SATA_MAX_BURST attribute is set to %d.  Legal values for this attribute are 1 to 63. Instance: %m", MODULE_NAME, USB_POLL_SATA_MAX_BURST_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((USB_POLL_SATA_MIN_BURST_REG < 1) || (USB_POLL_SATA_MIN_BURST_REG > 61))) begin
    $display("Error: [Unisim %s-760] USB_POLL_SATA_MIN_BURST attribute is set to %d.  Legal values for this attribute are 1 to 61. Instance: %m", MODULE_NAME, USB_POLL_SATA_MIN_BURST_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((USB_U1_SATA_MAX_WAKE_REG < 1) || (USB_U1_SATA_MAX_WAKE_REG > 63))) begin
    $display("Error: [Unisim %s-764] USB_U1_SATA_MAX_WAKE attribute is set to %d.  Legal values for this attribute are 1 to 63. Instance: %m", MODULE_NAME, USB_U1_SATA_MAX_WAKE_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((USB_U1_SATA_MIN_WAKE_REG < 1) || (USB_U1_SATA_MIN_WAKE_REG > 63))) begin
    $display("Error: [Unisim %s-765] USB_U1_SATA_MIN_WAKE attribute is set to %d.  Legal values for this attribute are 1 to 63. Instance: %m", MODULE_NAME, USB_U1_SATA_MIN_WAKE_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((USB_U2_SAS_MAX_COM_REG < 1) || (USB_U2_SAS_MAX_COM_REG > 127))) begin
    $display("Error: [Unisim %s-766] USB_U2_SAS_MAX_COM attribute is set to %d.  Legal values for this attribute are 1 to 127. Instance: %m", MODULE_NAME, USB_U2_SAS_MAX_COM_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((USB_U2_SAS_MIN_COM_REG < 1) || (USB_U2_SAS_MIN_COM_REG > 63))) begin
    $display("Error: [Unisim %s-767] USB_U2_SAS_MIN_COM attribute is set to %d.  Legal values for this attribute are 1 to 63. Instance: %m", MODULE_NAME, USB_U2_SAS_MIN_COM_REG);
    attr_err = 1'b1;
  end
  
  if (attr_err == 1'b1) #1 $finish;
end
`endif


assign PMASCANCLK0_in = 1'b1; // tie off
assign PMASCANCLK1_in = 1'b1; // tie off
assign PMASCANCLK2_in = 1'b1; // tie off
assign PMASCANCLK3_in = 1'b1; // tie off
assign PMASCANCLK4_in = 1'b1; // tie off
assign PMASCANCLK5_in = 1'b1; // tie off
assign PMASCANCLK6_in = 1'b1; // tie off
assign PMASCANCLK7_in = 1'b1; // tie off
assign PMASCANCLK8_in = 1'b1; // tie off
assign SCANCLK_in = 1'b1; // tie off
assign TSTCLK0_in = 1'b1; // tie off
assign TSTCLK1_in = 1'b1; // tie off

assign BSR_SERIAL_in = 1'b1; // tie off
assign CSSDRSTB_in = 1'b1; // tie off
assign CSSDSTOPCLK_in = 1'b1; // tie off
assign PMASCANENB_in = 1'b1; // tie off
assign PMASCANIN_in = 18'b111111111111111111; // tie off
assign PMASCANMODEB_in = 1'b1; // tie off
assign PMASCANRSTEN_in = 1'b1; // tie off
assign SARCCLK_in = 1'b1; // tie off
assign SCANENB_in = 1'b1; // tie off
assign SCANIN_in = 19'b1111111111111111111; // tie off
assign SCANMODEB_in = 1'b1; // tie off
assign SCANRSTB_in = 1'b1; // tie off
assign SCANRSTEN_in = 1'b1; // tie off
assign TSTPDOVRDB_in = 1'b1; // tie off
assign TSTPD_in = 5'b11111; // tie off

SIP_GTYE4_CHANNEL SIP_GTYE4_CHANNEL_INST (
.ACJTAG_DEBUG_MODE (ACJTAG_DEBUG_MODE_REG),
.ACJTAG_MODE (ACJTAG_MODE_REG),
.ACJTAG_RESET (ACJTAG_RESET_REG),
.ADAPT_CFG0 (ADAPT_CFG0_REG),
.ADAPT_CFG1 (ADAPT_CFG1_REG),
.ADAPT_CFG2 (ADAPT_CFG2_REG),
.AEN_CDRSTEPSEL (AEN_CDRSTEPSEL_REG),
.AEN_CPLL (AEN_CPLL_REG),
.AEN_LOOPBACK (AEN_LOOPBACK_REG),
.AEN_MASTER (AEN_MASTER_REG),
.AEN_PD_AND_EIDLE (AEN_PD_AND_EIDLE_REG),
.AEN_POLARITY (AEN_POLARITY_REG),
.AEN_PRBS (AEN_PRBS_REG),
.AEN_RESET (AEN_RESET_REG),
.AEN_RXCDR (AEN_RXCDR_REG),
.AEN_RXDFE (AEN_RXDFE_REG),
.AEN_RXDFELPM (AEN_RXDFELPM_REG),
.AEN_RXOUTCLK_SEL (AEN_RXOUTCLK_SEL_REG),
.AEN_RXPHDLY (AEN_RXPHDLY_REG),
.AEN_RXPLLCLK_SEL (AEN_RXPLLCLK_SEL_REG),
.AEN_RXSYSCLK_SEL (AEN_RXSYSCLK_SEL_REG),
.AEN_TXMUXDCD (AEN_TXMUXDCD_REG),
.AEN_TXOUTCLK_SEL (AEN_TXOUTCLK_SEL_REG),
.AEN_TXPHDLY (AEN_TXPHDLY_REG),
.AEN_TXPI_PPM (AEN_TXPI_PPM_REG),
.AEN_TXPLLCLK_SEL (AEN_TXPLLCLK_SEL_REG),
.AEN_TXSYSCLK_SEL (AEN_TXSYSCLK_SEL_REG),
.AEN_TX_DRIVE_MODE (AEN_TX_DRIVE_MODE_REG),
.ALIGN_COMMA_DOUBLE (ALIGN_COMMA_DOUBLE_REG),
.ALIGN_COMMA_ENABLE (ALIGN_COMMA_ENABLE_REG),
.ALIGN_COMMA_WORD (ALIGN_COMMA_WORD_REG),
.ALIGN_MCOMMA_DET (ALIGN_MCOMMA_DET_REG),
.ALIGN_MCOMMA_VALUE (ALIGN_MCOMMA_VALUE_REG),
.ALIGN_PCOMMA_DET (ALIGN_PCOMMA_DET_REG),
.ALIGN_PCOMMA_VALUE (ALIGN_PCOMMA_VALUE_REG),
.AMONITOR_CFG (AMONITOR_CFG_REG),
.A_CPLLLOCKEN (A_CPLLLOCKEN_REG),
.A_CPLLPD (A_CPLLPD_REG),
.A_CPLLRESET (A_CPLLRESET_REG),
.A_EYESCANRESET (A_EYESCANRESET_REG),
.A_GTRESETSEL (A_GTRESETSEL_REG),
.A_GTRXRESET (A_GTRXRESET_REG),
.A_GTTXRESET (A_GTTXRESET_REG),
.A_LOOPBACK (A_LOOPBACK_REG),
.A_RXAFECFOKEN (A_RXAFECFOKEN_REG),
.A_RXBUFRESET (A_RXBUFRESET_REG),
.A_RXCDRFREQRESET (A_RXCDRFREQRESET_REG),
.A_RXCDRHOLD (A_RXCDRHOLD_REG),
.A_RXCDROVRDEN (A_RXCDROVRDEN_REG),
.A_RXCDRRESET (A_RXCDRRESET_REG),
.A_RXCKCALRESET (A_RXCKCALRESET_REG),
.A_RXDFEAGCHOLD (A_RXDFEAGCHOLD_REG),
.A_RXDFEAGCOVRDEN (A_RXDFEAGCOVRDEN_REG),
.A_RXDFECFOKFCNUM (A_RXDFECFOKFCNUM_REG),
.A_RXDFECFOKFEN (A_RXDFECFOKFEN_REG),
.A_RXDFECFOKFPULSE (A_RXDFECFOKFPULSE_REG),
.A_RXDFECFOKHOLD (A_RXDFECFOKHOLD_REG),
.A_RXDFECFOKOVREN (A_RXDFECFOKOVREN_REG),
.A_RXDFEKHHOLD (A_RXDFEKHHOLD_REG),
.A_RXDFEKHOVRDEN (A_RXDFEKHOVRDEN_REG),
.A_RXDFELFHOLD (A_RXDFELFHOLD_REG),
.A_RXDFELFOVRDEN (A_RXDFELFOVRDEN_REG),
.A_RXDFELPMRESET (A_RXDFELPMRESET_REG),
.A_RXDFETAP10HOLD (A_RXDFETAP10HOLD_REG),
.A_RXDFETAP10OVRDEN (A_RXDFETAP10OVRDEN_REG),
.A_RXDFETAP11HOLD (A_RXDFETAP11HOLD_REG),
.A_RXDFETAP11OVRDEN (A_RXDFETAP11OVRDEN_REG),
.A_RXDFETAP12HOLD (A_RXDFETAP12HOLD_REG),
.A_RXDFETAP12OVRDEN (A_RXDFETAP12OVRDEN_REG),
.A_RXDFETAP13HOLD (A_RXDFETAP13HOLD_REG),
.A_RXDFETAP13OVRDEN (A_RXDFETAP13OVRDEN_REG),
.A_RXDFETAP14HOLD (A_RXDFETAP14HOLD_REG),
.A_RXDFETAP14OVRDEN (A_RXDFETAP14OVRDEN_REG),
.A_RXDFETAP15HOLD (A_RXDFETAP15HOLD_REG),
.A_RXDFETAP15OVRDEN (A_RXDFETAP15OVRDEN_REG),
.A_RXDFETAP2HOLD (A_RXDFETAP2HOLD_REG),
.A_RXDFETAP2OVRDEN (A_RXDFETAP2OVRDEN_REG),
.A_RXDFETAP3HOLD (A_RXDFETAP3HOLD_REG),
.A_RXDFETAP3OVRDEN (A_RXDFETAP3OVRDEN_REG),
.A_RXDFETAP4HOLD (A_RXDFETAP4HOLD_REG),
.A_RXDFETAP4OVRDEN (A_RXDFETAP4OVRDEN_REG),
.A_RXDFETAP5HOLD (A_RXDFETAP5HOLD_REG),
.A_RXDFETAP5OVRDEN (A_RXDFETAP5OVRDEN_REG),
.A_RXDFETAP6HOLD (A_RXDFETAP6HOLD_REG),
.A_RXDFETAP6OVRDEN (A_RXDFETAP6OVRDEN_REG),
.A_RXDFETAP7HOLD (A_RXDFETAP7HOLD_REG),
.A_RXDFETAP7OVRDEN (A_RXDFETAP7OVRDEN_REG),
.A_RXDFETAP8HOLD (A_RXDFETAP8HOLD_REG),
.A_RXDFETAP8OVRDEN (A_RXDFETAP8OVRDEN_REG),
.A_RXDFETAP9HOLD (A_RXDFETAP9HOLD_REG),
.A_RXDFETAP9OVRDEN (A_RXDFETAP9OVRDEN_REG),
.A_RXDFEUTHOLD (A_RXDFEUTHOLD_REG),
.A_RXDFEUTOVRDEN (A_RXDFEUTOVRDEN_REG),
.A_RXDFEVPHOLD (A_RXDFEVPHOLD_REG),
.A_RXDFEVPOVRDEN (A_RXDFEVPOVRDEN_REG),
.A_RXDFEXYDEN (A_RXDFEXYDEN_REG),
.A_RXDLYBYPASS (A_RXDLYBYPASS_REG),
.A_RXDLYEN (A_RXDLYEN_REG),
.A_RXDLYOVRDEN (A_RXDLYOVRDEN_REG),
.A_RXDLYSRESET (A_RXDLYSRESET_REG),
.A_RXLPMEN (A_RXLPMEN_REG),
.A_RXLPMGCHOLD (A_RXLPMGCHOLD_REG),
.A_RXLPMGCOVRDEN (A_RXLPMGCOVRDEN_REG),
.A_RXLPMHFHOLD (A_RXLPMHFHOLD_REG),
.A_RXLPMHFOVRDEN (A_RXLPMHFOVRDEN_REG),
.A_RXLPMLFHOLD (A_RXLPMLFHOLD_REG),
.A_RXLPMLFKLOVRDEN (A_RXLPMLFKLOVRDEN_REG),
.A_RXLPMOSHOLD (A_RXLPMOSHOLD_REG),
.A_RXLPMOSOVRDEN (A_RXLPMOSOVRDEN_REG),
.A_RXMONITORSEL (A_RXMONITORSEL_REG),
.A_RXOOBRESET (A_RXOOBRESET_REG),
.A_RXOSCALRESET (A_RXOSCALRESET_REG),
.A_RXOSHOLD (A_RXOSHOLD_REG),
.A_RXOSOVRDEN (A_RXOSOVRDEN_REG),
.A_RXOUTCLKSEL (A_RXOUTCLKSEL_REG),
.A_RXPCSRESET (A_RXPCSRESET_REG),
.A_RXPD (A_RXPD_REG),
.A_RXPHALIGN (A_RXPHALIGN_REG),
.A_RXPHALIGNEN (A_RXPHALIGNEN_REG),
.A_RXPHDLYPD (A_RXPHDLYPD_REG),
.A_RXPHDLYRESET (A_RXPHDLYRESET_REG),
.A_RXPLLCLKSEL (A_RXPLLCLKSEL_REG),
.A_RXPMARESET (A_RXPMARESET_REG),
.A_RXPOLARITY (A_RXPOLARITY_REG),
.A_RXPRBSCNTRESET (A_RXPRBSCNTRESET_REG),
.A_RXPRBSSEL (A_RXPRBSSEL_REG),
.A_RXPROGDIVRESET (A_RXPROGDIVRESET_REG),
.A_RXSYSCLKSEL (A_RXSYSCLKSEL_REG),
.A_RXTERMINATION (A_RXTERMINATION_REG),
.A_TXBUFDIFFCTRL (A_TXBUFDIFFCTRL_REG),
.A_TXDCCRESET (A_TXDCCRESET_REG),
.A_TXDEEMPH (A_TXDEEMPH_REG),
.A_TXDIFFCTRL (A_TXDIFFCTRL_REG),
.A_TXDLYBYPASS (A_TXDLYBYPASS_REG),
.A_TXDLYEN (A_TXDLYEN_REG),
.A_TXDLYOVRDEN (A_TXDLYOVRDEN_REG),
.A_TXDLYSRESET (A_TXDLYSRESET_REG),
.A_TXELECIDLE (A_TXELECIDLE_REG),
.A_TXINHIBIT (A_TXINHIBIT_REG),
.A_TXMAINCURSOR (A_TXMAINCURSOR_REG),
.A_TXMARGIN (A_TXMARGIN_REG),
.A_TXMUXDCDEXHOLD (A_TXMUXDCDEXHOLD_REG),
.A_TXMUXDCDORWREN (A_TXMUXDCDORWREN_REG),
.A_TXOUTCLKSEL (A_TXOUTCLKSEL_REG),
.A_TXPCSRESET (A_TXPCSRESET_REG),
.A_TXPD (A_TXPD_REG),
.A_TXPHALIGN (A_TXPHALIGN_REG),
.A_TXPHALIGNEN (A_TXPHALIGNEN_REG),
.A_TXPHDLYPD (A_TXPHDLYPD_REG),
.A_TXPHDLYRESET (A_TXPHDLYRESET_REG),
.A_TXPHINIT (A_TXPHINIT_REG),
.A_TXPHOVRDEN (A_TXPHOVRDEN_REG),
.A_TXPIPPMOVRDEN (A_TXPIPPMOVRDEN_REG),
.A_TXPIPPMPD (A_TXPIPPMPD_REG),
.A_TXPIPPMSEL (A_TXPIPPMSEL_REG),
.A_TXPLLCLKSEL (A_TXPLLCLKSEL_REG),
.A_TXPMARESET (A_TXPMARESET_REG),
.A_TXPOLARITY (A_TXPOLARITY_REG),
.A_TXPOSTCURSOR (A_TXPOSTCURSOR_REG),
.A_TXPRBSFORCEERR (A_TXPRBSFORCEERR_REG),
.A_TXPRBSSEL (A_TXPRBSSEL_REG),
.A_TXPRECURSOR (A_TXPRECURSOR_REG),
.A_TXPROGDIVRESET (A_TXPROGDIVRESET_REG),
.A_TXRESETSEL (A_TXRESETSEL_REG),
.A_TXSWING (A_TXSWING_REG),
.A_TXSYSCLKSEL (A_TXSYSCLKSEL_REG),
.BSR_ENABLE (BSR_ENABLE_REG),
.CBCC_DATA_SOURCE_SEL (CBCC_DATA_SOURCE_SEL_REG),
.CDR_SWAP_MODE_EN (CDR_SWAP_MODE_EN_REG),
.CFOK_PWRSVE_EN (CFOK_PWRSVE_EN_REG),
.CHAN_BOND_KEEP_ALIGN (CHAN_BOND_KEEP_ALIGN_REG),
.CHAN_BOND_MAX_SKEW (CHAN_BOND_MAX_SKEW_REG),
.CHAN_BOND_SEQ_1_1 (CHAN_BOND_SEQ_1_1_REG),
.CHAN_BOND_SEQ_1_2 (CHAN_BOND_SEQ_1_2_REG),
.CHAN_BOND_SEQ_1_3 (CHAN_BOND_SEQ_1_3_REG),
.CHAN_BOND_SEQ_1_4 (CHAN_BOND_SEQ_1_4_REG),
.CHAN_BOND_SEQ_1_ENABLE (CHAN_BOND_SEQ_1_ENABLE_REG),
.CHAN_BOND_SEQ_2_1 (CHAN_BOND_SEQ_2_1_REG),
.CHAN_BOND_SEQ_2_2 (CHAN_BOND_SEQ_2_2_REG),
.CHAN_BOND_SEQ_2_3 (CHAN_BOND_SEQ_2_3_REG),
.CHAN_BOND_SEQ_2_4 (CHAN_BOND_SEQ_2_4_REG),
.CHAN_BOND_SEQ_2_ENABLE (CHAN_BOND_SEQ_2_ENABLE_REG),
.CHAN_BOND_SEQ_2_USE (CHAN_BOND_SEQ_2_USE_REG),
.CHAN_BOND_SEQ_LEN (CHAN_BOND_SEQ_LEN_REG),
.CH_HSPMUX (CH_HSPMUX_REG),
.CKCAL1_CFG_0 (CKCAL1_CFG_0_REG),
.CKCAL1_CFG_1 (CKCAL1_CFG_1_REG),
.CKCAL1_CFG_2 (CKCAL1_CFG_2_REG),
.CKCAL1_CFG_3 (CKCAL1_CFG_3_REG),
.CKCAL2_CFG_0 (CKCAL2_CFG_0_REG),
.CKCAL2_CFG_1 (CKCAL2_CFG_1_REG),
.CKCAL2_CFG_2 (CKCAL2_CFG_2_REG),
.CKCAL2_CFG_3 (CKCAL2_CFG_3_REG),
.CKCAL2_CFG_4 (CKCAL2_CFG_4_REG),
.CLK_CORRECT_USE (CLK_CORRECT_USE_REG),
.CLK_COR_KEEP_IDLE (CLK_COR_KEEP_IDLE_REG),
.CLK_COR_MAX_LAT (CLK_COR_MAX_LAT_REG),
.CLK_COR_MIN_LAT (CLK_COR_MIN_LAT_REG),
.CLK_COR_PRECEDENCE (CLK_COR_PRECEDENCE_REG),
.CLK_COR_REPEAT_WAIT (CLK_COR_REPEAT_WAIT_REG),
.CLK_COR_SEQ_1_1 (CLK_COR_SEQ_1_1_REG),
.CLK_COR_SEQ_1_2 (CLK_COR_SEQ_1_2_REG),
.CLK_COR_SEQ_1_3 (CLK_COR_SEQ_1_3_REG),
.CLK_COR_SEQ_1_4 (CLK_COR_SEQ_1_4_REG),
.CLK_COR_SEQ_1_ENABLE (CLK_COR_SEQ_1_ENABLE_REG),
.CLK_COR_SEQ_2_1 (CLK_COR_SEQ_2_1_REG),
.CLK_COR_SEQ_2_2 (CLK_COR_SEQ_2_2_REG),
.CLK_COR_SEQ_2_3 (CLK_COR_SEQ_2_3_REG),
.CLK_COR_SEQ_2_4 (CLK_COR_SEQ_2_4_REG),
.CLK_COR_SEQ_2_ENABLE (CLK_COR_SEQ_2_ENABLE_REG),
.CLK_COR_SEQ_2_USE (CLK_COR_SEQ_2_USE_REG),
.CLK_COR_SEQ_LEN (CLK_COR_SEQ_LEN_REG),
.CPLL_CFG0 (CPLL_CFG0_REG),
.CPLL_CFG1 (CPLL_CFG1_REG),
.CPLL_CFG2 (CPLL_CFG2_REG),
.CPLL_CFG3 (CPLL_CFG3_REG),
.CPLL_FBDIV (CPLL_FBDIV_REG),
.CPLL_FBDIV_45 (CPLL_FBDIV_45_REG),
.CPLL_INIT_CFG0 (CPLL_INIT_CFG0_REG),
.CPLL_LOCK_CFG (CPLL_LOCK_CFG_REG),
.CPLL_REFCLK_DIV (CPLL_REFCLK_DIV_REG),
.CSSD_CLK_MASK0 (CSSD_CLK_MASK0_REG),
.CSSD_CLK_MASK1 (CSSD_CLK_MASK1_REG),
.CSSD_REG0 (CSSD_REG0_REG),
.CSSD_REG1 (CSSD_REG1_REG),
.CSSD_REG10 (CSSD_REG10_REG),
.CSSD_REG2 (CSSD_REG2_REG),
.CSSD_REG3 (CSSD_REG3_REG),
.CSSD_REG4 (CSSD_REG4_REG),
.CSSD_REG5 (CSSD_REG5_REG),
.CSSD_REG6 (CSSD_REG6_REG),
.CSSD_REG7 (CSSD_REG7_REG),
.CSSD_REG8 (CSSD_REG8_REG),
.CSSD_REG9 (CSSD_REG9_REG),
.CTLE3_OCAP_EXT_CTRL (CTLE3_OCAP_EXT_CTRL_REG),
.CTLE3_OCAP_EXT_EN (CTLE3_OCAP_EXT_EN_REG),
.DDI_CTRL (DDI_CTRL_REG),
.DDI_REALIGN_WAIT (DDI_REALIGN_WAIT_REG),
.DEC_MCOMMA_DETECT (DEC_MCOMMA_DETECT_REG),
.DEC_PCOMMA_DETECT (DEC_PCOMMA_DETECT_REG),
.DEC_VALID_COMMA_ONLY (DEC_VALID_COMMA_ONLY_REG),
.DELAY_ELEC (DELAY_ELEC_REG),
.DMONITOR_CFG0 (DMONITOR_CFG0_REG),
.DMONITOR_CFG1 (DMONITOR_CFG1_REG),
.ES_CLK_PHASE_SEL (ES_CLK_PHASE_SEL_REG),
.ES_CONTROL (ES_CONTROL_REG),
.ES_ERRDET_EN (ES_ERRDET_EN_REG),
.ES_EYE_SCAN_EN (ES_EYE_SCAN_EN_REG),
.ES_HORZ_OFFSET (ES_HORZ_OFFSET_REG),
.ES_PRESCALE (ES_PRESCALE_REG),
.ES_QUALIFIER0 (ES_QUALIFIER0_REG),
.ES_QUALIFIER1 (ES_QUALIFIER1_REG),
.ES_QUALIFIER2 (ES_QUALIFIER2_REG),
.ES_QUALIFIER3 (ES_QUALIFIER3_REG),
.ES_QUALIFIER4 (ES_QUALIFIER4_REG),
.ES_QUALIFIER5 (ES_QUALIFIER5_REG),
.ES_QUALIFIER6 (ES_QUALIFIER6_REG),
.ES_QUALIFIER7 (ES_QUALIFIER7_REG),
.ES_QUALIFIER8 (ES_QUALIFIER8_REG),
.ES_QUALIFIER9 (ES_QUALIFIER9_REG),
.ES_QUAL_MASK0 (ES_QUAL_MASK0_REG),
.ES_QUAL_MASK1 (ES_QUAL_MASK1_REG),
.ES_QUAL_MASK2 (ES_QUAL_MASK2_REG),
.ES_QUAL_MASK3 (ES_QUAL_MASK3_REG),
.ES_QUAL_MASK4 (ES_QUAL_MASK4_REG),
.ES_QUAL_MASK5 (ES_QUAL_MASK5_REG),
.ES_QUAL_MASK6 (ES_QUAL_MASK6_REG),
.ES_QUAL_MASK7 (ES_QUAL_MASK7_REG),
.ES_QUAL_MASK8 (ES_QUAL_MASK8_REG),
.ES_QUAL_MASK9 (ES_QUAL_MASK9_REG),
.ES_SDATA_MASK0 (ES_SDATA_MASK0_REG),
.ES_SDATA_MASK1 (ES_SDATA_MASK1_REG),
.ES_SDATA_MASK2 (ES_SDATA_MASK2_REG),
.ES_SDATA_MASK3 (ES_SDATA_MASK3_REG),
.ES_SDATA_MASK4 (ES_SDATA_MASK4_REG),
.ES_SDATA_MASK5 (ES_SDATA_MASK5_REG),
.ES_SDATA_MASK6 (ES_SDATA_MASK6_REG),
.ES_SDATA_MASK7 (ES_SDATA_MASK7_REG),
.ES_SDATA_MASK8 (ES_SDATA_MASK8_REG),
.ES_SDATA_MASK9 (ES_SDATA_MASK9_REG),
.EYESCAN_VP_RANGE (EYESCAN_VP_RANGE_REG),
.EYE_SCAN_SWAP_EN (EYE_SCAN_SWAP_EN_REG),
.FTS_DESKEW_SEQ_ENABLE (FTS_DESKEW_SEQ_ENABLE_REG),
.FTS_LANE_DESKEW_CFG (FTS_LANE_DESKEW_CFG_REG),
.FTS_LANE_DESKEW_EN (FTS_LANE_DESKEW_EN_REG),
.GEARBOX_MODE (GEARBOX_MODE_REG),
.GEN_RXUSRCLK (GEN_RXUSRCLK_REG),
.GEN_TXUSRCLK (GEN_TXUSRCLK_REG),
.GT_INSTANTIATED (GT_INSTANTIATED_REG),
.INT_MASK_CFG0 (INT_MASK_CFG0_REG),
.INT_MASK_CFG1 (INT_MASK_CFG1_REG),
.ISCAN_CK_PH_SEL2 (ISCAN_CK_PH_SEL2_REG),
.LOCAL_MASTER (LOCAL_MASTER_REG),
.LPBK_BIAS_CTRL (LPBK_BIAS_CTRL_REG),
.LPBK_EN_RCAL_B (LPBK_EN_RCAL_B_REG),
.LPBK_EXT_RCAL (LPBK_EXT_RCAL_REG),
.LPBK_IND_CTRL0 (LPBK_IND_CTRL0_REG),
.LPBK_IND_CTRL1 (LPBK_IND_CTRL1_REG),
.LPBK_IND_CTRL2 (LPBK_IND_CTRL2_REG),
.LPBK_RG_CTRL (LPBK_RG_CTRL_REG),
.OOBDIVCTL (OOBDIVCTL_REG),
.OOB_PWRUP (OOB_PWRUP_REG),
.PCI3_AUTO_REALIGN (PCI3_AUTO_REALIGN_REG),
.PCI3_PIPE_RX_ELECIDLE (PCI3_PIPE_RX_ELECIDLE_REG),
.PCI3_RX_ASYNC_EBUF_BYPASS (PCI3_RX_ASYNC_EBUF_BYPASS_REG),
.PCI3_RX_ELECIDLE_EI2_ENABLE (PCI3_RX_ELECIDLE_EI2_ENABLE_REG),
.PCI3_RX_ELECIDLE_H2L_COUNT (PCI3_RX_ELECIDLE_H2L_COUNT_REG),
.PCI3_RX_ELECIDLE_H2L_DISABLE (PCI3_RX_ELECIDLE_H2L_DISABLE_REG),
.PCI3_RX_ELECIDLE_HI_COUNT (PCI3_RX_ELECIDLE_HI_COUNT_REG),
.PCI3_RX_ELECIDLE_LP4_DISABLE (PCI3_RX_ELECIDLE_LP4_DISABLE_REG),
.PCI3_RX_FIFO_DISABLE (PCI3_RX_FIFO_DISABLE_REG),
.PCIE3_CLK_COR_EMPTY_THRSH (PCIE3_CLK_COR_EMPTY_THRSH_REG),
.PCIE3_CLK_COR_FULL_THRSH (PCIE3_CLK_COR_FULL_THRSH_REG),
.PCIE3_CLK_COR_MAX_LAT (PCIE3_CLK_COR_MAX_LAT_REG),
.PCIE3_CLK_COR_MIN_LAT (PCIE3_CLK_COR_MIN_LAT_REG),
.PCIE3_CLK_COR_THRSH_TIMER (PCIE3_CLK_COR_THRSH_TIMER_REG),
.PCIE_64B_DYN_CLKSW_DIS (PCIE_64B_DYN_CLKSW_DIS_REG),
.PCIE_BUFG_DIV_CTRL (PCIE_BUFG_DIV_CTRL_REG),
.PCIE_GEN4_64BIT_INT_EN (PCIE_GEN4_64BIT_INT_EN_REG),
.PCIE_PLL_SEL_MODE_GEN12 (PCIE_PLL_SEL_MODE_GEN12_REG),
.PCIE_PLL_SEL_MODE_GEN3 (PCIE_PLL_SEL_MODE_GEN3_REG),
.PCIE_PLL_SEL_MODE_GEN4 (PCIE_PLL_SEL_MODE_GEN4_REG),
.PCIE_RXPCS_CFG_GEN3 (PCIE_RXPCS_CFG_GEN3_REG),
.PCIE_RXPMA_CFG (PCIE_RXPMA_CFG_REG),
.PCIE_TXPCS_CFG_GEN3 (PCIE_TXPCS_CFG_GEN3_REG),
.PCIE_TXPMA_CFG (PCIE_TXPMA_CFG_REG),
.PCS_PCIE_EN (PCS_PCIE_EN_REG),
.PCS_RSVD0 (PCS_RSVD0_REG),
.PD_TRANS_TIME_FROM_P2 (PD_TRANS_TIME_FROM_P2_REG),
.PD_TRANS_TIME_NONE_P2 (PD_TRANS_TIME_NONE_P2_REG),
.PD_TRANS_TIME_TO_P2 (PD_TRANS_TIME_TO_P2_REG),
.PREIQ_FREQ_BST (PREIQ_FREQ_BST_REG),
.RATE_SW_USE_DRP (RATE_SW_USE_DRP_REG),
.RCLK_SIPO_DLY_ENB (RCLK_SIPO_DLY_ENB_REG),
.RCLK_SIPO_INV_EN (RCLK_SIPO_INV_EN_REG),
.RTX_BUF_CML_CTRL (RTX_BUF_CML_CTRL_REG),
.RTX_BUF_TERM_CTRL (RTX_BUF_TERM_CTRL_REG),
.RXBUFRESET_TIME (RXBUFRESET_TIME_REG),
.RXBUF_ADDR_MODE (RXBUF_ADDR_MODE_REG),
.RXBUF_EIDLE_HI_CNT (RXBUF_EIDLE_HI_CNT_REG),
.RXBUF_EIDLE_LO_CNT (RXBUF_EIDLE_LO_CNT_REG),
.RXBUF_EN (RXBUF_EN_REG),
.RXBUF_RESET_ON_CB_CHANGE (RXBUF_RESET_ON_CB_CHANGE_REG),
.RXBUF_RESET_ON_COMMAALIGN (RXBUF_RESET_ON_COMMAALIGN_REG),
.RXBUF_RESET_ON_EIDLE (RXBUF_RESET_ON_EIDLE_REG),
.RXBUF_RESET_ON_RATE_CHANGE (RXBUF_RESET_ON_RATE_CHANGE_REG),
.RXBUF_THRESH_OVFLW (RXBUF_THRESH_OVFLW_REG),
.RXBUF_THRESH_OVRD (RXBUF_THRESH_OVRD_REG),
.RXBUF_THRESH_UNDFLW (RXBUF_THRESH_UNDFLW_REG),
.RXCDRFREQRESET_TIME (RXCDRFREQRESET_TIME_REG),
.RXCDRPHRESET_TIME (RXCDRPHRESET_TIME_REG),
.RXCDR_CFG0 (RXCDR_CFG0_REG),
.RXCDR_CFG0_GEN3 (RXCDR_CFG0_GEN3_REG),
.RXCDR_CFG1 (RXCDR_CFG1_REG),
.RXCDR_CFG1_GEN3 (RXCDR_CFG1_GEN3_REG),
.RXCDR_CFG2 (RXCDR_CFG2_REG),
.RXCDR_CFG2_GEN2 (RXCDR_CFG2_GEN2_REG),
.RXCDR_CFG2_GEN3 (RXCDR_CFG2_GEN3_REG),
.RXCDR_CFG2_GEN4 (RXCDR_CFG2_GEN4_REG),
.RXCDR_CFG3 (RXCDR_CFG3_REG),
.RXCDR_CFG3_GEN2 (RXCDR_CFG3_GEN2_REG),
.RXCDR_CFG3_GEN3 (RXCDR_CFG3_GEN3_REG),
.RXCDR_CFG3_GEN4 (RXCDR_CFG3_GEN4_REG),
.RXCDR_CFG4 (RXCDR_CFG4_REG),
.RXCDR_CFG4_GEN3 (RXCDR_CFG4_GEN3_REG),
.RXCDR_CFG5 (RXCDR_CFG5_REG),
.RXCDR_CFG5_GEN3 (RXCDR_CFG5_GEN3_REG),
.RXCDR_FR_RESET_ON_EIDLE (RXCDR_FR_RESET_ON_EIDLE_REG),
.RXCDR_HOLD_DURING_EIDLE (RXCDR_HOLD_DURING_EIDLE_REG),
.RXCDR_LOCK_CFG0 (RXCDR_LOCK_CFG0_REG),
.RXCDR_LOCK_CFG1 (RXCDR_LOCK_CFG1_REG),
.RXCDR_LOCK_CFG2 (RXCDR_LOCK_CFG2_REG),
.RXCDR_LOCK_CFG3 (RXCDR_LOCK_CFG3_REG),
.RXCDR_LOCK_CFG4 (RXCDR_LOCK_CFG4_REG),
.RXCDR_PH_RESET_ON_EIDLE (RXCDR_PH_RESET_ON_EIDLE_REG),
.RXCFOK_CFG0 (RXCFOK_CFG0_REG),
.RXCFOK_CFG1 (RXCFOK_CFG1_REG),
.RXCFOK_CFG2 (RXCFOK_CFG2_REG),
.RXCKCAL1_IQ_LOOP_RST_CFG (RXCKCAL1_IQ_LOOP_RST_CFG_REG),
.RXCKCAL1_I_LOOP_RST_CFG (RXCKCAL1_I_LOOP_RST_CFG_REG),
.RXCKCAL1_Q_LOOP_RST_CFG (RXCKCAL1_Q_LOOP_RST_CFG_REG),
.RXCKCAL2_DX_LOOP_RST_CFG (RXCKCAL2_DX_LOOP_RST_CFG_REG),
.RXCKCAL2_D_LOOP_RST_CFG (RXCKCAL2_D_LOOP_RST_CFG_REG),
.RXCKCAL2_S_LOOP_RST_CFG (RXCKCAL2_S_LOOP_RST_CFG_REG),
.RXCKCAL2_X_LOOP_RST_CFG (RXCKCAL2_X_LOOP_RST_CFG_REG),
.RXDFELPMRESET_TIME (RXDFELPMRESET_TIME_REG),
.RXDFELPM_KL_CFG0 (RXDFELPM_KL_CFG0_REG),
.RXDFELPM_KL_CFG1 (RXDFELPM_KL_CFG1_REG),
.RXDFELPM_KL_CFG2 (RXDFELPM_KL_CFG2_REG),
.RXDFE_CFG0 (RXDFE_CFG0_REG),
.RXDFE_CFG1 (RXDFE_CFG1_REG),
.RXDFE_GC_CFG0 (RXDFE_GC_CFG0_REG),
.RXDFE_GC_CFG1 (RXDFE_GC_CFG1_REG),
.RXDFE_GC_CFG2 (RXDFE_GC_CFG2_REG),
.RXDFE_H2_CFG0 (RXDFE_H2_CFG0_REG),
.RXDFE_H2_CFG1 (RXDFE_H2_CFG1_REG),
.RXDFE_H3_CFG0 (RXDFE_H3_CFG0_REG),
.RXDFE_H3_CFG1 (RXDFE_H3_CFG1_REG),
.RXDFE_H4_CFG0 (RXDFE_H4_CFG0_REG),
.RXDFE_H4_CFG1 (RXDFE_H4_CFG1_REG),
.RXDFE_H5_CFG0 (RXDFE_H5_CFG0_REG),
.RXDFE_H5_CFG1 (RXDFE_H5_CFG1_REG),
.RXDFE_H6_CFG0 (RXDFE_H6_CFG0_REG),
.RXDFE_H6_CFG1 (RXDFE_H6_CFG1_REG),
.RXDFE_H7_CFG0 (RXDFE_H7_CFG0_REG),
.RXDFE_H7_CFG1 (RXDFE_H7_CFG1_REG),
.RXDFE_H8_CFG0 (RXDFE_H8_CFG0_REG),
.RXDFE_H8_CFG1 (RXDFE_H8_CFG1_REG),
.RXDFE_H9_CFG0 (RXDFE_H9_CFG0_REG),
.RXDFE_H9_CFG1 (RXDFE_H9_CFG1_REG),
.RXDFE_HA_CFG0 (RXDFE_HA_CFG0_REG),
.RXDFE_HA_CFG1 (RXDFE_HA_CFG1_REG),
.RXDFE_HB_CFG0 (RXDFE_HB_CFG0_REG),
.RXDFE_HB_CFG1 (RXDFE_HB_CFG1_REG),
.RXDFE_HC_CFG0 (RXDFE_HC_CFG0_REG),
.RXDFE_HC_CFG1 (RXDFE_HC_CFG1_REG),
.RXDFE_HD_CFG0 (RXDFE_HD_CFG0_REG),
.RXDFE_HD_CFG1 (RXDFE_HD_CFG1_REG),
.RXDFE_HE_CFG0 (RXDFE_HE_CFG0_REG),
.RXDFE_HE_CFG1 (RXDFE_HE_CFG1_REG),
.RXDFE_HF_CFG0 (RXDFE_HF_CFG0_REG),
.RXDFE_HF_CFG1 (RXDFE_HF_CFG1_REG),
.RXDFE_KH_CFG0 (RXDFE_KH_CFG0_REG),
.RXDFE_KH_CFG1 (RXDFE_KH_CFG1_REG),
.RXDFE_KH_CFG2 (RXDFE_KH_CFG2_REG),
.RXDFE_KH_CFG3 (RXDFE_KH_CFG3_REG),
.RXDFE_OS_CFG0 (RXDFE_OS_CFG0_REG),
.RXDFE_OS_CFG1 (RXDFE_OS_CFG1_REG),
.RXDFE_UT_CFG0 (RXDFE_UT_CFG0_REG),
.RXDFE_UT_CFG1 (RXDFE_UT_CFG1_REG),
.RXDFE_UT_CFG2 (RXDFE_UT_CFG2_REG),
.RXDFE_VP_CFG0 (RXDFE_VP_CFG0_REG),
.RXDFE_VP_CFG1 (RXDFE_VP_CFG1_REG),
.RXDLY_CFG (RXDLY_CFG_REG),
.RXDLY_LCFG (RXDLY_LCFG_REG),
.RXELECIDLE_CFG (RXELECIDLE_CFG_REG),
.RXGBOX_FIFO_INIT_RD_ADDR (RXGBOX_FIFO_INIT_RD_ADDR_REG),
.RXGEARBOX_EN (RXGEARBOX_EN_REG),
.RXISCANRESET_TIME (RXISCANRESET_TIME_REG),
.RXLPM_CFG (RXLPM_CFG_REG),
.RXLPM_GC_CFG (RXLPM_GC_CFG_REG),
.RXLPM_KH_CFG0 (RXLPM_KH_CFG0_REG),
.RXLPM_KH_CFG1 (RXLPM_KH_CFG1_REG),
.RXLPM_OS_CFG0 (RXLPM_OS_CFG0_REG),
.RXLPM_OS_CFG1 (RXLPM_OS_CFG1_REG),
.RXOOB_CFG (RXOOB_CFG_REG),
.RXOOB_CLK_CFG (RXOOB_CLK_CFG_REG),
.RXOSCALRESET_TIME (RXOSCALRESET_TIME_REG),
.RXOUT_DIV (RXOUT_DIV_REG),
.RXPCSRESET_TIME (RXPCSRESET_TIME_REG),
.RXPHBEACON_CFG (RXPHBEACON_CFG_REG),
.RXPHDLY_CFG (RXPHDLY_CFG_REG),
.RXPHSAMP_CFG (RXPHSAMP_CFG_REG),
.RXPHSLIP_CFG (RXPHSLIP_CFG_REG),
.RXPH_MONITOR_SEL (RXPH_MONITOR_SEL_REG),
.RXPI_CFG0 (RXPI_CFG0_REG),
.RXPI_CFG1 (RXPI_CFG1_REG),
.RXPMACLK_SEL (RXPMACLK_SEL_REG),
.RXPMARESET_TIME (RXPMARESET_TIME_REG),
.RXPRBS_ERR_LOOPBACK (RXPRBS_ERR_LOOPBACK_REG),
.RXPRBS_LINKACQ_CNT (RXPRBS_LINKACQ_CNT_REG),
.RXREFCLKDIV2_SEL (RXREFCLKDIV2_SEL_REG),
.RXSLIDE_AUTO_WAIT (RXSLIDE_AUTO_WAIT_REG),
.RXSLIDE_MODE (RXSLIDE_MODE_REG),
.RXSYNC_MULTILANE (RXSYNC_MULTILANE_REG),
.RXSYNC_OVRD (RXSYNC_OVRD_REG),
.RXSYNC_SKIP_DA (RXSYNC_SKIP_DA_REG),
.RX_AFE_CM_EN (RX_AFE_CM_EN_REG),
.RX_BIAS_CFG0 (RX_BIAS_CFG0_REG),
.RX_BUFFER_CFG (RX_BUFFER_CFG_REG),
.RX_CAPFF_SARC_ENB (RX_CAPFF_SARC_ENB_REG),
.RX_CLK25_DIV (RX_CLK25_DIV_REG),
.RX_CLKMUX_EN (RX_CLKMUX_EN_REG),
.RX_CLK_SLIP_OVRD (RX_CLK_SLIP_OVRD_REG),
.RX_CM_BUF_CFG (RX_CM_BUF_CFG_REG),
.RX_CM_BUF_PD (RX_CM_BUF_PD_REG),
.RX_CM_SEL (RX_CM_SEL_REG),
.RX_CM_TRIM (RX_CM_TRIM_REG),
.RX_CTLE_PWR_SAVING (RX_CTLE_PWR_SAVING_REG),
.RX_CTLE_RES_CTRL (RX_CTLE_RES_CTRL_REG),
.RX_DATA_WIDTH (RX_DATA_WIDTH_REG),
.RX_DDI_SEL (RX_DDI_SEL_REG),
.RX_DEFER_RESET_BUF_EN (RX_DEFER_RESET_BUF_EN_REG),
.RX_DEGEN_CTRL (RX_DEGEN_CTRL_REG),
.RX_DFECFOKFCDAC (RX_DFECFOKFCDAC_REG),
.RX_DFELPM_CFG0 (RX_DFELPM_CFG0_REG),
.RX_DFELPM_CFG1 (RX_DFELPM_CFG1_REG),
.RX_DFELPM_KLKH_AGC_STUP_EN (RX_DFELPM_KLKH_AGC_STUP_EN_REG),
.RX_DFE_AGC_CFG1 (RX_DFE_AGC_CFG1_REG),
.RX_DFE_KL_LPM_KH_CFG0 (RX_DFE_KL_LPM_KH_CFG0_REG),
.RX_DFE_KL_LPM_KH_CFG1 (RX_DFE_KL_LPM_KH_CFG1_REG),
.RX_DFE_KL_LPM_KL_CFG0 (RX_DFE_KL_LPM_KL_CFG0_REG),
.RX_DFE_KL_LPM_KL_CFG1 (RX_DFE_KL_LPM_KL_CFG1_REG),
.RX_DFE_LPM_HOLD_DURING_EIDLE (RX_DFE_LPM_HOLD_DURING_EIDLE_REG),
.RX_DISPERR_SEQ_MATCH (RX_DISPERR_SEQ_MATCH_REG),
.RX_DIVRESET_TIME (RX_DIVRESET_TIME_REG),
.RX_EN_CTLE_RCAL_B (RX_EN_CTLE_RCAL_B_REG),
.RX_EN_SUM_RCAL_B (RX_EN_SUM_RCAL_B_REG),
.RX_EYESCAN_VS_CODE (RX_EYESCAN_VS_CODE_REG),
.RX_EYESCAN_VS_NEG_DIR (RX_EYESCAN_VS_NEG_DIR_REG),
.RX_EYESCAN_VS_RANGE (RX_EYESCAN_VS_RANGE_REG),
.RX_EYESCAN_VS_UT_SIGN (RX_EYESCAN_VS_UT_SIGN_REG),
.RX_FABINT_USRCLK_FLOP (RX_FABINT_USRCLK_FLOP_REG),
.RX_I2V_FILTER_EN (RX_I2V_FILTER_EN_REG),
.RX_INT_DATAWIDTH (RX_INT_DATAWIDTH_REG),
.RX_PMA_POWER_SAVE (RX_PMA_POWER_SAVE_REG),
.RX_PMA_RSV0 (RX_PMA_RSV0_REG),
.RX_PROGDIV_CFG (RX_PROGDIV_CFG_BIN),
.RX_PROGDIV_RATE (RX_PROGDIV_RATE_REG),
.RX_RESLOAD_CTRL (RX_RESLOAD_CTRL_REG),
.RX_RESLOAD_OVRD (RX_RESLOAD_OVRD_REG),
.RX_SAMPLE_PERIOD (RX_SAMPLE_PERIOD_REG),
.RX_SIG_VALID_DLY (RX_SIG_VALID_DLY_REG),
.RX_SUM_DEGEN_AVTT_OVERITE (RX_SUM_DEGEN_AVTT_OVERITE_REG),
.RX_SUM_DFETAPREP_EN (RX_SUM_DFETAPREP_EN_REG),
.RX_SUM_IREF_TUNE (RX_SUM_IREF_TUNE_REG),
.RX_SUM_PWR_SAVING (RX_SUM_PWR_SAVING_REG),
.RX_SUM_RES_CTRL (RX_SUM_RES_CTRL_REG),
.RX_SUM_VCMTUNE (RX_SUM_VCMTUNE_REG),
.RX_SUM_VCM_BIAS_TUNE_EN (RX_SUM_VCM_BIAS_TUNE_EN_REG),
.RX_SUM_VCM_OVWR (RX_SUM_VCM_OVWR_REG),
.RX_SUM_VREF_TUNE (RX_SUM_VREF_TUNE_REG),
.RX_TUNE_AFE_OS (RX_TUNE_AFE_OS_REG),
.RX_VREG_CTRL (RX_VREG_CTRL_REG),
.RX_VREG_PDB (RX_VREG_PDB_REG),
.RX_VREG_VREFSEL (RX_VREG_VREFSEL_REG),
.RX_WIDEMODE_CDR (RX_WIDEMODE_CDR_REG),
.RX_WIDEMODE_CDR_GEN3 (RX_WIDEMODE_CDR_GEN3_REG),
.RX_WIDEMODE_CDR_GEN4 (RX_WIDEMODE_CDR_GEN4_REG),
.RX_XCLK_SEL (RX_XCLK_SEL_REG),
.RX_XMODE_SEL (RX_XMODE_SEL_REG),
.SAMPLE_CLK_PHASE (SAMPLE_CLK_PHASE_REG),
.SAS_12G_MODE (SAS_12G_MODE_REG),
.SATA_BURST_SEQ_LEN (SATA_BURST_SEQ_LEN_REG),
.SATA_BURST_VAL (SATA_BURST_VAL_REG),
.SATA_CPLL_CFG (SATA_CPLL_CFG_REG),
.SATA_EIDLE_VAL (SATA_EIDLE_VAL_REG),
.SHOW_REALIGN_COMMA (SHOW_REALIGN_COMMA_REG),
.SIM_DEVICE (SIM_DEVICE_REG),
.SIM_MODE (SIM_MODE_REG),
.SIM_RECEIVER_DETECT_PASS (SIM_RECEIVER_DETECT_PASS_REG),
.SIM_RESET_SPEEDUP (SIM_RESET_SPEEDUP_REG),
.SIM_TX_EIDLE_DRIVE_LEVEL (SIM_TX_EIDLE_DRIVE_LEVEL_REG),
.SRSTMODE (SRSTMODE_REG),
.TAPDLY_SET_TX (TAPDLY_SET_TX_REG),
.TERM_RCAL_CFG (TERM_RCAL_CFG_REG),
.TERM_RCAL_OVRD (TERM_RCAL_OVRD_REG),
.TRANS_TIME_RATE (TRANS_TIME_RATE_REG),
.TST_RSV0 (TST_RSV0_REG),
.TST_RSV1 (TST_RSV1_REG),
.TXBUF_EN (TXBUF_EN_REG),
.TXBUF_RESET_ON_RATE_CHANGE (TXBUF_RESET_ON_RATE_CHANGE_REG),
.TXDLY_CFG (TXDLY_CFG_REG),
.TXDLY_LCFG (TXDLY_LCFG_REG),
.TXDRV_FREQBAND (TXDRV_FREQBAND_REG),
.TXFE_CFG0 (TXFE_CFG0_REG),
.TXFE_CFG1 (TXFE_CFG1_REG),
.TXFE_CFG2 (TXFE_CFG2_REG),
.TXFE_CFG3 (TXFE_CFG3_REG),
.TXFIFO_ADDR_CFG (TXFIFO_ADDR_CFG_REG),
.TXGBOX_FIFO_INIT_RD_ADDR (TXGBOX_FIFO_INIT_RD_ADDR_REG),
.TXGEARBOX_EN (TXGEARBOX_EN_REG),
.TXOUTCLKPCS_SEL (TXOUTCLKPCS_SEL_REG),
.TXOUT_DIV (TXOUT_DIV_REG),
.TXPCSRESET_TIME (TXPCSRESET_TIME_REG),
.TXPHDLY_CFG0 (TXPHDLY_CFG0_REG),
.TXPHDLY_CFG1 (TXPHDLY_CFG1_REG),
.TXPH_CFG (TXPH_CFG_REG),
.TXPH_CFG2 (TXPH_CFG2_REG),
.TXPH_MONITOR_SEL (TXPH_MONITOR_SEL_REG),
.TXPI_CFG0 (TXPI_CFG0_REG),
.TXPI_CFG1 (TXPI_CFG1_REG),
.TXPI_GRAY_SEL (TXPI_GRAY_SEL_REG),
.TXPI_INVSTROBE_SEL (TXPI_INVSTROBE_SEL_REG),
.TXPI_PPM (TXPI_PPM_REG),
.TXPI_PPM_CFG (TXPI_PPM_CFG_REG),
.TXPI_SYNFREQ_PPM (TXPI_SYNFREQ_PPM_REG),
.TXPMARESET_TIME (TXPMARESET_TIME_REG),
.TXREFCLKDIV2_SEL (TXREFCLKDIV2_SEL_REG),
.TXSWBST_BST (TXSWBST_BST_REG),
.TXSWBST_EN (TXSWBST_EN_REG),
.TXSWBST_MAG (TXSWBST_MAG_REG),
.TXSYNC_MULTILANE (TXSYNC_MULTILANE_REG),
.TXSYNC_OVRD (TXSYNC_OVRD_REG),
.TXSYNC_SKIP_DA (TXSYNC_SKIP_DA_REG),
.TX_CLK25_DIV (TX_CLK25_DIV_REG),
.TX_CLKMUX_EN (TX_CLKMUX_EN_REG),
.TX_DATA_WIDTH (TX_DATA_WIDTH_REG),
.TX_DCC_LOOP_RST_CFG (TX_DCC_LOOP_RST_CFG_REG),
.TX_DEEMPH0 (TX_DEEMPH0_REG),
.TX_DEEMPH1 (TX_DEEMPH1_REG),
.TX_DEEMPH2 (TX_DEEMPH2_REG),
.TX_DEEMPH3 (TX_DEEMPH3_REG),
.TX_DIVRESET_TIME (TX_DIVRESET_TIME_REG),
.TX_DRIVE_MODE (TX_DRIVE_MODE_REG),
.TX_EIDLE_ASSERT_DELAY (TX_EIDLE_ASSERT_DELAY_REG),
.TX_EIDLE_DEASSERT_DELAY (TX_EIDLE_DEASSERT_DELAY_REG),
.TX_FABINT_USRCLK_FLOP (TX_FABINT_USRCLK_FLOP_REG),
.TX_FIFO_BYP_EN (TX_FIFO_BYP_EN_REG),
.TX_IDLE_DATA_ZERO (TX_IDLE_DATA_ZERO_REG),
.TX_INT_DATAWIDTH (TX_INT_DATAWIDTH_REG),
.TX_LOOPBACK_DRIVE_HIZ (TX_LOOPBACK_DRIVE_HIZ_REG),
.TX_MAINCURSOR_SEL (TX_MAINCURSOR_SEL_REG),
.TX_MARGIN_FULL_0 (TX_MARGIN_FULL_0_REG),
.TX_MARGIN_FULL_1 (TX_MARGIN_FULL_1_REG),
.TX_MARGIN_FULL_2 (TX_MARGIN_FULL_2_REG),
.TX_MARGIN_FULL_3 (TX_MARGIN_FULL_3_REG),
.TX_MARGIN_FULL_4 (TX_MARGIN_FULL_4_REG),
.TX_MARGIN_LOW_0 (TX_MARGIN_LOW_0_REG),
.TX_MARGIN_LOW_1 (TX_MARGIN_LOW_1_REG),
.TX_MARGIN_LOW_2 (TX_MARGIN_LOW_2_REG),
.TX_MARGIN_LOW_3 (TX_MARGIN_LOW_3_REG),
.TX_MARGIN_LOW_4 (TX_MARGIN_LOW_4_REG),
.TX_PHICAL_CFG0 (TX_PHICAL_CFG0_REG),
.TX_PHICAL_CFG1 (TX_PHICAL_CFG1_REG),
.TX_PI_BIASSET (TX_PI_BIASSET_REG),
.TX_PMADATA_OPT (TX_PMADATA_OPT_REG),
.TX_PMA_POWER_SAVE (TX_PMA_POWER_SAVE_REG),
.TX_PMA_RSV0 (TX_PMA_RSV0_REG),
.TX_PMA_RSV1 (TX_PMA_RSV1_REG),
.TX_PROGCLK_SEL (TX_PROGCLK_SEL_REG),
.TX_PROGDIV_CFG (TX_PROGDIV_CFG_BIN),
.TX_PROGDIV_RATE (TX_PROGDIV_RATE_REG),
.TX_RXDETECT_CFG (TX_RXDETECT_CFG_REG),
.TX_RXDETECT_REF (TX_RXDETECT_REF_REG),
.TX_SAMPLE_PERIOD (TX_SAMPLE_PERIOD_REG),
.TX_SW_MEAS (TX_SW_MEAS_REG),
.TX_USERPATTERN_DATA0 (TX_USERPATTERN_DATA0_REG),
.TX_USERPATTERN_DATA1 (TX_USERPATTERN_DATA1_REG),
.TX_USERPATTERN_DATA2 (TX_USERPATTERN_DATA2_REG),
.TX_USERPATTERN_DATA3 (TX_USERPATTERN_DATA3_REG),
.TX_USERPATTERN_DATA4 (TX_USERPATTERN_DATA4_REG),
.TX_USERPATTERN_DATA5 (TX_USERPATTERN_DATA5_REG),
.TX_USERPATTERN_DATA6 (TX_USERPATTERN_DATA6_REG),
.TX_USERPATTERN_DATA7 (TX_USERPATTERN_DATA7_REG),
.TX_VREG_CTRL (TX_VREG_CTRL_REG),
.TX_VREG_PDB (TX_VREG_PDB_REG),
.TX_VREG_VREFSEL (TX_VREG_VREFSEL_REG),
.TX_XCLK_SEL (TX_XCLK_SEL_REG),
.USB_BOTH_BURST_IDLE (USB_BOTH_BURST_IDLE_REG),
.USB_BURSTMAX_U3WAKE (USB_BURSTMAX_U3WAKE_REG),
.USB_BURSTMIN_U3WAKE (USB_BURSTMIN_U3WAKE_REG),
.USB_CLK_COR_EQ_EN (USB_CLK_COR_EQ_EN_REG),
.USB_EXT_CNTL (USB_EXT_CNTL_REG),
.USB_IDLEMAX_POLLING (USB_IDLEMAX_POLLING_REG),
.USB_IDLEMIN_POLLING (USB_IDLEMIN_POLLING_REG),
.USB_LFPSPING_BURST (USB_LFPSPING_BURST_REG),
.USB_LFPSPOLLING_BURST (USB_LFPSPOLLING_BURST_REG),
.USB_LFPSPOLLING_IDLE_MS (USB_LFPSPOLLING_IDLE_MS_REG),
.USB_LFPSU1EXIT_BURST (USB_LFPSU1EXIT_BURST_REG),
.USB_LFPSU2LPEXIT_BURST_MS (USB_LFPSU2LPEXIT_BURST_MS_REG),
.USB_LFPSU3WAKE_BURST_MS (USB_LFPSU3WAKE_BURST_MS_REG),
.USB_LFPS_TPERIOD (USB_LFPS_TPERIOD_REG),
.USB_LFPS_TPERIOD_ACCURATE (USB_LFPS_TPERIOD_ACCURATE_REG),
.USB_MODE (USB_MODE_REG),
.USB_PCIE_ERR_REP_DIS (USB_PCIE_ERR_REP_DIS_REG),
.USB_PING_SATA_MAX_INIT (USB_PING_SATA_MAX_INIT_REG),
.USB_PING_SATA_MIN_INIT (USB_PING_SATA_MIN_INIT_REG),
.USB_POLL_SATA_MAX_BURST (USB_POLL_SATA_MAX_BURST_REG),
.USB_POLL_SATA_MIN_BURST (USB_POLL_SATA_MIN_BURST_REG),
.USB_RAW_ELEC (USB_RAW_ELEC_REG),
.USB_RXIDLE_P0_CTRL (USB_RXIDLE_P0_CTRL_REG),
.USB_TXIDLE_TUNE_ENABLE (USB_TXIDLE_TUNE_ENABLE_REG),
.USB_U1_SATA_MAX_WAKE (USB_U1_SATA_MAX_WAKE_REG),
.USB_U1_SATA_MIN_WAKE (USB_U1_SATA_MIN_WAKE_REG),
.USB_U2_SAS_MAX_COM (USB_U2_SAS_MAX_COM_REG),
.USB_U2_SAS_MIN_COM (USB_U2_SAS_MIN_COM_REG),
.USE_PCS_CLK_PHASE_SEL (USE_PCS_CLK_PHASE_SEL_REG),
.Y_ALL_MODE (Y_ALL_MODE_REG),
.BUFGTCE (BUFGTCE_out),
.BUFGTCEMASK (BUFGTCEMASK_out),
.BUFGTDIV (BUFGTDIV_out),
.BUFGTRESET (BUFGTRESET_out),
.BUFGTRSTMASK (BUFGTRSTMASK_out),
.CPLLFBCLKLOST (CPLLFBCLKLOST_out),
.CPLLLOCK (CPLLLOCK_out),
.CPLLREFCLKLOST (CPLLREFCLKLOST_out),
.CSSDSTOPCLKDONE (CSSDSTOPCLKDONE_out),
.DMONITOROUT (DMONITOROUT_out),
.DMONITOROUTCLK (DMONITOROUTCLK_out),
.DRPDO (DRPDO_out),
.DRPRDY (DRPRDY_out),
.EYESCANDATAERROR (EYESCANDATAERROR_out),
.GTPOWERGOOD (GTPOWERGOOD_out),
.GTREFCLKMONITOR (GTREFCLKMONITOR_out),
.GTYTXN (GTYTXN_out),
.GTYTXP (GTYTXP_out),
.PCIERATEGEN3 (PCIERATEGEN3_out),
.PCIERATEIDLE (PCIERATEIDLE_out),
.PCIERATEQPLLPD (PCIERATEQPLLPD_out),
.PCIERATEQPLLRESET (PCIERATEQPLLRESET_out),
.PCIESYNCTXSYNCDONE (PCIESYNCTXSYNCDONE_out),
.PCIEUSERGEN3RDY (PCIEUSERGEN3RDY_out),
.PCIEUSERPHYSTATUSRST (PCIEUSERPHYSTATUSRST_out),
.PCIEUSERRATESTART (PCIEUSERRATESTART_out),
.PCSRSVDOUT (PCSRSVDOUT_out),
.PHYSTATUS (PHYSTATUS_out),
.PINRSRVDAS (PINRSRVDAS_out),
.PMASCANOUT (PMASCANOUT_out),
.POWERPRESENT (POWERPRESENT_out),
.RESETEXCEPTION (RESETEXCEPTION_out),
.RXBUFSTATUS (RXBUFSTATUS_out),
.RXBYTEISALIGNED (RXBYTEISALIGNED_out),
.RXBYTEREALIGN (RXBYTEREALIGN_out),
.RXCDRLOCK (RXCDRLOCK_out),
.RXCDRPHDONE (RXCDRPHDONE_out),
.RXCHANBONDSEQ (RXCHANBONDSEQ_out),
.RXCHANISALIGNED (RXCHANISALIGNED_out),
.RXCHANREALIGN (RXCHANREALIGN_out),
.RXCHBONDO (RXCHBONDO_out),
.RXCKCALDONE (RXCKCALDONE_out),
.RXCLKCORCNT (RXCLKCORCNT_out),
.RXCOMINITDET (RXCOMINITDET_out),
.RXCOMMADET (RXCOMMADET_out),
.RXCOMSASDET (RXCOMSASDET_out),
.RXCOMWAKEDET (RXCOMWAKEDET_out),
.RXCTRL0 (RXCTRL0_out),
.RXCTRL1 (RXCTRL1_out),
.RXCTRL2 (RXCTRL2_out),
.RXCTRL3 (RXCTRL3_out),
.RXDATA (RXDATA_out),
.RXDATAEXTENDRSVD (RXDATAEXTENDRSVD_out),
.RXDATAVALID (RXDATAVALID_out),
.RXDLYSRESETDONE (RXDLYSRESETDONE_out),
.RXELECIDLE (RXELECIDLE_out),
.RXHEADER (RXHEADER_out),
.RXHEADERVALID (RXHEADERVALID_out),
.RXLFPSTRESETDET (RXLFPSTRESETDET_out),
.RXLFPSU2LPEXITDET (RXLFPSU2LPEXITDET_out),
.RXLFPSU3WAKEDET (RXLFPSU3WAKEDET_out),
.RXMONITOROUT (RXMONITOROUT_out),
.RXOSINTDONE (RXOSINTDONE_out),
.RXOSINTSTARTED (RXOSINTSTARTED_out),
.RXOSINTSTROBEDONE (RXOSINTSTROBEDONE_out),
.RXOSINTSTROBESTARTED (RXOSINTSTROBESTARTED_out),
.RXOUTCLK (RXOUTCLK_out),
.RXOUTCLKFABRIC (RXOUTCLKFABRIC_out),
.RXOUTCLKPCS (RXOUTCLKPCS_out),
.RXPHALIGNDONE (RXPHALIGNDONE_out),
.RXPHALIGNERR (RXPHALIGNERR_out),
.RXPMARESETDONE (RXPMARESETDONE_out),
.RXPRBSERR (RXPRBSERR_out),
.RXPRBSLOCKED (RXPRBSLOCKED_out),
.RXPRGDIVRESETDONE (RXPRGDIVRESETDONE_out),
.RXRATEDONE (RXRATEDONE_out),
.RXRECCLKOUT (RXRECCLKOUT_out),
.RXRESETDONE (RXRESETDONE_out),
.RXSLIDERDY (RXSLIDERDY_out),
.RXSLIPDONE (RXSLIPDONE_out),
.RXSLIPOUTCLKRDY (RXSLIPOUTCLKRDY_out),
.RXSLIPPMARDY (RXSLIPPMARDY_out),
.RXSTARTOFSEQ (RXSTARTOFSEQ_out),
.RXSTATUS (RXSTATUS_out),
.RXSYNCDONE (RXSYNCDONE_out),
.RXSYNCOUT (RXSYNCOUT_out),
.RXVALID (RXVALID_out),
.SCANOUT (SCANOUT_out),
.TXBUFSTATUS (TXBUFSTATUS_out),
.TXCOMFINISH (TXCOMFINISH_out),
.TXDCCDONE (TXDCCDONE_out),
.TXDLYSRESETDONE (TXDLYSRESETDONE_out),
.TXOUTCLK (TXOUTCLK_out),
.TXOUTCLKFABRIC (TXOUTCLKFABRIC_out),
.TXOUTCLKPCS (TXOUTCLKPCS_out),
.TXPHALIGNDONE (TXPHALIGNDONE_out),
.TXPHINITDONE (TXPHINITDONE_out),
.TXPMARESETDONE (TXPMARESETDONE_out),
.TXPRGDIVRESETDONE (TXPRGDIVRESETDONE_out),
.TXRATEDONE (TXRATEDONE_out),
.TXRESETDONE (TXRESETDONE_out),
.TXSYNCDONE (TXSYNCDONE_out),
.TXSYNCOUT (TXSYNCOUT_out),
.BSR_SERIAL (BSR_SERIAL_in),
.CDRSTEPDIR (CDRSTEPDIR_in),
.CDRSTEPSQ (CDRSTEPSQ_in),
.CDRSTEPSX (CDRSTEPSX_in),
.CFGRESET (CFGRESET_in),
.CLKRSVD0 (CLKRSVD0_in),
.CLKRSVD1 (CLKRSVD1_in),
.CPLLFREQLOCK (CPLLFREQLOCK_in),
.CPLLLOCKDETCLK (CPLLLOCKDETCLK_in),
.CPLLLOCKEN (CPLLLOCKEN_in),
.CPLLPD (CPLLPD_in),
.CPLLREFCLKSEL (CPLLREFCLKSEL_in),
.CPLLRESET (CPLLRESET_in),
.CSSDRSTB (CSSDRSTB_in),
.CSSDSTOPCLK (CSSDSTOPCLK_in),
.DMONFIFORESET (DMONFIFORESET_in),
.DMONITORCLK (DMONITORCLK_in),
.DRPADDR (DRPADDR_in),
.DRPCLK (DRPCLK_in),
.DRPDI (DRPDI_in),
.DRPEN (DRPEN_in),
.DRPRST (DRPRST_in),
.DRPWE (DRPWE_in),
.EYESCANRESET (EYESCANRESET_in),
.EYESCANTRIGGER (EYESCANTRIGGER_in),
.FREQOS (FREQOS_in),
.GTGREFCLK (GTGREFCLK_in),
.GTNORTHREFCLK0 (GTNORTHREFCLK0_in),
.GTNORTHREFCLK1 (GTNORTHREFCLK1_in),
.GTREFCLK0 (GTREFCLK0_in),
.GTREFCLK1 (GTREFCLK1_in),
.GTRSVD (GTRSVD_in),
.GTRXRESET (GTRXRESET_in),
.GTRXRESETSEL (GTRXRESETSEL_in),
.GTSOUTHREFCLK0 (GTSOUTHREFCLK0_in),
.GTSOUTHREFCLK1 (GTSOUTHREFCLK1_in),
.GTTXRESET (GTTXRESET_in),
.GTTXRESETSEL (GTTXRESETSEL_in),
.GTYRXN (GTYRXN_in),
.GTYRXP (GTYRXP_in),
.INCPCTRL (INCPCTRL_in),
.LOOPBACK (LOOPBACK_in),
.PCIEEQRXEQADAPTDONE (PCIEEQRXEQADAPTDONE_in),
.PCIERSTIDLE (PCIERSTIDLE_in),
.PCIERSTTXSYNCSTART (PCIERSTTXSYNCSTART_in),
.PCIEUSERRATEDONE (PCIEUSERRATEDONE_in),
.PCSRSVDIN (PCSRSVDIN_in),
.PMASCANCLK0 (PMASCANCLK0_in),
.PMASCANCLK1 (PMASCANCLK1_in),
.PMASCANCLK2 (PMASCANCLK2_in),
.PMASCANCLK3 (PMASCANCLK3_in),
.PMASCANCLK4 (PMASCANCLK4_in),
.PMASCANCLK5 (PMASCANCLK5_in),
.PMASCANCLK6 (PMASCANCLK6_in),
.PMASCANCLK7 (PMASCANCLK7_in),
.PMASCANCLK8 (PMASCANCLK8_in),
.PMASCANENB (PMASCANENB_in),
.PMASCANIN (PMASCANIN_in),
.PMASCANMODEB (PMASCANMODEB_in),
.PMASCANRSTEN (PMASCANRSTEN_in),
.QPLL0CLK (QPLL0CLK_in),
.QPLL0FREQLOCK (QPLL0FREQLOCK_in),
.QPLL0REFCLK (QPLL0REFCLK_in),
.QPLL1CLK (QPLL1CLK_in),
.QPLL1FREQLOCK (QPLL1FREQLOCK_in),
.QPLL1REFCLK (QPLL1REFCLK_in),
.RESETOVRD (RESETOVRD_in),
.RX8B10BEN (RX8B10BEN_in),
.RXAFECFOKEN (RXAFECFOKEN_in),
.RXBUFRESET (RXBUFRESET_in),
.RXCDRFREQRESET (RXCDRFREQRESET_in),
.RXCDRHOLD (RXCDRHOLD_in),
.RXCDROVRDEN (RXCDROVRDEN_in),
.RXCDRRESET (RXCDRRESET_in),
.RXCHBONDEN (RXCHBONDEN_in),
.RXCHBONDI (RXCHBONDI_in),
.RXCHBONDLEVEL (RXCHBONDLEVEL_in),
.RXCHBONDMASTER (RXCHBONDMASTER_in),
.RXCHBONDSLAVE (RXCHBONDSLAVE_in),
.RXCKCALRESET (RXCKCALRESET_in),
.RXCKCALSTART (RXCKCALSTART_in),
.RXCOMMADETEN (RXCOMMADETEN_in),
.RXDFEAGCHOLD (RXDFEAGCHOLD_in),
.RXDFEAGCOVRDEN (RXDFEAGCOVRDEN_in),
.RXDFECFOKFCNUM (RXDFECFOKFCNUM_in),
.RXDFECFOKFEN (RXDFECFOKFEN_in),
.RXDFECFOKFPULSE (RXDFECFOKFPULSE_in),
.RXDFECFOKHOLD (RXDFECFOKHOLD_in),
.RXDFECFOKOVREN (RXDFECFOKOVREN_in),
.RXDFEKHHOLD (RXDFEKHHOLD_in),
.RXDFEKHOVRDEN (RXDFEKHOVRDEN_in),
.RXDFELFHOLD (RXDFELFHOLD_in),
.RXDFELFOVRDEN (RXDFELFOVRDEN_in),
.RXDFELPMRESET (RXDFELPMRESET_in),
.RXDFETAP10HOLD (RXDFETAP10HOLD_in),
.RXDFETAP10OVRDEN (RXDFETAP10OVRDEN_in),
.RXDFETAP11HOLD (RXDFETAP11HOLD_in),
.RXDFETAP11OVRDEN (RXDFETAP11OVRDEN_in),
.RXDFETAP12HOLD (RXDFETAP12HOLD_in),
.RXDFETAP12OVRDEN (RXDFETAP12OVRDEN_in),
.RXDFETAP13HOLD (RXDFETAP13HOLD_in),
.RXDFETAP13OVRDEN (RXDFETAP13OVRDEN_in),
.RXDFETAP14HOLD (RXDFETAP14HOLD_in),
.RXDFETAP14OVRDEN (RXDFETAP14OVRDEN_in),
.RXDFETAP15HOLD (RXDFETAP15HOLD_in),
.RXDFETAP15OVRDEN (RXDFETAP15OVRDEN_in),
.RXDFETAP2HOLD (RXDFETAP2HOLD_in),
.RXDFETAP2OVRDEN (RXDFETAP2OVRDEN_in),
.RXDFETAP3HOLD (RXDFETAP3HOLD_in),
.RXDFETAP3OVRDEN (RXDFETAP3OVRDEN_in),
.RXDFETAP4HOLD (RXDFETAP4HOLD_in),
.RXDFETAP4OVRDEN (RXDFETAP4OVRDEN_in),
.RXDFETAP5HOLD (RXDFETAP5HOLD_in),
.RXDFETAP5OVRDEN (RXDFETAP5OVRDEN_in),
.RXDFETAP6HOLD (RXDFETAP6HOLD_in),
.RXDFETAP6OVRDEN (RXDFETAP6OVRDEN_in),
.RXDFETAP7HOLD (RXDFETAP7HOLD_in),
.RXDFETAP7OVRDEN (RXDFETAP7OVRDEN_in),
.RXDFETAP8HOLD (RXDFETAP8HOLD_in),
.RXDFETAP8OVRDEN (RXDFETAP8OVRDEN_in),
.RXDFETAP9HOLD (RXDFETAP9HOLD_in),
.RXDFETAP9OVRDEN (RXDFETAP9OVRDEN_in),
.RXDFEUTHOLD (RXDFEUTHOLD_in),
.RXDFEUTOVRDEN (RXDFEUTOVRDEN_in),
.RXDFEVPHOLD (RXDFEVPHOLD_in),
.RXDFEVPOVRDEN (RXDFEVPOVRDEN_in),
.RXDFEXYDEN (RXDFEXYDEN_in),
.RXDLYBYPASS (RXDLYBYPASS_in),
.RXDLYEN (RXDLYEN_in),
.RXDLYOVRDEN (RXDLYOVRDEN_in),
.RXDLYSRESET (RXDLYSRESET_in),
.RXELECIDLEMODE (RXELECIDLEMODE_in),
.RXEQTRAINING (RXEQTRAINING_in),
.RXGEARBOXSLIP (RXGEARBOXSLIP_in),
.RXLATCLK (RXLATCLK_in),
.RXLPMEN (RXLPMEN_in),
.RXLPMGCHOLD (RXLPMGCHOLD_in),
.RXLPMGCOVRDEN (RXLPMGCOVRDEN_in),
.RXLPMHFHOLD (RXLPMHFHOLD_in),
.RXLPMHFOVRDEN (RXLPMHFOVRDEN_in),
.RXLPMLFHOLD (RXLPMLFHOLD_in),
.RXLPMLFKLOVRDEN (RXLPMLFKLOVRDEN_in),
.RXLPMOSHOLD (RXLPMOSHOLD_in),
.RXLPMOSOVRDEN (RXLPMOSOVRDEN_in),
.RXMCOMMAALIGNEN (RXMCOMMAALIGNEN_in),
.RXMONITORSEL (RXMONITORSEL_in),
.RXOOBRESET (RXOOBRESET_in),
.RXOSCALRESET (RXOSCALRESET_in),
.RXOSHOLD (RXOSHOLD_in),
.RXOSOVRDEN (RXOSOVRDEN_in),
.RXOUTCLKSEL (RXOUTCLKSEL_in),
.RXPCOMMAALIGNEN (RXPCOMMAALIGNEN_in),
.RXPCSRESET (RXPCSRESET_in),
.RXPD (RXPD_in),
.RXPHALIGN (RXPHALIGN_in),
.RXPHALIGNEN (RXPHALIGNEN_in),
.RXPHDLYPD (RXPHDLYPD_in),
.RXPHDLYRESET (RXPHDLYRESET_in),
.RXPLLCLKSEL (RXPLLCLKSEL_in),
.RXPMARESET (RXPMARESET_in),
.RXPOLARITY (RXPOLARITY_in),
.RXPRBSCNTRESET (RXPRBSCNTRESET_in),
.RXPRBSSEL (RXPRBSSEL_in),
.RXPROGDIVRESET (RXPROGDIVRESET_in),
.RXRATE (RXRATE_in),
.RXRATEMODE (RXRATEMODE_in),
.RXSLIDE (RXSLIDE_in),
.RXSLIPOUTCLK (RXSLIPOUTCLK_in),
.RXSLIPPMA (RXSLIPPMA_in),
.RXSYNCALLIN (RXSYNCALLIN_in),
.RXSYNCIN (RXSYNCIN_in),
.RXSYNCMODE (RXSYNCMODE_in),
.RXSYSCLKSEL (RXSYSCLKSEL_in),
.RXTERMINATION (RXTERMINATION_in),
.RXUSERRDY (RXUSERRDY_in),
.RXUSRCLK (RXUSRCLK_in),
.RXUSRCLK2 (RXUSRCLK2_in),
.SARCCLK (SARCCLK_in),
.SCANCLK (SCANCLK_in),
.SCANENB (SCANENB_in),
.SCANIN (SCANIN_in),
.SCANMODEB (SCANMODEB_in),
.SCANRSTB (SCANRSTB_in),
.SCANRSTEN (SCANRSTEN_in),
.SIGVALIDCLK (SIGVALIDCLK_in),
.TSTCLK0 (TSTCLK0_in),
.TSTCLK1 (TSTCLK1_in),
.TSTIN (TSTIN_in),
.TSTPD (TSTPD_in),
.TSTPDOVRDB (TSTPDOVRDB_in),
.TX8B10BBYPASS (TX8B10BBYPASS_in),
.TX8B10BEN (TX8B10BEN_in),
.TXCOMINIT (TXCOMINIT_in),
.TXCOMSAS (TXCOMSAS_in),
.TXCOMWAKE (TXCOMWAKE_in),
.TXCTRL0 (TXCTRL0_in),
.TXCTRL1 (TXCTRL1_in),
.TXCTRL2 (TXCTRL2_in),
.TXDATA (TXDATA_in),
.TXDATAEXTENDRSVD (TXDATAEXTENDRSVD_in),
.TXDCCFORCESTART (TXDCCFORCESTART_in),
.TXDCCRESET (TXDCCRESET_in),
.TXDEEMPH (TXDEEMPH_in),
.TXDETECTRX (TXDETECTRX_in),
.TXDIFFCTRL (TXDIFFCTRL_in),
.TXDLYBYPASS (TXDLYBYPASS_in),
.TXDLYEN (TXDLYEN_in),
.TXDLYHOLD (TXDLYHOLD_in),
.TXDLYOVRDEN (TXDLYOVRDEN_in),
.TXDLYSRESET (TXDLYSRESET_in),
.TXDLYUPDOWN (TXDLYUPDOWN_in),
.TXELECIDLE (TXELECIDLE_in),
.TXHEADER (TXHEADER_in),
.TXINHIBIT (TXINHIBIT_in),
.TXLATCLK (TXLATCLK_in),
.TXLFPSTRESET (TXLFPSTRESET_in),
.TXLFPSU2LPEXIT (TXLFPSU2LPEXIT_in),
.TXLFPSU3WAKE (TXLFPSU3WAKE_in),
.TXMAINCURSOR (TXMAINCURSOR_in),
.TXMARGIN (TXMARGIN_in),
.TXMUXDCDEXHOLD (TXMUXDCDEXHOLD_in),
.TXMUXDCDORWREN (TXMUXDCDORWREN_in),
.TXONESZEROS (TXONESZEROS_in),
.TXOUTCLKSEL (TXOUTCLKSEL_in),
.TXPCSRESET (TXPCSRESET_in),
.TXPD (TXPD_in),
.TXPDELECIDLEMODE (TXPDELECIDLEMODE_in),
.TXPHALIGN (TXPHALIGN_in),
.TXPHALIGNEN (TXPHALIGNEN_in),
.TXPHDLYPD (TXPHDLYPD_in),
.TXPHDLYRESET (TXPHDLYRESET_in),
.TXPHDLYTSTCLK (TXPHDLYTSTCLK_in),
.TXPHINIT (TXPHINIT_in),
.TXPHOVRDEN (TXPHOVRDEN_in),
.TXPIPPMEN (TXPIPPMEN_in),
.TXPIPPMOVRDEN (TXPIPPMOVRDEN_in),
.TXPIPPMPD (TXPIPPMPD_in),
.TXPIPPMSEL (TXPIPPMSEL_in),
.TXPIPPMSTEPSIZE (TXPIPPMSTEPSIZE_in),
.TXPISOPD (TXPISOPD_in),
.TXPLLCLKSEL (TXPLLCLKSEL_in),
.TXPMARESET (TXPMARESET_in),
.TXPOLARITY (TXPOLARITY_in),
.TXPOSTCURSOR (TXPOSTCURSOR_in),
.TXPRBSFORCEERR (TXPRBSFORCEERR_in),
.TXPRBSSEL (TXPRBSSEL_in),
.TXPRECURSOR (TXPRECURSOR_in),
.TXPROGDIVRESET (TXPROGDIVRESET_in),
.TXRATE (TXRATE_in),
.TXRATEMODE (TXRATEMODE_in),
.TXSEQUENCE (TXSEQUENCE_in),
.TXSWING (TXSWING_in),
.TXSYNCALLIN (TXSYNCALLIN_in),
.TXSYNCIN (TXSYNCIN_in),
.TXSYNCMODE (TXSYNCMODE_in),
.TXSYSCLKSEL (TXSYSCLKSEL_in),
.TXUSERRDY (TXUSERRDY_in),
.TXUSRCLK (TXUSRCLK_in),
.TXUSRCLK2 (TXUSRCLK2_in),
.GSR (glblGSR)
);

`ifndef XIL_XECLIB
`ifdef XIL_TIMING
  reg notifier;
`endif

  specify
    (DMONITORCLK => DMONITOROUT[0]) = (0:0:0, 0:0:0);
    (DMONITORCLK => DMONITOROUT[10]) = (0:0:0, 0:0:0);
    (DMONITORCLK => DMONITOROUT[11]) = (0:0:0, 0:0:0);
    (DMONITORCLK => DMONITOROUT[12]) = (0:0:0, 0:0:0);
    (DMONITORCLK => DMONITOROUT[13]) = (0:0:0, 0:0:0);
    (DMONITORCLK => DMONITOROUT[14]) = (0:0:0, 0:0:0);
    (DMONITORCLK => DMONITOROUT[15]) = (0:0:0, 0:0:0);
    (DMONITORCLK => DMONITOROUT[1]) = (0:0:0, 0:0:0);
    (DMONITORCLK => DMONITOROUT[2]) = (0:0:0, 0:0:0);
    (DMONITORCLK => DMONITOROUT[3]) = (0:0:0, 0:0:0);
    (DMONITORCLK => DMONITOROUT[4]) = (0:0:0, 0:0:0);
    (DMONITORCLK => DMONITOROUT[5]) = (0:0:0, 0:0:0);
    (DMONITORCLK => DMONITOROUT[6]) = (0:0:0, 0:0:0);
    (DMONITORCLK => DMONITOROUT[7]) = (0:0:0, 0:0:0);
    (DMONITORCLK => DMONITOROUT[8]) = (0:0:0, 0:0:0);
    (DMONITORCLK => DMONITOROUT[9]) = (0:0:0, 0:0:0);
    (DRPCLK => DMONITOROUTCLK) = (100:100:100, 100:100:100);
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
    (DRPCLK => RXLFPSTRESETDET) = (100:100:100, 100:100:100);
    (GTGREFCLK => GTREFCLKMONITOR) = (0:0:0, 0:0:0);
    (GTNORTHREFCLK0 => GTREFCLKMONITOR) = (0:0:0, 0:0:0);
    (GTNORTHREFCLK1 => GTREFCLKMONITOR) = (0:0:0, 0:0:0);
    (GTREFCLK0 => GTREFCLKMONITOR) = (0:0:0, 0:0:0);
    (GTREFCLK1 => GTREFCLKMONITOR) = (0:0:0, 0:0:0);
    (GTSOUTHREFCLK0 => GTREFCLKMONITOR) = (0:0:0, 0:0:0);
    (GTSOUTHREFCLK1 => GTREFCLKMONITOR) = (0:0:0, 0:0:0);
    (RXUSRCLK => RXCHBONDO[0]) = (100:100:100, 100:100:100);
    (RXUSRCLK => RXCHBONDO[1]) = (100:100:100, 100:100:100);
    (RXUSRCLK => RXCHBONDO[2]) = (100:100:100, 100:100:100);
    (RXUSRCLK => RXCHBONDO[3]) = (100:100:100, 100:100:100);
    (RXUSRCLK => RXCHBONDO[4]) = (100:100:100, 100:100:100);
    (RXUSRCLK => RXLFPSTRESETDET) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => PHYSTATUS) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXBUFSTATUS[0]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXBUFSTATUS[1]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXBUFSTATUS[2]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXBYTEISALIGNED) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXBYTEREALIGN) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCHANBONDSEQ) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCHANISALIGNED) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCHANREALIGN) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCHBONDO[0]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCHBONDO[1]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCHBONDO[2]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCHBONDO[3]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCHBONDO[4]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCLKCORCNT[0]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCLKCORCNT[1]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCOMINITDET) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCOMMADET) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCOMSASDET) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCOMWAKEDET) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL0[0]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL0[10]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL0[11]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL0[12]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL0[13]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL0[14]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL0[15]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL0[1]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL0[2]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL0[3]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL0[4]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL0[5]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL0[6]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL0[7]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL0[8]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL0[9]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL1[0]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL1[10]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL1[11]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL1[12]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL1[13]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL1[14]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL1[15]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL1[1]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL1[2]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL1[3]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL1[4]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL1[5]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL1[6]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL1[7]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL1[8]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL1[9]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL2[0]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL2[1]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL2[2]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL2[3]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL2[4]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL2[5]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL2[6]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL2[7]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL3[0]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL3[1]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL3[2]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL3[3]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL3[4]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL3[5]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL3[6]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXCTRL3[7]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATAVALID[0]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATAVALID[1]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[0]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[100]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[101]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[102]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[103]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[104]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[105]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[106]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[107]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[108]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[109]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[10]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[110]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[111]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[112]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[113]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[114]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[115]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[116]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[117]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[118]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[119]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[11]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[120]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[121]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[122]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[123]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[124]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[125]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[126]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[127]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[12]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[13]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[14]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[15]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[16]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[17]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[18]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[19]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[1]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[20]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[21]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[22]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[23]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[24]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[25]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[26]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[27]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[28]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[29]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[2]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[30]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[31]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[32]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[33]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[34]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[35]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[36]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[37]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[38]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[39]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[3]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[40]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[41]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[42]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[43]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[44]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[45]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[46]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[47]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[48]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[49]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[4]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[50]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[51]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[52]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[53]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[54]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[55]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[56]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[57]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[58]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[59]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[5]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[60]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[61]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[62]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[63]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[64]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[65]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[66]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[67]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[68]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[69]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[6]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[70]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[71]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[72]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[73]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[74]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[75]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[76]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[77]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[78]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[79]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[7]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[80]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[81]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[82]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[83]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[84]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[85]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[86]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[87]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[88]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[89]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[8]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[90]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[91]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[92]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[93]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[94]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[95]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[96]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[97]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[98]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[99]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXDATA[9]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXHEADERVALID[0]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXHEADERVALID[1]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXHEADER[0]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXHEADER[1]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXHEADER[2]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXHEADER[3]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXHEADER[4]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXHEADER[5]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXLFPSTRESETDET) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXPRBSERR) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXPRBSLOCKED) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXRATEDONE) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXRESETDONE) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXSLIDERDY) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXSLIPDONE) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXSLIPOUTCLKRDY) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXSLIPPMARDY) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXSTARTOFSEQ[0]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXSTARTOFSEQ[1]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXSTATUS[0]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXSTATUS[1]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXSTATUS[2]) = (100:100:100, 100:100:100);
    (RXUSRCLK2 => RXVALID) = (100:100:100, 100:100:100);
    (TXUSRCLK => RXLFPSTRESETDET) = (0:0:0, 0:0:0);
    (TXUSRCLK2 => RXLFPSTRESETDET) = (100:100:100, 100:100:100);
    (TXUSRCLK2 => TXBUFSTATUS[0]) = (100:100:100, 100:100:100);
    (TXUSRCLK2 => TXBUFSTATUS[1]) = (100:100:100, 100:100:100);
    (TXUSRCLK2 => TXCOMFINISH) = (100:100:100, 100:100:100);
    (TXUSRCLK2 => TXRATEDONE) = (100:100:100, 100:100:100);
    (TXUSRCLK2 => TXRESETDONE) = (100:100:100, 100:100:100);
`ifdef XIL_TIMING
    $period (negedge DRPCLK, 0:0:0, notifier);
    $period (negedge RXUSRCLK, 0:0:0, notifier);
    $period (negedge RXUSRCLK2, 0:0:0, notifier);
    $period (negedge TXUSRCLK, 0:0:0, notifier);
    $period (negedge TXUSRCLK2, 0:0:0, notifier);
    $period (posedge DRPCLK, 0:0:0, notifier);
    $period (posedge RXUSRCLK, 0:0:0, notifier);
    $period (posedge RXUSRCLK2, 0:0:0, notifier);
    $period (posedge TXUSRCLK, 0:0:0, notifier);
    $period (posedge TXUSRCLK2, 0:0:0, notifier);
    $setuphold (posedge DRPCLK, negedge DRPADDR[0], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay[0]);
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
    $setuphold (posedge DRPCLK, posedge DRPADDR[0], 0:0:0, 0:0:0, notifier, , , DRPCLK_delay, DRPADDR_delay[0]);
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
    $setuphold (posedge RXUSRCLK, negedge RXCHBONDI[0], 0:0:0, 0:0:0, notifier, , , RXUSRCLK_delay, RXCHBONDI_delay[0]);
    $setuphold (posedge RXUSRCLK, negedge RXCHBONDI[1], 0:0:0, 0:0:0, notifier, , , RXUSRCLK_delay, RXCHBONDI_delay[1]);
    $setuphold (posedge RXUSRCLK, negedge RXCHBONDI[2], 0:0:0, 0:0:0, notifier, , , RXUSRCLK_delay, RXCHBONDI_delay[2]);
    $setuphold (posedge RXUSRCLK, negedge RXCHBONDI[3], 0:0:0, 0:0:0, notifier, , , RXUSRCLK_delay, RXCHBONDI_delay[3]);
    $setuphold (posedge RXUSRCLK, negedge RXCHBONDI[4], 0:0:0, 0:0:0, notifier, , , RXUSRCLK_delay, RXCHBONDI_delay[4]);
    $setuphold (posedge RXUSRCLK, posedge RXCHBONDI[0], 0:0:0, 0:0:0, notifier, , , RXUSRCLK_delay, RXCHBONDI_delay[0]);
    $setuphold (posedge RXUSRCLK, posedge RXCHBONDI[1], 0:0:0, 0:0:0, notifier, , , RXUSRCLK_delay, RXCHBONDI_delay[1]);
    $setuphold (posedge RXUSRCLK, posedge RXCHBONDI[2], 0:0:0, 0:0:0, notifier, , , RXUSRCLK_delay, RXCHBONDI_delay[2]);
    $setuphold (posedge RXUSRCLK, posedge RXCHBONDI[3], 0:0:0, 0:0:0, notifier, , , RXUSRCLK_delay, RXCHBONDI_delay[3]);
    $setuphold (posedge RXUSRCLK, posedge RXCHBONDI[4], 0:0:0, 0:0:0, notifier, , , RXUSRCLK_delay, RXCHBONDI_delay[4]);
    $setuphold (posedge RXUSRCLK2, negedge RX8B10BEN, 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RX8B10BEN_delay);
    $setuphold (posedge RXUSRCLK2, negedge RXCHBONDEN, 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXCHBONDEN_delay);
    $setuphold (posedge RXUSRCLK2, negedge RXCHBONDI[0], 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXCHBONDI_delay[0]);
    $setuphold (posedge RXUSRCLK2, negedge RXCHBONDI[1], 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXCHBONDI_delay[1]);
    $setuphold (posedge RXUSRCLK2, negedge RXCHBONDI[2], 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXCHBONDI_delay[2]);
    $setuphold (posedge RXUSRCLK2, negedge RXCHBONDI[3], 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXCHBONDI_delay[3]);
    $setuphold (posedge RXUSRCLK2, negedge RXCHBONDI[4], 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXCHBONDI_delay[4]);
    $setuphold (posedge RXUSRCLK2, negedge RXCHBONDLEVEL[0], 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXCHBONDLEVEL_delay[0]);
    $setuphold (posedge RXUSRCLK2, negedge RXCHBONDLEVEL[1], 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXCHBONDLEVEL_delay[1]);
    $setuphold (posedge RXUSRCLK2, negedge RXCHBONDLEVEL[2], 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXCHBONDLEVEL_delay[2]);
    $setuphold (posedge RXUSRCLK2, negedge RXCHBONDMASTER, 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXCHBONDMASTER_delay);
    $setuphold (posedge RXUSRCLK2, negedge RXCHBONDSLAVE, 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXCHBONDSLAVE_delay);
    $setuphold (posedge RXUSRCLK2, negedge RXCOMMADETEN, 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXCOMMADETEN_delay);
    $setuphold (posedge RXUSRCLK2, negedge RXGEARBOXSLIP, 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXGEARBOXSLIP_delay);
    $setuphold (posedge RXUSRCLK2, negedge RXMCOMMAALIGNEN, 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXMCOMMAALIGNEN_delay);
    $setuphold (posedge RXUSRCLK2, negedge RXPCOMMAALIGNEN, 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXPCOMMAALIGNEN_delay);
    $setuphold (posedge RXUSRCLK2, negedge RXPOLARITY, 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXPOLARITY_delay);
    $setuphold (posedge RXUSRCLK2, negedge RXPRBSCNTRESET, 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXPRBSCNTRESET_delay);
    $setuphold (posedge RXUSRCLK2, negedge RXPRBSSEL[0], 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXPRBSSEL_delay[0]);
    $setuphold (posedge RXUSRCLK2, negedge RXPRBSSEL[1], 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXPRBSSEL_delay[1]);
    $setuphold (posedge RXUSRCLK2, negedge RXPRBSSEL[2], 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXPRBSSEL_delay[2]);
    $setuphold (posedge RXUSRCLK2, negedge RXRATE[0], 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXRATE_delay[0]);
    $setuphold (posedge RXUSRCLK2, negedge RXRATE[1], 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXRATE_delay[1]);
    $setuphold (posedge RXUSRCLK2, negedge RXRATE[2], 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXRATE_delay[2]);
    $setuphold (posedge RXUSRCLK2, negedge RXSLIDE, 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXSLIDE_delay);
    $setuphold (posedge RXUSRCLK2, negedge RXSLIPOUTCLK, 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXSLIPOUTCLK_delay);
    $setuphold (posedge RXUSRCLK2, negedge RXSLIPPMA, 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXSLIPPMA_delay);
    $setuphold (posedge RXUSRCLK2, posedge RX8B10BEN, 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RX8B10BEN_delay);
    $setuphold (posedge RXUSRCLK2, posedge RXCHBONDEN, 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXCHBONDEN_delay);
    $setuphold (posedge RXUSRCLK2, posedge RXCHBONDI[0], 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXCHBONDI_delay[0]);
    $setuphold (posedge RXUSRCLK2, posedge RXCHBONDI[1], 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXCHBONDI_delay[1]);
    $setuphold (posedge RXUSRCLK2, posedge RXCHBONDI[2], 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXCHBONDI_delay[2]);
    $setuphold (posedge RXUSRCLK2, posedge RXCHBONDI[3], 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXCHBONDI_delay[3]);
    $setuphold (posedge RXUSRCLK2, posedge RXCHBONDI[4], 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXCHBONDI_delay[4]);
    $setuphold (posedge RXUSRCLK2, posedge RXCHBONDLEVEL[0], 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXCHBONDLEVEL_delay[0]);
    $setuphold (posedge RXUSRCLK2, posedge RXCHBONDLEVEL[1], 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXCHBONDLEVEL_delay[1]);
    $setuphold (posedge RXUSRCLK2, posedge RXCHBONDLEVEL[2], 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXCHBONDLEVEL_delay[2]);
    $setuphold (posedge RXUSRCLK2, posedge RXCHBONDMASTER, 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXCHBONDMASTER_delay);
    $setuphold (posedge RXUSRCLK2, posedge RXCHBONDSLAVE, 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXCHBONDSLAVE_delay);
    $setuphold (posedge RXUSRCLK2, posedge RXCOMMADETEN, 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXCOMMADETEN_delay);
    $setuphold (posedge RXUSRCLK2, posedge RXGEARBOXSLIP, 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXGEARBOXSLIP_delay);
    $setuphold (posedge RXUSRCLK2, posedge RXMCOMMAALIGNEN, 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXMCOMMAALIGNEN_delay);
    $setuphold (posedge RXUSRCLK2, posedge RXPCOMMAALIGNEN, 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXPCOMMAALIGNEN_delay);
    $setuphold (posedge RXUSRCLK2, posedge RXPOLARITY, 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXPOLARITY_delay);
    $setuphold (posedge RXUSRCLK2, posedge RXPRBSCNTRESET, 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXPRBSCNTRESET_delay);
    $setuphold (posedge RXUSRCLK2, posedge RXPRBSSEL[0], 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXPRBSSEL_delay[0]);
    $setuphold (posedge RXUSRCLK2, posedge RXPRBSSEL[1], 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXPRBSSEL_delay[1]);
    $setuphold (posedge RXUSRCLK2, posedge RXPRBSSEL[2], 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXPRBSSEL_delay[2]);
    $setuphold (posedge RXUSRCLK2, posedge RXRATE[0], 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXRATE_delay[0]);
    $setuphold (posedge RXUSRCLK2, posedge RXRATE[1], 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXRATE_delay[1]);
    $setuphold (posedge RXUSRCLK2, posedge RXRATE[2], 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXRATE_delay[2]);
    $setuphold (posedge RXUSRCLK2, posedge RXSLIDE, 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXSLIDE_delay);
    $setuphold (posedge RXUSRCLK2, posedge RXSLIPOUTCLK, 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXSLIPOUTCLK_delay);
    $setuphold (posedge RXUSRCLK2, posedge RXSLIPPMA, 0:0:0, 0:0:0, notifier, , , RXUSRCLK2_delay, RXSLIPPMA_delay);
    $setuphold (posedge TXUSRCLK2, negedge TX8B10BBYPASS[0], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TX8B10BBYPASS_delay[0]);
    $setuphold (posedge TXUSRCLK2, negedge TX8B10BBYPASS[1], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TX8B10BBYPASS_delay[1]);
    $setuphold (posedge TXUSRCLK2, negedge TX8B10BBYPASS[2], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TX8B10BBYPASS_delay[2]);
    $setuphold (posedge TXUSRCLK2, negedge TX8B10BBYPASS[3], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TX8B10BBYPASS_delay[3]);
    $setuphold (posedge TXUSRCLK2, negedge TX8B10BBYPASS[4], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TX8B10BBYPASS_delay[4]);
    $setuphold (posedge TXUSRCLK2, negedge TX8B10BBYPASS[5], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TX8B10BBYPASS_delay[5]);
    $setuphold (posedge TXUSRCLK2, negedge TX8B10BBYPASS[6], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TX8B10BBYPASS_delay[6]);
    $setuphold (posedge TXUSRCLK2, negedge TX8B10BBYPASS[7], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TX8B10BBYPASS_delay[7]);
    $setuphold (posedge TXUSRCLK2, negedge TX8B10BEN, 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TX8B10BEN_delay);
    $setuphold (posedge TXUSRCLK2, negedge TXCOMINIT, 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCOMINIT_delay);
    $setuphold (posedge TXUSRCLK2, negedge TXCOMSAS, 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCOMSAS_delay);
    $setuphold (posedge TXUSRCLK2, negedge TXCOMWAKE, 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCOMWAKE_delay);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL0[0], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[0]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL0[10], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[10]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL0[11], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[11]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL0[12], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[12]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL0[13], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[13]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL0[14], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[14]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL0[15], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[15]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL0[1], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[1]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL0[2], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[2]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL0[3], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[3]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL0[4], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[4]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL0[5], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[5]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL0[6], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[6]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL0[7], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[7]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL0[8], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[8]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL0[9], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[9]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL1[0], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[0]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL1[10], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[10]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL1[11], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[11]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL1[12], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[12]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL1[13], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[13]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL1[14], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[14]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL1[15], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[15]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL1[1], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[1]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL1[2], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[2]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL1[3], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[3]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL1[4], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[4]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL1[5], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[5]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL1[6], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[6]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL1[7], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[7]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL1[8], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[8]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL1[9], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[9]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL2[0], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL2_delay[0]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL2[1], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL2_delay[1]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL2[2], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL2_delay[2]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL2[3], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL2_delay[3]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL2[4], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL2_delay[4]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL2[5], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL2_delay[5]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL2[6], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL2_delay[6]);
    $setuphold (posedge TXUSRCLK2, negedge TXCTRL2[7], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL2_delay[7]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[0], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[0]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[100], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[100]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[101], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[101]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[102], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[102]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[103], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[103]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[104], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[104]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[105], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[105]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[106], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[106]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[107], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[107]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[108], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[108]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[109], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[109]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[10], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[10]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[110], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[110]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[111], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[111]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[112], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[112]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[113], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[113]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[114], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[114]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[115], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[115]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[116], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[116]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[117], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[117]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[118], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[118]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[119], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[119]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[11], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[11]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[120], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[120]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[121], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[121]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[122], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[122]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[123], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[123]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[124], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[124]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[125], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[125]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[126], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[126]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[127], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[127]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[12], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[12]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[13], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[13]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[14], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[14]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[15], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[15]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[16], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[16]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[17], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[17]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[18], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[18]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[19], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[19]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[1], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[1]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[20], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[20]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[21], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[21]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[22], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[22]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[23], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[23]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[24], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[24]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[25], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[25]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[26], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[26]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[27], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[27]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[28], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[28]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[29], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[29]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[2], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[2]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[30], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[30]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[31], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[31]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[32], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[32]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[33], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[33]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[34], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[34]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[35], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[35]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[36], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[36]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[37], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[37]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[38], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[38]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[39], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[39]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[3], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[3]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[40], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[40]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[41], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[41]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[42], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[42]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[43], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[43]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[44], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[44]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[45], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[45]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[46], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[46]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[47], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[47]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[48], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[48]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[49], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[49]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[4], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[4]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[50], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[50]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[51], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[51]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[52], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[52]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[53], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[53]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[54], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[54]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[55], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[55]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[56], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[56]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[57], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[57]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[58], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[58]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[59], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[59]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[5], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[5]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[60], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[60]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[61], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[61]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[62], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[62]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[63], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[63]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[64], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[64]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[65], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[65]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[66], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[66]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[67], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[67]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[68], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[68]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[69], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[69]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[6], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[6]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[70], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[70]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[71], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[71]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[72], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[72]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[73], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[73]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[74], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[74]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[75], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[75]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[76], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[76]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[77], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[77]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[78], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[78]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[79], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[79]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[7], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[7]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[80], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[80]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[81], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[81]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[82], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[82]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[83], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[83]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[84], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[84]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[85], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[85]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[86], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[86]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[87], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[87]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[88], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[88]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[89], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[89]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[8], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[8]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[90], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[90]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[91], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[91]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[92], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[92]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[93], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[93]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[94], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[94]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[95], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[95]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[96], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[96]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[97], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[97]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[98], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[98]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[99], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[99]);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA[9], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[9]);
    $setuphold (posedge TXUSRCLK2, negedge TXDETECTRX, 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDETECTRX_delay);
    $setuphold (posedge TXUSRCLK2, negedge TXELECIDLE, 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXELECIDLE_delay);
    $setuphold (posedge TXUSRCLK2, negedge TXHEADER[0], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXHEADER_delay[0]);
    $setuphold (posedge TXUSRCLK2, negedge TXHEADER[1], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXHEADER_delay[1]);
    $setuphold (posedge TXUSRCLK2, negedge TXHEADER[2], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXHEADER_delay[2]);
    $setuphold (posedge TXUSRCLK2, negedge TXHEADER[3], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXHEADER_delay[3]);
    $setuphold (posedge TXUSRCLK2, negedge TXHEADER[4], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXHEADER_delay[4]);
    $setuphold (posedge TXUSRCLK2, negedge TXHEADER[5], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXHEADER_delay[5]);
    $setuphold (posedge TXUSRCLK2, negedge TXINHIBIT, 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXINHIBIT_delay);
    $setuphold (posedge TXUSRCLK2, negedge TXPD[0], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXPD_delay[0]);
    $setuphold (posedge TXUSRCLK2, negedge TXPD[1], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXPD_delay[1]);
    $setuphold (posedge TXUSRCLK2, negedge TXPOLARITY, 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXPOLARITY_delay);
    $setuphold (posedge TXUSRCLK2, negedge TXPRBSFORCEERR, 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXPRBSFORCEERR_delay);
    $setuphold (posedge TXUSRCLK2, negedge TXPRBSSEL[0], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXPRBSSEL_delay[0]);
    $setuphold (posedge TXUSRCLK2, negedge TXPRBSSEL[1], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXPRBSSEL_delay[1]);
    $setuphold (posedge TXUSRCLK2, negedge TXPRBSSEL[2], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXPRBSSEL_delay[2]);
    $setuphold (posedge TXUSRCLK2, negedge TXPRBSSEL[3], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXPRBSSEL_delay[3]);
    $setuphold (posedge TXUSRCLK2, negedge TXRATE[0], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXRATE_delay[0]);
    $setuphold (posedge TXUSRCLK2, negedge TXRATE[1], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXRATE_delay[1]);
    $setuphold (posedge TXUSRCLK2, negedge TXRATE[2], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXRATE_delay[2]);
    $setuphold (posedge TXUSRCLK2, negedge TXSEQUENCE[0], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXSEQUENCE_delay[0]);
    $setuphold (posedge TXUSRCLK2, negedge TXSEQUENCE[1], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXSEQUENCE_delay[1]);
    $setuphold (posedge TXUSRCLK2, negedge TXSEQUENCE[2], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXSEQUENCE_delay[2]);
    $setuphold (posedge TXUSRCLK2, negedge TXSEQUENCE[3], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXSEQUENCE_delay[3]);
    $setuphold (posedge TXUSRCLK2, negedge TXSEQUENCE[4], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXSEQUENCE_delay[4]);
    $setuphold (posedge TXUSRCLK2, negedge TXSEQUENCE[5], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXSEQUENCE_delay[5]);
    $setuphold (posedge TXUSRCLK2, negedge TXSEQUENCE[6], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXSEQUENCE_delay[6]);
    $setuphold (posedge TXUSRCLK2, posedge TX8B10BBYPASS[0], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TX8B10BBYPASS_delay[0]);
    $setuphold (posedge TXUSRCLK2, posedge TX8B10BBYPASS[1], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TX8B10BBYPASS_delay[1]);
    $setuphold (posedge TXUSRCLK2, posedge TX8B10BBYPASS[2], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TX8B10BBYPASS_delay[2]);
    $setuphold (posedge TXUSRCLK2, posedge TX8B10BBYPASS[3], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TX8B10BBYPASS_delay[3]);
    $setuphold (posedge TXUSRCLK2, posedge TX8B10BBYPASS[4], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TX8B10BBYPASS_delay[4]);
    $setuphold (posedge TXUSRCLK2, posedge TX8B10BBYPASS[5], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TX8B10BBYPASS_delay[5]);
    $setuphold (posedge TXUSRCLK2, posedge TX8B10BBYPASS[6], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TX8B10BBYPASS_delay[6]);
    $setuphold (posedge TXUSRCLK2, posedge TX8B10BBYPASS[7], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TX8B10BBYPASS_delay[7]);
    $setuphold (posedge TXUSRCLK2, posedge TX8B10BEN, 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TX8B10BEN_delay);
    $setuphold (posedge TXUSRCLK2, posedge TXCOMINIT, 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCOMINIT_delay);
    $setuphold (posedge TXUSRCLK2, posedge TXCOMSAS, 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCOMSAS_delay);
    $setuphold (posedge TXUSRCLK2, posedge TXCOMWAKE, 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCOMWAKE_delay);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL0[0], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[0]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL0[10], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[10]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL0[11], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[11]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL0[12], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[12]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL0[13], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[13]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL0[14], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[14]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL0[15], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[15]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL0[1], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[1]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL0[2], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[2]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL0[3], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[3]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL0[4], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[4]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL0[5], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[5]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL0[6], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[6]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL0[7], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[7]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL0[8], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[8]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL0[9], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL0_delay[9]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL1[0], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[0]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL1[10], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[10]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL1[11], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[11]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL1[12], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[12]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL1[13], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[13]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL1[14], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[14]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL1[15], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[15]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL1[1], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[1]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL1[2], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[2]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL1[3], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[3]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL1[4], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[4]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL1[5], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[5]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL1[6], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[6]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL1[7], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[7]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL1[8], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[8]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL1[9], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL1_delay[9]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL2[0], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL2_delay[0]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL2[1], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL2_delay[1]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL2[2], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL2_delay[2]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL2[3], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL2_delay[3]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL2[4], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL2_delay[4]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL2[5], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL2_delay[5]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL2[6], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL2_delay[6]);
    $setuphold (posedge TXUSRCLK2, posedge TXCTRL2[7], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXCTRL2_delay[7]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[0], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[0]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[100], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[100]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[101], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[101]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[102], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[102]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[103], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[103]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[104], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[104]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[105], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[105]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[106], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[106]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[107], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[107]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[108], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[108]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[109], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[109]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[10], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[10]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[110], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[110]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[111], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[111]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[112], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[112]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[113], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[113]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[114], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[114]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[115], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[115]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[116], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[116]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[117], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[117]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[118], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[118]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[119], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[119]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[11], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[11]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[120], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[120]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[121], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[121]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[122], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[122]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[123], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[123]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[124], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[124]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[125], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[125]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[126], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[126]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[127], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[127]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[12], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[12]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[13], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[13]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[14], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[14]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[15], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[15]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[16], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[16]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[17], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[17]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[18], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[18]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[19], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[19]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[1], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[1]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[20], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[20]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[21], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[21]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[22], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[22]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[23], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[23]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[24], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[24]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[25], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[25]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[26], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[26]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[27], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[27]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[28], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[28]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[29], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[29]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[2], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[2]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[30], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[30]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[31], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[31]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[32], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[32]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[33], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[33]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[34], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[34]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[35], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[35]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[36], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[36]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[37], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[37]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[38], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[38]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[39], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[39]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[3], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[3]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[40], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[40]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[41], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[41]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[42], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[42]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[43], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[43]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[44], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[44]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[45], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[45]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[46], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[46]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[47], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[47]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[48], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[48]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[49], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[49]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[4], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[4]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[50], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[50]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[51], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[51]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[52], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[52]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[53], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[53]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[54], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[54]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[55], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[55]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[56], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[56]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[57], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[57]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[58], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[58]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[59], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[59]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[5], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[5]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[60], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[60]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[61], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[61]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[62], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[62]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[63], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[63]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[64], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[64]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[65], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[65]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[66], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[66]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[67], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[67]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[68], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[68]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[69], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[69]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[6], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[6]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[70], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[70]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[71], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[71]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[72], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[72]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[73], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[73]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[74], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[74]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[75], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[75]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[76], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[76]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[77], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[77]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[78], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[78]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[79], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[79]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[7], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[7]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[80], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[80]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[81], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[81]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[82], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[82]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[83], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[83]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[84], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[84]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[85], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[85]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[86], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[86]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[87], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[87]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[88], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[88]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[89], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[89]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[8], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[8]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[90], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[90]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[91], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[91]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[92], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[92]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[93], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[93]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[94], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[94]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[95], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[95]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[96], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[96]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[97], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[97]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[98], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[98]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[99], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[99]);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA[9], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDATA_delay[9]);
    $setuphold (posedge TXUSRCLK2, posedge TXDETECTRX, 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXDETECTRX_delay);
    $setuphold (posedge TXUSRCLK2, posedge TXELECIDLE, 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXELECIDLE_delay);
    $setuphold (posedge TXUSRCLK2, posedge TXHEADER[0], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXHEADER_delay[0]);
    $setuphold (posedge TXUSRCLK2, posedge TXHEADER[1], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXHEADER_delay[1]);
    $setuphold (posedge TXUSRCLK2, posedge TXHEADER[2], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXHEADER_delay[2]);
    $setuphold (posedge TXUSRCLK2, posedge TXHEADER[3], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXHEADER_delay[3]);
    $setuphold (posedge TXUSRCLK2, posedge TXHEADER[4], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXHEADER_delay[4]);
    $setuphold (posedge TXUSRCLK2, posedge TXHEADER[5], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXHEADER_delay[5]);
    $setuphold (posedge TXUSRCLK2, posedge TXINHIBIT, 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXINHIBIT_delay);
    $setuphold (posedge TXUSRCLK2, posedge TXPD[0], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXPD_delay[0]);
    $setuphold (posedge TXUSRCLK2, posedge TXPD[1], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXPD_delay[1]);
    $setuphold (posedge TXUSRCLK2, posedge TXPOLARITY, 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXPOLARITY_delay);
    $setuphold (posedge TXUSRCLK2, posedge TXPRBSFORCEERR, 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXPRBSFORCEERR_delay);
    $setuphold (posedge TXUSRCLK2, posedge TXPRBSSEL[0], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXPRBSSEL_delay[0]);
    $setuphold (posedge TXUSRCLK2, posedge TXPRBSSEL[1], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXPRBSSEL_delay[1]);
    $setuphold (posedge TXUSRCLK2, posedge TXPRBSSEL[2], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXPRBSSEL_delay[2]);
    $setuphold (posedge TXUSRCLK2, posedge TXPRBSSEL[3], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXPRBSSEL_delay[3]);
    $setuphold (posedge TXUSRCLK2, posedge TXRATE[0], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXRATE_delay[0]);
    $setuphold (posedge TXUSRCLK2, posedge TXRATE[1], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXRATE_delay[1]);
    $setuphold (posedge TXUSRCLK2, posedge TXRATE[2], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXRATE_delay[2]);
    $setuphold (posedge TXUSRCLK2, posedge TXSEQUENCE[0], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXSEQUENCE_delay[0]);
    $setuphold (posedge TXUSRCLK2, posedge TXSEQUENCE[1], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXSEQUENCE_delay[1]);
    $setuphold (posedge TXUSRCLK2, posedge TXSEQUENCE[2], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXSEQUENCE_delay[2]);
    $setuphold (posedge TXUSRCLK2, posedge TXSEQUENCE[3], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXSEQUENCE_delay[3]);
    $setuphold (posedge TXUSRCLK2, posedge TXSEQUENCE[4], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXSEQUENCE_delay[4]);
    $setuphold (posedge TXUSRCLK2, posedge TXSEQUENCE[5], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXSEQUENCE_delay[5]);
    $setuphold (posedge TXUSRCLK2, posedge TXSEQUENCE[6], 0:0:0, 0:0:0, notifier, , , TXUSRCLK2_delay, TXSEQUENCE_delay[6]);
    $width (negedge DRPCLK, 0:0:0, 0, notifier);
    $width (negedge RXUSRCLK, 0:0:0, 0, notifier);
    $width (negedge RXUSRCLK2, 0:0:0, 0, notifier);
    $width (negedge TXUSRCLK, 0:0:0, 0, notifier);
    $width (negedge TXUSRCLK2, 0:0:0, 0, notifier);
    $width (posedge DRPCLK, 0:0:0, 0, notifier);
    $width (posedge RXUSRCLK, 0:0:0, 0, notifier);
    $width (posedge RXUSRCLK2, 0:0:0, 0, notifier);
    $width (posedge TXUSRCLK, 0:0:0, 0, notifier);
    $width (posedge TXUSRCLK2, 0:0:0, 0, notifier);
`endif
    specparam PATHPULSE$ = 0;
  endspecify
`endif
endmodule

`endcelldefine
