///////////////////////////////////////////////////////
//     Copyright (c) 2011 Xilinx Inc.
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
///////////////////////////////////////////////////////
//
//   ____   ___
//  /   /\/   / 
// /___/  \  /     Vendor      : Xilinx 
// \  \    \/      Version     :  13.1
//  \  \           Description : 
//  /  /                      
// /__/   /\       Filename    : GTPE2_CHANNEL.uniprim.v
// \  \  /  \ 
//  \__\/\__ \                    
//                                 
//  11/8/12  - 686589 - YML default changes
//  01/18/13 - 695630 - added drp monitor
//  08/29/14 - 821138 - add negedge specify section for IS_INVERTED*CLK*
///////////////////////////////////////////////////////

`timescale 1 ps / 1 ps 
`celldefine
module GTPE2_CHANNEL (
  DMONITOROUT,
  DRPDO,
  DRPRDY,
  EYESCANDATAERROR,
  GTPTXN,
  GTPTXP,
  PCSRSVDOUT,
  PHYSTATUS,
  PMARSVDOUT0,
  PMARSVDOUT1,
  RXBUFSTATUS,
  RXBYTEISALIGNED,
  RXBYTEREALIGN,
  RXCDRLOCK,
  RXCHANBONDSEQ,
  RXCHANISALIGNED,
  RXCHANREALIGN,
  RXCHARISCOMMA,
  RXCHARISK,
  RXCHBONDO,
  RXCLKCORCNT,
  RXCOMINITDET,
  RXCOMMADET,
  RXCOMSASDET,
  RXCOMWAKEDET,
  RXDATA,
  RXDATAVALID,
  RXDISPERR,
  RXDLYSRESETDONE,
  RXELECIDLE,
  RXHEADER,
  RXHEADERVALID,
  RXNOTINTABLE,
  RXOSINTDONE,
  RXOSINTSTARTED,
  RXOSINTSTROBEDONE,
  RXOSINTSTROBESTARTED,
  RXOUTCLK,
  RXOUTCLKFABRIC,
  RXOUTCLKPCS,
  RXPHALIGNDONE,
  RXPHMONITOR,
  RXPHSLIPMONITOR,
  RXPMARESETDONE,
  RXPRBSERR,
  RXRATEDONE,
  RXRESETDONE,
  RXSTARTOFSEQ,
  RXSTATUS,
  RXSYNCDONE,
  RXSYNCOUT,
  RXVALID,
  TXBUFSTATUS,
  TXCOMFINISH,
  TXDLYSRESETDONE,
  TXGEARBOXREADY,
  TXOUTCLK,
  TXOUTCLKFABRIC,
  TXOUTCLKPCS,
  TXPHALIGNDONE,
  TXPHINITDONE,
  TXPMARESETDONE,
  TXRATEDONE,
  TXRESETDONE,
  TXSYNCDONE,
  TXSYNCOUT,

  CFGRESET,
  CLKRSVD0,
  CLKRSVD1,
  DMONFIFORESET,
  DMONITORCLK,
  DRPADDR,
  DRPCLK,
  DRPDI,
  DRPEN,
  DRPWE,
  EYESCANMODE,
  EYESCANRESET,
  EYESCANTRIGGER,
  GTPRXN,
  GTPRXP,
  GTRESETSEL,
  GTRSVD,
  GTRXRESET,
  GTTXRESET,
  LOOPBACK,
  PCSRSVDIN,
  PLL0CLK,
  PLL0REFCLK,
  PLL1CLK,
  PLL1REFCLK,
  PMARSVDIN0,
  PMARSVDIN1,
  PMARSVDIN2,
  PMARSVDIN3,
  PMARSVDIN4,
  RESETOVRD,
  RX8B10BEN,
  RXADAPTSELTEST,
  RXBUFRESET,
  RXCDRFREQRESET,
  RXCDRHOLD,
  RXCDROVRDEN,
  RXCDRRESET,
  RXCDRRESETRSV,
  RXCHBONDEN,
  RXCHBONDI,
  RXCHBONDLEVEL,
  RXCHBONDMASTER,
  RXCHBONDSLAVE,
  RXCOMMADETEN,
  RXDDIEN,
  RXDFEXYDEN,
  RXDLYBYPASS,
  RXDLYEN,
  RXDLYOVRDEN,
  RXDLYSRESET,
  RXELECIDLEMODE,
  RXGEARBOXSLIP,
  RXLPMHFHOLD,
  RXLPMHFOVRDEN,
  RXLPMLFHOLD,
  RXLPMLFOVRDEN,
  RXLPMOSINTNTRLEN,
  RXLPMRESET,
  RXMCOMMAALIGNEN,
  RXOOBRESET,
  RXOSCALRESET,
  RXOSHOLD,
  RXOSINTCFG,
  RXOSINTEN,
  RXOSINTHOLD,
  RXOSINTID0,
  RXOSINTNTRLEN,
  RXOSINTOVRDEN,
  RXOSINTPD,
  RXOSINTSTROBE,
  RXOSINTTESTOVRDEN,
  RXOSOVRDEN,
  RXOUTCLKSEL,
  RXPCOMMAALIGNEN,
  RXPCSRESET,
  RXPD,
  RXPHALIGN,
  RXPHALIGNEN,
  RXPHDLYPD,
  RXPHDLYRESET,
  RXPHOVRDEN,
  RXPMARESET,
  RXPOLARITY,
  RXPRBSCNTRESET,
  RXPRBSSEL,
  RXRATE,
  RXRATEMODE,
  RXSLIDE,
  RXSYNCALLIN,
  RXSYNCIN,
  RXSYNCMODE,
  RXSYSCLKSEL,
  RXUSERRDY,
  RXUSRCLK,
  RXUSRCLK2,
  SETERRSTATUS,
  SIGVALIDCLK,
  TSTIN,
  TX8B10BBYPASS,
  TX8B10BEN,
  TXBUFDIFFCTRL,
  TXCHARDISPMODE,
  TXCHARDISPVAL,
  TXCHARISK,
  TXCOMINIT,
  TXCOMSAS,
  TXCOMWAKE,
  TXDATA,
  TXDEEMPH,
  TXDETECTRX,
  TXDIFFCTRL,
  TXDIFFPD,
  TXDLYBYPASS,
  TXDLYEN,
  TXDLYHOLD,
  TXDLYOVRDEN,
  TXDLYSRESET,
  TXDLYUPDOWN,
  TXELECIDLE,
  TXHEADER,
  TXINHIBIT,
  TXMAINCURSOR,
  TXMARGIN,
  TXOUTCLKSEL,
  TXPCSRESET,
  TXPD,
  TXPDELECIDLEMODE,
  TXPHALIGN,
  TXPHALIGNEN,
  TXPHDLYPD,
  TXPHDLYRESET,
  TXPHDLYTSTCLK,
  TXPHINIT,
  TXPHOVRDEN,
  TXPIPPMEN,
  TXPIPPMOVRDEN,
  TXPIPPMPD,
  TXPIPPMSEL,
  TXPIPPMSTEPSIZE,
  TXPISOPD,
  TXPMARESET,
  TXPOLARITY,
  TXPOSTCURSOR,
  TXPOSTCURSORINV,
  TXPRBSFORCEERR,
  TXPRBSSEL,
  TXPRECURSOR,
  TXPRECURSORINV,
  TXRATE,
  TXRATEMODE,
  TXSEQUENCE,
  TXSTARTSEQ,
  TXSWING,
  TXSYNCALLIN,
  TXSYNCIN,
  TXSYNCMODE,
  TXSYSCLKSEL,
  TXUSERRDY,
  TXUSRCLK,
  TXUSRCLK2
);

  `ifdef XIL_TIMING //Simprim 
  parameter LOC = "UNPLACED";
  `endif
    parameter [0:0] ACJTAG_DEBUG_MODE = 1'b0;
  parameter [0:0] ACJTAG_MODE = 1'b0;
  parameter [0:0] ACJTAG_RESET = 1'b0;
  parameter [19:0] ADAPT_CFG0 = 20'b00000000000000000000;
  parameter ALIGN_COMMA_DOUBLE = "FALSE";
  parameter [9:0] ALIGN_COMMA_ENABLE = 10'b0001111111;
  parameter integer ALIGN_COMMA_WORD = 1;
  parameter ALIGN_MCOMMA_DET = "TRUE";
  parameter [9:0] ALIGN_MCOMMA_VALUE = 10'b1010000011;
  parameter ALIGN_PCOMMA_DET = "TRUE";
  parameter [9:0] ALIGN_PCOMMA_VALUE = 10'b0101111100;
  parameter CBCC_DATA_SOURCE_SEL = "DECODED";
  parameter [42:0] CFOK_CFG = 43'b1001001000000000000000001000000111010000000;
  parameter [6:0] CFOK_CFG2 = 7'b0100000;
  parameter [6:0] CFOK_CFG3 = 7'b0100000;
  parameter [0:0] CFOK_CFG4 = 1'b0;
  parameter [1:0] CFOK_CFG5 = 2'b00;
  parameter [3:0] CFOK_CFG6 = 4'b0000;
  parameter CHAN_BOND_KEEP_ALIGN = "FALSE";
  parameter integer CHAN_BOND_MAX_SKEW = 7;
  parameter [9:0] CHAN_BOND_SEQ_1_1 = 10'b0101111100;
  parameter [9:0] CHAN_BOND_SEQ_1_2 = 10'b0000000000;
  parameter [9:0] CHAN_BOND_SEQ_1_3 = 10'b0000000000;
  parameter [9:0] CHAN_BOND_SEQ_1_4 = 10'b0000000000;
  parameter [3:0] CHAN_BOND_SEQ_1_ENABLE = 4'b1111;
  parameter [9:0] CHAN_BOND_SEQ_2_1 = 10'b0100000000;
  parameter [9:0] CHAN_BOND_SEQ_2_2 = 10'b0100000000;
  parameter [9:0] CHAN_BOND_SEQ_2_3 = 10'b0100000000;
  parameter [9:0] CHAN_BOND_SEQ_2_4 = 10'b0100000000;
  parameter [3:0] CHAN_BOND_SEQ_2_ENABLE = 4'b1111;
  parameter CHAN_BOND_SEQ_2_USE = "FALSE";
  parameter integer CHAN_BOND_SEQ_LEN = 1;
  parameter [0:0] CLK_COMMON_SWING = 1'b0;
  parameter CLK_CORRECT_USE = "TRUE";
  parameter CLK_COR_KEEP_IDLE = "FALSE";
  parameter integer CLK_COR_MAX_LAT = 20;
  parameter integer CLK_COR_MIN_LAT = 18;
  parameter CLK_COR_PRECEDENCE = "TRUE";
  parameter integer CLK_COR_REPEAT_WAIT = 0;
  parameter [9:0] CLK_COR_SEQ_1_1 = 10'b0100011100;
  parameter [9:0] CLK_COR_SEQ_1_2 = 10'b0000000000;
  parameter [9:0] CLK_COR_SEQ_1_3 = 10'b0000000000;
  parameter [9:0] CLK_COR_SEQ_1_4 = 10'b0000000000;
  parameter [3:0] CLK_COR_SEQ_1_ENABLE = 4'b1111;
  parameter [9:0] CLK_COR_SEQ_2_1 = 10'b0100000000;
  parameter [9:0] CLK_COR_SEQ_2_2 = 10'b0100000000;
  parameter [9:0] CLK_COR_SEQ_2_3 = 10'b0100000000;
  parameter [9:0] CLK_COR_SEQ_2_4 = 10'b0100000000;
  parameter [3:0] CLK_COR_SEQ_2_ENABLE = 4'b1111;
  parameter CLK_COR_SEQ_2_USE = "FALSE";
  parameter integer CLK_COR_SEQ_LEN = 1;
  parameter DEC_MCOMMA_DETECT = "TRUE";
  parameter DEC_PCOMMA_DETECT = "TRUE";
  parameter DEC_VALID_COMMA_ONLY = "TRUE";
  parameter [23:0] DMONITOR_CFG = 24'h000A00;
  parameter [0:0] ES_CLK_PHASE_SEL = 1'b0;
  parameter [5:0] ES_CONTROL = 6'b000000;
  parameter ES_ERRDET_EN = "FALSE";
  parameter ES_EYE_SCAN_EN = "FALSE";
  parameter [11:0] ES_HORZ_OFFSET = 12'h010;
  parameter [9:0] ES_PMA_CFG = 10'b0000000000;
  parameter [4:0] ES_PRESCALE = 5'b00000;
  parameter [79:0] ES_QUALIFIER = 80'h00000000000000000000;
  parameter [79:0] ES_QUAL_MASK = 80'h00000000000000000000;
  parameter [79:0] ES_SDATA_MASK = 80'h00000000000000000000;
  parameter [8:0] ES_VERT_OFFSET = 9'b000000000;
  parameter [3:0] FTS_DESKEW_SEQ_ENABLE = 4'b1111;
  parameter [3:0] FTS_LANE_DESKEW_CFG = 4'b1111;
  parameter FTS_LANE_DESKEW_EN = "FALSE";
  parameter [2:0] GEARBOX_MODE = 3'b000;
  parameter [0:0] IS_CLKRSVD0_INVERTED = 1'b0;
  parameter [0:0] IS_CLKRSVD1_INVERTED = 1'b0;
  parameter [0:0] IS_DMONITORCLK_INVERTED = 1'b0;
  parameter [0:0] IS_DRPCLK_INVERTED = 1'b0;
  parameter [0:0] IS_RXUSRCLK2_INVERTED = 1'b0;
  parameter [0:0] IS_RXUSRCLK_INVERTED = 1'b0;
  parameter [0:0] IS_SIGVALIDCLK_INVERTED = 1'b0;
  parameter [0:0] IS_TXPHDLYTSTCLK_INVERTED = 1'b0;
  parameter [0:0] IS_TXUSRCLK2_INVERTED = 1'b0;
  parameter [0:0] IS_TXUSRCLK_INVERTED = 1'b0;
  parameter [0:0] LOOPBACK_CFG = 1'b0;
  parameter [1:0] OUTREFCLK_SEL_INV = 2'b11;
  parameter PCS_PCIE_EN = "FALSE";
  parameter [47:0] PCS_RSVD_ATTR = 48'h000000000000;
  parameter [11:0] PD_TRANS_TIME_FROM_P2 = 12'h03C;
  parameter [7:0] PD_TRANS_TIME_NONE_P2 = 8'h19;
  parameter [7:0] PD_TRANS_TIME_TO_P2 = 8'h64;
  parameter [0:0] PMA_LOOPBACK_CFG = 1'b0;
  parameter [31:0] PMA_RSV = 32'h00000333;
  parameter [31:0] PMA_RSV2 = 32'h00002050;
  parameter [1:0] PMA_RSV3 = 2'b00;
  parameter [3:0] PMA_RSV4 = 4'b0000;
  parameter [0:0] PMA_RSV5 = 1'b0;
  parameter [0:0] PMA_RSV6 = 1'b0;
  parameter [0:0] PMA_RSV7 = 1'b0;
  parameter [4:0] RXBUFRESET_TIME = 5'b00001;
  parameter RXBUF_ADDR_MODE = "FULL";
  parameter [3:0] RXBUF_EIDLE_HI_CNT = 4'b1000;
  parameter [3:0] RXBUF_EIDLE_LO_CNT = 4'b0000;
  parameter RXBUF_EN = "TRUE";
  parameter RXBUF_RESET_ON_CB_CHANGE = "TRUE";
  parameter RXBUF_RESET_ON_COMMAALIGN = "FALSE";
  parameter RXBUF_RESET_ON_EIDLE = "FALSE";
  parameter RXBUF_RESET_ON_RATE_CHANGE = "TRUE";
  parameter integer RXBUF_THRESH_OVFLW = 61;
  parameter RXBUF_THRESH_OVRD = "FALSE";
  parameter integer RXBUF_THRESH_UNDFLW = 4;
  parameter [4:0] RXCDRFREQRESET_TIME = 5'b00001;
  parameter [4:0] RXCDRPHRESET_TIME = 5'b00001;
  parameter [82:0] RXCDR_CFG = 83'h0000107FE406001041010;
  parameter [0:0] RXCDR_FR_RESET_ON_EIDLE = 1'b0;
  parameter [0:0] RXCDR_HOLD_DURING_EIDLE = 1'b0;
  parameter [5:0] RXCDR_LOCK_CFG = 6'b001001;
  parameter [0:0] RXCDR_PH_RESET_ON_EIDLE = 1'b0;
  parameter [15:0] RXDLY_CFG = 16'h0010;
  parameter [8:0] RXDLY_LCFG = 9'h020;
  parameter [15:0] RXDLY_TAP_CFG = 16'h0000;
  parameter RXGEARBOX_EN = "FALSE";
  parameter [4:0] RXISCANRESET_TIME = 5'b00001;
  parameter [6:0] RXLPMRESET_TIME = 7'b0001111;
  parameter [0:0] RXLPM_BIAS_STARTUP_DISABLE = 1'b0;
  parameter [3:0] RXLPM_CFG = 4'b0110;
  parameter [0:0] RXLPM_CFG1 = 1'b0;
  parameter [0:0] RXLPM_CM_CFG = 1'b0;
  parameter [8:0] RXLPM_GC_CFG = 9'b111100010;
  parameter [2:0] RXLPM_GC_CFG2 = 3'b001;
  parameter [13:0] RXLPM_HF_CFG = 14'b00001111110000;
  parameter [4:0] RXLPM_HF_CFG2 = 5'b01010;
  parameter [3:0] RXLPM_HF_CFG3 = 4'b0000;
  parameter [0:0] RXLPM_HOLD_DURING_EIDLE = 1'b0;
  parameter [0:0] RXLPM_INCM_CFG = 1'b0;
  parameter [0:0] RXLPM_IPCM_CFG = 1'b0;
  parameter [17:0] RXLPM_LF_CFG = 18'b000000001111110000;
  parameter [4:0] RXLPM_LF_CFG2 = 5'b01010;
  parameter [2:0] RXLPM_OSINT_CFG = 3'b100;
  parameter [6:0] RXOOB_CFG = 7'b0000110;
  parameter RXOOB_CLK_CFG = "PMA";
  parameter [4:0] RXOSCALRESET_TIME = 5'b00011;
  parameter [4:0] RXOSCALRESET_TIMEOUT = 5'b00000;
  parameter integer RXOUT_DIV = 2;
  parameter [4:0] RXPCSRESET_TIME = 5'b00001;
  parameter [23:0] RXPHDLY_CFG = 24'h084000;
  parameter [23:0] RXPH_CFG = 24'hC00002;
  parameter [4:0] RXPH_MONITOR_SEL = 5'b00000;
  parameter [2:0] RXPI_CFG0 = 3'b000;
  parameter [0:0] RXPI_CFG1 = 1'b0;
  parameter [0:0] RXPI_CFG2 = 1'b0;
  parameter [4:0] RXPMARESET_TIME = 5'b00011;
  parameter [0:0] RXPRBS_ERR_LOOPBACK = 1'b0;
  parameter integer RXSLIDE_AUTO_WAIT = 7;
  parameter RXSLIDE_MODE = "OFF";
  parameter [0:0] RXSYNC_MULTILANE = 1'b0;
  parameter [0:0] RXSYNC_OVRD = 1'b0;
  parameter [0:0] RXSYNC_SKIP_DA = 1'b0;
  parameter [15:0] RX_BIAS_CFG = 16'b0000111100110011;
  parameter [5:0] RX_BUFFER_CFG = 6'b000000;
  parameter integer RX_CLK25_DIV = 7;
  parameter [0:0] RX_CLKMUX_EN = 1'b1;
  parameter [1:0] RX_CM_SEL = 2'b11;
  parameter [3:0] RX_CM_TRIM = 4'b0100;
  parameter integer RX_DATA_WIDTH = 20;
  parameter [5:0] RX_DDI_SEL = 6'b000000;
  parameter [13:0] RX_DEBUG_CFG = 14'b00000000000000;
  parameter RX_DEFER_RESET_BUF_EN = "TRUE";
  parameter RX_DISPERR_SEQ_MATCH = "TRUE";
  parameter [12:0] RX_OS_CFG = 13'b0001111110000;
  parameter integer RX_SIG_VALID_DLY = 10;
  parameter RX_XCLK_SEL = "RXREC";
  parameter integer SAS_MAX_COM = 64;
  parameter integer SAS_MIN_COM = 36;
  parameter [3:0] SATA_BURST_SEQ_LEN = 4'b1111;
  parameter [2:0] SATA_BURST_VAL = 3'b100;
  parameter [2:0] SATA_EIDLE_VAL = 3'b100;
  parameter integer SATA_MAX_BURST = 8;
  parameter integer SATA_MAX_INIT = 21;
  parameter integer SATA_MAX_WAKE = 7;
  parameter integer SATA_MIN_BURST = 4;
  parameter integer SATA_MIN_INIT = 12;
  parameter integer SATA_MIN_WAKE = 4;
  parameter SATA_PLL_CFG = "VCO_3000MHZ";
  parameter SHOW_REALIGN_COMMA = "TRUE";
  parameter SIM_RECEIVER_DETECT_PASS = "TRUE";
  parameter SIM_RESET_SPEEDUP = "TRUE";
  parameter SIM_TX_EIDLE_DRIVE_LEVEL = "X";
  parameter SIM_VERSION = "1.0";
  parameter [14:0] TERM_RCAL_CFG = 15'b100001000010000;
  parameter [2:0] TERM_RCAL_OVRD = 3'b000;
  parameter [7:0] TRANS_TIME_RATE = 8'h0E;
  parameter [31:0] TST_RSV = 32'h00000000;
  parameter TXBUF_EN = "TRUE";
  parameter TXBUF_RESET_ON_RATE_CHANGE = "FALSE";
  parameter [15:0] TXDLY_CFG = 16'h0010;
  parameter [8:0] TXDLY_LCFG = 9'h020;
  parameter [15:0] TXDLY_TAP_CFG = 16'h0000;
  parameter TXGEARBOX_EN = "FALSE";
  parameter [0:0] TXOOB_CFG = 1'b0;
  parameter integer TXOUT_DIV = 2;
  parameter [4:0] TXPCSRESET_TIME = 5'b00001;
  parameter [23:0] TXPHDLY_CFG = 24'h084000;
  parameter [15:0] TXPH_CFG = 16'h0400;
  parameter [4:0] TXPH_MONITOR_SEL = 5'b00000;
  parameter [1:0] TXPI_CFG0 = 2'b00;
  parameter [1:0] TXPI_CFG1 = 2'b00;
  parameter [1:0] TXPI_CFG2 = 2'b00;
  parameter [0:0] TXPI_CFG3 = 1'b0;
  parameter [0:0] TXPI_CFG4 = 1'b0;
  parameter [2:0] TXPI_CFG5 = 3'b000;
  parameter [0:0] TXPI_GREY_SEL = 1'b0;
  parameter [0:0] TXPI_INVSTROBE_SEL = 1'b0;
  parameter TXPI_PPMCLK_SEL = "TXUSRCLK2";
  parameter [7:0] TXPI_PPM_CFG = 8'b00000000;
  parameter [2:0] TXPI_SYNFREQ_PPM = 3'b000;
  parameter [4:0] TXPMARESET_TIME = 5'b00001;
  parameter [0:0] TXSYNC_MULTILANE = 1'b0;
  parameter [0:0] TXSYNC_OVRD = 1'b0;
  parameter [0:0] TXSYNC_SKIP_DA = 1'b0;
  parameter integer TX_CLK25_DIV = 7;
  parameter [0:0] TX_CLKMUX_EN = 1'b1;
  parameter integer TX_DATA_WIDTH = 20;
  parameter [5:0] TX_DEEMPH0 = 6'b000000;
  parameter [5:0] TX_DEEMPH1 = 6'b000000;
  parameter TX_DRIVE_MODE = "DIRECT";
  parameter [2:0] TX_EIDLE_ASSERT_DELAY = 3'b110;
  parameter [2:0] TX_EIDLE_DEASSERT_DELAY = 3'b100;
  parameter TX_LOOPBACK_DRIVE_HIZ = "FALSE";
  parameter [0:0] TX_MAINCURSOR_SEL = 1'b0;
  parameter [6:0] TX_MARGIN_FULL_0 = 7'b1001110;
  parameter [6:0] TX_MARGIN_FULL_1 = 7'b1001001;
  parameter [6:0] TX_MARGIN_FULL_2 = 7'b1000101;
  parameter [6:0] TX_MARGIN_FULL_3 = 7'b1000010;
  parameter [6:0] TX_MARGIN_FULL_4 = 7'b1000000;
  parameter [6:0] TX_MARGIN_LOW_0 = 7'b1000110;
  parameter [6:0] TX_MARGIN_LOW_1 = 7'b1000100;
  parameter [6:0] TX_MARGIN_LOW_2 = 7'b1000010;
  parameter [6:0] TX_MARGIN_LOW_3 = 7'b1000000;
  parameter [6:0] TX_MARGIN_LOW_4 = 7'b1000000;
  parameter [0:0] TX_PREDRIVER_MODE = 1'b0;
  parameter [13:0] TX_RXDETECT_CFG = 14'h1832;
  parameter [2:0] TX_RXDETECT_REF = 3'b100;
  parameter TX_XCLK_SEL = "TXUSR";
  parameter [0:0] UCODEER_CLR = 1'b0;
  parameter [0:0] USE_PCS_CLK_PHASE_SEL = 1'b0;


  localparam in_delay = 0;
  localparam out_delay = 0;
  localparam INCLK_DELAY = 0;
  localparam OUTCLK_DELAY = 0;

  output DRPRDY;
  output EYESCANDATAERROR;
  output GTPTXN;
  output GTPTXP;
  output PHYSTATUS;
  output PMARSVDOUT0;
  output PMARSVDOUT1;
  output RXBYTEISALIGNED;
  output RXBYTEREALIGN;
  output RXCDRLOCK;
  output RXCHANBONDSEQ;
  output RXCHANISALIGNED;
  output RXCHANREALIGN;
  output RXCOMINITDET;
  output RXCOMMADET;
  output RXCOMSASDET;
  output RXCOMWAKEDET;
  output RXDLYSRESETDONE;
  output RXELECIDLE;
  output RXHEADERVALID;
  output RXOSINTDONE;
  output RXOSINTSTARTED;
  output RXOSINTSTROBEDONE;
  output RXOSINTSTROBESTARTED;
  output RXOUTCLK;
  output RXOUTCLKFABRIC;
  output RXOUTCLKPCS;
  output RXPHALIGNDONE;
  output RXPMARESETDONE;
  output RXPRBSERR;
  output RXRATEDONE;
  output RXRESETDONE;
  output RXSYNCDONE;
  output RXSYNCOUT;
  output RXVALID;
  output TXCOMFINISH;
  output TXDLYSRESETDONE;
  output TXGEARBOXREADY;
  output TXOUTCLK;
  output TXOUTCLKFABRIC;
  output TXOUTCLKPCS;
  output TXPHALIGNDONE;
  output TXPHINITDONE;
  output TXPMARESETDONE;
  output TXRATEDONE;
  output TXRESETDONE;
  output TXSYNCDONE;
  output TXSYNCOUT;
  output [14:0] DMONITOROUT;
  output [15:0] DRPDO;
  output [15:0] PCSRSVDOUT;
  output [1:0] RXCLKCORCNT;
  output [1:0] RXDATAVALID;
  output [1:0] RXSTARTOFSEQ;
  output [1:0] TXBUFSTATUS;
  output [2:0] RXBUFSTATUS;
  output [2:0] RXHEADER;
  output [2:0] RXSTATUS;
  output [31:0] RXDATA;
  output [3:0] RXCHARISCOMMA;
  output [3:0] RXCHARISK;
  output [3:0] RXCHBONDO;
  output [3:0] RXDISPERR;
  output [3:0] RXNOTINTABLE;
  output [4:0] RXPHMONITOR;
  output [4:0] RXPHSLIPMONITOR;

  input CFGRESET;
  input CLKRSVD0;
  input CLKRSVD1;
  input DMONFIFORESET;
  input DMONITORCLK;
  input DRPCLK;
  input DRPEN;
  input DRPWE;
  input EYESCANMODE;
  input EYESCANRESET;
  input EYESCANTRIGGER;
  input GTPRXN;
  input GTPRXP;
  input GTRESETSEL;
  input GTRXRESET;
  input GTTXRESET;
  input PLL0CLK;
  input PLL0REFCLK;
  input PLL1CLK;
  input PLL1REFCLK;
  input PMARSVDIN0;
  input PMARSVDIN1;
  input PMARSVDIN2;
  input PMARSVDIN3;
  input PMARSVDIN4;
  input RESETOVRD;
  input RX8B10BEN;
  input RXBUFRESET;
  input RXCDRFREQRESET;
  input RXCDRHOLD;
  input RXCDROVRDEN;
  input RXCDRRESET;
  input RXCDRRESETRSV;
  input RXCHBONDEN;
  input RXCHBONDMASTER;
  input RXCHBONDSLAVE;
  input RXCOMMADETEN;
  input RXDDIEN;
  input RXDFEXYDEN;
  input RXDLYBYPASS;
  input RXDLYEN;
  input RXDLYOVRDEN;
  input RXDLYSRESET;
  input RXGEARBOXSLIP;
  input RXLPMHFHOLD;
  input RXLPMHFOVRDEN;
  input RXLPMLFHOLD;
  input RXLPMLFOVRDEN;
  input RXLPMOSINTNTRLEN;
  input RXLPMRESET;
  input RXMCOMMAALIGNEN;
  input RXOOBRESET;
  input RXOSCALRESET;
  input RXOSHOLD;
  input RXOSINTEN;
  input RXOSINTHOLD;
  input RXOSINTNTRLEN;
  input RXOSINTOVRDEN;
  input RXOSINTPD;
  input RXOSINTSTROBE;
  input RXOSINTTESTOVRDEN;
  input RXOSOVRDEN;
  input RXPCOMMAALIGNEN;
  input RXPCSRESET;
  input RXPHALIGN;
  input RXPHALIGNEN;
  input RXPHDLYPD;
  input RXPHDLYRESET;
  input RXPHOVRDEN;
  input RXPMARESET;
  input RXPOLARITY;
  input RXPRBSCNTRESET;
  input RXRATEMODE;
  input RXSLIDE;
  input RXSYNCALLIN;
  input RXSYNCIN;
  input RXSYNCMODE;
  input RXUSERRDY;
  input RXUSRCLK2;
  input RXUSRCLK;
  input SETERRSTATUS;
  input SIGVALIDCLK;
  input TX8B10BEN;
  input TXCOMINIT;
  input TXCOMSAS;
  input TXCOMWAKE;
  input TXDEEMPH;
  input TXDETECTRX;
  input TXDIFFPD;
  input TXDLYBYPASS;
  input TXDLYEN;
  input TXDLYHOLD;
  input TXDLYOVRDEN;
  input TXDLYSRESET;
  input TXDLYUPDOWN;
  input TXELECIDLE;
  input TXINHIBIT;
  input TXPCSRESET;
  input TXPDELECIDLEMODE;
  input TXPHALIGN;
  input TXPHALIGNEN;
  input TXPHDLYPD;
  input TXPHDLYRESET;
  input TXPHDLYTSTCLK;
  input TXPHINIT;
  input TXPHOVRDEN;
  input TXPIPPMEN;
  input TXPIPPMOVRDEN;
  input TXPIPPMPD;
  input TXPIPPMSEL;
  input TXPISOPD;
  input TXPMARESET;
  input TXPOLARITY;
  input TXPOSTCURSORINV;
  input TXPRBSFORCEERR;
  input TXPRECURSORINV;
  input TXRATEMODE;
  input TXSTARTSEQ;
  input TXSWING;
  input TXSYNCALLIN;
  input TXSYNCIN;
  input TXSYNCMODE;
  input TXUSERRDY;
  input TXUSRCLK2;
  input TXUSRCLK;
  input [13:0] RXADAPTSELTEST;
  input [15:0] DRPDI;
  input [15:0] GTRSVD;
  input [15:0] PCSRSVDIN;
  input [19:0] TSTIN;
  input [1:0] RXELECIDLEMODE;
  input [1:0] RXPD;
  input [1:0] RXSYSCLKSEL;
  input [1:0] TXPD;
  input [1:0] TXSYSCLKSEL;
  input [2:0] LOOPBACK;
  input [2:0] RXCHBONDLEVEL;
  input [2:0] RXOUTCLKSEL;
  input [2:0] RXPRBSSEL;
  input [2:0] RXRATE;
  input [2:0] TXBUFDIFFCTRL;
  input [2:0] TXHEADER;
  input [2:0] TXMARGIN;
  input [2:0] TXOUTCLKSEL;
  input [2:0] TXPRBSSEL;
  input [2:0] TXRATE;
  input [31:0] TXDATA;
  input [3:0] RXCHBONDI;
  input [3:0] RXOSINTCFG;
  input [3:0] RXOSINTID0;
  input [3:0] TX8B10BBYPASS;
  input [3:0] TXCHARDISPMODE;
  input [3:0] TXCHARDISPVAL;
  input [3:0] TXCHARISK;
  input [3:0] TXDIFFCTRL;
  input [4:0] TXPIPPMSTEPSIZE;
  input [4:0] TXPOSTCURSOR;
  input [4:0] TXPRECURSOR;
  input [6:0] TXMAINCURSOR;
  input [6:0] TXSEQUENCE;
  input [8:0] DRPADDR;

  reg SIM_RECEIVER_DETECT_PASS_BINARY;
  reg SIM_RESET_SPEEDUP_BINARY;
  reg SIM_TX_EIDLE_DRIVE_LEVEL_BINARY;
  reg SIM_VERSION_BINARY;
  reg [0:0] ACJTAG_DEBUG_MODE_BINARY;
  reg [0:0] ACJTAG_MODE_BINARY;
  reg [0:0] ACJTAG_RESET_BINARY;
  reg [0:0] ALIGN_COMMA_DOUBLE_BINARY;
  reg [0:0] ALIGN_MCOMMA_DET_BINARY;
  reg [0:0] ALIGN_PCOMMA_DET_BINARY;
  reg [0:0] CBCC_DATA_SOURCE_SEL_BINARY;
  reg [0:0] CFOK_CFG4_BINARY;
  reg [0:0] CHAN_BOND_KEEP_ALIGN_BINARY;
  reg [0:0] CHAN_BOND_SEQ_2_USE_BINARY;
  reg [0:0] CLK_COMMON_SWING_BINARY;
  reg [0:0] CLK_CORRECT_USE_BINARY;
  reg [0:0] CLK_COR_KEEP_IDLE_BINARY;
  reg [0:0] CLK_COR_PRECEDENCE_BINARY;
  reg [0:0] CLK_COR_SEQ_2_USE_BINARY;
  reg [0:0] DEC_MCOMMA_DETECT_BINARY;
  reg [0:0] DEC_PCOMMA_DETECT_BINARY;
  reg [0:0] DEC_VALID_COMMA_ONLY_BINARY;
  reg [0:0] ES_CLK_PHASE_SEL_BINARY;
  reg [0:0] ES_ERRDET_EN_BINARY;
  reg [0:0] ES_EYE_SCAN_EN_BINARY;
  reg [0:0] FTS_LANE_DESKEW_EN_BINARY;
  reg [0:0] LOOPBACK_CFG_BINARY;
  reg [0:0] PCS_PCIE_EN_BINARY;
  reg [0:0] PMA_LOOPBACK_CFG_BINARY;
  reg [0:0] PMA_RSV5_BINARY;
  reg [0:0] PMA_RSV6_BINARY;
  reg [0:0] PMA_RSV7_BINARY;
  reg [0:0] RXBUF_ADDR_MODE_BINARY;
  reg [0:0] RXBUF_EN_BINARY;
  reg [0:0] RXBUF_RESET_ON_CB_CHANGE_BINARY;
  reg [0:0] RXBUF_RESET_ON_COMMAALIGN_BINARY;
  reg [0:0] RXBUF_RESET_ON_EIDLE_BINARY;
  reg [0:0] RXBUF_RESET_ON_RATE_CHANGE_BINARY;
  reg [0:0] RXBUF_THRESH_OVRD_BINARY;
  reg [0:0] RXCDR_FR_RESET_ON_EIDLE_BINARY;
  reg [0:0] RXCDR_HOLD_DURING_EIDLE_BINARY;
  reg [0:0] RXCDR_PH_RESET_ON_EIDLE_BINARY;
  reg [0:0] RXGEARBOX_EN_BINARY;
  reg [0:0] RXLPM_BIAS_STARTUP_DISABLE_BINARY;
  reg [0:0] RXLPM_CFG1_BINARY;
  reg [0:0] RXLPM_CM_CFG_BINARY;
  reg [0:0] RXLPM_HOLD_DURING_EIDLE_BINARY;
  reg [0:0] RXLPM_INCM_CFG_BINARY;
  reg [0:0] RXLPM_IPCM_CFG_BINARY;
  reg [0:0] RXOOB_CLK_CFG_BINARY;
  reg [0:0] RXPI_CFG1_BINARY;
  reg [0:0] RXPI_CFG2_BINARY;
  reg [0:0] RXPRBS_ERR_LOOPBACK_BINARY;
  reg [0:0] RXSYNC_MULTILANE_BINARY;
  reg [0:0] RXSYNC_OVRD_BINARY;
  reg [0:0] RXSYNC_SKIP_DA_BINARY;
  reg [0:0] RX_CLKMUX_EN_BINARY;
  reg [0:0] RX_DEFER_RESET_BUF_EN_BINARY;
  reg [0:0] RX_DISPERR_SEQ_MATCH_BINARY;
  reg [0:0] RX_XCLK_SEL_BINARY;
  reg [0:0] SHOW_REALIGN_COMMA_BINARY;
  reg [0:0] TXBUF_EN_BINARY;
  reg [0:0] TXBUF_RESET_ON_RATE_CHANGE_BINARY;
  reg [0:0] TXGEARBOX_EN_BINARY;
  reg [0:0] TXOOB_CFG_BINARY;
  reg [0:0] TXPI_CFG3_BINARY;
  reg [0:0] TXPI_CFG4_BINARY;
  reg [0:0] TXPI_GREY_SEL_BINARY;
  reg [0:0] TXPI_INVSTROBE_SEL_BINARY;
  reg [0:0] TXPI_PPMCLK_SEL_BINARY;
  reg [0:0] TXSYNC_MULTILANE_BINARY;
  reg [0:0] TXSYNC_OVRD_BINARY;
  reg [0:0] TXSYNC_SKIP_DA_BINARY;
  reg [0:0] TX_CLKMUX_EN_BINARY;
  reg [0:0] TX_LOOPBACK_DRIVE_HIZ_BINARY;
  reg [0:0] TX_MAINCURSOR_SEL_BINARY;
  reg [0:0] TX_PREDRIVER_MODE_BINARY;
  reg [0:0] TX_XCLK_SEL_BINARY;
  reg [0:0] UCODEER_CLR_BINARY;
  reg [0:0] USE_PCS_CLK_PHASE_SEL_BINARY;
  reg [12:0] RX_OS_CFG_BINARY;
  reg [13:0] RXLPM_HF_CFG_BINARY;
  reg [13:0] RX_DEBUG_CFG_BINARY;
  reg [14:0] TERM_RCAL_CFG_BINARY;
  reg [15:0] RX_BIAS_CFG_BINARY;
  reg [17:0] RXLPM_LF_CFG_BINARY;
  reg [19:0] ADAPT_CFG0_BINARY;
  reg [1:0] ALIGN_COMMA_WORD_BINARY;
  reg [1:0] CFOK_CFG5_BINARY;
  reg [1:0] CHAN_BOND_SEQ_LEN_BINARY;
  reg [1:0] CLK_COR_SEQ_LEN_BINARY;
  reg [1:0] OUTREFCLK_SEL_INV_BINARY;
  reg [1:0] PMA_RSV3_BINARY;
  reg [1:0] RXSLIDE_MODE_BINARY;
  reg [1:0] RX_CM_SEL_BINARY;
  reg [1:0] SATA_PLL_CFG_BINARY;
  reg [1:0] TXPI_CFG0_BINARY;
  reg [1:0] TXPI_CFG1_BINARY;
  reg [1:0] TXPI_CFG2_BINARY;
  reg [2:0] GEARBOX_MODE_BINARY;
  reg [2:0] RXLPM_GC_CFG2_BINARY;
  reg [2:0] RXLPM_OSINT_CFG_BINARY;
  reg [2:0] RXOUT_DIV_BINARY;
  reg [2:0] RXPI_CFG0_BINARY;
  reg [2:0] RX_DATA_WIDTH_BINARY;
  reg [2:0] SATA_BURST_VAL_BINARY;
  reg [2:0] SATA_EIDLE_VAL_BINARY;
  reg [2:0] TERM_RCAL_OVRD_BINARY;
  reg [2:0] TXOUT_DIV_BINARY;
  reg [2:0] TXPI_CFG5_BINARY;
  reg [2:0] TXPI_SYNFREQ_PPM_BINARY;
  reg [2:0] TX_DATA_WIDTH_BINARY;
  reg [2:0] TX_EIDLE_ASSERT_DELAY_BINARY;
  reg [2:0] TX_EIDLE_DEASSERT_DELAY_BINARY;
  reg [2:0] TX_RXDETECT_REF_BINARY;
  reg [3:0] CFOK_CFG6_BINARY;
  reg [3:0] CHAN_BOND_MAX_SKEW_BINARY;
  reg [3:0] CHAN_BOND_SEQ_1_ENABLE_BINARY;
  reg [3:0] CHAN_BOND_SEQ_2_ENABLE_BINARY;
  reg [3:0] CLK_COR_SEQ_1_ENABLE_BINARY;
  reg [3:0] CLK_COR_SEQ_2_ENABLE_BINARY;
  reg [3:0] FTS_DESKEW_SEQ_ENABLE_BINARY;
  reg [3:0] FTS_LANE_DESKEW_CFG_BINARY;
  reg [3:0] PMA_RSV4_BINARY;
  reg [3:0] RXBUF_EIDLE_HI_CNT_BINARY;
  reg [3:0] RXBUF_EIDLE_LO_CNT_BINARY;
  reg [3:0] RXLPM_CFG_BINARY;
  reg [3:0] RXLPM_HF_CFG3_BINARY;
  reg [3:0] RXSLIDE_AUTO_WAIT_BINARY;
  reg [3:0] RX_CM_TRIM_BINARY;
  reg [3:0] SATA_BURST_SEQ_LEN_BINARY;
  reg [42:0] CFOK_CFG_BINARY;
  reg [4:0] CLK_COR_REPEAT_WAIT_BINARY;
  reg [4:0] ES_PRESCALE_BINARY;
  reg [4:0] RXBUFRESET_TIME_BINARY;
  reg [4:0] RXCDRFREQRESET_TIME_BINARY;
  reg [4:0] RXCDRPHRESET_TIME_BINARY;
  reg [4:0] RXISCANRESET_TIME_BINARY;
  reg [4:0] RXLPM_HF_CFG2_BINARY;
  reg [4:0] RXLPM_LF_CFG2_BINARY;
  reg [4:0] RXOSCALRESET_TIMEOUT_BINARY;
  reg [4:0] RXOSCALRESET_TIME_BINARY;
  reg [4:0] RXPCSRESET_TIME_BINARY;
  reg [4:0] RXPH_MONITOR_SEL_BINARY;
  reg [4:0] RXPMARESET_TIME_BINARY;
  reg [4:0] RX_CLK25_DIV_BINARY;
  reg [4:0] RX_SIG_VALID_DLY_BINARY;
  reg [4:0] TXPCSRESET_TIME_BINARY;
  reg [4:0] TXPH_MONITOR_SEL_BINARY;
  reg [4:0] TXPMARESET_TIME_BINARY;
  reg [4:0] TX_CLK25_DIV_BINARY;
  reg [4:0] TX_DRIVE_MODE_BINARY;
  reg [5:0] CLK_COR_MAX_LAT_BINARY;
  reg [5:0] CLK_COR_MIN_LAT_BINARY;
  reg [5:0] ES_CONTROL_BINARY;
  reg [5:0] RXBUF_THRESH_OVFLW_BINARY;
  reg [5:0] RXBUF_THRESH_UNDFLW_BINARY;
  reg [5:0] RXCDR_LOCK_CFG_BINARY;
  reg [5:0] RX_BUFFER_CFG_BINARY;
  reg [5:0] RX_DDI_SEL_BINARY;
  reg [5:0] SAS_MIN_COM_BINARY;
  reg [5:0] SATA_MAX_BURST_BINARY;
  reg [5:0] SATA_MAX_INIT_BINARY;
  reg [5:0] SATA_MAX_WAKE_BINARY;
  reg [5:0] SATA_MIN_BURST_BINARY;
  reg [5:0] SATA_MIN_INIT_BINARY;
  reg [5:0] SATA_MIN_WAKE_BINARY;
  reg [5:0] TX_DEEMPH0_BINARY;
  reg [5:0] TX_DEEMPH1_BINARY;
  reg [6:0] CFOK_CFG2_BINARY;
  reg [6:0] CFOK_CFG3_BINARY;
  reg [6:0] RXLPMRESET_TIME_BINARY;
  reg [6:0] RXOOB_CFG_BINARY;
  reg [6:0] SAS_MAX_COM_BINARY;
  reg [6:0] TX_MARGIN_FULL_0_BINARY;
  reg [6:0] TX_MARGIN_FULL_1_BINARY;
  reg [6:0] TX_MARGIN_FULL_2_BINARY;
  reg [6:0] TX_MARGIN_FULL_3_BINARY;
  reg [6:0] TX_MARGIN_FULL_4_BINARY;
  reg [6:0] TX_MARGIN_LOW_0_BINARY;
  reg [6:0] TX_MARGIN_LOW_1_BINARY;
  reg [6:0] TX_MARGIN_LOW_2_BINARY;
  reg [6:0] TX_MARGIN_LOW_3_BINARY;
  reg [6:0] TX_MARGIN_LOW_4_BINARY;
  reg [7:0] TXPI_PPM_CFG_BINARY;
  reg [8:0] ES_VERT_OFFSET_BINARY;
  reg [8:0] RXLPM_GC_CFG_BINARY;
  reg [9:0] ALIGN_COMMA_ENABLE_BINARY;
  reg [9:0] ALIGN_MCOMMA_VALUE_BINARY;
  reg [9:0] ALIGN_PCOMMA_VALUE_BINARY;
  reg [9:0] CHAN_BOND_SEQ_1_1_BINARY;
  reg [9:0] CHAN_BOND_SEQ_1_2_BINARY;
  reg [9:0] CHAN_BOND_SEQ_1_3_BINARY;
  reg [9:0] CHAN_BOND_SEQ_1_4_BINARY;
  reg [9:0] CHAN_BOND_SEQ_2_1_BINARY;
  reg [9:0] CHAN_BOND_SEQ_2_2_BINARY;
  reg [9:0] CHAN_BOND_SEQ_2_3_BINARY;
  reg [9:0] CHAN_BOND_SEQ_2_4_BINARY;
  reg [9:0] CLK_COR_SEQ_1_1_BINARY;
  reg [9:0] CLK_COR_SEQ_1_2_BINARY;
  reg [9:0] CLK_COR_SEQ_1_3_BINARY;
  reg [9:0] CLK_COR_SEQ_1_4_BINARY;
  reg [9:0] CLK_COR_SEQ_2_1_BINARY;
  reg [9:0] CLK_COR_SEQ_2_2_BINARY;
  reg [9:0] CLK_COR_SEQ_2_3_BINARY;
  reg [9:0] CLK_COR_SEQ_2_4_BINARY;
  reg [9:0] ES_PMA_CFG_BINARY;

  tri0 GSR = glbl.GSR;
  reg notifier;

  initial begin
    case (ALIGN_COMMA_DOUBLE)
      "FALSE" : ALIGN_COMMA_DOUBLE_BINARY = 1'b0;
      "TRUE" : ALIGN_COMMA_DOUBLE_BINARY = 1'b1;
      default : begin
        $display("Attribute Syntax Error : The Attribute ALIGN_COMMA_DOUBLE on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are FALSE, or TRUE.", ALIGN_COMMA_DOUBLE);
        #1 $finish;
      end
    endcase

    case (ALIGN_MCOMMA_DET)
      "TRUE" : ALIGN_MCOMMA_DET_BINARY = 1'b1;
      "FALSE" : ALIGN_MCOMMA_DET_BINARY = 1'b0;
      default : begin
        $display("Attribute Syntax Error : The Attribute ALIGN_MCOMMA_DET on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are TRUE, or FALSE.", ALIGN_MCOMMA_DET);
        #1 $finish;
      end
    endcase

    case (ALIGN_PCOMMA_DET)
      "TRUE" : ALIGN_PCOMMA_DET_BINARY = 1'b1;
      "FALSE" : ALIGN_PCOMMA_DET_BINARY = 1'b0;
      default : begin
        $display("Attribute Syntax Error : The Attribute ALIGN_PCOMMA_DET on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are TRUE, or FALSE.", ALIGN_PCOMMA_DET);
        #1 $finish;
      end
    endcase

    case (CBCC_DATA_SOURCE_SEL)
      "DECODED" : CBCC_DATA_SOURCE_SEL_BINARY = 1'b1;
      "ENCODED" : CBCC_DATA_SOURCE_SEL_BINARY = 1'b0;
      default : begin
        $display("Attribute Syntax Error : The Attribute CBCC_DATA_SOURCE_SEL on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are DECODED, or ENCODED.", CBCC_DATA_SOURCE_SEL);
        #1 $finish;
      end
    endcase

    case (CHAN_BOND_KEEP_ALIGN)
      "FALSE" : CHAN_BOND_KEEP_ALIGN_BINARY = 1'b0;
      "TRUE" : CHAN_BOND_KEEP_ALIGN_BINARY = 1'b1;
      default : begin
        $display("Attribute Syntax Error : The Attribute CHAN_BOND_KEEP_ALIGN on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are FALSE, or TRUE.", CHAN_BOND_KEEP_ALIGN);
        #1 $finish;
      end
    endcase

    case (CHAN_BOND_SEQ_2_USE)
      "FALSE" : CHAN_BOND_SEQ_2_USE_BINARY = 1'b0;
      "TRUE" : CHAN_BOND_SEQ_2_USE_BINARY = 1'b1;
      default : begin
        $display("Attribute Syntax Error : The Attribute CHAN_BOND_SEQ_2_USE on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are FALSE, or TRUE.", CHAN_BOND_SEQ_2_USE);
        #1 $finish;
      end
    endcase

    case (CHAN_BOND_SEQ_LEN)
      1 : CHAN_BOND_SEQ_LEN_BINARY = 2'b00;
      2 : CHAN_BOND_SEQ_LEN_BINARY = 2'b01;
      3 : CHAN_BOND_SEQ_LEN_BINARY = 2'b10;
      4 : CHAN_BOND_SEQ_LEN_BINARY = 2'b11;
      default : begin
        $display("Attribute Syntax Error : The Attribute CHAN_BOND_SEQ_LEN on X_GTPE2_CHANNEL instance %m is set to %d.  Legal values for this attribute are 1 to 4.", CHAN_BOND_SEQ_LEN, 1);
        #1 $finish;
      end
    endcase

    case (CLK_CORRECT_USE)
      "TRUE" : CLK_CORRECT_USE_BINARY = 1'b1;
      "FALSE" : CLK_CORRECT_USE_BINARY = 1'b0;
      default : begin
        $display("Attribute Syntax Error : The Attribute CLK_CORRECT_USE on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are TRUE, or FALSE.", CLK_CORRECT_USE);
        #1 $finish;
      end
    endcase

    case (CLK_COR_KEEP_IDLE)
      "FALSE" : CLK_COR_KEEP_IDLE_BINARY = 1'b0;
      "TRUE" : CLK_COR_KEEP_IDLE_BINARY = 1'b1;
      default : begin
        $display("Attribute Syntax Error : The Attribute CLK_COR_KEEP_IDLE on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are FALSE, or TRUE.", CLK_COR_KEEP_IDLE);
        #1 $finish;
      end
    endcase

    case (CLK_COR_PRECEDENCE)
      "TRUE" : CLK_COR_PRECEDENCE_BINARY = 1'b1;
      "FALSE" : CLK_COR_PRECEDENCE_BINARY = 1'b0;
      default : begin
        $display("Attribute Syntax Error : The Attribute CLK_COR_PRECEDENCE on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are TRUE, or FALSE.", CLK_COR_PRECEDENCE);
        #1 $finish;
      end
    endcase

    case (CLK_COR_SEQ_2_USE)
      "FALSE" : CLK_COR_SEQ_2_USE_BINARY = 1'b0;
      "TRUE" : CLK_COR_SEQ_2_USE_BINARY = 1'b1;
      default : begin
        $display("Attribute Syntax Error : The Attribute CLK_COR_SEQ_2_USE on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are FALSE, or TRUE.", CLK_COR_SEQ_2_USE);
        #1 $finish;
      end
    endcase

    case (CLK_COR_SEQ_LEN)
      1 : CLK_COR_SEQ_LEN_BINARY = 2'b00;
      2 : CLK_COR_SEQ_LEN_BINARY = 2'b01;
      3 : CLK_COR_SEQ_LEN_BINARY = 2'b10;
      4 : CLK_COR_SEQ_LEN_BINARY = 2'b11;
      default : begin
        $display("Attribute Syntax Error : The Attribute CLK_COR_SEQ_LEN on X_GTPE2_CHANNEL instance %m is set to %d.  Legal values for this attribute are 1 to 4.", CLK_COR_SEQ_LEN, 1);
        #1 $finish;
      end
    endcase

    case (DEC_MCOMMA_DETECT)
      "TRUE" : DEC_MCOMMA_DETECT_BINARY = 1'b1;
      "FALSE" : DEC_MCOMMA_DETECT_BINARY = 1'b0;
      default : begin
        $display("Attribute Syntax Error : The Attribute DEC_MCOMMA_DETECT on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are TRUE, or FALSE.", DEC_MCOMMA_DETECT);
        #1 $finish;
      end
    endcase

    case (DEC_PCOMMA_DETECT)
      "TRUE" : DEC_PCOMMA_DETECT_BINARY = 1'b1;
      "FALSE" : DEC_PCOMMA_DETECT_BINARY = 1'b0;
      default : begin
        $display("Attribute Syntax Error : The Attribute DEC_PCOMMA_DETECT on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are TRUE, or FALSE.", DEC_PCOMMA_DETECT);
        #1 $finish;
      end
    endcase

    case (DEC_VALID_COMMA_ONLY)
      "TRUE" : DEC_VALID_COMMA_ONLY_BINARY = 1'b1;
      "FALSE" : DEC_VALID_COMMA_ONLY_BINARY = 1'b0;
      default : begin
        $display("Attribute Syntax Error : The Attribute DEC_VALID_COMMA_ONLY on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are TRUE, or FALSE.", DEC_VALID_COMMA_ONLY);
        #1 $finish;
      end
    endcase

    case (ES_ERRDET_EN)
      "FALSE" : ES_ERRDET_EN_BINARY = 1'b0;
      "TRUE" : ES_ERRDET_EN_BINARY = 1'b1;
      default : begin
        $display("Attribute Syntax Error : The Attribute ES_ERRDET_EN on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are FALSE, or TRUE.", ES_ERRDET_EN);
        #1 $finish;
      end
    endcase

    case (ES_EYE_SCAN_EN)
      "FALSE" : ES_EYE_SCAN_EN_BINARY = 1'b0;
      "TRUE" : ES_EYE_SCAN_EN_BINARY = 1'b1;
      default : begin
        $display("Attribute Syntax Error : The Attribute ES_EYE_SCAN_EN on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are FALSE, or TRUE.", ES_EYE_SCAN_EN);
        #1 $finish;
      end
    endcase

    case (FTS_LANE_DESKEW_EN)
      "FALSE" : FTS_LANE_DESKEW_EN_BINARY = 1'b0;
      "TRUE" : FTS_LANE_DESKEW_EN_BINARY = 1'b1;
      default : begin
        $display("Attribute Syntax Error : The Attribute FTS_LANE_DESKEW_EN on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are FALSE, or TRUE.", FTS_LANE_DESKEW_EN);
        #1 $finish;
      end
    endcase

    case (PCS_PCIE_EN)
      "FALSE" : PCS_PCIE_EN_BINARY = 1'b0;
      "TRUE" : PCS_PCIE_EN_BINARY = 1'b1;
      default : begin
        $display("Attribute Syntax Error : The Attribute PCS_PCIE_EN on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are FALSE, or TRUE.", PCS_PCIE_EN);
        #1 $finish;
      end
    endcase

    case (RXBUF_ADDR_MODE)
      "FULL" : RXBUF_ADDR_MODE_BINARY = 1'b0;
      "FAST" : RXBUF_ADDR_MODE_BINARY = 1'b1;
      default : begin
        $display("Attribute Syntax Error : The Attribute RXBUF_ADDR_MODE on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are FULL, or FAST.", RXBUF_ADDR_MODE);
        #1 $finish;
      end
    endcase

    case (RXBUF_EN)
      "TRUE" : RXBUF_EN_BINARY = 1'b1;
      "FALSE" : RXBUF_EN_BINARY = 1'b0;
      default : begin
        $display("Attribute Syntax Error : The Attribute RXBUF_EN on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are TRUE, or FALSE.", RXBUF_EN);
        #1 $finish;
      end
    endcase

    case (RXBUF_RESET_ON_CB_CHANGE)
      "TRUE" : RXBUF_RESET_ON_CB_CHANGE_BINARY = 1'b1;
      "FALSE" : RXBUF_RESET_ON_CB_CHANGE_BINARY = 1'b0;
      default : begin
        $display("Attribute Syntax Error : The Attribute RXBUF_RESET_ON_CB_CHANGE on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are TRUE, or FALSE.", RXBUF_RESET_ON_CB_CHANGE);
        #1 $finish;
      end
    endcase

    case (RXBUF_RESET_ON_COMMAALIGN)
      "FALSE" : RXBUF_RESET_ON_COMMAALIGN_BINARY = 1'b0;
      "TRUE" : RXBUF_RESET_ON_COMMAALIGN_BINARY = 1'b1;
      default : begin
        $display("Attribute Syntax Error : The Attribute RXBUF_RESET_ON_COMMAALIGN on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are FALSE, or TRUE.", RXBUF_RESET_ON_COMMAALIGN);
        #1 $finish;
      end
    endcase

    case (RXBUF_RESET_ON_EIDLE)
      "FALSE" : RXBUF_RESET_ON_EIDLE_BINARY = 1'b0;
      "TRUE" : RXBUF_RESET_ON_EIDLE_BINARY = 1'b1;
      default : begin
        $display("Attribute Syntax Error : The Attribute RXBUF_RESET_ON_EIDLE on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are FALSE, or TRUE.", RXBUF_RESET_ON_EIDLE);
        #1 $finish;
      end
    endcase

    case (RXBUF_RESET_ON_RATE_CHANGE)
      "TRUE" : RXBUF_RESET_ON_RATE_CHANGE_BINARY = 1'b1;
      "FALSE" : RXBUF_RESET_ON_RATE_CHANGE_BINARY = 1'b0;
      default : begin
        $display("Attribute Syntax Error : The Attribute RXBUF_RESET_ON_RATE_CHANGE on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are TRUE, or FALSE.", RXBUF_RESET_ON_RATE_CHANGE);
        #1 $finish;
      end
    endcase

    case (RXBUF_THRESH_OVRD)
      "FALSE" : RXBUF_THRESH_OVRD_BINARY = 1'b0;
      "TRUE" : RXBUF_THRESH_OVRD_BINARY = 1'b1;
      default : begin
        $display("Attribute Syntax Error : The Attribute RXBUF_THRESH_OVRD on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are FALSE, or TRUE.", RXBUF_THRESH_OVRD);
        #1 $finish;
      end
    endcase

    case (RXGEARBOX_EN)
      "FALSE" : RXGEARBOX_EN_BINARY = 1'b0;
      "TRUE" : RXGEARBOX_EN_BINARY = 1'b1;
      default : begin
        $display("Attribute Syntax Error : The Attribute RXGEARBOX_EN on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are FALSE, or TRUE.", RXGEARBOX_EN);
        #1 $finish;
      end
    endcase

    case (RXOOB_CLK_CFG)
      "PMA" : RXOOB_CLK_CFG_BINARY = 1'b0;
      "FABRIC" : RXOOB_CLK_CFG_BINARY = 1'b1;
      default : begin
        $display("Attribute Syntax Error : The Attribute RXOOB_CLK_CFG on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are PMA, or FABRIC.", RXOOB_CLK_CFG);
        #1 $finish;
      end
    endcase

    case (RXOUT_DIV)
      2 : RXOUT_DIV_BINARY = 3'b001;
      1 : RXOUT_DIV_BINARY = 3'b000;
      4 : RXOUT_DIV_BINARY = 3'b010;
      8 : RXOUT_DIV_BINARY = 3'b011;
      16 : RXOUT_DIV_BINARY = 3'b100;
      default : begin
        $display("Attribute Syntax Error : The Attribute RXOUT_DIV on X_GTPE2_CHANNEL instance %m is set to %d.  Legal values for this attribute are 1 to 16.", RXOUT_DIV, 2);
        #1 $finish;
      end
    endcase

    case (RXSLIDE_MODE)
      "OFF" : RXSLIDE_MODE_BINARY = 2'b00;
      "AUTO" : RXSLIDE_MODE_BINARY = 2'b01;
      "PCS" : RXSLIDE_MODE_BINARY = 2'b10;
      "PMA" : RXSLIDE_MODE_BINARY = 2'b11;
      default : begin
        $display("Attribute Syntax Error : The Attribute RXSLIDE_MODE on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are OFF, AUTO, PCS, or PMA.", RXSLIDE_MODE);
        #1 $finish;
      end
    endcase

    case (RX_CLK25_DIV)
      7 : RX_CLK25_DIV_BINARY = 5'b00110;
      1 : RX_CLK25_DIV_BINARY = 5'b00000;
      2 : RX_CLK25_DIV_BINARY = 5'b00001;
      3 : RX_CLK25_DIV_BINARY = 5'b00010;
      4 : RX_CLK25_DIV_BINARY = 5'b00011;
      5 : RX_CLK25_DIV_BINARY = 5'b00100;
      6 : RX_CLK25_DIV_BINARY = 5'b00101;
      8 : RX_CLK25_DIV_BINARY = 5'b00111;
      9 : RX_CLK25_DIV_BINARY = 5'b01000;
      10 : RX_CLK25_DIV_BINARY = 5'b01001;
      11 : RX_CLK25_DIV_BINARY = 5'b01010;
      12 : RX_CLK25_DIV_BINARY = 5'b01011;
      13 : RX_CLK25_DIV_BINARY = 5'b01100;
      14 : RX_CLK25_DIV_BINARY = 5'b01101;
      15 : RX_CLK25_DIV_BINARY = 5'b01110;
      16 : RX_CLK25_DIV_BINARY = 5'b01111;
      17 : RX_CLK25_DIV_BINARY = 5'b10000;
      18 : RX_CLK25_DIV_BINARY = 5'b10001;
      19 : RX_CLK25_DIV_BINARY = 5'b10010;
      20 : RX_CLK25_DIV_BINARY = 5'b10011;
      21 : RX_CLK25_DIV_BINARY = 5'b10100;
      22 : RX_CLK25_DIV_BINARY = 5'b10101;
      23 : RX_CLK25_DIV_BINARY = 5'b10110;
      24 : RX_CLK25_DIV_BINARY = 5'b10111;
      25 : RX_CLK25_DIV_BINARY = 5'b11000;
      26 : RX_CLK25_DIV_BINARY = 5'b11001;
      27 : RX_CLK25_DIV_BINARY = 5'b11010;
      28 : RX_CLK25_DIV_BINARY = 5'b11011;
      29 : RX_CLK25_DIV_BINARY = 5'b11100;
      30 : RX_CLK25_DIV_BINARY = 5'b11101;
      31 : RX_CLK25_DIV_BINARY = 5'b11110;
      32 : RX_CLK25_DIV_BINARY = 5'b11111;
      default : begin
        $display("Attribute Syntax Error : The Attribute RX_CLK25_DIV on X_GTPE2_CHANNEL instance %m is set to %d.  Legal values for this attribute are 1 to 32.", RX_CLK25_DIV, 7);
        #1 $finish;
      end
    endcase

    case (RX_DATA_WIDTH)
      20 : RX_DATA_WIDTH_BINARY = 3'b011;
      16 : RX_DATA_WIDTH_BINARY = 3'b010;
      32 : RX_DATA_WIDTH_BINARY = 3'b100;
      40 : RX_DATA_WIDTH_BINARY = 3'b101;
      default : begin
        $display("Attribute Syntax Error : The Attribute RX_DATA_WIDTH on X_GTPE2_CHANNEL instance %m is set to %d.  Legal values for this attribute are 16 to 40.", RX_DATA_WIDTH, 20);
        #1 $finish;
      end
    endcase

    case (RX_DEFER_RESET_BUF_EN)
      "TRUE" : RX_DEFER_RESET_BUF_EN_BINARY = 1'b1;
      "FALSE" : RX_DEFER_RESET_BUF_EN_BINARY = 1'b0;
      default : begin
        $display("Attribute Syntax Error : The Attribute RX_DEFER_RESET_BUF_EN on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are TRUE, or FALSE.", RX_DEFER_RESET_BUF_EN);
        #1 $finish;
      end
    endcase

    case (RX_DISPERR_SEQ_MATCH)
      "TRUE" : RX_DISPERR_SEQ_MATCH_BINARY = 1'b1;
      "FALSE" : RX_DISPERR_SEQ_MATCH_BINARY = 1'b0;
      default : begin
        $display("Attribute Syntax Error : The Attribute RX_DISPERR_SEQ_MATCH on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are TRUE, or FALSE.", RX_DISPERR_SEQ_MATCH);
        #1 $finish;
      end
    endcase

    case (RX_SIG_VALID_DLY)
      10 : RX_SIG_VALID_DLY_BINARY = 5'b01001;
      1 : RX_SIG_VALID_DLY_BINARY = 5'b00000;
      2 : RX_SIG_VALID_DLY_BINARY = 5'b00001;
      3 : RX_SIG_VALID_DLY_BINARY = 5'b00010;
      4 : RX_SIG_VALID_DLY_BINARY = 5'b00011;
      5 : RX_SIG_VALID_DLY_BINARY = 5'b00100;
      6 : RX_SIG_VALID_DLY_BINARY = 5'b00101;
      7 : RX_SIG_VALID_DLY_BINARY = 5'b00110;
      8 : RX_SIG_VALID_DLY_BINARY = 5'b00111;
      9 : RX_SIG_VALID_DLY_BINARY = 5'b01000;
      11 : RX_SIG_VALID_DLY_BINARY = 5'b01010;
      12 : RX_SIG_VALID_DLY_BINARY = 5'b01011;
      13 : RX_SIG_VALID_DLY_BINARY = 5'b01100;
      14 : RX_SIG_VALID_DLY_BINARY = 5'b01101;
      15 : RX_SIG_VALID_DLY_BINARY = 5'b01110;
      16 : RX_SIG_VALID_DLY_BINARY = 5'b01111;
      17 : RX_SIG_VALID_DLY_BINARY = 5'b10000;
      18 : RX_SIG_VALID_DLY_BINARY = 5'b10001;
      19 : RX_SIG_VALID_DLY_BINARY = 5'b10010;
      20 : RX_SIG_VALID_DLY_BINARY = 5'b10011;
      21 : RX_SIG_VALID_DLY_BINARY = 5'b10100;
      22 : RX_SIG_VALID_DLY_BINARY = 5'b10101;
      23 : RX_SIG_VALID_DLY_BINARY = 5'b10110;
      24 : RX_SIG_VALID_DLY_BINARY = 5'b10111;
      25 : RX_SIG_VALID_DLY_BINARY = 5'b11000;
      26 : RX_SIG_VALID_DLY_BINARY = 5'b11001;
      27 : RX_SIG_VALID_DLY_BINARY = 5'b11010;
      28 : RX_SIG_VALID_DLY_BINARY = 5'b11011;
      29 : RX_SIG_VALID_DLY_BINARY = 5'b11100;
      30 : RX_SIG_VALID_DLY_BINARY = 5'b11101;
      31 : RX_SIG_VALID_DLY_BINARY = 5'b11110;
      32 : RX_SIG_VALID_DLY_BINARY = 5'b11111;
      default : begin
        $display("Attribute Syntax Error : The Attribute RX_SIG_VALID_DLY on X_GTPE2_CHANNEL instance %m is set to %d.  Legal values for this attribute are 1 to 32.", RX_SIG_VALID_DLY, 10);
        #1 $finish;
      end
    endcase

    case (RX_XCLK_SEL)
      "RXREC" : RX_XCLK_SEL_BINARY = 1'b0;
      "RXUSR" : RX_XCLK_SEL_BINARY = 1'b1;
      default : begin
        $display("Attribute Syntax Error : The Attribute RX_XCLK_SEL on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are RXREC, or RXUSR.", RX_XCLK_SEL);
        #1 $finish;
      end
    endcase

    case (SATA_PLL_CFG)
      "VCO_3000MHZ" : SATA_PLL_CFG_BINARY = 2'b00;
      "VCO_750MHZ" : SATA_PLL_CFG_BINARY = 2'b10;
      "VCO_1500MHZ" : SATA_PLL_CFG_BINARY = 2'b01;
      default : begin
        $display("Attribute Syntax Error : The Attribute SATA_PLL_CFG on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are VCO_3000MHZ, VCO_750MHZ, or VCO_1500MHZ.", SATA_PLL_CFG);
        #1 $finish;
      end
    endcase

    case (SHOW_REALIGN_COMMA)
      "TRUE" : SHOW_REALIGN_COMMA_BINARY = 1'b1;
      "FALSE" : SHOW_REALIGN_COMMA_BINARY = 1'b0;
      default : begin
        $display("Attribute Syntax Error : The Attribute SHOW_REALIGN_COMMA on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are TRUE, or FALSE.", SHOW_REALIGN_COMMA);
        #1 $finish;
      end
    endcase

    case (SIM_RECEIVER_DETECT_PASS)
      "TRUE" : SIM_RECEIVER_DETECT_PASS_BINARY = 0;
      "FALSE" : SIM_RECEIVER_DETECT_PASS_BINARY = 0;
      default : begin
        $display("Attribute Syntax Error : The Attribute SIM_RECEIVER_DETECT_PASS on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are TRUE, or FALSE.", SIM_RECEIVER_DETECT_PASS);
        #1 $finish;
      end
    endcase

    case (SIM_RESET_SPEEDUP)
      "TRUE" : SIM_RESET_SPEEDUP_BINARY = 0;
      "FALSE" : SIM_RESET_SPEEDUP_BINARY = 0;
      default : begin
        $display("Attribute Syntax Error : The Attribute SIM_RESET_SPEEDUP on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are TRUE, or FALSE.", SIM_RESET_SPEEDUP);
        #1 $finish;
      end
    endcase

    case (SIM_TX_EIDLE_DRIVE_LEVEL)
      "X" : SIM_TX_EIDLE_DRIVE_LEVEL_BINARY = 0;
      "0" : SIM_TX_EIDLE_DRIVE_LEVEL_BINARY = 0;
      "1" : SIM_TX_EIDLE_DRIVE_LEVEL_BINARY = 0;
      "Z" : SIM_TX_EIDLE_DRIVE_LEVEL_BINARY = 0;
      default : begin
        $display("Attribute Syntax Error : The Attribute SIM_TX_EIDLE_DRIVE_LEVEL on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are X, 0, 1, or Z.", SIM_TX_EIDLE_DRIVE_LEVEL);
        #1 $finish;
      end
    endcase

    case (SIM_VERSION)
      "1.0" : SIM_VERSION_BINARY = 0;
      "1.1" : SIM_VERSION_BINARY = 0;
      "2.0" : SIM_VERSION_BINARY = 0;
      default : begin
        $display("Attribute Syntax Error : The Attribute SIM_VERSION on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are 1.0, 1.1, or 2.0.", SIM_VERSION);
        #1 $finish;
      end
    endcase

    case (TXBUF_EN)
      "TRUE" : TXBUF_EN_BINARY = 1'b1;
      "FALSE" : TXBUF_EN_BINARY = 1'b0;
      default : begin
        $display("Attribute Syntax Error : The Attribute TXBUF_EN on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are TRUE, or FALSE.", TXBUF_EN);
        #1 $finish;
      end
    endcase

    case (TXBUF_RESET_ON_RATE_CHANGE)
      "FALSE" : TXBUF_RESET_ON_RATE_CHANGE_BINARY = 1'b0;
      "TRUE" : TXBUF_RESET_ON_RATE_CHANGE_BINARY = 1'b1;
      default : begin
        $display("Attribute Syntax Error : The Attribute TXBUF_RESET_ON_RATE_CHANGE on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are FALSE, or TRUE.", TXBUF_RESET_ON_RATE_CHANGE);
        #1 $finish;
      end
    endcase

    case (TXGEARBOX_EN)
      "FALSE" : TXGEARBOX_EN_BINARY = 1'b0;
      "TRUE" : TXGEARBOX_EN_BINARY = 1'b1;
      default : begin
        $display("Attribute Syntax Error : The Attribute TXGEARBOX_EN on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are FALSE, or TRUE.", TXGEARBOX_EN);
        #1 $finish;
      end
    endcase

    case (TXOUT_DIV)
      2 : TXOUT_DIV_BINARY = 3'b001;
      1 : TXOUT_DIV_BINARY = 3'b000;
      4 : TXOUT_DIV_BINARY = 3'b010;
      8 : TXOUT_DIV_BINARY = 3'b011;
      16 : TXOUT_DIV_BINARY = 3'b100;
      default : begin
        $display("Attribute Syntax Error : The Attribute TXOUT_DIV on X_GTPE2_CHANNEL instance %m is set to %d.  Legal values for this attribute are 1 to 16.", TXOUT_DIV, 2);
        #1 $finish;
      end
    endcase

    case (TXPI_PPMCLK_SEL)
      "TXUSRCLK2" : TXPI_PPMCLK_SEL_BINARY = 1'b1;
      "TXUSRCLK" : TXPI_PPMCLK_SEL_BINARY = 1'b0;
      default : begin
        $display("Attribute Syntax Error : The Attribute TXPI_PPMCLK_SEL on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are TXUSRCLK2, or TXUSRCLK.", TXPI_PPMCLK_SEL);
        #1 $finish;
      end
    endcase

    case (TX_CLK25_DIV)
      7 : TX_CLK25_DIV_BINARY = 5'b00110;
      1 : TX_CLK25_DIV_BINARY = 5'b00000;
      2 : TX_CLK25_DIV_BINARY = 5'b00001;
      3 : TX_CLK25_DIV_BINARY = 5'b00010;
      4 : TX_CLK25_DIV_BINARY = 5'b00011;
      5 : TX_CLK25_DIV_BINARY = 5'b00100;
      6 : TX_CLK25_DIV_BINARY = 5'b00101;
      8 : TX_CLK25_DIV_BINARY = 5'b00111;
      9 : TX_CLK25_DIV_BINARY = 5'b01000;
      10 : TX_CLK25_DIV_BINARY = 5'b01001;
      11 : TX_CLK25_DIV_BINARY = 5'b01010;
      12 : TX_CLK25_DIV_BINARY = 5'b01011;
      13 : TX_CLK25_DIV_BINARY = 5'b01100;
      14 : TX_CLK25_DIV_BINARY = 5'b01101;
      15 : TX_CLK25_DIV_BINARY = 5'b01110;
      16 : TX_CLK25_DIV_BINARY = 5'b01111;
      17 : TX_CLK25_DIV_BINARY = 5'b10000;
      18 : TX_CLK25_DIV_BINARY = 5'b10001;
      19 : TX_CLK25_DIV_BINARY = 5'b10010;
      20 : TX_CLK25_DIV_BINARY = 5'b10011;
      21 : TX_CLK25_DIV_BINARY = 5'b10100;
      22 : TX_CLK25_DIV_BINARY = 5'b10101;
      23 : TX_CLK25_DIV_BINARY = 5'b10110;
      24 : TX_CLK25_DIV_BINARY = 5'b10111;
      25 : TX_CLK25_DIV_BINARY = 5'b11000;
      26 : TX_CLK25_DIV_BINARY = 5'b11001;
      27 : TX_CLK25_DIV_BINARY = 5'b11010;
      28 : TX_CLK25_DIV_BINARY = 5'b11011;
      29 : TX_CLK25_DIV_BINARY = 5'b11100;
      30 : TX_CLK25_DIV_BINARY = 5'b11101;
      31 : TX_CLK25_DIV_BINARY = 5'b11110;
      32 : TX_CLK25_DIV_BINARY = 5'b11111;
      default : begin
        $display("Attribute Syntax Error : The Attribute TX_CLK25_DIV on X_GTPE2_CHANNEL instance %m is set to %d.  Legal values for this attribute are 1 to 32.", TX_CLK25_DIV, 7);
        #1 $finish;
      end
    endcase

    case (TX_DATA_WIDTH)
      20 : TX_DATA_WIDTH_BINARY = 3'b011;
      16 : TX_DATA_WIDTH_BINARY = 3'b010;
      32 : TX_DATA_WIDTH_BINARY = 3'b100;
      40 : TX_DATA_WIDTH_BINARY = 3'b101;
      default : begin
        $display("Attribute Syntax Error : The Attribute TX_DATA_WIDTH on X_GTPE2_CHANNEL instance %m is set to %d.  Legal values for this attribute are 16 to 40.", TX_DATA_WIDTH, 20);
        #1 $finish;
      end
    endcase

    case (TX_DRIVE_MODE)
      "DIRECT" : TX_DRIVE_MODE_BINARY = 5'b00000;
      "PIPE" : TX_DRIVE_MODE_BINARY = 5'b00001;
      "PIPEGEN3" : TX_DRIVE_MODE_BINARY = 5'b00010;
      default : begin
        $display("Attribute Syntax Error : The Attribute TX_DRIVE_MODE on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are DIRECT, PIPE, or PIPEGEN3.", TX_DRIVE_MODE);
        #1 $finish;
      end
    endcase

    case (TX_LOOPBACK_DRIVE_HIZ)
      "FALSE" : TX_LOOPBACK_DRIVE_HIZ_BINARY = 1'b0;
      "TRUE" : TX_LOOPBACK_DRIVE_HIZ_BINARY = 1'b1;
      default : begin
        $display("Attribute Syntax Error : The Attribute TX_LOOPBACK_DRIVE_HIZ on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are FALSE, or TRUE.", TX_LOOPBACK_DRIVE_HIZ);
        #1 $finish;
      end
    endcase

    case (TX_XCLK_SEL)
      "TXUSR" : TX_XCLK_SEL_BINARY = 1'b1;
      "TXOUT" : TX_XCLK_SEL_BINARY = 1'b0;
      default : begin
        $display("Attribute Syntax Error : The Attribute TX_XCLK_SEL on X_GTPE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are TXUSR, or TXOUT.", TX_XCLK_SEL);
        #1 $finish;
      end
    endcase

    if ((ACJTAG_DEBUG_MODE >= 1'b0) && (ACJTAG_DEBUG_MODE <= 1'b1))
      ACJTAG_DEBUG_MODE_BINARY = ACJTAG_DEBUG_MODE;
    else begin
      $display("Attribute Syntax Error : The Attribute ACJTAG_DEBUG_MODE on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", ACJTAG_DEBUG_MODE);
      #1 $finish;
    end

    if ((ACJTAG_MODE >= 1'b0) && (ACJTAG_MODE <= 1'b1))
      ACJTAG_MODE_BINARY = ACJTAG_MODE;
    else begin
      $display("Attribute Syntax Error : The Attribute ACJTAG_MODE on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", ACJTAG_MODE);
      #1 $finish;
    end

    if ((ACJTAG_RESET >= 1'b0) && (ACJTAG_RESET <= 1'b1))
      ACJTAG_RESET_BINARY = ACJTAG_RESET;
    else begin
      $display("Attribute Syntax Error : The Attribute ACJTAG_RESET on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", ACJTAG_RESET);
      #1 $finish;
    end

    if ((ADAPT_CFG0 >= 20'b00000000000000000000) && (ADAPT_CFG0 <= 20'b11111111111111111111))
      ADAPT_CFG0_BINARY = ADAPT_CFG0;
    else begin
      $display("Attribute Syntax Error : The Attribute ADAPT_CFG0 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 20'b00000000000000000000 to 20'b11111111111111111111.", ADAPT_CFG0);
      #1 $finish;
    end

    if ((ALIGN_COMMA_ENABLE >= 10'b0000000000) && (ALIGN_COMMA_ENABLE <= 10'b1111111111))
      ALIGN_COMMA_ENABLE_BINARY = ALIGN_COMMA_ENABLE;
    else begin
      $display("Attribute Syntax Error : The Attribute ALIGN_COMMA_ENABLE on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 10'b0000000000 to 10'b1111111111.", ALIGN_COMMA_ENABLE);
      #1 $finish;
    end

    if ((ALIGN_COMMA_WORD >= 1) && (ALIGN_COMMA_WORD <= 2))
      ALIGN_COMMA_WORD_BINARY = ALIGN_COMMA_WORD;
    else begin
      $display("Attribute Syntax Error : The Attribute ALIGN_COMMA_WORD on X_GTPE2_CHANNEL instance %m is set to %d.  Legal values for this attribute are  1 to 2.", ALIGN_COMMA_WORD);
      #1 $finish;
    end

    if ((ALIGN_MCOMMA_VALUE >= 10'b0000000000) && (ALIGN_MCOMMA_VALUE <= 10'b1111111111))
      ALIGN_MCOMMA_VALUE_BINARY = ALIGN_MCOMMA_VALUE;
    else begin
      $display("Attribute Syntax Error : The Attribute ALIGN_MCOMMA_VALUE on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 10'b0000000000 to 10'b1111111111.", ALIGN_MCOMMA_VALUE);
      #1 $finish;
    end

    if ((ALIGN_PCOMMA_VALUE >= 10'b0000000000) && (ALIGN_PCOMMA_VALUE <= 10'b1111111111))
      ALIGN_PCOMMA_VALUE_BINARY = ALIGN_PCOMMA_VALUE;
    else begin
      $display("Attribute Syntax Error : The Attribute ALIGN_PCOMMA_VALUE on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 10'b0000000000 to 10'b1111111111.", ALIGN_PCOMMA_VALUE);
      #1 $finish;
    end

    if ((CFOK_CFG >= 43'b0000000000000000000000000000000000000000000) && (CFOK_CFG <= 43'b1111111111111111111111111111111111111111111))
      CFOK_CFG_BINARY = CFOK_CFG;
    else begin
      $display("Attribute Syntax Error : The Attribute CFOK_CFG on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 43'b0000000000000000000000000000000000000000000 to 43'b1111111111111111111111111111111111111111111.", CFOK_CFG);
      #1 $finish;
    end

    if ((CFOK_CFG2 >= 7'b0000000) && (CFOK_CFG2 <= 7'b1111111))
      CFOK_CFG2_BINARY = CFOK_CFG2;
    else begin
      $display("Attribute Syntax Error : The Attribute CFOK_CFG2 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 7'b0000000 to 7'b1111111.", CFOK_CFG2);
      #1 $finish;
    end

    if ((CFOK_CFG3 >= 7'b0000000) && (CFOK_CFG3 <= 7'b1111111))
      CFOK_CFG3_BINARY = CFOK_CFG3;
    else begin
      $display("Attribute Syntax Error : The Attribute CFOK_CFG3 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 7'b0000000 to 7'b1111111.", CFOK_CFG3);
      #1 $finish;
    end

    if ((CFOK_CFG4 >= 1'b0) && (CFOK_CFG4 <= 1'b1))
      CFOK_CFG4_BINARY = CFOK_CFG4;
    else begin
      $display("Attribute Syntax Error : The Attribute CFOK_CFG4 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", CFOK_CFG4);
      #1 $finish;
    end

    if ((CFOK_CFG5 >= 2'b00) && (CFOK_CFG5 <= 2'b11))
      CFOK_CFG5_BINARY = CFOK_CFG5;
    else begin
      $display("Attribute Syntax Error : The Attribute CFOK_CFG5 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 2'b00 to 2'b11.", CFOK_CFG5);
      #1 $finish;
    end

    if ((CFOK_CFG6 >= 4'b0000) && (CFOK_CFG6 <= 4'b1111))
      CFOK_CFG6_BINARY = CFOK_CFG6;
    else begin
      $display("Attribute Syntax Error : The Attribute CFOK_CFG6 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 4'b0000 to 4'b1111.", CFOK_CFG6);
      #1 $finish;
    end

    if ((CHAN_BOND_MAX_SKEW >= 1) && (CHAN_BOND_MAX_SKEW <= 14))
      CHAN_BOND_MAX_SKEW_BINARY = CHAN_BOND_MAX_SKEW;
    else begin
      $display("Attribute Syntax Error : The Attribute CHAN_BOND_MAX_SKEW on X_GTPE2_CHANNEL instance %m is set to %d.  Legal values for this attribute are  1 to 14.", CHAN_BOND_MAX_SKEW);
      #1 $finish;
    end

    if ((CHAN_BOND_SEQ_1_1 >= 10'b0000000000) && (CHAN_BOND_SEQ_1_1 <= 10'b1111111111))
      CHAN_BOND_SEQ_1_1_BINARY = CHAN_BOND_SEQ_1_1;
    else begin
      $display("Attribute Syntax Error : The Attribute CHAN_BOND_SEQ_1_1 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 10'b0000000000 to 10'b1111111111.", CHAN_BOND_SEQ_1_1);
      #1 $finish;
    end

    if ((CHAN_BOND_SEQ_1_2 >= 10'b0000000000) && (CHAN_BOND_SEQ_1_2 <= 10'b1111111111))
      CHAN_BOND_SEQ_1_2_BINARY = CHAN_BOND_SEQ_1_2;
    else begin
      $display("Attribute Syntax Error : The Attribute CHAN_BOND_SEQ_1_2 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 10'b0000000000 to 10'b1111111111.", CHAN_BOND_SEQ_1_2);
      #1 $finish;
    end

    if ((CHAN_BOND_SEQ_1_3 >= 10'b0000000000) && (CHAN_BOND_SEQ_1_3 <= 10'b1111111111))
      CHAN_BOND_SEQ_1_3_BINARY = CHAN_BOND_SEQ_1_3;
    else begin
      $display("Attribute Syntax Error : The Attribute CHAN_BOND_SEQ_1_3 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 10'b0000000000 to 10'b1111111111.", CHAN_BOND_SEQ_1_3);
      #1 $finish;
    end

    if ((CHAN_BOND_SEQ_1_4 >= 10'b0000000000) && (CHAN_BOND_SEQ_1_4 <= 10'b1111111111))
      CHAN_BOND_SEQ_1_4_BINARY = CHAN_BOND_SEQ_1_4;
    else begin
      $display("Attribute Syntax Error : The Attribute CHAN_BOND_SEQ_1_4 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 10'b0000000000 to 10'b1111111111.", CHAN_BOND_SEQ_1_4);
      #1 $finish;
    end

    if ((CHAN_BOND_SEQ_1_ENABLE >= 4'b0000) && (CHAN_BOND_SEQ_1_ENABLE <= 4'b1111))
      CHAN_BOND_SEQ_1_ENABLE_BINARY = CHAN_BOND_SEQ_1_ENABLE;
    else begin
      $display("Attribute Syntax Error : The Attribute CHAN_BOND_SEQ_1_ENABLE on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 4'b0000 to 4'b1111.", CHAN_BOND_SEQ_1_ENABLE);
      #1 $finish;
    end

    if ((CHAN_BOND_SEQ_2_1 >= 10'b0000000000) && (CHAN_BOND_SEQ_2_1 <= 10'b1111111111))
      CHAN_BOND_SEQ_2_1_BINARY = CHAN_BOND_SEQ_2_1;
    else begin
      $display("Attribute Syntax Error : The Attribute CHAN_BOND_SEQ_2_1 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 10'b0000000000 to 10'b1111111111.", CHAN_BOND_SEQ_2_1);
      #1 $finish;
    end

    if ((CHAN_BOND_SEQ_2_2 >= 10'b0000000000) && (CHAN_BOND_SEQ_2_2 <= 10'b1111111111))
      CHAN_BOND_SEQ_2_2_BINARY = CHAN_BOND_SEQ_2_2;
    else begin
      $display("Attribute Syntax Error : The Attribute CHAN_BOND_SEQ_2_2 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 10'b0000000000 to 10'b1111111111.", CHAN_BOND_SEQ_2_2);
      #1 $finish;
    end

    if ((CHAN_BOND_SEQ_2_3 >= 10'b0000000000) && (CHAN_BOND_SEQ_2_3 <= 10'b1111111111))
      CHAN_BOND_SEQ_2_3_BINARY = CHAN_BOND_SEQ_2_3;
    else begin
      $display("Attribute Syntax Error : The Attribute CHAN_BOND_SEQ_2_3 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 10'b0000000000 to 10'b1111111111.", CHAN_BOND_SEQ_2_3);
      #1 $finish;
    end

    if ((CHAN_BOND_SEQ_2_4 >= 10'b0000000000) && (CHAN_BOND_SEQ_2_4 <= 10'b1111111111))
      CHAN_BOND_SEQ_2_4_BINARY = CHAN_BOND_SEQ_2_4;
    else begin
      $display("Attribute Syntax Error : The Attribute CHAN_BOND_SEQ_2_4 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 10'b0000000000 to 10'b1111111111.", CHAN_BOND_SEQ_2_4);
      #1 $finish;
    end

    if ((CHAN_BOND_SEQ_2_ENABLE >= 4'b0000) && (CHAN_BOND_SEQ_2_ENABLE <= 4'b1111))
      CHAN_BOND_SEQ_2_ENABLE_BINARY = CHAN_BOND_SEQ_2_ENABLE;
    else begin
      $display("Attribute Syntax Error : The Attribute CHAN_BOND_SEQ_2_ENABLE on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 4'b0000 to 4'b1111.", CHAN_BOND_SEQ_2_ENABLE);
      #1 $finish;
    end

    if ((CLK_COMMON_SWING >= 1'b0) && (CLK_COMMON_SWING <= 1'b1))
      CLK_COMMON_SWING_BINARY = CLK_COMMON_SWING;
    else begin
      $display("Attribute Syntax Error : The Attribute CLK_COMMON_SWING on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", CLK_COMMON_SWING);
      #1 $finish;
    end

    if ((CLK_COR_MAX_LAT >= 3) && (CLK_COR_MAX_LAT <= 60))
      CLK_COR_MAX_LAT_BINARY = CLK_COR_MAX_LAT;
    else begin
      $display("Attribute Syntax Error : The Attribute CLK_COR_MAX_LAT on X_GTPE2_CHANNEL instance %m is set to %d.  Legal values for this attribute are  3 to 60.", CLK_COR_MAX_LAT);
      #1 $finish;
    end

    if ((CLK_COR_MIN_LAT >= 3) && (CLK_COR_MIN_LAT <= 60))
      CLK_COR_MIN_LAT_BINARY = CLK_COR_MIN_LAT;
    else begin
      $display("Attribute Syntax Error : The Attribute CLK_COR_MIN_LAT on X_GTPE2_CHANNEL instance %m is set to %d.  Legal values for this attribute are  3 to 60.", CLK_COR_MIN_LAT);
      #1 $finish;
    end

    if ((CLK_COR_REPEAT_WAIT >= 0) && (CLK_COR_REPEAT_WAIT <= 31))
      CLK_COR_REPEAT_WAIT_BINARY = CLK_COR_REPEAT_WAIT;
    else begin
      $display("Attribute Syntax Error : The Attribute CLK_COR_REPEAT_WAIT on X_GTPE2_CHANNEL instance %m is set to %d.  Legal values for this attribute are  0 to 31.", CLK_COR_REPEAT_WAIT);
      #1 $finish;
    end

    if ((CLK_COR_SEQ_1_1 >= 10'b0000000000) && (CLK_COR_SEQ_1_1 <= 10'b1111111111))
      CLK_COR_SEQ_1_1_BINARY = CLK_COR_SEQ_1_1;
    else begin
      $display("Attribute Syntax Error : The Attribute CLK_COR_SEQ_1_1 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 10'b0000000000 to 10'b1111111111.", CLK_COR_SEQ_1_1);
      #1 $finish;
    end

    if ((CLK_COR_SEQ_1_2 >= 10'b0000000000) && (CLK_COR_SEQ_1_2 <= 10'b1111111111))
      CLK_COR_SEQ_1_2_BINARY = CLK_COR_SEQ_1_2;
    else begin
      $display("Attribute Syntax Error : The Attribute CLK_COR_SEQ_1_2 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 10'b0000000000 to 10'b1111111111.", CLK_COR_SEQ_1_2);
      #1 $finish;
    end

    if ((CLK_COR_SEQ_1_3 >= 10'b0000000000) && (CLK_COR_SEQ_1_3 <= 10'b1111111111))
      CLK_COR_SEQ_1_3_BINARY = CLK_COR_SEQ_1_3;
    else begin
      $display("Attribute Syntax Error : The Attribute CLK_COR_SEQ_1_3 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 10'b0000000000 to 10'b1111111111.", CLK_COR_SEQ_1_3);
      #1 $finish;
    end

    if ((CLK_COR_SEQ_1_4 >= 10'b0000000000) && (CLK_COR_SEQ_1_4 <= 10'b1111111111))
      CLK_COR_SEQ_1_4_BINARY = CLK_COR_SEQ_1_4;
    else begin
      $display("Attribute Syntax Error : The Attribute CLK_COR_SEQ_1_4 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 10'b0000000000 to 10'b1111111111.", CLK_COR_SEQ_1_4);
      #1 $finish;
    end

    if ((CLK_COR_SEQ_1_ENABLE >= 4'b0000) && (CLK_COR_SEQ_1_ENABLE <= 4'b1111))
      CLK_COR_SEQ_1_ENABLE_BINARY = CLK_COR_SEQ_1_ENABLE;
    else begin
      $display("Attribute Syntax Error : The Attribute CLK_COR_SEQ_1_ENABLE on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 4'b0000 to 4'b1111.", CLK_COR_SEQ_1_ENABLE);
      #1 $finish;
    end

    if ((CLK_COR_SEQ_2_1 >= 10'b0000000000) && (CLK_COR_SEQ_2_1 <= 10'b1111111111))
      CLK_COR_SEQ_2_1_BINARY = CLK_COR_SEQ_2_1;
    else begin
      $display("Attribute Syntax Error : The Attribute CLK_COR_SEQ_2_1 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 10'b0000000000 to 10'b1111111111.", CLK_COR_SEQ_2_1);
      #1 $finish;
    end

    if ((CLK_COR_SEQ_2_2 >= 10'b0000000000) && (CLK_COR_SEQ_2_2 <= 10'b1111111111))
      CLK_COR_SEQ_2_2_BINARY = CLK_COR_SEQ_2_2;
    else begin
      $display("Attribute Syntax Error : The Attribute CLK_COR_SEQ_2_2 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 10'b0000000000 to 10'b1111111111.", CLK_COR_SEQ_2_2);
      #1 $finish;
    end

    if ((CLK_COR_SEQ_2_3 >= 10'b0000000000) && (CLK_COR_SEQ_2_3 <= 10'b1111111111))
      CLK_COR_SEQ_2_3_BINARY = CLK_COR_SEQ_2_3;
    else begin
      $display("Attribute Syntax Error : The Attribute CLK_COR_SEQ_2_3 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 10'b0000000000 to 10'b1111111111.", CLK_COR_SEQ_2_3);
      #1 $finish;
    end

    if ((CLK_COR_SEQ_2_4 >= 10'b0000000000) && (CLK_COR_SEQ_2_4 <= 10'b1111111111))
      CLK_COR_SEQ_2_4_BINARY = CLK_COR_SEQ_2_4;
    else begin
      $display("Attribute Syntax Error : The Attribute CLK_COR_SEQ_2_4 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 10'b0000000000 to 10'b1111111111.", CLK_COR_SEQ_2_4);
      #1 $finish;
    end

    if ((CLK_COR_SEQ_2_ENABLE >= 4'b0000) && (CLK_COR_SEQ_2_ENABLE <= 4'b1111))
      CLK_COR_SEQ_2_ENABLE_BINARY = CLK_COR_SEQ_2_ENABLE;
    else begin
      $display("Attribute Syntax Error : The Attribute CLK_COR_SEQ_2_ENABLE on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 4'b0000 to 4'b1111.", CLK_COR_SEQ_2_ENABLE);
      #1 $finish;
    end

    if ((ES_CLK_PHASE_SEL >= 1'b0) && (ES_CLK_PHASE_SEL <= 1'b1))
      ES_CLK_PHASE_SEL_BINARY = ES_CLK_PHASE_SEL;
    else begin
      $display("Attribute Syntax Error : The Attribute ES_CLK_PHASE_SEL on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", ES_CLK_PHASE_SEL);
      #1 $finish;
    end

    if ((ES_CONTROL >= 6'b000000) && (ES_CONTROL <= 6'b111111))
      ES_CONTROL_BINARY = ES_CONTROL;
    else begin
      $display("Attribute Syntax Error : The Attribute ES_CONTROL on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 6'b000000 to 6'b111111.", ES_CONTROL);
      #1 $finish;
    end

    if ((ES_PMA_CFG >= 10'b0000000000) && (ES_PMA_CFG <= 10'b1111111111))
      ES_PMA_CFG_BINARY = ES_PMA_CFG;
    else begin
      $display("Attribute Syntax Error : The Attribute ES_PMA_CFG on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 10'b0000000000 to 10'b1111111111.", ES_PMA_CFG);
      #1 $finish;
    end

    if ((ES_PRESCALE >= 5'b00000) && (ES_PRESCALE <= 5'b11111))
      ES_PRESCALE_BINARY = ES_PRESCALE;
    else begin
      $display("Attribute Syntax Error : The Attribute ES_PRESCALE on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 5'b00000 to 5'b11111.", ES_PRESCALE);
      #1 $finish;
    end

    if ((ES_VERT_OFFSET >= 9'b000000000) && (ES_VERT_OFFSET <= 9'b111111111))
      ES_VERT_OFFSET_BINARY = ES_VERT_OFFSET;
    else begin
      $display("Attribute Syntax Error : The Attribute ES_VERT_OFFSET on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 9'b000000000 to 9'b111111111.", ES_VERT_OFFSET);
      #1 $finish;
    end

    if ((FTS_DESKEW_SEQ_ENABLE >= 4'b0000) && (FTS_DESKEW_SEQ_ENABLE <= 4'b1111))
      FTS_DESKEW_SEQ_ENABLE_BINARY = FTS_DESKEW_SEQ_ENABLE;
    else begin
      $display("Attribute Syntax Error : The Attribute FTS_DESKEW_SEQ_ENABLE on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 4'b0000 to 4'b1111.", FTS_DESKEW_SEQ_ENABLE);
      #1 $finish;
    end

    if ((FTS_LANE_DESKEW_CFG >= 4'b0000) && (FTS_LANE_DESKEW_CFG <= 4'b1111))
      FTS_LANE_DESKEW_CFG_BINARY = FTS_LANE_DESKEW_CFG;
    else begin
      $display("Attribute Syntax Error : The Attribute FTS_LANE_DESKEW_CFG on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 4'b0000 to 4'b1111.", FTS_LANE_DESKEW_CFG);
      #1 $finish;
    end

    if ((GEARBOX_MODE >= 3'b000) && (GEARBOX_MODE <= 3'b111))
      GEARBOX_MODE_BINARY = GEARBOX_MODE;
    else begin
      $display("Attribute Syntax Error : The Attribute GEARBOX_MODE on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 3'b000 to 3'b111.", GEARBOX_MODE);
      #1 $finish;
    end

    if ((LOOPBACK_CFG >= 1'b0) && (LOOPBACK_CFG <= 1'b1))
      LOOPBACK_CFG_BINARY = LOOPBACK_CFG;
    else begin
      $display("Attribute Syntax Error : The Attribute LOOPBACK_CFG on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", LOOPBACK_CFG);
      #1 $finish;
    end

    if ((OUTREFCLK_SEL_INV >= 2'b00) && (OUTREFCLK_SEL_INV <= 2'b11))
      OUTREFCLK_SEL_INV_BINARY = OUTREFCLK_SEL_INV;
    else begin
      $display("Attribute Syntax Error : The Attribute OUTREFCLK_SEL_INV on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 2'b00 to 2'b11.", OUTREFCLK_SEL_INV);
      #1 $finish;
    end

    if ((PMA_LOOPBACK_CFG >= 1'b0) && (PMA_LOOPBACK_CFG <= 1'b1))
      PMA_LOOPBACK_CFG_BINARY = PMA_LOOPBACK_CFG;
    else begin
      $display("Attribute Syntax Error : The Attribute PMA_LOOPBACK_CFG on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", PMA_LOOPBACK_CFG);
      #1 $finish;
    end

    if ((PMA_RSV3 >= 2'b00) && (PMA_RSV3 <= 2'b11))
      PMA_RSV3_BINARY = PMA_RSV3;
    else begin
      $display("Attribute Syntax Error : The Attribute PMA_RSV3 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 2'b00 to 2'b11.", PMA_RSV3);
      #1 $finish;
    end

    if ((PMA_RSV4 >= 4'b0000) && (PMA_RSV4 <= 4'b1111))
      PMA_RSV4_BINARY = PMA_RSV4;
    else begin
      $display("Attribute Syntax Error : The Attribute PMA_RSV4 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 4'b0000 to 4'b1111.", PMA_RSV4);
      #1 $finish;
    end

    if ((PMA_RSV5 >= 1'b0) && (PMA_RSV5 <= 1'b1))
      PMA_RSV5_BINARY = PMA_RSV5;
    else begin
      $display("Attribute Syntax Error : The Attribute PMA_RSV5 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", PMA_RSV5);
      #1 $finish;
    end

    if ((PMA_RSV6 >= 1'b0) && (PMA_RSV6 <= 1'b1))
      PMA_RSV6_BINARY = PMA_RSV6;
    else begin
      $display("Attribute Syntax Error : The Attribute PMA_RSV6 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", PMA_RSV6);
      #1 $finish;
    end

    if ((PMA_RSV7 >= 1'b0) && (PMA_RSV7 <= 1'b1))
      PMA_RSV7_BINARY = PMA_RSV7;
    else begin
      $display("Attribute Syntax Error : The Attribute PMA_RSV7 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", PMA_RSV7);
      #1 $finish;
    end

    if ((RXBUFRESET_TIME >= 5'b00000) && (RXBUFRESET_TIME <= 5'b11111))
      RXBUFRESET_TIME_BINARY = RXBUFRESET_TIME;
    else begin
      $display("Attribute Syntax Error : The Attribute RXBUFRESET_TIME on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 5'b00000 to 5'b11111.", RXBUFRESET_TIME);
      #1 $finish;
    end

    if ((RXBUF_EIDLE_HI_CNT >= 4'b0000) && (RXBUF_EIDLE_HI_CNT <= 4'b1111))
      RXBUF_EIDLE_HI_CNT_BINARY = RXBUF_EIDLE_HI_CNT;
    else begin
      $display("Attribute Syntax Error : The Attribute RXBUF_EIDLE_HI_CNT on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 4'b0000 to 4'b1111.", RXBUF_EIDLE_HI_CNT);
      #1 $finish;
    end

    if ((RXBUF_EIDLE_LO_CNT >= 4'b0000) && (RXBUF_EIDLE_LO_CNT <= 4'b1111))
      RXBUF_EIDLE_LO_CNT_BINARY = RXBUF_EIDLE_LO_CNT;
    else begin
      $display("Attribute Syntax Error : The Attribute RXBUF_EIDLE_LO_CNT on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 4'b0000 to 4'b1111.", RXBUF_EIDLE_LO_CNT);
      #1 $finish;
    end

    if ((RXBUF_THRESH_OVFLW >= 0) && (RXBUF_THRESH_OVFLW <= 63))
      RXBUF_THRESH_OVFLW_BINARY = RXBUF_THRESH_OVFLW;
    else begin
      $display("Attribute Syntax Error : The Attribute RXBUF_THRESH_OVFLW on X_GTPE2_CHANNEL instance %m is set to %d.  Legal values for this attribute are  0 to 63.", RXBUF_THRESH_OVFLW);
      #1 $finish;
    end

    if ((RXBUF_THRESH_UNDFLW >= 0) && (RXBUF_THRESH_UNDFLW <= 63))
      RXBUF_THRESH_UNDFLW_BINARY = RXBUF_THRESH_UNDFLW;
    else begin
      $display("Attribute Syntax Error : The Attribute RXBUF_THRESH_UNDFLW on X_GTPE2_CHANNEL instance %m is set to %d.  Legal values for this attribute are  0 to 63.", RXBUF_THRESH_UNDFLW);
      #1 $finish;
    end

    if ((RXCDRFREQRESET_TIME >= 5'b00000) && (RXCDRFREQRESET_TIME <= 5'b11111))
      RXCDRFREQRESET_TIME_BINARY = RXCDRFREQRESET_TIME;
    else begin
      $display("Attribute Syntax Error : The Attribute RXCDRFREQRESET_TIME on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 5'b00000 to 5'b11111.", RXCDRFREQRESET_TIME);
      #1 $finish;
    end

    if ((RXCDRPHRESET_TIME >= 5'b00000) && (RXCDRPHRESET_TIME <= 5'b11111))
      RXCDRPHRESET_TIME_BINARY = RXCDRPHRESET_TIME;
    else begin
      $display("Attribute Syntax Error : The Attribute RXCDRPHRESET_TIME on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 5'b00000 to 5'b11111.", RXCDRPHRESET_TIME);
      #1 $finish;
    end

    if ((RXCDR_FR_RESET_ON_EIDLE >= 1'b0) && (RXCDR_FR_RESET_ON_EIDLE <= 1'b1))
      RXCDR_FR_RESET_ON_EIDLE_BINARY = RXCDR_FR_RESET_ON_EIDLE;
    else begin
      $display("Attribute Syntax Error : The Attribute RXCDR_FR_RESET_ON_EIDLE on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", RXCDR_FR_RESET_ON_EIDLE);
      #1 $finish;
    end

    if ((RXCDR_HOLD_DURING_EIDLE >= 1'b0) && (RXCDR_HOLD_DURING_EIDLE <= 1'b1))
      RXCDR_HOLD_DURING_EIDLE_BINARY = RXCDR_HOLD_DURING_EIDLE;
    else begin
      $display("Attribute Syntax Error : The Attribute RXCDR_HOLD_DURING_EIDLE on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", RXCDR_HOLD_DURING_EIDLE);
      #1 $finish;
    end

    if ((RXCDR_LOCK_CFG >= 6'b000000) && (RXCDR_LOCK_CFG <= 6'b111111))
      RXCDR_LOCK_CFG_BINARY = RXCDR_LOCK_CFG;
    else begin
      $display("Attribute Syntax Error : The Attribute RXCDR_LOCK_CFG on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 6'b000000 to 6'b111111.", RXCDR_LOCK_CFG);
      #1 $finish;
    end

    if ((RXCDR_PH_RESET_ON_EIDLE >= 1'b0) && (RXCDR_PH_RESET_ON_EIDLE <= 1'b1))
      RXCDR_PH_RESET_ON_EIDLE_BINARY = RXCDR_PH_RESET_ON_EIDLE;
    else begin
      $display("Attribute Syntax Error : The Attribute RXCDR_PH_RESET_ON_EIDLE on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", RXCDR_PH_RESET_ON_EIDLE);
      #1 $finish;
    end

    if ((RXISCANRESET_TIME >= 5'b00000) && (RXISCANRESET_TIME <= 5'b11111))
      RXISCANRESET_TIME_BINARY = RXISCANRESET_TIME;
    else begin
      $display("Attribute Syntax Error : The Attribute RXISCANRESET_TIME on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 5'b00000 to 5'b11111.", RXISCANRESET_TIME);
      #1 $finish;
    end

    if ((RXLPMRESET_TIME >= 7'b0000000) && (RXLPMRESET_TIME <= 7'b1111111))
      RXLPMRESET_TIME_BINARY = RXLPMRESET_TIME;
    else begin
      $display("Attribute Syntax Error : The Attribute RXLPMRESET_TIME on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 7'b0000000 to 7'b1111111.", RXLPMRESET_TIME);
      #1 $finish;
    end

    if ((RXLPM_BIAS_STARTUP_DISABLE >= 1'b0) && (RXLPM_BIAS_STARTUP_DISABLE <= 1'b1))
      RXLPM_BIAS_STARTUP_DISABLE_BINARY = RXLPM_BIAS_STARTUP_DISABLE;
    else begin
      $display("Attribute Syntax Error : The Attribute RXLPM_BIAS_STARTUP_DISABLE on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", RXLPM_BIAS_STARTUP_DISABLE);
      #1 $finish;
    end

    if ((RXLPM_CFG >= 4'b0000) && (RXLPM_CFG <= 4'b1111))
      RXLPM_CFG_BINARY = RXLPM_CFG;
    else begin
      $display("Attribute Syntax Error : The Attribute RXLPM_CFG on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 4'b0000 to 4'b1111.", RXLPM_CFG);
      #1 $finish;
    end

    if ((RXLPM_CFG1 >= 1'b0) && (RXLPM_CFG1 <= 1'b1))
      RXLPM_CFG1_BINARY = RXLPM_CFG1;
    else begin
      $display("Attribute Syntax Error : The Attribute RXLPM_CFG1 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", RXLPM_CFG1);
      #1 $finish;
    end

    if ((RXLPM_CM_CFG >= 1'b0) && (RXLPM_CM_CFG <= 1'b1))
      RXLPM_CM_CFG_BINARY = RXLPM_CM_CFG;
    else begin
      $display("Attribute Syntax Error : The Attribute RXLPM_CM_CFG on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", RXLPM_CM_CFG);
      #1 $finish;
    end

    if ((RXLPM_GC_CFG >= 9'b000000000) && (RXLPM_GC_CFG <= 9'b111111111))
      RXLPM_GC_CFG_BINARY = RXLPM_GC_CFG;
    else begin
      $display("Attribute Syntax Error : The Attribute RXLPM_GC_CFG on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 9'b000000000 to 9'b111111111.", RXLPM_GC_CFG);
      #1 $finish;
    end

    if ((RXLPM_GC_CFG2 >= 3'b000) && (RXLPM_GC_CFG2 <= 3'b111))
      RXLPM_GC_CFG2_BINARY = RXLPM_GC_CFG2;
    else begin
      $display("Attribute Syntax Error : The Attribute RXLPM_GC_CFG2 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 3'b000 to 3'b111.", RXLPM_GC_CFG2);
      #1 $finish;
    end

    if ((RXLPM_HF_CFG >= 14'b00000000000000) && (RXLPM_HF_CFG <= 14'b11111111111111))
      RXLPM_HF_CFG_BINARY = RXLPM_HF_CFG;
    else begin
      $display("Attribute Syntax Error : The Attribute RXLPM_HF_CFG on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 14'b00000000000000 to 14'b11111111111111.", RXLPM_HF_CFG);
      #1 $finish;
    end

    if ((RXLPM_HF_CFG2 >= 5'b00000) && (RXLPM_HF_CFG2 <= 5'b11111))
      RXLPM_HF_CFG2_BINARY = RXLPM_HF_CFG2;
    else begin
      $display("Attribute Syntax Error : The Attribute RXLPM_HF_CFG2 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 5'b00000 to 5'b11111.", RXLPM_HF_CFG2);
      #1 $finish;
    end

    if ((RXLPM_HF_CFG3 >= 4'b0000) && (RXLPM_HF_CFG3 <= 4'b1111))
      RXLPM_HF_CFG3_BINARY = RXLPM_HF_CFG3;
    else begin
      $display("Attribute Syntax Error : The Attribute RXLPM_HF_CFG3 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 4'b0000 to 4'b1111.", RXLPM_HF_CFG3);
      #1 $finish;
    end

    if ((RXLPM_HOLD_DURING_EIDLE >= 1'b0) && (RXLPM_HOLD_DURING_EIDLE <= 1'b1))
      RXLPM_HOLD_DURING_EIDLE_BINARY = RXLPM_HOLD_DURING_EIDLE;
    else begin
      $display("Attribute Syntax Error : The Attribute RXLPM_HOLD_DURING_EIDLE on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", RXLPM_HOLD_DURING_EIDLE);
      #1 $finish;
    end

    if ((RXLPM_INCM_CFG >= 1'b0) && (RXLPM_INCM_CFG <= 1'b1))
      RXLPM_INCM_CFG_BINARY = RXLPM_INCM_CFG;
    else begin
      $display("Attribute Syntax Error : The Attribute RXLPM_INCM_CFG on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", RXLPM_INCM_CFG);
      #1 $finish;
    end

    if ((RXLPM_IPCM_CFG >= 1'b0) && (RXLPM_IPCM_CFG <= 1'b1))
      RXLPM_IPCM_CFG_BINARY = RXLPM_IPCM_CFG;
    else begin
      $display("Attribute Syntax Error : The Attribute RXLPM_IPCM_CFG on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", RXLPM_IPCM_CFG);
      #1 $finish;
    end

    if ((RXLPM_LF_CFG >= 18'b000000000000000000) && (RXLPM_LF_CFG <= 18'b111111111111111111))
      RXLPM_LF_CFG_BINARY = RXLPM_LF_CFG;
    else begin
      $display("Attribute Syntax Error : The Attribute RXLPM_LF_CFG on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 18'b000000000000000000 to 18'b111111111111111111.", RXLPM_LF_CFG);
      #1 $finish;
    end

    if ((RXLPM_LF_CFG2 >= 5'b00000) && (RXLPM_LF_CFG2 <= 5'b11111))
      RXLPM_LF_CFG2_BINARY = RXLPM_LF_CFG2;
    else begin
      $display("Attribute Syntax Error : The Attribute RXLPM_LF_CFG2 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 5'b00000 to 5'b11111.", RXLPM_LF_CFG2);
      #1 $finish;
    end

    if ((RXLPM_OSINT_CFG >= 3'b000) && (RXLPM_OSINT_CFG <= 3'b111))
      RXLPM_OSINT_CFG_BINARY = RXLPM_OSINT_CFG;
    else begin
      $display("Attribute Syntax Error : The Attribute RXLPM_OSINT_CFG on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 3'b000 to 3'b111.", RXLPM_OSINT_CFG);
      #1 $finish;
    end

    if ((RXOOB_CFG >= 7'b0000000) && (RXOOB_CFG <= 7'b1111111))
      RXOOB_CFG_BINARY = RXOOB_CFG;
    else begin
      $display("Attribute Syntax Error : The Attribute RXOOB_CFG on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 7'b0000000 to 7'b1111111.", RXOOB_CFG);
      #1 $finish;
    end

    if ((RXOSCALRESET_TIME >= 5'b00000) && (RXOSCALRESET_TIME <= 5'b11111))
      RXOSCALRESET_TIME_BINARY = RXOSCALRESET_TIME;
    else begin
      $display("Attribute Syntax Error : The Attribute RXOSCALRESET_TIME on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 5'b00000 to 5'b11111.", RXOSCALRESET_TIME);
      #1 $finish;
    end

    if ((RXOSCALRESET_TIMEOUT >= 5'b00000) && (RXOSCALRESET_TIMEOUT <= 5'b11111))
      RXOSCALRESET_TIMEOUT_BINARY = RXOSCALRESET_TIMEOUT;
    else begin
      $display("Attribute Syntax Error : The Attribute RXOSCALRESET_TIMEOUT on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 5'b00000 to 5'b11111.", RXOSCALRESET_TIMEOUT);
      #1 $finish;
    end

    if ((RXPCSRESET_TIME >= 5'b00000) && (RXPCSRESET_TIME <= 5'b11111))
      RXPCSRESET_TIME_BINARY = RXPCSRESET_TIME;
    else begin
      $display("Attribute Syntax Error : The Attribute RXPCSRESET_TIME on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 5'b00000 to 5'b11111.", RXPCSRESET_TIME);
      #1 $finish;
    end

    if ((RXPH_MONITOR_SEL >= 5'b00000) && (RXPH_MONITOR_SEL <= 5'b11111))
      RXPH_MONITOR_SEL_BINARY = RXPH_MONITOR_SEL;
    else begin
      $display("Attribute Syntax Error : The Attribute RXPH_MONITOR_SEL on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 5'b00000 to 5'b11111.", RXPH_MONITOR_SEL);
      #1 $finish;
    end

    if ((RXPI_CFG0 >= 3'b000) && (RXPI_CFG0 <= 3'b111))
      RXPI_CFG0_BINARY = RXPI_CFG0;
    else begin
      $display("Attribute Syntax Error : The Attribute RXPI_CFG0 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 3'b000 to 3'b111.", RXPI_CFG0);
      #1 $finish;
    end

    if ((RXPI_CFG1 >= 1'b0) && (RXPI_CFG1 <= 1'b1))
      RXPI_CFG1_BINARY = RXPI_CFG1;
    else begin
      $display("Attribute Syntax Error : The Attribute RXPI_CFG1 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", RXPI_CFG1);
      #1 $finish;
    end

    if ((RXPI_CFG2 >= 1'b0) && (RXPI_CFG2 <= 1'b1))
      RXPI_CFG2_BINARY = RXPI_CFG2;
    else begin
      $display("Attribute Syntax Error : The Attribute RXPI_CFG2 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", RXPI_CFG2);
      #1 $finish;
    end

    if ((RXPMARESET_TIME >= 5'b00000) && (RXPMARESET_TIME <= 5'b11111))
      RXPMARESET_TIME_BINARY = RXPMARESET_TIME;
    else begin
      $display("Attribute Syntax Error : The Attribute RXPMARESET_TIME on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 5'b00000 to 5'b11111.", RXPMARESET_TIME);
      #1 $finish;
    end

    if ((RXPRBS_ERR_LOOPBACK >= 1'b0) && (RXPRBS_ERR_LOOPBACK <= 1'b1))
      RXPRBS_ERR_LOOPBACK_BINARY = RXPRBS_ERR_LOOPBACK;
    else begin
      $display("Attribute Syntax Error : The Attribute RXPRBS_ERR_LOOPBACK on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", RXPRBS_ERR_LOOPBACK);
      #1 $finish;
    end

    if ((RXSLIDE_AUTO_WAIT >= 0) && (RXSLIDE_AUTO_WAIT <= 15))
      RXSLIDE_AUTO_WAIT_BINARY = RXSLIDE_AUTO_WAIT;
    else begin
      $display("Attribute Syntax Error : The Attribute RXSLIDE_AUTO_WAIT on X_GTPE2_CHANNEL instance %m is set to %d.  Legal values for this attribute are  0 to 15.", RXSLIDE_AUTO_WAIT);
      #1 $finish;
    end

    if ((RXSYNC_MULTILANE >= 1'b0) && (RXSYNC_MULTILANE <= 1'b1))
      RXSYNC_MULTILANE_BINARY = RXSYNC_MULTILANE;
    else begin
      $display("Attribute Syntax Error : The Attribute RXSYNC_MULTILANE on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", RXSYNC_MULTILANE);
      #1 $finish;
    end

    if ((RXSYNC_OVRD >= 1'b0) && (RXSYNC_OVRD <= 1'b1))
      RXSYNC_OVRD_BINARY = RXSYNC_OVRD;
    else begin
      $display("Attribute Syntax Error : The Attribute RXSYNC_OVRD on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", RXSYNC_OVRD);
      #1 $finish;
    end

    if ((RXSYNC_SKIP_DA >= 1'b0) && (RXSYNC_SKIP_DA <= 1'b1))
      RXSYNC_SKIP_DA_BINARY = RXSYNC_SKIP_DA;
    else begin
      $display("Attribute Syntax Error : The Attribute RXSYNC_SKIP_DA on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", RXSYNC_SKIP_DA);
      #1 $finish;
    end

    if ((RX_BIAS_CFG >= 16'b0000000000000000) && (RX_BIAS_CFG <= 16'b1111111111111111))
      RX_BIAS_CFG_BINARY = RX_BIAS_CFG;
    else begin
      $display("Attribute Syntax Error : The Attribute RX_BIAS_CFG on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 16'b0000000000000000 to 16'b1111111111111111.", RX_BIAS_CFG);
      #1 $finish;
    end

    if ((RX_BUFFER_CFG >= 6'b000000) && (RX_BUFFER_CFG <= 6'b111111))
      RX_BUFFER_CFG_BINARY = RX_BUFFER_CFG;
    else begin
      $display("Attribute Syntax Error : The Attribute RX_BUFFER_CFG on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 6'b000000 to 6'b111111.", RX_BUFFER_CFG);
      #1 $finish;
    end

    if ((RX_CLKMUX_EN >= 1'b0) && (RX_CLKMUX_EN <= 1'b1))
      RX_CLKMUX_EN_BINARY = RX_CLKMUX_EN;
    else begin
      $display("Attribute Syntax Error : The Attribute RX_CLKMUX_EN on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", RX_CLKMUX_EN);
      #1 $finish;
    end

    if ((RX_CM_SEL >= 2'b00) && (RX_CM_SEL <= 2'b11))
      RX_CM_SEL_BINARY = RX_CM_SEL;
    else begin
      $display("Attribute Syntax Error : The Attribute RX_CM_SEL on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 2'b00 to 2'b11.", RX_CM_SEL);
      #1 $finish;
    end

    if ((RX_CM_TRIM >= 4'b0000) && (RX_CM_TRIM <= 4'b1111))
      RX_CM_TRIM_BINARY = RX_CM_TRIM;
    else begin
      $display("Attribute Syntax Error : The Attribute RX_CM_TRIM on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 4'b0000 to 4'b1111.", RX_CM_TRIM);
      #1 $finish;
    end

    if ((RX_DDI_SEL >= 6'b000000) && (RX_DDI_SEL <= 6'b111111))
      RX_DDI_SEL_BINARY = RX_DDI_SEL;
    else begin
      $display("Attribute Syntax Error : The Attribute RX_DDI_SEL on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 6'b000000 to 6'b111111.", RX_DDI_SEL);
      #1 $finish;
    end

    if ((RX_DEBUG_CFG >= 14'b00000000000000) && (RX_DEBUG_CFG <= 14'b11111111111111))
      RX_DEBUG_CFG_BINARY = RX_DEBUG_CFG;
    else begin
      $display("Attribute Syntax Error : The Attribute RX_DEBUG_CFG on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 14'b00000000000000 to 14'b11111111111111.", RX_DEBUG_CFG);
      #1 $finish;
    end

    if ((RX_OS_CFG >= 13'b0000000000000) && (RX_OS_CFG <= 13'b1111111111111))
      RX_OS_CFG_BINARY = RX_OS_CFG;
    else begin
      $display("Attribute Syntax Error : The Attribute RX_OS_CFG on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 13'b0000000000000 to 13'b1111111111111.", RX_OS_CFG);
      #1 $finish;
    end

    if ((SAS_MAX_COM >= 1) && (SAS_MAX_COM <= 127))
      SAS_MAX_COM_BINARY = SAS_MAX_COM;
    else begin
      $display("Attribute Syntax Error : The Attribute SAS_MAX_COM on X_GTPE2_CHANNEL instance %m is set to %d.  Legal values for this attribute are  1 to 127.", SAS_MAX_COM);
      #1 $finish;
    end

    if ((SAS_MIN_COM >= 1) && (SAS_MIN_COM <= 63))
      SAS_MIN_COM_BINARY = SAS_MIN_COM;
    else begin
      $display("Attribute Syntax Error : The Attribute SAS_MIN_COM on X_GTPE2_CHANNEL instance %m is set to %d.  Legal values for this attribute are  1 to 63.", SAS_MIN_COM);
      #1 $finish;
    end

    if ((SATA_BURST_SEQ_LEN >= 4'b0000) && (SATA_BURST_SEQ_LEN <= 4'b1111))
      SATA_BURST_SEQ_LEN_BINARY = SATA_BURST_SEQ_LEN;
    else begin
      $display("Attribute Syntax Error : The Attribute SATA_BURST_SEQ_LEN on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 4'b0000 to 4'b1111.", SATA_BURST_SEQ_LEN);
      #1 $finish;
    end

    if ((SATA_BURST_VAL >= 3'b000) && (SATA_BURST_VAL <= 3'b111))
      SATA_BURST_VAL_BINARY = SATA_BURST_VAL;
    else begin
      $display("Attribute Syntax Error : The Attribute SATA_BURST_VAL on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 3'b000 to 3'b111.", SATA_BURST_VAL);
      #1 $finish;
    end

    if ((SATA_EIDLE_VAL >= 3'b000) && (SATA_EIDLE_VAL <= 3'b111))
      SATA_EIDLE_VAL_BINARY = SATA_EIDLE_VAL;
    else begin
      $display("Attribute Syntax Error : The Attribute SATA_EIDLE_VAL on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 3'b000 to 3'b111.", SATA_EIDLE_VAL);
      #1 $finish;
    end

    if ((SATA_MAX_BURST >= 1) && (SATA_MAX_BURST <= 63))
      SATA_MAX_BURST_BINARY = SATA_MAX_BURST;
    else begin
      $display("Attribute Syntax Error : The Attribute SATA_MAX_BURST on X_GTPE2_CHANNEL instance %m is set to %d.  Legal values for this attribute are  1 to 63.", SATA_MAX_BURST);
      #1 $finish;
    end

    if ((SATA_MAX_INIT >= 1) && (SATA_MAX_INIT <= 63))
      SATA_MAX_INIT_BINARY = SATA_MAX_INIT;
    else begin
      $display("Attribute Syntax Error : The Attribute SATA_MAX_INIT on X_GTPE2_CHANNEL instance %m is set to %d.  Legal values for this attribute are  1 to 63.", SATA_MAX_INIT);
      #1 $finish;
    end

    if ((SATA_MAX_WAKE >= 1) && (SATA_MAX_WAKE <= 63))
      SATA_MAX_WAKE_BINARY = SATA_MAX_WAKE;
    else begin
      $display("Attribute Syntax Error : The Attribute SATA_MAX_WAKE on X_GTPE2_CHANNEL instance %m is set to %d.  Legal values for this attribute are  1 to 63.", SATA_MAX_WAKE);
      #1 $finish;
    end

    if ((SATA_MIN_BURST >= 1) && (SATA_MIN_BURST <= 61))
      SATA_MIN_BURST_BINARY = SATA_MIN_BURST;
    else begin
      $display("Attribute Syntax Error : The Attribute SATA_MIN_BURST on X_GTPE2_CHANNEL instance %m is set to %d.  Legal values for this attribute are  1 to 61.", SATA_MIN_BURST);
      #1 $finish;
    end

    if ((SATA_MIN_INIT >= 1) && (SATA_MIN_INIT <= 63))
      SATA_MIN_INIT_BINARY = SATA_MIN_INIT;
    else begin
      $display("Attribute Syntax Error : The Attribute SATA_MIN_INIT on X_GTPE2_CHANNEL instance %m is set to %d.  Legal values for this attribute are  1 to 63.", SATA_MIN_INIT);
      #1 $finish;
    end

    if ((SATA_MIN_WAKE >= 1) && (SATA_MIN_WAKE <= 63))
      SATA_MIN_WAKE_BINARY = SATA_MIN_WAKE;
    else begin
      $display("Attribute Syntax Error : The Attribute SATA_MIN_WAKE on X_GTPE2_CHANNEL instance %m is set to %d.  Legal values for this attribute are  1 to 63.", SATA_MIN_WAKE);
      #1 $finish;
    end

    if ((TERM_RCAL_CFG >= 15'b000000000000000) && (TERM_RCAL_CFG <= 15'b111111111111111))
      TERM_RCAL_CFG_BINARY = TERM_RCAL_CFG;
    else begin
      $display("Attribute Syntax Error : The Attribute TERM_RCAL_CFG on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 15'b000000000000000 to 15'b111111111111111.", TERM_RCAL_CFG);
      #1 $finish;
    end

    if ((TERM_RCAL_OVRD >= 3'b000) && (TERM_RCAL_OVRD <= 3'b111))
      TERM_RCAL_OVRD_BINARY = TERM_RCAL_OVRD;
    else begin
      $display("Attribute Syntax Error : The Attribute TERM_RCAL_OVRD on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 3'b000 to 3'b111.", TERM_RCAL_OVRD);
      #1 $finish;
    end

    if ((TXOOB_CFG >= 1'b0) && (TXOOB_CFG <= 1'b1))
      TXOOB_CFG_BINARY = TXOOB_CFG;
    else begin
      $display("Attribute Syntax Error : The Attribute TXOOB_CFG on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", TXOOB_CFG);
      #1 $finish;
    end

    if ((TXPCSRESET_TIME >= 5'b00000) && (TXPCSRESET_TIME <= 5'b11111))
      TXPCSRESET_TIME_BINARY = TXPCSRESET_TIME;
    else begin
      $display("Attribute Syntax Error : The Attribute TXPCSRESET_TIME on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 5'b00000 to 5'b11111.", TXPCSRESET_TIME);
      #1 $finish;
    end

    if ((TXPH_MONITOR_SEL >= 5'b00000) && (TXPH_MONITOR_SEL <= 5'b11111))
      TXPH_MONITOR_SEL_BINARY = TXPH_MONITOR_SEL;
    else begin
      $display("Attribute Syntax Error : The Attribute TXPH_MONITOR_SEL on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 5'b00000 to 5'b11111.", TXPH_MONITOR_SEL);
      #1 $finish;
    end

    if ((TXPI_CFG0 >= 2'b00) && (TXPI_CFG0 <= 2'b11))
      TXPI_CFG0_BINARY = TXPI_CFG0;
    else begin
      $display("Attribute Syntax Error : The Attribute TXPI_CFG0 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 2'b00 to 2'b11.", TXPI_CFG0);
      #1 $finish;
    end

    if ((TXPI_CFG1 >= 2'b00) && (TXPI_CFG1 <= 2'b11))
      TXPI_CFG1_BINARY = TXPI_CFG1;
    else begin
      $display("Attribute Syntax Error : The Attribute TXPI_CFG1 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 2'b00 to 2'b11.", TXPI_CFG1);
      #1 $finish;
    end

    if ((TXPI_CFG2 >= 2'b00) && (TXPI_CFG2 <= 2'b11))
      TXPI_CFG2_BINARY = TXPI_CFG2;
    else begin
      $display("Attribute Syntax Error : The Attribute TXPI_CFG2 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 2'b00 to 2'b11.", TXPI_CFG2);
      #1 $finish;
    end

    if ((TXPI_CFG3 >= 1'b0) && (TXPI_CFG3 <= 1'b1))
      TXPI_CFG3_BINARY = TXPI_CFG3;
    else begin
      $display("Attribute Syntax Error : The Attribute TXPI_CFG3 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", TXPI_CFG3);
      #1 $finish;
    end

    if ((TXPI_CFG4 >= 1'b0) && (TXPI_CFG4 <= 1'b1))
      TXPI_CFG4_BINARY = TXPI_CFG4;
    else begin
      $display("Attribute Syntax Error : The Attribute TXPI_CFG4 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", TXPI_CFG4);
      #1 $finish;
    end

    if ((TXPI_CFG5 >= 3'b000) && (TXPI_CFG5 <= 3'b111))
      TXPI_CFG5_BINARY = TXPI_CFG5;
    else begin
      $display("Attribute Syntax Error : The Attribute TXPI_CFG5 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 3'b000 to 3'b111.", TXPI_CFG5);
      #1 $finish;
    end

    if ((TXPI_GREY_SEL >= 1'b0) && (TXPI_GREY_SEL <= 1'b1))
      TXPI_GREY_SEL_BINARY = TXPI_GREY_SEL;
    else begin
      $display("Attribute Syntax Error : The Attribute TXPI_GREY_SEL on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", TXPI_GREY_SEL);
      #1 $finish;
    end

    if ((TXPI_INVSTROBE_SEL >= 1'b0) && (TXPI_INVSTROBE_SEL <= 1'b1))
      TXPI_INVSTROBE_SEL_BINARY = TXPI_INVSTROBE_SEL;
    else begin
      $display("Attribute Syntax Error : The Attribute TXPI_INVSTROBE_SEL on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", TXPI_INVSTROBE_SEL);
      #1 $finish;
    end

    if ((TXPI_PPM_CFG >= 8'b00000000) && (TXPI_PPM_CFG <= 8'b11111111))
      TXPI_PPM_CFG_BINARY = TXPI_PPM_CFG;
    else begin
      $display("Attribute Syntax Error : The Attribute TXPI_PPM_CFG on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 8'b00000000 to 8'b11111111.", TXPI_PPM_CFG);
      #1 $finish;
    end

    if ((TXPI_SYNFREQ_PPM >= 3'b000) && (TXPI_SYNFREQ_PPM <= 3'b111))
      TXPI_SYNFREQ_PPM_BINARY = TXPI_SYNFREQ_PPM;
    else begin
      $display("Attribute Syntax Error : The Attribute TXPI_SYNFREQ_PPM on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 3'b000 to 3'b111.", TXPI_SYNFREQ_PPM);
      #1 $finish;
    end

    if ((TXPMARESET_TIME >= 5'b00000) && (TXPMARESET_TIME <= 5'b11111))
      TXPMARESET_TIME_BINARY = TXPMARESET_TIME;
    else begin
      $display("Attribute Syntax Error : The Attribute TXPMARESET_TIME on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 5'b00000 to 5'b11111.", TXPMARESET_TIME);
      #1 $finish;
    end

    if ((TXSYNC_MULTILANE >= 1'b0) && (TXSYNC_MULTILANE <= 1'b1))
      TXSYNC_MULTILANE_BINARY = TXSYNC_MULTILANE;
    else begin
      $display("Attribute Syntax Error : The Attribute TXSYNC_MULTILANE on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", TXSYNC_MULTILANE);
      #1 $finish;
    end

    if ((TXSYNC_OVRD >= 1'b0) && (TXSYNC_OVRD <= 1'b1))
      TXSYNC_OVRD_BINARY = TXSYNC_OVRD;
    else begin
      $display("Attribute Syntax Error : The Attribute TXSYNC_OVRD on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", TXSYNC_OVRD);
      #1 $finish;
    end

    if ((TXSYNC_SKIP_DA >= 1'b0) && (TXSYNC_SKIP_DA <= 1'b1))
      TXSYNC_SKIP_DA_BINARY = TXSYNC_SKIP_DA;
    else begin
      $display("Attribute Syntax Error : The Attribute TXSYNC_SKIP_DA on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", TXSYNC_SKIP_DA);
      #1 $finish;
    end

    if ((TX_CLKMUX_EN >= 1'b0) && (TX_CLKMUX_EN <= 1'b1))
      TX_CLKMUX_EN_BINARY = TX_CLKMUX_EN;
    else begin
      $display("Attribute Syntax Error : The Attribute TX_CLKMUX_EN on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", TX_CLKMUX_EN);
      #1 $finish;
    end

    if ((TX_DEEMPH0 >= 6'b000000) && (TX_DEEMPH0 <= 6'b111111))
      TX_DEEMPH0_BINARY = TX_DEEMPH0;
    else begin
      $display("Attribute Syntax Error : The Attribute TX_DEEMPH0 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 6'b000000 to 6'b111111.", TX_DEEMPH0);
      #1 $finish;
    end

    if ((TX_DEEMPH1 >= 6'b000000) && (TX_DEEMPH1 <= 6'b111111))
      TX_DEEMPH1_BINARY = TX_DEEMPH1;
    else begin
      $display("Attribute Syntax Error : The Attribute TX_DEEMPH1 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 6'b000000 to 6'b111111.", TX_DEEMPH1);
      #1 $finish;
    end

    if ((TX_EIDLE_ASSERT_DELAY >= 3'b000) && (TX_EIDLE_ASSERT_DELAY <= 3'b111))
      TX_EIDLE_ASSERT_DELAY_BINARY = TX_EIDLE_ASSERT_DELAY;
    else begin
      $display("Attribute Syntax Error : The Attribute TX_EIDLE_ASSERT_DELAY on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 3'b000 to 3'b111.", TX_EIDLE_ASSERT_DELAY);
      #1 $finish;
    end

    if ((TX_EIDLE_DEASSERT_DELAY >= 3'b000) && (TX_EIDLE_DEASSERT_DELAY <= 3'b111))
      TX_EIDLE_DEASSERT_DELAY_BINARY = TX_EIDLE_DEASSERT_DELAY;
    else begin
      $display("Attribute Syntax Error : The Attribute TX_EIDLE_DEASSERT_DELAY on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 3'b000 to 3'b111.", TX_EIDLE_DEASSERT_DELAY);
      #1 $finish;
    end

    if ((TX_MAINCURSOR_SEL >= 1'b0) && (TX_MAINCURSOR_SEL <= 1'b1))
      TX_MAINCURSOR_SEL_BINARY = TX_MAINCURSOR_SEL;
    else begin
      $display("Attribute Syntax Error : The Attribute TX_MAINCURSOR_SEL on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", TX_MAINCURSOR_SEL);
      #1 $finish;
    end

    if ((TX_MARGIN_FULL_0 >= 7'b0000000) && (TX_MARGIN_FULL_0 <= 7'b1111111))
      TX_MARGIN_FULL_0_BINARY = TX_MARGIN_FULL_0;
    else begin
      $display("Attribute Syntax Error : The Attribute TX_MARGIN_FULL_0 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 7'b0000000 to 7'b1111111.", TX_MARGIN_FULL_0);
      #1 $finish;
    end

    if ((TX_MARGIN_FULL_1 >= 7'b0000000) && (TX_MARGIN_FULL_1 <= 7'b1111111))
      TX_MARGIN_FULL_1_BINARY = TX_MARGIN_FULL_1;
    else begin
      $display("Attribute Syntax Error : The Attribute TX_MARGIN_FULL_1 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 7'b0000000 to 7'b1111111.", TX_MARGIN_FULL_1);
      #1 $finish;
    end

    if ((TX_MARGIN_FULL_2 >= 7'b0000000) && (TX_MARGIN_FULL_2 <= 7'b1111111))
      TX_MARGIN_FULL_2_BINARY = TX_MARGIN_FULL_2;
    else begin
      $display("Attribute Syntax Error : The Attribute TX_MARGIN_FULL_2 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 7'b0000000 to 7'b1111111.", TX_MARGIN_FULL_2);
      #1 $finish;
    end

    if ((TX_MARGIN_FULL_3 >= 7'b0000000) && (TX_MARGIN_FULL_3 <= 7'b1111111))
      TX_MARGIN_FULL_3_BINARY = TX_MARGIN_FULL_3;
    else begin
      $display("Attribute Syntax Error : The Attribute TX_MARGIN_FULL_3 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 7'b0000000 to 7'b1111111.", TX_MARGIN_FULL_3);
      #1 $finish;
    end

    if ((TX_MARGIN_FULL_4 >= 7'b0000000) && (TX_MARGIN_FULL_4 <= 7'b1111111))
      TX_MARGIN_FULL_4_BINARY = TX_MARGIN_FULL_4;
    else begin
      $display("Attribute Syntax Error : The Attribute TX_MARGIN_FULL_4 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 7'b0000000 to 7'b1111111.", TX_MARGIN_FULL_4);
      #1 $finish;
    end

    if ((TX_MARGIN_LOW_0 >= 7'b0000000) && (TX_MARGIN_LOW_0 <= 7'b1111111))
      TX_MARGIN_LOW_0_BINARY = TX_MARGIN_LOW_0;
    else begin
      $display("Attribute Syntax Error : The Attribute TX_MARGIN_LOW_0 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 7'b0000000 to 7'b1111111.", TX_MARGIN_LOW_0);
      #1 $finish;
    end

    if ((TX_MARGIN_LOW_1 >= 7'b0000000) && (TX_MARGIN_LOW_1 <= 7'b1111111))
      TX_MARGIN_LOW_1_BINARY = TX_MARGIN_LOW_1;
    else begin
      $display("Attribute Syntax Error : The Attribute TX_MARGIN_LOW_1 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 7'b0000000 to 7'b1111111.", TX_MARGIN_LOW_1);
      #1 $finish;
    end

    if ((TX_MARGIN_LOW_2 >= 7'b0000000) && (TX_MARGIN_LOW_2 <= 7'b1111111))
      TX_MARGIN_LOW_2_BINARY = TX_MARGIN_LOW_2;
    else begin
      $display("Attribute Syntax Error : The Attribute TX_MARGIN_LOW_2 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 7'b0000000 to 7'b1111111.", TX_MARGIN_LOW_2);
      #1 $finish;
    end

    if ((TX_MARGIN_LOW_3 >= 7'b0000000) && (TX_MARGIN_LOW_3 <= 7'b1111111))
      TX_MARGIN_LOW_3_BINARY = TX_MARGIN_LOW_3;
    else begin
      $display("Attribute Syntax Error : The Attribute TX_MARGIN_LOW_3 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 7'b0000000 to 7'b1111111.", TX_MARGIN_LOW_3);
      #1 $finish;
    end

    if ((TX_MARGIN_LOW_4 >= 7'b0000000) && (TX_MARGIN_LOW_4 <= 7'b1111111))
      TX_MARGIN_LOW_4_BINARY = TX_MARGIN_LOW_4;
    else begin
      $display("Attribute Syntax Error : The Attribute TX_MARGIN_LOW_4 on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 7'b0000000 to 7'b1111111.", TX_MARGIN_LOW_4);
      #1 $finish;
    end

    if ((TX_PREDRIVER_MODE >= 1'b0) && (TX_PREDRIVER_MODE <= 1'b1))
      TX_PREDRIVER_MODE_BINARY = TX_PREDRIVER_MODE;
    else begin
      $display("Attribute Syntax Error : The Attribute TX_PREDRIVER_MODE on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", TX_PREDRIVER_MODE);
      #1 $finish;
    end

    if ((TX_RXDETECT_REF >= 3'b000) && (TX_RXDETECT_REF <= 3'b111))
      TX_RXDETECT_REF_BINARY = TX_RXDETECT_REF;
    else begin
      $display("Attribute Syntax Error : The Attribute TX_RXDETECT_REF on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 3'b000 to 3'b111.", TX_RXDETECT_REF);
      #1 $finish;
    end

    if ((UCODEER_CLR >= 1'b0) && (UCODEER_CLR <= 1'b1))
      UCODEER_CLR_BINARY = UCODEER_CLR;
    else begin
      $display("Attribute Syntax Error : The Attribute UCODEER_CLR on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", UCODEER_CLR);
      #1 $finish;
    end

    if ((USE_PCS_CLK_PHASE_SEL >= 1'b0) && (USE_PCS_CLK_PHASE_SEL <= 1'b1))
      USE_PCS_CLK_PHASE_SEL_BINARY = USE_PCS_CLK_PHASE_SEL;
    else begin
      $display("Attribute Syntax Error : The Attribute USE_PCS_CLK_PHASE_SEL on X_GTPE2_CHANNEL instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", USE_PCS_CLK_PHASE_SEL);
      #1 $finish;
    end

  end

  wire [14:0] delay_DMONITOROUT;
  wire [15:0] delay_DRPDO;
  wire [15:0] delay_PCSRSVDOUT;
  wire [1:0] delay_RXCLKCORCNT;
  wire [1:0] delay_RXDATAVALID;
  wire [1:0] delay_RXSTARTOFSEQ;
  wire [1:0] delay_TXBUFSTATUS;
  wire [2:0] delay_RXBUFSTATUS;
  wire [2:0] delay_RXHEADER;
  wire [2:0] delay_RXSTATUS;
  wire [31:0] delay_RXDATA;
  wire [3:0] delay_RXCHARISCOMMA;
  wire [3:0] delay_RXCHARISK;
  wire [3:0] delay_RXCHBONDO;
  wire [3:0] delay_RXDISPERR;
  wire [3:0] delay_RXNOTINTABLE;
  wire [4:0] delay_RXPHMONITOR;
  wire [4:0] delay_RXPHSLIPMONITOR;
  wire delay_DRPRDY;
  wire delay_EYESCANDATAERROR;
  wire delay_GTPTXN;
  wire delay_GTPTXP;
  wire delay_PHYSTATUS;
  wire delay_PMARSVDOUT0;
  wire delay_PMARSVDOUT1;
  wire delay_RXBYTEISALIGNED;
  wire delay_RXBYTEREALIGN;
  wire delay_RXCDRLOCK;
  wire delay_RXCHANBONDSEQ;
  wire delay_RXCHANISALIGNED;
  wire delay_RXCHANREALIGN;
  wire delay_RXCOMINITDET;
  wire delay_RXCOMMADET;
  wire delay_RXCOMSASDET;
  wire delay_RXCOMWAKEDET;
  wire delay_RXDLYSRESETDONE;
  wire delay_RXELECIDLE;
  wire delay_RXHEADERVALID;
  wire delay_RXOSINTDONE;
  wire delay_RXOSINTSTARTED;
  wire delay_RXOSINTSTROBEDONE;
  wire delay_RXOSINTSTROBESTARTED;
  wire delay_RXOUTCLK;
  wire delay_RXOUTCLKFABRIC;
  wire delay_RXOUTCLKPCS;
  wire delay_RXPHALIGNDONE;
  wire delay_RXPMARESETDONE;
  wire delay_RXPRBSERR;
  wire delay_RXRATEDONE;
  wire delay_RXRESETDONE;
  wire delay_RXSYNCDONE;
  wire delay_RXSYNCOUT;
  wire delay_RXVALID;
  wire delay_TXCOMFINISH;
  wire delay_TXDLYSRESETDONE;
  wire delay_TXGEARBOXREADY;
  wire delay_TXOUTCLK;
  wire delay_TXOUTCLKFABRIC;
  wire delay_TXOUTCLKPCS;
  wire delay_TXPHALIGNDONE;
  wire delay_TXPHINITDONE;
  wire delay_TXPMARESETDONE;
  wire delay_TXRATEDONE;
  wire delay_TXRESETDONE;
  wire delay_TXSYNCDONE;
  wire delay_TXSYNCOUT;

  wire [13:0] delay_RXADAPTSELTEST;
  wire [15:0] delay_DRPDI;
  wire [15:0] delay_GTRSVD;
  wire [15:0] delay_PCSRSVDIN;
  wire [19:0] delay_TSTIN;
  wire [1:0] delay_RXELECIDLEMODE;
  wire [1:0] delay_RXPD;
  wire [1:0] delay_RXSYSCLKSEL;
  wire [1:0] delay_TXPD;
  wire [1:0] delay_TXSYSCLKSEL;
  wire [2:0] delay_LOOPBACK;
  wire [2:0] delay_RXCHBONDLEVEL;
  wire [2:0] delay_RXOUTCLKSEL;
  wire [2:0] delay_RXPRBSSEL;
  wire [2:0] delay_RXRATE;
  wire [2:0] delay_TXBUFDIFFCTRL;
  wire [2:0] delay_TXHEADER;
  wire [2:0] delay_TXMARGIN;
  wire [2:0] delay_TXOUTCLKSEL;
  wire [2:0] delay_TXPRBSSEL;
  wire [2:0] delay_TXRATE;
  wire [31:0] delay_TXDATA;
  wire [3:0] delay_RXCHBONDI;
  wire [3:0] delay_RXOSINTCFG;
  wire [3:0] delay_RXOSINTID0;
  wire [3:0] delay_TX8B10BBYPASS;
  wire [3:0] delay_TXCHARDISPMODE;
  wire [3:0] delay_TXCHARDISPVAL;
  wire [3:0] delay_TXCHARISK;
  wire [3:0] delay_TXDIFFCTRL;
  wire [4:0] delay_TXPIPPMSTEPSIZE;
  wire [4:0] delay_TXPOSTCURSOR;
  wire [4:0] delay_TXPRECURSOR;
  wire [6:0] delay_TXMAINCURSOR;
  wire [6:0] delay_TXSEQUENCE;
  wire [8:0] delay_DRPADDR;
  wire delay_CFGRESET;
  wire delay_CLKRSVD0;
  wire delay_CLKRSVD1;
  wire delay_DMONFIFORESET;
  wire delay_DMONITORCLK;
  wire delay_DRPCLK;
  wire delay_DRPEN;
  wire delay_DRPWE;
  wire delay_EYESCANMODE;
  wire delay_EYESCANRESET;
  wire delay_EYESCANTRIGGER;
  wire delay_GTPRXN;
  wire delay_GTPRXP;
  wire delay_GTRESETSEL;
  wire delay_GTRXRESET;
  wire delay_GTTXRESET;
  wire delay_PLL0CLK;
  wire delay_PLL0REFCLK;
  wire delay_PLL1CLK;
  wire delay_PLL1REFCLK;
  wire delay_PMARSVDIN0;
  wire delay_PMARSVDIN1;
  wire delay_PMARSVDIN2;
  wire delay_PMARSVDIN3;
  wire delay_PMARSVDIN4;
  wire delay_RESETOVRD;
  wire delay_RX8B10BEN;
  wire delay_RXBUFRESET;
  wire delay_RXCDRFREQRESET;
  wire delay_RXCDRHOLD;
  wire delay_RXCDROVRDEN;
  wire delay_RXCDRRESET;
  wire delay_RXCDRRESETRSV;
  wire delay_RXCHBONDEN;
  wire delay_RXCHBONDMASTER;
  wire delay_RXCHBONDSLAVE;
  wire delay_RXCOMMADETEN;
  wire delay_RXDDIEN;
  wire delay_RXDFEXYDEN;
  wire delay_RXDLYBYPASS;
  wire delay_RXDLYEN;
  wire delay_RXDLYOVRDEN;
  wire delay_RXDLYSRESET;
  wire delay_RXGEARBOXSLIP;
  wire delay_RXLPMHFHOLD;
  wire delay_RXLPMHFOVRDEN;
  wire delay_RXLPMLFHOLD;
  wire delay_RXLPMLFOVRDEN;
  wire delay_RXLPMOSINTNTRLEN;
  wire delay_RXLPMRESET;
  wire delay_RXMCOMMAALIGNEN;
  wire delay_RXOOBRESET;
  wire delay_RXOSCALRESET;
  wire delay_RXOSHOLD;
  wire delay_RXOSINTEN;
  wire delay_RXOSINTHOLD;
  wire delay_RXOSINTNTRLEN;
  wire delay_RXOSINTOVRDEN;
  wire delay_RXOSINTPD;
  wire delay_RXOSINTSTROBE;
  wire delay_RXOSINTTESTOVRDEN;
  wire delay_RXOSOVRDEN;
  wire delay_RXPCOMMAALIGNEN;
  wire delay_RXPCSRESET;
  wire delay_RXPHALIGN;
  wire delay_RXPHALIGNEN;
  wire delay_RXPHDLYPD;
  wire delay_RXPHDLYRESET;
  wire delay_RXPHOVRDEN;
  wire delay_RXPMARESET;
  wire delay_RXPOLARITY;
  wire delay_RXPRBSCNTRESET;
  wire delay_RXRATEMODE;
  wire delay_RXSLIDE;
  wire delay_RXSYNCALLIN;
  wire delay_RXSYNCIN;
  wire delay_RXSYNCMODE;
  wire delay_RXUSERRDY;
  wire delay_RXUSRCLK2;
  wire delay_RXUSRCLK;
  wire delay_SETERRSTATUS;
  wire delay_SIGVALIDCLK;
  wire delay_TX8B10BEN;
  wire delay_TXCOMINIT;
  wire delay_TXCOMSAS;
  wire delay_TXCOMWAKE;
  wire delay_TXDEEMPH;
  wire delay_TXDETECTRX;
  wire delay_TXDIFFPD;
  wire delay_TXDLYBYPASS;
  wire delay_TXDLYEN;
  wire delay_TXDLYHOLD;
  wire delay_TXDLYOVRDEN;
  wire delay_TXDLYSRESET;
  wire delay_TXDLYUPDOWN;
  wire delay_TXELECIDLE;
  wire delay_TXINHIBIT;
  wire delay_TXPCSRESET;
  wire delay_TXPDELECIDLEMODE;
  wire delay_TXPHALIGN;
  wire delay_TXPHALIGNEN;
  wire delay_TXPHDLYPD;
  wire delay_TXPHDLYRESET;
  wire delay_TXPHDLYTSTCLK;
  wire delay_TXPHINIT;
  wire delay_TXPHOVRDEN;
  wire delay_TXPIPPMEN;
  wire delay_TXPIPPMOVRDEN;
  wire delay_TXPIPPMPD;
  wire delay_TXPIPPMSEL;
  wire delay_TXPISOPD;
  wire delay_TXPMARESET;
  wire delay_TXPOLARITY;
  wire delay_TXPOSTCURSORINV;
  wire delay_TXPRBSFORCEERR;
  wire delay_TXPRECURSORINV;
  wire delay_TXRATEMODE;
  wire delay_TXSTARTSEQ;
  wire delay_TXSWING;
  wire delay_TXSYNCALLIN;
  wire delay_TXSYNCIN;
  wire delay_TXSYNCMODE;
  wire delay_TXUSERRDY;
  wire delay_TXUSRCLK2;
  wire delay_TXUSRCLK;

   
   //drp monitor
   reg drpen_r1 = 1'b0;
   reg drpen_r2 = 1'b0;
   reg drpwe_r1 = 1'b0;
   reg drpwe_r2 = 1'b0;
   
   reg [1:0] sfsm = 2'b01;
    
   localparam FSM_IDLE = 2'b01;  
   localparam FSM_WAIT = 2'b10;
  

   always @(posedge DRPCLK)
     begin
	// pipeline the DRPEN and DRPWE
        drpen_r1 <= DRPEN;
        drpwe_r1 <= DRPWE;
	drpen_r2 <= drpen_r1;
        drpwe_r2 <= drpwe_r1;

	
	// Check -  if DRPEN or DRPWE is more than 1 DCLK
	if ((drpen_r1 == 1'b1) && (drpen_r2 == 1'b1)) 
	  begin
	     $display("DRC Error : DRPEN is high for more than 1 DRPCLK on %m instance");
	     $finish; 
          end
	
	if ((drpwe_r1 == 1'b1) && (drpwe_r2 == 1'b1))
	  begin
             $display("DRC Error : DRPWE is high for more than 1 DRPCLK on %m instance");
             $finish;
          end


	//After the 1st DRPEN pulse, check the DRPEN and DRPRDY.
	case (sfsm)
          FSM_IDLE:   
            begin
               if(DRPEN == 1'b1)
		 sfsm <= FSM_WAIT;  
            end
          
          FSM_WAIT:
            begin
               // After the 1st DRPEN, 4 cases can happen
               // DRPEN DRPRDY NEXT STATE
               // 0     0      FSM_WAIT - wait for DRPRDY
               // 0     1      FSM_IDLE - normal operation
               // 1     0      FSM_WAIT - display error and wait for DRPRDY
               // 1     1      FSM_WAIT - normal operation. Per UG470, DRPEN and DRPRDY can be at the same cycle.
               
               //Add the check for another DPREN pulse
               if(DRPEN === 1'b1 && delay_DRPRDY === 1'b0) 
		 begin
		    $display("DRC Error : DRPEN is enabled before DRPRDY returns on %m instance");  
		    $finish;
		 end

               //Add the check for another DRPWE pulse
               if ((DRPWE === 1'b1) && (DRPEN === 1'b0))
		 begin
		    $display("DRC Error : DRPWE is enabled before DRPRDY returns on %m instance");
		    $finish;
		 end
                    
               if ((delay_DRPRDY === 1'b1) && (DRPEN === 1'b0))
		 begin
		    sfsm <= FSM_IDLE;
		 end  
               
               if ((delay_DRPRDY === 1'b1)&& (DRPEN === 1'b1))
		 begin
		    sfsm <= FSM_WAIT;
		 end  
            end
        
          default:                  
            begin
               $display("DRC Error : Default state in DRP FSM.");
               $finish;
            end
	endcase

     end // always @ (posedge DRPCLK)
   //end drp monitor

  reg [0:0] IS_CLKRSVD0_INVERTED_REG = IS_CLKRSVD0_INVERTED;
  reg [0:0] IS_CLKRSVD1_INVERTED_REG = IS_CLKRSVD1_INVERTED;
  reg [0:0] IS_DMONITORCLK_INVERTED_REG = IS_DMONITORCLK_INVERTED;
  reg [0:0] IS_DRPCLK_INVERTED_REG = IS_DRPCLK_INVERTED;
  reg [0:0] IS_RXUSRCLK2_INVERTED_REG = IS_RXUSRCLK2_INVERTED;
  reg [0:0] IS_RXUSRCLK_INVERTED_REG = IS_RXUSRCLK_INVERTED;
  reg [0:0] IS_SIGVALIDCLK_INVERTED_REG = IS_SIGVALIDCLK_INVERTED;
  reg [0:0] IS_TXPHDLYTSTCLK_INVERTED_REG = IS_TXPHDLYTSTCLK_INVERTED;
  reg [0:0] IS_TXUSRCLK2_INVERTED_REG = IS_TXUSRCLK2_INVERTED;
  reg [0:0] IS_TXUSRCLK_INVERTED_REG = IS_TXUSRCLK_INVERTED;
   
  assign #(OUTCLK_DELAY) RXOUTCLK = delay_RXOUTCLK;
  assign #(OUTCLK_DELAY) TXOUTCLK = delay_TXOUTCLK;

  assign #(out_delay) DMONITOROUT = delay_DMONITOROUT;
  assign #(out_delay) DRPDO = delay_DRPDO;
  assign #(out_delay) DRPRDY = delay_DRPRDY;
  assign #(out_delay) EYESCANDATAERROR = delay_EYESCANDATAERROR;
  assign #(out_delay) GTPTXN = delay_GTPTXN;
  assign #(out_delay) GTPTXP = delay_GTPTXP;
  assign #(out_delay) PCSRSVDOUT = delay_PCSRSVDOUT;
  assign #(out_delay) PHYSTATUS = delay_PHYSTATUS;
  assign #(out_delay) PMARSVDOUT0 = delay_PMARSVDOUT0;
  assign #(out_delay) PMARSVDOUT1 = delay_PMARSVDOUT1;
  assign #(out_delay) RXBUFSTATUS = delay_RXBUFSTATUS;
  assign #(out_delay) RXBYTEISALIGNED = delay_RXBYTEISALIGNED;
  assign #(out_delay) RXBYTEREALIGN = delay_RXBYTEREALIGN;
  assign #(out_delay) RXCDRLOCK = delay_RXCDRLOCK;
  assign #(out_delay) RXCHANBONDSEQ = delay_RXCHANBONDSEQ;
  assign #(out_delay) RXCHANISALIGNED = delay_RXCHANISALIGNED;
  assign #(out_delay) RXCHANREALIGN = delay_RXCHANREALIGN;
  assign #(out_delay) RXCHARISCOMMA = delay_RXCHARISCOMMA;
  assign #(out_delay) RXCHARISK = delay_RXCHARISK;
  assign #(out_delay) RXCHBONDO = delay_RXCHBONDO;
  assign #(out_delay) RXCLKCORCNT = delay_RXCLKCORCNT;
  assign #(out_delay) RXCOMINITDET = delay_RXCOMINITDET;
  assign #(out_delay) RXCOMMADET = delay_RXCOMMADET;
  assign #(out_delay) RXCOMSASDET = delay_RXCOMSASDET;
  assign #(out_delay) RXCOMWAKEDET = delay_RXCOMWAKEDET;
  assign #(out_delay) RXDATA = delay_RXDATA;
  assign #(out_delay) RXDATAVALID = delay_RXDATAVALID;
  assign #(out_delay) RXDISPERR = delay_RXDISPERR;
  assign #(out_delay) RXDLYSRESETDONE = delay_RXDLYSRESETDONE;
  assign #(out_delay) RXELECIDLE = delay_RXELECIDLE;
  assign #(out_delay) RXHEADER = delay_RXHEADER;
  assign #(out_delay) RXHEADERVALID = delay_RXHEADERVALID;
  assign #(out_delay) RXNOTINTABLE = delay_RXNOTINTABLE;
  assign #(out_delay) RXOSINTDONE = delay_RXOSINTDONE;
  assign #(out_delay) RXOSINTSTARTED = delay_RXOSINTSTARTED;
  assign #(out_delay) RXOSINTSTROBEDONE = delay_RXOSINTSTROBEDONE;
  assign #(out_delay) RXOSINTSTROBESTARTED = delay_RXOSINTSTROBESTARTED;
  assign #(out_delay) RXOUTCLKFABRIC = delay_RXOUTCLKFABRIC;
  assign #(out_delay) RXOUTCLKPCS = delay_RXOUTCLKPCS;
  assign #(out_delay) RXPHALIGNDONE = delay_RXPHALIGNDONE;
  assign #(out_delay) RXPHMONITOR = delay_RXPHMONITOR;
  assign #(out_delay) RXPHSLIPMONITOR = delay_RXPHSLIPMONITOR;
  assign #(out_delay) RXPMARESETDONE = delay_RXPMARESETDONE;
  assign #(out_delay) RXPRBSERR = delay_RXPRBSERR;
  assign #(out_delay) RXRATEDONE = delay_RXRATEDONE;
  assign #(out_delay) RXRESETDONE = delay_RXRESETDONE;
  assign #(out_delay) RXSTARTOFSEQ = delay_RXSTARTOFSEQ;
  assign #(out_delay) RXSTATUS = delay_RXSTATUS;
  assign #(out_delay) RXSYNCDONE = delay_RXSYNCDONE;
  assign #(out_delay) RXSYNCOUT = delay_RXSYNCOUT;
  assign #(out_delay) RXVALID = delay_RXVALID;
  assign #(out_delay) TXBUFSTATUS = delay_TXBUFSTATUS;
  assign #(out_delay) TXCOMFINISH = delay_TXCOMFINISH;
  assign #(out_delay) TXDLYSRESETDONE = delay_TXDLYSRESETDONE;
  assign #(out_delay) TXGEARBOXREADY = delay_TXGEARBOXREADY;
  assign #(out_delay) TXOUTCLKFABRIC = delay_TXOUTCLKFABRIC;
  assign #(out_delay) TXOUTCLKPCS = delay_TXOUTCLKPCS;
  assign #(out_delay) TXPHALIGNDONE = delay_TXPHALIGNDONE;
  assign #(out_delay) TXPHINITDONE = delay_TXPHINITDONE;
  assign #(out_delay) TXPMARESETDONE = delay_TXPMARESETDONE;
  assign #(out_delay) TXRATEDONE = delay_TXRATEDONE;
  assign #(out_delay) TXRESETDONE = delay_TXRESETDONE;
  assign #(out_delay) TXSYNCDONE = delay_TXSYNCDONE;
  assign #(out_delay) TXSYNCOUT = delay_TXSYNCOUT;
  
`ifndef XIL_TIMING // unisim
  assign #(INCLK_DELAY) delay_CLKRSVD0 = CLKRSVD0 ^ IS_CLKRSVD0_INVERTED_REG;
  assign #(INCLK_DELAY) delay_CLKRSVD1 = CLKRSVD1 ^ IS_CLKRSVD1_INVERTED_REG;
  assign #(INCLK_DELAY) delay_DMONITORCLK = DMONITORCLK ^ IS_DMONITORCLK_INVERTED_REG;
  assign #(INCLK_DELAY) delay_DRPCLK = DRPCLK ^ IS_DRPCLK_INVERTED_REG;
  assign #(INCLK_DELAY) delay_PLL0CLK = PLL0CLK;
  assign #(INCLK_DELAY) delay_PLL1CLK = PLL1CLK;
  assign #(INCLK_DELAY) delay_RXUSRCLK = RXUSRCLK ^ IS_RXUSRCLK2_INVERTED_REG;
  assign #(INCLK_DELAY) delay_RXUSRCLK2 = RXUSRCLK2 ^ IS_RXUSRCLK2_INVERTED_REG;
  assign #(INCLK_DELAY) delay_SIGVALIDCLK = SIGVALIDCLK^  IS_SIGVALIDCLK_INVERTED_REG;
  assign #(INCLK_DELAY) delay_TXPHDLYTSTCLK = TXPHDLYTSTCLK ^ IS_TXPHDLYTSTCLK_INVERTED_REG;
  assign #(INCLK_DELAY) delay_TXUSRCLK = TXUSRCLK;
  assign #(INCLK_DELAY) delay_TXUSRCLK2 = TXUSRCLK2;

  assign #(in_delay) delay_CFGRESET = CFGRESET;
  assign #(in_delay) delay_DMONFIFORESET = DMONFIFORESET;
  assign #(in_delay) delay_DRPADDR = DRPADDR;
  assign #(in_delay) delay_DRPDI = DRPDI;
  assign #(in_delay) delay_DRPEN = DRPEN;
  assign #(in_delay) delay_DRPWE = DRPWE;
  assign #(in_delay) delay_EYESCANMODE = EYESCANMODE;
  assign #(in_delay) delay_EYESCANRESET = EYESCANRESET;
  assign #(in_delay) delay_EYESCANTRIGGER = EYESCANTRIGGER;
  assign #(in_delay) delay_GTPRXN = GTPRXN;
  assign #(in_delay) delay_GTPRXP = GTPRXP;
  assign #(in_delay) delay_GTRESETSEL = GTRESETSEL;
  assign #(in_delay) delay_GTRSVD = GTRSVD;
  assign #(in_delay) delay_GTRXRESET = GTRXRESET;
  assign #(in_delay) delay_GTTXRESET = GTTXRESET;
  assign #(in_delay) delay_LOOPBACK = LOOPBACK;
  assign #(in_delay) delay_PCSRSVDIN = PCSRSVDIN;
  assign #(in_delay) delay_PLL0REFCLK = PLL0REFCLK;
  assign #(in_delay) delay_PLL1REFCLK = PLL1REFCLK;
  assign #(in_delay) delay_PMARSVDIN0 = PMARSVDIN0;
  assign #(in_delay) delay_PMARSVDIN1 = PMARSVDIN1;
  assign #(in_delay) delay_PMARSVDIN2 = PMARSVDIN2;
  assign #(in_delay) delay_PMARSVDIN3 = PMARSVDIN3;
  assign #(in_delay) delay_PMARSVDIN4 = PMARSVDIN4;
  assign #(in_delay) delay_RESETOVRD = RESETOVRD;
  assign #(in_delay) delay_RX8B10BEN = RX8B10BEN;
  assign #(in_delay) delay_RXADAPTSELTEST = RXADAPTSELTEST;
  assign #(in_delay) delay_RXBUFRESET = RXBUFRESET;
  assign #(in_delay) delay_RXCDRFREQRESET = RXCDRFREQRESET;
  assign #(in_delay) delay_RXCDRHOLD = RXCDRHOLD;
  assign #(in_delay) delay_RXCDROVRDEN = RXCDROVRDEN;
  assign #(in_delay) delay_RXCDRRESET = RXCDRRESET;
  assign #(in_delay) delay_RXCDRRESETRSV = RXCDRRESETRSV;
  assign #(in_delay) delay_RXCHBONDEN = RXCHBONDEN;
  assign #(in_delay) delay_RXCHBONDI = RXCHBONDI;
  assign #(in_delay) delay_RXCHBONDLEVEL = RXCHBONDLEVEL;
  assign #(in_delay) delay_RXCHBONDMASTER = RXCHBONDMASTER;
  assign #(in_delay) delay_RXCHBONDSLAVE = RXCHBONDSLAVE;
  assign #(in_delay) delay_RXCOMMADETEN = RXCOMMADETEN;
  assign #(in_delay) delay_RXDDIEN = RXDDIEN;
  assign #(in_delay) delay_RXDFEXYDEN = RXDFEXYDEN;
  assign #(in_delay) delay_RXDLYBYPASS = RXDLYBYPASS;
  assign #(in_delay) delay_RXDLYEN = RXDLYEN;
  assign #(in_delay) delay_RXDLYOVRDEN = RXDLYOVRDEN;
  assign #(in_delay) delay_RXDLYSRESET = RXDLYSRESET;
  assign #(in_delay) delay_RXELECIDLEMODE = RXELECIDLEMODE;
  assign #(in_delay) delay_RXGEARBOXSLIP = RXGEARBOXSLIP;
  assign #(in_delay) delay_RXLPMHFHOLD = RXLPMHFHOLD;
  assign #(in_delay) delay_RXLPMHFOVRDEN = RXLPMHFOVRDEN;
  assign #(in_delay) delay_RXLPMLFHOLD = RXLPMLFHOLD;
  assign #(in_delay) delay_RXLPMLFOVRDEN = RXLPMLFOVRDEN;
  assign #(in_delay) delay_RXLPMOSINTNTRLEN = RXLPMOSINTNTRLEN;
  assign #(in_delay) delay_RXLPMRESET = RXLPMRESET;
  assign #(in_delay) delay_RXMCOMMAALIGNEN = RXMCOMMAALIGNEN;
  assign #(in_delay) delay_RXOOBRESET = RXOOBRESET;
  assign #(in_delay) delay_RXOSCALRESET = RXOSCALRESET;
  assign #(in_delay) delay_RXOSHOLD = RXOSHOLD;
  assign #(in_delay) delay_RXOSINTCFG = RXOSINTCFG;
  assign #(in_delay) delay_RXOSINTEN = RXOSINTEN;
  assign #(in_delay) delay_RXOSINTHOLD = RXOSINTHOLD;
  assign #(in_delay) delay_RXOSINTID0 = RXOSINTID0;
  assign #(in_delay) delay_RXOSINTNTRLEN = RXOSINTNTRLEN;
  assign #(in_delay) delay_RXOSINTOVRDEN = RXOSINTOVRDEN;
  assign #(in_delay) delay_RXOSINTPD = RXOSINTPD;
  assign #(in_delay) delay_RXOSINTSTROBE = RXOSINTSTROBE;
  assign #(in_delay) delay_RXOSINTTESTOVRDEN = RXOSINTTESTOVRDEN;
  assign #(in_delay) delay_RXOSOVRDEN = RXOSOVRDEN;
  assign #(in_delay) delay_RXOUTCLKSEL = RXOUTCLKSEL;
  assign #(in_delay) delay_RXPCOMMAALIGNEN = RXPCOMMAALIGNEN;
  assign #(in_delay) delay_RXPCSRESET = RXPCSRESET;
  assign #(in_delay) delay_RXPD = RXPD;
  assign #(in_delay) delay_RXPHALIGN = RXPHALIGN;
  assign #(in_delay) delay_RXPHALIGNEN = RXPHALIGNEN;
  assign #(in_delay) delay_RXPHDLYPD = RXPHDLYPD;
  assign #(in_delay) delay_RXPHDLYRESET = RXPHDLYRESET;
  assign #(in_delay) delay_RXPHOVRDEN = RXPHOVRDEN;
  assign #(in_delay) delay_RXPMARESET = RXPMARESET;
  assign #(in_delay) delay_RXPOLARITY = RXPOLARITY;
  assign #(in_delay) delay_RXPRBSCNTRESET = RXPRBSCNTRESET;
  assign #(in_delay) delay_RXPRBSSEL = RXPRBSSEL;
  assign #(in_delay) delay_RXRATE = RXRATE;
  assign #(in_delay) delay_RXRATEMODE = RXRATEMODE;
  assign #(in_delay) delay_RXSLIDE = RXSLIDE;
  assign #(in_delay) delay_RXSYNCALLIN = RXSYNCALLIN;
  assign #(in_delay) delay_RXSYNCIN = RXSYNCIN;
  assign #(in_delay) delay_RXSYNCMODE = RXSYNCMODE;
  assign #(in_delay) delay_RXSYSCLKSEL = RXSYSCLKSEL;
  assign #(in_delay) delay_RXUSERRDY = RXUSERRDY;
  assign #(in_delay) delay_SETERRSTATUS = SETERRSTATUS;
  assign #(in_delay) delay_TSTIN = TSTIN;
  assign #(in_delay) delay_TX8B10BBYPASS = TX8B10BBYPASS;
  assign #(in_delay) delay_TX8B10BEN = TX8B10BEN;
  assign #(in_delay) delay_TXBUFDIFFCTRL = TXBUFDIFFCTRL;
  assign #(in_delay) delay_TXCHARDISPMODE = TXCHARDISPMODE;
  assign #(in_delay) delay_TXCHARDISPVAL = TXCHARDISPVAL;
  assign #(in_delay) delay_TXCHARISK = TXCHARISK;
  assign #(in_delay) delay_TXCOMINIT = TXCOMINIT;
  assign #(in_delay) delay_TXCOMSAS = TXCOMSAS;
  assign #(in_delay) delay_TXCOMWAKE = TXCOMWAKE;
  assign #(in_delay) delay_TXDATA = TXDATA;
  assign #(in_delay) delay_TXDEEMPH = TXDEEMPH;
  assign #(in_delay) delay_TXDETECTRX = TXDETECTRX;
  assign #(in_delay) delay_TXDIFFCTRL = TXDIFFCTRL;
  assign #(in_delay) delay_TXDIFFPD = TXDIFFPD;
  assign #(in_delay) delay_TXDLYBYPASS = TXDLYBYPASS;
  assign #(in_delay) delay_TXDLYEN = TXDLYEN;
  assign #(in_delay) delay_TXDLYHOLD = TXDLYHOLD;
  assign #(in_delay) delay_TXDLYOVRDEN = TXDLYOVRDEN;
  assign #(in_delay) delay_TXDLYSRESET = TXDLYSRESET;
  assign #(in_delay) delay_TXDLYUPDOWN = TXDLYUPDOWN;
  assign #(in_delay) delay_TXELECIDLE = TXELECIDLE;
  assign #(in_delay) delay_TXHEADER = TXHEADER;
  assign #(in_delay) delay_TXINHIBIT = TXINHIBIT;
  assign #(in_delay) delay_TXMAINCURSOR = TXMAINCURSOR;
  assign #(in_delay) delay_TXMARGIN = TXMARGIN;
  assign #(in_delay) delay_TXOUTCLKSEL = TXOUTCLKSEL;
  assign #(in_delay) delay_TXPCSRESET = TXPCSRESET;
  assign #(in_delay) delay_TXPD = TXPD;
  assign #(in_delay) delay_TXPDELECIDLEMODE = TXPDELECIDLEMODE;
  assign #(in_delay) delay_TXPHALIGN = TXPHALIGN;
  assign #(in_delay) delay_TXPHALIGNEN = TXPHALIGNEN;
  assign #(in_delay) delay_TXPHDLYPD = TXPHDLYPD;
  assign #(in_delay) delay_TXPHDLYRESET = TXPHDLYRESET;
  assign #(in_delay) delay_TXPHINIT = TXPHINIT;
  assign #(in_delay) delay_TXPHOVRDEN = TXPHOVRDEN;
  assign #(in_delay) delay_TXPIPPMEN = TXPIPPMEN;
  assign #(in_delay) delay_TXPIPPMOVRDEN = TXPIPPMOVRDEN;
  assign #(in_delay) delay_TXPIPPMPD = TXPIPPMPD;
  assign #(in_delay) delay_TXPIPPMSEL = TXPIPPMSEL;
  assign #(in_delay) delay_TXPIPPMSTEPSIZE = TXPIPPMSTEPSIZE;
  assign #(in_delay) delay_TXPISOPD = TXPISOPD;
  assign #(in_delay) delay_TXPMARESET = TXPMARESET;
  assign #(in_delay) delay_TXPOLARITY = TXPOLARITY;
  assign #(in_delay) delay_TXPOSTCURSOR = TXPOSTCURSOR;
  assign #(in_delay) delay_TXPOSTCURSORINV = TXPOSTCURSORINV;
  assign #(in_delay) delay_TXPRBSFORCEERR = TXPRBSFORCEERR;
  assign #(in_delay) delay_TXPRBSSEL = TXPRBSSEL;
  assign #(in_delay) delay_TXPRECURSOR = TXPRECURSOR;
  assign #(in_delay) delay_TXPRECURSORINV = TXPRECURSORINV;
  assign #(in_delay) delay_TXRATE = TXRATE;
  assign #(in_delay) delay_TXRATEMODE = TXRATEMODE;
  assign #(in_delay) delay_TXSEQUENCE = TXSEQUENCE;
  assign #(in_delay) delay_TXSTARTSEQ = TXSTARTSEQ;
  assign #(in_delay) delay_TXSWING = TXSWING;
  assign #(in_delay) delay_TXSYNCALLIN = TXSYNCALLIN;
  assign #(in_delay) delay_TXSYNCIN = TXSYNCIN;
  assign #(in_delay) delay_TXSYNCMODE = TXSYNCMODE;
  assign #(in_delay) delay_TXSYSCLKSEL = TXSYSCLKSEL;
  assign #(in_delay) delay_TXUSERRDY = TXUSERRDY;
`endif //  `ifndef XIL_TIMING

`ifdef XIL_TIMING //Simprim
  assign delay_CFGRESET = CFGRESET;
  assign delay_CLKRSVD0 = CLKRSVD0;
  assign delay_CLKRSVD1 = CLKRSVD1;
  assign delay_DMONFIFORESET = DMONFIFORESET;
  assign delay_DMONITORCLK = DMONITORCLK;
  assign delay_EYESCANMODE = EYESCANMODE;
  assign delay_EYESCANRESET = EYESCANRESET;
  assign delay_EYESCANTRIGGER = EYESCANTRIGGER;
  assign delay_GTPRXN = GTPRXN;
  assign delay_GTPRXP = GTPRXP;
  assign delay_GTRESETSEL = GTRESETSEL;
  assign delay_GTRSVD = GTRSVD;
  assign delay_GTRXRESET = GTRXRESET;
  assign delay_GTTXRESET = GTTXRESET;
  assign delay_LOOPBACK = LOOPBACK;
  assign delay_PCSRSVDIN = PCSRSVDIN;
  assign delay_PLL0CLK = PLL0CLK;
  assign delay_PLL0REFCLK = PLL0REFCLK;
  assign delay_PLL1CLK = PLL1CLK;
  assign delay_PLL1REFCLK = PLL1REFCLK;
  assign delay_PMARSVDIN0 = PMARSVDIN0;
  assign delay_PMARSVDIN1 = PMARSVDIN1;
  assign delay_PMARSVDIN2 = PMARSVDIN2;
  assign delay_PMARSVDIN3 = PMARSVDIN3;
  assign delay_PMARSVDIN4 = PMARSVDIN4;
  assign delay_RESETOVRD = RESETOVRD;
  assign delay_RXADAPTSELTEST = RXADAPTSELTEST;
  assign delay_RXBUFRESET = RXBUFRESET;
  assign delay_RXCDRFREQRESET = RXCDRFREQRESET;
  assign delay_RXCDRHOLD = RXCDRHOLD;
  assign delay_RXCDROVRDEN = RXCDROVRDEN;
  assign delay_RXCDRRESET = RXCDRRESET;
  assign delay_RXCDRRESETRSV = RXCDRRESETRSV;
  assign delay_RXCHBONDI = RXCHBONDI;
  assign delay_RXDDIEN = RXDDIEN;
  assign delay_RXDFEXYDEN = RXDFEXYDEN;
  assign delay_RXDLYBYPASS = RXDLYBYPASS;
  assign delay_RXDLYEN = RXDLYEN;
  assign delay_RXDLYOVRDEN = RXDLYOVRDEN;
  assign delay_RXDLYSRESET = RXDLYSRESET;
  assign delay_RXELECIDLEMODE = RXELECIDLEMODE;
  assign delay_RXLPMHFHOLD = RXLPMHFHOLD;
  assign delay_RXLPMHFOVRDEN = RXLPMHFOVRDEN;
  assign delay_RXLPMLFHOLD = RXLPMLFHOLD;
  assign delay_RXLPMLFOVRDEN = RXLPMLFOVRDEN;
  assign delay_RXLPMOSINTNTRLEN = RXLPMOSINTNTRLEN;
  assign delay_RXLPMRESET = RXLPMRESET;
  assign delay_RXOOBRESET = RXOOBRESET;
  assign delay_RXOSCALRESET = RXOSCALRESET;
  assign delay_RXOSHOLD = RXOSHOLD;
  assign delay_RXOSINTCFG = RXOSINTCFG;
  assign delay_RXOSINTEN = RXOSINTEN;
  assign delay_RXOSINTHOLD = RXOSINTHOLD;
  assign delay_RXOSINTID0 = RXOSINTID0;
  assign delay_RXOSINTNTRLEN = RXOSINTNTRLEN;
  assign delay_RXOSINTOVRDEN = RXOSINTOVRDEN;
  assign delay_RXOSINTPD = RXOSINTPD;
  assign delay_RXOSINTSTROBE = RXOSINTSTROBE;
  assign delay_RXOSINTTESTOVRDEN = RXOSINTTESTOVRDEN;
  assign delay_RXOSOVRDEN = RXOSOVRDEN;
  assign delay_RXOUTCLKSEL = RXOUTCLKSEL;
  assign delay_RXPCSRESET = RXPCSRESET;
  assign delay_RXPD = RXPD;
  assign delay_RXPHALIGN = RXPHALIGN;
  assign delay_RXPHALIGNEN = RXPHALIGNEN;
  assign delay_RXPHDLYPD = RXPHDLYPD;
  assign delay_RXPHDLYRESET = RXPHDLYRESET;
  assign delay_RXPHOVRDEN = RXPHOVRDEN;
  assign delay_RXPMARESET = RXPMARESET;
  assign delay_RXRATEMODE = RXRATEMODE;
  assign delay_RXSYNCALLIN = RXSYNCALLIN;
  assign delay_RXSYNCIN = RXSYNCIN;
  assign delay_RXSYNCMODE = RXSYNCMODE;
  assign delay_RXSYSCLKSEL = RXSYSCLKSEL;
  assign delay_RXUSERRDY = RXUSERRDY;
  assign delay_SIGVALIDCLK = SIGVALIDCLK;
  assign delay_TSTIN = TSTIN;
  assign delay_TXBUFDIFFCTRL = TXBUFDIFFCTRL;
  assign delay_TXDEEMPH = TXDEEMPH;
  assign delay_TXDIFFCTRL = TXDIFFCTRL;
  assign delay_TXDIFFPD = TXDIFFPD;
  assign delay_TXDLYBYPASS = TXDLYBYPASS;
  assign delay_TXDLYEN = TXDLYEN;
  assign delay_TXDLYOVRDEN = TXDLYOVRDEN;
  assign delay_TXDLYSRESET = TXDLYSRESET;
  assign delay_TXMAINCURSOR = TXMAINCURSOR;
  assign delay_TXMARGIN = TXMARGIN;
  assign delay_TXOUTCLKSEL = TXOUTCLKSEL;
  assign delay_TXPCSRESET = TXPCSRESET;
  assign delay_TXPDELECIDLEMODE = TXPDELECIDLEMODE;
  assign delay_TXPHALIGN = TXPHALIGN;
  assign delay_TXPHALIGNEN = TXPHALIGNEN;
  assign delay_TXPHDLYPD = TXPHDLYPD;
  assign delay_TXPHDLYRESET = TXPHDLYRESET;
  assign delay_TXPHINIT = TXPHINIT;
  assign delay_TXPHOVRDEN = TXPHOVRDEN;
  assign delay_TXPIPPMOVRDEN = TXPIPPMOVRDEN;
  assign delay_TXPIPPMPD = TXPIPPMPD;
  assign delay_TXPIPPMSEL = TXPIPPMSEL;
  assign delay_TXPISOPD = TXPISOPD;
  assign delay_TXPMARESET = TXPMARESET;
  assign delay_TXPOSTCURSOR = TXPOSTCURSOR;
  assign delay_TXPOSTCURSORINV = TXPOSTCURSORINV;
  assign delay_TXPRECURSOR = TXPRECURSOR;
  assign delay_TXPRECURSORINV = TXPRECURSORINV;
  assign delay_TXRATEMODE = TXRATEMODE;
  assign delay_TXSWING = TXSWING;
  assign delay_TXSYNCALLIN = TXSYNCALLIN;
  assign delay_TXSYNCIN = TXSYNCIN;
  assign delay_TXSYNCMODE = TXSYNCMODE;
  assign delay_TXSYSCLKSEL = TXSYSCLKSEL;
  assign delay_TXUSERRDY = TXUSERRDY;

  wire drpclk_en_p;
  wire drpclk_en_n;
  wire rxusrclk2_en_p;
  wire rxusrclk2_en_n;
  wire rxusrclk_en_p;
  wire rxusrclk_en_n;
  wire txphdlytstclk_en_p;
  wire txphdlytstclk_en_n;
  wire txusrclk2_en_p;
  wire txusrclk2_en_n;
  wire txusrclk_en_p;
  wire txusrclk_en_n;

  assign drpclk_en_p = ~IS_DRPCLK_INVERTED;
  assign drpclk_en_n = IS_DRPCLK_INVERTED;
  assign rxusrclk2_en_p = ~IS_RXUSRCLK2_INVERTED;
  assign rxusrclk2_en_n = IS_RXUSRCLK2_INVERTED;
  assign rxusrclk_en_p = ~IS_RXUSRCLK_INVERTED;
  assign rxusrclk_en_n = IS_RXUSRCLK_INVERTED;
  assign txphdlytstclk_en_p = ~IS_TXPHDLYTSTCLK_INVERTED;
  assign txphdlytstclk_en_n = IS_TXPHDLYTSTCLK_INVERTED;
  assign txusrclk2_en_p = ~IS_TXUSRCLK2_INVERTED;
  assign txusrclk2_en_n = IS_TXUSRCLK2_INVERTED;
  assign txusrclk_en_p = ~IS_TXUSRCLK_INVERTED;
  assign txusrclk_en_n = IS_TXUSRCLK_INVERTED;
`endif

  B_GTPE2_CHANNEL #(
    .ACJTAG_DEBUG_MODE (ACJTAG_DEBUG_MODE),
    .ACJTAG_MODE (ACJTAG_MODE),
    .ACJTAG_RESET (ACJTAG_RESET),
    .ADAPT_CFG0 (ADAPT_CFG0),
    .ALIGN_COMMA_DOUBLE (ALIGN_COMMA_DOUBLE),
    .ALIGN_COMMA_ENABLE (ALIGN_COMMA_ENABLE),
    .ALIGN_COMMA_WORD (ALIGN_COMMA_WORD),
    .ALIGN_MCOMMA_DET (ALIGN_MCOMMA_DET),
    .ALIGN_MCOMMA_VALUE (ALIGN_MCOMMA_VALUE),
    .ALIGN_PCOMMA_DET (ALIGN_PCOMMA_DET),
    .ALIGN_PCOMMA_VALUE (ALIGN_PCOMMA_VALUE),
    .CBCC_DATA_SOURCE_SEL (CBCC_DATA_SOURCE_SEL),
    .CFOK_CFG (CFOK_CFG),
    .CFOK_CFG2 (CFOK_CFG2),
    .CFOK_CFG3 (CFOK_CFG3),
    .CFOK_CFG4 (CFOK_CFG4),
    .CFOK_CFG5 (CFOK_CFG5),
    .CFOK_CFG6 (CFOK_CFG6),
    .CHAN_BOND_KEEP_ALIGN (CHAN_BOND_KEEP_ALIGN),
    .CHAN_BOND_MAX_SKEW (CHAN_BOND_MAX_SKEW),
    .CHAN_BOND_SEQ_1_1 (CHAN_BOND_SEQ_1_1),
    .CHAN_BOND_SEQ_1_2 (CHAN_BOND_SEQ_1_2),
    .CHAN_BOND_SEQ_1_3 (CHAN_BOND_SEQ_1_3),
    .CHAN_BOND_SEQ_1_4 (CHAN_BOND_SEQ_1_4),
    .CHAN_BOND_SEQ_1_ENABLE (CHAN_BOND_SEQ_1_ENABLE),
    .CHAN_BOND_SEQ_2_1 (CHAN_BOND_SEQ_2_1),
    .CHAN_BOND_SEQ_2_2 (CHAN_BOND_SEQ_2_2),
    .CHAN_BOND_SEQ_2_3 (CHAN_BOND_SEQ_2_3),
    .CHAN_BOND_SEQ_2_4 (CHAN_BOND_SEQ_2_4),
    .CHAN_BOND_SEQ_2_ENABLE (CHAN_BOND_SEQ_2_ENABLE),
    .CHAN_BOND_SEQ_2_USE (CHAN_BOND_SEQ_2_USE),
    .CHAN_BOND_SEQ_LEN (CHAN_BOND_SEQ_LEN),
    .CLK_COMMON_SWING (CLK_COMMON_SWING),
    .CLK_CORRECT_USE (CLK_CORRECT_USE),
    .CLK_COR_KEEP_IDLE (CLK_COR_KEEP_IDLE),
    .CLK_COR_MAX_LAT (CLK_COR_MAX_LAT),
    .CLK_COR_MIN_LAT (CLK_COR_MIN_LAT),
    .CLK_COR_PRECEDENCE (CLK_COR_PRECEDENCE),
    .CLK_COR_REPEAT_WAIT (CLK_COR_REPEAT_WAIT),
    .CLK_COR_SEQ_1_1 (CLK_COR_SEQ_1_1),
    .CLK_COR_SEQ_1_2 (CLK_COR_SEQ_1_2),
    .CLK_COR_SEQ_1_3 (CLK_COR_SEQ_1_3),
    .CLK_COR_SEQ_1_4 (CLK_COR_SEQ_1_4),
    .CLK_COR_SEQ_1_ENABLE (CLK_COR_SEQ_1_ENABLE),
    .CLK_COR_SEQ_2_1 (CLK_COR_SEQ_2_1),
    .CLK_COR_SEQ_2_2 (CLK_COR_SEQ_2_2),
    .CLK_COR_SEQ_2_3 (CLK_COR_SEQ_2_3),
    .CLK_COR_SEQ_2_4 (CLK_COR_SEQ_2_4),
    .CLK_COR_SEQ_2_ENABLE (CLK_COR_SEQ_2_ENABLE),
    .CLK_COR_SEQ_2_USE (CLK_COR_SEQ_2_USE),
    .CLK_COR_SEQ_LEN (CLK_COR_SEQ_LEN),
    .DEC_MCOMMA_DETECT (DEC_MCOMMA_DETECT),
    .DEC_PCOMMA_DETECT (DEC_PCOMMA_DETECT),
    .DEC_VALID_COMMA_ONLY (DEC_VALID_COMMA_ONLY),
    .DMONITOR_CFG (DMONITOR_CFG),
    .ES_CLK_PHASE_SEL (ES_CLK_PHASE_SEL),
    .ES_CONTROL (ES_CONTROL),
    .ES_ERRDET_EN (ES_ERRDET_EN),
    .ES_EYE_SCAN_EN (ES_EYE_SCAN_EN),
    .ES_HORZ_OFFSET (ES_HORZ_OFFSET),
    .ES_PMA_CFG (ES_PMA_CFG),
    .ES_PRESCALE (ES_PRESCALE),
    .ES_QUALIFIER (ES_QUALIFIER),
    .ES_QUAL_MASK (ES_QUAL_MASK),
    .ES_SDATA_MASK (ES_SDATA_MASK),
    .ES_VERT_OFFSET (ES_VERT_OFFSET),
    .FTS_DESKEW_SEQ_ENABLE (FTS_DESKEW_SEQ_ENABLE),
    .FTS_LANE_DESKEW_CFG (FTS_LANE_DESKEW_CFG),
    .FTS_LANE_DESKEW_EN (FTS_LANE_DESKEW_EN),
    .GEARBOX_MODE (GEARBOX_MODE),
    .LOOPBACK_CFG (LOOPBACK_CFG),
    .OUTREFCLK_SEL_INV (OUTREFCLK_SEL_INV),
    .PCS_PCIE_EN (PCS_PCIE_EN),
    .PCS_RSVD_ATTR (PCS_RSVD_ATTR),
    .PD_TRANS_TIME_FROM_P2 (PD_TRANS_TIME_FROM_P2),
    .PD_TRANS_TIME_NONE_P2 (PD_TRANS_TIME_NONE_P2),
    .PD_TRANS_TIME_TO_P2 (PD_TRANS_TIME_TO_P2),
    .PMA_LOOPBACK_CFG (PMA_LOOPBACK_CFG),
    .PMA_RSV (PMA_RSV),
    .PMA_RSV2 (PMA_RSV2),
    .PMA_RSV3 (PMA_RSV3),
    .PMA_RSV4 (PMA_RSV4),
    .PMA_RSV5 (PMA_RSV5),
    .PMA_RSV6 (PMA_RSV6),
    .PMA_RSV7 (PMA_RSV7),
    .RXBUFRESET_TIME (RXBUFRESET_TIME),
    .RXBUF_ADDR_MODE (RXBUF_ADDR_MODE),
    .RXBUF_EIDLE_HI_CNT (RXBUF_EIDLE_HI_CNT),
    .RXBUF_EIDLE_LO_CNT (RXBUF_EIDLE_LO_CNT),
    .RXBUF_EN (RXBUF_EN),
    .RXBUF_RESET_ON_CB_CHANGE (RXBUF_RESET_ON_CB_CHANGE),
    .RXBUF_RESET_ON_COMMAALIGN (RXBUF_RESET_ON_COMMAALIGN),
    .RXBUF_RESET_ON_EIDLE (RXBUF_RESET_ON_EIDLE),
    .RXBUF_RESET_ON_RATE_CHANGE (RXBUF_RESET_ON_RATE_CHANGE),
    .RXBUF_THRESH_OVFLW (RXBUF_THRESH_OVFLW),
    .RXBUF_THRESH_OVRD (RXBUF_THRESH_OVRD),
    .RXBUF_THRESH_UNDFLW (RXBUF_THRESH_UNDFLW),
    .RXCDRFREQRESET_TIME (RXCDRFREQRESET_TIME),
    .RXCDRPHRESET_TIME (RXCDRPHRESET_TIME),
    .RXCDR_CFG (RXCDR_CFG),
    .RXCDR_FR_RESET_ON_EIDLE (RXCDR_FR_RESET_ON_EIDLE),
    .RXCDR_HOLD_DURING_EIDLE (RXCDR_HOLD_DURING_EIDLE),
    .RXCDR_LOCK_CFG (RXCDR_LOCK_CFG),
    .RXCDR_PH_RESET_ON_EIDLE (RXCDR_PH_RESET_ON_EIDLE),
    .RXDLY_CFG (RXDLY_CFG),
    .RXDLY_LCFG (RXDLY_LCFG),
    .RXDLY_TAP_CFG (RXDLY_TAP_CFG),
    .RXGEARBOX_EN (RXGEARBOX_EN),
    .RXISCANRESET_TIME (RXISCANRESET_TIME),
    .RXLPMRESET_TIME (RXLPMRESET_TIME),
    .RXLPM_BIAS_STARTUP_DISABLE (RXLPM_BIAS_STARTUP_DISABLE),
    .RXLPM_CFG (RXLPM_CFG),
    .RXLPM_CFG1 (RXLPM_CFG1),
    .RXLPM_CM_CFG (RXLPM_CM_CFG),
    .RXLPM_GC_CFG (RXLPM_GC_CFG),
    .RXLPM_GC_CFG2 (RXLPM_GC_CFG2),
    .RXLPM_HF_CFG (RXLPM_HF_CFG),
    .RXLPM_HF_CFG2 (RXLPM_HF_CFG2),
    .RXLPM_HF_CFG3 (RXLPM_HF_CFG3),
    .RXLPM_HOLD_DURING_EIDLE (RXLPM_HOLD_DURING_EIDLE),
    .RXLPM_INCM_CFG (RXLPM_INCM_CFG),
    .RXLPM_IPCM_CFG (RXLPM_IPCM_CFG),
    .RXLPM_LF_CFG (RXLPM_LF_CFG),
    .RXLPM_LF_CFG2 (RXLPM_LF_CFG2),
    .RXLPM_OSINT_CFG (RXLPM_OSINT_CFG),
    .RXOOB_CFG (RXOOB_CFG),
    .RXOOB_CLK_CFG (RXOOB_CLK_CFG),
    .RXOSCALRESET_TIME (RXOSCALRESET_TIME),
    .RXOSCALRESET_TIMEOUT (RXOSCALRESET_TIMEOUT),
    .RXOUT_DIV (RXOUT_DIV),
    .RXPCSRESET_TIME (RXPCSRESET_TIME),
    .RXPHDLY_CFG (RXPHDLY_CFG),
    .RXPH_CFG (RXPH_CFG),
    .RXPH_MONITOR_SEL (RXPH_MONITOR_SEL),
    .RXPI_CFG0 (RXPI_CFG0),
    .RXPI_CFG1 (RXPI_CFG1),
    .RXPI_CFG2 (RXPI_CFG2),
    .RXPMARESET_TIME (RXPMARESET_TIME),
    .RXPRBS_ERR_LOOPBACK (RXPRBS_ERR_LOOPBACK),
    .RXSLIDE_AUTO_WAIT (RXSLIDE_AUTO_WAIT),
    .RXSLIDE_MODE (RXSLIDE_MODE),
    .RXSYNC_MULTILANE (RXSYNC_MULTILANE),
    .RXSYNC_OVRD (RXSYNC_OVRD),
    .RXSYNC_SKIP_DA (RXSYNC_SKIP_DA),
    .RX_BIAS_CFG (RX_BIAS_CFG),
    .RX_BUFFER_CFG (RX_BUFFER_CFG),
    .RX_CLK25_DIV (RX_CLK25_DIV),
    .RX_CLKMUX_EN (RX_CLKMUX_EN),
    .RX_CM_SEL (RX_CM_SEL),
    .RX_CM_TRIM (RX_CM_TRIM),
    .RX_DATA_WIDTH (RX_DATA_WIDTH),
    .RX_DDI_SEL (RX_DDI_SEL),
    .RX_DEBUG_CFG (RX_DEBUG_CFG),
    .RX_DEFER_RESET_BUF_EN (RX_DEFER_RESET_BUF_EN),
    .RX_DISPERR_SEQ_MATCH (RX_DISPERR_SEQ_MATCH),
    .RX_OS_CFG (RX_OS_CFG),
    .RX_SIG_VALID_DLY (RX_SIG_VALID_DLY),
    .RX_XCLK_SEL (RX_XCLK_SEL),
    .SAS_MAX_COM (SAS_MAX_COM),
    .SAS_MIN_COM (SAS_MIN_COM),
    .SATA_BURST_SEQ_LEN (SATA_BURST_SEQ_LEN),
    .SATA_BURST_VAL (SATA_BURST_VAL),
    .SATA_EIDLE_VAL (SATA_EIDLE_VAL),
    .SATA_MAX_BURST (SATA_MAX_BURST),
    .SATA_MAX_INIT (SATA_MAX_INIT),
    .SATA_MAX_WAKE (SATA_MAX_WAKE),
    .SATA_MIN_BURST (SATA_MIN_BURST),
    .SATA_MIN_INIT (SATA_MIN_INIT),
    .SATA_MIN_WAKE (SATA_MIN_WAKE),
    .SATA_PLL_CFG (SATA_PLL_CFG),
    .SHOW_REALIGN_COMMA (SHOW_REALIGN_COMMA),
    .SIM_RECEIVER_DETECT_PASS (SIM_RECEIVER_DETECT_PASS),
    .SIM_RESET_SPEEDUP (SIM_RESET_SPEEDUP),
    .SIM_TX_EIDLE_DRIVE_LEVEL (SIM_TX_EIDLE_DRIVE_LEVEL),
    .SIM_VERSION (SIM_VERSION),
    .TERM_RCAL_CFG (TERM_RCAL_CFG),
    .TERM_RCAL_OVRD (TERM_RCAL_OVRD),
    .TRANS_TIME_RATE (TRANS_TIME_RATE),
    .TST_RSV (TST_RSV),
    .TXBUF_EN (TXBUF_EN),
    .TXBUF_RESET_ON_RATE_CHANGE (TXBUF_RESET_ON_RATE_CHANGE),
    .TXDLY_CFG (TXDLY_CFG),
    .TXDLY_LCFG (TXDLY_LCFG),
    .TXDLY_TAP_CFG (TXDLY_TAP_CFG),
    .TXGEARBOX_EN (TXGEARBOX_EN),
    .TXOOB_CFG (TXOOB_CFG),
    .TXOUT_DIV (TXOUT_DIV),
    .TXPCSRESET_TIME (TXPCSRESET_TIME),
    .TXPHDLY_CFG (TXPHDLY_CFG),
    .TXPH_CFG (TXPH_CFG),
    .TXPH_MONITOR_SEL (TXPH_MONITOR_SEL),
    .TXPI_CFG0 (TXPI_CFG0),
    .TXPI_CFG1 (TXPI_CFG1),
    .TXPI_CFG2 (TXPI_CFG2),
    .TXPI_CFG3 (TXPI_CFG3),
    .TXPI_CFG4 (TXPI_CFG4),
    .TXPI_CFG5 (TXPI_CFG5),
    .TXPI_GREY_SEL (TXPI_GREY_SEL),
    .TXPI_INVSTROBE_SEL (TXPI_INVSTROBE_SEL),
    .TXPI_PPMCLK_SEL (TXPI_PPMCLK_SEL),
    .TXPI_PPM_CFG (TXPI_PPM_CFG),
    .TXPI_SYNFREQ_PPM (TXPI_SYNFREQ_PPM),
    .TXPMARESET_TIME (TXPMARESET_TIME),
    .TXSYNC_MULTILANE (TXSYNC_MULTILANE),
    .TXSYNC_OVRD (TXSYNC_OVRD),
    .TXSYNC_SKIP_DA (TXSYNC_SKIP_DA),
    .TX_CLK25_DIV (TX_CLK25_DIV),
    .TX_CLKMUX_EN (TX_CLKMUX_EN),
    .TX_DATA_WIDTH (TX_DATA_WIDTH),
    .TX_DEEMPH0 (TX_DEEMPH0),
    .TX_DEEMPH1 (TX_DEEMPH1),
    .TX_DRIVE_MODE (TX_DRIVE_MODE),
    .TX_EIDLE_ASSERT_DELAY (TX_EIDLE_ASSERT_DELAY),
    .TX_EIDLE_DEASSERT_DELAY (TX_EIDLE_DEASSERT_DELAY),
    .TX_LOOPBACK_DRIVE_HIZ (TX_LOOPBACK_DRIVE_HIZ),
    .TX_MAINCURSOR_SEL (TX_MAINCURSOR_SEL),
    .TX_MARGIN_FULL_0 (TX_MARGIN_FULL_0),
    .TX_MARGIN_FULL_1 (TX_MARGIN_FULL_1),
    .TX_MARGIN_FULL_2 (TX_MARGIN_FULL_2),
    .TX_MARGIN_FULL_3 (TX_MARGIN_FULL_3),
    .TX_MARGIN_FULL_4 (TX_MARGIN_FULL_4),
    .TX_MARGIN_LOW_0 (TX_MARGIN_LOW_0),
    .TX_MARGIN_LOW_1 (TX_MARGIN_LOW_1),
    .TX_MARGIN_LOW_2 (TX_MARGIN_LOW_2),
    .TX_MARGIN_LOW_3 (TX_MARGIN_LOW_3),
    .TX_MARGIN_LOW_4 (TX_MARGIN_LOW_4),
    .TX_PREDRIVER_MODE (TX_PREDRIVER_MODE),
    .TX_RXDETECT_CFG (TX_RXDETECT_CFG),
    .TX_RXDETECT_REF (TX_RXDETECT_REF),
    .TX_XCLK_SEL (TX_XCLK_SEL),
    .UCODEER_CLR (UCODEER_CLR),
    .USE_PCS_CLK_PHASE_SEL (USE_PCS_CLK_PHASE_SEL))

    B_GTPE2_CHANNEL_INST (
    .DMONITOROUT (delay_DMONITOROUT),
    .DRPDO (delay_DRPDO),
    .DRPRDY (delay_DRPRDY),
    .EYESCANDATAERROR (delay_EYESCANDATAERROR),
    .GTPTXN (delay_GTPTXN),
    .GTPTXP (delay_GTPTXP),
    .PCSRSVDOUT (delay_PCSRSVDOUT),
    .PHYSTATUS (delay_PHYSTATUS),
    .PMARSVDOUT0 (delay_PMARSVDOUT0),
    .PMARSVDOUT1 (delay_PMARSVDOUT1),
    .RXBUFSTATUS (delay_RXBUFSTATUS),
    .RXBYTEISALIGNED (delay_RXBYTEISALIGNED),
    .RXBYTEREALIGN (delay_RXBYTEREALIGN),
    .RXCDRLOCK (delay_RXCDRLOCK),
    .RXCHANBONDSEQ (delay_RXCHANBONDSEQ),
    .RXCHANISALIGNED (delay_RXCHANISALIGNED),
    .RXCHANREALIGN (delay_RXCHANREALIGN),
    .RXCHARISCOMMA (delay_RXCHARISCOMMA),
    .RXCHARISK (delay_RXCHARISK),
    .RXCHBONDO (delay_RXCHBONDO),
    .RXCLKCORCNT (delay_RXCLKCORCNT),
    .RXCOMINITDET (delay_RXCOMINITDET),
    .RXCOMMADET (delay_RXCOMMADET),
    .RXCOMSASDET (delay_RXCOMSASDET),
    .RXCOMWAKEDET (delay_RXCOMWAKEDET),
    .RXDATA (delay_RXDATA),
    .RXDATAVALID (delay_RXDATAVALID),
    .RXDISPERR (delay_RXDISPERR),
    .RXDLYSRESETDONE (delay_RXDLYSRESETDONE),
    .RXELECIDLE (delay_RXELECIDLE),
    .RXHEADER (delay_RXHEADER),
    .RXHEADERVALID (delay_RXHEADERVALID),
    .RXNOTINTABLE (delay_RXNOTINTABLE),
    .RXOSINTDONE (delay_RXOSINTDONE),
    .RXOSINTSTARTED (delay_RXOSINTSTARTED),
    .RXOSINTSTROBEDONE (delay_RXOSINTSTROBEDONE),
    .RXOSINTSTROBESTARTED (delay_RXOSINTSTROBESTARTED),
    .RXOUTCLK (delay_RXOUTCLK),
    .RXOUTCLKFABRIC (delay_RXOUTCLKFABRIC),
    .RXOUTCLKPCS (delay_RXOUTCLKPCS),
    .RXPHALIGNDONE (delay_RXPHALIGNDONE),
    .RXPHMONITOR (delay_RXPHMONITOR),
    .RXPHSLIPMONITOR (delay_RXPHSLIPMONITOR),
    .RXPMARESETDONE (delay_RXPMARESETDONE),
    .RXPRBSERR (delay_RXPRBSERR),
    .RXRATEDONE (delay_RXRATEDONE),
    .RXRESETDONE (delay_RXRESETDONE),
    .RXSTARTOFSEQ (delay_RXSTARTOFSEQ),
    .RXSTATUS (delay_RXSTATUS),
    .RXSYNCDONE (delay_RXSYNCDONE),
    .RXSYNCOUT (delay_RXSYNCOUT),
    .RXVALID (delay_RXVALID),
    .TXBUFSTATUS (delay_TXBUFSTATUS),
    .TXCOMFINISH (delay_TXCOMFINISH),
    .TXDLYSRESETDONE (delay_TXDLYSRESETDONE),
    .TXGEARBOXREADY (delay_TXGEARBOXREADY),
    .TXOUTCLK (delay_TXOUTCLK),
    .TXOUTCLKFABRIC (delay_TXOUTCLKFABRIC),
    .TXOUTCLKPCS (delay_TXOUTCLKPCS),
    .TXPHALIGNDONE (delay_TXPHALIGNDONE),
    .TXPHINITDONE (delay_TXPHINITDONE),
    .TXPMARESETDONE (delay_TXPMARESETDONE),
    .TXRATEDONE (delay_TXRATEDONE),
    .TXRESETDONE (delay_TXRESETDONE),
    .TXSYNCDONE (delay_TXSYNCDONE),
    .TXSYNCOUT (delay_TXSYNCOUT),
    .CFGRESET (delay_CFGRESET),
    .CLKRSVD0 (delay_CLKRSVD0),
    .CLKRSVD1 (delay_CLKRSVD1),
    .DMONFIFORESET (delay_DMONFIFORESET),
    .DMONITORCLK (delay_DMONITORCLK),
    .DRPADDR (delay_DRPADDR),
    .DRPCLK (delay_DRPCLK),
    .DRPDI (delay_DRPDI),
    .DRPEN (delay_DRPEN),
    .DRPWE (delay_DRPWE),
    .EYESCANMODE (delay_EYESCANMODE),
    .EYESCANRESET (delay_EYESCANRESET),
    .EYESCANTRIGGER (delay_EYESCANTRIGGER),
    .GTPRXN (delay_GTPRXN),
    .GTPRXP (delay_GTPRXP),
    .GTRESETSEL (delay_GTRESETSEL),
    .GTRSVD (delay_GTRSVD),
    .GTRXRESET (delay_GTRXRESET),
    .GTTXRESET (delay_GTTXRESET),
    .LOOPBACK (delay_LOOPBACK),
    .PCSRSVDIN (delay_PCSRSVDIN),
    .PLL0CLK (delay_PLL0CLK),
    .PLL0REFCLK (delay_PLL0REFCLK),
    .PLL1CLK (delay_PLL1CLK),
    .PLL1REFCLK (delay_PLL1REFCLK),
    .PMARSVDIN0 (delay_PMARSVDIN0),
    .PMARSVDIN1 (delay_PMARSVDIN1),
    .PMARSVDIN2 (delay_PMARSVDIN2),
    .PMARSVDIN3 (delay_PMARSVDIN3),
    .PMARSVDIN4 (delay_PMARSVDIN4),
    .RESETOVRD (delay_RESETOVRD),
    .RX8B10BEN (delay_RX8B10BEN),
    .RXADAPTSELTEST (delay_RXADAPTSELTEST),
    .RXBUFRESET (delay_RXBUFRESET),
    .RXCDRFREQRESET (delay_RXCDRFREQRESET),
    .RXCDRHOLD (delay_RXCDRHOLD),
    .RXCDROVRDEN (delay_RXCDROVRDEN),
    .RXCDRRESET (delay_RXCDRRESET),
    .RXCDRRESETRSV (delay_RXCDRRESETRSV),
    .RXCHBONDEN (delay_RXCHBONDEN),
    .RXCHBONDI (delay_RXCHBONDI),
    .RXCHBONDLEVEL (delay_RXCHBONDLEVEL),
    .RXCHBONDMASTER (delay_RXCHBONDMASTER),
    .RXCHBONDSLAVE (delay_RXCHBONDSLAVE),
    .RXCOMMADETEN (delay_RXCOMMADETEN),
    .RXDDIEN (delay_RXDDIEN),
    .RXDFEXYDEN (delay_RXDFEXYDEN),
    .RXDLYBYPASS (delay_RXDLYBYPASS),
    .RXDLYEN (delay_RXDLYEN),
    .RXDLYOVRDEN (delay_RXDLYOVRDEN),
    .RXDLYSRESET (delay_RXDLYSRESET),
    .RXELECIDLEMODE (delay_RXELECIDLEMODE),
    .RXGEARBOXSLIP (delay_RXGEARBOXSLIP),
    .RXLPMHFHOLD (delay_RXLPMHFHOLD),
    .RXLPMHFOVRDEN (delay_RXLPMHFOVRDEN),
    .RXLPMLFHOLD (delay_RXLPMLFHOLD),
    .RXLPMLFOVRDEN (delay_RXLPMLFOVRDEN),
    .RXLPMOSINTNTRLEN (delay_RXLPMOSINTNTRLEN),
    .RXLPMRESET (delay_RXLPMRESET),
    .RXMCOMMAALIGNEN (delay_RXMCOMMAALIGNEN),
    .RXOOBRESET (delay_RXOOBRESET),
    .RXOSCALRESET (delay_RXOSCALRESET),
    .RXOSHOLD (delay_RXOSHOLD),
    .RXOSINTCFG (delay_RXOSINTCFG),
    .RXOSINTEN (delay_RXOSINTEN),
    .RXOSINTHOLD (delay_RXOSINTHOLD),
    .RXOSINTID0 (delay_RXOSINTID0),
    .RXOSINTNTRLEN (delay_RXOSINTNTRLEN),
    .RXOSINTOVRDEN (delay_RXOSINTOVRDEN),
    .RXOSINTPD (delay_RXOSINTPD),
    .RXOSINTSTROBE (delay_RXOSINTSTROBE),
    .RXOSINTTESTOVRDEN (delay_RXOSINTTESTOVRDEN),
    .RXOSOVRDEN (delay_RXOSOVRDEN),
    .RXOUTCLKSEL (delay_RXOUTCLKSEL),
    .RXPCOMMAALIGNEN (delay_RXPCOMMAALIGNEN),
    .RXPCSRESET (delay_RXPCSRESET),
    .RXPD (delay_RXPD),
    .RXPHALIGN (delay_RXPHALIGN),
    .RXPHALIGNEN (delay_RXPHALIGNEN),
    .RXPHDLYPD (delay_RXPHDLYPD),
    .RXPHDLYRESET (delay_RXPHDLYRESET),
    .RXPHOVRDEN (delay_RXPHOVRDEN),
    .RXPMARESET (delay_RXPMARESET),
    .RXPOLARITY (delay_RXPOLARITY),
    .RXPRBSCNTRESET (delay_RXPRBSCNTRESET),
    .RXPRBSSEL (delay_RXPRBSSEL),
    .RXRATE (delay_RXRATE),
    .RXRATEMODE (delay_RXRATEMODE),
    .RXSLIDE (delay_RXSLIDE),
    .RXSYNCALLIN (delay_RXSYNCALLIN),
    .RXSYNCIN (delay_RXSYNCIN),
    .RXSYNCMODE (delay_RXSYNCMODE),
    .RXSYSCLKSEL (delay_RXSYSCLKSEL),
    .RXUSERRDY (delay_RXUSERRDY),
    .RXUSRCLK (delay_RXUSRCLK),
    .RXUSRCLK2 (delay_RXUSRCLK2),
    .SETERRSTATUS (delay_SETERRSTATUS),
    .SIGVALIDCLK (delay_SIGVALIDCLK),
    .TSTIN (delay_TSTIN),
    .TX8B10BBYPASS (delay_TX8B10BBYPASS),
    .TX8B10BEN (delay_TX8B10BEN),
    .TXBUFDIFFCTRL (delay_TXBUFDIFFCTRL),
    .TXCHARDISPMODE (delay_TXCHARDISPMODE),
    .TXCHARDISPVAL (delay_TXCHARDISPVAL),
    .TXCHARISK (delay_TXCHARISK),
    .TXCOMINIT (delay_TXCOMINIT),
    .TXCOMSAS (delay_TXCOMSAS),
    .TXCOMWAKE (delay_TXCOMWAKE),
    .TXDATA (delay_TXDATA),
    .TXDEEMPH (delay_TXDEEMPH),
    .TXDETECTRX (delay_TXDETECTRX),
    .TXDIFFCTRL (delay_TXDIFFCTRL),
    .TXDIFFPD (delay_TXDIFFPD),
    .TXDLYBYPASS (delay_TXDLYBYPASS),
    .TXDLYEN (delay_TXDLYEN),
    .TXDLYHOLD (delay_TXDLYHOLD),
    .TXDLYOVRDEN (delay_TXDLYOVRDEN),
    .TXDLYSRESET (delay_TXDLYSRESET),
    .TXDLYUPDOWN (delay_TXDLYUPDOWN),
    .TXELECIDLE (delay_TXELECIDLE),
    .TXHEADER (delay_TXHEADER),
    .TXINHIBIT (delay_TXINHIBIT),
    .TXMAINCURSOR (delay_TXMAINCURSOR),
    .TXMARGIN (delay_TXMARGIN),
    .TXOUTCLKSEL (delay_TXOUTCLKSEL),
    .TXPCSRESET (delay_TXPCSRESET),
    .TXPD (delay_TXPD),
    .TXPDELECIDLEMODE (delay_TXPDELECIDLEMODE),
    .TXPHALIGN (delay_TXPHALIGN),
    .TXPHALIGNEN (delay_TXPHALIGNEN),
    .TXPHDLYPD (delay_TXPHDLYPD),
    .TXPHDLYRESET (delay_TXPHDLYRESET),
    .TXPHDLYTSTCLK (delay_TXPHDLYTSTCLK),
    .TXPHINIT (delay_TXPHINIT),
    .TXPHOVRDEN (delay_TXPHOVRDEN),
    .TXPIPPMEN (delay_TXPIPPMEN),
    .TXPIPPMOVRDEN (delay_TXPIPPMOVRDEN),
    .TXPIPPMPD (delay_TXPIPPMPD),
    .TXPIPPMSEL (delay_TXPIPPMSEL),
    .TXPIPPMSTEPSIZE (delay_TXPIPPMSTEPSIZE),
    .TXPISOPD (delay_TXPISOPD),
    .TXPMARESET (delay_TXPMARESET),
    .TXPOLARITY (delay_TXPOLARITY),
    .TXPOSTCURSOR (delay_TXPOSTCURSOR),
    .TXPOSTCURSORINV (delay_TXPOSTCURSORINV),
    .TXPRBSFORCEERR (delay_TXPRBSFORCEERR),
    .TXPRBSSEL (delay_TXPRBSSEL),
    .TXPRECURSOR (delay_TXPRECURSOR),
    .TXPRECURSORINV (delay_TXPRECURSORINV),
    .TXRATE (delay_TXRATE),
    .TXRATEMODE (delay_TXRATEMODE),
    .TXSEQUENCE (delay_TXSEQUENCE),
    .TXSTARTSEQ (delay_TXSTARTSEQ),
    .TXSWING (delay_TXSWING),
    .TXSYNCALLIN (delay_TXSYNCALLIN),
    .TXSYNCIN (delay_TXSYNCIN),
    .TXSYNCMODE (delay_TXSYNCMODE),
    .TXSYSCLKSEL (delay_TXSYSCLKSEL),
    .TXUSERRDY (delay_TXUSERRDY),
    .TXUSRCLK (delay_TXUSRCLK),
    .TXUSRCLK2 (delay_TXUSRCLK2),
    .GSR (GSR)
  );

  specify
`ifdef XIL_TIMING // Simprim
    $period (posedge CLKRSVD0, 0:0:0, notifier);
    $period (negedge CLKRSVD0, 0:0:0, notifier);
    $period (posedge CLKRSVD1, 0:0:0, notifier);
    $period (negedge CLKRSVD1, 0:0:0, notifier);
    $period (posedge DMONITORCLK, 0:0:0, notifier);
    $period (negedge DMONITORCLK, 0:0:0, notifier);
    $period (posedge DRPCLK, 0:0:0, notifier);
    $period (negedge DRPCLK, 0:0:0, notifier);
    $period (posedge PLL0CLK, 0:0:0, notifier);
    $period (posedge PLL1CLK, 0:0:0, notifier);
    $period (posedge RXOUTCLK, 0:0:0, notifier);
    $period (posedge RXOUTCLKFABRIC, 0:0:0, notifier);
    $period (posedge RXOUTCLKPCS, 0:0:0, notifier);
    $period (posedge RXUSRCLK, 0:0:0, notifier);
    $period (negedge RXUSRCLK, 0:0:0, notifier);
    $period (posedge RXUSRCLK2, 0:0:0, notifier);
    $period (negedge RXUSRCLK2, 0:0:0, notifier);
    $period (posedge SIGVALIDCLK, 0:0:0, notifier);
    $period (negedge SIGVALIDCLK, 0:0:0, notifier);
    $period (posedge TXOUTCLK, 0:0:0, notifier);
    $period (posedge TXOUTCLKFABRIC, 0:0:0, notifier);
    $period (posedge TXOUTCLKPCS, 0:0:0, notifier);
    $period (posedge TXPHDLYTSTCLK, 0:0:0, notifier);
    $period (negedge TXPHDLYTSTCLK, 0:0:0, notifier);
    $period (posedge TXUSRCLK, 0:0:0, notifier);
    $period (negedge TXUSRCLK, 0:0:0, notifier);
    $period (posedge TXUSRCLK2, 0:0:0, notifier);
    $period (negedge TXUSRCLK2, 0:0:0, notifier);

    $setuphold (posedge DRPCLK, negedge DRPADDR, 0:0:0, 0:0:0, notifier, drpclk_en_p, drpclk_en_p, delay_DRPCLK, delay_DRPADDR);
    $setuphold (posedge DRPCLK, negedge DRPDI, 0:0:0, 0:0:0, notifier, drpclk_en_p, drpclk_en_p, delay_DRPCLK, delay_DRPDI);
    $setuphold (posedge DRPCLK, negedge DRPEN, 0:0:0, 0:0:0, notifier, drpclk_en_p, drpclk_en_p, delay_DRPCLK, delay_DRPEN);
    $setuphold (posedge DRPCLK, negedge DRPWE, 0:0:0, 0:0:0, notifier, drpclk_en_p, drpclk_en_p, delay_DRPCLK, delay_DRPWE);
    $setuphold (posedge DRPCLK, posedge DRPADDR, 0:0:0, 0:0:0, notifier, drpclk_en_p, drpclk_en_p, delay_DRPCLK, delay_DRPADDR);
    $setuphold (posedge DRPCLK, posedge DRPDI, 0:0:0, 0:0:0, notifier, drpclk_en_p, drpclk_en_p, delay_DRPCLK, delay_DRPDI);
    $setuphold (posedge DRPCLK, posedge DRPEN, 0:0:0, 0:0:0, notifier, drpclk_en_p, drpclk_en_p, delay_DRPCLK, delay_DRPEN);
    $setuphold (posedge DRPCLK, posedge DRPWE, 0:0:0, 0:0:0, notifier, drpclk_en_p, drpclk_en_p, delay_DRPCLK, delay_DRPWE);
    $setuphold (negedge DRPCLK, negedge DRPADDR, 0:0:0, 0:0:0, notifier, drpclk_en_n, drpclk_en_n, delay_DRPCLK, delay_DRPADDR);
    $setuphold (negedge DRPCLK, negedge DRPDI, 0:0:0, 0:0:0, notifier, drpclk_en_n, drpclk_en_n, delay_DRPCLK, delay_DRPDI);
    $setuphold (negedge DRPCLK, negedge DRPEN, 0:0:0, 0:0:0, notifier, drpclk_en_n, drpclk_en_n, delay_DRPCLK, delay_DRPEN);
    $setuphold (negedge DRPCLK, negedge DRPWE, 0:0:0, 0:0:0, notifier, drpclk_en_n, drpclk_en_n, delay_DRPCLK, delay_DRPWE);
    $setuphold (negedge DRPCLK, posedge DRPADDR, 0:0:0, 0:0:0, notifier, drpclk_en_n, drpclk_en_n, delay_DRPCLK, delay_DRPADDR);
    $setuphold (negedge DRPCLK, posedge DRPDI, 0:0:0, 0:0:0, notifier, drpclk_en_n, drpclk_en_n, delay_DRPCLK, delay_DRPDI);
    $setuphold (negedge DRPCLK, posedge DRPEN, 0:0:0, 0:0:0, notifier, drpclk_en_n, drpclk_en_n, delay_DRPCLK, delay_DRPEN);
    $setuphold (negedge DRPCLK, posedge DRPWE, 0:0:0, 0:0:0, notifier, drpclk_en_n, drpclk_en_n, delay_DRPCLK, delay_DRPWE);
    $setuphold (posedge RXUSRCLK, posedge RXCHBONDI, 0:0:0, 0:0:0, notifier, rxusrclk_en_p, rxusrclk_en_p, delay_RXUSRCLK, delay_RXCHBONDI);
    $setuphold (posedge RXUSRCLK, negedge RXCHBONDI, 0:0:0, 0:0:0, notifier, rxusrclk_en_p, rxusrclk_en_p, delay_RXUSRCLK, delay_RXCHBONDI);
    $setuphold (negedge RXUSRCLK, posedge RXCHBONDI, 0:0:0, 0:0:0, notifier, rxusrclk_en_n, rxusrclk_en_n, delay_RXUSRCLK, delay_RXCHBONDI);
    $setuphold (negedge RXUSRCLK, negedge RXCHBONDI, 0:0:0, 0:0:0, notifier, rxusrclk_en_n, rxusrclk_en_n, delay_RXUSRCLK, delay_RXCHBONDI);
    $setuphold (posedge RXUSRCLK2, posedge RXCHBONDI, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_RXCHBONDI);
    $setuphold (posedge RXUSRCLK2, negedge RXCHBONDI, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_RXCHBONDI);
    $setuphold (posedge RXUSRCLK2, negedge RX8B10BEN, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_RX8B10BEN);
    $setuphold (posedge RXUSRCLK2, negedge RXCHBONDEN, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_RXCHBONDEN);
    $setuphold (posedge RXUSRCLK2, negedge RXCHBONDLEVEL, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_RXCHBONDLEVEL);
    $setuphold (posedge RXUSRCLK2, negedge RXCHBONDMASTER, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_RXCHBONDMASTER);
    $setuphold (posedge RXUSRCLK2, negedge RXCHBONDSLAVE, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_RXCHBONDSLAVE);
    $setuphold (posedge RXUSRCLK2, negedge RXCOMMADETEN, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_RXCOMMADETEN);
    $setuphold (posedge RXUSRCLK2, negedge RXGEARBOXSLIP, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_RXGEARBOXSLIP);
    $setuphold (posedge RXUSRCLK2, negedge RXMCOMMAALIGNEN, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_RXMCOMMAALIGNEN);
    $setuphold (posedge RXUSRCLK2, negedge RXPCOMMAALIGNEN, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_RXPCOMMAALIGNEN);
    $setuphold (posedge RXUSRCLK2, negedge RXPOLARITY, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_RXPOLARITY);
    $setuphold (posedge RXUSRCLK2, negedge RXPRBSCNTRESET, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_RXPRBSCNTRESET);
    $setuphold (posedge RXUSRCLK2, negedge RXPRBSSEL, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_RXPRBSSEL);
    $setuphold (posedge RXUSRCLK2, negedge RXRATE, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_RXRATE);
    $setuphold (posedge RXUSRCLK2, negedge RXSLIDE, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_RXSLIDE);
    $setuphold (posedge RXUSRCLK2, negedge SETERRSTATUS, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_SETERRSTATUS);
    $setuphold (posedge RXUSRCLK2, posedge RX8B10BEN, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_RX8B10BEN);
    $setuphold (posedge RXUSRCLK2, posedge RXCHBONDEN, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_RXCHBONDEN);
    $setuphold (posedge RXUSRCLK2, posedge RXCHBONDLEVEL, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_RXCHBONDLEVEL);
    $setuphold (posedge RXUSRCLK2, posedge RXCHBONDMASTER, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_RXCHBONDMASTER);
    $setuphold (posedge RXUSRCLK2, posedge RXCHBONDSLAVE, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_RXCHBONDSLAVE);
    $setuphold (posedge RXUSRCLK2, posedge RXCOMMADETEN, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_RXCOMMADETEN);
    $setuphold (posedge RXUSRCLK2, posedge RXGEARBOXSLIP, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_RXGEARBOXSLIP);
    $setuphold (posedge RXUSRCLK2, posedge RXMCOMMAALIGNEN, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_RXMCOMMAALIGNEN);
    $setuphold (posedge RXUSRCLK2, posedge RXPCOMMAALIGNEN, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_RXPCOMMAALIGNEN);
    $setuphold (posedge RXUSRCLK2, posedge RXPOLARITY, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_RXPOLARITY);
    $setuphold (posedge RXUSRCLK2, posedge RXPRBSCNTRESET, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_RXPRBSCNTRESET);
    $setuphold (posedge RXUSRCLK2, posedge RXPRBSSEL, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_RXPRBSSEL);
    $setuphold (posedge RXUSRCLK2, posedge RXRATE, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_RXRATE);
    $setuphold (posedge RXUSRCLK2, posedge RXSLIDE, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_RXSLIDE);
    $setuphold (posedge RXUSRCLK2, posedge SETERRSTATUS, 0:0:0, 0:0:0, notifier, rxusrclk2_en_p, rxusrclk2_en_p, delay_RXUSRCLK2, delay_SETERRSTATUS);
    $setuphold (negedge RXUSRCLK2, posedge RXCHBONDI, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_RXCHBONDI);
    $setuphold (negedge RXUSRCLK2, negedge RXCHBONDI, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_RXCHBONDI);
    $setuphold (negedge RXUSRCLK2, negedge RX8B10BEN, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_RX8B10BEN);
    $setuphold (negedge RXUSRCLK2, negedge RXCHBONDEN, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_RXCHBONDEN);
    $setuphold (negedge RXUSRCLK2, negedge RXCHBONDLEVEL, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_RXCHBONDLEVEL);
    $setuphold (negedge RXUSRCLK2, negedge RXCHBONDMASTER, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_RXCHBONDMASTER);
    $setuphold (negedge RXUSRCLK2, negedge RXCHBONDSLAVE, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_RXCHBONDSLAVE);
    $setuphold (negedge RXUSRCLK2, negedge RXCOMMADETEN, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_RXCOMMADETEN);
    $setuphold (negedge RXUSRCLK2, negedge RXGEARBOXSLIP, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_RXGEARBOXSLIP);
    $setuphold (negedge RXUSRCLK2, negedge RXMCOMMAALIGNEN, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_RXMCOMMAALIGNEN);
    $setuphold (negedge RXUSRCLK2, negedge RXPCOMMAALIGNEN, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_RXPCOMMAALIGNEN);
    $setuphold (negedge RXUSRCLK2, negedge RXPOLARITY, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_RXPOLARITY);
    $setuphold (negedge RXUSRCLK2, negedge RXPRBSCNTRESET, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_RXPRBSCNTRESET);
    $setuphold (negedge RXUSRCLK2, negedge RXPRBSSEL, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_RXPRBSSEL);
    $setuphold (negedge RXUSRCLK2, negedge RXRATE, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_RXRATE);
    $setuphold (negedge RXUSRCLK2, negedge RXSLIDE, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_RXSLIDE);
    $setuphold (negedge RXUSRCLK2, negedge SETERRSTATUS, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_SETERRSTATUS);
    $setuphold (negedge RXUSRCLK2, posedge RX8B10BEN, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_RX8B10BEN);
    $setuphold (negedge RXUSRCLK2, posedge RXCHBONDEN, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_RXCHBONDEN);
    $setuphold (negedge RXUSRCLK2, posedge RXCHBONDLEVEL, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_RXCHBONDLEVEL);
    $setuphold (negedge RXUSRCLK2, posedge RXCHBONDMASTER, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_RXCHBONDMASTER);
    $setuphold (negedge RXUSRCLK2, posedge RXCHBONDSLAVE, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_RXCHBONDSLAVE);
    $setuphold (negedge RXUSRCLK2, posedge RXCOMMADETEN, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_RXCOMMADETEN);
    $setuphold (negedge RXUSRCLK2, posedge RXGEARBOXSLIP, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_RXGEARBOXSLIP);
    $setuphold (negedge RXUSRCLK2, posedge RXMCOMMAALIGNEN, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_RXMCOMMAALIGNEN);
    $setuphold (negedge RXUSRCLK2, posedge RXPCOMMAALIGNEN, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_RXPCOMMAALIGNEN);
    $setuphold (negedge RXUSRCLK2, posedge RXPOLARITY, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_RXPOLARITY);
    $setuphold (negedge RXUSRCLK2, posedge RXPRBSCNTRESET, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_RXPRBSCNTRESET);
    $setuphold (negedge RXUSRCLK2, posedge RXPRBSSEL, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_RXPRBSSEL);
    $setuphold (negedge RXUSRCLK2, posedge RXRATE, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_RXRATE);
    $setuphold (negedge RXUSRCLK2, posedge RXSLIDE, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_RXSLIDE);
    $setuphold (negedge RXUSRCLK2, posedge SETERRSTATUS, 0:0:0, 0:0:0, notifier, rxusrclk2_en_n, rxusrclk2_en_n, delay_RXUSRCLK2, delay_SETERRSTATUS);
    $setuphold (posedge TXPHDLYTSTCLK, negedge TXDLYHOLD, 0:0:0, 0:0:0, notifier, txphdlytstclk_en_p, txphdlytstclk_en_p, delay_TXPHDLYTSTCLK, delay_TXDLYHOLD);
    $setuphold (posedge TXPHDLYTSTCLK, negedge TXDLYUPDOWN, 0:0:0, 0:0:0, notifier, txphdlytstclk_en_p, txphdlytstclk_en_p, delay_TXPHDLYTSTCLK, delay_TXDLYUPDOWN);
    $setuphold (posedge TXPHDLYTSTCLK, posedge TXDLYHOLD, 0:0:0, 0:0:0, notifier, txphdlytstclk_en_p, txphdlytstclk_en_p, delay_TXPHDLYTSTCLK, delay_TXDLYHOLD);
    $setuphold (posedge TXPHDLYTSTCLK, posedge TXDLYUPDOWN, 0:0:0, 0:0:0, notifier, txphdlytstclk_en_p, txphdlytstclk_en_p, delay_TXPHDLYTSTCLK, delay_TXDLYUPDOWN);
    $setuphold (negedge TXPHDLYTSTCLK, negedge TXDLYHOLD, 0:0:0, 0:0:0, notifier, txphdlytstclk_en_n, txphdlytstclk_en_n, delay_TXPHDLYTSTCLK, delay_TXDLYHOLD);
    $setuphold (negedge TXPHDLYTSTCLK, negedge TXDLYUPDOWN, 0:0:0, 0:0:0, notifier, txphdlytstclk_en_n, txphdlytstclk_en_n, delay_TXPHDLYTSTCLK, delay_TXDLYUPDOWN);
    $setuphold (negedge TXPHDLYTSTCLK, posedge TXDLYHOLD, 0:0:0, 0:0:0, notifier, txphdlytstclk_en_n, txphdlytstclk_en_n, delay_TXPHDLYTSTCLK, delay_TXDLYHOLD);
    $setuphold (negedge TXPHDLYTSTCLK, posedge TXDLYUPDOWN, 0:0:0, 0:0:0, notifier, txphdlytstclk_en_n, txphdlytstclk_en_n, delay_TXPHDLYTSTCLK, delay_TXDLYUPDOWN);
    $setuphold (posedge TXUSRCLK, negedge TXPIPPMEN, 0:0:0, 0:0:0, notifier, txusrclk_en_p, txusrclk_en_p, delay_TXUSRCLK, delay_TXPIPPMEN);
    $setuphold (posedge TXUSRCLK, negedge TXPIPPMSTEPSIZE, 0:0:0, 0:0:0, notifier, txusrclk_en_p, txusrclk_en_p, delay_TXUSRCLK, delay_TXPIPPMSTEPSIZE);
    $setuphold (posedge TXUSRCLK, posedge TXPIPPMEN, 0:0:0, 0:0:0, notifier, txusrclk_en_p, txusrclk_en_p, delay_TXUSRCLK, delay_TXPIPPMEN);
    $setuphold (posedge TXUSRCLK, posedge TXPIPPMSTEPSIZE, 0:0:0, 0:0:0, notifier, txusrclk_en_p, txusrclk_en_p, delay_TXUSRCLK, delay_TXPIPPMSTEPSIZE);
    $setuphold (negedge TXUSRCLK, negedge TXPIPPMEN, 0:0:0, 0:0:0, notifier, txusrclk_en_n, txusrclk_en_n, delay_TXUSRCLK, delay_TXPIPPMEN);
    $setuphold (negedge TXUSRCLK, negedge TXPIPPMSTEPSIZE, 0:0:0, 0:0:0, notifier, txusrclk_en_n, txusrclk_en_n, delay_TXUSRCLK, delay_TXPIPPMSTEPSIZE);
    $setuphold (negedge TXUSRCLK, posedge TXPIPPMEN, 0:0:0, 0:0:0, notifier, txusrclk_en_n, txusrclk_en_n, delay_TXUSRCLK, delay_TXPIPPMEN);
    $setuphold (negedge TXUSRCLK, posedge TXPIPPMSTEPSIZE, 0:0:0, 0:0:0, notifier, txusrclk_en_n, txusrclk_en_n, delay_TXUSRCLK, delay_TXPIPPMSTEPSIZE);
    $setuphold (posedge TXUSRCLK2, negedge TX8B10BBYPASS, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TX8B10BBYPASS);
    $setuphold (posedge TXUSRCLK2, negedge TX8B10BEN, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TX8B10BEN);
    $setuphold (posedge TXUSRCLK2, negedge TXCHARDISPMODE, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXCHARDISPMODE);
    $setuphold (posedge TXUSRCLK2, negedge TXCHARDISPVAL, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXCHARDISPVAL);
    $setuphold (posedge TXUSRCLK2, negedge TXCHARISK, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXCHARISK);
    $setuphold (posedge TXUSRCLK2, negedge TXCOMINIT, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXCOMINIT);
    $setuphold (posedge TXUSRCLK2, negedge TXCOMSAS, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXCOMSAS);
    $setuphold (posedge TXUSRCLK2, negedge TXCOMWAKE, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXCOMWAKE);
    $setuphold (posedge TXUSRCLK2, negedge TXDATA, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXDATA);
    $setuphold (posedge TXUSRCLK2, negedge TXDETECTRX, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXDETECTRX);
    $setuphold (posedge TXUSRCLK2, negedge TXELECIDLE, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXELECIDLE);
    $setuphold (posedge TXUSRCLK2, negedge TXHEADER, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXHEADER);
    $setuphold (posedge TXUSRCLK2, negedge TXINHIBIT, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXINHIBIT);
    $setuphold (posedge TXUSRCLK2, negedge TXPD, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXPD);
    $setuphold (posedge TXUSRCLK2, negedge TXPIPPMEN, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXPIPPMEN);
    $setuphold (posedge TXUSRCLK2, negedge TXPIPPMSTEPSIZE, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXPIPPMSTEPSIZE);
    $setuphold (posedge TXUSRCLK2, negedge TXPOLARITY, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXPOLARITY);
    $setuphold (posedge TXUSRCLK2, negedge TXPRBSFORCEERR, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXPRBSFORCEERR);
    $setuphold (posedge TXUSRCLK2, negedge TXPRBSSEL, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXPRBSSEL);
    $setuphold (posedge TXUSRCLK2, negedge TXRATE, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXRATE);
    $setuphold (posedge TXUSRCLK2, negedge TXSEQUENCE, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXSEQUENCE);
    $setuphold (posedge TXUSRCLK2, negedge TXSTARTSEQ, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXSTARTSEQ);
    $setuphold (posedge TXUSRCLK2, posedge TX8B10BBYPASS, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TX8B10BBYPASS);
    $setuphold (posedge TXUSRCLK2, posedge TX8B10BEN, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TX8B10BEN);
    $setuphold (posedge TXUSRCLK2, posedge TXCHARDISPMODE, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXCHARDISPMODE);
    $setuphold (posedge TXUSRCLK2, posedge TXCHARDISPVAL, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXCHARDISPVAL);
    $setuphold (posedge TXUSRCLK2, posedge TXCHARISK, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXCHARISK);
    $setuphold (posedge TXUSRCLK2, posedge TXCOMINIT, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXCOMINIT);
    $setuphold (posedge TXUSRCLK2, posedge TXCOMSAS, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXCOMSAS);
    $setuphold (posedge TXUSRCLK2, posedge TXCOMWAKE, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXCOMWAKE);
    $setuphold (posedge TXUSRCLK2, posedge TXDATA, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXDATA);
    $setuphold (posedge TXUSRCLK2, posedge TXDETECTRX, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXDETECTRX);
    $setuphold (posedge TXUSRCLK2, posedge TXELECIDLE, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXELECIDLE);
    $setuphold (posedge TXUSRCLK2, posedge TXHEADER, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXHEADER);
    $setuphold (posedge TXUSRCLK2, posedge TXINHIBIT, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXINHIBIT);
    $setuphold (posedge TXUSRCLK2, posedge TXPD, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXPD);
    $setuphold (posedge TXUSRCLK2, posedge TXPIPPMEN, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXPIPPMEN);
    $setuphold (posedge TXUSRCLK2, posedge TXPIPPMSTEPSIZE, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXPIPPMSTEPSIZE);
    $setuphold (posedge TXUSRCLK2, posedge TXPOLARITY, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXPOLARITY);
    $setuphold (posedge TXUSRCLK2, posedge TXPRBSFORCEERR, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXPRBSFORCEERR);
    $setuphold (posedge TXUSRCLK2, posedge TXPRBSSEL, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXPRBSSEL);
    $setuphold (posedge TXUSRCLK2, posedge TXRATE, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXRATE);
    $setuphold (posedge TXUSRCLK2, posedge TXSEQUENCE, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXSEQUENCE);
    $setuphold (posedge TXUSRCLK2, posedge TXSTARTSEQ, 0:0:0, 0:0:0, notifier, txusrclk2_en_p, txusrclk2_en_p, delay_TXUSRCLK2, delay_TXSTARTSEQ);
    $setuphold (negedge TXUSRCLK2, negedge TX8B10BBYPASS, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TX8B10BBYPASS);
    $setuphold (negedge TXUSRCLK2, negedge TX8B10BEN, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TX8B10BEN);
    $setuphold (negedge TXUSRCLK2, negedge TXCHARDISPMODE, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXCHARDISPMODE);
    $setuphold (negedge TXUSRCLK2, negedge TXCHARDISPVAL, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXCHARDISPVAL);
    $setuphold (negedge TXUSRCLK2, negedge TXCHARISK, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXCHARISK);
    $setuphold (negedge TXUSRCLK2, negedge TXCOMINIT, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXCOMINIT);
    $setuphold (negedge TXUSRCLK2, negedge TXCOMSAS, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXCOMSAS);
    $setuphold (negedge TXUSRCLK2, negedge TXCOMWAKE, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXCOMWAKE);
    $setuphold (negedge TXUSRCLK2, negedge TXDATA, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXDATA);
    $setuphold (negedge TXUSRCLK2, negedge TXDETECTRX, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXDETECTRX);
    $setuphold (negedge TXUSRCLK2, negedge TXELECIDLE, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXELECIDLE);
    $setuphold (negedge TXUSRCLK2, negedge TXHEADER, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXHEADER);
    $setuphold (negedge TXUSRCLK2, negedge TXINHIBIT, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXINHIBIT);
    $setuphold (negedge TXUSRCLK2, negedge TXPD, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXPD);
    $setuphold (negedge TXUSRCLK2, negedge TXPIPPMEN, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXPIPPMEN);
    $setuphold (negedge TXUSRCLK2, negedge TXPIPPMSTEPSIZE, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXPIPPMSTEPSIZE);
    $setuphold (negedge TXUSRCLK2, negedge TXPOLARITY, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXPOLARITY);
    $setuphold (negedge TXUSRCLK2, negedge TXPRBSFORCEERR, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXPRBSFORCEERR);
    $setuphold (negedge TXUSRCLK2, negedge TXPRBSSEL, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXPRBSSEL);
    $setuphold (negedge TXUSRCLK2, negedge TXRATE, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXRATE);
    $setuphold (negedge TXUSRCLK2, negedge TXSEQUENCE, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXSEQUENCE);
    $setuphold (negedge TXUSRCLK2, negedge TXSTARTSEQ, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXSTARTSEQ);
    $setuphold (negedge TXUSRCLK2, posedge TX8B10BBYPASS, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TX8B10BBYPASS);
    $setuphold (negedge TXUSRCLK2, posedge TX8B10BEN, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TX8B10BEN);
    $setuphold (negedge TXUSRCLK2, posedge TXCHARDISPMODE, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXCHARDISPMODE);
    $setuphold (negedge TXUSRCLK2, posedge TXCHARDISPVAL, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXCHARDISPVAL);
    $setuphold (negedge TXUSRCLK2, posedge TXCHARISK, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXCHARISK);
    $setuphold (negedge TXUSRCLK2, posedge TXCOMINIT, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXCOMINIT);
    $setuphold (negedge TXUSRCLK2, posedge TXCOMSAS, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXCOMSAS);
    $setuphold (negedge TXUSRCLK2, posedge TXCOMWAKE, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXCOMWAKE);
    $setuphold (negedge TXUSRCLK2, posedge TXDATA, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXDATA);
    $setuphold (negedge TXUSRCLK2, posedge TXDETECTRX, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXDETECTRX);
    $setuphold (negedge TXUSRCLK2, posedge TXELECIDLE, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXELECIDLE);
    $setuphold (negedge TXUSRCLK2, posedge TXHEADER, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXHEADER);
    $setuphold (negedge TXUSRCLK2, posedge TXINHIBIT, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXINHIBIT);
    $setuphold (negedge TXUSRCLK2, posedge TXPD, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXPD);
    $setuphold (negedge TXUSRCLK2, posedge TXPIPPMEN, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXPIPPMEN);
    $setuphold (negedge TXUSRCLK2, posedge TXPIPPMSTEPSIZE, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXPIPPMSTEPSIZE);
    $setuphold (negedge TXUSRCLK2, posedge TXPOLARITY, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXPOLARITY);
    $setuphold (negedge TXUSRCLK2, posedge TXPRBSFORCEERR, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXPRBSFORCEERR);
    $setuphold (negedge TXUSRCLK2, posedge TXPRBSSEL, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXPRBSSEL);
    $setuphold (negedge TXUSRCLK2, posedge TXRATE, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXRATE);
    $setuphold (negedge TXUSRCLK2, posedge TXSEQUENCE, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXSEQUENCE);
    $setuphold (negedge TXUSRCLK2, posedge TXSTARTSEQ, 0:0:0, 0:0:0, notifier, txusrclk2_en_n, txusrclk2_en_n, delay_TXUSRCLK2, delay_TXSTARTSEQ);
`endif

    ( DMONITORCLK *> DMONITOROUT) = (0, 0);
    ( DRPCLK *> DRPDO) = (0, 0);
    ( DRPCLK *> DRPRDY) = (0, 0);
    ( RXUSRCLK2 *> PHYSTATUS) = (0, 0);
    ( RXUSRCLK2 *> RXBUFSTATUS) = (0, 0);
    ( RXUSRCLK2 *> RXBYTEISALIGNED) = (0, 0);
    ( RXUSRCLK2 *> RXBYTEREALIGN) = (0, 0);
    ( RXUSRCLK2 *> RXCHANBONDSEQ) = (0, 0);
    ( RXUSRCLK2 *> RXCHANISALIGNED) = (0, 0);
    ( RXUSRCLK2 *> RXCHANREALIGN) = (0, 0);
    ( RXUSRCLK2 *> RXCHARISCOMMA) = (0, 0);
    ( RXUSRCLK2 *> RXCHARISK) = (0, 0);
    ( RXUSRCLK2 *> RXCHBONDO) = (0, 0);
    ( RXUSRCLK *> RXCHBONDO) = (0, 0);
    ( RXUSRCLK2 *> RXCLKCORCNT) = (0, 0);
    ( RXUSRCLK2 *> RXCOMINITDET) = (0, 0);
    ( RXUSRCLK2 *> RXCOMMADET) = (0, 0);
    ( RXUSRCLK2 *> RXCOMSASDET) = (0, 0);
    ( RXUSRCLK2 *> RXCOMWAKEDET) = (0, 0);
    ( RXUSRCLK2 *> RXDATA) = (0, 0);
    ( RXUSRCLK2 *> RXDATAVALID) = (0, 0);
    ( RXUSRCLK2 *> RXDISPERR) = (0, 0);
    ( RXUSRCLK2 *> RXHEADER) = (0, 0);
    ( RXUSRCLK2 *> RXHEADERVALID) = (0, 0);
    ( RXUSRCLK2 *> RXNOTINTABLE) = (0, 0);
    ( RXUSRCLK2 *> RXPRBSERR) = (0, 0);
    ( RXUSRCLK2 *> RXRATEDONE) = (0, 0);
    ( RXUSRCLK2 *> RXRESETDONE) = (0, 0);
    ( RXUSRCLK2 *> RXSTARTOFSEQ) = (0, 0);
    ( RXUSRCLK2 *> RXSTATUS) = (0, 0);
    ( RXUSRCLK2 *> RXVALID) = (0, 0);
    ( TXUSRCLK2 *> TXBUFSTATUS) = (0, 0);
    ( TXUSRCLK2 *> TXCOMFINISH) = (0, 0);
    ( TXUSRCLK2 *> TXGEARBOXREADY) = (0, 0);
    ( TXUSRCLK2 *> TXRATEDONE) = (0, 0);
    ( TXUSRCLK2 *> TXRESETDONE) = (0, 0);

    specparam PATHPULSE$ = 0;
  endspecify
endmodule
`endcelldefine
