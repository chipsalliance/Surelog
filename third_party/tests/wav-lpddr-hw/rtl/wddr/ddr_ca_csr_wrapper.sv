
/*********************************************************************************
Copyright (c) 2021 Wavious LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

*********************************************************************************/

`include "ddr_global_define.vh"
`include "ddr_project_define.vh"
`include "ddr_ca_csr_defs.vh"
//`include "ddr_pi_small_wrapper_define.vh"
`include "ddr_pi_wrapper_define.vh"
`include "ddr_pi_match_wrapper_define.vh"

import ddr_global_pkg::*;

module ddr_ca_csr_wrapper #(
   parameter             AHB_AWIDTH    =  32,                              // AHB address width
   parameter             DQ_WIDTH      =  9,                               // DQ bus width
   parameter             DQS_WIDTH     =  6,                               // DQS bus width
   parameter             TXRX_DQS_WIDTH =  2,                               // DQS bus width
   parameter             TX0WIDTH      =  12,                              // Tx IO configuration width
   parameter             TX1WIDTH      =  14,                              // Tx IO configuration width
   parameter             RX0WIDTH      =  16,                              // Rx IO configuration width
   parameter             RX1WIDTH      =  24,                              // Rx IO configuration width
   parameter             A0WIDTH       =  20,                              // Sense amp configuration width
   parameter             A1WIDTH       =  5,                               // Sense amp configuration width
   parameter             A2WIDTH       =  32,                              // Sense amp configuration width
`ifdef DDR_DQS_VREF
   parameter             VWIDTH        =  11,                              // VREF configuration width
`endif
   parameter             E0WIDTH       =  6,                               // Tx egress mode width (ANA)
   parameter             E1WIDTH       =  7,                               // Tx egress mode width (DIG)
   parameter             FWIDTH        =  2,                               // Full cycle delay select width
   parameter             MAX_MXWIDTH   =  $clog2(8),                       // Max Num Phases supported in DP
   parameter             MXWIDTH       =  3,                               // Mux-X select width width
   parameter             LWIDTH        =  11,                              // LPDE delay select width
   parameter             P1WIDTH       =  9,                               // PI Matching cell cfg width
   parameter             P0WIDTH       =  15,                              // PI code select width
   parameter             PDWIDTH       =  34                               // PI decoded code select width
) (

   // AHB interface
   input   logic                              i_hclk,
   input   logic                              i_hreset,
   input   logic [AHB_AWIDTH-1:0]             i_haddr,
   input   logic                              i_hwrite,
   input   logic                              i_hsel,
   input   logic [31:0]                       i_hwdata,
   input   logic [1:0]                        i_htrans,
   input   logic [2:0]                        i_hsize,
   input   logic [2:0]                        i_hburst,
   input   logic                              i_hreadyin,
   output  logic                              o_hready,
   output  logic [31:0]                       o_hrdata,
   output  logic [1:0]                        o_hresp,

   input   logic                              i_bscan_mode,
   input   logic                              i_csp_pi_en,
   input   logic                              i_wcs,
   input   logic                              i_rcs,
   input   logic                              i_msr,

   // DQ RX
   output logic                               o_dq_fifo_clr,
   output logic                               o_dq_training_mode,
   input  logic [DQ_WIDTH-1:0]                i_dq_ingress_bscan,             // RX ingress bscan value
   output logic [DEC_DGBWIDTH-1:0]            o_dq_rgb_mode,                  // Receiver datapath gearbox mode
   output fgb_t                               o_dq_fgb_mode,                  // Receiver fifo gearbox mode
   output logic [RX0WIDTH*DQ_WIDTH-1:0]       o_dq_pad_rx_cfg,                // RX pad configuration
   output logic [A0WIDTH*DQ_WIDTH-1:0]        o_dq_sa_cfg,                    // Sense amp setting
   output logic [A2WIDTH*DQ_WIDTH-1:0]        o_dq_sa_dly_cfg,                // Sense amp setting
   input  logic [4*DQ_WIDTH-1:0]              i_dq_sa_sta,                    // Sense amp output
   input  logic [DQ_WIDTH-1:0]                i_dq_io_sta,                    // IO output

   // DQ TX
   output logic [DQ_WIDTH-1:0]                o_dq_egress_bscan,              // TX egress bscan value
   output logic [E0WIDTH*DQ_WIDTH-1:0]        o_dq_egress_mode_ana,           // TX egress mode (ANA)
   output logic [E1WIDTH*DQ_WIDTH-1:0]        o_dq_egress_mode_dig,           // TX egress mode (DIG)
   output logic [DQ_WIDTH-1:0]                o_dq_sdr_rt_pipe_en,            // Retimer pipeline enable
   output logic [DQ_WIDTH-1:0]                o_dq_sdr_0_pipe_en,             // SDR pipeline enable
   output logic [MXWIDTH*DQ_WIDTH-1:0]        o_dq_sdr_0_x_sel,               // Rise/Fall slice crossing select
   output logic [FWIDTH*DQ_WIDTH-1:0]         o_dq_sdr_0_fc_dly,              // SDR full-cycle delay select
   output logic [DQ_WIDTH-1:0]                o_dq_sdr_1_pipe_en,             // SDR pipeline enable
   output logic [MXWIDTH*DQ_WIDTH-1:0]        o_dq_sdr_1_x_sel,               // Rise/Fall slice crossing select
   output logic [FWIDTH*DQ_WIDTH-1:0]         o_dq_sdr_1_fc_dly,              // SDR full-cycle delay select
   output logic [DQ_WIDTH-1:0]                o_dq_sdr_2_pipe_en,             // SDR pipeline enable
   output logic [MXWIDTH*DQ_WIDTH-1:0]        o_dq_sdr_2_x_sel,               // Rise/Fall slice crossing select
   output logic [FWIDTH*DQ_WIDTH-1:0]         o_dq_sdr_2_fc_dly,              // SDR full-cycle delay select
   output logic [DQ_WIDTH-1:0]                o_dq_sdr_3_pipe_en,             // SDR pipeline enable
   output logic [MXWIDTH*DQ_WIDTH-1:0]        o_dq_sdr_3_x_sel,               // Rise/Fall slice crossing select
   output logic [FWIDTH*DQ_WIDTH-1:0]         o_dq_sdr_3_fc_dly,              // SDR full-cycle delay select
   output logic [DQ_WIDTH-1:0]                o_dq_ddr_0_pipe_en,             // SDR pipeline enable
   output logic [(MXWIDTH-1)*DQ_WIDTH-1:0]    o_dq_ddr_0_x_sel,               // Rise/Fall slice crossing select
   output logic [DQ_WIDTH-1:0]                o_dq_ddr_1_pipe_en,             // SDR pipeline enable
   output logic [(MXWIDTH-1)*DQ_WIDTH-1:0]    o_dq_ddr_1_x_sel,               // Rise/Fall slice crossing select
   output logic [LWIDTH*DQ_WIDTH-1:0]         o_dq_xdr_lpde_cfg,              // TX per-bit LPDE setting
   output logic [PDWIDTH-1:0]                 o_dq_qdr_pi_0_cfg,              // QDR PI setting
   output logic [PDWIDTH-1:0]                 o_dq_qdr_pi_1_cfg,              // QDR PI setting
   output logic [PDWIDTH-1:0]                 o_dq_ddr_pi_0_cfg,              // DDR PI setting
   output logic [PDWIDTH-1:0]                 o_dq_ddr_pi_1_cfg,              // DDR PI setting
   output logic [PDWIDTH-1:0]                 o_dq_sdr_rt_pi_cfg,             // SDR Retimer PI setting
   output logic [P1WIDTH-1:0]                 o_sdr_pi_cfg,
   output logic [P1WIDTH-1:0]                 o_dfi_pi_cfg,
   output logic [TX0WIDTH*DQ_WIDTH-1:0]       o_dq_pad_tx_cfg,                // TX pad configuration

   // DQS TX
   output logic [1:0]                         o_dqs_bscan_ctrl,               // TX bscan control value
   output logic [2*TXRX_DQS_WIDTH-1:0]        o_dqs_egress_bscan,             // TX egress bscan value
   output logic [E0WIDTH*DQS_WIDTH-1:0]       o_dqs_egress_mode_ana,          // TX egress mode (ANA)
   output logic [E1WIDTH*DQS_WIDTH-1:0]       o_dqs_egress_mode_dig,          // TX egress mode (DIG)
   output logic [DEC_DGBWIDTH-1:0]            o_dqs_tgb_mode,                 // Transmitter gearbox mode
   output logic [DEC_WGBWIDTH-1:0]            o_dqs_wgb_mode,                 // Write gearbox mode
   output logic [DEC_CK2WCKRWIDTH-1:0]        o_dqs_ck2wck_ratio,
   output logic [DQS_WIDTH-1:0]               o_dqs_sdr_rt_pipe_en,           // Retimer pipeline enable
   output logic [FWIDTH*DQS_WIDTH-1:0]        o_dqs_sdr_0_fc_dly,             // SDR full-cycle delay select
   output logic [MXWIDTH*DQS_WIDTH-1:0]       o_dqs_sdr_0_x_sel,              // Rise/Fall slice crossing select
   output logic [DQS_WIDTH-1:0]               o_dqs_sdr_0_pipe_en,            // SDR pipeline enable
   output logic [FWIDTH*DQS_WIDTH-1:0]        o_dqs_sdr_1_fc_dly,             // SDR full-cycle delay select
   output logic [MXWIDTH*DQS_WIDTH-1:0]       o_dqs_sdr_1_x_sel,              // Rise/Fall slice crossing select
   output logic [DQS_WIDTH-1:0]               o_dqs_sdr_1_pipe_en,            // SDR pipeline enable
   output logic [FWIDTH*DQS_WIDTH-1:0]        o_dqs_sdr_2_fc_dly,             // SDR full-cycle delay select
   output logic [MXWIDTH*DQS_WIDTH-1:0]       o_dqs_sdr_2_x_sel,              // Rise/Fall slice crossing select
   output logic [DQS_WIDTH-1:0]               o_dqs_sdr_2_pipe_en,            // SDR pipeline enable
   output logic [FWIDTH*DQS_WIDTH-1:0]        o_dqs_sdr_3_fc_dly,             // SDR full-cycle delay select
   output logic [MXWIDTH*DQS_WIDTH-1:0]       o_dqs_sdr_3_x_sel,              // Rise/Fall slice crossing select
   output logic [DQS_WIDTH-1:0]               o_dqs_sdr_3_pipe_en,            // SDR pipeline enable
   output logic [(MXWIDTH-1)*DQS_WIDTH-1:0]   o_dqs_ddr_0_x_sel,              // Rise/Fall slice crossing select
   output logic [DQS_WIDTH-1:0]               o_dqs_ddr_0_pipe_en,            // SDR pipeline enable
   output logic [(MXWIDTH-1)*DQS_WIDTH-1:0]   o_dqs_ddr_1_x_sel,              // Rise/Fall slice crossing select
   output logic [DQS_WIDTH-1:0]               o_dqs_ddr_1_pipe_en,            // SDR pipeline enable
   output logic [LWIDTH*TXRX_DQS_WIDTH-1:0]   o_dqs_xdr_lpde_cfg,             // TX per-bit LPDE setting
   output logic [PDWIDTH-1:0]                 o_dqs_qdr_pi_0_cfg,             // QDR PI setting
   output logic [PDWIDTH-1:0]                 o_dqs_qdr_pi_1_cfg,             // QDR PI setting
   output logic [PDWIDTH-1:0]                 o_dqs_ddr_pi_0_cfg,             // DDR PI setting
   output logic [PDWIDTH-1:0]                 o_dqs_ddr_pi_1_cfg,             // DDR PI setting
   output logic [PDWIDTH-1:0]                 o_dqs_sdr_rt_pi_cfg,            // SDR Retimer PI setting

   // DQS RX
   input  logic [2*TXRX_DQS_WIDTH-1:0]        i_dqs_ingress_bscan,            // RX ingress bscan value
   output logic [DEC_DGBWIDTH-1:0]            o_dqs_rgb_mode,                 // Receiver datapath gearbox mode
   output fgb_t                               o_dqs_fgb_mode,                  // Receiver fifo gearbox mode
   output logic                               o_dqs_wck_mode,                 // WCK loopback mode (only valid in rdqs_mode)
`ifdef DDR_DQS_VREF
   output logic [VWIDTH-1:0]                  o_dqs_refgen_cfg,               // VREF setting
`endif
   output logic [A0WIDTH*TXRX_DQS_WIDTH-1:0]  o_dqs_sa_cfg,                   // Sense amp setting
   output logic [A1WIDTH-1:0]                 o_dqs_sa_cmn_cfg,               // Sense amp setting
   output logic [LWIDTH-1:0]                  o_dqs_sdr_lpde_cfg,             // RX FIFO LPDE setting
   output logic [1:0]                         o_dqs_pre_filter_sel,           // Preamble filter select
   output logic [PDWIDTH-1:0]                 o_dqs_ren_pi_cfg,               // REN PI setting
   output logic [PDWIDTH-1:0]                 o_dqs_rcs_pi_cfg,               // RCS PI setting
   output logic [PDWIDTH-1:0]                 o_dqs_rdqs_pi_0_cfg,            // RDQS PI setting
   output logic [PDWIDTH-1:0]                 o_dqs_rdqs_pi_1_cfg,            // RDQS PI setting
   input  logic [DQS_WIDTH-1:0]               i_dqs_io_sta,                   // IO output
   input  logic                               i_dqs_rcs_pi_phase_sta,
   input  logic                               i_dqs_ren_pi_phase_sta,

   // Pads
   output logic [RX0WIDTH*TXRX_DQS_WIDTH-1:0] o_dqs_pad_rx_cfg,               // RX pad configuration
   output logic [RX1WIDTH-1:0]                o_dqs_pad_rx_cmn_cfg,           // RX pad configuration
   output logic [TX0WIDTH*TXRX_DQS_WIDTH-1:0] o_dqs_pad_tx_cfg,               // TX pad configuration
   output logic [TX1WIDTH-1:0]                o_dqs_pad_tx_cmn_cfg            // TX pad configuration

);

   logic [DGBWIDTH-1:0]         dqs_rgb_mode;
   logic [DGBWIDTH-1:0]         dq_rgb_mode;
   logic [DGBWIDTH-1:0]         dqs_tgb_mode;
   logic [WGBWIDTH-1:0]         dqs_wgb_mode;
   logic [CK2WCKRWIDTH-1:0]     dqs_ck2wck_ratio;
   // ---------------------------------------------------------
   // TOP
   // ---------------------------------------------------------

   logic [`DDR_CA_TOP_CFG_RANGE]                      dq_top_cfg;
   logic [`DDR_CA_TOP_STA_RANGE]                      dq_top_sta;

   // ---------------------------------------------------------
   // DQ RX
   // ---------------------------------------------------------

   logic [`DDR_CA_DQ_RX_BSCAN_STA_RANGE]              dq_dq_rx_bscan_sta;
   logic [`DDR_CA_DQ_RX_M0_CFG_RANGE]                 dq_dq_rx_m0_cfg;
   logic [`DDR_CA_DQ_RX_M1_CFG_RANGE]                 dq_dq_rx_m1_cfg;
   logic [`DDR_CA_DQ_RX_IO_M0_R0_CFG_0_RANGE]         dq_dq_rx_io_m0_r0_cfg_0;
   logic [`DDR_CA_DQ_RX_IO_M0_R0_CFG_1_RANGE]         dq_dq_rx_io_m0_r0_cfg_1;
   logic [`DDR_CA_DQ_RX_IO_M0_R0_CFG_2_RANGE]         dq_dq_rx_io_m0_r0_cfg_2;
   logic [`DDR_CA_DQ_RX_IO_M0_R0_CFG_3_RANGE]         dq_dq_rx_io_m0_r0_cfg_3;
   logic [`DDR_CA_DQ_RX_IO_M0_R0_CFG_4_RANGE]         dq_dq_rx_io_m0_r0_cfg_4;
   logic [`DDR_CA_DQ_RX_IO_M0_R0_CFG_5_RANGE]         dq_dq_rx_io_m0_r0_cfg_5;
   logic [`DDR_CA_DQ_RX_IO_M0_R0_CFG_6_RANGE]         dq_dq_rx_io_m0_r0_cfg_6;
   logic [`DDR_CA_DQ_RX_IO_M0_R0_CFG_7_RANGE]         dq_dq_rx_io_m0_r0_cfg_7;
   logic [`DDR_CA_DQ_RX_IO_M0_R0_CFG_8_RANGE]         dq_dq_rx_io_m0_r0_cfg_8;
   logic [`DDR_CA_DQ_RX_IO_M0_R0_CFG_9_RANGE]         dq_dq_rx_io_m0_r0_cfg_9;
   logic [`DDR_CA_DQ_RX_IO_M0_R0_CFG_10_RANGE]         dq_dq_rx_io_m0_r0_cfg_10;
   logic [`DDR_CA_DQ_RX_IO_M0_R1_CFG_0_RANGE]         dq_dq_rx_io_m0_r1_cfg_0;
   logic [`DDR_CA_DQ_RX_IO_M0_R1_CFG_1_RANGE]         dq_dq_rx_io_m0_r1_cfg_1;
   logic [`DDR_CA_DQ_RX_IO_M0_R1_CFG_2_RANGE]         dq_dq_rx_io_m0_r1_cfg_2;
   logic [`DDR_CA_DQ_RX_IO_M0_R1_CFG_3_RANGE]         dq_dq_rx_io_m0_r1_cfg_3;
   logic [`DDR_CA_DQ_RX_IO_M0_R1_CFG_4_RANGE]         dq_dq_rx_io_m0_r1_cfg_4;
   logic [`DDR_CA_DQ_RX_IO_M0_R1_CFG_5_RANGE]         dq_dq_rx_io_m0_r1_cfg_5;
   logic [`DDR_CA_DQ_RX_IO_M0_R1_CFG_6_RANGE]         dq_dq_rx_io_m0_r1_cfg_6;
   logic [`DDR_CA_DQ_RX_IO_M0_R1_CFG_7_RANGE]         dq_dq_rx_io_m0_r1_cfg_7;
   logic [`DDR_CA_DQ_RX_IO_M0_R1_CFG_8_RANGE]         dq_dq_rx_io_m0_r1_cfg_8;
   logic [`DDR_CA_DQ_RX_IO_M0_R1_CFG_9_RANGE]         dq_dq_rx_io_m0_r1_cfg_9;
   logic [`DDR_CA_DQ_RX_IO_M0_R1_CFG_10_RANGE]         dq_dq_rx_io_m0_r1_cfg_10;
   logic [`DDR_CA_DQ_RX_IO_M1_R0_CFG_0_RANGE]         dq_dq_rx_io_m1_r0_cfg_0;
   logic [`DDR_CA_DQ_RX_IO_M1_R0_CFG_1_RANGE]         dq_dq_rx_io_m1_r0_cfg_1;
   logic [`DDR_CA_DQ_RX_IO_M1_R0_CFG_2_RANGE]         dq_dq_rx_io_m1_r0_cfg_2;
   logic [`DDR_CA_DQ_RX_IO_M1_R0_CFG_3_RANGE]         dq_dq_rx_io_m1_r0_cfg_3;
   logic [`DDR_CA_DQ_RX_IO_M1_R0_CFG_4_RANGE]         dq_dq_rx_io_m1_r0_cfg_4;
   logic [`DDR_CA_DQ_RX_IO_M1_R0_CFG_5_RANGE]         dq_dq_rx_io_m1_r0_cfg_5;
   logic [`DDR_CA_DQ_RX_IO_M1_R0_CFG_6_RANGE]         dq_dq_rx_io_m1_r0_cfg_6;
   logic [`DDR_CA_DQ_RX_IO_M1_R0_CFG_7_RANGE]         dq_dq_rx_io_m1_r0_cfg_7;
   logic [`DDR_CA_DQ_RX_IO_M1_R0_CFG_8_RANGE]         dq_dq_rx_io_m1_r0_cfg_8;
   logic [`DDR_CA_DQ_RX_IO_M1_R0_CFG_9_RANGE]         dq_dq_rx_io_m1_r0_cfg_9;
   logic [`DDR_CA_DQ_RX_IO_M1_R0_CFG_10_RANGE]         dq_dq_rx_io_m1_r0_cfg_10;
   logic [`DDR_CA_DQ_RX_IO_M1_R1_CFG_0_RANGE]         dq_dq_rx_io_m1_r1_cfg_0;
   logic [`DDR_CA_DQ_RX_IO_M1_R1_CFG_1_RANGE]         dq_dq_rx_io_m1_r1_cfg_1;
   logic [`DDR_CA_DQ_RX_IO_M1_R1_CFG_2_RANGE]         dq_dq_rx_io_m1_r1_cfg_2;
   logic [`DDR_CA_DQ_RX_IO_M1_R1_CFG_3_RANGE]         dq_dq_rx_io_m1_r1_cfg_3;
   logic [`DDR_CA_DQ_RX_IO_M1_R1_CFG_4_RANGE]         dq_dq_rx_io_m1_r1_cfg_4;
   logic [`DDR_CA_DQ_RX_IO_M1_R1_CFG_5_RANGE]         dq_dq_rx_io_m1_r1_cfg_5;
   logic [`DDR_CA_DQ_RX_IO_M1_R1_CFG_6_RANGE]         dq_dq_rx_io_m1_r1_cfg_6;
   logic [`DDR_CA_DQ_RX_IO_M1_R1_CFG_7_RANGE]         dq_dq_rx_io_m1_r1_cfg_7;
   logic [`DDR_CA_DQ_RX_IO_M1_R1_CFG_8_RANGE]         dq_dq_rx_io_m1_r1_cfg_8;
   logic [`DDR_CA_DQ_RX_IO_M1_R1_CFG_9_RANGE]         dq_dq_rx_io_m1_r1_cfg_9;
   logic [`DDR_CA_DQ_RX_IO_M1_R1_CFG_10_RANGE]         dq_dq_rx_io_m1_r1_cfg_10;
   logic [`DDR_CA_DQ_RX_SA_M0_R0_CFG_0_RANGE]         dq_dq_rx_sa_m0_r0_cfg_0;
   logic [`DDR_CA_DQ_RX_SA_M0_R0_CFG_1_RANGE]         dq_dq_rx_sa_m0_r0_cfg_1;
   logic [`DDR_CA_DQ_RX_SA_M0_R0_CFG_2_RANGE]         dq_dq_rx_sa_m0_r0_cfg_2;
   logic [`DDR_CA_DQ_RX_SA_M0_R0_CFG_3_RANGE]         dq_dq_rx_sa_m0_r0_cfg_3;
   logic [`DDR_CA_DQ_RX_SA_M0_R0_CFG_4_RANGE]         dq_dq_rx_sa_m0_r0_cfg_4;
   logic [`DDR_CA_DQ_RX_SA_M0_R0_CFG_5_RANGE]         dq_dq_rx_sa_m0_r0_cfg_5;
   logic [`DDR_CA_DQ_RX_SA_M0_R0_CFG_6_RANGE]         dq_dq_rx_sa_m0_r0_cfg_6;
   logic [`DDR_CA_DQ_RX_SA_M0_R0_CFG_7_RANGE]         dq_dq_rx_sa_m0_r0_cfg_7;
   logic [`DDR_CA_DQ_RX_SA_M0_R0_CFG_8_RANGE]         dq_dq_rx_sa_m0_r0_cfg_8;
   logic [`DDR_CA_DQ_RX_SA_M0_R0_CFG_9_RANGE]         dq_dq_rx_sa_m0_r0_cfg_9;
   logic [`DDR_CA_DQ_RX_SA_M0_R0_CFG_10_RANGE]         dq_dq_rx_sa_m0_r0_cfg_10;
   logic [`DDR_CA_DQ_RX_SA_M0_R1_CFG_0_RANGE]         dq_dq_rx_sa_m0_r1_cfg_0;
   logic [`DDR_CA_DQ_RX_SA_M0_R1_CFG_1_RANGE]         dq_dq_rx_sa_m0_r1_cfg_1;
   logic [`DDR_CA_DQ_RX_SA_M0_R1_CFG_2_RANGE]         dq_dq_rx_sa_m0_r1_cfg_2;
   logic [`DDR_CA_DQ_RX_SA_M0_R1_CFG_3_RANGE]         dq_dq_rx_sa_m0_r1_cfg_3;
   logic [`DDR_CA_DQ_RX_SA_M0_R1_CFG_4_RANGE]         dq_dq_rx_sa_m0_r1_cfg_4;
   logic [`DDR_CA_DQ_RX_SA_M0_R1_CFG_5_RANGE]         dq_dq_rx_sa_m0_r1_cfg_5;
   logic [`DDR_CA_DQ_RX_SA_M0_R1_CFG_6_RANGE]         dq_dq_rx_sa_m0_r1_cfg_6;
   logic [`DDR_CA_DQ_RX_SA_M0_R1_CFG_7_RANGE]         dq_dq_rx_sa_m0_r1_cfg_7;
   logic [`DDR_CA_DQ_RX_SA_M0_R1_CFG_8_RANGE]         dq_dq_rx_sa_m0_r1_cfg_8;
   logic [`DDR_CA_DQ_RX_SA_M0_R1_CFG_9_RANGE]         dq_dq_rx_sa_m0_r1_cfg_9;
   logic [`DDR_CA_DQ_RX_SA_M0_R1_CFG_10_RANGE]         dq_dq_rx_sa_m0_r1_cfg_10;
   logic [`DDR_CA_DQ_RX_SA_M1_R0_CFG_0_RANGE]         dq_dq_rx_sa_m1_r0_cfg_0;
   logic [`DDR_CA_DQ_RX_SA_M1_R0_CFG_1_RANGE]         dq_dq_rx_sa_m1_r0_cfg_1;
   logic [`DDR_CA_DQ_RX_SA_M1_R0_CFG_2_RANGE]         dq_dq_rx_sa_m1_r0_cfg_2;
   logic [`DDR_CA_DQ_RX_SA_M1_R0_CFG_3_RANGE]         dq_dq_rx_sa_m1_r0_cfg_3;
   logic [`DDR_CA_DQ_RX_SA_M1_R0_CFG_4_RANGE]         dq_dq_rx_sa_m1_r0_cfg_4;
   logic [`DDR_CA_DQ_RX_SA_M1_R0_CFG_5_RANGE]         dq_dq_rx_sa_m1_r0_cfg_5;
   logic [`DDR_CA_DQ_RX_SA_M1_R0_CFG_6_RANGE]         dq_dq_rx_sa_m1_r0_cfg_6;
   logic [`DDR_CA_DQ_RX_SA_M1_R0_CFG_7_RANGE]         dq_dq_rx_sa_m1_r0_cfg_7;
   logic [`DDR_CA_DQ_RX_SA_M1_R0_CFG_8_RANGE]         dq_dq_rx_sa_m1_r0_cfg_8;
   logic [`DDR_CA_DQ_RX_SA_M1_R0_CFG_9_RANGE]         dq_dq_rx_sa_m1_r0_cfg_9;
   logic [`DDR_CA_DQ_RX_SA_M1_R0_CFG_10_RANGE]         dq_dq_rx_sa_m1_r0_cfg_10;
   logic [`DDR_CA_DQ_RX_SA_M1_R1_CFG_0_RANGE]         dq_dq_rx_sa_m1_r1_cfg_0;
   logic [`DDR_CA_DQ_RX_SA_M1_R1_CFG_1_RANGE]         dq_dq_rx_sa_m1_r1_cfg_1;
   logic [`DDR_CA_DQ_RX_SA_M1_R1_CFG_2_RANGE]         dq_dq_rx_sa_m1_r1_cfg_2;
   logic [`DDR_CA_DQ_RX_SA_M1_R1_CFG_3_RANGE]         dq_dq_rx_sa_m1_r1_cfg_3;
   logic [`DDR_CA_DQ_RX_SA_M1_R1_CFG_4_RANGE]         dq_dq_rx_sa_m1_r1_cfg_4;
   logic [`DDR_CA_DQ_RX_SA_M1_R1_CFG_5_RANGE]         dq_dq_rx_sa_m1_r1_cfg_5;
   logic [`DDR_CA_DQ_RX_SA_M1_R1_CFG_6_RANGE]         dq_dq_rx_sa_m1_r1_cfg_6;
   logic [`DDR_CA_DQ_RX_SA_M1_R1_CFG_7_RANGE]         dq_dq_rx_sa_m1_r1_cfg_7;
   logic [`DDR_CA_DQ_RX_SA_M1_R1_CFG_8_RANGE]         dq_dq_rx_sa_m1_r1_cfg_8;
   logic [`DDR_CA_DQ_RX_SA_M1_R1_CFG_9_RANGE]         dq_dq_rx_sa_m1_r1_cfg_9;
   logic [`DDR_CA_DQ_RX_SA_M1_R1_CFG_10_RANGE]         dq_dq_rx_sa_m1_r1_cfg_10;
   logic [`DDR_CA_DQ_RX_SA_DLY_M0_R0_CFG_0_RANGE]     dq_dq_rx_sa_dly_m0_r0_cfg_0;
   logic [`DDR_CA_DQ_RX_SA_DLY_M0_R0_CFG_1_RANGE]     dq_dq_rx_sa_dly_m0_r0_cfg_1;
   logic [`DDR_CA_DQ_RX_SA_DLY_M0_R0_CFG_2_RANGE]     dq_dq_rx_sa_dly_m0_r0_cfg_2;
   logic [`DDR_CA_DQ_RX_SA_DLY_M0_R0_CFG_3_RANGE]     dq_dq_rx_sa_dly_m0_r0_cfg_3;
   logic [`DDR_CA_DQ_RX_SA_DLY_M0_R0_CFG_4_RANGE]     dq_dq_rx_sa_dly_m0_r0_cfg_4;
   logic [`DDR_CA_DQ_RX_SA_DLY_M0_R0_CFG_5_RANGE]     dq_dq_rx_sa_dly_m0_r0_cfg_5;
   logic [`DDR_CA_DQ_RX_SA_DLY_M0_R0_CFG_6_RANGE]     dq_dq_rx_sa_dly_m0_r0_cfg_6;
   logic [`DDR_CA_DQ_RX_SA_DLY_M0_R0_CFG_7_RANGE]     dq_dq_rx_sa_dly_m0_r0_cfg_7;
   logic [`DDR_CA_DQ_RX_SA_DLY_M0_R0_CFG_8_RANGE]     dq_dq_rx_sa_dly_m0_r0_cfg_8;
   logic [`DDR_CA_DQ_RX_SA_DLY_M0_R0_CFG_9_RANGE]     dq_dq_rx_sa_dly_m0_r0_cfg_9;
   logic [`DDR_CA_DQ_RX_SA_DLY_M0_R0_CFG_10_RANGE]     dq_dq_rx_sa_dly_m0_r0_cfg_10;
   logic [`DDR_CA_DQ_RX_SA_DLY_M0_R1_CFG_0_RANGE]     dq_dq_rx_sa_dly_m0_r1_cfg_0;
   logic [`DDR_CA_DQ_RX_SA_DLY_M0_R1_CFG_1_RANGE]     dq_dq_rx_sa_dly_m0_r1_cfg_1;
   logic [`DDR_CA_DQ_RX_SA_DLY_M0_R1_CFG_2_RANGE]     dq_dq_rx_sa_dly_m0_r1_cfg_2;
   logic [`DDR_CA_DQ_RX_SA_DLY_M0_R1_CFG_3_RANGE]     dq_dq_rx_sa_dly_m0_r1_cfg_3;
   logic [`DDR_CA_DQ_RX_SA_DLY_M0_R1_CFG_4_RANGE]     dq_dq_rx_sa_dly_m0_r1_cfg_4;
   logic [`DDR_CA_DQ_RX_SA_DLY_M0_R1_CFG_5_RANGE]     dq_dq_rx_sa_dly_m0_r1_cfg_5;
   logic [`DDR_CA_DQ_RX_SA_DLY_M0_R1_CFG_6_RANGE]     dq_dq_rx_sa_dly_m0_r1_cfg_6;
   logic [`DDR_CA_DQ_RX_SA_DLY_M0_R1_CFG_7_RANGE]     dq_dq_rx_sa_dly_m0_r1_cfg_7;
   logic [`DDR_CA_DQ_RX_SA_DLY_M0_R1_CFG_8_RANGE]     dq_dq_rx_sa_dly_m0_r1_cfg_8;
   logic [`DDR_CA_DQ_RX_SA_DLY_M0_R1_CFG_9_RANGE]     dq_dq_rx_sa_dly_m0_r1_cfg_9;
   logic [`DDR_CA_DQ_RX_SA_DLY_M0_R1_CFG_10_RANGE]     dq_dq_rx_sa_dly_m0_r1_cfg_10;
   logic [`DDR_CA_DQ_RX_SA_DLY_M1_R0_CFG_0_RANGE]     dq_dq_rx_sa_dly_m1_r0_cfg_0;
   logic [`DDR_CA_DQ_RX_SA_DLY_M1_R0_CFG_1_RANGE]     dq_dq_rx_sa_dly_m1_r0_cfg_1;
   logic [`DDR_CA_DQ_RX_SA_DLY_M1_R0_CFG_2_RANGE]     dq_dq_rx_sa_dly_m1_r0_cfg_2;
   logic [`DDR_CA_DQ_RX_SA_DLY_M1_R0_CFG_3_RANGE]     dq_dq_rx_sa_dly_m1_r0_cfg_3;
   logic [`DDR_CA_DQ_RX_SA_DLY_M1_R0_CFG_4_RANGE]     dq_dq_rx_sa_dly_m1_r0_cfg_4;
   logic [`DDR_CA_DQ_RX_SA_DLY_M1_R0_CFG_5_RANGE]     dq_dq_rx_sa_dly_m1_r0_cfg_5;
   logic [`DDR_CA_DQ_RX_SA_DLY_M1_R0_CFG_6_RANGE]     dq_dq_rx_sa_dly_m1_r0_cfg_6;
   logic [`DDR_CA_DQ_RX_SA_DLY_M1_R0_CFG_7_RANGE]     dq_dq_rx_sa_dly_m1_r0_cfg_7;
   logic [`DDR_CA_DQ_RX_SA_DLY_M1_R0_CFG_8_RANGE]     dq_dq_rx_sa_dly_m1_r0_cfg_8;
   logic [`DDR_CA_DQ_RX_SA_DLY_M1_R0_CFG_9_RANGE]     dq_dq_rx_sa_dly_m1_r0_cfg_9;
   logic [`DDR_CA_DQ_RX_SA_DLY_M1_R0_CFG_10_RANGE]     dq_dq_rx_sa_dly_m1_r0_cfg_10;
   logic [`DDR_CA_DQ_RX_SA_DLY_M1_R1_CFG_0_RANGE]     dq_dq_rx_sa_dly_m1_r1_cfg_0;
   logic [`DDR_CA_DQ_RX_SA_DLY_M1_R1_CFG_1_RANGE]     dq_dq_rx_sa_dly_m1_r1_cfg_1;
   logic [`DDR_CA_DQ_RX_SA_DLY_M1_R1_CFG_2_RANGE]     dq_dq_rx_sa_dly_m1_r1_cfg_2;
   logic [`DDR_CA_DQ_RX_SA_DLY_M1_R1_CFG_3_RANGE]     dq_dq_rx_sa_dly_m1_r1_cfg_3;
   logic [`DDR_CA_DQ_RX_SA_DLY_M1_R1_CFG_4_RANGE]     dq_dq_rx_sa_dly_m1_r1_cfg_4;
   logic [`DDR_CA_DQ_RX_SA_DLY_M1_R1_CFG_5_RANGE]     dq_dq_rx_sa_dly_m1_r1_cfg_5;
   logic [`DDR_CA_DQ_RX_SA_DLY_M1_R1_CFG_6_RANGE]     dq_dq_rx_sa_dly_m1_r1_cfg_6;
   logic [`DDR_CA_DQ_RX_SA_DLY_M1_R1_CFG_7_RANGE]     dq_dq_rx_sa_dly_m1_r1_cfg_7;
   logic [`DDR_CA_DQ_RX_SA_DLY_M1_R1_CFG_8_RANGE]     dq_dq_rx_sa_dly_m1_r1_cfg_8;
   logic [`DDR_CA_DQ_RX_SA_DLY_M1_R1_CFG_9_RANGE]     dq_dq_rx_sa_dly_m1_r1_cfg_9;
   logic [`DDR_CA_DQ_RX_SA_DLY_M1_R1_CFG_10_RANGE]     dq_dq_rx_sa_dly_m1_r1_cfg_10;
   logic [`DDR_CA_DQ_RX_SA_STA_0_RANGE]               dq_dq_rx_sa_sta_0;
   logic [`DDR_CA_DQ_RX_SA_STA_1_RANGE]               dq_dq_rx_sa_sta_1;
   logic [`DDR_CA_DQ_RX_SA_STA_2_RANGE]               dq_dq_rx_sa_sta_2;
   logic [`DDR_CA_DQ_RX_SA_STA_3_RANGE]               dq_dq_rx_sa_sta_3;
   logic [`DDR_CA_DQ_RX_SA_STA_4_RANGE]               dq_dq_rx_sa_sta_4;
   logic [`DDR_CA_DQ_RX_SA_STA_5_RANGE]               dq_dq_rx_sa_sta_5;
   logic [`DDR_CA_DQ_RX_SA_STA_6_RANGE]               dq_dq_rx_sa_sta_6;
   logic [`DDR_CA_DQ_RX_SA_STA_7_RANGE]               dq_dq_rx_sa_sta_7;
   logic [`DDR_CA_DQ_RX_SA_STA_8_RANGE]               dq_dq_rx_sa_sta_8;
   logic [`DDR_CA_DQ_RX_SA_STA_9_RANGE]               dq_dq_rx_sa_sta_9;
   logic [`DDR_CA_DQ_RX_SA_STA_10_RANGE]               dq_dq_rx_sa_sta_10;
   logic [`DDR_CA_DQ_RX_IO_STA_RANGE]                    dq_dq_rx_io_sta;

   // ---------------------------------------------------------
   // DQ TX
   // ---------------------------------------------------------

   logic [`DDR_CA_DQ_TX_BSCAN_CFG_RANGE]              dq_dq_tx_bscan_cfg;
   logic [`DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_0_RANGE] dq_dq_tx_egress_ana_m0_cfg_0;
   logic [`DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_1_RANGE] dq_dq_tx_egress_ana_m0_cfg_1;
   logic [`DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_2_RANGE] dq_dq_tx_egress_ana_m0_cfg_2;
   logic [`DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_3_RANGE] dq_dq_tx_egress_ana_m0_cfg_3;
   logic [`DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_4_RANGE] dq_dq_tx_egress_ana_m0_cfg_4;
   logic [`DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_5_RANGE] dq_dq_tx_egress_ana_m0_cfg_5;
   logic [`DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_6_RANGE] dq_dq_tx_egress_ana_m0_cfg_6;
   logic [`DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_7_RANGE] dq_dq_tx_egress_ana_m0_cfg_7;
   logic [`DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_8_RANGE] dq_dq_tx_egress_ana_m0_cfg_8;
   logic [`DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_9_RANGE] dq_dq_tx_egress_ana_m0_cfg_9;
   logic [`DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_10_RANGE] dq_dq_tx_egress_ana_m0_cfg_10;
   logic [`DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_0_RANGE] dq_dq_tx_egress_ana_m1_cfg_0;
   logic [`DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_1_RANGE] dq_dq_tx_egress_ana_m1_cfg_1;
   logic [`DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_2_RANGE] dq_dq_tx_egress_ana_m1_cfg_2;
   logic [`DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_3_RANGE] dq_dq_tx_egress_ana_m1_cfg_3;
   logic [`DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_4_RANGE] dq_dq_tx_egress_ana_m1_cfg_4;
   logic [`DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_5_RANGE] dq_dq_tx_egress_ana_m1_cfg_5;
   logic [`DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_6_RANGE] dq_dq_tx_egress_ana_m1_cfg_6;
   logic [`DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_7_RANGE] dq_dq_tx_egress_ana_m1_cfg_7;
   logic [`DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_8_RANGE] dq_dq_tx_egress_ana_m1_cfg_8;
   logic [`DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_9_RANGE] dq_dq_tx_egress_ana_m1_cfg_9;
   logic [`DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_10_RANGE] dq_dq_tx_egress_ana_m1_cfg_10;
   logic [`DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_0_RANGE] dq_dq_tx_egress_dig_m0_cfg_0;
   logic [`DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_1_RANGE] dq_dq_tx_egress_dig_m0_cfg_1;
   logic [`DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_2_RANGE] dq_dq_tx_egress_dig_m0_cfg_2;
   logic [`DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_3_RANGE] dq_dq_tx_egress_dig_m0_cfg_3;
   logic [`DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_4_RANGE] dq_dq_tx_egress_dig_m0_cfg_4;
   logic [`DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_5_RANGE] dq_dq_tx_egress_dig_m0_cfg_5;
   logic [`DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_6_RANGE] dq_dq_tx_egress_dig_m0_cfg_6;
   logic [`DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_7_RANGE] dq_dq_tx_egress_dig_m0_cfg_7;
   logic [`DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_8_RANGE] dq_dq_tx_egress_dig_m0_cfg_8;
   logic [`DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_9_RANGE] dq_dq_tx_egress_dig_m0_cfg_9;
   logic [`DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_10_RANGE] dq_dq_tx_egress_dig_m0_cfg_10;
   logic [`DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_0_RANGE] dq_dq_tx_egress_dig_m1_cfg_0;
   logic [`DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_1_RANGE] dq_dq_tx_egress_dig_m1_cfg_1;
   logic [`DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_2_RANGE] dq_dq_tx_egress_dig_m1_cfg_2;
   logic [`DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_3_RANGE] dq_dq_tx_egress_dig_m1_cfg_3;
   logic [`DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_4_RANGE] dq_dq_tx_egress_dig_m1_cfg_4;
   logic [`DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_5_RANGE] dq_dq_tx_egress_dig_m1_cfg_5;
   logic [`DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_6_RANGE] dq_dq_tx_egress_dig_m1_cfg_6;
   logic [`DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_7_RANGE] dq_dq_tx_egress_dig_m1_cfg_7;
   logic [`DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_8_RANGE] dq_dq_tx_egress_dig_m1_cfg_8;
   logic [`DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_9_RANGE] dq_dq_tx_egress_dig_m1_cfg_9;
   logic [`DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_10_RANGE] dq_dq_tx_egress_dig_m1_cfg_10;
   logic [`DDR_CA_DQ_TX_ODR_PI_M0_R0_CFG_RANGE]       dq_dq_tx_odr_pi_m0_r0_cfg;
   logic [`DDR_CA_DQ_TX_ODR_PI_M0_R1_CFG_RANGE]       dq_dq_tx_odr_pi_m0_r1_cfg;
   logic [`DDR_CA_DQ_TX_ODR_PI_M1_R0_CFG_RANGE]       dq_dq_tx_odr_pi_m1_r0_cfg;
   logic [`DDR_CA_DQ_TX_ODR_PI_M1_R1_CFG_RANGE]       dq_dq_tx_odr_pi_m1_r1_cfg;
   logic [`DDR_CA_DQ_TX_QDR_PI_0_M0_R0_CFG_RANGE]     dq_dq_tx_qdr_pi_0_m0_r0_cfg;
   logic [`DDR_CA_DQ_TX_QDR_PI_1_M0_R0_CFG_RANGE]     dq_dq_tx_qdr_pi_1_m0_r0_cfg;
   logic [`DDR_CA_DQ_TX_QDR_PI_0_M1_R0_CFG_RANGE]     dq_dq_tx_qdr_pi_0_m1_r0_cfg;
   logic [`DDR_CA_DQ_TX_QDR_PI_1_M1_R0_CFG_RANGE]     dq_dq_tx_qdr_pi_1_m1_r0_cfg;
   logic [`DDR_CA_DQ_TX_QDR_PI_0_M0_R1_CFG_RANGE]     dq_dq_tx_qdr_pi_0_m0_r1_cfg;
   logic [`DDR_CA_DQ_TX_QDR_PI_1_M0_R1_CFG_RANGE]     dq_dq_tx_qdr_pi_1_m0_r1_cfg;
   logic [`DDR_CA_DQ_TX_QDR_PI_0_M1_R1_CFG_RANGE]     dq_dq_tx_qdr_pi_0_m1_r1_cfg;
   logic [`DDR_CA_DQ_TX_QDR_PI_1_M1_R1_CFG_RANGE]     dq_dq_tx_qdr_pi_1_m1_r1_cfg;
   logic [`DDR_CA_DQ_TX_DDR_PI_0_M0_R0_CFG_RANGE]     dq_dq_tx_ddr_pi_0_m0_r0_cfg;
   logic [`DDR_CA_DQ_TX_DDR_PI_0_M0_R1_CFG_RANGE]     dq_dq_tx_ddr_pi_0_m0_r1_cfg;
   logic [`DDR_CA_DQ_TX_DDR_PI_1_M1_R0_CFG_RANGE]     dq_dq_tx_ddr_pi_0_m1_r0_cfg;
   logic [`DDR_CA_DQ_TX_DDR_PI_1_M1_R1_CFG_RANGE]     dq_dq_tx_ddr_pi_0_m1_r1_cfg;
   logic [`DDR_CA_DQ_TX_DDR_PI_1_M0_R0_CFG_RANGE]     dq_dq_tx_ddr_pi_1_m0_r0_cfg;
   logic [`DDR_CA_DQ_TX_DDR_PI_1_M0_R1_CFG_RANGE]     dq_dq_tx_ddr_pi_1_m0_r1_cfg;
   logic [`DDR_CA_DQ_TX_DDR_PI_1_M1_R0_CFG_RANGE]     dq_dq_tx_ddr_pi_1_m1_r0_cfg;
   logic [`DDR_CA_DQ_TX_DDR_PI_1_M1_R1_CFG_RANGE]     dq_dq_tx_ddr_pi_1_m1_r1_cfg;
   logic [`DDR_CA_DQ_TX_PI_RT_M0_R0_CFG_RANGE]        dq_dq_tx_pi_rt_m0_r0_cfg;
   logic [`DDR_CA_DQ_TX_PI_RT_M0_R1_CFG_RANGE]        dq_dq_tx_pi_rt_m0_r1_cfg;
   logic [`DDR_CA_DQ_TX_PI_RT_M1_R0_CFG_RANGE]        dq_dq_tx_pi_rt_m1_r0_cfg;
   logic [`DDR_CA_DQ_TX_PI_RT_M1_R1_CFG_RANGE]        dq_dq_tx_pi_rt_m1_r1_cfg;
   logic [`DDR_CA_DQ_TX_RT_M0_R0_CFG_RANGE]           dq_dq_tx_rt_m0_r0_cfg;
   logic [`DDR_CA_DQ_TX_RT_M0_R1_CFG_RANGE]           dq_dq_tx_rt_m0_r1_cfg;
   logic [`DDR_CA_DQ_TX_RT_M1_R0_CFG_RANGE]           dq_dq_tx_rt_m1_r0_cfg;
   logic [`DDR_CA_DQ_TX_RT_M1_R1_CFG_RANGE]           dq_dq_tx_rt_m1_r1_cfg;
   logic [`DDR_CA_DQ_TX_SDR_M0_R0_CFG_0_RANGE]        dq_dq_tx_sdr_m0_r0_cfg_0;
   logic [`DDR_CA_DQ_TX_SDR_M0_R0_CFG_1_RANGE]        dq_dq_tx_sdr_m0_r0_cfg_1;
   logic [`DDR_CA_DQ_TX_SDR_M0_R0_CFG_2_RANGE]        dq_dq_tx_sdr_m0_r0_cfg_2;
   logic [`DDR_CA_DQ_TX_SDR_M0_R0_CFG_3_RANGE]        dq_dq_tx_sdr_m0_r0_cfg_3;
   logic [`DDR_CA_DQ_TX_SDR_M0_R0_CFG_4_RANGE]        dq_dq_tx_sdr_m0_r0_cfg_4;
   logic [`DDR_CA_DQ_TX_SDR_M0_R0_CFG_5_RANGE]        dq_dq_tx_sdr_m0_r0_cfg_5;
   logic [`DDR_CA_DQ_TX_SDR_M0_R0_CFG_6_RANGE]        dq_dq_tx_sdr_m0_r0_cfg_6;
   logic [`DDR_CA_DQ_TX_SDR_M0_R0_CFG_7_RANGE]        dq_dq_tx_sdr_m0_r0_cfg_7;
   logic [`DDR_CA_DQ_TX_SDR_M0_R0_CFG_8_RANGE]        dq_dq_tx_sdr_m0_r0_cfg_8;
   logic [`DDR_CA_DQ_TX_SDR_M0_R0_CFG_9_RANGE]        dq_dq_tx_sdr_m0_r0_cfg_9;
   logic [`DDR_CA_DQ_TX_SDR_M0_R0_CFG_10_RANGE]        dq_dq_tx_sdr_m0_r0_cfg_10;
   logic [`DDR_CA_DQ_TX_SDR_M0_R1_CFG_0_RANGE]        dq_dq_tx_sdr_m0_r1_cfg_0;
   logic [`DDR_CA_DQ_TX_SDR_M0_R1_CFG_1_RANGE]        dq_dq_tx_sdr_m0_r1_cfg_1;
   logic [`DDR_CA_DQ_TX_SDR_M0_R1_CFG_2_RANGE]        dq_dq_tx_sdr_m0_r1_cfg_2;
   logic [`DDR_CA_DQ_TX_SDR_M0_R1_CFG_3_RANGE]        dq_dq_tx_sdr_m0_r1_cfg_3;
   logic [`DDR_CA_DQ_TX_SDR_M0_R1_CFG_4_RANGE]        dq_dq_tx_sdr_m0_r1_cfg_4;
   logic [`DDR_CA_DQ_TX_SDR_M0_R1_CFG_5_RANGE]        dq_dq_tx_sdr_m0_r1_cfg_5;
   logic [`DDR_CA_DQ_TX_SDR_M0_R1_CFG_6_RANGE]        dq_dq_tx_sdr_m0_r1_cfg_6;
   logic [`DDR_CA_DQ_TX_SDR_M0_R1_CFG_7_RANGE]        dq_dq_tx_sdr_m0_r1_cfg_7;
   logic [`DDR_CA_DQ_TX_SDR_M0_R1_CFG_8_RANGE]        dq_dq_tx_sdr_m0_r1_cfg_8;
   logic [`DDR_CA_DQ_TX_SDR_M0_R1_CFG_9_RANGE]        dq_dq_tx_sdr_m0_r1_cfg_9;
   logic [`DDR_CA_DQ_TX_SDR_M0_R1_CFG_10_RANGE]        dq_dq_tx_sdr_m0_r1_cfg_10;
   logic [`DDR_CA_DQ_TX_SDR_M1_R0_CFG_0_RANGE]        dq_dq_tx_sdr_m1_r0_cfg_0;
   logic [`DDR_CA_DQ_TX_SDR_M1_R0_CFG_1_RANGE]        dq_dq_tx_sdr_m1_r0_cfg_1;
   logic [`DDR_CA_DQ_TX_SDR_M1_R0_CFG_2_RANGE]        dq_dq_tx_sdr_m1_r0_cfg_2;
   logic [`DDR_CA_DQ_TX_SDR_M1_R0_CFG_3_RANGE]        dq_dq_tx_sdr_m1_r0_cfg_3;
   logic [`DDR_CA_DQ_TX_SDR_M1_R0_CFG_4_RANGE]        dq_dq_tx_sdr_m1_r0_cfg_4;
   logic [`DDR_CA_DQ_TX_SDR_M1_R0_CFG_5_RANGE]        dq_dq_tx_sdr_m1_r0_cfg_5;
   logic [`DDR_CA_DQ_TX_SDR_M1_R0_CFG_6_RANGE]        dq_dq_tx_sdr_m1_r0_cfg_6;
   logic [`DDR_CA_DQ_TX_SDR_M1_R0_CFG_7_RANGE]        dq_dq_tx_sdr_m1_r0_cfg_7;
   logic [`DDR_CA_DQ_TX_SDR_M1_R0_CFG_8_RANGE]        dq_dq_tx_sdr_m1_r0_cfg_8;
   logic [`DDR_CA_DQ_TX_SDR_M1_R0_CFG_9_RANGE]        dq_dq_tx_sdr_m1_r0_cfg_9;
   logic [`DDR_CA_DQ_TX_SDR_M1_R0_CFG_10_RANGE]        dq_dq_tx_sdr_m1_r0_cfg_10;
   logic [`DDR_CA_DQ_TX_SDR_M1_R1_CFG_0_RANGE]        dq_dq_tx_sdr_m1_r1_cfg_0;
   logic [`DDR_CA_DQ_TX_SDR_M1_R1_CFG_1_RANGE]        dq_dq_tx_sdr_m1_r1_cfg_1;
   logic [`DDR_CA_DQ_TX_SDR_M1_R1_CFG_2_RANGE]        dq_dq_tx_sdr_m1_r1_cfg_2;
   logic [`DDR_CA_DQ_TX_SDR_M1_R1_CFG_3_RANGE]        dq_dq_tx_sdr_m1_r1_cfg_3;
   logic [`DDR_CA_DQ_TX_SDR_M1_R1_CFG_4_RANGE]        dq_dq_tx_sdr_m1_r1_cfg_4;
   logic [`DDR_CA_DQ_TX_SDR_M1_R1_CFG_5_RANGE]        dq_dq_tx_sdr_m1_r1_cfg_5;
   logic [`DDR_CA_DQ_TX_SDR_M1_R1_CFG_6_RANGE]        dq_dq_tx_sdr_m1_r1_cfg_6;
   logic [`DDR_CA_DQ_TX_SDR_M1_R1_CFG_7_RANGE]        dq_dq_tx_sdr_m1_r1_cfg_7;
   logic [`DDR_CA_DQ_TX_SDR_M1_R1_CFG_8_RANGE]        dq_dq_tx_sdr_m1_r1_cfg_8;
   logic [`DDR_CA_DQ_TX_SDR_M1_R1_CFG_9_RANGE]        dq_dq_tx_sdr_m1_r1_cfg_9;
   logic [`DDR_CA_DQ_TX_SDR_M1_R1_CFG_10_RANGE]        dq_dq_tx_sdr_m1_r1_cfg_10;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_0_RANGE]     dq_dq_tx_sdr_x_sel_m0_r0_cfg_0;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_1_RANGE]     dq_dq_tx_sdr_x_sel_m0_r0_cfg_1;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_2_RANGE]     dq_dq_tx_sdr_x_sel_m0_r0_cfg_2;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_3_RANGE]     dq_dq_tx_sdr_x_sel_m0_r0_cfg_3;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_4_RANGE]     dq_dq_tx_sdr_x_sel_m0_r0_cfg_4;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_5_RANGE]     dq_dq_tx_sdr_x_sel_m0_r0_cfg_5;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_6_RANGE]     dq_dq_tx_sdr_x_sel_m0_r0_cfg_6;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_7_RANGE]     dq_dq_tx_sdr_x_sel_m0_r0_cfg_7;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_8_RANGE]     dq_dq_tx_sdr_x_sel_m0_r0_cfg_8;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_9_RANGE]     dq_dq_tx_sdr_x_sel_m0_r0_cfg_9;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_10_RANGE]     dq_dq_tx_sdr_x_sel_m0_r0_cfg_10;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_0_RANGE]     dq_dq_tx_sdr_x_sel_m0_r1_cfg_0;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_1_RANGE]     dq_dq_tx_sdr_x_sel_m0_r1_cfg_1;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_2_RANGE]     dq_dq_tx_sdr_x_sel_m0_r1_cfg_2;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_3_RANGE]     dq_dq_tx_sdr_x_sel_m0_r1_cfg_3;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_4_RANGE]     dq_dq_tx_sdr_x_sel_m0_r1_cfg_4;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_5_RANGE]     dq_dq_tx_sdr_x_sel_m0_r1_cfg_5;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_6_RANGE]     dq_dq_tx_sdr_x_sel_m0_r1_cfg_6;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_7_RANGE]     dq_dq_tx_sdr_x_sel_m0_r1_cfg_7;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_8_RANGE]     dq_dq_tx_sdr_x_sel_m0_r1_cfg_8;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_9_RANGE]     dq_dq_tx_sdr_x_sel_m0_r1_cfg_9;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_10_RANGE]     dq_dq_tx_sdr_x_sel_m0_r1_cfg_10;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_0_RANGE]     dq_dq_tx_sdr_x_sel_m1_r0_cfg_0;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_1_RANGE]     dq_dq_tx_sdr_x_sel_m1_r0_cfg_1;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_2_RANGE]     dq_dq_tx_sdr_x_sel_m1_r0_cfg_2;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_3_RANGE]     dq_dq_tx_sdr_x_sel_m1_r0_cfg_3;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_4_RANGE]     dq_dq_tx_sdr_x_sel_m1_r0_cfg_4;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_5_RANGE]     dq_dq_tx_sdr_x_sel_m1_r0_cfg_5;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_6_RANGE]     dq_dq_tx_sdr_x_sel_m1_r0_cfg_6;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_7_RANGE]     dq_dq_tx_sdr_x_sel_m1_r0_cfg_7;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_8_RANGE]     dq_dq_tx_sdr_x_sel_m1_r0_cfg_8;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_9_RANGE]     dq_dq_tx_sdr_x_sel_m1_r0_cfg_9;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_10_RANGE]     dq_dq_tx_sdr_x_sel_m1_r0_cfg_10;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_0_RANGE]     dq_dq_tx_sdr_x_sel_m1_r1_cfg_0;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_1_RANGE]     dq_dq_tx_sdr_x_sel_m1_r1_cfg_1;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_2_RANGE]     dq_dq_tx_sdr_x_sel_m1_r1_cfg_2;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_3_RANGE]     dq_dq_tx_sdr_x_sel_m1_r1_cfg_3;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_4_RANGE]     dq_dq_tx_sdr_x_sel_m1_r1_cfg_4;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_5_RANGE]     dq_dq_tx_sdr_x_sel_m1_r1_cfg_5;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_6_RANGE]     dq_dq_tx_sdr_x_sel_m1_r1_cfg_6;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_7_RANGE]     dq_dq_tx_sdr_x_sel_m1_r1_cfg_7;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_8_RANGE]     dq_dq_tx_sdr_x_sel_m1_r1_cfg_8;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_9_RANGE]     dq_dq_tx_sdr_x_sel_m1_r1_cfg_9;
   logic [`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_10_RANGE]     dq_dq_tx_sdr_x_sel_m1_r1_cfg_10;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_0_RANGE]    dq_dq_tx_sdr_fc_dly_m0_r0_cfg_0;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_1_RANGE]    dq_dq_tx_sdr_fc_dly_m0_r0_cfg_1;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_2_RANGE]    dq_dq_tx_sdr_fc_dly_m0_r0_cfg_2;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_3_RANGE]    dq_dq_tx_sdr_fc_dly_m0_r0_cfg_3;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_4_RANGE]    dq_dq_tx_sdr_fc_dly_m0_r0_cfg_4;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_5_RANGE]    dq_dq_tx_sdr_fc_dly_m0_r0_cfg_5;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_6_RANGE]    dq_dq_tx_sdr_fc_dly_m0_r0_cfg_6;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_7_RANGE]    dq_dq_tx_sdr_fc_dly_m0_r0_cfg_7;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_8_RANGE]    dq_dq_tx_sdr_fc_dly_m0_r0_cfg_8;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_9_RANGE]    dq_dq_tx_sdr_fc_dly_m0_r0_cfg_9;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_10_RANGE]    dq_dq_tx_sdr_fc_dly_m0_r0_cfg_10;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_0_RANGE]    dq_dq_tx_sdr_fc_dly_m0_r1_cfg_0;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_1_RANGE]    dq_dq_tx_sdr_fc_dly_m0_r1_cfg_1;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_2_RANGE]    dq_dq_tx_sdr_fc_dly_m0_r1_cfg_2;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_3_RANGE]    dq_dq_tx_sdr_fc_dly_m0_r1_cfg_3;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_4_RANGE]    dq_dq_tx_sdr_fc_dly_m0_r1_cfg_4;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_5_RANGE]    dq_dq_tx_sdr_fc_dly_m0_r1_cfg_5;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_6_RANGE]    dq_dq_tx_sdr_fc_dly_m0_r1_cfg_6;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_7_RANGE]    dq_dq_tx_sdr_fc_dly_m0_r1_cfg_7;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_8_RANGE]    dq_dq_tx_sdr_fc_dly_m0_r1_cfg_8;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_9_RANGE]    dq_dq_tx_sdr_fc_dly_m0_r1_cfg_9;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_10_RANGE]    dq_dq_tx_sdr_fc_dly_m0_r1_cfg_10;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_0_RANGE]    dq_dq_tx_sdr_fc_dly_m1_r0_cfg_0;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_1_RANGE]    dq_dq_tx_sdr_fc_dly_m1_r0_cfg_1;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_2_RANGE]    dq_dq_tx_sdr_fc_dly_m1_r0_cfg_2;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_3_RANGE]    dq_dq_tx_sdr_fc_dly_m1_r0_cfg_3;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_4_RANGE]    dq_dq_tx_sdr_fc_dly_m1_r0_cfg_4;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_5_RANGE]    dq_dq_tx_sdr_fc_dly_m1_r0_cfg_5;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_6_RANGE]    dq_dq_tx_sdr_fc_dly_m1_r0_cfg_6;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_7_RANGE]    dq_dq_tx_sdr_fc_dly_m1_r0_cfg_7;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_8_RANGE]    dq_dq_tx_sdr_fc_dly_m1_r0_cfg_8;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_9_RANGE]    dq_dq_tx_sdr_fc_dly_m1_r0_cfg_9;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_10_RANGE]    dq_dq_tx_sdr_fc_dly_m1_r0_cfg_10;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_0_RANGE]    dq_dq_tx_sdr_fc_dly_m1_r1_cfg_0;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_1_RANGE]    dq_dq_tx_sdr_fc_dly_m1_r1_cfg_1;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_2_RANGE]    dq_dq_tx_sdr_fc_dly_m1_r1_cfg_2;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_3_RANGE]    dq_dq_tx_sdr_fc_dly_m1_r1_cfg_3;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_4_RANGE]    dq_dq_tx_sdr_fc_dly_m1_r1_cfg_4;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_5_RANGE]    dq_dq_tx_sdr_fc_dly_m1_r1_cfg_5;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_6_RANGE]    dq_dq_tx_sdr_fc_dly_m1_r1_cfg_6;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_7_RANGE]    dq_dq_tx_sdr_fc_dly_m1_r1_cfg_7;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_8_RANGE]    dq_dq_tx_sdr_fc_dly_m1_r1_cfg_8;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_9_RANGE]    dq_dq_tx_sdr_fc_dly_m1_r1_cfg_9;
   logic [`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_10_RANGE]    dq_dq_tx_sdr_fc_dly_m1_r1_cfg_10;
   logic [(MAX_MXWIDTH)*DQ_WIDTH-1:0]                              dq_sdr_0_x_sel;
   logic [(MAX_MXWIDTH)*DQ_WIDTH-1:0]                              dq_sdr_1_x_sel;
   logic [(MAX_MXWIDTH)*DQ_WIDTH-1:0]                              dq_sdr_2_x_sel;
   logic [(MAX_MXWIDTH)*DQ_WIDTH-1:0]                              dq_sdr_3_x_sel;
   logic [(MAX_MXWIDTH-1)*DQ_WIDTH-1:0]                            dq_ddr_0_x_sel;
   logic [(MAX_MXWIDTH-1)*DQ_WIDTH-1:0]                            dq_ddr_1_x_sel;
   logic [(MAX_MXWIDTH-2)*DQ_WIDTH-1:0]                            dq_qdr_0_x_sel;
   logic [`DDR_CA_DQ_TX_DDR_M0_R0_CFG_0_RANGE]        dq_dq_tx_ddr_m0_r0_cfg_0;
   logic [`DDR_CA_DQ_TX_DDR_M0_R0_CFG_1_RANGE]        dq_dq_tx_ddr_m0_r0_cfg_1;
   logic [`DDR_CA_DQ_TX_DDR_M0_R0_CFG_2_RANGE]        dq_dq_tx_ddr_m0_r0_cfg_2;
   logic [`DDR_CA_DQ_TX_DDR_M0_R0_CFG_3_RANGE]        dq_dq_tx_ddr_m0_r0_cfg_3;
   logic [`DDR_CA_DQ_TX_DDR_M0_R0_CFG_4_RANGE]        dq_dq_tx_ddr_m0_r0_cfg_4;
   logic [`DDR_CA_DQ_TX_DDR_M0_R0_CFG_5_RANGE]        dq_dq_tx_ddr_m0_r0_cfg_5;
   logic [`DDR_CA_DQ_TX_DDR_M0_R0_CFG_6_RANGE]        dq_dq_tx_ddr_m0_r0_cfg_6;
   logic [`DDR_CA_DQ_TX_DDR_M0_R0_CFG_7_RANGE]        dq_dq_tx_ddr_m0_r0_cfg_7;
   logic [`DDR_CA_DQ_TX_DDR_M0_R0_CFG_8_RANGE]        dq_dq_tx_ddr_m0_r0_cfg_8;
   logic [`DDR_CA_DQ_TX_DDR_M0_R0_CFG_9_RANGE]        dq_dq_tx_ddr_m0_r0_cfg_9;
   logic [`DDR_CA_DQ_TX_DDR_M0_R0_CFG_10_RANGE]        dq_dq_tx_ddr_m0_r0_cfg_10;
   logic [`DDR_CA_DQ_TX_DDR_M0_R1_CFG_0_RANGE]        dq_dq_tx_ddr_m0_r1_cfg_0;
   logic [`DDR_CA_DQ_TX_DDR_M0_R1_CFG_1_RANGE]        dq_dq_tx_ddr_m0_r1_cfg_1;
   logic [`DDR_CA_DQ_TX_DDR_M0_R1_CFG_2_RANGE]        dq_dq_tx_ddr_m0_r1_cfg_2;
   logic [`DDR_CA_DQ_TX_DDR_M0_R1_CFG_3_RANGE]        dq_dq_tx_ddr_m0_r1_cfg_3;
   logic [`DDR_CA_DQ_TX_DDR_M0_R1_CFG_4_RANGE]        dq_dq_tx_ddr_m0_r1_cfg_4;
   logic [`DDR_CA_DQ_TX_DDR_M0_R1_CFG_5_RANGE]        dq_dq_tx_ddr_m0_r1_cfg_5;
   logic [`DDR_CA_DQ_TX_DDR_M0_R1_CFG_6_RANGE]        dq_dq_tx_ddr_m0_r1_cfg_6;
   logic [`DDR_CA_DQ_TX_DDR_M0_R1_CFG_7_RANGE]        dq_dq_tx_ddr_m0_r1_cfg_7;
   logic [`DDR_CA_DQ_TX_DDR_M0_R1_CFG_8_RANGE]        dq_dq_tx_ddr_m0_r1_cfg_8;
   logic [`DDR_CA_DQ_TX_DDR_M0_R1_CFG_9_RANGE]        dq_dq_tx_ddr_m0_r1_cfg_9;
   logic [`DDR_CA_DQ_TX_DDR_M0_R1_CFG_10_RANGE]        dq_dq_tx_ddr_m0_r1_cfg_10;
   logic [`DDR_CA_DQ_TX_DDR_M1_R0_CFG_0_RANGE]        dq_dq_tx_ddr_m1_r0_cfg_0;
   logic [`DDR_CA_DQ_TX_DDR_M1_R0_CFG_1_RANGE]        dq_dq_tx_ddr_m1_r0_cfg_1;
   logic [`DDR_CA_DQ_TX_DDR_M1_R0_CFG_2_RANGE]        dq_dq_tx_ddr_m1_r0_cfg_2;
   logic [`DDR_CA_DQ_TX_DDR_M1_R0_CFG_3_RANGE]        dq_dq_tx_ddr_m1_r0_cfg_3;
   logic [`DDR_CA_DQ_TX_DDR_M1_R0_CFG_4_RANGE]        dq_dq_tx_ddr_m1_r0_cfg_4;
   logic [`DDR_CA_DQ_TX_DDR_M1_R0_CFG_5_RANGE]        dq_dq_tx_ddr_m1_r0_cfg_5;
   logic [`DDR_CA_DQ_TX_DDR_M1_R0_CFG_6_RANGE]        dq_dq_tx_ddr_m1_r0_cfg_6;
   logic [`DDR_CA_DQ_TX_DDR_M1_R0_CFG_7_RANGE]        dq_dq_tx_ddr_m1_r0_cfg_7;
   logic [`DDR_CA_DQ_TX_DDR_M1_R0_CFG_8_RANGE]        dq_dq_tx_ddr_m1_r0_cfg_8;
   logic [`DDR_CA_DQ_TX_DDR_M1_R0_CFG_9_RANGE]        dq_dq_tx_ddr_m1_r0_cfg_9;
   logic [`DDR_CA_DQ_TX_DDR_M1_R0_CFG_10_RANGE]        dq_dq_tx_ddr_m1_r0_cfg_10;
   logic [`DDR_CA_DQ_TX_DDR_M1_R1_CFG_0_RANGE]        dq_dq_tx_ddr_m1_r1_cfg_0;
   logic [`DDR_CA_DQ_TX_DDR_M1_R1_CFG_1_RANGE]        dq_dq_tx_ddr_m1_r1_cfg_1;
   logic [`DDR_CA_DQ_TX_DDR_M1_R1_CFG_2_RANGE]        dq_dq_tx_ddr_m1_r1_cfg_2;
   logic [`DDR_CA_DQ_TX_DDR_M1_R1_CFG_3_RANGE]        dq_dq_tx_ddr_m1_r1_cfg_3;
   logic [`DDR_CA_DQ_TX_DDR_M1_R1_CFG_4_RANGE]        dq_dq_tx_ddr_m1_r1_cfg_4;
   logic [`DDR_CA_DQ_TX_DDR_M1_R1_CFG_5_RANGE]        dq_dq_tx_ddr_m1_r1_cfg_5;
   logic [`DDR_CA_DQ_TX_DDR_M1_R1_CFG_6_RANGE]        dq_dq_tx_ddr_m1_r1_cfg_6;
   logic [`DDR_CA_DQ_TX_DDR_M1_R1_CFG_7_RANGE]        dq_dq_tx_ddr_m1_r1_cfg_7;
   logic [`DDR_CA_DQ_TX_DDR_M1_R1_CFG_8_RANGE]        dq_dq_tx_ddr_m1_r1_cfg_8;
   logic [`DDR_CA_DQ_TX_DDR_M1_R1_CFG_9_RANGE]        dq_dq_tx_ddr_m1_r1_cfg_9;
   logic [`DDR_CA_DQ_TX_DDR_M1_R1_CFG_10_RANGE]        dq_dq_tx_ddr_m1_r1_cfg_10;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_0_RANGE]  dq_dq_tx_ddr_x_sel_m0_r0_cfg_0;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_1_RANGE]  dq_dq_tx_ddr_x_sel_m0_r0_cfg_1;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_2_RANGE]  dq_dq_tx_ddr_x_sel_m0_r0_cfg_2;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_3_RANGE]  dq_dq_tx_ddr_x_sel_m0_r0_cfg_3;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_4_RANGE]  dq_dq_tx_ddr_x_sel_m0_r0_cfg_4;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_5_RANGE]  dq_dq_tx_ddr_x_sel_m0_r0_cfg_5;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_6_RANGE]  dq_dq_tx_ddr_x_sel_m0_r0_cfg_6;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_7_RANGE]  dq_dq_tx_ddr_x_sel_m0_r0_cfg_7;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_8_RANGE]  dq_dq_tx_ddr_x_sel_m0_r0_cfg_8;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_9_RANGE]  dq_dq_tx_ddr_x_sel_m0_r0_cfg_9;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_10_RANGE]  dq_dq_tx_ddr_x_sel_m0_r0_cfg_10;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_0_RANGE]  dq_dq_tx_ddr_x_sel_m0_r1_cfg_0;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_1_RANGE]  dq_dq_tx_ddr_x_sel_m0_r1_cfg_1;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_2_RANGE]  dq_dq_tx_ddr_x_sel_m0_r1_cfg_2;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_3_RANGE]  dq_dq_tx_ddr_x_sel_m0_r1_cfg_3;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_4_RANGE]  dq_dq_tx_ddr_x_sel_m0_r1_cfg_4;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_5_RANGE]  dq_dq_tx_ddr_x_sel_m0_r1_cfg_5;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_6_RANGE]  dq_dq_tx_ddr_x_sel_m0_r1_cfg_6;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_7_RANGE]  dq_dq_tx_ddr_x_sel_m0_r1_cfg_7;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_8_RANGE]  dq_dq_tx_ddr_x_sel_m0_r1_cfg_8;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_9_RANGE]  dq_dq_tx_ddr_x_sel_m0_r1_cfg_9;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_10_RANGE]  dq_dq_tx_ddr_x_sel_m0_r1_cfg_10;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_0_RANGE]  dq_dq_tx_ddr_x_sel_m1_r0_cfg_0;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_1_RANGE]  dq_dq_tx_ddr_x_sel_m1_r0_cfg_1;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_2_RANGE]  dq_dq_tx_ddr_x_sel_m1_r0_cfg_2;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_3_RANGE]  dq_dq_tx_ddr_x_sel_m1_r0_cfg_3;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_4_RANGE]  dq_dq_tx_ddr_x_sel_m1_r0_cfg_4;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_5_RANGE]  dq_dq_tx_ddr_x_sel_m1_r0_cfg_5;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_6_RANGE]  dq_dq_tx_ddr_x_sel_m1_r0_cfg_6;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_7_RANGE]  dq_dq_tx_ddr_x_sel_m1_r0_cfg_7;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_8_RANGE]  dq_dq_tx_ddr_x_sel_m1_r0_cfg_8;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_9_RANGE]  dq_dq_tx_ddr_x_sel_m1_r0_cfg_9;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_10_RANGE]  dq_dq_tx_ddr_x_sel_m1_r0_cfg_10;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_0_RANGE]  dq_dq_tx_ddr_x_sel_m1_r1_cfg_0;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_1_RANGE]  dq_dq_tx_ddr_x_sel_m1_r1_cfg_1;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_2_RANGE]  dq_dq_tx_ddr_x_sel_m1_r1_cfg_2;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_3_RANGE]  dq_dq_tx_ddr_x_sel_m1_r1_cfg_3;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_4_RANGE]  dq_dq_tx_ddr_x_sel_m1_r1_cfg_4;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_5_RANGE]  dq_dq_tx_ddr_x_sel_m1_r1_cfg_5;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_6_RANGE]  dq_dq_tx_ddr_x_sel_m1_r1_cfg_6;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_7_RANGE]  dq_dq_tx_ddr_x_sel_m1_r1_cfg_7;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_8_RANGE]  dq_dq_tx_ddr_x_sel_m1_r1_cfg_8;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_9_RANGE]  dq_dq_tx_ddr_x_sel_m1_r1_cfg_9;
   logic [`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_10_RANGE]  dq_dq_tx_ddr_x_sel_m1_r1_cfg_10;
   logic [`DDR_CA_DQ_TX_QDR_M0_R0_CFG_0_RANGE]        dq_dq_tx_qdr_m0_r0_cfg_0;
   logic [`DDR_CA_DQ_TX_QDR_M0_R0_CFG_1_RANGE]        dq_dq_tx_qdr_m0_r0_cfg_1;
   logic [`DDR_CA_DQ_TX_QDR_M0_R0_CFG_2_RANGE]        dq_dq_tx_qdr_m0_r0_cfg_2;
   logic [`DDR_CA_DQ_TX_QDR_M0_R0_CFG_3_RANGE]        dq_dq_tx_qdr_m0_r0_cfg_3;
   logic [`DDR_CA_DQ_TX_QDR_M0_R0_CFG_4_RANGE]        dq_dq_tx_qdr_m0_r0_cfg_4;
   logic [`DDR_CA_DQ_TX_QDR_M0_R0_CFG_5_RANGE]        dq_dq_tx_qdr_m0_r0_cfg_5;
   logic [`DDR_CA_DQ_TX_QDR_M0_R0_CFG_6_RANGE]        dq_dq_tx_qdr_m0_r0_cfg_6;
   logic [`DDR_CA_DQ_TX_QDR_M0_R0_CFG_7_RANGE]        dq_dq_tx_qdr_m0_r0_cfg_7;
   logic [`DDR_CA_DQ_TX_QDR_M0_R0_CFG_8_RANGE]        dq_dq_tx_qdr_m0_r0_cfg_8;
   logic [`DDR_CA_DQ_TX_QDR_M0_R0_CFG_9_RANGE]        dq_dq_tx_qdr_m0_r0_cfg_9;
   logic [`DDR_CA_DQ_TX_QDR_M0_R0_CFG_10_RANGE]        dq_dq_tx_qdr_m0_r0_cfg_10;
   logic [`DDR_CA_DQ_TX_QDR_M0_R1_CFG_0_RANGE]        dq_dq_tx_qdr_m0_r1_cfg_0;
   logic [`DDR_CA_DQ_TX_QDR_M0_R1_CFG_1_RANGE]        dq_dq_tx_qdr_m0_r1_cfg_1;
   logic [`DDR_CA_DQ_TX_QDR_M0_R1_CFG_2_RANGE]        dq_dq_tx_qdr_m0_r1_cfg_2;
   logic [`DDR_CA_DQ_TX_QDR_M0_R1_CFG_3_RANGE]        dq_dq_tx_qdr_m0_r1_cfg_3;
   logic [`DDR_CA_DQ_TX_QDR_M0_R1_CFG_4_RANGE]        dq_dq_tx_qdr_m0_r1_cfg_4;
   logic [`DDR_CA_DQ_TX_QDR_M0_R1_CFG_5_RANGE]        dq_dq_tx_qdr_m0_r1_cfg_5;
   logic [`DDR_CA_DQ_TX_QDR_M0_R1_CFG_6_RANGE]        dq_dq_tx_qdr_m0_r1_cfg_6;
   logic [`DDR_CA_DQ_TX_QDR_M0_R1_CFG_7_RANGE]        dq_dq_tx_qdr_m0_r1_cfg_7;
   logic [`DDR_CA_DQ_TX_QDR_M0_R1_CFG_8_RANGE]        dq_dq_tx_qdr_m0_r1_cfg_8;
   logic [`DDR_CA_DQ_TX_QDR_M0_R1_CFG_9_RANGE]        dq_dq_tx_qdr_m0_r1_cfg_9;
   logic [`DDR_CA_DQ_TX_QDR_M0_R1_CFG_10_RANGE]        dq_dq_tx_qdr_m0_r1_cfg_10;
   logic [`DDR_CA_DQ_TX_QDR_M1_R0_CFG_0_RANGE]        dq_dq_tx_qdr_m1_r0_cfg_0;
   logic [`DDR_CA_DQ_TX_QDR_M1_R0_CFG_1_RANGE]        dq_dq_tx_qdr_m1_r0_cfg_1;
   logic [`DDR_CA_DQ_TX_QDR_M1_R0_CFG_2_RANGE]        dq_dq_tx_qdr_m1_r0_cfg_2;
   logic [`DDR_CA_DQ_TX_QDR_M1_R0_CFG_3_RANGE]        dq_dq_tx_qdr_m1_r0_cfg_3;
   logic [`DDR_CA_DQ_TX_QDR_M1_R0_CFG_4_RANGE]        dq_dq_tx_qdr_m1_r0_cfg_4;
   logic [`DDR_CA_DQ_TX_QDR_M1_R0_CFG_5_RANGE]        dq_dq_tx_qdr_m1_r0_cfg_5;
   logic [`DDR_CA_DQ_TX_QDR_M1_R0_CFG_6_RANGE]        dq_dq_tx_qdr_m1_r0_cfg_6;
   logic [`DDR_CA_DQ_TX_QDR_M1_R0_CFG_7_RANGE]        dq_dq_tx_qdr_m1_r0_cfg_7;
   logic [`DDR_CA_DQ_TX_QDR_M1_R0_CFG_8_RANGE]        dq_dq_tx_qdr_m1_r0_cfg_8;
   logic [`DDR_CA_DQ_TX_QDR_M1_R0_CFG_9_RANGE]        dq_dq_tx_qdr_m1_r0_cfg_9;
   logic [`DDR_CA_DQ_TX_QDR_M1_R0_CFG_10_RANGE]        dq_dq_tx_qdr_m1_r0_cfg_10;
   logic [`DDR_CA_DQ_TX_QDR_M1_R1_CFG_0_RANGE]        dq_dq_tx_qdr_m1_r1_cfg_0;
   logic [`DDR_CA_DQ_TX_QDR_M1_R1_CFG_1_RANGE]        dq_dq_tx_qdr_m1_r1_cfg_1;
   logic [`DDR_CA_DQ_TX_QDR_M1_R1_CFG_2_RANGE]        dq_dq_tx_qdr_m1_r1_cfg_2;
   logic [`DDR_CA_DQ_TX_QDR_M1_R1_CFG_3_RANGE]        dq_dq_tx_qdr_m1_r1_cfg_3;
   logic [`DDR_CA_DQ_TX_QDR_M1_R1_CFG_4_RANGE]        dq_dq_tx_qdr_m1_r1_cfg_4;
   logic [`DDR_CA_DQ_TX_QDR_M1_R1_CFG_5_RANGE]        dq_dq_tx_qdr_m1_r1_cfg_5;
   logic [`DDR_CA_DQ_TX_QDR_M1_R1_CFG_6_RANGE]        dq_dq_tx_qdr_m1_r1_cfg_6;
   logic [`DDR_CA_DQ_TX_QDR_M1_R1_CFG_7_RANGE]        dq_dq_tx_qdr_m1_r1_cfg_7;
   logic [`DDR_CA_DQ_TX_QDR_M1_R1_CFG_8_RANGE]        dq_dq_tx_qdr_m1_r1_cfg_8;
   logic [`DDR_CA_DQ_TX_QDR_M1_R1_CFG_9_RANGE]        dq_dq_tx_qdr_m1_r1_cfg_9;
   logic [`DDR_CA_DQ_TX_QDR_M1_R1_CFG_10_RANGE]        dq_dq_tx_qdr_m1_r1_cfg_10;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_0_RANGE]  dq_dq_tx_qdr_x_sel_m0_r0_cfg_0;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_1_RANGE]  dq_dq_tx_qdr_x_sel_m0_r0_cfg_1;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_2_RANGE]  dq_dq_tx_qdr_x_sel_m0_r0_cfg_2;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_3_RANGE]  dq_dq_tx_qdr_x_sel_m0_r0_cfg_3;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_4_RANGE]  dq_dq_tx_qdr_x_sel_m0_r0_cfg_4;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_5_RANGE]  dq_dq_tx_qdr_x_sel_m0_r0_cfg_5;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_6_RANGE]  dq_dq_tx_qdr_x_sel_m0_r0_cfg_6;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_7_RANGE]  dq_dq_tx_qdr_x_sel_m0_r0_cfg_7;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_8_RANGE]  dq_dq_tx_qdr_x_sel_m0_r0_cfg_8;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_9_RANGE]  dq_dq_tx_qdr_x_sel_m0_r0_cfg_9;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_10_RANGE]  dq_dq_tx_qdr_x_sel_m0_r0_cfg_10;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_0_RANGE]  dq_dq_tx_qdr_x_sel_m0_r1_cfg_0;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_1_RANGE]  dq_dq_tx_qdr_x_sel_m0_r1_cfg_1;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_2_RANGE]  dq_dq_tx_qdr_x_sel_m0_r1_cfg_2;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_3_RANGE]  dq_dq_tx_qdr_x_sel_m0_r1_cfg_3;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_4_RANGE]  dq_dq_tx_qdr_x_sel_m0_r1_cfg_4;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_5_RANGE]  dq_dq_tx_qdr_x_sel_m0_r1_cfg_5;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_6_RANGE]  dq_dq_tx_qdr_x_sel_m0_r1_cfg_6;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_7_RANGE]  dq_dq_tx_qdr_x_sel_m0_r1_cfg_7;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_8_RANGE]  dq_dq_tx_qdr_x_sel_m0_r1_cfg_8;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_9_RANGE]  dq_dq_tx_qdr_x_sel_m0_r1_cfg_9;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_10_RANGE]  dq_dq_tx_qdr_x_sel_m0_r1_cfg_10;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_0_RANGE]  dq_dq_tx_qdr_x_sel_m1_r0_cfg_0;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_1_RANGE]  dq_dq_tx_qdr_x_sel_m1_r0_cfg_1;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_2_RANGE]  dq_dq_tx_qdr_x_sel_m1_r0_cfg_2;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_3_RANGE]  dq_dq_tx_qdr_x_sel_m1_r0_cfg_3;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_4_RANGE]  dq_dq_tx_qdr_x_sel_m1_r0_cfg_4;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_5_RANGE]  dq_dq_tx_qdr_x_sel_m1_r0_cfg_5;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_6_RANGE]  dq_dq_tx_qdr_x_sel_m1_r0_cfg_6;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_7_RANGE]  dq_dq_tx_qdr_x_sel_m1_r0_cfg_7;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_8_RANGE]  dq_dq_tx_qdr_x_sel_m1_r0_cfg_8;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_9_RANGE]  dq_dq_tx_qdr_x_sel_m1_r0_cfg_9;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_10_RANGE]  dq_dq_tx_qdr_x_sel_m1_r0_cfg_10;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_0_RANGE]  dq_dq_tx_qdr_x_sel_m1_r1_cfg_0;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_1_RANGE]  dq_dq_tx_qdr_x_sel_m1_r1_cfg_1;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_2_RANGE]  dq_dq_tx_qdr_x_sel_m1_r1_cfg_2;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_3_RANGE]  dq_dq_tx_qdr_x_sel_m1_r1_cfg_3;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_4_RANGE]  dq_dq_tx_qdr_x_sel_m1_r1_cfg_4;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_5_RANGE]  dq_dq_tx_qdr_x_sel_m1_r1_cfg_5;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_6_RANGE]  dq_dq_tx_qdr_x_sel_m1_r1_cfg_6;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_7_RANGE]  dq_dq_tx_qdr_x_sel_m1_r1_cfg_7;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_8_RANGE]  dq_dq_tx_qdr_x_sel_m1_r1_cfg_8;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_9_RANGE]  dq_dq_tx_qdr_x_sel_m1_r1_cfg_9;
   logic [`DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_10_RANGE]  dq_dq_tx_qdr_x_sel_m1_r1_cfg_10;
   logic [`DDR_CA_DQ_TX_LPDE_M0_R0_CFG_0_RANGE]       dq_dq_tx_lpde_m0_r0_cfg_0;
   logic [`DDR_CA_DQ_TX_LPDE_M0_R0_CFG_1_RANGE]       dq_dq_tx_lpde_m0_r0_cfg_1;
   logic [`DDR_CA_DQ_TX_LPDE_M0_R0_CFG_2_RANGE]       dq_dq_tx_lpde_m0_r0_cfg_2;
   logic [`DDR_CA_DQ_TX_LPDE_M0_R0_CFG_3_RANGE]       dq_dq_tx_lpde_m0_r0_cfg_3;
   logic [`DDR_CA_DQ_TX_LPDE_M0_R0_CFG_4_RANGE]       dq_dq_tx_lpde_m0_r0_cfg_4;
   logic [`DDR_CA_DQ_TX_LPDE_M0_R0_CFG_5_RANGE]       dq_dq_tx_lpde_m0_r0_cfg_5;
   logic [`DDR_CA_DQ_TX_LPDE_M0_R0_CFG_6_RANGE]       dq_dq_tx_lpde_m0_r0_cfg_6;
   logic [`DDR_CA_DQ_TX_LPDE_M0_R0_CFG_7_RANGE]       dq_dq_tx_lpde_m0_r0_cfg_7;
   logic [`DDR_CA_DQ_TX_LPDE_M0_R0_CFG_8_RANGE]       dq_dq_tx_lpde_m0_r0_cfg_8;
   logic [`DDR_CA_DQ_TX_LPDE_M0_R0_CFG_9_RANGE]       dq_dq_tx_lpde_m0_r0_cfg_9;
   logic [`DDR_CA_DQ_TX_LPDE_M0_R0_CFG_10_RANGE]       dq_dq_tx_lpde_m0_r0_cfg_10;
   logic [`DDR_CA_DQ_TX_LPDE_M0_R1_CFG_0_RANGE]       dq_dq_tx_lpde_m0_r1_cfg_0;
   logic [`DDR_CA_DQ_TX_LPDE_M0_R1_CFG_1_RANGE]       dq_dq_tx_lpde_m0_r1_cfg_1;
   logic [`DDR_CA_DQ_TX_LPDE_M0_R1_CFG_2_RANGE]       dq_dq_tx_lpde_m0_r1_cfg_2;
   logic [`DDR_CA_DQ_TX_LPDE_M0_R1_CFG_3_RANGE]       dq_dq_tx_lpde_m0_r1_cfg_3;
   logic [`DDR_CA_DQ_TX_LPDE_M0_R1_CFG_4_RANGE]       dq_dq_tx_lpde_m0_r1_cfg_4;
   logic [`DDR_CA_DQ_TX_LPDE_M0_R1_CFG_5_RANGE]       dq_dq_tx_lpde_m0_r1_cfg_5;
   logic [`DDR_CA_DQ_TX_LPDE_M0_R1_CFG_6_RANGE]       dq_dq_tx_lpde_m0_r1_cfg_6;
   logic [`DDR_CA_DQ_TX_LPDE_M0_R1_CFG_7_RANGE]       dq_dq_tx_lpde_m0_r1_cfg_7;
   logic [`DDR_CA_DQ_TX_LPDE_M0_R1_CFG_8_RANGE]       dq_dq_tx_lpde_m0_r1_cfg_8;
   logic [`DDR_CA_DQ_TX_LPDE_M0_R1_CFG_9_RANGE]       dq_dq_tx_lpde_m0_r1_cfg_9;
   logic [`DDR_CA_DQ_TX_LPDE_M0_R1_CFG_10_RANGE]       dq_dq_tx_lpde_m0_r1_cfg_10;
   logic [`DDR_CA_DQ_TX_LPDE_M1_R0_CFG_0_RANGE]       dq_dq_tx_lpde_m1_r0_cfg_0;
   logic [`DDR_CA_DQ_TX_LPDE_M1_R0_CFG_1_RANGE]       dq_dq_tx_lpde_m1_r0_cfg_1;
   logic [`DDR_CA_DQ_TX_LPDE_M1_R0_CFG_2_RANGE]       dq_dq_tx_lpde_m1_r0_cfg_2;
   logic [`DDR_CA_DQ_TX_LPDE_M1_R0_CFG_3_RANGE]       dq_dq_tx_lpde_m1_r0_cfg_3;
   logic [`DDR_CA_DQ_TX_LPDE_M1_R0_CFG_4_RANGE]       dq_dq_tx_lpde_m1_r0_cfg_4;
   logic [`DDR_CA_DQ_TX_LPDE_M1_R0_CFG_5_RANGE]       dq_dq_tx_lpde_m1_r0_cfg_5;
   logic [`DDR_CA_DQ_TX_LPDE_M1_R0_CFG_6_RANGE]       dq_dq_tx_lpde_m1_r0_cfg_6;
   logic [`DDR_CA_DQ_TX_LPDE_M1_R0_CFG_7_RANGE]       dq_dq_tx_lpde_m1_r0_cfg_7;
   logic [`DDR_CA_DQ_TX_LPDE_M1_R0_CFG_8_RANGE]       dq_dq_tx_lpde_m1_r0_cfg_8;
   logic [`DDR_CA_DQ_TX_LPDE_M1_R0_CFG_9_RANGE]       dq_dq_tx_lpde_m1_r0_cfg_9;
   logic [`DDR_CA_DQ_TX_LPDE_M1_R0_CFG_10_RANGE]       dq_dq_tx_lpde_m1_r0_cfg_10;
   logic [`DDR_CA_DQ_TX_LPDE_M1_R1_CFG_0_RANGE]       dq_dq_tx_lpde_m1_r1_cfg_0;
   logic [`DDR_CA_DQ_TX_LPDE_M1_R1_CFG_1_RANGE]       dq_dq_tx_lpde_m1_r1_cfg_1;
   logic [`DDR_CA_DQ_TX_LPDE_M1_R1_CFG_2_RANGE]       dq_dq_tx_lpde_m1_r1_cfg_2;
   logic [`DDR_CA_DQ_TX_LPDE_M1_R1_CFG_3_RANGE]       dq_dq_tx_lpde_m1_r1_cfg_3;
   logic [`DDR_CA_DQ_TX_LPDE_M1_R1_CFG_4_RANGE]       dq_dq_tx_lpde_m1_r1_cfg_4;
   logic [`DDR_CA_DQ_TX_LPDE_M1_R1_CFG_5_RANGE]       dq_dq_tx_lpde_m1_r1_cfg_5;
   logic [`DDR_CA_DQ_TX_LPDE_M1_R1_CFG_6_RANGE]       dq_dq_tx_lpde_m1_r1_cfg_6;
   logic [`DDR_CA_DQ_TX_LPDE_M1_R1_CFG_7_RANGE]       dq_dq_tx_lpde_m1_r1_cfg_7;
   logic [`DDR_CA_DQ_TX_LPDE_M1_R1_CFG_8_RANGE]       dq_dq_tx_lpde_m1_r1_cfg_8;
   logic [`DDR_CA_DQ_TX_LPDE_M1_R1_CFG_9_RANGE]       dq_dq_tx_lpde_m1_r1_cfg_9;
   logic [`DDR_CA_DQ_TX_LPDE_M1_R1_CFG_10_RANGE]       dq_dq_tx_lpde_m1_r1_cfg_10;
//`for (i=0; i<`DDR_NUM_CA_SLICES; i++)
//   logic [`DDR_CA_DQ_TX_IO_M0_R0_CFG_`i::_RANGE]         dq_dq_tx_io_m0_r0_cfg_`i;
//`endfor
//`for (i=0; i<`DDR_NUM_CA_SLICES; i++)
//   logic [`DDR_CA_DQ_TX_IO_M0_R1_CFG_`i::_RANGE]         dq_dq_tx_io_m0_r1_cfg_`i;
//`endfor
//`for (i=0; i<`DDR_NUM_CA_SLICES; i++)
//   logic [`DDR_CA_DQ_TX_IO_M1_R0_CFG_`i::_RANGE]         dq_dq_tx_io_m1_r0_cfg_`i;
//`endfor
//`for (i=0; i<`DDR_NUM_CA_SLICES; i++)
//   logic [`DDR_CA_DQ_TX_IO_M1_R1_CFG_`i::_RANGE]         dq_dq_tx_io_m1_r1_cfg_`i;
//`endfor
   logic [`DDR_CA_DQ_TX_IO_M0_CFG_0_RANGE]            dq_dq_tx_io_m0_cfg_0;
   logic [`DDR_CA_DQ_TX_IO_M0_CFG_1_RANGE]            dq_dq_tx_io_m0_cfg_1;
   logic [`DDR_CA_DQ_TX_IO_M0_CFG_2_RANGE]            dq_dq_tx_io_m0_cfg_2;
   logic [`DDR_CA_DQ_TX_IO_M0_CFG_3_RANGE]            dq_dq_tx_io_m0_cfg_3;
   logic [`DDR_CA_DQ_TX_IO_M0_CFG_4_RANGE]            dq_dq_tx_io_m0_cfg_4;
   logic [`DDR_CA_DQ_TX_IO_M0_CFG_5_RANGE]            dq_dq_tx_io_m0_cfg_5;
   logic [`DDR_CA_DQ_TX_IO_M0_CFG_6_RANGE]            dq_dq_tx_io_m0_cfg_6;
   logic [`DDR_CA_DQ_TX_IO_M0_CFG_7_RANGE]            dq_dq_tx_io_m0_cfg_7;
   logic [`DDR_CA_DQ_TX_IO_M0_CFG_8_RANGE]            dq_dq_tx_io_m0_cfg_8;
   logic [`DDR_CA_DQ_TX_IO_M0_CFG_9_RANGE]            dq_dq_tx_io_m0_cfg_9;
   logic [`DDR_CA_DQ_TX_IO_M0_CFG_10_RANGE]            dq_dq_tx_io_m0_cfg_10;
   logic [`DDR_CA_DQ_TX_IO_M1_CFG_0_RANGE]            dq_dq_tx_io_m1_cfg_0;
   logic [`DDR_CA_DQ_TX_IO_M1_CFG_1_RANGE]            dq_dq_tx_io_m1_cfg_1;
   logic [`DDR_CA_DQ_TX_IO_M1_CFG_2_RANGE]            dq_dq_tx_io_m1_cfg_2;
   logic [`DDR_CA_DQ_TX_IO_M1_CFG_3_RANGE]            dq_dq_tx_io_m1_cfg_3;
   logic [`DDR_CA_DQ_TX_IO_M1_CFG_4_RANGE]            dq_dq_tx_io_m1_cfg_4;
   logic [`DDR_CA_DQ_TX_IO_M1_CFG_5_RANGE]            dq_dq_tx_io_m1_cfg_5;
   logic [`DDR_CA_DQ_TX_IO_M1_CFG_6_RANGE]            dq_dq_tx_io_m1_cfg_6;
   logic [`DDR_CA_DQ_TX_IO_M1_CFG_7_RANGE]            dq_dq_tx_io_m1_cfg_7;
   logic [`DDR_CA_DQ_TX_IO_M1_CFG_8_RANGE]            dq_dq_tx_io_m1_cfg_8;
   logic [`DDR_CA_DQ_TX_IO_M1_CFG_9_RANGE]            dq_dq_tx_io_m1_cfg_9;
   logic [`DDR_CA_DQ_TX_IO_M1_CFG_10_RANGE]            dq_dq_tx_io_m1_cfg_10;
   logic [(MAX_MXWIDTH)*DQS_WIDTH-1:0]                             dqs_sdr_0_x_sel;
   logic [(MAX_MXWIDTH)*DQS_WIDTH-1:0]                             dqs_sdr_1_x_sel;
   logic [(MAX_MXWIDTH)*DQS_WIDTH-1:0]                             dqs_sdr_2_x_sel;
   logic [(MAX_MXWIDTH)*DQS_WIDTH-1:0]                             dqs_sdr_3_x_sel;
   logic [(MAX_MXWIDTH-1)*DQS_WIDTH-1:0]                           dqs_ddr_0_x_sel;
   logic [(MAX_MXWIDTH-1)*DQS_WIDTH-1:0]                           dqs_ddr_1_x_sel;
   logic [(MAX_MXWIDTH-2)*DQS_WIDTH-1:0]                           dqs_qdr_0_x_sel;

   // ---------------------------------------------------------
   // DQS RX
   // ---------------------------------------------------------

   logic [`DDR_CA_DQS_RX_M0_CFG_RANGE]                dq_dqs_rx_m0_cfg;
   logic [`DDR_CA_DQS_RX_M1_CFG_RANGE]                dq_dqs_rx_m1_cfg;
   logic [`DDR_CA_DQS_RX_BSCAN_STA_RANGE]             dq_dqs_rx_bscan_sta;
   logic [`DDR_CA_DQS_RX_SDR_LPDE_M0_R0_CFG_RANGE]    dq_dqs_rx_sdr_lpde_m0_r0_cfg;
   logic [`DDR_CA_DQS_RX_SDR_LPDE_M0_R1_CFG_RANGE]    dq_dqs_rx_sdr_lpde_m0_r1_cfg;
   logic [`DDR_CA_DQS_RX_SDR_LPDE_M1_R0_CFG_RANGE]    dq_dqs_rx_sdr_lpde_m1_r0_cfg;
   logic [`DDR_CA_DQS_RX_SDR_LPDE_M1_R1_CFG_RANGE]    dq_dqs_rx_sdr_lpde_m1_r1_cfg;
   logic [`DDR_CA_DQS_RX_REN_PI_M0_R0_CFG_RANGE]      dq_dqs_rx_ren_pi_m0_r0_cfg;
   logic [`DDR_CA_DQS_RX_REN_PI_M0_R1_CFG_RANGE]      dq_dqs_rx_ren_pi_m0_r1_cfg;
   logic [`DDR_CA_DQS_RX_REN_PI_M1_R0_CFG_RANGE]      dq_dqs_rx_ren_pi_m1_r0_cfg;
   logic [`DDR_CA_DQS_RX_REN_PI_M1_R1_CFG_RANGE]      dq_dqs_rx_ren_pi_m1_r1_cfg;
   logic [`DDR_CA_DQS_RX_RCS_PI_M0_R0_CFG_RANGE]      dq_dqs_rx_rcs_pi_m0_r0_cfg;
   logic [`DDR_CA_DQS_RX_RCS_PI_M0_R1_CFG_RANGE]      dq_dqs_rx_rcs_pi_m0_r1_cfg;
   logic [`DDR_CA_DQS_RX_RCS_PI_M1_R0_CFG_RANGE]      dq_dqs_rx_rcs_pi_m1_r0_cfg;
   logic [`DDR_CA_DQS_RX_RCS_PI_M1_R1_CFG_RANGE]      dq_dqs_rx_rcs_pi_m1_r1_cfg;
   logic [`DDR_CA_DQS_RX_RDQS_PI_0_M0_R0_CFG_RANGE]   dq_dqs_rx_rdqs_pi_0_m0_r0_cfg;
   logic [`DDR_CA_DQS_RX_RDQS_PI_0_M0_R1_CFG_RANGE]   dq_dqs_rx_rdqs_pi_0_m0_r1_cfg;
   logic [`DDR_CA_DQS_RX_RDQS_PI_0_M1_R0_CFG_RANGE]   dq_dqs_rx_rdqs_pi_0_m1_r0_cfg;
   logic [`DDR_CA_DQS_RX_RDQS_PI_0_M1_R1_CFG_RANGE]   dq_dqs_rx_rdqs_pi_0_m1_r1_cfg;
   logic [`DDR_CA_DQS_RX_RDQS_PI_1_M0_R0_CFG_RANGE]   dq_dqs_rx_rdqs_pi_1_m0_r0_cfg;
   logic [`DDR_CA_DQS_RX_RDQS_PI_1_M0_R1_CFG_RANGE]   dq_dqs_rx_rdqs_pi_1_m0_r1_cfg;
   logic [`DDR_CA_DQS_RX_RDQS_PI_1_M1_R0_CFG_RANGE]   dq_dqs_rx_rdqs_pi_1_m1_r0_cfg;
   logic [`DDR_CA_DQS_RX_RDQS_PI_1_M1_R1_CFG_RANGE]   dq_dqs_rx_rdqs_pi_1_m1_r1_cfg;
   logic [`DDR_CA_DQS_RX_IO_M0_R0_CFG_0_RANGE]        dq_dqs_rx_io_m0_r0_cfg_0;
   logic [`DDR_CA_DQS_RX_IO_M0_R1_CFG_0_RANGE]        dq_dqs_rx_io_m0_r1_cfg_0;
   logic [`DDR_CA_DQS_RX_IO_M1_R0_CFG_0_RANGE]        dq_dqs_rx_io_m1_r0_cfg_0;
   logic [`DDR_CA_DQS_RX_IO_M1_R1_CFG_0_RANGE]        dq_dqs_rx_io_m1_r1_cfg_0;
   logic [`DDR_CA_DQS_RX_IO_CMN_M0_R0_CFG_RANGE]      dq_dqs_rx_io_cmn_m0_r0_cfg;
   logic [`DDR_CA_DQS_RX_IO_CMN_M0_R1_CFG_RANGE]      dq_dqs_rx_io_cmn_m0_r1_cfg;
   logic [`DDR_CA_DQS_RX_IO_CMN_M1_R0_CFG_RANGE]      dq_dqs_rx_io_cmn_m1_r0_cfg;
   logic [`DDR_CA_DQS_RX_IO_CMN_M1_R1_CFG_RANGE]      dq_dqs_rx_io_cmn_m1_r1_cfg;
   logic [`DDR_CA_DQS_RX_SA_M0_R0_CFG_0_RANGE]        dq_dqs_rx_sa_m0_r0_cfg_0;
   logic [`DDR_CA_DQS_RX_SA_M0_R1_CFG_0_RANGE]        dq_dqs_rx_sa_m0_r1_cfg_0;
   logic [`DDR_CA_DQS_RX_SA_M1_R0_CFG_0_RANGE]        dq_dqs_rx_sa_m1_r0_cfg_0;
   logic [`DDR_CA_DQS_RX_SA_M1_R1_CFG_0_RANGE]        dq_dqs_rx_sa_m1_r1_cfg_0;
   //logic [`DDR_CA_DQS_RX_SA_CMN_R0_CFG_RANGE]         dq_dqs_rx_sa_cmn_r0_cfg;
   //logic [`DDR_CA_DQS_RX_SA_CMN_R1_CFG_RANGE]         dq_dqs_rx_sa_cmn_r1_cfg;
   logic [`DDR_CA_DQS_RX_SA_CMN_CFG_RANGE]            dq_dqs_rx_sa_cmn_cfg;
`ifdef DDR_DQS_VREF
   logic [`DDR_CA_DQS_RX_REFGEN_M0_R0_CFG_RANGE]      dq_dqs_rx_refgen_m0_r0_cfg;
   logic [`DDR_CA_DQS_RX_REFGEN_M0_R1_CFG_RANGE]      dq_dqs_rx_refgen_m0_r1_cfg;
   logic [`DDR_CA_DQS_RX_REFGEN_M1_R0_CFG_RANGE]      dq_dqs_rx_refgen_m1_r0_cfg;
   logic [`DDR_CA_DQS_RX_REFGEN_M1_R1_CFG_RANGE]      dq_dqs_rx_refgen_m1_r1_cfg;
`endif
   logic [`DDR_CA_DQS_RX_IO_STA_RANGE]                dq_dqs_rx_io_sta;
   logic [`DDR_CA_DQS_RX_PI_STA_RANGE]                dq_dqs_rx_pi_sta;

   // ---------------------------------------------------------
   // DQS TX
   // ---------------------------------------------------------

   logic [`DDR_CA_DQS_TX_M0_CFG_RANGE]                dq_dqs_tx_m0_cfg;
   logic [`DDR_CA_DQS_TX_M1_CFG_RANGE]                dq_dqs_tx_m1_cfg;
   logic [`DDR_CA_DQS_TX_BSCAN_CTRL_CFG_RANGE]        dq_dqs_tx_bscan_ctrl_cfg;
   logic [`DDR_CA_DQS_TX_BSCAN_CFG_RANGE]             dq_dqs_tx_bscan_cfg;
   logic [`DDR_CA_DQS_TX_EGRESS_ANA_M0_CFG_0_RANGE]   dq_dqs_tx_egress_ana_m0_cfg_0;
   logic [`DDR_CA_DQS_TX_EGRESS_ANA_M1_CFG_0_RANGE]   dq_dqs_tx_egress_ana_m1_cfg_0;
   logic [`DDR_CA_DQS_TX_EGRESS_DIG_M0_CFG_0_RANGE]   dq_dqs_tx_egress_dig_m0_cfg_0;
   logic [`DDR_CA_DQS_TX_EGRESS_DIG_M1_CFG_0_RANGE]   dq_dqs_tx_egress_dig_m1_cfg_0;
   logic [`DDR_CA_DQS_TX_ODR_PI_M0_R0_CFG_RANGE]      dq_dqs_tx_odr_pi_m0_r0_cfg;
   logic [`DDR_CA_DQS_TX_ODR_PI_M0_R1_CFG_RANGE]      dq_dqs_tx_odr_pi_m0_r1_cfg;
   logic [`DDR_CA_DQS_TX_ODR_PI_M1_R0_CFG_RANGE]      dq_dqs_tx_odr_pi_m1_r0_cfg;
   logic [`DDR_CA_DQS_TX_ODR_PI_M1_R1_CFG_RANGE]      dq_dqs_tx_odr_pi_m1_r1_cfg;
   logic [`DDR_CA_DQS_TX_QDR_PI_0_M0_R0_CFG_RANGE]    dq_dqs_tx_qdr_pi_0_m0_r0_cfg;
   logic [`DDR_CA_DQS_TX_QDR_PI_1_M0_R0_CFG_RANGE]    dq_dqs_tx_qdr_pi_1_m0_r0_cfg;
   logic [`DDR_CA_DQS_TX_QDR_PI_0_M1_R0_CFG_RANGE]    dq_dqs_tx_qdr_pi_0_m1_r0_cfg;
   logic [`DDR_CA_DQS_TX_QDR_PI_1_M1_R0_CFG_RANGE]    dq_dqs_tx_qdr_pi_1_m1_r0_cfg;
   logic [`DDR_CA_DQS_TX_QDR_PI_0_M0_R1_CFG_RANGE]    dq_dqs_tx_qdr_pi_0_m0_r1_cfg;
   logic [`DDR_CA_DQS_TX_QDR_PI_1_M0_R1_CFG_RANGE]    dq_dqs_tx_qdr_pi_1_m0_r1_cfg;
   logic [`DDR_CA_DQS_TX_QDR_PI_0_M1_R1_CFG_RANGE]    dq_dqs_tx_qdr_pi_0_m1_r1_cfg;
   logic [`DDR_CA_DQS_TX_QDR_PI_1_M1_R1_CFG_RANGE]    dq_dqs_tx_qdr_pi_1_m1_r1_cfg;
   logic [`DDR_CA_DQS_TX_DDR_PI_0_M0_R0_CFG_RANGE]    dq_dqs_tx_ddr_pi_0_m0_r0_cfg;
   logic [`DDR_CA_DQS_TX_DDR_PI_0_M0_R1_CFG_RANGE]    dq_dqs_tx_ddr_pi_0_m0_r1_cfg;
   logic [`DDR_CA_DQS_TX_DDR_PI_1_M1_R0_CFG_RANGE]    dq_dqs_tx_ddr_pi_0_m1_r0_cfg;
   logic [`DDR_CA_DQS_TX_DDR_PI_1_M1_R1_CFG_RANGE]    dq_dqs_tx_ddr_pi_0_m1_r1_cfg;
   logic [`DDR_CA_DQS_TX_DDR_PI_1_M0_R0_CFG_RANGE]    dq_dqs_tx_ddr_pi_1_m0_r0_cfg;
   logic [`DDR_CA_DQS_TX_DDR_PI_1_M0_R1_CFG_RANGE]    dq_dqs_tx_ddr_pi_1_m0_r1_cfg;
   logic [`DDR_CA_DQS_TX_DDR_PI_1_M1_R0_CFG_RANGE]    dq_dqs_tx_ddr_pi_1_m1_r0_cfg;
   logic [`DDR_CA_DQS_TX_DDR_PI_1_M1_R1_CFG_RANGE]    dq_dqs_tx_ddr_pi_1_m1_r1_cfg;
   logic [`DDR_CA_DQS_TX_PI_RT_M0_R0_CFG_RANGE]       dq_dqs_tx_pi_rt_m0_r0_cfg;
   logic [`DDR_CA_DQS_TX_PI_RT_M0_R1_CFG_RANGE]       dq_dqs_tx_pi_rt_m0_r1_cfg;
   logic [`DDR_CA_DQS_TX_PI_RT_M1_R0_CFG_RANGE]       dq_dqs_tx_pi_rt_m1_r0_cfg;
   logic [`DDR_CA_DQS_TX_PI_RT_M1_R1_CFG_RANGE]       dq_dqs_tx_pi_rt_m1_r1_cfg;
   logic [`DDR_CA_DQS_TX_SDR_PI_M0_R0_CFG_RANGE]      dq_dqs_tx_sdr_pi_m0_r0_cfg;
   logic [`DDR_CA_DQS_TX_SDR_PI_M0_R1_CFG_RANGE]      dq_dqs_tx_sdr_pi_m0_r1_cfg;
   logic [`DDR_CA_DQS_TX_SDR_PI_M1_R0_CFG_RANGE]      dq_dqs_tx_sdr_pi_m1_r0_cfg;
   logic [`DDR_CA_DQS_TX_SDR_PI_M1_R1_CFG_RANGE]      dq_dqs_tx_sdr_pi_m1_r1_cfg;
   logic [`DDR_CA_DQS_TX_DFI_PI_M0_R0_CFG_RANGE]      dq_dqs_tx_dfi_pi_m0_r0_cfg;
   logic [`DDR_CA_DQS_TX_DFI_PI_M0_R1_CFG_RANGE]      dq_dqs_tx_dfi_pi_m0_r1_cfg;
   logic [`DDR_CA_DQS_TX_DFI_PI_M1_R0_CFG_RANGE]      dq_dqs_tx_dfi_pi_m1_r0_cfg;
   logic [`DDR_CA_DQS_TX_DFI_PI_M1_R1_CFG_RANGE]      dq_dqs_tx_dfi_pi_m1_r1_cfg;
   logic [`DDR_CA_DQS_TX_RT_M0_R0_CFG_RANGE]          dq_dqs_tx_rt_m0_r0_cfg;
   logic [`DDR_CA_DQS_TX_RT_M0_R1_CFG_RANGE]          dq_dqs_tx_rt_m0_r1_cfg;
   logic [`DDR_CA_DQS_TX_RT_M1_R0_CFG_RANGE]          dq_dqs_tx_rt_m1_r0_cfg;
   logic [`DDR_CA_DQS_TX_RT_M1_R1_CFG_RANGE]          dq_dqs_tx_rt_m1_r1_cfg;
   logic [`DDR_CA_DQS_TX_SDR_M0_R0_CFG_0_RANGE]       dq_dqs_tx_sdr_m0_r0_cfg_0;
   logic [`DDR_CA_DQS_TX_SDR_M0_R1_CFG_0_RANGE]       dq_dqs_tx_sdr_m0_r1_cfg_0;
   logic [`DDR_CA_DQS_TX_SDR_M1_R0_CFG_0_RANGE]       dq_dqs_tx_sdr_m1_r0_cfg_0;
   logic [`DDR_CA_DQS_TX_SDR_M1_R1_CFG_0_RANGE]       dq_dqs_tx_sdr_m1_r1_cfg_0;
   logic [`DDR_CA_DQS_TX_SDR_X_SEL_M0_R0_CFG_0_RANGE] dq_dqs_tx_sdr_x_sel_m0_r0_cfg_0;
   logic [`DDR_CA_DQS_TX_SDR_X_SEL_M0_R1_CFG_0_RANGE] dq_dqs_tx_sdr_x_sel_m0_r1_cfg_0;
   logic [`DDR_CA_DQS_TX_SDR_X_SEL_M1_R0_CFG_0_RANGE] dq_dqs_tx_sdr_x_sel_m1_r0_cfg_0;
   logic [`DDR_CA_DQS_TX_SDR_X_SEL_M1_R1_CFG_0_RANGE] dq_dqs_tx_sdr_x_sel_m1_r1_cfg_0;
   logic [`DDR_CA_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0_RANGE]dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_0;
   logic [`DDR_CA_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0_RANGE]dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_0;
   logic [`DDR_CA_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0_RANGE]dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_0;
   logic [`DDR_CA_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0_RANGE]dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_0;
   logic [`DDR_CA_DQS_TX_DDR_M0_R0_CFG_0_RANGE]       dq_dqs_tx_ddr_m0_r0_cfg_0;
   logic [`DDR_CA_DQS_TX_DDR_M0_R1_CFG_0_RANGE]       dq_dqs_tx_ddr_m0_r1_cfg_0;
   logic [`DDR_CA_DQS_TX_DDR_M1_R0_CFG_0_RANGE]       dq_dqs_tx_ddr_m1_r0_cfg_0;
   logic [`DDR_CA_DQS_TX_DDR_M1_R1_CFG_0_RANGE]       dq_dqs_tx_ddr_m1_r1_cfg_0;
   logic [`DDR_CA_DQS_TX_DDR_X_SEL_M0_R0_CFG_0_RANGE] dq_dqs_tx_ddr_x_sel_m0_r0_cfg_0;
   logic [`DDR_CA_DQS_TX_DDR_X_SEL_M0_R1_CFG_0_RANGE] dq_dqs_tx_ddr_x_sel_m0_r1_cfg_0;
   logic [`DDR_CA_DQS_TX_DDR_X_SEL_M1_R0_CFG_0_RANGE] dq_dqs_tx_ddr_x_sel_m1_r0_cfg_0;
   logic [`DDR_CA_DQS_TX_DDR_X_SEL_M1_R1_CFG_0_RANGE] dq_dqs_tx_ddr_x_sel_m1_r1_cfg_0;
   logic [`DDR_CA_DQS_TX_QDR_M0_R0_CFG_0_RANGE]       dq_dqs_tx_qdr_m0_r0_cfg_0;
   logic [`DDR_CA_DQS_TX_QDR_M0_R1_CFG_0_RANGE]       dq_dqs_tx_qdr_m0_r1_cfg_0;
   logic [`DDR_CA_DQS_TX_QDR_M1_R0_CFG_0_RANGE]       dq_dqs_tx_qdr_m1_r0_cfg_0;
   logic [`DDR_CA_DQS_TX_QDR_M1_R1_CFG_0_RANGE]       dq_dqs_tx_qdr_m1_r1_cfg_0;
   logic [`DDR_CA_DQS_TX_QDR_X_SEL_M0_R0_CFG_0_RANGE] dq_dqs_tx_qdr_x_sel_m0_r0_cfg_0;
   logic [`DDR_CA_DQS_TX_QDR_X_SEL_M0_R1_CFG_0_RANGE] dq_dqs_tx_qdr_x_sel_m0_r1_cfg_0;
   logic [`DDR_CA_DQS_TX_QDR_X_SEL_M0_R0_CFG_0_RANGE] dq_dqs_tx_qdr_x_sel_m1_r0_cfg_0;
   logic [`DDR_CA_DQS_TX_QDR_X_SEL_M0_R1_CFG_0_RANGE] dq_dqs_tx_qdr_x_sel_m1_r1_cfg_0;
   logic [`DDR_CA_DQS_TX_LPDE_M0_R0_CFG_0_RANGE]      dq_dqs_tx_lpde_m0_r0_cfg_0;
   logic [`DDR_CA_DQS_TX_LPDE_M0_R1_CFG_0_RANGE]      dq_dqs_tx_lpde_m0_r1_cfg_0;
   logic [`DDR_CA_DQS_TX_LPDE_M1_R0_CFG_0_RANGE]      dq_dqs_tx_lpde_m1_r0_cfg_0;
   logic [`DDR_CA_DQS_TX_LPDE_M1_R1_CFG_0_RANGE]      dq_dqs_tx_lpde_m1_r1_cfg_0;
//`for (i=0; i<`DDR_NUM_TXRX_CK_SLICES; i++)
//   logic [`DDR_CA_DQS_TX_IO_M0_R0_CFG_`i::_RANGE]        dq_dqs_tx_io_m0_r0_cfg_`i;
//`endfor
//`for (i=0; i<`DDR_NUM_TXRX_CK_SLICES; i++)
//   logic [`DDR_CA_DQS_TX_IO_M0_R1_CFG_`i::_RANGE]        dq_dqs_tx_io_m0_r1_cfg_`i;
//`endfor
//`for (i=0; i<`DDR_NUM_TXRX_CK_SLICES; i++)
//   logic [`DDR_CA_DQS_TX_IO_M1_R0_CFG_`i::_RANGE]        dq_dqs_tx_io_m1_r0_cfg_`i;
//`endfor
//`for (i=0; i<`DDR_NUM_TXRX_CK_SLICES; i++)
//   logic [`DDR_CA_DQS_TX_IO_M1_R1_CFG_`i::_RANGE]        dq_dqs_tx_io_m1_r1_cfg_`i;
//`endfor
   logic [`DDR_CA_DQS_TX_IO_M0_CFG_0_RANGE]           dq_dqs_tx_io_m0_cfg_0;
   logic [`DDR_CA_DQS_TX_IO_M1_CFG_0_RANGE]           dq_dqs_tx_io_m1_cfg_0;
   logic [`DDR_CA_DQS_TX_IO_CMN_M0_R0_CFG_RANGE]      dq_dqs_tx_io_cmn_m0_r0_cfg;
   logic [`DDR_CA_DQS_TX_IO_CMN_M0_R1_CFG_RANGE]      dq_dqs_tx_io_cmn_m0_r1_cfg;
   logic [`DDR_CA_DQS_TX_IO_CMN_M1_R0_CFG_RANGE]      dq_dqs_tx_io_cmn_m1_r0_cfg;
   logic [`DDR_CA_DQS_TX_IO_CMN_M1_R1_CFG_RANGE]      dq_dqs_tx_io_cmn_m1_r1_cfg;

   ddr_ca_ahb_csr #(
      .AWIDTH                          (AHB_AWIDTH),
      .DWIDTH                          (32)
   ) u_ca_ahb_csr (

      // ---------------------------------------------------------
      // AHB
      // ---------------------------------------------------------

      .i_hclk                          (i_hclk),
      .i_hreset                        (i_hreset),
      .i_haddr                         (i_haddr),
      .i_hwrite                        (i_hwrite),
      .i_hsel                          (i_hsel),
      .i_hwdata                        (i_hwdata),
      .i_htrans                        (i_htrans),
      .i_hsize                         (i_hsize),
      .i_hburst                        (i_hburst),
      .i_hreadyin                      (i_hreadyin),
      .o_hready                        (o_hready),
      .o_hrdata                        (o_hrdata),
      .o_hresp                         (o_hresp),

      // ---------------------------------------------------------
      // TOP
      // ---------------------------------------------------------

      .o_ca_top_cfg                    (dq_top_cfg),
      .i_ca_top_sta                    (dq_top_sta),

      // ---------------------------------------------------------
      // DQ RX
      // ---------------------------------------------------------

      .i_ca_dq_rx_bscan_sta            (dq_dq_rx_bscan_sta),
      .o_ca_dq_rx_m0_cfg               (dq_dq_rx_m0_cfg),
      .o_ca_dq_rx_m1_cfg               (dq_dq_rx_m1_cfg),
      .o_ca_dq_rx_io_m0_r0_cfg_0      (dq_dq_rx_io_m0_r0_cfg_0),
      .o_ca_dq_rx_io_m0_r0_cfg_1      (dq_dq_rx_io_m0_r0_cfg_1),
      .o_ca_dq_rx_io_m0_r0_cfg_2      (dq_dq_rx_io_m0_r0_cfg_2),
      .o_ca_dq_rx_io_m0_r0_cfg_3      (dq_dq_rx_io_m0_r0_cfg_3),
      .o_ca_dq_rx_io_m0_r0_cfg_4      (dq_dq_rx_io_m0_r0_cfg_4),
      .o_ca_dq_rx_io_m0_r0_cfg_5      (dq_dq_rx_io_m0_r0_cfg_5),
      .o_ca_dq_rx_io_m0_r0_cfg_6      (dq_dq_rx_io_m0_r0_cfg_6),
      .o_ca_dq_rx_io_m0_r0_cfg_7      (dq_dq_rx_io_m0_r0_cfg_7),
      .o_ca_dq_rx_io_m0_r0_cfg_8      (dq_dq_rx_io_m0_r0_cfg_8),
      .o_ca_dq_rx_io_m0_r0_cfg_9      (dq_dq_rx_io_m0_r0_cfg_9),
      .o_ca_dq_rx_io_m0_r0_cfg_10      (dq_dq_rx_io_m0_r0_cfg_10),
      .o_ca_dq_rx_io_m0_r1_cfg_0      (dq_dq_rx_io_m0_r1_cfg_0),
      .o_ca_dq_rx_io_m0_r1_cfg_1      (dq_dq_rx_io_m0_r1_cfg_1),
      .o_ca_dq_rx_io_m0_r1_cfg_2      (dq_dq_rx_io_m0_r1_cfg_2),
      .o_ca_dq_rx_io_m0_r1_cfg_3      (dq_dq_rx_io_m0_r1_cfg_3),
      .o_ca_dq_rx_io_m0_r1_cfg_4      (dq_dq_rx_io_m0_r1_cfg_4),
      .o_ca_dq_rx_io_m0_r1_cfg_5      (dq_dq_rx_io_m0_r1_cfg_5),
      .o_ca_dq_rx_io_m0_r1_cfg_6      (dq_dq_rx_io_m0_r1_cfg_6),
      .o_ca_dq_rx_io_m0_r1_cfg_7      (dq_dq_rx_io_m0_r1_cfg_7),
      .o_ca_dq_rx_io_m0_r1_cfg_8      (dq_dq_rx_io_m0_r1_cfg_8),
      .o_ca_dq_rx_io_m0_r1_cfg_9      (dq_dq_rx_io_m0_r1_cfg_9),
      .o_ca_dq_rx_io_m0_r1_cfg_10      (dq_dq_rx_io_m0_r1_cfg_10),
      .o_ca_dq_rx_io_m1_r0_cfg_0      (dq_dq_rx_io_m1_r0_cfg_0),
      .o_ca_dq_rx_io_m1_r0_cfg_1      (dq_dq_rx_io_m1_r0_cfg_1),
      .o_ca_dq_rx_io_m1_r0_cfg_2      (dq_dq_rx_io_m1_r0_cfg_2),
      .o_ca_dq_rx_io_m1_r0_cfg_3      (dq_dq_rx_io_m1_r0_cfg_3),
      .o_ca_dq_rx_io_m1_r0_cfg_4      (dq_dq_rx_io_m1_r0_cfg_4),
      .o_ca_dq_rx_io_m1_r0_cfg_5      (dq_dq_rx_io_m1_r0_cfg_5),
      .o_ca_dq_rx_io_m1_r0_cfg_6      (dq_dq_rx_io_m1_r0_cfg_6),
      .o_ca_dq_rx_io_m1_r0_cfg_7      (dq_dq_rx_io_m1_r0_cfg_7),
      .o_ca_dq_rx_io_m1_r0_cfg_8      (dq_dq_rx_io_m1_r0_cfg_8),
      .o_ca_dq_rx_io_m1_r0_cfg_9      (dq_dq_rx_io_m1_r0_cfg_9),
      .o_ca_dq_rx_io_m1_r0_cfg_10      (dq_dq_rx_io_m1_r0_cfg_10),
      .o_ca_dq_rx_io_m1_r1_cfg_0      (dq_dq_rx_io_m1_r1_cfg_0),
      .o_ca_dq_rx_io_m1_r1_cfg_1      (dq_dq_rx_io_m1_r1_cfg_1),
      .o_ca_dq_rx_io_m1_r1_cfg_2      (dq_dq_rx_io_m1_r1_cfg_2),
      .o_ca_dq_rx_io_m1_r1_cfg_3      (dq_dq_rx_io_m1_r1_cfg_3),
      .o_ca_dq_rx_io_m1_r1_cfg_4      (dq_dq_rx_io_m1_r1_cfg_4),
      .o_ca_dq_rx_io_m1_r1_cfg_5      (dq_dq_rx_io_m1_r1_cfg_5),
      .o_ca_dq_rx_io_m1_r1_cfg_6      (dq_dq_rx_io_m1_r1_cfg_6),
      .o_ca_dq_rx_io_m1_r1_cfg_7      (dq_dq_rx_io_m1_r1_cfg_7),
      .o_ca_dq_rx_io_m1_r1_cfg_8      (dq_dq_rx_io_m1_r1_cfg_8),
      .o_ca_dq_rx_io_m1_r1_cfg_9      (dq_dq_rx_io_m1_r1_cfg_9),
      .o_ca_dq_rx_io_m1_r1_cfg_10      (dq_dq_rx_io_m1_r1_cfg_10),
      .o_ca_dq_rx_sa_m0_r0_cfg_0       (dq_dq_rx_sa_m0_r0_cfg_0),
      .o_ca_dq_rx_sa_m0_r0_cfg_1       (dq_dq_rx_sa_m0_r0_cfg_1),
      .o_ca_dq_rx_sa_m0_r0_cfg_2       (dq_dq_rx_sa_m0_r0_cfg_2),
      .o_ca_dq_rx_sa_m0_r0_cfg_3       (dq_dq_rx_sa_m0_r0_cfg_3),
      .o_ca_dq_rx_sa_m0_r0_cfg_4       (dq_dq_rx_sa_m0_r0_cfg_4),
      .o_ca_dq_rx_sa_m0_r0_cfg_5       (dq_dq_rx_sa_m0_r0_cfg_5),
      .o_ca_dq_rx_sa_m0_r0_cfg_6       (dq_dq_rx_sa_m0_r0_cfg_6),
      .o_ca_dq_rx_sa_m0_r0_cfg_7       (dq_dq_rx_sa_m0_r0_cfg_7),
      .o_ca_dq_rx_sa_m0_r0_cfg_8       (dq_dq_rx_sa_m0_r0_cfg_8),
      .o_ca_dq_rx_sa_m0_r0_cfg_9       (dq_dq_rx_sa_m0_r0_cfg_9),
      .o_ca_dq_rx_sa_m0_r0_cfg_10       (dq_dq_rx_sa_m0_r0_cfg_10),
      .o_ca_dq_rx_sa_m0_r1_cfg_0       (dq_dq_rx_sa_m0_r1_cfg_0),
      .o_ca_dq_rx_sa_m0_r1_cfg_1       (dq_dq_rx_sa_m0_r1_cfg_1),
      .o_ca_dq_rx_sa_m0_r1_cfg_2       (dq_dq_rx_sa_m0_r1_cfg_2),
      .o_ca_dq_rx_sa_m0_r1_cfg_3       (dq_dq_rx_sa_m0_r1_cfg_3),
      .o_ca_dq_rx_sa_m0_r1_cfg_4       (dq_dq_rx_sa_m0_r1_cfg_4),
      .o_ca_dq_rx_sa_m0_r1_cfg_5       (dq_dq_rx_sa_m0_r1_cfg_5),
      .o_ca_dq_rx_sa_m0_r1_cfg_6       (dq_dq_rx_sa_m0_r1_cfg_6),
      .o_ca_dq_rx_sa_m0_r1_cfg_7       (dq_dq_rx_sa_m0_r1_cfg_7),
      .o_ca_dq_rx_sa_m0_r1_cfg_8       (dq_dq_rx_sa_m0_r1_cfg_8),
      .o_ca_dq_rx_sa_m0_r1_cfg_9       (dq_dq_rx_sa_m0_r1_cfg_9),
      .o_ca_dq_rx_sa_m0_r1_cfg_10       (dq_dq_rx_sa_m0_r1_cfg_10),
      .o_ca_dq_rx_sa_m1_r0_cfg_0       (dq_dq_rx_sa_m1_r0_cfg_0),
      .o_ca_dq_rx_sa_m1_r0_cfg_1       (dq_dq_rx_sa_m1_r0_cfg_1),
      .o_ca_dq_rx_sa_m1_r0_cfg_2       (dq_dq_rx_sa_m1_r0_cfg_2),
      .o_ca_dq_rx_sa_m1_r0_cfg_3       (dq_dq_rx_sa_m1_r0_cfg_3),
      .o_ca_dq_rx_sa_m1_r0_cfg_4       (dq_dq_rx_sa_m1_r0_cfg_4),
      .o_ca_dq_rx_sa_m1_r0_cfg_5       (dq_dq_rx_sa_m1_r0_cfg_5),
      .o_ca_dq_rx_sa_m1_r0_cfg_6       (dq_dq_rx_sa_m1_r0_cfg_6),
      .o_ca_dq_rx_sa_m1_r0_cfg_7       (dq_dq_rx_sa_m1_r0_cfg_7),
      .o_ca_dq_rx_sa_m1_r0_cfg_8       (dq_dq_rx_sa_m1_r0_cfg_8),
      .o_ca_dq_rx_sa_m1_r0_cfg_9       (dq_dq_rx_sa_m1_r0_cfg_9),
      .o_ca_dq_rx_sa_m1_r0_cfg_10       (dq_dq_rx_sa_m1_r0_cfg_10),
      .o_ca_dq_rx_sa_m1_r1_cfg_0       (dq_dq_rx_sa_m1_r1_cfg_0),
      .o_ca_dq_rx_sa_m1_r1_cfg_1       (dq_dq_rx_sa_m1_r1_cfg_1),
      .o_ca_dq_rx_sa_m1_r1_cfg_2       (dq_dq_rx_sa_m1_r1_cfg_2),
      .o_ca_dq_rx_sa_m1_r1_cfg_3       (dq_dq_rx_sa_m1_r1_cfg_3),
      .o_ca_dq_rx_sa_m1_r1_cfg_4       (dq_dq_rx_sa_m1_r1_cfg_4),
      .o_ca_dq_rx_sa_m1_r1_cfg_5       (dq_dq_rx_sa_m1_r1_cfg_5),
      .o_ca_dq_rx_sa_m1_r1_cfg_6       (dq_dq_rx_sa_m1_r1_cfg_6),
      .o_ca_dq_rx_sa_m1_r1_cfg_7       (dq_dq_rx_sa_m1_r1_cfg_7),
      .o_ca_dq_rx_sa_m1_r1_cfg_8       (dq_dq_rx_sa_m1_r1_cfg_8),
      .o_ca_dq_rx_sa_m1_r1_cfg_9       (dq_dq_rx_sa_m1_r1_cfg_9),
      .o_ca_dq_rx_sa_m1_r1_cfg_10       (dq_dq_rx_sa_m1_r1_cfg_10),
      .o_ca_dq_rx_sa_dly_m0_r0_cfg_0   (dq_dq_rx_sa_dly_m0_r0_cfg_0),
      .o_ca_dq_rx_sa_dly_m0_r0_cfg_1   (dq_dq_rx_sa_dly_m0_r0_cfg_1),
      .o_ca_dq_rx_sa_dly_m0_r0_cfg_2   (dq_dq_rx_sa_dly_m0_r0_cfg_2),
      .o_ca_dq_rx_sa_dly_m0_r0_cfg_3   (dq_dq_rx_sa_dly_m0_r0_cfg_3),
      .o_ca_dq_rx_sa_dly_m0_r0_cfg_4   (dq_dq_rx_sa_dly_m0_r0_cfg_4),
      .o_ca_dq_rx_sa_dly_m0_r0_cfg_5   (dq_dq_rx_sa_dly_m0_r0_cfg_5),
      .o_ca_dq_rx_sa_dly_m0_r0_cfg_6   (dq_dq_rx_sa_dly_m0_r0_cfg_6),
      .o_ca_dq_rx_sa_dly_m0_r0_cfg_7   (dq_dq_rx_sa_dly_m0_r0_cfg_7),
      .o_ca_dq_rx_sa_dly_m0_r0_cfg_8   (dq_dq_rx_sa_dly_m0_r0_cfg_8),
      .o_ca_dq_rx_sa_dly_m0_r0_cfg_9   (dq_dq_rx_sa_dly_m0_r0_cfg_9),
      .o_ca_dq_rx_sa_dly_m0_r0_cfg_10   (dq_dq_rx_sa_dly_m0_r0_cfg_10),
      .o_ca_dq_rx_sa_dly_m0_r1_cfg_0   (dq_dq_rx_sa_dly_m0_r1_cfg_0),
      .o_ca_dq_rx_sa_dly_m0_r1_cfg_1   (dq_dq_rx_sa_dly_m0_r1_cfg_1),
      .o_ca_dq_rx_sa_dly_m0_r1_cfg_2   (dq_dq_rx_sa_dly_m0_r1_cfg_2),
      .o_ca_dq_rx_sa_dly_m0_r1_cfg_3   (dq_dq_rx_sa_dly_m0_r1_cfg_3),
      .o_ca_dq_rx_sa_dly_m0_r1_cfg_4   (dq_dq_rx_sa_dly_m0_r1_cfg_4),
      .o_ca_dq_rx_sa_dly_m0_r1_cfg_5   (dq_dq_rx_sa_dly_m0_r1_cfg_5),
      .o_ca_dq_rx_sa_dly_m0_r1_cfg_6   (dq_dq_rx_sa_dly_m0_r1_cfg_6),
      .o_ca_dq_rx_sa_dly_m0_r1_cfg_7   (dq_dq_rx_sa_dly_m0_r1_cfg_7),
      .o_ca_dq_rx_sa_dly_m0_r1_cfg_8   (dq_dq_rx_sa_dly_m0_r1_cfg_8),
      .o_ca_dq_rx_sa_dly_m0_r1_cfg_9   (dq_dq_rx_sa_dly_m0_r1_cfg_9),
      .o_ca_dq_rx_sa_dly_m0_r1_cfg_10   (dq_dq_rx_sa_dly_m0_r1_cfg_10),
      .o_ca_dq_rx_sa_dly_m1_r0_cfg_0   (dq_dq_rx_sa_dly_m1_r0_cfg_0),
      .o_ca_dq_rx_sa_dly_m1_r0_cfg_1   (dq_dq_rx_sa_dly_m1_r0_cfg_1),
      .o_ca_dq_rx_sa_dly_m1_r0_cfg_2   (dq_dq_rx_sa_dly_m1_r0_cfg_2),
      .o_ca_dq_rx_sa_dly_m1_r0_cfg_3   (dq_dq_rx_sa_dly_m1_r0_cfg_3),
      .o_ca_dq_rx_sa_dly_m1_r0_cfg_4   (dq_dq_rx_sa_dly_m1_r0_cfg_4),
      .o_ca_dq_rx_sa_dly_m1_r0_cfg_5   (dq_dq_rx_sa_dly_m1_r0_cfg_5),
      .o_ca_dq_rx_sa_dly_m1_r0_cfg_6   (dq_dq_rx_sa_dly_m1_r0_cfg_6),
      .o_ca_dq_rx_sa_dly_m1_r0_cfg_7   (dq_dq_rx_sa_dly_m1_r0_cfg_7),
      .o_ca_dq_rx_sa_dly_m1_r0_cfg_8   (dq_dq_rx_sa_dly_m1_r0_cfg_8),
      .o_ca_dq_rx_sa_dly_m1_r0_cfg_9   (dq_dq_rx_sa_dly_m1_r0_cfg_9),
      .o_ca_dq_rx_sa_dly_m1_r0_cfg_10   (dq_dq_rx_sa_dly_m1_r0_cfg_10),
      .o_ca_dq_rx_sa_dly_m1_r1_cfg_0   (dq_dq_rx_sa_dly_m1_r1_cfg_0),
      .o_ca_dq_rx_sa_dly_m1_r1_cfg_1   (dq_dq_rx_sa_dly_m1_r1_cfg_1),
      .o_ca_dq_rx_sa_dly_m1_r1_cfg_2   (dq_dq_rx_sa_dly_m1_r1_cfg_2),
      .o_ca_dq_rx_sa_dly_m1_r1_cfg_3   (dq_dq_rx_sa_dly_m1_r1_cfg_3),
      .o_ca_dq_rx_sa_dly_m1_r1_cfg_4   (dq_dq_rx_sa_dly_m1_r1_cfg_4),
      .o_ca_dq_rx_sa_dly_m1_r1_cfg_5   (dq_dq_rx_sa_dly_m1_r1_cfg_5),
      .o_ca_dq_rx_sa_dly_m1_r1_cfg_6   (dq_dq_rx_sa_dly_m1_r1_cfg_6),
      .o_ca_dq_rx_sa_dly_m1_r1_cfg_7   (dq_dq_rx_sa_dly_m1_r1_cfg_7),
      .o_ca_dq_rx_sa_dly_m1_r1_cfg_8   (dq_dq_rx_sa_dly_m1_r1_cfg_8),
      .o_ca_dq_rx_sa_dly_m1_r1_cfg_9   (dq_dq_rx_sa_dly_m1_r1_cfg_9),
      .o_ca_dq_rx_sa_dly_m1_r1_cfg_10   (dq_dq_rx_sa_dly_m1_r1_cfg_10),
      .i_ca_dq_rx_sa_sta_0             (dq_dq_rx_sa_sta_0),
      .i_ca_dq_rx_sa_sta_1             (dq_dq_rx_sa_sta_1),
      .i_ca_dq_rx_sa_sta_2             (dq_dq_rx_sa_sta_2),
      .i_ca_dq_rx_sa_sta_3             (dq_dq_rx_sa_sta_3),
      .i_ca_dq_rx_sa_sta_4             (dq_dq_rx_sa_sta_4),
      .i_ca_dq_rx_sa_sta_5             (dq_dq_rx_sa_sta_5),
      .i_ca_dq_rx_sa_sta_6             (dq_dq_rx_sa_sta_6),
      .i_ca_dq_rx_sa_sta_7             (dq_dq_rx_sa_sta_7),
      .i_ca_dq_rx_sa_sta_8             (dq_dq_rx_sa_sta_8),
      .i_ca_dq_rx_sa_sta_9             (dq_dq_rx_sa_sta_9),
      .i_ca_dq_rx_sa_sta_10             (dq_dq_rx_sa_sta_10),
      .i_ca_dq_rx_io_sta                (dq_dq_rx_io_sta),

      // ---------------------------------------------------------
      // DQ TX
      // ---------------------------------------------------------

      .o_ca_dq_tx_bscan_cfg            (dq_dq_tx_bscan_cfg),
      .o_ca_dq_tx_egress_ana_m0_cfg_0  (dq_dq_tx_egress_ana_m0_cfg_0),
      .o_ca_dq_tx_egress_ana_m0_cfg_1  (dq_dq_tx_egress_ana_m0_cfg_1),
      .o_ca_dq_tx_egress_ana_m0_cfg_2  (dq_dq_tx_egress_ana_m0_cfg_2),
      .o_ca_dq_tx_egress_ana_m0_cfg_3  (dq_dq_tx_egress_ana_m0_cfg_3),
      .o_ca_dq_tx_egress_ana_m0_cfg_4  (dq_dq_tx_egress_ana_m0_cfg_4),
      .o_ca_dq_tx_egress_ana_m0_cfg_5  (dq_dq_tx_egress_ana_m0_cfg_5),
      .o_ca_dq_tx_egress_ana_m0_cfg_6  (dq_dq_tx_egress_ana_m0_cfg_6),
      .o_ca_dq_tx_egress_ana_m0_cfg_7  (dq_dq_tx_egress_ana_m0_cfg_7),
      .o_ca_dq_tx_egress_ana_m0_cfg_8  (dq_dq_tx_egress_ana_m0_cfg_8),
      .o_ca_dq_tx_egress_ana_m0_cfg_9  (dq_dq_tx_egress_ana_m0_cfg_9),
      .o_ca_dq_tx_egress_ana_m0_cfg_10  (dq_dq_tx_egress_ana_m0_cfg_10),
      .o_ca_dq_tx_egress_ana_m1_cfg_0  (dq_dq_tx_egress_ana_m1_cfg_0),
      .o_ca_dq_tx_egress_ana_m1_cfg_1  (dq_dq_tx_egress_ana_m1_cfg_1),
      .o_ca_dq_tx_egress_ana_m1_cfg_2  (dq_dq_tx_egress_ana_m1_cfg_2),
      .o_ca_dq_tx_egress_ana_m1_cfg_3  (dq_dq_tx_egress_ana_m1_cfg_3),
      .o_ca_dq_tx_egress_ana_m1_cfg_4  (dq_dq_tx_egress_ana_m1_cfg_4),
      .o_ca_dq_tx_egress_ana_m1_cfg_5  (dq_dq_tx_egress_ana_m1_cfg_5),
      .o_ca_dq_tx_egress_ana_m1_cfg_6  (dq_dq_tx_egress_ana_m1_cfg_6),
      .o_ca_dq_tx_egress_ana_m1_cfg_7  (dq_dq_tx_egress_ana_m1_cfg_7),
      .o_ca_dq_tx_egress_ana_m1_cfg_8  (dq_dq_tx_egress_ana_m1_cfg_8),
      .o_ca_dq_tx_egress_ana_m1_cfg_9  (dq_dq_tx_egress_ana_m1_cfg_9),
      .o_ca_dq_tx_egress_ana_m1_cfg_10  (dq_dq_tx_egress_ana_m1_cfg_10),
      .o_ca_dq_tx_egress_dig_m0_cfg_0  (dq_dq_tx_egress_dig_m0_cfg_0),
      .o_ca_dq_tx_egress_dig_m0_cfg_1  (dq_dq_tx_egress_dig_m0_cfg_1),
      .o_ca_dq_tx_egress_dig_m0_cfg_2  (dq_dq_tx_egress_dig_m0_cfg_2),
      .o_ca_dq_tx_egress_dig_m0_cfg_3  (dq_dq_tx_egress_dig_m0_cfg_3),
      .o_ca_dq_tx_egress_dig_m0_cfg_4  (dq_dq_tx_egress_dig_m0_cfg_4),
      .o_ca_dq_tx_egress_dig_m0_cfg_5  (dq_dq_tx_egress_dig_m0_cfg_5),
      .o_ca_dq_tx_egress_dig_m0_cfg_6  (dq_dq_tx_egress_dig_m0_cfg_6),
      .o_ca_dq_tx_egress_dig_m0_cfg_7  (dq_dq_tx_egress_dig_m0_cfg_7),
      .o_ca_dq_tx_egress_dig_m0_cfg_8  (dq_dq_tx_egress_dig_m0_cfg_8),
      .o_ca_dq_tx_egress_dig_m0_cfg_9  (dq_dq_tx_egress_dig_m0_cfg_9),
      .o_ca_dq_tx_egress_dig_m0_cfg_10  (dq_dq_tx_egress_dig_m0_cfg_10),
      .o_ca_dq_tx_egress_dig_m1_cfg_0  (dq_dq_tx_egress_dig_m1_cfg_0),
      .o_ca_dq_tx_egress_dig_m1_cfg_1  (dq_dq_tx_egress_dig_m1_cfg_1),
      .o_ca_dq_tx_egress_dig_m1_cfg_2  (dq_dq_tx_egress_dig_m1_cfg_2),
      .o_ca_dq_tx_egress_dig_m1_cfg_3  (dq_dq_tx_egress_dig_m1_cfg_3),
      .o_ca_dq_tx_egress_dig_m1_cfg_4  (dq_dq_tx_egress_dig_m1_cfg_4),
      .o_ca_dq_tx_egress_dig_m1_cfg_5  (dq_dq_tx_egress_dig_m1_cfg_5),
      .o_ca_dq_tx_egress_dig_m1_cfg_6  (dq_dq_tx_egress_dig_m1_cfg_6),
      .o_ca_dq_tx_egress_dig_m1_cfg_7  (dq_dq_tx_egress_dig_m1_cfg_7),
      .o_ca_dq_tx_egress_dig_m1_cfg_8  (dq_dq_tx_egress_dig_m1_cfg_8),
      .o_ca_dq_tx_egress_dig_m1_cfg_9  (dq_dq_tx_egress_dig_m1_cfg_9),
      .o_ca_dq_tx_egress_dig_m1_cfg_10  (dq_dq_tx_egress_dig_m1_cfg_10),
      .o_ca_dq_tx_odr_pi_m0_r0_cfg     (dq_dq_tx_odr_pi_m0_r0_cfg),
      .o_ca_dq_tx_odr_pi_m0_r1_cfg     (dq_dq_tx_odr_pi_m0_r1_cfg),
      .o_ca_dq_tx_odr_pi_m1_r0_cfg     (dq_dq_tx_odr_pi_m1_r0_cfg),
      .o_ca_dq_tx_odr_pi_m1_r1_cfg     (dq_dq_tx_odr_pi_m1_r1_cfg),
      .o_ca_dq_tx_qdr_pi_0_m0_r0_cfg   (dq_dq_tx_qdr_pi_0_m0_r0_cfg),
      .o_ca_dq_tx_qdr_pi_0_m0_r1_cfg   (dq_dq_tx_qdr_pi_0_m0_r1_cfg),
      .o_ca_dq_tx_qdr_pi_0_m1_r0_cfg   (dq_dq_tx_qdr_pi_0_m1_r0_cfg),
      .o_ca_dq_tx_qdr_pi_0_m1_r1_cfg   (dq_dq_tx_qdr_pi_0_m1_r1_cfg),
      .o_ca_dq_tx_qdr_pi_1_m0_r0_cfg   (dq_dq_tx_qdr_pi_1_m0_r0_cfg),
      .o_ca_dq_tx_qdr_pi_1_m0_r1_cfg   (dq_dq_tx_qdr_pi_1_m0_r1_cfg),
      .o_ca_dq_tx_qdr_pi_1_m1_r0_cfg   (dq_dq_tx_qdr_pi_1_m1_r0_cfg),
      .o_ca_dq_tx_qdr_pi_1_m1_r1_cfg   (dq_dq_tx_qdr_pi_1_m1_r1_cfg),
      .o_ca_dq_tx_ddr_pi_0_m0_r0_cfg   (dq_dq_tx_ddr_pi_0_m0_r0_cfg),
      .o_ca_dq_tx_ddr_pi_0_m0_r1_cfg   (dq_dq_tx_ddr_pi_0_m0_r1_cfg),
      .o_ca_dq_tx_ddr_pi_0_m1_r0_cfg   (dq_dq_tx_ddr_pi_0_m1_r0_cfg),
      .o_ca_dq_tx_ddr_pi_0_m1_r1_cfg   (dq_dq_tx_ddr_pi_0_m1_r1_cfg),
      .o_ca_dq_tx_ddr_pi_1_m0_r0_cfg   (dq_dq_tx_ddr_pi_1_m0_r0_cfg),
      .o_ca_dq_tx_ddr_pi_1_m0_r1_cfg   (dq_dq_tx_ddr_pi_1_m0_r1_cfg),
      .o_ca_dq_tx_ddr_pi_1_m1_r0_cfg   (dq_dq_tx_ddr_pi_1_m1_r0_cfg),
      .o_ca_dq_tx_ddr_pi_1_m1_r1_cfg   (dq_dq_tx_ddr_pi_1_m1_r1_cfg),
      .o_ca_dq_tx_pi_rt_m0_r0_cfg      (dq_dq_tx_pi_rt_m0_r0_cfg),
      .o_ca_dq_tx_pi_rt_m0_r1_cfg      (dq_dq_tx_pi_rt_m0_r1_cfg),
      .o_ca_dq_tx_pi_rt_m1_r0_cfg      (dq_dq_tx_pi_rt_m1_r0_cfg),
      .o_ca_dq_tx_pi_rt_m1_r1_cfg      (dq_dq_tx_pi_rt_m1_r1_cfg),
      .o_ca_dq_tx_rt_m0_r0_cfg         (dq_dq_tx_rt_m0_r0_cfg),
      .o_ca_dq_tx_rt_m0_r1_cfg         (dq_dq_tx_rt_m0_r1_cfg),
      .o_ca_dq_tx_rt_m1_r0_cfg         (dq_dq_tx_rt_m1_r0_cfg),
      .o_ca_dq_tx_rt_m1_r1_cfg         (dq_dq_tx_rt_m1_r1_cfg),
      .o_ca_dq_tx_sdr_m0_r0_cfg_0      (dq_dq_tx_sdr_m0_r0_cfg_0),
      .o_ca_dq_tx_sdr_m0_r0_cfg_1      (dq_dq_tx_sdr_m0_r0_cfg_1),
      .o_ca_dq_tx_sdr_m0_r0_cfg_2      (dq_dq_tx_sdr_m0_r0_cfg_2),
      .o_ca_dq_tx_sdr_m0_r0_cfg_3      (dq_dq_tx_sdr_m0_r0_cfg_3),
      .o_ca_dq_tx_sdr_m0_r0_cfg_4      (dq_dq_tx_sdr_m0_r0_cfg_4),
      .o_ca_dq_tx_sdr_m0_r0_cfg_5      (dq_dq_tx_sdr_m0_r0_cfg_5),
      .o_ca_dq_tx_sdr_m0_r0_cfg_6      (dq_dq_tx_sdr_m0_r0_cfg_6),
      .o_ca_dq_tx_sdr_m0_r0_cfg_7      (dq_dq_tx_sdr_m0_r0_cfg_7),
      .o_ca_dq_tx_sdr_m0_r0_cfg_8      (dq_dq_tx_sdr_m0_r0_cfg_8),
      .o_ca_dq_tx_sdr_m0_r0_cfg_9      (dq_dq_tx_sdr_m0_r0_cfg_9),
      .o_ca_dq_tx_sdr_m0_r0_cfg_10      (dq_dq_tx_sdr_m0_r0_cfg_10),
      .o_ca_dq_tx_sdr_m0_r1_cfg_0      (dq_dq_tx_sdr_m0_r1_cfg_0),
      .o_ca_dq_tx_sdr_m0_r1_cfg_1      (dq_dq_tx_sdr_m0_r1_cfg_1),
      .o_ca_dq_tx_sdr_m0_r1_cfg_2      (dq_dq_tx_sdr_m0_r1_cfg_2),
      .o_ca_dq_tx_sdr_m0_r1_cfg_3      (dq_dq_tx_sdr_m0_r1_cfg_3),
      .o_ca_dq_tx_sdr_m0_r1_cfg_4      (dq_dq_tx_sdr_m0_r1_cfg_4),
      .o_ca_dq_tx_sdr_m0_r1_cfg_5      (dq_dq_tx_sdr_m0_r1_cfg_5),
      .o_ca_dq_tx_sdr_m0_r1_cfg_6      (dq_dq_tx_sdr_m0_r1_cfg_6),
      .o_ca_dq_tx_sdr_m0_r1_cfg_7      (dq_dq_tx_sdr_m0_r1_cfg_7),
      .o_ca_dq_tx_sdr_m0_r1_cfg_8      (dq_dq_tx_sdr_m0_r1_cfg_8),
      .o_ca_dq_tx_sdr_m0_r1_cfg_9      (dq_dq_tx_sdr_m0_r1_cfg_9),
      .o_ca_dq_tx_sdr_m0_r1_cfg_10      (dq_dq_tx_sdr_m0_r1_cfg_10),
      .o_ca_dq_tx_sdr_m1_r0_cfg_0      (dq_dq_tx_sdr_m1_r0_cfg_0),
      .o_ca_dq_tx_sdr_m1_r0_cfg_1      (dq_dq_tx_sdr_m1_r0_cfg_1),
      .o_ca_dq_tx_sdr_m1_r0_cfg_2      (dq_dq_tx_sdr_m1_r0_cfg_2),
      .o_ca_dq_tx_sdr_m1_r0_cfg_3      (dq_dq_tx_sdr_m1_r0_cfg_3),
      .o_ca_dq_tx_sdr_m1_r0_cfg_4      (dq_dq_tx_sdr_m1_r0_cfg_4),
      .o_ca_dq_tx_sdr_m1_r0_cfg_5      (dq_dq_tx_sdr_m1_r0_cfg_5),
      .o_ca_dq_tx_sdr_m1_r0_cfg_6      (dq_dq_tx_sdr_m1_r0_cfg_6),
      .o_ca_dq_tx_sdr_m1_r0_cfg_7      (dq_dq_tx_sdr_m1_r0_cfg_7),
      .o_ca_dq_tx_sdr_m1_r0_cfg_8      (dq_dq_tx_sdr_m1_r0_cfg_8),
      .o_ca_dq_tx_sdr_m1_r0_cfg_9      (dq_dq_tx_sdr_m1_r0_cfg_9),
      .o_ca_dq_tx_sdr_m1_r0_cfg_10      (dq_dq_tx_sdr_m1_r0_cfg_10),
      .o_ca_dq_tx_sdr_m1_r1_cfg_0      (dq_dq_tx_sdr_m1_r1_cfg_0),
      .o_ca_dq_tx_sdr_m1_r1_cfg_1      (dq_dq_tx_sdr_m1_r1_cfg_1),
      .o_ca_dq_tx_sdr_m1_r1_cfg_2      (dq_dq_tx_sdr_m1_r1_cfg_2),
      .o_ca_dq_tx_sdr_m1_r1_cfg_3      (dq_dq_tx_sdr_m1_r1_cfg_3),
      .o_ca_dq_tx_sdr_m1_r1_cfg_4      (dq_dq_tx_sdr_m1_r1_cfg_4),
      .o_ca_dq_tx_sdr_m1_r1_cfg_5      (dq_dq_tx_sdr_m1_r1_cfg_5),
      .o_ca_dq_tx_sdr_m1_r1_cfg_6      (dq_dq_tx_sdr_m1_r1_cfg_6),
      .o_ca_dq_tx_sdr_m1_r1_cfg_7      (dq_dq_tx_sdr_m1_r1_cfg_7),
      .o_ca_dq_tx_sdr_m1_r1_cfg_8      (dq_dq_tx_sdr_m1_r1_cfg_8),
      .o_ca_dq_tx_sdr_m1_r1_cfg_9      (dq_dq_tx_sdr_m1_r1_cfg_9),
      .o_ca_dq_tx_sdr_m1_r1_cfg_10      (dq_dq_tx_sdr_m1_r1_cfg_10),
      .o_ca_dq_tx_sdr_x_sel_m0_r0_cfg_0 (dq_dq_tx_sdr_x_sel_m0_r0_cfg_0),
      .o_ca_dq_tx_sdr_x_sel_m0_r0_cfg_1 (dq_dq_tx_sdr_x_sel_m0_r0_cfg_1),
      .o_ca_dq_tx_sdr_x_sel_m0_r0_cfg_2 (dq_dq_tx_sdr_x_sel_m0_r0_cfg_2),
      .o_ca_dq_tx_sdr_x_sel_m0_r0_cfg_3 (dq_dq_tx_sdr_x_sel_m0_r0_cfg_3),
      .o_ca_dq_tx_sdr_x_sel_m0_r0_cfg_4 (dq_dq_tx_sdr_x_sel_m0_r0_cfg_4),
      .o_ca_dq_tx_sdr_x_sel_m0_r0_cfg_5 (dq_dq_tx_sdr_x_sel_m0_r0_cfg_5),
      .o_ca_dq_tx_sdr_x_sel_m0_r0_cfg_6 (dq_dq_tx_sdr_x_sel_m0_r0_cfg_6),
      .o_ca_dq_tx_sdr_x_sel_m0_r0_cfg_7 (dq_dq_tx_sdr_x_sel_m0_r0_cfg_7),
      .o_ca_dq_tx_sdr_x_sel_m0_r0_cfg_8 (dq_dq_tx_sdr_x_sel_m0_r0_cfg_8),
      .o_ca_dq_tx_sdr_x_sel_m0_r0_cfg_9 (dq_dq_tx_sdr_x_sel_m0_r0_cfg_9),
      .o_ca_dq_tx_sdr_x_sel_m0_r0_cfg_10 (dq_dq_tx_sdr_x_sel_m0_r0_cfg_10),
      .o_ca_dq_tx_sdr_x_sel_m0_r1_cfg_0 (dq_dq_tx_sdr_x_sel_m0_r1_cfg_0),
      .o_ca_dq_tx_sdr_x_sel_m0_r1_cfg_1 (dq_dq_tx_sdr_x_sel_m0_r1_cfg_1),
      .o_ca_dq_tx_sdr_x_sel_m0_r1_cfg_2 (dq_dq_tx_sdr_x_sel_m0_r1_cfg_2),
      .o_ca_dq_tx_sdr_x_sel_m0_r1_cfg_3 (dq_dq_tx_sdr_x_sel_m0_r1_cfg_3),
      .o_ca_dq_tx_sdr_x_sel_m0_r1_cfg_4 (dq_dq_tx_sdr_x_sel_m0_r1_cfg_4),
      .o_ca_dq_tx_sdr_x_sel_m0_r1_cfg_5 (dq_dq_tx_sdr_x_sel_m0_r1_cfg_5),
      .o_ca_dq_tx_sdr_x_sel_m0_r1_cfg_6 (dq_dq_tx_sdr_x_sel_m0_r1_cfg_6),
      .o_ca_dq_tx_sdr_x_sel_m0_r1_cfg_7 (dq_dq_tx_sdr_x_sel_m0_r1_cfg_7),
      .o_ca_dq_tx_sdr_x_sel_m0_r1_cfg_8 (dq_dq_tx_sdr_x_sel_m0_r1_cfg_8),
      .o_ca_dq_tx_sdr_x_sel_m0_r1_cfg_9 (dq_dq_tx_sdr_x_sel_m0_r1_cfg_9),
      .o_ca_dq_tx_sdr_x_sel_m0_r1_cfg_10 (dq_dq_tx_sdr_x_sel_m0_r1_cfg_10),
      .o_ca_dq_tx_sdr_x_sel_m1_r0_cfg_0 (dq_dq_tx_sdr_x_sel_m1_r0_cfg_0),
      .o_ca_dq_tx_sdr_x_sel_m1_r0_cfg_1 (dq_dq_tx_sdr_x_sel_m1_r0_cfg_1),
      .o_ca_dq_tx_sdr_x_sel_m1_r0_cfg_2 (dq_dq_tx_sdr_x_sel_m1_r0_cfg_2),
      .o_ca_dq_tx_sdr_x_sel_m1_r0_cfg_3 (dq_dq_tx_sdr_x_sel_m1_r0_cfg_3),
      .o_ca_dq_tx_sdr_x_sel_m1_r0_cfg_4 (dq_dq_tx_sdr_x_sel_m1_r0_cfg_4),
      .o_ca_dq_tx_sdr_x_sel_m1_r0_cfg_5 (dq_dq_tx_sdr_x_sel_m1_r0_cfg_5),
      .o_ca_dq_tx_sdr_x_sel_m1_r0_cfg_6 (dq_dq_tx_sdr_x_sel_m1_r0_cfg_6),
      .o_ca_dq_tx_sdr_x_sel_m1_r0_cfg_7 (dq_dq_tx_sdr_x_sel_m1_r0_cfg_7),
      .o_ca_dq_tx_sdr_x_sel_m1_r0_cfg_8 (dq_dq_tx_sdr_x_sel_m1_r0_cfg_8),
      .o_ca_dq_tx_sdr_x_sel_m1_r0_cfg_9 (dq_dq_tx_sdr_x_sel_m1_r0_cfg_9),
      .o_ca_dq_tx_sdr_x_sel_m1_r0_cfg_10 (dq_dq_tx_sdr_x_sel_m1_r0_cfg_10),
      .o_ca_dq_tx_sdr_x_sel_m1_r1_cfg_0 (dq_dq_tx_sdr_x_sel_m1_r1_cfg_0),
      .o_ca_dq_tx_sdr_x_sel_m1_r1_cfg_1 (dq_dq_tx_sdr_x_sel_m1_r1_cfg_1),
      .o_ca_dq_tx_sdr_x_sel_m1_r1_cfg_2 (dq_dq_tx_sdr_x_sel_m1_r1_cfg_2),
      .o_ca_dq_tx_sdr_x_sel_m1_r1_cfg_3 (dq_dq_tx_sdr_x_sel_m1_r1_cfg_3),
      .o_ca_dq_tx_sdr_x_sel_m1_r1_cfg_4 (dq_dq_tx_sdr_x_sel_m1_r1_cfg_4),
      .o_ca_dq_tx_sdr_x_sel_m1_r1_cfg_5 (dq_dq_tx_sdr_x_sel_m1_r1_cfg_5),
      .o_ca_dq_tx_sdr_x_sel_m1_r1_cfg_6 (dq_dq_tx_sdr_x_sel_m1_r1_cfg_6),
      .o_ca_dq_tx_sdr_x_sel_m1_r1_cfg_7 (dq_dq_tx_sdr_x_sel_m1_r1_cfg_7),
      .o_ca_dq_tx_sdr_x_sel_m1_r1_cfg_8 (dq_dq_tx_sdr_x_sel_m1_r1_cfg_8),
      .o_ca_dq_tx_sdr_x_sel_m1_r1_cfg_9 (dq_dq_tx_sdr_x_sel_m1_r1_cfg_9),
      .o_ca_dq_tx_sdr_x_sel_m1_r1_cfg_10 (dq_dq_tx_sdr_x_sel_m1_r1_cfg_10),
      .o_ca_dq_tx_sdr_fc_dly_m0_r0_cfg_0 (dq_dq_tx_sdr_fc_dly_m0_r0_cfg_0),
      .o_ca_dq_tx_sdr_fc_dly_m0_r0_cfg_1 (dq_dq_tx_sdr_fc_dly_m0_r0_cfg_1),
      .o_ca_dq_tx_sdr_fc_dly_m0_r0_cfg_2 (dq_dq_tx_sdr_fc_dly_m0_r0_cfg_2),
      .o_ca_dq_tx_sdr_fc_dly_m0_r0_cfg_3 (dq_dq_tx_sdr_fc_dly_m0_r0_cfg_3),
      .o_ca_dq_tx_sdr_fc_dly_m0_r0_cfg_4 (dq_dq_tx_sdr_fc_dly_m0_r0_cfg_4),
      .o_ca_dq_tx_sdr_fc_dly_m0_r0_cfg_5 (dq_dq_tx_sdr_fc_dly_m0_r0_cfg_5),
      .o_ca_dq_tx_sdr_fc_dly_m0_r0_cfg_6 (dq_dq_tx_sdr_fc_dly_m0_r0_cfg_6),
      .o_ca_dq_tx_sdr_fc_dly_m0_r0_cfg_7 (dq_dq_tx_sdr_fc_dly_m0_r0_cfg_7),
      .o_ca_dq_tx_sdr_fc_dly_m0_r0_cfg_8 (dq_dq_tx_sdr_fc_dly_m0_r0_cfg_8),
      .o_ca_dq_tx_sdr_fc_dly_m0_r0_cfg_9 (dq_dq_tx_sdr_fc_dly_m0_r0_cfg_9),
      .o_ca_dq_tx_sdr_fc_dly_m0_r0_cfg_10 (dq_dq_tx_sdr_fc_dly_m0_r0_cfg_10),
      .o_ca_dq_tx_sdr_fc_dly_m0_r1_cfg_0 (dq_dq_tx_sdr_fc_dly_m0_r1_cfg_0),
      .o_ca_dq_tx_sdr_fc_dly_m0_r1_cfg_1 (dq_dq_tx_sdr_fc_dly_m0_r1_cfg_1),
      .o_ca_dq_tx_sdr_fc_dly_m0_r1_cfg_2 (dq_dq_tx_sdr_fc_dly_m0_r1_cfg_2),
      .o_ca_dq_tx_sdr_fc_dly_m0_r1_cfg_3 (dq_dq_tx_sdr_fc_dly_m0_r1_cfg_3),
      .o_ca_dq_tx_sdr_fc_dly_m0_r1_cfg_4 (dq_dq_tx_sdr_fc_dly_m0_r1_cfg_4),
      .o_ca_dq_tx_sdr_fc_dly_m0_r1_cfg_5 (dq_dq_tx_sdr_fc_dly_m0_r1_cfg_5),
      .o_ca_dq_tx_sdr_fc_dly_m0_r1_cfg_6 (dq_dq_tx_sdr_fc_dly_m0_r1_cfg_6),
      .o_ca_dq_tx_sdr_fc_dly_m0_r1_cfg_7 (dq_dq_tx_sdr_fc_dly_m0_r1_cfg_7),
      .o_ca_dq_tx_sdr_fc_dly_m0_r1_cfg_8 (dq_dq_tx_sdr_fc_dly_m0_r1_cfg_8),
      .o_ca_dq_tx_sdr_fc_dly_m0_r1_cfg_9 (dq_dq_tx_sdr_fc_dly_m0_r1_cfg_9),
      .o_ca_dq_tx_sdr_fc_dly_m0_r1_cfg_10 (dq_dq_tx_sdr_fc_dly_m0_r1_cfg_10),
      .o_ca_dq_tx_sdr_fc_dly_m1_r0_cfg_0 (dq_dq_tx_sdr_fc_dly_m1_r0_cfg_0),
      .o_ca_dq_tx_sdr_fc_dly_m1_r0_cfg_1 (dq_dq_tx_sdr_fc_dly_m1_r0_cfg_1),
      .o_ca_dq_tx_sdr_fc_dly_m1_r0_cfg_2 (dq_dq_tx_sdr_fc_dly_m1_r0_cfg_2),
      .o_ca_dq_tx_sdr_fc_dly_m1_r0_cfg_3 (dq_dq_tx_sdr_fc_dly_m1_r0_cfg_3),
      .o_ca_dq_tx_sdr_fc_dly_m1_r0_cfg_4 (dq_dq_tx_sdr_fc_dly_m1_r0_cfg_4),
      .o_ca_dq_tx_sdr_fc_dly_m1_r0_cfg_5 (dq_dq_tx_sdr_fc_dly_m1_r0_cfg_5),
      .o_ca_dq_tx_sdr_fc_dly_m1_r0_cfg_6 (dq_dq_tx_sdr_fc_dly_m1_r0_cfg_6),
      .o_ca_dq_tx_sdr_fc_dly_m1_r0_cfg_7 (dq_dq_tx_sdr_fc_dly_m1_r0_cfg_7),
      .o_ca_dq_tx_sdr_fc_dly_m1_r0_cfg_8 (dq_dq_tx_sdr_fc_dly_m1_r0_cfg_8),
      .o_ca_dq_tx_sdr_fc_dly_m1_r0_cfg_9 (dq_dq_tx_sdr_fc_dly_m1_r0_cfg_9),
      .o_ca_dq_tx_sdr_fc_dly_m1_r0_cfg_10 (dq_dq_tx_sdr_fc_dly_m1_r0_cfg_10),
      .o_ca_dq_tx_sdr_fc_dly_m1_r1_cfg_0 (dq_dq_tx_sdr_fc_dly_m1_r1_cfg_0),
      .o_ca_dq_tx_sdr_fc_dly_m1_r1_cfg_1 (dq_dq_tx_sdr_fc_dly_m1_r1_cfg_1),
      .o_ca_dq_tx_sdr_fc_dly_m1_r1_cfg_2 (dq_dq_tx_sdr_fc_dly_m1_r1_cfg_2),
      .o_ca_dq_tx_sdr_fc_dly_m1_r1_cfg_3 (dq_dq_tx_sdr_fc_dly_m1_r1_cfg_3),
      .o_ca_dq_tx_sdr_fc_dly_m1_r1_cfg_4 (dq_dq_tx_sdr_fc_dly_m1_r1_cfg_4),
      .o_ca_dq_tx_sdr_fc_dly_m1_r1_cfg_5 (dq_dq_tx_sdr_fc_dly_m1_r1_cfg_5),
      .o_ca_dq_tx_sdr_fc_dly_m1_r1_cfg_6 (dq_dq_tx_sdr_fc_dly_m1_r1_cfg_6),
      .o_ca_dq_tx_sdr_fc_dly_m1_r1_cfg_7 (dq_dq_tx_sdr_fc_dly_m1_r1_cfg_7),
      .o_ca_dq_tx_sdr_fc_dly_m1_r1_cfg_8 (dq_dq_tx_sdr_fc_dly_m1_r1_cfg_8),
      .o_ca_dq_tx_sdr_fc_dly_m1_r1_cfg_9 (dq_dq_tx_sdr_fc_dly_m1_r1_cfg_9),
      .o_ca_dq_tx_sdr_fc_dly_m1_r1_cfg_10 (dq_dq_tx_sdr_fc_dly_m1_r1_cfg_10),
      .o_ca_dq_tx_ddr_m0_r0_cfg_0      (dq_dq_tx_ddr_m0_r0_cfg_0),
      .o_ca_dq_tx_ddr_m0_r0_cfg_1      (dq_dq_tx_ddr_m0_r0_cfg_1),
      .o_ca_dq_tx_ddr_m0_r0_cfg_2      (dq_dq_tx_ddr_m0_r0_cfg_2),
      .o_ca_dq_tx_ddr_m0_r0_cfg_3      (dq_dq_tx_ddr_m0_r0_cfg_3),
      .o_ca_dq_tx_ddr_m0_r0_cfg_4      (dq_dq_tx_ddr_m0_r0_cfg_4),
      .o_ca_dq_tx_ddr_m0_r0_cfg_5      (dq_dq_tx_ddr_m0_r0_cfg_5),
      .o_ca_dq_tx_ddr_m0_r0_cfg_6      (dq_dq_tx_ddr_m0_r0_cfg_6),
      .o_ca_dq_tx_ddr_m0_r0_cfg_7      (dq_dq_tx_ddr_m0_r0_cfg_7),
      .o_ca_dq_tx_ddr_m0_r0_cfg_8      (dq_dq_tx_ddr_m0_r0_cfg_8),
      .o_ca_dq_tx_ddr_m0_r0_cfg_9      (dq_dq_tx_ddr_m0_r0_cfg_9),
      .o_ca_dq_tx_ddr_m0_r0_cfg_10      (dq_dq_tx_ddr_m0_r0_cfg_10),
      .o_ca_dq_tx_ddr_m0_r1_cfg_0      (dq_dq_tx_ddr_m0_r1_cfg_0),
      .o_ca_dq_tx_ddr_m0_r1_cfg_1      (dq_dq_tx_ddr_m0_r1_cfg_1),
      .o_ca_dq_tx_ddr_m0_r1_cfg_2      (dq_dq_tx_ddr_m0_r1_cfg_2),
      .o_ca_dq_tx_ddr_m0_r1_cfg_3      (dq_dq_tx_ddr_m0_r1_cfg_3),
      .o_ca_dq_tx_ddr_m0_r1_cfg_4      (dq_dq_tx_ddr_m0_r1_cfg_4),
      .o_ca_dq_tx_ddr_m0_r1_cfg_5      (dq_dq_tx_ddr_m0_r1_cfg_5),
      .o_ca_dq_tx_ddr_m0_r1_cfg_6      (dq_dq_tx_ddr_m0_r1_cfg_6),
      .o_ca_dq_tx_ddr_m0_r1_cfg_7      (dq_dq_tx_ddr_m0_r1_cfg_7),
      .o_ca_dq_tx_ddr_m0_r1_cfg_8      (dq_dq_tx_ddr_m0_r1_cfg_8),
      .o_ca_dq_tx_ddr_m0_r1_cfg_9      (dq_dq_tx_ddr_m0_r1_cfg_9),
      .o_ca_dq_tx_ddr_m0_r1_cfg_10      (dq_dq_tx_ddr_m0_r1_cfg_10),
      .o_ca_dq_tx_ddr_m1_r0_cfg_0      (dq_dq_tx_ddr_m1_r0_cfg_0),
      .o_ca_dq_tx_ddr_m1_r0_cfg_1      (dq_dq_tx_ddr_m1_r0_cfg_1),
      .o_ca_dq_tx_ddr_m1_r0_cfg_2      (dq_dq_tx_ddr_m1_r0_cfg_2),
      .o_ca_dq_tx_ddr_m1_r0_cfg_3      (dq_dq_tx_ddr_m1_r0_cfg_3),
      .o_ca_dq_tx_ddr_m1_r0_cfg_4      (dq_dq_tx_ddr_m1_r0_cfg_4),
      .o_ca_dq_tx_ddr_m1_r0_cfg_5      (dq_dq_tx_ddr_m1_r0_cfg_5),
      .o_ca_dq_tx_ddr_m1_r0_cfg_6      (dq_dq_tx_ddr_m1_r0_cfg_6),
      .o_ca_dq_tx_ddr_m1_r0_cfg_7      (dq_dq_tx_ddr_m1_r0_cfg_7),
      .o_ca_dq_tx_ddr_m1_r0_cfg_8      (dq_dq_tx_ddr_m1_r0_cfg_8),
      .o_ca_dq_tx_ddr_m1_r0_cfg_9      (dq_dq_tx_ddr_m1_r0_cfg_9),
      .o_ca_dq_tx_ddr_m1_r0_cfg_10      (dq_dq_tx_ddr_m1_r0_cfg_10),
      .o_ca_dq_tx_ddr_m1_r1_cfg_0      (dq_dq_tx_ddr_m1_r1_cfg_0),
      .o_ca_dq_tx_ddr_m1_r1_cfg_1      (dq_dq_tx_ddr_m1_r1_cfg_1),
      .o_ca_dq_tx_ddr_m1_r1_cfg_2      (dq_dq_tx_ddr_m1_r1_cfg_2),
      .o_ca_dq_tx_ddr_m1_r1_cfg_3      (dq_dq_tx_ddr_m1_r1_cfg_3),
      .o_ca_dq_tx_ddr_m1_r1_cfg_4      (dq_dq_tx_ddr_m1_r1_cfg_4),
      .o_ca_dq_tx_ddr_m1_r1_cfg_5      (dq_dq_tx_ddr_m1_r1_cfg_5),
      .o_ca_dq_tx_ddr_m1_r1_cfg_6      (dq_dq_tx_ddr_m1_r1_cfg_6),
      .o_ca_dq_tx_ddr_m1_r1_cfg_7      (dq_dq_tx_ddr_m1_r1_cfg_7),
      .o_ca_dq_tx_ddr_m1_r1_cfg_8      (dq_dq_tx_ddr_m1_r1_cfg_8),
      .o_ca_dq_tx_ddr_m1_r1_cfg_9      (dq_dq_tx_ddr_m1_r1_cfg_9),
      .o_ca_dq_tx_ddr_m1_r1_cfg_10      (dq_dq_tx_ddr_m1_r1_cfg_10),
      .o_ca_dq_tx_ddr_x_sel_m0_r0_cfg_0 (dq_dq_tx_ddr_x_sel_m0_r0_cfg_0),
      .o_ca_dq_tx_ddr_x_sel_m0_r0_cfg_1 (dq_dq_tx_ddr_x_sel_m0_r0_cfg_1),
      .o_ca_dq_tx_ddr_x_sel_m0_r0_cfg_2 (dq_dq_tx_ddr_x_sel_m0_r0_cfg_2),
      .o_ca_dq_tx_ddr_x_sel_m0_r0_cfg_3 (dq_dq_tx_ddr_x_sel_m0_r0_cfg_3),
      .o_ca_dq_tx_ddr_x_sel_m0_r0_cfg_4 (dq_dq_tx_ddr_x_sel_m0_r0_cfg_4),
      .o_ca_dq_tx_ddr_x_sel_m0_r0_cfg_5 (dq_dq_tx_ddr_x_sel_m0_r0_cfg_5),
      .o_ca_dq_tx_ddr_x_sel_m0_r0_cfg_6 (dq_dq_tx_ddr_x_sel_m0_r0_cfg_6),
      .o_ca_dq_tx_ddr_x_sel_m0_r0_cfg_7 (dq_dq_tx_ddr_x_sel_m0_r0_cfg_7),
      .o_ca_dq_tx_ddr_x_sel_m0_r0_cfg_8 (dq_dq_tx_ddr_x_sel_m0_r0_cfg_8),
      .o_ca_dq_tx_ddr_x_sel_m0_r0_cfg_9 (dq_dq_tx_ddr_x_sel_m0_r0_cfg_9),
      .o_ca_dq_tx_ddr_x_sel_m0_r0_cfg_10 (dq_dq_tx_ddr_x_sel_m0_r0_cfg_10),
      .o_ca_dq_tx_ddr_x_sel_m0_r1_cfg_0 (dq_dq_tx_ddr_x_sel_m0_r1_cfg_0),
      .o_ca_dq_tx_ddr_x_sel_m0_r1_cfg_1 (dq_dq_tx_ddr_x_sel_m0_r1_cfg_1),
      .o_ca_dq_tx_ddr_x_sel_m0_r1_cfg_2 (dq_dq_tx_ddr_x_sel_m0_r1_cfg_2),
      .o_ca_dq_tx_ddr_x_sel_m0_r1_cfg_3 (dq_dq_tx_ddr_x_sel_m0_r1_cfg_3),
      .o_ca_dq_tx_ddr_x_sel_m0_r1_cfg_4 (dq_dq_tx_ddr_x_sel_m0_r1_cfg_4),
      .o_ca_dq_tx_ddr_x_sel_m0_r1_cfg_5 (dq_dq_tx_ddr_x_sel_m0_r1_cfg_5),
      .o_ca_dq_tx_ddr_x_sel_m0_r1_cfg_6 (dq_dq_tx_ddr_x_sel_m0_r1_cfg_6),
      .o_ca_dq_tx_ddr_x_sel_m0_r1_cfg_7 (dq_dq_tx_ddr_x_sel_m0_r1_cfg_7),
      .o_ca_dq_tx_ddr_x_sel_m0_r1_cfg_8 (dq_dq_tx_ddr_x_sel_m0_r1_cfg_8),
      .o_ca_dq_tx_ddr_x_sel_m0_r1_cfg_9 (dq_dq_tx_ddr_x_sel_m0_r1_cfg_9),
      .o_ca_dq_tx_ddr_x_sel_m0_r1_cfg_10 (dq_dq_tx_ddr_x_sel_m0_r1_cfg_10),
      .o_ca_dq_tx_ddr_x_sel_m1_r0_cfg_0 (dq_dq_tx_ddr_x_sel_m1_r0_cfg_0),
      .o_ca_dq_tx_ddr_x_sel_m1_r0_cfg_1 (dq_dq_tx_ddr_x_sel_m1_r0_cfg_1),
      .o_ca_dq_tx_ddr_x_sel_m1_r0_cfg_2 (dq_dq_tx_ddr_x_sel_m1_r0_cfg_2),
      .o_ca_dq_tx_ddr_x_sel_m1_r0_cfg_3 (dq_dq_tx_ddr_x_sel_m1_r0_cfg_3),
      .o_ca_dq_tx_ddr_x_sel_m1_r0_cfg_4 (dq_dq_tx_ddr_x_sel_m1_r0_cfg_4),
      .o_ca_dq_tx_ddr_x_sel_m1_r0_cfg_5 (dq_dq_tx_ddr_x_sel_m1_r0_cfg_5),
      .o_ca_dq_tx_ddr_x_sel_m1_r0_cfg_6 (dq_dq_tx_ddr_x_sel_m1_r0_cfg_6),
      .o_ca_dq_tx_ddr_x_sel_m1_r0_cfg_7 (dq_dq_tx_ddr_x_sel_m1_r0_cfg_7),
      .o_ca_dq_tx_ddr_x_sel_m1_r0_cfg_8 (dq_dq_tx_ddr_x_sel_m1_r0_cfg_8),
      .o_ca_dq_tx_ddr_x_sel_m1_r0_cfg_9 (dq_dq_tx_ddr_x_sel_m1_r0_cfg_9),
      .o_ca_dq_tx_ddr_x_sel_m1_r0_cfg_10 (dq_dq_tx_ddr_x_sel_m1_r0_cfg_10),
      .o_ca_dq_tx_ddr_x_sel_m1_r1_cfg_0 (dq_dq_tx_ddr_x_sel_m1_r1_cfg_0),
      .o_ca_dq_tx_ddr_x_sel_m1_r1_cfg_1 (dq_dq_tx_ddr_x_sel_m1_r1_cfg_1),
      .o_ca_dq_tx_ddr_x_sel_m1_r1_cfg_2 (dq_dq_tx_ddr_x_sel_m1_r1_cfg_2),
      .o_ca_dq_tx_ddr_x_sel_m1_r1_cfg_3 (dq_dq_tx_ddr_x_sel_m1_r1_cfg_3),
      .o_ca_dq_tx_ddr_x_sel_m1_r1_cfg_4 (dq_dq_tx_ddr_x_sel_m1_r1_cfg_4),
      .o_ca_dq_tx_ddr_x_sel_m1_r1_cfg_5 (dq_dq_tx_ddr_x_sel_m1_r1_cfg_5),
      .o_ca_dq_tx_ddr_x_sel_m1_r1_cfg_6 (dq_dq_tx_ddr_x_sel_m1_r1_cfg_6),
      .o_ca_dq_tx_ddr_x_sel_m1_r1_cfg_7 (dq_dq_tx_ddr_x_sel_m1_r1_cfg_7),
      .o_ca_dq_tx_ddr_x_sel_m1_r1_cfg_8 (dq_dq_tx_ddr_x_sel_m1_r1_cfg_8),
      .o_ca_dq_tx_ddr_x_sel_m1_r1_cfg_9 (dq_dq_tx_ddr_x_sel_m1_r1_cfg_9),
      .o_ca_dq_tx_ddr_x_sel_m1_r1_cfg_10 (dq_dq_tx_ddr_x_sel_m1_r1_cfg_10),
      .o_ca_dq_tx_qdr_m0_r0_cfg_0      (dq_dq_tx_qdr_m0_r0_cfg_0),
      .o_ca_dq_tx_qdr_m0_r0_cfg_1      (dq_dq_tx_qdr_m0_r0_cfg_1),
      .o_ca_dq_tx_qdr_m0_r0_cfg_2      (dq_dq_tx_qdr_m0_r0_cfg_2),
      .o_ca_dq_tx_qdr_m0_r0_cfg_3      (dq_dq_tx_qdr_m0_r0_cfg_3),
      .o_ca_dq_tx_qdr_m0_r0_cfg_4      (dq_dq_tx_qdr_m0_r0_cfg_4),
      .o_ca_dq_tx_qdr_m0_r0_cfg_5      (dq_dq_tx_qdr_m0_r0_cfg_5),
      .o_ca_dq_tx_qdr_m0_r0_cfg_6      (dq_dq_tx_qdr_m0_r0_cfg_6),
      .o_ca_dq_tx_qdr_m0_r0_cfg_7      (dq_dq_tx_qdr_m0_r0_cfg_7),
      .o_ca_dq_tx_qdr_m0_r0_cfg_8      (dq_dq_tx_qdr_m0_r0_cfg_8),
      .o_ca_dq_tx_qdr_m0_r0_cfg_9      (dq_dq_tx_qdr_m0_r0_cfg_9),
      .o_ca_dq_tx_qdr_m0_r0_cfg_10      (dq_dq_tx_qdr_m0_r0_cfg_10),
      .o_ca_dq_tx_qdr_m0_r1_cfg_0      (dq_dq_tx_qdr_m0_r1_cfg_0),
      .o_ca_dq_tx_qdr_m0_r1_cfg_1      (dq_dq_tx_qdr_m0_r1_cfg_1),
      .o_ca_dq_tx_qdr_m0_r1_cfg_2      (dq_dq_tx_qdr_m0_r1_cfg_2),
      .o_ca_dq_tx_qdr_m0_r1_cfg_3      (dq_dq_tx_qdr_m0_r1_cfg_3),
      .o_ca_dq_tx_qdr_m0_r1_cfg_4      (dq_dq_tx_qdr_m0_r1_cfg_4),
      .o_ca_dq_tx_qdr_m0_r1_cfg_5      (dq_dq_tx_qdr_m0_r1_cfg_5),
      .o_ca_dq_tx_qdr_m0_r1_cfg_6      (dq_dq_tx_qdr_m0_r1_cfg_6),
      .o_ca_dq_tx_qdr_m0_r1_cfg_7      (dq_dq_tx_qdr_m0_r1_cfg_7),
      .o_ca_dq_tx_qdr_m0_r1_cfg_8      (dq_dq_tx_qdr_m0_r1_cfg_8),
      .o_ca_dq_tx_qdr_m0_r1_cfg_9      (dq_dq_tx_qdr_m0_r1_cfg_9),
      .o_ca_dq_tx_qdr_m0_r1_cfg_10      (dq_dq_tx_qdr_m0_r1_cfg_10),
      .o_ca_dq_tx_qdr_m1_r0_cfg_0      (dq_dq_tx_qdr_m1_r0_cfg_0),
      .o_ca_dq_tx_qdr_m1_r0_cfg_1      (dq_dq_tx_qdr_m1_r0_cfg_1),
      .o_ca_dq_tx_qdr_m1_r0_cfg_2      (dq_dq_tx_qdr_m1_r0_cfg_2),
      .o_ca_dq_tx_qdr_m1_r0_cfg_3      (dq_dq_tx_qdr_m1_r0_cfg_3),
      .o_ca_dq_tx_qdr_m1_r0_cfg_4      (dq_dq_tx_qdr_m1_r0_cfg_4),
      .o_ca_dq_tx_qdr_m1_r0_cfg_5      (dq_dq_tx_qdr_m1_r0_cfg_5),
      .o_ca_dq_tx_qdr_m1_r0_cfg_6      (dq_dq_tx_qdr_m1_r0_cfg_6),
      .o_ca_dq_tx_qdr_m1_r0_cfg_7      (dq_dq_tx_qdr_m1_r0_cfg_7),
      .o_ca_dq_tx_qdr_m1_r0_cfg_8      (dq_dq_tx_qdr_m1_r0_cfg_8),
      .o_ca_dq_tx_qdr_m1_r0_cfg_9      (dq_dq_tx_qdr_m1_r0_cfg_9),
      .o_ca_dq_tx_qdr_m1_r0_cfg_10      (dq_dq_tx_qdr_m1_r0_cfg_10),
      .o_ca_dq_tx_qdr_m1_r1_cfg_0      (dq_dq_tx_qdr_m1_r1_cfg_0),
      .o_ca_dq_tx_qdr_m1_r1_cfg_1      (dq_dq_tx_qdr_m1_r1_cfg_1),
      .o_ca_dq_tx_qdr_m1_r1_cfg_2      (dq_dq_tx_qdr_m1_r1_cfg_2),
      .o_ca_dq_tx_qdr_m1_r1_cfg_3      (dq_dq_tx_qdr_m1_r1_cfg_3),
      .o_ca_dq_tx_qdr_m1_r1_cfg_4      (dq_dq_tx_qdr_m1_r1_cfg_4),
      .o_ca_dq_tx_qdr_m1_r1_cfg_5      (dq_dq_tx_qdr_m1_r1_cfg_5),
      .o_ca_dq_tx_qdr_m1_r1_cfg_6      (dq_dq_tx_qdr_m1_r1_cfg_6),
      .o_ca_dq_tx_qdr_m1_r1_cfg_7      (dq_dq_tx_qdr_m1_r1_cfg_7),
      .o_ca_dq_tx_qdr_m1_r1_cfg_8      (dq_dq_tx_qdr_m1_r1_cfg_8),
      .o_ca_dq_tx_qdr_m1_r1_cfg_9      (dq_dq_tx_qdr_m1_r1_cfg_9),
      .o_ca_dq_tx_qdr_m1_r1_cfg_10      (dq_dq_tx_qdr_m1_r1_cfg_10),
      .o_ca_dq_tx_qdr_x_sel_m0_r0_cfg_0 (dq_dq_tx_qdr_x_sel_m0_r0_cfg_0),
      .o_ca_dq_tx_qdr_x_sel_m0_r0_cfg_1 (dq_dq_tx_qdr_x_sel_m0_r0_cfg_1),
      .o_ca_dq_tx_qdr_x_sel_m0_r0_cfg_2 (dq_dq_tx_qdr_x_sel_m0_r0_cfg_2),
      .o_ca_dq_tx_qdr_x_sel_m0_r0_cfg_3 (dq_dq_tx_qdr_x_sel_m0_r0_cfg_3),
      .o_ca_dq_tx_qdr_x_sel_m0_r0_cfg_4 (dq_dq_tx_qdr_x_sel_m0_r0_cfg_4),
      .o_ca_dq_tx_qdr_x_sel_m0_r0_cfg_5 (dq_dq_tx_qdr_x_sel_m0_r0_cfg_5),
      .o_ca_dq_tx_qdr_x_sel_m0_r0_cfg_6 (dq_dq_tx_qdr_x_sel_m0_r0_cfg_6),
      .o_ca_dq_tx_qdr_x_sel_m0_r0_cfg_7 (dq_dq_tx_qdr_x_sel_m0_r0_cfg_7),
      .o_ca_dq_tx_qdr_x_sel_m0_r0_cfg_8 (dq_dq_tx_qdr_x_sel_m0_r0_cfg_8),
      .o_ca_dq_tx_qdr_x_sel_m0_r0_cfg_9 (dq_dq_tx_qdr_x_sel_m0_r0_cfg_9),
      .o_ca_dq_tx_qdr_x_sel_m0_r0_cfg_10 (dq_dq_tx_qdr_x_sel_m0_r0_cfg_10),
      .o_ca_dq_tx_qdr_x_sel_m0_r1_cfg_0 (dq_dq_tx_qdr_x_sel_m0_r1_cfg_0),
      .o_ca_dq_tx_qdr_x_sel_m0_r1_cfg_1 (dq_dq_tx_qdr_x_sel_m0_r1_cfg_1),
      .o_ca_dq_tx_qdr_x_sel_m0_r1_cfg_2 (dq_dq_tx_qdr_x_sel_m0_r1_cfg_2),
      .o_ca_dq_tx_qdr_x_sel_m0_r1_cfg_3 (dq_dq_tx_qdr_x_sel_m0_r1_cfg_3),
      .o_ca_dq_tx_qdr_x_sel_m0_r1_cfg_4 (dq_dq_tx_qdr_x_sel_m0_r1_cfg_4),
      .o_ca_dq_tx_qdr_x_sel_m0_r1_cfg_5 (dq_dq_tx_qdr_x_sel_m0_r1_cfg_5),
      .o_ca_dq_tx_qdr_x_sel_m0_r1_cfg_6 (dq_dq_tx_qdr_x_sel_m0_r1_cfg_6),
      .o_ca_dq_tx_qdr_x_sel_m0_r1_cfg_7 (dq_dq_tx_qdr_x_sel_m0_r1_cfg_7),
      .o_ca_dq_tx_qdr_x_sel_m0_r1_cfg_8 (dq_dq_tx_qdr_x_sel_m0_r1_cfg_8),
      .o_ca_dq_tx_qdr_x_sel_m0_r1_cfg_9 (dq_dq_tx_qdr_x_sel_m0_r1_cfg_9),
      .o_ca_dq_tx_qdr_x_sel_m0_r1_cfg_10 (dq_dq_tx_qdr_x_sel_m0_r1_cfg_10),
      .o_ca_dq_tx_qdr_x_sel_m1_r0_cfg_0 (dq_dq_tx_qdr_x_sel_m1_r0_cfg_0),
      .o_ca_dq_tx_qdr_x_sel_m1_r0_cfg_1 (dq_dq_tx_qdr_x_sel_m1_r0_cfg_1),
      .o_ca_dq_tx_qdr_x_sel_m1_r0_cfg_2 (dq_dq_tx_qdr_x_sel_m1_r0_cfg_2),
      .o_ca_dq_tx_qdr_x_sel_m1_r0_cfg_3 (dq_dq_tx_qdr_x_sel_m1_r0_cfg_3),
      .o_ca_dq_tx_qdr_x_sel_m1_r0_cfg_4 (dq_dq_tx_qdr_x_sel_m1_r0_cfg_4),
      .o_ca_dq_tx_qdr_x_sel_m1_r0_cfg_5 (dq_dq_tx_qdr_x_sel_m1_r0_cfg_5),
      .o_ca_dq_tx_qdr_x_sel_m1_r0_cfg_6 (dq_dq_tx_qdr_x_sel_m1_r0_cfg_6),
      .o_ca_dq_tx_qdr_x_sel_m1_r0_cfg_7 (dq_dq_tx_qdr_x_sel_m1_r0_cfg_7),
      .o_ca_dq_tx_qdr_x_sel_m1_r0_cfg_8 (dq_dq_tx_qdr_x_sel_m1_r0_cfg_8),
      .o_ca_dq_tx_qdr_x_sel_m1_r0_cfg_9 (dq_dq_tx_qdr_x_sel_m1_r0_cfg_9),
      .o_ca_dq_tx_qdr_x_sel_m1_r0_cfg_10 (dq_dq_tx_qdr_x_sel_m1_r0_cfg_10),
      .o_ca_dq_tx_qdr_x_sel_m1_r1_cfg_0 (dq_dq_tx_qdr_x_sel_m1_r1_cfg_0),
      .o_ca_dq_tx_qdr_x_sel_m1_r1_cfg_1 (dq_dq_tx_qdr_x_sel_m1_r1_cfg_1),
      .o_ca_dq_tx_qdr_x_sel_m1_r1_cfg_2 (dq_dq_tx_qdr_x_sel_m1_r1_cfg_2),
      .o_ca_dq_tx_qdr_x_sel_m1_r1_cfg_3 (dq_dq_tx_qdr_x_sel_m1_r1_cfg_3),
      .o_ca_dq_tx_qdr_x_sel_m1_r1_cfg_4 (dq_dq_tx_qdr_x_sel_m1_r1_cfg_4),
      .o_ca_dq_tx_qdr_x_sel_m1_r1_cfg_5 (dq_dq_tx_qdr_x_sel_m1_r1_cfg_5),
      .o_ca_dq_tx_qdr_x_sel_m1_r1_cfg_6 (dq_dq_tx_qdr_x_sel_m1_r1_cfg_6),
      .o_ca_dq_tx_qdr_x_sel_m1_r1_cfg_7 (dq_dq_tx_qdr_x_sel_m1_r1_cfg_7),
      .o_ca_dq_tx_qdr_x_sel_m1_r1_cfg_8 (dq_dq_tx_qdr_x_sel_m1_r1_cfg_8),
      .o_ca_dq_tx_qdr_x_sel_m1_r1_cfg_9 (dq_dq_tx_qdr_x_sel_m1_r1_cfg_9),
      .o_ca_dq_tx_qdr_x_sel_m1_r1_cfg_10 (dq_dq_tx_qdr_x_sel_m1_r1_cfg_10),
      .o_ca_dq_tx_lpde_m0_r0_cfg_0    (dq_dq_tx_lpde_m0_r0_cfg_0),
      .o_ca_dq_tx_lpde_m0_r0_cfg_1    (dq_dq_tx_lpde_m0_r0_cfg_1),
      .o_ca_dq_tx_lpde_m0_r0_cfg_2    (dq_dq_tx_lpde_m0_r0_cfg_2),
      .o_ca_dq_tx_lpde_m0_r0_cfg_3    (dq_dq_tx_lpde_m0_r0_cfg_3),
      .o_ca_dq_tx_lpde_m0_r0_cfg_4    (dq_dq_tx_lpde_m0_r0_cfg_4),
      .o_ca_dq_tx_lpde_m0_r0_cfg_5    (dq_dq_tx_lpde_m0_r0_cfg_5),
      .o_ca_dq_tx_lpde_m0_r0_cfg_6    (dq_dq_tx_lpde_m0_r0_cfg_6),
      .o_ca_dq_tx_lpde_m0_r0_cfg_7    (dq_dq_tx_lpde_m0_r0_cfg_7),
      .o_ca_dq_tx_lpde_m0_r0_cfg_8    (dq_dq_tx_lpde_m0_r0_cfg_8),
      .o_ca_dq_tx_lpde_m0_r0_cfg_9    (dq_dq_tx_lpde_m0_r0_cfg_9),
      .o_ca_dq_tx_lpde_m0_r0_cfg_10    (dq_dq_tx_lpde_m0_r0_cfg_10),
      .o_ca_dq_tx_lpde_m0_r1_cfg_0    (dq_dq_tx_lpde_m0_r1_cfg_0),
      .o_ca_dq_tx_lpde_m0_r1_cfg_1    (dq_dq_tx_lpde_m0_r1_cfg_1),
      .o_ca_dq_tx_lpde_m0_r1_cfg_2    (dq_dq_tx_lpde_m0_r1_cfg_2),
      .o_ca_dq_tx_lpde_m0_r1_cfg_3    (dq_dq_tx_lpde_m0_r1_cfg_3),
      .o_ca_dq_tx_lpde_m0_r1_cfg_4    (dq_dq_tx_lpde_m0_r1_cfg_4),
      .o_ca_dq_tx_lpde_m0_r1_cfg_5    (dq_dq_tx_lpde_m0_r1_cfg_5),
      .o_ca_dq_tx_lpde_m0_r1_cfg_6    (dq_dq_tx_lpde_m0_r1_cfg_6),
      .o_ca_dq_tx_lpde_m0_r1_cfg_7    (dq_dq_tx_lpde_m0_r1_cfg_7),
      .o_ca_dq_tx_lpde_m0_r1_cfg_8    (dq_dq_tx_lpde_m0_r1_cfg_8),
      .o_ca_dq_tx_lpde_m0_r1_cfg_9    (dq_dq_tx_lpde_m0_r1_cfg_9),
      .o_ca_dq_tx_lpde_m0_r1_cfg_10    (dq_dq_tx_lpde_m0_r1_cfg_10),
      .o_ca_dq_tx_lpde_m1_r0_cfg_0    (dq_dq_tx_lpde_m1_r0_cfg_0),
      .o_ca_dq_tx_lpde_m1_r0_cfg_1    (dq_dq_tx_lpde_m1_r0_cfg_1),
      .o_ca_dq_tx_lpde_m1_r0_cfg_2    (dq_dq_tx_lpde_m1_r0_cfg_2),
      .o_ca_dq_tx_lpde_m1_r0_cfg_3    (dq_dq_tx_lpde_m1_r0_cfg_3),
      .o_ca_dq_tx_lpde_m1_r0_cfg_4    (dq_dq_tx_lpde_m1_r0_cfg_4),
      .o_ca_dq_tx_lpde_m1_r0_cfg_5    (dq_dq_tx_lpde_m1_r0_cfg_5),
      .o_ca_dq_tx_lpde_m1_r0_cfg_6    (dq_dq_tx_lpde_m1_r0_cfg_6),
      .o_ca_dq_tx_lpde_m1_r0_cfg_7    (dq_dq_tx_lpde_m1_r0_cfg_7),
      .o_ca_dq_tx_lpde_m1_r0_cfg_8    (dq_dq_tx_lpde_m1_r0_cfg_8),
      .o_ca_dq_tx_lpde_m1_r0_cfg_9    (dq_dq_tx_lpde_m1_r0_cfg_9),
      .o_ca_dq_tx_lpde_m1_r0_cfg_10    (dq_dq_tx_lpde_m1_r0_cfg_10),
      .o_ca_dq_tx_lpde_m1_r1_cfg_0    (dq_dq_tx_lpde_m1_r1_cfg_0),
      .o_ca_dq_tx_lpde_m1_r1_cfg_1    (dq_dq_tx_lpde_m1_r1_cfg_1),
      .o_ca_dq_tx_lpde_m1_r1_cfg_2    (dq_dq_tx_lpde_m1_r1_cfg_2),
      .o_ca_dq_tx_lpde_m1_r1_cfg_3    (dq_dq_tx_lpde_m1_r1_cfg_3),
      .o_ca_dq_tx_lpde_m1_r1_cfg_4    (dq_dq_tx_lpde_m1_r1_cfg_4),
      .o_ca_dq_tx_lpde_m1_r1_cfg_5    (dq_dq_tx_lpde_m1_r1_cfg_5),
      .o_ca_dq_tx_lpde_m1_r1_cfg_6    (dq_dq_tx_lpde_m1_r1_cfg_6),
      .o_ca_dq_tx_lpde_m1_r1_cfg_7    (dq_dq_tx_lpde_m1_r1_cfg_7),
      .o_ca_dq_tx_lpde_m1_r1_cfg_8    (dq_dq_tx_lpde_m1_r1_cfg_8),
      .o_ca_dq_tx_lpde_m1_r1_cfg_9    (dq_dq_tx_lpde_m1_r1_cfg_9),
      .o_ca_dq_tx_lpde_m1_r1_cfg_10    (dq_dq_tx_lpde_m1_r1_cfg_10),
   //`for (i=0; i<`DDR_NUM_CA_SLICES; i++)
   //   .o_ca_dq_tx_io_m0_r0_cfg_`i      (dq_dq_tx_io_m0_r0_cfg_`i),
   //`endfor
   //`for (i=0; i<`DDR_NUM_CA_SLICES; i++)
   //   .o_ca_dq_tx_io_m0_r1_cfg_`i      (dq_dq_tx_io_m0_r1_cfg_`i),
   //`endfor
   //`for (i=0; i<`DDR_NUM_CA_SLICES; i++)
   //   .o_ca_dq_tx_io_m1_r0_cfg_`i      (dq_dq_tx_io_m1_r0_cfg_`i),
   //`endfor
   //`for (i=0; i<`DDR_NUM_CA_SLICES; i++)
   //   .o_ca_dq_tx_io_m1_r1_cfg_`i      (dq_dq_tx_io_m1_r1_cfg_`i),
   //`endfor
      .o_ca_dq_tx_io_m0_cfg_0      (dq_dq_tx_io_m0_cfg_0),
      .o_ca_dq_tx_io_m0_cfg_1      (dq_dq_tx_io_m0_cfg_1),
      .o_ca_dq_tx_io_m0_cfg_2      (dq_dq_tx_io_m0_cfg_2),
      .o_ca_dq_tx_io_m0_cfg_3      (dq_dq_tx_io_m0_cfg_3),
      .o_ca_dq_tx_io_m0_cfg_4      (dq_dq_tx_io_m0_cfg_4),
      .o_ca_dq_tx_io_m0_cfg_5      (dq_dq_tx_io_m0_cfg_5),
      .o_ca_dq_tx_io_m0_cfg_6      (dq_dq_tx_io_m0_cfg_6),
      .o_ca_dq_tx_io_m0_cfg_7      (dq_dq_tx_io_m0_cfg_7),
      .o_ca_dq_tx_io_m0_cfg_8      (dq_dq_tx_io_m0_cfg_8),
      .o_ca_dq_tx_io_m0_cfg_9      (dq_dq_tx_io_m0_cfg_9),
      .o_ca_dq_tx_io_m0_cfg_10      (dq_dq_tx_io_m0_cfg_10),
      .o_ca_dq_tx_io_m1_cfg_0      (dq_dq_tx_io_m1_cfg_0),
      .o_ca_dq_tx_io_m1_cfg_1      (dq_dq_tx_io_m1_cfg_1),
      .o_ca_dq_tx_io_m1_cfg_2      (dq_dq_tx_io_m1_cfg_2),
      .o_ca_dq_tx_io_m1_cfg_3      (dq_dq_tx_io_m1_cfg_3),
      .o_ca_dq_tx_io_m1_cfg_4      (dq_dq_tx_io_m1_cfg_4),
      .o_ca_dq_tx_io_m1_cfg_5      (dq_dq_tx_io_m1_cfg_5),
      .o_ca_dq_tx_io_m1_cfg_6      (dq_dq_tx_io_m1_cfg_6),
      .o_ca_dq_tx_io_m1_cfg_7      (dq_dq_tx_io_m1_cfg_7),
      .o_ca_dq_tx_io_m1_cfg_8      (dq_dq_tx_io_m1_cfg_8),
      .o_ca_dq_tx_io_m1_cfg_9      (dq_dq_tx_io_m1_cfg_9),
      .o_ca_dq_tx_io_m1_cfg_10      (dq_dq_tx_io_m1_cfg_10),

      // ---------------------------------------------------------
      // DQS RX
      // ---------------------------------------------------------

      .o_ca_dqs_rx_m0_cfg              (dq_dqs_rx_m0_cfg),
      .o_ca_dqs_rx_m1_cfg              (dq_dqs_rx_m1_cfg),
      .i_ca_dqs_rx_bscan_sta           (dq_dqs_rx_bscan_sta),
      .o_ca_dqs_rx_sdr_lpde_m0_r0_cfg  (dq_dqs_rx_sdr_lpde_m0_r0_cfg),
      .o_ca_dqs_rx_sdr_lpde_m0_r1_cfg  (dq_dqs_rx_sdr_lpde_m0_r1_cfg),
      .o_ca_dqs_rx_sdr_lpde_m1_r0_cfg  (dq_dqs_rx_sdr_lpde_m1_r0_cfg),
      .o_ca_dqs_rx_sdr_lpde_m1_r1_cfg  (dq_dqs_rx_sdr_lpde_m1_r1_cfg),
      .o_ca_dqs_rx_ren_pi_m0_r0_cfg    (dq_dqs_rx_ren_pi_m0_r0_cfg),
      .o_ca_dqs_rx_ren_pi_m0_r1_cfg    (dq_dqs_rx_ren_pi_m0_r1_cfg),
      .o_ca_dqs_rx_ren_pi_m1_r0_cfg    (dq_dqs_rx_ren_pi_m1_r0_cfg),
      .o_ca_dqs_rx_ren_pi_m1_r1_cfg    (dq_dqs_rx_ren_pi_m1_r1_cfg),
      .o_ca_dqs_rx_rcs_pi_m0_r0_cfg    (dq_dqs_rx_rcs_pi_m0_r0_cfg),
      .o_ca_dqs_rx_rcs_pi_m0_r1_cfg    (dq_dqs_rx_rcs_pi_m0_r1_cfg),
      .o_ca_dqs_rx_rcs_pi_m1_r0_cfg    (dq_dqs_rx_rcs_pi_m1_r0_cfg),
      .o_ca_dqs_rx_rcs_pi_m1_r1_cfg    (dq_dqs_rx_rcs_pi_m1_r1_cfg),
      .o_ca_dqs_rx_rdqs_pi_0_m0_r0_cfg (dq_dqs_rx_rdqs_pi_0_m0_r0_cfg),
      .o_ca_dqs_rx_rdqs_pi_0_m0_r1_cfg (dq_dqs_rx_rdqs_pi_0_m0_r1_cfg),
      .o_ca_dqs_rx_rdqs_pi_0_m1_r0_cfg (dq_dqs_rx_rdqs_pi_0_m1_r0_cfg),
      .o_ca_dqs_rx_rdqs_pi_0_m1_r1_cfg (dq_dqs_rx_rdqs_pi_0_m1_r1_cfg),
      .o_ca_dqs_rx_rdqs_pi_1_m0_r0_cfg (dq_dqs_rx_rdqs_pi_1_m0_r0_cfg),
      .o_ca_dqs_rx_rdqs_pi_1_m0_r1_cfg (dq_dqs_rx_rdqs_pi_1_m0_r1_cfg),
      .o_ca_dqs_rx_rdqs_pi_1_m1_r0_cfg (dq_dqs_rx_rdqs_pi_1_m1_r0_cfg),
      .o_ca_dqs_rx_rdqs_pi_1_m1_r1_cfg (dq_dqs_rx_rdqs_pi_1_m1_r1_cfg),
      .o_ca_dqs_rx_io_m0_r0_cfg_0     (dq_dqs_rx_io_m0_r0_cfg_0),
      .o_ca_dqs_rx_io_m0_r1_cfg_0     (dq_dqs_rx_io_m0_r1_cfg_0),
      .o_ca_dqs_rx_io_m1_r0_cfg_0     (dq_dqs_rx_io_m1_r0_cfg_0),
      .o_ca_dqs_rx_io_m1_r1_cfg_0     (dq_dqs_rx_io_m1_r1_cfg_0),
      .o_ca_dqs_rx_io_cmn_m0_r0_cfg    (dq_dqs_rx_io_cmn_m0_r0_cfg),
      .o_ca_dqs_rx_io_cmn_m0_r1_cfg    (dq_dqs_rx_io_cmn_m0_r1_cfg),
      .o_ca_dqs_rx_io_cmn_m1_r0_cfg    (dq_dqs_rx_io_cmn_m1_r0_cfg),
      .o_ca_dqs_rx_io_cmn_m1_r1_cfg    (dq_dqs_rx_io_cmn_m1_r1_cfg),
      .o_ca_dqs_rx_sa_m0_r0_cfg_0      (dq_dqs_rx_sa_m0_r0_cfg_0),
      .o_ca_dqs_rx_sa_m0_r1_cfg_0      (dq_dqs_rx_sa_m0_r1_cfg_0),
      .o_ca_dqs_rx_sa_m1_r0_cfg_0      (dq_dqs_rx_sa_m1_r0_cfg_0),
      .o_ca_dqs_rx_sa_m1_r1_cfg_0      (dq_dqs_rx_sa_m1_r1_cfg_0),
      //.o_ca_dqs_rx_sa_cmn_r0_cfg      (dq_dqs_rx_sa_cmn_r0_cfg),
      //.o_ca_dqs_rx_sa_cmn_r1_cfg      (dq_dqs_rx_sa_cmn_r1_cfg),
      .o_ca_dqs_rx_sa_cmn_cfg         (dq_dqs_rx_sa_cmn_cfg),
`ifdef DDR_DQS_VREF
      .o_ca_dqs_rx_refgen_m0_r0_cfg   (dq_dqs_rx_refgen_m0_r0_cfg),
      .o_ca_dqs_rx_refgen_m0_r1_cfg   (dq_dqs_rx_refgen_m0_r1_cfg),
      .o_ca_dqs_rx_refgen_m1_r0_cfg   (dq_dqs_rx_refgen_m1_r0_cfg),
      .o_ca_dqs_rx_refgen_m1_r1_cfg   (dq_dqs_rx_refgen_m1_r1_cfg),
`endif
      .i_ca_dqs_rx_io_sta             (dq_dqs_rx_io_sta),
      .i_ca_dqs_rx_pi_sta             (dq_dqs_rx_pi_sta),

      // ---------------------------------------------------------
      // DQS TX
      // ---------------------------------------------------------

      .o_ca_dqs_tx_m0_cfg              (dq_dqs_tx_m0_cfg),
      .o_ca_dqs_tx_m1_cfg              (dq_dqs_tx_m1_cfg),
      .o_ca_dqs_tx_bscan_ctrl_cfg      (dq_dqs_tx_bscan_ctrl_cfg),
      .o_ca_dqs_tx_bscan_cfg           (dq_dqs_tx_bscan_cfg),
      .o_ca_dqs_tx_egress_ana_m0_cfg_0 (dq_dqs_tx_egress_ana_m0_cfg_0),
      .o_ca_dqs_tx_egress_ana_m1_cfg_0 (dq_dqs_tx_egress_ana_m1_cfg_0),
      .o_ca_dqs_tx_egress_dig_m0_cfg_0 (dq_dqs_tx_egress_dig_m0_cfg_0),
      .o_ca_dqs_tx_egress_dig_m1_cfg_0 (dq_dqs_tx_egress_dig_m1_cfg_0),
      .o_ca_dqs_tx_odr_pi_m0_r0_cfg    (dq_dqs_tx_odr_pi_m0_r0_cfg),
      .o_ca_dqs_tx_odr_pi_m0_r1_cfg    (dq_dqs_tx_odr_pi_m0_r1_cfg),
      .o_ca_dqs_tx_odr_pi_m1_r0_cfg    (dq_dqs_tx_odr_pi_m1_r0_cfg),
      .o_ca_dqs_tx_odr_pi_m1_r1_cfg    (dq_dqs_tx_odr_pi_m1_r1_cfg),
      .o_ca_dqs_tx_qdr_pi_0_m0_r0_cfg  (dq_dqs_tx_qdr_pi_0_m0_r0_cfg),
      .o_ca_dqs_tx_qdr_pi_0_m0_r1_cfg  (dq_dqs_tx_qdr_pi_0_m0_r1_cfg),
      .o_ca_dqs_tx_qdr_pi_0_m1_r0_cfg  (dq_dqs_tx_qdr_pi_0_m1_r0_cfg),
      .o_ca_dqs_tx_qdr_pi_0_m1_r1_cfg  (dq_dqs_tx_qdr_pi_0_m1_r1_cfg),
      .o_ca_dqs_tx_qdr_pi_1_m0_r0_cfg  (dq_dqs_tx_qdr_pi_1_m0_r0_cfg),
      .o_ca_dqs_tx_qdr_pi_1_m0_r1_cfg  (dq_dqs_tx_qdr_pi_1_m0_r1_cfg),
      .o_ca_dqs_tx_qdr_pi_1_m1_r0_cfg  (dq_dqs_tx_qdr_pi_1_m1_r0_cfg),
      .o_ca_dqs_tx_qdr_pi_1_m1_r1_cfg  (dq_dqs_tx_qdr_pi_1_m1_r1_cfg),
      .o_ca_dqs_tx_ddr_pi_0_m0_r0_cfg  (dq_dqs_tx_ddr_pi_0_m0_r0_cfg),
      .o_ca_dqs_tx_ddr_pi_0_m0_r1_cfg  (dq_dqs_tx_ddr_pi_0_m0_r1_cfg),
      .o_ca_dqs_tx_ddr_pi_0_m1_r0_cfg  (dq_dqs_tx_ddr_pi_0_m1_r0_cfg),
      .o_ca_dqs_tx_ddr_pi_0_m1_r1_cfg  (dq_dqs_tx_ddr_pi_0_m1_r1_cfg),
      .o_ca_dqs_tx_ddr_pi_1_m0_r0_cfg  (dq_dqs_tx_ddr_pi_1_m0_r0_cfg),
      .o_ca_dqs_tx_ddr_pi_1_m0_r1_cfg  (dq_dqs_tx_ddr_pi_1_m0_r1_cfg),
      .o_ca_dqs_tx_ddr_pi_1_m1_r0_cfg  (dq_dqs_tx_ddr_pi_1_m1_r0_cfg),
      .o_ca_dqs_tx_ddr_pi_1_m1_r1_cfg  (dq_dqs_tx_ddr_pi_1_m1_r1_cfg),
      .o_ca_dqs_tx_pi_rt_m0_r0_cfg     (dq_dqs_tx_pi_rt_m0_r0_cfg),
      .o_ca_dqs_tx_pi_rt_m0_r1_cfg     (dq_dqs_tx_pi_rt_m0_r1_cfg),
      .o_ca_dqs_tx_pi_rt_m1_r0_cfg     (dq_dqs_tx_pi_rt_m1_r0_cfg),
      .o_ca_dqs_tx_pi_rt_m1_r1_cfg     (dq_dqs_tx_pi_rt_m1_r1_cfg),
      .o_ca_dqs_tx_sdr_pi_m0_r0_cfg    (dq_dqs_tx_sdr_pi_m0_r0_cfg),
      .o_ca_dqs_tx_sdr_pi_m0_r1_cfg    (dq_dqs_tx_sdr_pi_m0_r1_cfg),
      .o_ca_dqs_tx_sdr_pi_m1_r0_cfg    (dq_dqs_tx_sdr_pi_m1_r0_cfg),
      .o_ca_dqs_tx_sdr_pi_m1_r1_cfg    (dq_dqs_tx_sdr_pi_m1_r1_cfg),
      .o_ca_dqs_tx_dfi_pi_m0_r0_cfg    (dq_dqs_tx_dfi_pi_m0_r0_cfg),
      .o_ca_dqs_tx_dfi_pi_m0_r1_cfg    (dq_dqs_tx_dfi_pi_m0_r1_cfg),
      .o_ca_dqs_tx_dfi_pi_m1_r0_cfg    (dq_dqs_tx_dfi_pi_m1_r0_cfg),
      .o_ca_dqs_tx_dfi_pi_m1_r1_cfg    (dq_dqs_tx_dfi_pi_m1_r1_cfg),
      .o_ca_dqs_tx_rt_m0_r0_cfg        (dq_dqs_tx_rt_m0_r0_cfg),
      .o_ca_dqs_tx_rt_m0_r1_cfg        (dq_dqs_tx_rt_m0_r1_cfg),
      .o_ca_dqs_tx_rt_m1_r0_cfg        (dq_dqs_tx_rt_m1_r0_cfg),
      .o_ca_dqs_tx_rt_m1_r1_cfg        (dq_dqs_tx_rt_m1_r1_cfg),
      .o_ca_dqs_tx_sdr_m0_r0_cfg_0     (dq_dqs_tx_sdr_m0_r0_cfg_0),
      .o_ca_dqs_tx_sdr_m0_r1_cfg_0     (dq_dqs_tx_sdr_m0_r1_cfg_0),
      .o_ca_dqs_tx_sdr_m1_r0_cfg_0     (dq_dqs_tx_sdr_m1_r0_cfg_0),
      .o_ca_dqs_tx_sdr_m1_r1_cfg_0     (dq_dqs_tx_sdr_m1_r1_cfg_0),
      .o_ca_dqs_tx_sdr_x_sel_m0_r0_cfg_0  (dq_dqs_tx_sdr_x_sel_m0_r0_cfg_0),
      .o_ca_dqs_tx_sdr_x_sel_m0_r1_cfg_0  (dq_dqs_tx_sdr_x_sel_m0_r1_cfg_0),
      .o_ca_dqs_tx_sdr_x_sel_m1_r0_cfg_0  (dq_dqs_tx_sdr_x_sel_m1_r0_cfg_0),
      .o_ca_dqs_tx_sdr_x_sel_m1_r1_cfg_0  (dq_dqs_tx_sdr_x_sel_m1_r1_cfg_0),
      .o_ca_dqs_tx_sdr_fc_dly_m0_r0_cfg_0 (dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_0),
      .o_ca_dqs_tx_sdr_fc_dly_m0_r1_cfg_0 (dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_0),
      .o_ca_dqs_tx_sdr_fc_dly_m1_r0_cfg_0 (dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_0),
      .o_ca_dqs_tx_sdr_fc_dly_m1_r1_cfg_0 (dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_0),
      .o_ca_dqs_tx_ddr_m0_r0_cfg_0     (dq_dqs_tx_ddr_m0_r0_cfg_0),
      .o_ca_dqs_tx_ddr_m0_r1_cfg_0     (dq_dqs_tx_ddr_m0_r1_cfg_0),
      .o_ca_dqs_tx_ddr_m1_r0_cfg_0     (dq_dqs_tx_ddr_m1_r0_cfg_0),
      .o_ca_dqs_tx_ddr_m1_r1_cfg_0     (dq_dqs_tx_ddr_m1_r1_cfg_0),
      .o_ca_dqs_tx_ddr_x_sel_m0_r0_cfg_0 (dq_dqs_tx_ddr_x_sel_m0_r0_cfg_0),
      .o_ca_dqs_tx_ddr_x_sel_m0_r1_cfg_0 (dq_dqs_tx_ddr_x_sel_m0_r1_cfg_0),
      .o_ca_dqs_tx_ddr_x_sel_m1_r0_cfg_0 (dq_dqs_tx_ddr_x_sel_m1_r0_cfg_0),
      .o_ca_dqs_tx_ddr_x_sel_m1_r1_cfg_0 (dq_dqs_tx_ddr_x_sel_m1_r1_cfg_0),
      .o_ca_dqs_tx_qdr_m0_r0_cfg_0     (dq_dqs_tx_qdr_m0_r0_cfg_0),
      .o_ca_dqs_tx_qdr_m0_r1_cfg_0     (dq_dqs_tx_qdr_m0_r1_cfg_0),
      .o_ca_dqs_tx_qdr_m1_r0_cfg_0     (dq_dqs_tx_qdr_m1_r0_cfg_0),
      .o_ca_dqs_tx_qdr_m1_r1_cfg_0     (dq_dqs_tx_qdr_m1_r1_cfg_0),
      .o_ca_dqs_tx_qdr_x_sel_m0_r0_cfg_0 (dq_dqs_tx_qdr_x_sel_m0_r0_cfg_0),
      .o_ca_dqs_tx_qdr_x_sel_m0_r1_cfg_0 (dq_dqs_tx_qdr_x_sel_m0_r1_cfg_0),
      .o_ca_dqs_tx_qdr_x_sel_m1_r0_cfg_0 (dq_dqs_tx_qdr_x_sel_m1_r0_cfg_0),
      .o_ca_dqs_tx_qdr_x_sel_m1_r1_cfg_0 (dq_dqs_tx_qdr_x_sel_m1_r1_cfg_0),
      .o_ca_dqs_tx_lpde_m0_r0_cfg_0    (dq_dqs_tx_lpde_m0_r0_cfg_0),
      .o_ca_dqs_tx_lpde_m0_r1_cfg_0    (dq_dqs_tx_lpde_m0_r1_cfg_0),
      .o_ca_dqs_tx_lpde_m1_r0_cfg_0    (dq_dqs_tx_lpde_m1_r0_cfg_0),
      .o_ca_dqs_tx_lpde_m1_r1_cfg_0    (dq_dqs_tx_lpde_m1_r1_cfg_0),
   //`for (i=0; i<`DDR_NUM_TXRX_CK_SLICES; i++)
   //   .o_ca_dqs_tx_io_m0_r0_cfg_`i     (dq_dqs_tx_io_m0_r0_cfg_`i),
   //`endfor
   //`for (i=0; i<`DDR_NUM_TXRX_CK_SLICES; i++)
   //   .o_ca_dqs_tx_io_m0_r1_cfg_`i     (dq_dqs_tx_io_m0_r1_cfg_`i),
   //`endfor
   //`for (i=0; i<`DDR_NUM_TXRX_CK_SLICES; i++)
   //   .o_ca_dqs_tx_io_m1_r0_cfg_`i     (dq_dqs_tx_io_m1_r0_cfg_`i),
   //`endfor
   //`for (i=0; i<`DDR_NUM_TXRX_CK_SLICES; i++)
   //   .o_ca_dqs_tx_io_m1_r1_cfg_`i     (dq_dqs_tx_io_m1_r1_cfg_`i),
   //`endfor
      .o_ca_dqs_tx_io_m0_cfg_0        (dq_dqs_tx_io_m0_cfg_0),
      .o_ca_dqs_tx_io_m1_cfg_0        (dq_dqs_tx_io_m1_cfg_0),
      .o_ca_dqs_tx_io_cmn_m0_r0_cfg    (dq_dqs_tx_io_cmn_m0_r0_cfg),
      .o_ca_dqs_tx_io_cmn_m0_r1_cfg    (dq_dqs_tx_io_cmn_m0_r1_cfg),
      .o_ca_dqs_tx_io_cmn_m1_r0_cfg    (dq_dqs_tx_io_cmn_m1_r0_cfg),
      .o_ca_dqs_tx_io_cmn_m1_r1_cfg    (dq_dqs_tx_io_cmn_m1_r1_cfg)

   );

   // ---------------------------------------------------------
   // TOP
   // ---------------------------------------------------------

   logic wcs;
   logic rcs;

   ddr_mux u_wcs_mux (.i_sel(dq_top_cfg[`DDR_CA_TOP_CFG_WCS_SW_OVR_FIELD]), .i_a(i_wcs), .i_b(dq_top_cfg[`DDR_CA_TOP_CFG_WCS_SW_OVR_VAL_FIELD]), .o_z(wcs));
   ddr_mux u_rcs_mux (.i_sel(dq_top_cfg[`DDR_CA_TOP_CFG_RCS_SW_OVR_FIELD]), .i_a(i_rcs), .i_b(dq_top_cfg[`DDR_CA_TOP_CFG_RCS_SW_OVR_VAL_FIELD]), .o_z(rcs));

   logic msr;
   assign msr = i_msr;

   assign o_dq_fifo_clr      = dq_top_cfg[`DDR_CA_TOP_CFG_FIFO_CLR_FIELD];
   assign o_dq_training_mode = dq_top_cfg[`DDR_CA_TOP_CFG_TRAINING_MODE_FIELD];

   assign dq_top_sta[`DDR_CA_TOP_STA_WCS_FIELD] = wcs;
   assign dq_top_sta[`DDR_CA_TOP_STA_RCS_FIELD] = rcs;

   //---------------------------------------------------------------------------------
   // PI Decode and Disable for Byte Sync
   //---------------------------------------------------------------------------------

   logic [P0WIDTH-1:0] dqs_ren_pi_cfg, dqs_ren_pi_cfg_;
   logic [P0WIDTH-1:0] dqs_rcs_pi_cfg, dqs_rcs_pi_cfg_;
   logic [P0WIDTH-1:0] dqs_rdqs_pi_0_cfg, dqs_rdqs_pi_0_cfg_;
   logic [P0WIDTH-1:0] dqs_rdqs_pi_1_cfg, dqs_rdqs_pi_1_cfg_;
   logic [P0WIDTH-1:0] dqs_qdr_pi_0_cfg, dqs_qdr_pi_0_cfg_;
   logic [P0WIDTH-1:0] dq_qdr_pi_0_cfg, dq_qdr_pi_0_cfg_;
   logic [P0WIDTH-1:0] dqs_qdr_pi_1_cfg, dqs_qdr_pi_1_cfg_;
   logic [P0WIDTH-1:0] dq_qdr_pi_1_cfg, dq_qdr_pi_1_cfg_;
   logic [P0WIDTH-1:0] dqs_ddr_pi_0_cfg, dqs_ddr_pi_0_cfg_;
   logic [P0WIDTH-1:0] dq_ddr_pi_0_cfg, dq_ddr_pi_0_cfg_;
   logic [P0WIDTH-1:0] dqs_ddr_pi_1_cfg, dqs_ddr_pi_1_cfg_;
   logic [P0WIDTH-1:0] dq_ddr_pi_1_cfg, dq_ddr_pi_1_cfg_;
   logic [P0WIDTH-1:0] dqs_sdr_rt_pi_cfg, dqs_sdr_rt_pi_cfg_;
   logic [P0WIDTH-1:0] dq_sdr_rt_pi_cfg, dq_sdr_rt_pi_cfg_;
   logic [P1WIDTH-1:0] sdr_pi_cfg;
   logic [P1WIDTH-1:0] dfi_pi_cfg;

   logic [P0WIDTH-1:0] pi_en_mask;
   assign pi_en_mask = ~(({{P0WIDTH{1'd0}},~i_csp_pi_en}) << `DDR_CA_DQS_RX_REN_PI_M0_R0_CFG_EN_FIELD) ;

   assign dqs_ren_pi_cfg_    = dqs_ren_pi_cfg    & pi_en_mask;
   assign dqs_rcs_pi_cfg_    = dqs_rcs_pi_cfg    & pi_en_mask;
   assign dqs_rdqs_pi_0_cfg_ = dqs_rdqs_pi_0_cfg & pi_en_mask;
   assign dqs_rdqs_pi_1_cfg_ = dqs_rdqs_pi_1_cfg & pi_en_mask;
   assign dqs_qdr_pi_0_cfg_  = dqs_qdr_pi_0_cfg  & pi_en_mask;
   assign dq_qdr_pi_0_cfg_   = dq_qdr_pi_0_cfg   & pi_en_mask;
   assign dqs_qdr_pi_1_cfg_  = dqs_qdr_pi_1_cfg  & pi_en_mask;
   assign dq_qdr_pi_1_cfg_   = dq_qdr_pi_1_cfg   & pi_en_mask;
   assign dqs_ddr_pi_0_cfg_  = dqs_ddr_pi_0_cfg  & pi_en_mask;
   assign dq_ddr_pi_0_cfg_   = dq_ddr_pi_0_cfg   & pi_en_mask;
   assign dqs_ddr_pi_1_cfg_  = dqs_ddr_pi_1_cfg  & pi_en_mask;
   assign dq_ddr_pi_1_cfg_   = dq_ddr_pi_1_cfg   & pi_en_mask;
   assign dqs_sdr_rt_pi_cfg_ = dqs_sdr_rt_pi_cfg & pi_en_mask;
   assign dq_sdr_rt_pi_cfg_  = dq_sdr_rt_pi_cfg  & pi_en_mask;

   assign o_dqs_ren_pi_cfg[`DDR_ANA_PI_ENC_RANGE]    = dqs_ren_pi_cfg_;
   assign o_dqs_rcs_pi_cfg[`DDR_ANA_PI_ENC_RANGE]    = dqs_rcs_pi_cfg_;
   assign o_dqs_rdqs_pi_0_cfg[`DDR_ANA_PI_ENC_RANGE] = dqs_rdqs_pi_0_cfg_;
   assign o_dqs_rdqs_pi_1_cfg[`DDR_ANA_PI_ENC_RANGE] = dqs_rdqs_pi_1_cfg_;
   assign o_dqs_qdr_pi_0_cfg[`DDR_ANA_PI_ENC_RANGE]  = dqs_qdr_pi_0_cfg_;
   assign o_dqs_qdr_pi_1_cfg[`DDR_ANA_PI_ENC_RANGE]  = dqs_qdr_pi_1_cfg_;
   assign o_dqs_ddr_pi_0_cfg[`DDR_ANA_PI_ENC_RANGE]  = dqs_ddr_pi_0_cfg_;
   assign o_dqs_ddr_pi_1_cfg[`DDR_ANA_PI_ENC_RANGE]  = dqs_ddr_pi_1_cfg_;
   assign o_dqs_sdr_rt_pi_cfg[`DDR_ANA_PI_ENC_RANGE] = dqs_sdr_rt_pi_cfg_;

   assign o_dq_qdr_pi_0_cfg[`DDR_ANA_PI_ENC_RANGE]   = dq_qdr_pi_0_cfg_;
   assign o_dq_qdr_pi_1_cfg[`DDR_ANA_PI_ENC_RANGE]   = dq_qdr_pi_1_cfg_;
   assign o_dq_ddr_pi_0_cfg[`DDR_ANA_PI_ENC_RANGE]   = dq_ddr_pi_0_cfg_;
   assign o_dq_ddr_pi_1_cfg[`DDR_ANA_PI_ENC_RANGE]   = dq_ddr_pi_1_cfg_;
   assign o_dq_sdr_rt_pi_cfg[`DDR_ANA_PI_ENC_RANGE]  = dq_sdr_rt_pi_cfg_;
   assign o_sdr_pi_cfg[`DDR_ANA_PI_MATCH_RANGE]      = sdr_pi_cfg ;
   assign o_dfi_pi_cfg[`DDR_ANA_PI_MATCH_RANGE]      = dfi_pi_cfg ;

`ifdef DDR_PI_CSR_DEC
   `ifdef DDR_REN_PI_SMALL
   ddr_pi_b2t_dec_small u_dqs_ren_pi_dec (.i_code_bin(dqs_ren_pi_cfg_[`DDR_ANA_PI_SMALL_CODE_RANGE]), .o_code_therm(o_dqs_ren_pi_cfg[`DDR_ANA_PI_SMALL_THERM_RANGE]), .o_quad(o_dqs_ren_pi_cfg[`DDR_ANA_PI_SMALL_QUAD_RANGE]));
   `else
   ddr_pi_b2t_dec       u_dqs_ren_pi_dec (.i_code_bin(dqs_ren_pi_cfg_[`DDR_ANA_PI_CODE_RANGE]), .o_code_therm(o_dqs_ren_pi_cfg[`DDR_ANA_PI_THERM_RANGE]), .o_quad(o_dqs_ren_pi_cfg[`DDR_ANA_PI_QUAD_RANGE]));
   `endif

   `ifdef DDR_RCS_PI_SMALL
   ddr_pi_b2t_dec_small u_dqs_rcs_pi_dec (.i_code_bin(dqs_rcs_pi_cfg_[`DDR_ANA_PI_SMALL_CODE_RANGE]), .o_code_therm(o_dqs_rcs_pi_cfg[`DDR_ANA_PI_SMALL_THERM_RANGE]), .o_quad(o_dqs_rcs_pi_cfg[`DDR_ANA_PI_SMALL_QUAD_RANGE]));
   `else
   ddr_pi_b2t_dec       u_dqs_rcs_pi_dec (.i_code_bin(dqs_rcs_pi_cfg_[`DDR_ANA_PI_CODE_RANGE]), .o_code_therm(o_dqs_rcs_pi_cfg[`DDR_ANA_PI_THERM_RANGE]), .o_quad(o_dqs_rcs_pi_cfg[`DDR_ANA_PI_QUAD_RANGE]));
   `endif

   ddr_pi_b2t_dec u_dqs_rdqs_pi_0_dec  (.i_code_bin(dqs_rdqs_pi_0_cfg_[`DDR_ANA_PI_CODE_RANGE]), .o_code_therm(o_dqs_rdqs_pi_0_cfg[`DDR_ANA_PI_THERM_RANGE]), .o_quad(o_dqs_rdqs_pi_0_cfg[`DDR_ANA_PI_QUAD_RANGE]));
   ddr_pi_b2t_dec u_dqs_rdqs_pi_1_dec  (.i_code_bin(dqs_rdqs_pi_1_cfg_[`DDR_ANA_PI_CODE_RANGE]), .o_code_therm(o_dqs_rdqs_pi_1_cfg[`DDR_ANA_PI_THERM_RANGE]), .o_quad(o_dqs_rdqs_pi_1_cfg[`DDR_ANA_PI_QUAD_RANGE]));
   ddr_pi_b2t_dec u_dqs_qdr_pi_0_dec   (.i_code_bin( dqs_qdr_pi_0_cfg_[`DDR_ANA_PI_CODE_RANGE]), .o_code_therm( o_dqs_qdr_pi_0_cfg[`DDR_ANA_PI_THERM_RANGE]), .o_quad( o_dqs_qdr_pi_0_cfg[`DDR_ANA_PI_QUAD_RANGE]));
   ddr_pi_b2t_dec u_dqs_qdr_pi_1_dec   (.i_code_bin( dqs_qdr_pi_1_cfg_[`DDR_ANA_PI_CODE_RANGE]), .o_code_therm( o_dqs_qdr_pi_1_cfg[`DDR_ANA_PI_THERM_RANGE]), .o_quad( o_dqs_qdr_pi_1_cfg[`DDR_ANA_PI_QUAD_RANGE]));
   ddr_pi_b2t_dec u_dqs_ddr_pi_0_dec   (.i_code_bin( dqs_ddr_pi_0_cfg_[`DDR_ANA_PI_CODE_RANGE]), .o_code_therm( o_dqs_ddr_pi_0_cfg[`DDR_ANA_PI_THERM_RANGE]), .o_quad( o_dqs_ddr_pi_0_cfg[`DDR_ANA_PI_QUAD_RANGE]));
   ddr_pi_b2t_dec u_dqs_ddr_pi_1_dec   (.i_code_bin( dqs_ddr_pi_1_cfg_[`DDR_ANA_PI_CODE_RANGE]), .o_code_therm( o_dqs_ddr_pi_1_cfg[`DDR_ANA_PI_THERM_RANGE]), .o_quad( o_dqs_ddr_pi_1_cfg[`DDR_ANA_PI_QUAD_RANGE]));
   ddr_pi_b2t_dec u_dqs_dqs_sdr_rt_dec (.i_code_bin(dqs_sdr_rt_pi_cfg_[`DDR_ANA_PI_CODE_RANGE]), .o_code_therm(o_dqs_sdr_rt_pi_cfg[`DDR_ANA_PI_THERM_RANGE]), .o_quad(o_dqs_sdr_rt_pi_cfg[`DDR_ANA_PI_QUAD_RANGE]));

   ddr_pi_b2t_dec u_dq_qdr_pi_0_dec    (.i_code_bin(  dq_qdr_pi_0_cfg_[`DDR_ANA_PI_CODE_RANGE]), .o_code_therm(  o_dq_qdr_pi_0_cfg[`DDR_ANA_PI_THERM_RANGE]), .o_quad(  o_dq_qdr_pi_0_cfg[`DDR_ANA_PI_QUAD_RANGE]));
   ddr_pi_b2t_dec u_dq_qdr_pi_1_dec    (.i_code_bin(  dq_qdr_pi_1_cfg_[`DDR_ANA_PI_CODE_RANGE]), .o_code_therm(  o_dq_qdr_pi_1_cfg[`DDR_ANA_PI_THERM_RANGE]), .o_quad(  o_dq_qdr_pi_1_cfg[`DDR_ANA_PI_QUAD_RANGE]));
   ddr_pi_b2t_dec u_dq_ddr_pi_0_dec    (.i_code_bin(  dq_ddr_pi_0_cfg_[`DDR_ANA_PI_CODE_RANGE]), .o_code_therm(  o_dq_ddr_pi_0_cfg[`DDR_ANA_PI_THERM_RANGE]), .o_quad(  o_dq_ddr_pi_0_cfg[`DDR_ANA_PI_QUAD_RANGE]));
   ddr_pi_b2t_dec u_dq_ddr_pi_1_dec    (.i_code_bin(  dq_ddr_pi_1_cfg_[`DDR_ANA_PI_CODE_RANGE]), .o_code_therm(  o_dq_ddr_pi_1_cfg[`DDR_ANA_PI_THERM_RANGE]), .o_quad(  o_dq_ddr_pi_1_cfg[`DDR_ANA_PI_QUAD_RANGE]));
   ddr_pi_b2t_dec u_dq_dq_sdr_rt_dec   (.i_code_bin( dq_sdr_rt_pi_cfg_[`DDR_ANA_PI_CODE_RANGE]), .o_code_therm( o_dq_sdr_rt_pi_cfg[`DDR_ANA_PI_THERM_RANGE]), .o_quad( o_dq_sdr_rt_pi_cfg[`DDR_ANA_PI_QUAD_RANGE]));
`else
   assign o_dqs_ren_pi_cfg[`DDR_ANA_PI_SMALL_DEC_RANGE] = '0;
   assign o_dqs_rcs_pi_cfg[`DDR_ANA_PI_SMALL_DEC_RANGE] = '0;

   assign o_dqs_rdqs_pi_0_cfg[`DDR_ANA_PI_DEC_RANGE] = '0;
   assign o_dqs_rdqs_pi_1_cfg[`DDR_ANA_PI_DEC_RANGE] = '0;
   assign o_dqs_qdr_pi_0_cfg[`DDR_ANA_PI_DEC_RANGE]  = '0;
   assign o_dqs_qdr_pi_1_cfg[`DDR_ANA_PI_DEC_RANGE]  = '0;
   assign o_dqs_ddr_pi_0_cfg[`DDR_ANA_PI_DEC_RANGE]  = '0;
   assign o_dqs_ddr_pi_1_cfg[`DDR_ANA_PI_DEC_RANGE]  = '0;
   assign o_dqs_sdr_rt_pi_cfg[`DDR_ANA_PI_DEC_RANGE] = '0;

   assign o_dq_qdr_pi_0_cfg[`DDR_ANA_PI_DEC_RANGE]   = '0;
   assign o_dq_qdr_pi_1_cfg[`DDR_ANA_PI_DEC_RANGE]   = '0;
   assign o_dq_ddr_pi_0_cfg[`DDR_ANA_PI_DEC_RANGE]   = '0;
   assign o_dq_ddr_pi_1_cfg[`DDR_ANA_PI_DEC_RANGE]   = '0;
   assign o_dq_sdr_rt_pi_cfg[`DDR_ANA_PI_DEC_RANGE]  = '0;
`endif

   // ---------------------------------------------------------
   // DQ RX
   // ---------------------------------------------------------

   assign dq_dq_rx_bscan_sta[`DDR_CA_DQ_RX_BSCAN_STA_VAL_FIELD] = i_dq_ingress_bscan;
   assign dq_rgb_mode = msr ?
         cast_dgb_t(dq_dq_rx_m1_cfg[`DDR_CA_DQ_RX_M1_CFG_RGB_MODE_FIELD]):
         cast_dgb_t(dq_dq_rx_m0_cfg[`DDR_CA_DQ_RX_M0_CFG_RGB_MODE_FIELD]);
   assign o_dq_fgb_mode = msr ?
         cast_fgb_t(dq_dq_rx_m1_cfg[`DDR_CA_DQ_RX_M1_CFG_FGB_MODE_FIELD]):
         cast_fgb_t(dq_dq_rx_m0_cfg[`DDR_CA_DQ_RX_M0_CFG_FGB_MODE_FIELD]);

   always_comb begin
      case(dq_rgb_mode)
        DGB_8TO1_HF : o_dq_rgb_mode = {{(DEC_DGBWIDTH-1){1'b0}},1'b1} << `DGB_8TO1_HF_IDX ;
        DGB_8TO1_LF : o_dq_rgb_mode = {{(DEC_DGBWIDTH-1){1'b0}},1'b1} << `DGB_8TO1_LF_IDX ;
        DGB_4TO1_IR : o_dq_rgb_mode = {{(DEC_DGBWIDTH-1){1'b0}},1'b1} << `DGB_4TO1_IR_IDX ;
        DGB_4TO1_HF : o_dq_rgb_mode = {{(DEC_DGBWIDTH-1){1'b0}},1'b1} << `DGB_4TO1_HF_IDX ;
        DGB_4TO1_LF : o_dq_rgb_mode = {{(DEC_DGBWIDTH-1){1'b0}},1'b1} << `DGB_4TO1_LF_IDX ;
        DGB_2TO1_IR : o_dq_rgb_mode = {{(DEC_DGBWIDTH-1){1'b0}},1'b1} << `DGB_2TO1_IR_IDX ;
        DGB_2TO1_HF : o_dq_rgb_mode = {{(DEC_DGBWIDTH-1){1'b0}},1'b1} << `DGB_2TO1_HF_IDX ;
        DGB_1TO1_HF : o_dq_rgb_mode = {{(DEC_DGBWIDTH-1){1'b0}},1'b1} << `DGB_1TO1_HF_IDX ;
        default     : o_dq_rgb_mode = {{(DEC_DGBWIDTH-1){1'b0}},1'b1} << `DGB_1TO1_HF_IDX ;
      endcase
   end

   assign o_dq_pad_rx_cfg  = msr ? rcs ?
      {
         dq_dq_rx_io_m1_r1_cfg_10[`DDR_CA_DQ_RX_IO_M1_R1_CFG_10_RANGE],
         dq_dq_rx_io_m1_r1_cfg_9[`DDR_CA_DQ_RX_IO_M1_R1_CFG_9_RANGE],
         dq_dq_rx_io_m1_r1_cfg_8[`DDR_CA_DQ_RX_IO_M1_R1_CFG_8_RANGE],
         dq_dq_rx_io_m1_r1_cfg_7[`DDR_CA_DQ_RX_IO_M1_R1_CFG_7_RANGE],
         dq_dq_rx_io_m1_r1_cfg_6[`DDR_CA_DQ_RX_IO_M1_R1_CFG_6_RANGE],
         dq_dq_rx_io_m1_r1_cfg_5[`DDR_CA_DQ_RX_IO_M1_R1_CFG_5_RANGE],
         dq_dq_rx_io_m1_r1_cfg_4[`DDR_CA_DQ_RX_IO_M1_R1_CFG_4_RANGE],
         dq_dq_rx_io_m1_r1_cfg_3[`DDR_CA_DQ_RX_IO_M1_R1_CFG_3_RANGE],
         dq_dq_rx_io_m1_r1_cfg_2[`DDR_CA_DQ_RX_IO_M1_R1_CFG_2_RANGE],
         dq_dq_rx_io_m1_r1_cfg_1[`DDR_CA_DQ_RX_IO_M1_R1_CFG_1_RANGE],
         dq_dq_rx_io_m1_r1_cfg_0[`DDR_CA_DQ_RX_IO_M1_R1_CFG_0_RANGE]
      }:
      {
         dq_dq_rx_io_m1_r0_cfg_10[`DDR_CA_DQ_RX_IO_M1_R0_CFG_10_RANGE],
         dq_dq_rx_io_m1_r0_cfg_9[`DDR_CA_DQ_RX_IO_M1_R0_CFG_9_RANGE],
         dq_dq_rx_io_m1_r0_cfg_8[`DDR_CA_DQ_RX_IO_M1_R0_CFG_8_RANGE],
         dq_dq_rx_io_m1_r0_cfg_7[`DDR_CA_DQ_RX_IO_M1_R0_CFG_7_RANGE],
         dq_dq_rx_io_m1_r0_cfg_6[`DDR_CA_DQ_RX_IO_M1_R0_CFG_6_RANGE],
         dq_dq_rx_io_m1_r0_cfg_5[`DDR_CA_DQ_RX_IO_M1_R0_CFG_5_RANGE],
         dq_dq_rx_io_m1_r0_cfg_4[`DDR_CA_DQ_RX_IO_M1_R0_CFG_4_RANGE],
         dq_dq_rx_io_m1_r0_cfg_3[`DDR_CA_DQ_RX_IO_M1_R0_CFG_3_RANGE],
         dq_dq_rx_io_m1_r0_cfg_2[`DDR_CA_DQ_RX_IO_M1_R0_CFG_2_RANGE],
         dq_dq_rx_io_m1_r0_cfg_1[`DDR_CA_DQ_RX_IO_M1_R0_CFG_1_RANGE],
         dq_dq_rx_io_m1_r0_cfg_0[`DDR_CA_DQ_RX_IO_M1_R0_CFG_0_RANGE]
       } : rcs ?
      {
         dq_dq_rx_io_m0_r1_cfg_10[`DDR_CA_DQ_RX_IO_M0_R1_CFG_10_RANGE],
         dq_dq_rx_io_m0_r1_cfg_9[`DDR_CA_DQ_RX_IO_M0_R1_CFG_9_RANGE],
         dq_dq_rx_io_m0_r1_cfg_8[`DDR_CA_DQ_RX_IO_M0_R1_CFG_8_RANGE],
         dq_dq_rx_io_m0_r1_cfg_7[`DDR_CA_DQ_RX_IO_M0_R1_CFG_7_RANGE],
         dq_dq_rx_io_m0_r1_cfg_6[`DDR_CA_DQ_RX_IO_M0_R1_CFG_6_RANGE],
         dq_dq_rx_io_m0_r1_cfg_5[`DDR_CA_DQ_RX_IO_M0_R1_CFG_5_RANGE],
         dq_dq_rx_io_m0_r1_cfg_4[`DDR_CA_DQ_RX_IO_M0_R1_CFG_4_RANGE],
         dq_dq_rx_io_m0_r1_cfg_3[`DDR_CA_DQ_RX_IO_M0_R1_CFG_3_RANGE],
         dq_dq_rx_io_m0_r1_cfg_2[`DDR_CA_DQ_RX_IO_M0_R1_CFG_2_RANGE],
         dq_dq_rx_io_m0_r1_cfg_1[`DDR_CA_DQ_RX_IO_M0_R1_CFG_1_RANGE],
         dq_dq_rx_io_m0_r1_cfg_0[`DDR_CA_DQ_RX_IO_M0_R1_CFG_0_RANGE]
      }:
      {
         dq_dq_rx_io_m0_r0_cfg_10[`DDR_CA_DQ_RX_IO_M0_R0_CFG_10_RANGE],
         dq_dq_rx_io_m0_r0_cfg_9[`DDR_CA_DQ_RX_IO_M0_R0_CFG_9_RANGE],
         dq_dq_rx_io_m0_r0_cfg_8[`DDR_CA_DQ_RX_IO_M0_R0_CFG_8_RANGE],
         dq_dq_rx_io_m0_r0_cfg_7[`DDR_CA_DQ_RX_IO_M0_R0_CFG_7_RANGE],
         dq_dq_rx_io_m0_r0_cfg_6[`DDR_CA_DQ_RX_IO_M0_R0_CFG_6_RANGE],
         dq_dq_rx_io_m0_r0_cfg_5[`DDR_CA_DQ_RX_IO_M0_R0_CFG_5_RANGE],
         dq_dq_rx_io_m0_r0_cfg_4[`DDR_CA_DQ_RX_IO_M0_R0_CFG_4_RANGE],
         dq_dq_rx_io_m0_r0_cfg_3[`DDR_CA_DQ_RX_IO_M0_R0_CFG_3_RANGE],
         dq_dq_rx_io_m0_r0_cfg_2[`DDR_CA_DQ_RX_IO_M0_R0_CFG_2_RANGE],
         dq_dq_rx_io_m0_r0_cfg_1[`DDR_CA_DQ_RX_IO_M0_R0_CFG_1_RANGE],
         dq_dq_rx_io_m0_r0_cfg_0[`DDR_CA_DQ_RX_IO_M0_R0_CFG_0_RANGE]
      };
   assign o_dq_sa_cfg = msr ? rcs ?
      {
         dq_dq_rx_sa_m1_r1_cfg_10[`DDR_CA_DQ_RX_SA_M1_R1_CFG_10_RANGE],
         dq_dq_rx_sa_m1_r1_cfg_9[`DDR_CA_DQ_RX_SA_M1_R1_CFG_9_RANGE],
         dq_dq_rx_sa_m1_r1_cfg_8[`DDR_CA_DQ_RX_SA_M1_R1_CFG_8_RANGE],
         dq_dq_rx_sa_m1_r1_cfg_7[`DDR_CA_DQ_RX_SA_M1_R1_CFG_7_RANGE],
         dq_dq_rx_sa_m1_r1_cfg_6[`DDR_CA_DQ_RX_SA_M1_R1_CFG_6_RANGE],
         dq_dq_rx_sa_m1_r1_cfg_5[`DDR_CA_DQ_RX_SA_M1_R1_CFG_5_RANGE],
         dq_dq_rx_sa_m1_r1_cfg_4[`DDR_CA_DQ_RX_SA_M1_R1_CFG_4_RANGE],
         dq_dq_rx_sa_m1_r1_cfg_3[`DDR_CA_DQ_RX_SA_M1_R1_CFG_3_RANGE],
         dq_dq_rx_sa_m1_r1_cfg_2[`DDR_CA_DQ_RX_SA_M1_R1_CFG_2_RANGE],
         dq_dq_rx_sa_m1_r1_cfg_1[`DDR_CA_DQ_RX_SA_M1_R1_CFG_1_RANGE],
         dq_dq_rx_sa_m1_r1_cfg_0[`DDR_CA_DQ_RX_SA_M1_R1_CFG_0_RANGE]
      }:
      {
         dq_dq_rx_sa_m1_r0_cfg_10[`DDR_CA_DQ_RX_SA_M1_R0_CFG_10_RANGE],
         dq_dq_rx_sa_m1_r0_cfg_9[`DDR_CA_DQ_RX_SA_M1_R0_CFG_9_RANGE],
         dq_dq_rx_sa_m1_r0_cfg_8[`DDR_CA_DQ_RX_SA_M1_R0_CFG_8_RANGE],
         dq_dq_rx_sa_m1_r0_cfg_7[`DDR_CA_DQ_RX_SA_M1_R0_CFG_7_RANGE],
         dq_dq_rx_sa_m1_r0_cfg_6[`DDR_CA_DQ_RX_SA_M1_R0_CFG_6_RANGE],
         dq_dq_rx_sa_m1_r0_cfg_5[`DDR_CA_DQ_RX_SA_M1_R0_CFG_5_RANGE],
         dq_dq_rx_sa_m1_r0_cfg_4[`DDR_CA_DQ_RX_SA_M1_R0_CFG_4_RANGE],
         dq_dq_rx_sa_m1_r0_cfg_3[`DDR_CA_DQ_RX_SA_M1_R0_CFG_3_RANGE],
         dq_dq_rx_sa_m1_r0_cfg_2[`DDR_CA_DQ_RX_SA_M1_R0_CFG_2_RANGE],
         dq_dq_rx_sa_m1_r0_cfg_1[`DDR_CA_DQ_RX_SA_M1_R0_CFG_1_RANGE],
         dq_dq_rx_sa_m1_r0_cfg_0[`DDR_CA_DQ_RX_SA_M1_R0_CFG_0_RANGE]
       } : rcs ?
      {
         dq_dq_rx_sa_m0_r1_cfg_10[`DDR_CA_DQ_RX_SA_M0_R1_CFG_10_RANGE],
         dq_dq_rx_sa_m0_r1_cfg_9[`DDR_CA_DQ_RX_SA_M0_R1_CFG_9_RANGE],
         dq_dq_rx_sa_m0_r1_cfg_8[`DDR_CA_DQ_RX_SA_M0_R1_CFG_8_RANGE],
         dq_dq_rx_sa_m0_r1_cfg_7[`DDR_CA_DQ_RX_SA_M0_R1_CFG_7_RANGE],
         dq_dq_rx_sa_m0_r1_cfg_6[`DDR_CA_DQ_RX_SA_M0_R1_CFG_6_RANGE],
         dq_dq_rx_sa_m0_r1_cfg_5[`DDR_CA_DQ_RX_SA_M0_R1_CFG_5_RANGE],
         dq_dq_rx_sa_m0_r1_cfg_4[`DDR_CA_DQ_RX_SA_M0_R1_CFG_4_RANGE],
         dq_dq_rx_sa_m0_r1_cfg_3[`DDR_CA_DQ_RX_SA_M0_R1_CFG_3_RANGE],
         dq_dq_rx_sa_m0_r1_cfg_2[`DDR_CA_DQ_RX_SA_M0_R1_CFG_2_RANGE],
         dq_dq_rx_sa_m0_r1_cfg_1[`DDR_CA_DQ_RX_SA_M0_R1_CFG_1_RANGE],
         dq_dq_rx_sa_m0_r1_cfg_0[`DDR_CA_DQ_RX_SA_M0_R1_CFG_0_RANGE]
      }:
      {
         dq_dq_rx_sa_m0_r0_cfg_10[`DDR_CA_DQ_RX_SA_M0_R0_CFG_10_RANGE],
         dq_dq_rx_sa_m0_r0_cfg_9[`DDR_CA_DQ_RX_SA_M0_R0_CFG_9_RANGE],
         dq_dq_rx_sa_m0_r0_cfg_8[`DDR_CA_DQ_RX_SA_M0_R0_CFG_8_RANGE],
         dq_dq_rx_sa_m0_r0_cfg_7[`DDR_CA_DQ_RX_SA_M0_R0_CFG_7_RANGE],
         dq_dq_rx_sa_m0_r0_cfg_6[`DDR_CA_DQ_RX_SA_M0_R0_CFG_6_RANGE],
         dq_dq_rx_sa_m0_r0_cfg_5[`DDR_CA_DQ_RX_SA_M0_R0_CFG_5_RANGE],
         dq_dq_rx_sa_m0_r0_cfg_4[`DDR_CA_DQ_RX_SA_M0_R0_CFG_4_RANGE],
         dq_dq_rx_sa_m0_r0_cfg_3[`DDR_CA_DQ_RX_SA_M0_R0_CFG_3_RANGE],
         dq_dq_rx_sa_m0_r0_cfg_2[`DDR_CA_DQ_RX_SA_M0_R0_CFG_2_RANGE],
         dq_dq_rx_sa_m0_r0_cfg_1[`DDR_CA_DQ_RX_SA_M0_R0_CFG_1_RANGE],
         dq_dq_rx_sa_m0_r0_cfg_0[`DDR_CA_DQ_RX_SA_M0_R0_CFG_0_RANGE]
      };
   assign o_dq_sa_dly_cfg = msr ? rcs ?
      {
         dq_dq_rx_sa_dly_m1_r1_cfg_10[`DDR_CA_DQ_RX_SA_DLY_M1_R1_CFG_10_RANGE],
         dq_dq_rx_sa_dly_m1_r1_cfg_9[`DDR_CA_DQ_RX_SA_DLY_M1_R1_CFG_9_RANGE],
         dq_dq_rx_sa_dly_m1_r1_cfg_8[`DDR_CA_DQ_RX_SA_DLY_M1_R1_CFG_8_RANGE],
         dq_dq_rx_sa_dly_m1_r1_cfg_7[`DDR_CA_DQ_RX_SA_DLY_M1_R1_CFG_7_RANGE],
         dq_dq_rx_sa_dly_m1_r1_cfg_6[`DDR_CA_DQ_RX_SA_DLY_M1_R1_CFG_6_RANGE],
         dq_dq_rx_sa_dly_m1_r1_cfg_5[`DDR_CA_DQ_RX_SA_DLY_M1_R1_CFG_5_RANGE],
         dq_dq_rx_sa_dly_m1_r1_cfg_4[`DDR_CA_DQ_RX_SA_DLY_M1_R1_CFG_4_RANGE],
         dq_dq_rx_sa_dly_m1_r1_cfg_3[`DDR_CA_DQ_RX_SA_DLY_M1_R1_CFG_3_RANGE],
         dq_dq_rx_sa_dly_m1_r1_cfg_2[`DDR_CA_DQ_RX_SA_DLY_M1_R1_CFG_2_RANGE],
         dq_dq_rx_sa_dly_m1_r1_cfg_1[`DDR_CA_DQ_RX_SA_DLY_M1_R1_CFG_1_RANGE],
         dq_dq_rx_sa_dly_m1_r1_cfg_0[`DDR_CA_DQ_RX_SA_DLY_M1_R1_CFG_0_RANGE]
      }:
      {
         dq_dq_rx_sa_dly_m1_r0_cfg_10[`DDR_CA_DQ_RX_SA_DLY_M1_R0_CFG_10_RANGE],
         dq_dq_rx_sa_dly_m1_r0_cfg_9[`DDR_CA_DQ_RX_SA_DLY_M1_R0_CFG_9_RANGE],
         dq_dq_rx_sa_dly_m1_r0_cfg_8[`DDR_CA_DQ_RX_SA_DLY_M1_R0_CFG_8_RANGE],
         dq_dq_rx_sa_dly_m1_r0_cfg_7[`DDR_CA_DQ_RX_SA_DLY_M1_R0_CFG_7_RANGE],
         dq_dq_rx_sa_dly_m1_r0_cfg_6[`DDR_CA_DQ_RX_SA_DLY_M1_R0_CFG_6_RANGE],
         dq_dq_rx_sa_dly_m1_r0_cfg_5[`DDR_CA_DQ_RX_SA_DLY_M1_R0_CFG_5_RANGE],
         dq_dq_rx_sa_dly_m1_r0_cfg_4[`DDR_CA_DQ_RX_SA_DLY_M1_R0_CFG_4_RANGE],
         dq_dq_rx_sa_dly_m1_r0_cfg_3[`DDR_CA_DQ_RX_SA_DLY_M1_R0_CFG_3_RANGE],
         dq_dq_rx_sa_dly_m1_r0_cfg_2[`DDR_CA_DQ_RX_SA_DLY_M1_R0_CFG_2_RANGE],
         dq_dq_rx_sa_dly_m1_r0_cfg_1[`DDR_CA_DQ_RX_SA_DLY_M1_R0_CFG_1_RANGE],
         dq_dq_rx_sa_dly_m1_r0_cfg_0[`DDR_CA_DQ_RX_SA_DLY_M1_R0_CFG_0_RANGE]
       } : rcs ?
      {
         dq_dq_rx_sa_dly_m0_r1_cfg_10[`DDR_CA_DQ_RX_SA_DLY_M0_R1_CFG_10_RANGE],
         dq_dq_rx_sa_dly_m0_r1_cfg_9[`DDR_CA_DQ_RX_SA_DLY_M0_R1_CFG_9_RANGE],
         dq_dq_rx_sa_dly_m0_r1_cfg_8[`DDR_CA_DQ_RX_SA_DLY_M0_R1_CFG_8_RANGE],
         dq_dq_rx_sa_dly_m0_r1_cfg_7[`DDR_CA_DQ_RX_SA_DLY_M0_R1_CFG_7_RANGE],
         dq_dq_rx_sa_dly_m0_r1_cfg_6[`DDR_CA_DQ_RX_SA_DLY_M0_R1_CFG_6_RANGE],
         dq_dq_rx_sa_dly_m0_r1_cfg_5[`DDR_CA_DQ_RX_SA_DLY_M0_R1_CFG_5_RANGE],
         dq_dq_rx_sa_dly_m0_r1_cfg_4[`DDR_CA_DQ_RX_SA_DLY_M0_R1_CFG_4_RANGE],
         dq_dq_rx_sa_dly_m0_r1_cfg_3[`DDR_CA_DQ_RX_SA_DLY_M0_R1_CFG_3_RANGE],
         dq_dq_rx_sa_dly_m0_r1_cfg_2[`DDR_CA_DQ_RX_SA_DLY_M0_R1_CFG_2_RANGE],
         dq_dq_rx_sa_dly_m0_r1_cfg_1[`DDR_CA_DQ_RX_SA_DLY_M0_R1_CFG_1_RANGE],
         dq_dq_rx_sa_dly_m0_r1_cfg_0[`DDR_CA_DQ_RX_SA_DLY_M0_R1_CFG_0_RANGE]
      }:
      {
         dq_dq_rx_sa_dly_m0_r0_cfg_10[`DDR_CA_DQ_RX_SA_DLY_M0_R0_CFG_10_RANGE],
         dq_dq_rx_sa_dly_m0_r0_cfg_9[`DDR_CA_DQ_RX_SA_DLY_M0_R0_CFG_9_RANGE],
         dq_dq_rx_sa_dly_m0_r0_cfg_8[`DDR_CA_DQ_RX_SA_DLY_M0_R0_CFG_8_RANGE],
         dq_dq_rx_sa_dly_m0_r0_cfg_7[`DDR_CA_DQ_RX_SA_DLY_M0_R0_CFG_7_RANGE],
         dq_dq_rx_sa_dly_m0_r0_cfg_6[`DDR_CA_DQ_RX_SA_DLY_M0_R0_CFG_6_RANGE],
         dq_dq_rx_sa_dly_m0_r0_cfg_5[`DDR_CA_DQ_RX_SA_DLY_M0_R0_CFG_5_RANGE],
         dq_dq_rx_sa_dly_m0_r0_cfg_4[`DDR_CA_DQ_RX_SA_DLY_M0_R0_CFG_4_RANGE],
         dq_dq_rx_sa_dly_m0_r0_cfg_3[`DDR_CA_DQ_RX_SA_DLY_M0_R0_CFG_3_RANGE],
         dq_dq_rx_sa_dly_m0_r0_cfg_2[`DDR_CA_DQ_RX_SA_DLY_M0_R0_CFG_2_RANGE],
         dq_dq_rx_sa_dly_m0_r0_cfg_1[`DDR_CA_DQ_RX_SA_DLY_M0_R0_CFG_1_RANGE],
         dq_dq_rx_sa_dly_m0_r0_cfg_0[`DDR_CA_DQ_RX_SA_DLY_M0_R0_CFG_0_RANGE]
      };

   assign dq_dq_rx_sa_sta_10[`DDR_CA_DQ_RX_SA_STA_10_RANGE] = i_dq_sa_sta[43:40];
   assign dq_dq_rx_sa_sta_9[`DDR_CA_DQ_RX_SA_STA_9_RANGE] = i_dq_sa_sta[39:36];
   assign dq_dq_rx_sa_sta_8[`DDR_CA_DQ_RX_SA_STA_8_RANGE] = i_dq_sa_sta[35:32];
   assign dq_dq_rx_sa_sta_7[`DDR_CA_DQ_RX_SA_STA_7_RANGE] = i_dq_sa_sta[31:28];
   assign dq_dq_rx_sa_sta_6[`DDR_CA_DQ_RX_SA_STA_6_RANGE] = i_dq_sa_sta[27:24];
   assign dq_dq_rx_sa_sta_5[`DDR_CA_DQ_RX_SA_STA_5_RANGE] = i_dq_sa_sta[23:20];
   assign dq_dq_rx_sa_sta_4[`DDR_CA_DQ_RX_SA_STA_4_RANGE] = i_dq_sa_sta[19:16];
   assign dq_dq_rx_sa_sta_3[`DDR_CA_DQ_RX_SA_STA_3_RANGE] = i_dq_sa_sta[15:12];
   assign dq_dq_rx_sa_sta_2[`DDR_CA_DQ_RX_SA_STA_2_RANGE] = i_dq_sa_sta[11:8];
   assign dq_dq_rx_sa_sta_1[`DDR_CA_DQ_RX_SA_STA_1_RANGE] = i_dq_sa_sta[7:4];
   assign dq_dq_rx_sa_sta_0[`DDR_CA_DQ_RX_SA_STA_0_RANGE] = i_dq_sa_sta[3:0];
   assign dq_dq_rx_io_sta[`DDR_CA_DQ_RX_IO_STA_RANGE] = i_dq_io_sta;

   // ---------------------------------------------------------
   // DQ TX
   // ---------------------------------------------------------

   assign o_dq_egress_bscan = dq_dq_tx_bscan_cfg[`DDR_CA_DQ_TX_BSCAN_CFG_VAL_FIELD];
   assign o_dq_egress_mode_ana = i_bscan_mode ? ({{(E0WIDTH-1){1'b0}},1'b1} << `DDR_ANA_EGRESS_BYPASS ) : msr ?
      {
         dq_dq_tx_egress_ana_m1_cfg_10[`DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_10_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_ana_m1_cfg_9[`DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_9_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_ana_m1_cfg_8[`DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_8_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_ana_m1_cfg_7[`DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_7_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_ana_m1_cfg_6[`DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_6_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_ana_m1_cfg_5[`DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_5_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_ana_m1_cfg_4[`DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_4_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_ana_m1_cfg_3[`DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_3_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_ana_m1_cfg_2[`DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_2_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_ana_m1_cfg_1[`DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_1_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_ana_m1_cfg_0[`DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_0_EGRESS_MODE_FIELD]
      }:
      {
         dq_dq_tx_egress_ana_m0_cfg_10[`DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_10_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_ana_m0_cfg_9[`DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_9_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_ana_m0_cfg_8[`DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_8_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_ana_m0_cfg_7[`DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_7_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_ana_m0_cfg_6[`DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_6_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_ana_m0_cfg_5[`DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_5_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_ana_m0_cfg_4[`DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_4_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_ana_m0_cfg_3[`DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_3_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_ana_m0_cfg_2[`DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_2_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_ana_m0_cfg_1[`DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_1_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_ana_m0_cfg_0[`DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_0_EGRESS_MODE_FIELD]
      };
   assign o_dq_egress_mode_dig = i_bscan_mode ? ({{(E1WIDTH-1){1'b0}},1'b1} << `DDR_DIG_EGRESS_BSCAN ) :msr ?
      {
         dq_dq_tx_egress_dig_m1_cfg_10[`DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_10_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_dig_m1_cfg_9[`DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_9_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_dig_m1_cfg_8[`DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_8_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_dig_m1_cfg_7[`DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_7_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_dig_m1_cfg_6[`DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_6_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_dig_m1_cfg_5[`DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_5_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_dig_m1_cfg_4[`DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_4_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_dig_m1_cfg_3[`DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_3_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_dig_m1_cfg_2[`DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_2_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_dig_m1_cfg_1[`DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_1_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_dig_m1_cfg_0[`DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_0_EGRESS_MODE_FIELD]
      }:
      {
         dq_dq_tx_egress_dig_m0_cfg_10[`DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_10_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_dig_m0_cfg_9[`DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_9_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_dig_m0_cfg_8[`DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_8_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_dig_m0_cfg_7[`DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_7_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_dig_m0_cfg_6[`DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_6_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_dig_m0_cfg_5[`DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_5_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_dig_m0_cfg_4[`DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_4_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_dig_m0_cfg_3[`DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_3_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_dig_m0_cfg_2[`DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_2_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_dig_m0_cfg_1[`DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_1_EGRESS_MODE_FIELD],
         dq_dq_tx_egress_dig_m0_cfg_0[`DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_0_EGRESS_MODE_FIELD]
      };
   assign dq_qdr_pi_0_cfg = msr ? wcs ?
         dq_dq_tx_qdr_pi_0_m1_r1_cfg[`DDR_CA_DQ_TX_QDR_PI_0_M1_R1_CFG_RANGE]:
         dq_dq_tx_qdr_pi_0_m1_r0_cfg[`DDR_CA_DQ_TX_QDR_PI_0_M1_R0_CFG_RANGE]: wcs ?
         dq_dq_tx_qdr_pi_0_m0_r1_cfg[`DDR_CA_DQ_TX_QDR_PI_0_M0_R1_CFG_RANGE]:
         dq_dq_tx_qdr_pi_0_m0_r0_cfg[`DDR_CA_DQ_TX_QDR_PI_0_M0_R0_CFG_RANGE];
   assign dq_qdr_pi_1_cfg = msr ? wcs ?
         dq_dq_tx_qdr_pi_1_m1_r1_cfg[`DDR_CA_DQ_TX_QDR_PI_1_M1_R1_CFG_RANGE]:
         dq_dq_tx_qdr_pi_1_m1_r0_cfg[`DDR_CA_DQ_TX_QDR_PI_1_M1_R0_CFG_RANGE]: wcs ?
         dq_dq_tx_qdr_pi_1_m0_r1_cfg[`DDR_CA_DQ_TX_QDR_PI_1_M0_R1_CFG_RANGE]:
         dq_dq_tx_qdr_pi_1_m0_r0_cfg[`DDR_CA_DQ_TX_QDR_PI_1_M0_R0_CFG_RANGE];
   assign dq_ddr_pi_0_cfg = msr ? wcs ?
         dq_dq_tx_ddr_pi_0_m1_r1_cfg[`DDR_CA_DQ_TX_DDR_PI_0_M1_R1_CFG_RANGE]:
         dq_dq_tx_ddr_pi_0_m1_r0_cfg[`DDR_CA_DQ_TX_DDR_PI_0_M1_R0_CFG_RANGE]: wcs ?
         dq_dq_tx_ddr_pi_0_m0_r1_cfg[`DDR_CA_DQ_TX_DDR_PI_0_M0_R1_CFG_RANGE]:
         dq_dq_tx_ddr_pi_0_m0_r0_cfg[`DDR_CA_DQ_TX_DDR_PI_0_M0_R0_CFG_RANGE];
   assign dq_ddr_pi_1_cfg = msr ? wcs ?
         dq_dq_tx_ddr_pi_1_m1_r1_cfg[`DDR_CA_DQ_TX_DDR_PI_1_M1_R1_CFG_RANGE]:
         dq_dq_tx_ddr_pi_1_m1_r0_cfg[`DDR_CA_DQ_TX_DDR_PI_1_M1_R0_CFG_RANGE]: wcs ?
         dq_dq_tx_ddr_pi_1_m0_r1_cfg[`DDR_CA_DQ_TX_DDR_PI_1_M0_R1_CFG_RANGE]:
         dq_dq_tx_ddr_pi_1_m0_r0_cfg[`DDR_CA_DQ_TX_DDR_PI_1_M0_R0_CFG_RANGE];
   assign dq_sdr_rt_pi_cfg = msr ? wcs ?
         dq_dq_tx_pi_rt_m1_r1_cfg[`DDR_CA_DQ_TX_PI_RT_M1_R1_CFG_RANGE]:
         dq_dq_tx_pi_rt_m1_r0_cfg[`DDR_CA_DQ_TX_PI_RT_M1_R0_CFG_RANGE]: wcs ?
         dq_dq_tx_pi_rt_m0_r1_cfg[`DDR_CA_DQ_TX_PI_RT_M0_R1_CFG_RANGE]:
         dq_dq_tx_pi_rt_m0_r0_cfg[`DDR_CA_DQ_TX_PI_RT_M0_R0_CFG_RANGE];
   assign o_dq_sdr_rt_pipe_en = msr ? wcs ?
         dq_dq_tx_rt_m1_r1_cfg[`DDR_CA_DQ_TX_RT_M1_R1_CFG_PIPE_EN_FIELD]:
         dq_dq_tx_rt_m1_r0_cfg[`DDR_CA_DQ_TX_RT_M1_R0_CFG_PIPE_EN_FIELD]: wcs ?
         dq_dq_tx_rt_m0_r1_cfg[`DDR_CA_DQ_TX_RT_M0_R1_CFG_PIPE_EN_FIELD]:
         dq_dq_tx_rt_m0_r0_cfg[`DDR_CA_DQ_TX_RT_M0_R0_CFG_PIPE_EN_FIELD];
   assign o_dq_sdr_0_pipe_en = msr ? wcs ?
      {
         dq_dq_tx_sdr_m1_r1_cfg_10[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_10_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_9[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_9_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_8[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_8_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_7[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_7_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_6[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_6_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_5[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_5_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_4[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_4_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_3[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_3_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_2[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_2_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_1[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_1_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_0[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_0_PIPE_EN_P0_FIELD]
      }:
      {
         dq_dq_tx_sdr_m1_r0_cfg_10[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_10_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_9[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_9_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_8[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_8_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_7[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_7_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_6[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_6_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_5[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_5_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_4[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_4_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_3[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_3_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_2[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_2_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_1[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_1_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_0[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_0_PIPE_EN_P0_FIELD]
       } : wcs ?
      {
         dq_dq_tx_sdr_m0_r1_cfg_10[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_10_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_9[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_9_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_8[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_8_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_7[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_7_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_6[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_6_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_5[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_5_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_4[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_4_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_3[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_3_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_2[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_2_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_1[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_1_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_0[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_0_PIPE_EN_P0_FIELD]
      }:
      {
         dq_dq_tx_sdr_m0_r0_cfg_10[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_10_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_9[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_9_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_8[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_8_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_7[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_7_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_6[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_6_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_5[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_5_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_4[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_4_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_3[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_3_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_2[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_2_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_1[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_1_PIPE_EN_P0_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_0[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_0_PIPE_EN_P0_FIELD]
      };

   assign o_dq_sdr_1_pipe_en = msr ? wcs ?
      {
         dq_dq_tx_sdr_m1_r1_cfg_10[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_10_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_9[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_9_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_8[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_8_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_7[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_7_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_6[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_6_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_5[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_5_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_4[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_4_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_3[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_3_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_2[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_2_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_1[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_1_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_0[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_0_PIPE_EN_P1_FIELD]
      }:
      {
         dq_dq_tx_sdr_m1_r0_cfg_10[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_10_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_9[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_9_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_8[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_8_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_7[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_7_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_6[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_6_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_5[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_5_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_4[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_4_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_3[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_3_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_2[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_2_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_1[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_1_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_0[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_0_PIPE_EN_P1_FIELD]
       } : wcs ?
      {
         dq_dq_tx_sdr_m0_r1_cfg_10[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_10_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_9[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_9_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_8[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_8_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_7[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_7_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_6[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_6_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_5[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_5_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_4[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_4_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_3[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_3_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_2[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_2_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_1[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_1_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_0[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_0_PIPE_EN_P1_FIELD]
      }:
      {
         dq_dq_tx_sdr_m0_r0_cfg_10[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_10_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_9[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_9_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_8[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_8_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_7[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_7_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_6[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_6_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_5[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_5_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_4[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_4_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_3[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_3_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_2[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_2_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_1[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_1_PIPE_EN_P1_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_0[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_0_PIPE_EN_P1_FIELD]
      };

   assign o_dq_sdr_2_pipe_en = msr ? wcs ?
      {
         dq_dq_tx_sdr_m1_r1_cfg_10[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_10_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_9[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_9_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_8[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_8_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_7[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_7_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_6[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_6_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_5[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_5_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_4[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_4_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_3[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_3_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_2[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_2_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_1[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_1_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_0[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_0_PIPE_EN_P2_FIELD]
      }:
      {
         dq_dq_tx_sdr_m1_r0_cfg_10[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_10_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_9[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_9_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_8[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_8_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_7[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_7_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_6[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_6_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_5[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_5_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_4[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_4_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_3[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_3_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_2[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_2_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_1[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_1_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_0[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_0_PIPE_EN_P2_FIELD]
       } : wcs ?
      {
         dq_dq_tx_sdr_m0_r1_cfg_10[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_10_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_9[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_9_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_8[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_8_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_7[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_7_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_6[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_6_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_5[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_5_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_4[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_4_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_3[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_3_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_2[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_2_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_1[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_1_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_0[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_0_PIPE_EN_P2_FIELD]
      }:
      {
         dq_dq_tx_sdr_m0_r0_cfg_10[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_10_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_9[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_9_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_8[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_8_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_7[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_7_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_6[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_6_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_5[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_5_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_4[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_4_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_3[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_3_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_2[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_2_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_1[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_1_PIPE_EN_P2_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_0[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_0_PIPE_EN_P2_FIELD]
      };

   assign o_dq_sdr_3_pipe_en = msr ? wcs ?
      {
         dq_dq_tx_sdr_m1_r1_cfg_10[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_10_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_9[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_9_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_8[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_8_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_7[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_7_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_6[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_6_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_5[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_5_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_4[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_4_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_3[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_3_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_2[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_2_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_1[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_1_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m1_r1_cfg_0[`DDR_CA_DQ_TX_SDR_M1_R1_CFG_0_PIPE_EN_P3_FIELD]
      }:
      {
         dq_dq_tx_sdr_m1_r0_cfg_10[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_10_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_9[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_9_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_8[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_8_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_7[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_7_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_6[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_6_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_5[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_5_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_4[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_4_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_3[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_3_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_2[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_2_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_1[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_1_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m1_r0_cfg_0[`DDR_CA_DQ_TX_SDR_M1_R0_CFG_0_PIPE_EN_P3_FIELD]
       } : wcs ?
      {
         dq_dq_tx_sdr_m0_r1_cfg_10[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_10_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_9[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_9_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_8[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_8_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_7[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_7_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_6[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_6_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_5[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_5_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_4[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_4_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_3[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_3_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_2[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_2_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_1[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_1_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m0_r1_cfg_0[`DDR_CA_DQ_TX_SDR_M0_R1_CFG_0_PIPE_EN_P3_FIELD]
      }:
      {
         dq_dq_tx_sdr_m0_r0_cfg_10[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_10_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_9[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_9_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_8[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_8_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_7[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_7_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_6[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_6_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_5[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_5_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_4[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_4_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_3[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_3_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_2[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_2_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_1[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_1_PIPE_EN_P3_FIELD],
         dq_dq_tx_sdr_m0_r0_cfg_0[`DDR_CA_DQ_TX_SDR_M0_R0_CFG_0_PIPE_EN_P3_FIELD]
      };

   assign dq_sdr_0_x_sel = msr ? wcs ?
      {
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_10[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_10_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_9[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_9_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_8[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_8_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_7[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_7_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_6[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_6_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_5[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_5_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_4[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_4_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_3[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_3_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_2[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_2_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_1[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_1_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_0[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_0_X_SEL_P0_FIELD]
      }:
      {
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_10[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_10_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_9[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_9_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_8[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_8_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_7[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_7_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_6[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_6_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_5[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_5_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_4[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_4_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_3[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_3_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_2[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_2_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_1[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_1_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_0[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_0_X_SEL_P0_FIELD]
       } : wcs ?
      {
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_10[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_10_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_9[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_9_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_8[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_8_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_7[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_7_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_6[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_6_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_5[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_5_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_4[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_4_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_3[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_3_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_2[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_2_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_1[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_1_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_0[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_0_X_SEL_P0_FIELD]
      }:
      {
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_10[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_10_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_9[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_9_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_8[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_8_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_7[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_7_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_6[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_6_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_5[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_5_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_4[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_4_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_3[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_3_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_2[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_2_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_1[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_1_X_SEL_P0_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_0[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_0_X_SEL_P0_FIELD]
      };
   assign dq_sdr_1_x_sel = msr ? wcs ?
      {
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_10[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_10_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_9[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_9_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_8[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_8_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_7[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_7_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_6[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_6_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_5[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_5_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_4[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_4_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_3[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_3_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_2[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_2_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_1[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_1_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_0[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_0_X_SEL_P1_FIELD]
      }:
      {
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_10[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_10_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_9[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_9_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_8[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_8_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_7[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_7_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_6[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_6_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_5[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_5_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_4[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_4_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_3[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_3_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_2[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_2_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_1[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_1_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_0[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_0_X_SEL_P1_FIELD]
       } : wcs ?
      {
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_10[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_10_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_9[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_9_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_8[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_8_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_7[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_7_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_6[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_6_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_5[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_5_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_4[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_4_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_3[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_3_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_2[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_2_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_1[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_1_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_0[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_0_X_SEL_P1_FIELD]
      }:
      {
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_10[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_10_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_9[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_9_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_8[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_8_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_7[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_7_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_6[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_6_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_5[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_5_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_4[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_4_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_3[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_3_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_2[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_2_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_1[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_1_X_SEL_P1_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_0[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_0_X_SEL_P1_FIELD]
      };
   assign dq_sdr_2_x_sel = msr ? wcs ?
      {
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_10[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_10_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_9[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_9_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_8[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_8_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_7[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_7_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_6[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_6_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_5[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_5_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_4[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_4_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_3[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_3_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_2[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_2_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_1[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_1_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_0[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_0_X_SEL_P2_FIELD]
      }:
      {
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_10[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_10_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_9[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_9_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_8[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_8_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_7[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_7_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_6[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_6_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_5[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_5_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_4[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_4_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_3[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_3_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_2[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_2_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_1[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_1_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_0[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_0_X_SEL_P2_FIELD]
       } : wcs ?
      {
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_10[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_10_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_9[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_9_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_8[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_8_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_7[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_7_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_6[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_6_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_5[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_5_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_4[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_4_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_3[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_3_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_2[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_2_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_1[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_1_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_0[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_0_X_SEL_P2_FIELD]
      }:
      {
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_10[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_10_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_9[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_9_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_8[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_8_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_7[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_7_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_6[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_6_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_5[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_5_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_4[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_4_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_3[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_3_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_2[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_2_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_1[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_1_X_SEL_P2_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_0[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_0_X_SEL_P2_FIELD]
      };
   assign dq_sdr_3_x_sel = msr ? wcs ?
      {
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_10[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_10_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_9[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_9_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_8[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_8_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_7[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_7_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_6[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_6_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_5[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_5_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_4[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_4_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_3[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_3_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_2[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_2_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_1[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_1_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_0[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_0_X_SEL_P3_FIELD]
      }:
      {
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_10[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_10_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_9[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_9_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_8[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_8_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_7[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_7_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_6[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_6_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_5[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_5_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_4[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_4_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_3[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_3_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_2[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_2_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_1[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_1_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_0[`DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_0_X_SEL_P3_FIELD]
       } : wcs ?
      {
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_10[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_10_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_9[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_9_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_8[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_8_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_7[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_7_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_6[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_6_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_5[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_5_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_4[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_4_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_3[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_3_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_2[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_2_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_1[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_1_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_0[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_0_X_SEL_P3_FIELD]
      }:
      {
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_10[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_10_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_9[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_9_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_8[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_8_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_7[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_7_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_6[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_6_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_5[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_5_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_4[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_4_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_3[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_3_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_2[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_2_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_1[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_1_X_SEL_P3_FIELD],
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_0[`DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_0_X_SEL_P3_FIELD]
      };
   assign o_dq_sdr_0_x_sel = {
         dq_sdr_0_x_sel[(MAX_MXWIDTH*10)+:MXWIDTH],
         dq_sdr_0_x_sel[(MAX_MXWIDTH*9)+:MXWIDTH],
         dq_sdr_0_x_sel[(MAX_MXWIDTH*8)+:MXWIDTH],
         dq_sdr_0_x_sel[(MAX_MXWIDTH*7)+:MXWIDTH],
         dq_sdr_0_x_sel[(MAX_MXWIDTH*6)+:MXWIDTH],
         dq_sdr_0_x_sel[(MAX_MXWIDTH*5)+:MXWIDTH],
         dq_sdr_0_x_sel[(MAX_MXWIDTH*4)+:MXWIDTH],
         dq_sdr_0_x_sel[(MAX_MXWIDTH*3)+:MXWIDTH],
         dq_sdr_0_x_sel[(MAX_MXWIDTH*2)+:MXWIDTH],
         dq_sdr_0_x_sel[(MAX_MXWIDTH*1)+:MXWIDTH],
         dq_sdr_0_x_sel[(MAX_MXWIDTH*0)+:MXWIDTH]
      };
   assign o_dq_sdr_1_x_sel = {
         dq_sdr_1_x_sel[(MAX_MXWIDTH*10)+:MXWIDTH],
         dq_sdr_1_x_sel[(MAX_MXWIDTH*9)+:MXWIDTH],
         dq_sdr_1_x_sel[(MAX_MXWIDTH*8)+:MXWIDTH],
         dq_sdr_1_x_sel[(MAX_MXWIDTH*7)+:MXWIDTH],
         dq_sdr_1_x_sel[(MAX_MXWIDTH*6)+:MXWIDTH],
         dq_sdr_1_x_sel[(MAX_MXWIDTH*5)+:MXWIDTH],
         dq_sdr_1_x_sel[(MAX_MXWIDTH*4)+:MXWIDTH],
         dq_sdr_1_x_sel[(MAX_MXWIDTH*3)+:MXWIDTH],
         dq_sdr_1_x_sel[(MAX_MXWIDTH*2)+:MXWIDTH],
         dq_sdr_1_x_sel[(MAX_MXWIDTH*1)+:MXWIDTH],
         dq_sdr_1_x_sel[(MAX_MXWIDTH*0)+:MXWIDTH]
      };
   assign o_dq_sdr_2_x_sel = {
         dq_sdr_2_x_sel[(MAX_MXWIDTH*10)+:MXWIDTH],
         dq_sdr_2_x_sel[(MAX_MXWIDTH*9)+:MXWIDTH],
         dq_sdr_2_x_sel[(MAX_MXWIDTH*8)+:MXWIDTH],
         dq_sdr_2_x_sel[(MAX_MXWIDTH*7)+:MXWIDTH],
         dq_sdr_2_x_sel[(MAX_MXWIDTH*6)+:MXWIDTH],
         dq_sdr_2_x_sel[(MAX_MXWIDTH*5)+:MXWIDTH],
         dq_sdr_2_x_sel[(MAX_MXWIDTH*4)+:MXWIDTH],
         dq_sdr_2_x_sel[(MAX_MXWIDTH*3)+:MXWIDTH],
         dq_sdr_2_x_sel[(MAX_MXWIDTH*2)+:MXWIDTH],
         dq_sdr_2_x_sel[(MAX_MXWIDTH*1)+:MXWIDTH],
         dq_sdr_2_x_sel[(MAX_MXWIDTH*0)+:MXWIDTH]
      };
   assign o_dq_sdr_3_x_sel = {
         dq_sdr_3_x_sel[(MAX_MXWIDTH*10)+:MXWIDTH],
         dq_sdr_3_x_sel[(MAX_MXWIDTH*9)+:MXWIDTH],
         dq_sdr_3_x_sel[(MAX_MXWIDTH*8)+:MXWIDTH],
         dq_sdr_3_x_sel[(MAX_MXWIDTH*7)+:MXWIDTH],
         dq_sdr_3_x_sel[(MAX_MXWIDTH*6)+:MXWIDTH],
         dq_sdr_3_x_sel[(MAX_MXWIDTH*5)+:MXWIDTH],
         dq_sdr_3_x_sel[(MAX_MXWIDTH*4)+:MXWIDTH],
         dq_sdr_3_x_sel[(MAX_MXWIDTH*3)+:MXWIDTH],
         dq_sdr_3_x_sel[(MAX_MXWIDTH*2)+:MXWIDTH],
         dq_sdr_3_x_sel[(MAX_MXWIDTH*1)+:MXWIDTH],
         dq_sdr_3_x_sel[(MAX_MXWIDTH*0)+:MXWIDTH]
      };
   assign o_dq_sdr_0_fc_dly = msr ? wcs ?
      {
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_10[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_10_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_9[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_9_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_8[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_8_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_7[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_7_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_6[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_6_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_5[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_5_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_4[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_4_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_3[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_3_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_2[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_2_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_1[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_1_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_0[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_0_DLY_P0_FIELD]
      }:
      {
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_10[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_10_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_9[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_9_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_8[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_8_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_7[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_7_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_6[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_6_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_5[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_5_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_4[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_4_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_3[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_3_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_2[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_2_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_1[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_1_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_0[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_0_DLY_P0_FIELD]
       } : wcs ?
      {
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_10[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_10_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_9[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_9_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_8[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_8_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_7[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_7_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_6[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_6_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_5[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_5_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_4[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_4_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_3[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_3_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_2[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_2_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_1[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_1_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_0[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_0_DLY_P0_FIELD]
      }:
      {
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_10[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_10_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_9[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_9_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_8[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_8_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_7[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_7_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_6[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_6_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_5[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_5_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_4[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_4_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_3[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_3_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_2[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_2_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_1[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_1_DLY_P0_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_0[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_0_DLY_P0_FIELD]
      };
   assign o_dq_sdr_1_fc_dly = msr ? wcs ?
      {
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_10[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_10_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_9[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_9_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_8[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_8_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_7[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_7_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_6[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_6_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_5[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_5_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_4[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_4_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_3[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_3_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_2[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_2_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_1[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_1_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_0[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_0_DLY_P1_FIELD]
      }:
      {
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_10[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_10_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_9[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_9_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_8[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_8_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_7[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_7_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_6[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_6_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_5[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_5_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_4[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_4_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_3[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_3_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_2[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_2_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_1[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_1_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_0[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_0_DLY_P1_FIELD]
       } : wcs ?
      {
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_10[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_10_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_9[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_9_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_8[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_8_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_7[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_7_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_6[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_6_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_5[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_5_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_4[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_4_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_3[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_3_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_2[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_2_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_1[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_1_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_0[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_0_DLY_P1_FIELD]
      }:
      {
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_10[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_10_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_9[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_9_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_8[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_8_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_7[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_7_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_6[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_6_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_5[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_5_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_4[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_4_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_3[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_3_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_2[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_2_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_1[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_1_DLY_P1_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_0[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_0_DLY_P1_FIELD]
      };
   assign o_dq_sdr_2_fc_dly = msr ? wcs ?
      {
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_10[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_10_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_9[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_9_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_8[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_8_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_7[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_7_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_6[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_6_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_5[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_5_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_4[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_4_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_3[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_3_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_2[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_2_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_1[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_1_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_0[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_0_DLY_P2_FIELD]
      }:
      {
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_10[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_10_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_9[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_9_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_8[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_8_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_7[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_7_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_6[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_6_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_5[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_5_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_4[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_4_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_3[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_3_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_2[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_2_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_1[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_1_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_0[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_0_DLY_P2_FIELD]
       } : wcs ?
      {
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_10[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_10_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_9[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_9_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_8[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_8_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_7[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_7_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_6[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_6_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_5[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_5_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_4[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_4_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_3[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_3_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_2[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_2_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_1[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_1_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_0[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_0_DLY_P2_FIELD]
      }:
      {
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_10[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_10_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_9[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_9_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_8[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_8_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_7[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_7_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_6[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_6_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_5[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_5_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_4[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_4_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_3[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_3_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_2[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_2_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_1[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_1_DLY_P2_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_0[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_0_DLY_P2_FIELD]
      };
   assign o_dq_sdr_3_fc_dly = msr ? wcs ?
      {
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_10[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_10_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_9[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_9_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_8[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_8_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_7[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_7_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_6[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_6_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_5[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_5_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_4[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_4_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_3[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_3_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_2[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_2_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_1[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_1_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_0[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_0_DLY_P3_FIELD]
      }:
      {
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_10[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_10_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_9[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_9_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_8[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_8_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_7[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_7_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_6[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_6_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_5[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_5_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_4[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_4_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_3[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_3_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_2[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_2_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_1[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_1_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_0[`DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_0_DLY_P3_FIELD]
       } : wcs ?
      {
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_10[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_10_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_9[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_9_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_8[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_8_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_7[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_7_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_6[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_6_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_5[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_5_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_4[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_4_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_3[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_3_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_2[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_2_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_1[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_1_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_0[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_0_DLY_P3_FIELD]
      }:
      {
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_10[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_10_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_9[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_9_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_8[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_8_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_7[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_7_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_6[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_6_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_5[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_5_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_4[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_4_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_3[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_3_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_2[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_2_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_1[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_1_DLY_P3_FIELD],
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_0[`DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_0_DLY_P3_FIELD]
      };
   assign o_dq_ddr_0_pipe_en = msr ? wcs ?
      {
         dq_dq_tx_ddr_m1_r1_cfg_10[`DDR_CA_DQ_TX_DDR_M1_R1_CFG_10_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m1_r1_cfg_9[`DDR_CA_DQ_TX_DDR_M1_R1_CFG_9_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m1_r1_cfg_8[`DDR_CA_DQ_TX_DDR_M1_R1_CFG_8_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m1_r1_cfg_7[`DDR_CA_DQ_TX_DDR_M1_R1_CFG_7_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m1_r1_cfg_6[`DDR_CA_DQ_TX_DDR_M1_R1_CFG_6_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m1_r1_cfg_5[`DDR_CA_DQ_TX_DDR_M1_R1_CFG_5_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m1_r1_cfg_4[`DDR_CA_DQ_TX_DDR_M1_R1_CFG_4_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m1_r1_cfg_3[`DDR_CA_DQ_TX_DDR_M1_R1_CFG_3_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m1_r1_cfg_2[`DDR_CA_DQ_TX_DDR_M1_R1_CFG_2_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m1_r1_cfg_1[`DDR_CA_DQ_TX_DDR_M1_R1_CFG_1_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m1_r1_cfg_0[`DDR_CA_DQ_TX_DDR_M1_R1_CFG_0_PIPE_EN_P0_FIELD]
      }:
      {
         dq_dq_tx_ddr_m1_r0_cfg_10[`DDR_CA_DQ_TX_DDR_M1_R0_CFG_10_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m1_r0_cfg_9[`DDR_CA_DQ_TX_DDR_M1_R0_CFG_9_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m1_r0_cfg_8[`DDR_CA_DQ_TX_DDR_M1_R0_CFG_8_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m1_r0_cfg_7[`DDR_CA_DQ_TX_DDR_M1_R0_CFG_7_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m1_r0_cfg_6[`DDR_CA_DQ_TX_DDR_M1_R0_CFG_6_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m1_r0_cfg_5[`DDR_CA_DQ_TX_DDR_M1_R0_CFG_5_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m1_r0_cfg_4[`DDR_CA_DQ_TX_DDR_M1_R0_CFG_4_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m1_r0_cfg_3[`DDR_CA_DQ_TX_DDR_M1_R0_CFG_3_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m1_r0_cfg_2[`DDR_CA_DQ_TX_DDR_M1_R0_CFG_2_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m1_r0_cfg_1[`DDR_CA_DQ_TX_DDR_M1_R0_CFG_1_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m1_r0_cfg_0[`DDR_CA_DQ_TX_DDR_M1_R0_CFG_0_PIPE_EN_P0_FIELD]
       } : rcs ?
      {
         dq_dq_tx_ddr_m0_r1_cfg_10[`DDR_CA_DQ_TX_DDR_M0_R1_CFG_10_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m0_r1_cfg_9[`DDR_CA_DQ_TX_DDR_M0_R1_CFG_9_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m0_r1_cfg_8[`DDR_CA_DQ_TX_DDR_M0_R1_CFG_8_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m0_r1_cfg_7[`DDR_CA_DQ_TX_DDR_M0_R1_CFG_7_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m0_r1_cfg_6[`DDR_CA_DQ_TX_DDR_M0_R1_CFG_6_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m0_r1_cfg_5[`DDR_CA_DQ_TX_DDR_M0_R1_CFG_5_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m0_r1_cfg_4[`DDR_CA_DQ_TX_DDR_M0_R1_CFG_4_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m0_r1_cfg_3[`DDR_CA_DQ_TX_DDR_M0_R1_CFG_3_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m0_r1_cfg_2[`DDR_CA_DQ_TX_DDR_M0_R1_CFG_2_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m0_r1_cfg_1[`DDR_CA_DQ_TX_DDR_M0_R1_CFG_1_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m0_r1_cfg_0[`DDR_CA_DQ_TX_DDR_M0_R1_CFG_0_PIPE_EN_P0_FIELD]
      }:
      {
         dq_dq_tx_ddr_m0_r0_cfg_10[`DDR_CA_DQ_TX_DDR_M0_R0_CFG_10_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m0_r0_cfg_9[`DDR_CA_DQ_TX_DDR_M0_R0_CFG_9_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m0_r0_cfg_8[`DDR_CA_DQ_TX_DDR_M0_R0_CFG_8_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m0_r0_cfg_7[`DDR_CA_DQ_TX_DDR_M0_R0_CFG_7_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m0_r0_cfg_6[`DDR_CA_DQ_TX_DDR_M0_R0_CFG_6_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m0_r0_cfg_5[`DDR_CA_DQ_TX_DDR_M0_R0_CFG_5_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m0_r0_cfg_4[`DDR_CA_DQ_TX_DDR_M0_R0_CFG_4_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m0_r0_cfg_3[`DDR_CA_DQ_TX_DDR_M0_R0_CFG_3_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m0_r0_cfg_2[`DDR_CA_DQ_TX_DDR_M0_R0_CFG_2_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m0_r0_cfg_1[`DDR_CA_DQ_TX_DDR_M0_R0_CFG_1_PIPE_EN_P0_FIELD],
         dq_dq_tx_ddr_m0_r0_cfg_0[`DDR_CA_DQ_TX_DDR_M0_R0_CFG_0_PIPE_EN_P0_FIELD]
      };
   assign o_dq_ddr_1_pipe_en = msr ? wcs ?
      {
         dq_dq_tx_ddr_m1_r1_cfg_10[`DDR_CA_DQ_TX_DDR_M1_R1_CFG_10_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m1_r1_cfg_9[`DDR_CA_DQ_TX_DDR_M1_R1_CFG_9_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m1_r1_cfg_8[`DDR_CA_DQ_TX_DDR_M1_R1_CFG_8_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m1_r1_cfg_7[`DDR_CA_DQ_TX_DDR_M1_R1_CFG_7_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m1_r1_cfg_6[`DDR_CA_DQ_TX_DDR_M1_R1_CFG_6_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m1_r1_cfg_5[`DDR_CA_DQ_TX_DDR_M1_R1_CFG_5_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m1_r1_cfg_4[`DDR_CA_DQ_TX_DDR_M1_R1_CFG_4_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m1_r1_cfg_3[`DDR_CA_DQ_TX_DDR_M1_R1_CFG_3_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m1_r1_cfg_2[`DDR_CA_DQ_TX_DDR_M1_R1_CFG_2_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m1_r1_cfg_1[`DDR_CA_DQ_TX_DDR_M1_R1_CFG_1_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m1_r1_cfg_0[`DDR_CA_DQ_TX_DDR_M1_R1_CFG_0_PIPE_EN_P1_FIELD]
      }:
      {
         dq_dq_tx_ddr_m1_r0_cfg_10[`DDR_CA_DQ_TX_DDR_M1_R0_CFG_10_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m1_r0_cfg_9[`DDR_CA_DQ_TX_DDR_M1_R0_CFG_9_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m1_r0_cfg_8[`DDR_CA_DQ_TX_DDR_M1_R0_CFG_8_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m1_r0_cfg_7[`DDR_CA_DQ_TX_DDR_M1_R0_CFG_7_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m1_r0_cfg_6[`DDR_CA_DQ_TX_DDR_M1_R0_CFG_6_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m1_r0_cfg_5[`DDR_CA_DQ_TX_DDR_M1_R0_CFG_5_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m1_r0_cfg_4[`DDR_CA_DQ_TX_DDR_M1_R0_CFG_4_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m1_r0_cfg_3[`DDR_CA_DQ_TX_DDR_M1_R0_CFG_3_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m1_r0_cfg_2[`DDR_CA_DQ_TX_DDR_M1_R0_CFG_2_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m1_r0_cfg_1[`DDR_CA_DQ_TX_DDR_M1_R0_CFG_1_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m1_r0_cfg_0[`DDR_CA_DQ_TX_DDR_M1_R0_CFG_0_PIPE_EN_P1_FIELD]
       } : rcs ?
      {
         dq_dq_tx_ddr_m0_r1_cfg_10[`DDR_CA_DQ_TX_DDR_M0_R1_CFG_10_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m0_r1_cfg_9[`DDR_CA_DQ_TX_DDR_M0_R1_CFG_9_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m0_r1_cfg_8[`DDR_CA_DQ_TX_DDR_M0_R1_CFG_8_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m0_r1_cfg_7[`DDR_CA_DQ_TX_DDR_M0_R1_CFG_7_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m0_r1_cfg_6[`DDR_CA_DQ_TX_DDR_M0_R1_CFG_6_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m0_r1_cfg_5[`DDR_CA_DQ_TX_DDR_M0_R1_CFG_5_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m0_r1_cfg_4[`DDR_CA_DQ_TX_DDR_M0_R1_CFG_4_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m0_r1_cfg_3[`DDR_CA_DQ_TX_DDR_M0_R1_CFG_3_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m0_r1_cfg_2[`DDR_CA_DQ_TX_DDR_M0_R1_CFG_2_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m0_r1_cfg_1[`DDR_CA_DQ_TX_DDR_M0_R1_CFG_1_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m0_r1_cfg_0[`DDR_CA_DQ_TX_DDR_M0_R1_CFG_0_PIPE_EN_P1_FIELD]
      }:
      {
         dq_dq_tx_ddr_m0_r0_cfg_10[`DDR_CA_DQ_TX_DDR_M0_R0_CFG_10_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m0_r0_cfg_9[`DDR_CA_DQ_TX_DDR_M0_R0_CFG_9_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m0_r0_cfg_8[`DDR_CA_DQ_TX_DDR_M0_R0_CFG_8_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m0_r0_cfg_7[`DDR_CA_DQ_TX_DDR_M0_R0_CFG_7_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m0_r0_cfg_6[`DDR_CA_DQ_TX_DDR_M0_R0_CFG_6_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m0_r0_cfg_5[`DDR_CA_DQ_TX_DDR_M0_R0_CFG_5_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m0_r0_cfg_4[`DDR_CA_DQ_TX_DDR_M0_R0_CFG_4_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m0_r0_cfg_3[`DDR_CA_DQ_TX_DDR_M0_R0_CFG_3_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m0_r0_cfg_2[`DDR_CA_DQ_TX_DDR_M0_R0_CFG_2_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m0_r0_cfg_1[`DDR_CA_DQ_TX_DDR_M0_R0_CFG_1_PIPE_EN_P1_FIELD],
         dq_dq_tx_ddr_m0_r0_cfg_0[`DDR_CA_DQ_TX_DDR_M0_R0_CFG_0_PIPE_EN_P1_FIELD]
      };
   assign dq_ddr_0_x_sel = msr ? wcs ?
      {
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_10[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_10_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_9[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_9_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_8[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_8_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_7[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_7_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_6[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_6_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_5[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_5_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_4[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_4_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_3[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_3_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_2[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_2_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_1[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_1_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_0[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_0_X_SEL_P0_FIELD]
      }:
      {
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_10[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_10_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_9[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_9_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_8[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_8_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_7[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_7_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_6[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_6_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_5[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_5_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_4[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_4_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_3[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_3_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_2[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_2_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_1[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_1_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_0[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_0_X_SEL_P0_FIELD]
       } : wcs ?
      {
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_10[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_10_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_9[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_9_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_8[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_8_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_7[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_7_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_6[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_6_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_5[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_5_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_4[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_4_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_3[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_3_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_2[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_2_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_1[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_1_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_0[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_0_X_SEL_P0_FIELD]
      }:
      {
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_10[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_10_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_9[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_9_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_8[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_8_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_7[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_7_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_6[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_6_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_5[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_5_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_4[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_4_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_3[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_3_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_2[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_2_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_1[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_1_X_SEL_P0_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_0[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_0_X_SEL_P0_FIELD]
      };
   assign dq_ddr_1_x_sel = msr ? wcs ?
      {
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_10[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_10_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_9[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_9_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_8[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_8_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_7[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_7_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_6[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_6_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_5[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_5_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_4[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_4_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_3[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_3_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_2[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_2_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_1[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_1_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_0[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_0_X_SEL_P1_FIELD]
      }:
      {
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_10[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_10_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_9[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_9_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_8[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_8_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_7[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_7_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_6[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_6_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_5[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_5_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_4[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_4_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_3[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_3_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_2[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_2_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_1[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_1_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_0[`DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_0_X_SEL_P1_FIELD]
       } : wcs ?
      {
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_10[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_10_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_9[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_9_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_8[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_8_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_7[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_7_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_6[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_6_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_5[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_5_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_4[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_4_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_3[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_3_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_2[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_2_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_1[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_1_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_0[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_0_X_SEL_P1_FIELD]
      }:
      {
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_10[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_10_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_9[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_9_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_8[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_8_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_7[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_7_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_6[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_6_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_5[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_5_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_4[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_4_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_3[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_3_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_2[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_2_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_1[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_1_X_SEL_P1_FIELD],
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_0[`DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_0_X_SEL_P1_FIELD]
      };
   assign o_dq_ddr_0_x_sel = {
         dq_ddr_0_x_sel[(MAX_MXWIDTH-1)*10+:(MXWIDTH-1)] ,
         dq_ddr_0_x_sel[(MAX_MXWIDTH-1)*9+:(MXWIDTH-1)] ,
         dq_ddr_0_x_sel[(MAX_MXWIDTH-1)*8+:(MXWIDTH-1)] ,
         dq_ddr_0_x_sel[(MAX_MXWIDTH-1)*7+:(MXWIDTH-1)] ,
         dq_ddr_0_x_sel[(MAX_MXWIDTH-1)*6+:(MXWIDTH-1)] ,
         dq_ddr_0_x_sel[(MAX_MXWIDTH-1)*5+:(MXWIDTH-1)] ,
         dq_ddr_0_x_sel[(MAX_MXWIDTH-1)*4+:(MXWIDTH-1)] ,
         dq_ddr_0_x_sel[(MAX_MXWIDTH-1)*3+:(MXWIDTH-1)] ,
         dq_ddr_0_x_sel[(MAX_MXWIDTH-1)*2+:(MXWIDTH-1)] ,
         dq_ddr_0_x_sel[(MAX_MXWIDTH-1)*1+:(MXWIDTH-1)] ,
         dq_ddr_0_x_sel[(MAX_MXWIDTH-1)*0 +:(MXWIDTH-1)]
      };
   assign o_dq_ddr_1_x_sel = {
         dq_ddr_1_x_sel[(MAX_MXWIDTH-1)*10+:(MXWIDTH-1)] ,
         dq_ddr_1_x_sel[(MAX_MXWIDTH-1)*9+:(MXWIDTH-1)] ,
         dq_ddr_1_x_sel[(MAX_MXWIDTH-1)*8+:(MXWIDTH-1)] ,
         dq_ddr_1_x_sel[(MAX_MXWIDTH-1)*7+:(MXWIDTH-1)] ,
         dq_ddr_1_x_sel[(MAX_MXWIDTH-1)*6+:(MXWIDTH-1)] ,
         dq_ddr_1_x_sel[(MAX_MXWIDTH-1)*5+:(MXWIDTH-1)] ,
         dq_ddr_1_x_sel[(MAX_MXWIDTH-1)*4+:(MXWIDTH-1)] ,
         dq_ddr_1_x_sel[(MAX_MXWIDTH-1)*3+:(MXWIDTH-1)] ,
         dq_ddr_1_x_sel[(MAX_MXWIDTH-1)*2+:(MXWIDTH-1)] ,
         dq_ddr_1_x_sel[(MAX_MXWIDTH-1)*1+:(MXWIDTH-1)] ,
         dq_ddr_1_x_sel[(MAX_MXWIDTH-1)*0 +:(MXWIDTH-1)]
      };
   assign o_dq_xdr_lpde_cfg = msr ? wcs ?
      {
         dq_dq_tx_lpde_m1_r1_cfg_10[`DDR_CA_DQ_TX_LPDE_M1_R1_CFG_10_RANGE],
         dq_dq_tx_lpde_m1_r1_cfg_9[`DDR_CA_DQ_TX_LPDE_M1_R1_CFG_9_RANGE],
         dq_dq_tx_lpde_m1_r1_cfg_8[`DDR_CA_DQ_TX_LPDE_M1_R1_CFG_8_RANGE],
         dq_dq_tx_lpde_m1_r1_cfg_7[`DDR_CA_DQ_TX_LPDE_M1_R1_CFG_7_RANGE],
         dq_dq_tx_lpde_m1_r1_cfg_6[`DDR_CA_DQ_TX_LPDE_M1_R1_CFG_6_RANGE],
         dq_dq_tx_lpde_m1_r1_cfg_5[`DDR_CA_DQ_TX_LPDE_M1_R1_CFG_5_RANGE],
         dq_dq_tx_lpde_m1_r1_cfg_4[`DDR_CA_DQ_TX_LPDE_M1_R1_CFG_4_RANGE],
         dq_dq_tx_lpde_m1_r1_cfg_3[`DDR_CA_DQ_TX_LPDE_M1_R1_CFG_3_RANGE],
         dq_dq_tx_lpde_m1_r1_cfg_2[`DDR_CA_DQ_TX_LPDE_M1_R1_CFG_2_RANGE],
         dq_dq_tx_lpde_m1_r1_cfg_1[`DDR_CA_DQ_TX_LPDE_M1_R1_CFG_1_RANGE],
         dq_dq_tx_lpde_m1_r1_cfg_0[`DDR_CA_DQ_TX_LPDE_M1_R1_CFG_0_RANGE]
      }:
      {
         dq_dq_tx_lpde_m1_r0_cfg_10[`DDR_CA_DQ_TX_LPDE_M1_R0_CFG_10_RANGE],
         dq_dq_tx_lpde_m1_r0_cfg_9[`DDR_CA_DQ_TX_LPDE_M1_R0_CFG_9_RANGE],
         dq_dq_tx_lpde_m1_r0_cfg_8[`DDR_CA_DQ_TX_LPDE_M1_R0_CFG_8_RANGE],
         dq_dq_tx_lpde_m1_r0_cfg_7[`DDR_CA_DQ_TX_LPDE_M1_R0_CFG_7_RANGE],
         dq_dq_tx_lpde_m1_r0_cfg_6[`DDR_CA_DQ_TX_LPDE_M1_R0_CFG_6_RANGE],
         dq_dq_tx_lpde_m1_r0_cfg_5[`DDR_CA_DQ_TX_LPDE_M1_R0_CFG_5_RANGE],
         dq_dq_tx_lpde_m1_r0_cfg_4[`DDR_CA_DQ_TX_LPDE_M1_R0_CFG_4_RANGE],
         dq_dq_tx_lpde_m1_r0_cfg_3[`DDR_CA_DQ_TX_LPDE_M1_R0_CFG_3_RANGE],
         dq_dq_tx_lpde_m1_r0_cfg_2[`DDR_CA_DQ_TX_LPDE_M1_R0_CFG_2_RANGE],
         dq_dq_tx_lpde_m1_r0_cfg_1[`DDR_CA_DQ_TX_LPDE_M1_R0_CFG_1_RANGE],
         dq_dq_tx_lpde_m1_r0_cfg_0[`DDR_CA_DQ_TX_LPDE_M1_R0_CFG_0_RANGE]
       } : wcs ?
      {
         dq_dq_tx_lpde_m0_r1_cfg_10[`DDR_CA_DQ_TX_LPDE_M0_R1_CFG_10_RANGE],
         dq_dq_tx_lpde_m0_r1_cfg_9[`DDR_CA_DQ_TX_LPDE_M0_R1_CFG_9_RANGE],
         dq_dq_tx_lpde_m0_r1_cfg_8[`DDR_CA_DQ_TX_LPDE_M0_R1_CFG_8_RANGE],
         dq_dq_tx_lpde_m0_r1_cfg_7[`DDR_CA_DQ_TX_LPDE_M0_R1_CFG_7_RANGE],
         dq_dq_tx_lpde_m0_r1_cfg_6[`DDR_CA_DQ_TX_LPDE_M0_R1_CFG_6_RANGE],
         dq_dq_tx_lpde_m0_r1_cfg_5[`DDR_CA_DQ_TX_LPDE_M0_R1_CFG_5_RANGE],
         dq_dq_tx_lpde_m0_r1_cfg_4[`DDR_CA_DQ_TX_LPDE_M0_R1_CFG_4_RANGE],
         dq_dq_tx_lpde_m0_r1_cfg_3[`DDR_CA_DQ_TX_LPDE_M0_R1_CFG_3_RANGE],
         dq_dq_tx_lpde_m0_r1_cfg_2[`DDR_CA_DQ_TX_LPDE_M0_R1_CFG_2_RANGE],
         dq_dq_tx_lpde_m0_r1_cfg_1[`DDR_CA_DQ_TX_LPDE_M0_R1_CFG_1_RANGE],
         dq_dq_tx_lpde_m0_r1_cfg_0[`DDR_CA_DQ_TX_LPDE_M0_R1_CFG_0_RANGE]
      }:
      {
         dq_dq_tx_lpde_m0_r0_cfg_10[`DDR_CA_DQ_TX_LPDE_M0_R0_CFG_10_RANGE],
         dq_dq_tx_lpde_m0_r0_cfg_9[`DDR_CA_DQ_TX_LPDE_M0_R0_CFG_9_RANGE],
         dq_dq_tx_lpde_m0_r0_cfg_8[`DDR_CA_DQ_TX_LPDE_M0_R0_CFG_8_RANGE],
         dq_dq_tx_lpde_m0_r0_cfg_7[`DDR_CA_DQ_TX_LPDE_M0_R0_CFG_7_RANGE],
         dq_dq_tx_lpde_m0_r0_cfg_6[`DDR_CA_DQ_TX_LPDE_M0_R0_CFG_6_RANGE],
         dq_dq_tx_lpde_m0_r0_cfg_5[`DDR_CA_DQ_TX_LPDE_M0_R0_CFG_5_RANGE],
         dq_dq_tx_lpde_m0_r0_cfg_4[`DDR_CA_DQ_TX_LPDE_M0_R0_CFG_4_RANGE],
         dq_dq_tx_lpde_m0_r0_cfg_3[`DDR_CA_DQ_TX_LPDE_M0_R0_CFG_3_RANGE],
         dq_dq_tx_lpde_m0_r0_cfg_2[`DDR_CA_DQ_TX_LPDE_M0_R0_CFG_2_RANGE],
         dq_dq_tx_lpde_m0_r0_cfg_1[`DDR_CA_DQ_TX_LPDE_M0_R0_CFG_1_RANGE],
         dq_dq_tx_lpde_m0_r0_cfg_0[`DDR_CA_DQ_TX_LPDE_M0_R0_CFG_0_RANGE]
      };
   //assign o_dq_pad_tx_cfg  = msr ? wcs ?
   //   {
   //`for (j=`DDR_NUM_CA_SLICES-1; j>0; j--)
   //      dq_dq_tx_io_m1_r1_cfg_`j[`DDR_CA_DQ_TX_IO_M1_R1_CFG_`j::_RANGE],
   //`endfor
   //      dq_dq_tx_io_m1_r1_cfg_0[`DDR_CA_DQ_TX_IO_M1_R1_CFG_0_RANGE]
   //   }:
   //   {
   //`for (j=`DDR_NUM_CA_SLICES-1; j>0; j--)
   //      dq_dq_tx_io_m1_r0_cfg_`j[`DDR_CA_DQ_TX_IO_M1_R0_CFG_`j::_RANGE],
   //`endfor
   //      dq_dq_tx_io_m1_r0_cfg_0[`DDR_CA_DQ_TX_IO_M1_R0_CFG_0_RANGE]
   //    } : wcs ?
   //   {
   //`for (j=`DDR_NUM_CA_SLICES-1; j>0; j--)
   //      dq_dq_tx_io_m0_r1_cfg_`j[`DDR_CA_DQ_TX_IO_M0_R1_CFG_`j::_RANGE],
   //`endfor
   //      dq_dq_tx_io_m0_r1_cfg_0[`DDR_CA_DQ_TX_IO_M0_R1_CFG_0_RANGE]
   //   }:
   //   {
   //`for (j=`DDR_NUM_CA_SLICES-1; j>0; j--)
   //      dq_dq_tx_io_m0_r0_cfg_`j[`DDR_CA_DQ_TX_IO_M0_R0_CFG_`j::_RANGE],
   //`endfor
   //      dq_dq_tx_io_m0_r0_cfg_0[`DDR_CA_DQ_TX_IO_M0_R0_CFG_0_RANGE]
   //   };
   assign o_dq_pad_tx_cfg  = msr ?
      {
         dq_dq_tx_io_m1_cfg_10[`DDR_CA_DQ_TX_IO_M1_CFG_10_RANGE],
         dq_dq_tx_io_m1_cfg_9[`DDR_CA_DQ_TX_IO_M1_CFG_9_RANGE],
         dq_dq_tx_io_m1_cfg_8[`DDR_CA_DQ_TX_IO_M1_CFG_8_RANGE],
         dq_dq_tx_io_m1_cfg_7[`DDR_CA_DQ_TX_IO_M1_CFG_7_RANGE],
         dq_dq_tx_io_m1_cfg_6[`DDR_CA_DQ_TX_IO_M1_CFG_6_RANGE],
         dq_dq_tx_io_m1_cfg_5[`DDR_CA_DQ_TX_IO_M1_CFG_5_RANGE],
         dq_dq_tx_io_m1_cfg_4[`DDR_CA_DQ_TX_IO_M1_CFG_4_RANGE],
         dq_dq_tx_io_m1_cfg_3[`DDR_CA_DQ_TX_IO_M1_CFG_3_RANGE],
         dq_dq_tx_io_m1_cfg_2[`DDR_CA_DQ_TX_IO_M1_CFG_2_RANGE],
         dq_dq_tx_io_m1_cfg_1[`DDR_CA_DQ_TX_IO_M1_CFG_1_RANGE],
         dq_dq_tx_io_m1_cfg_0[`DDR_CA_DQ_TX_IO_M1_CFG_0_RANGE]
      }:
      {
         dq_dq_tx_io_m0_cfg_10[`DDR_CA_DQ_TX_IO_M0_CFG_10_RANGE],
         dq_dq_tx_io_m0_cfg_9[`DDR_CA_DQ_TX_IO_M0_CFG_9_RANGE],
         dq_dq_tx_io_m0_cfg_8[`DDR_CA_DQ_TX_IO_M0_CFG_8_RANGE],
         dq_dq_tx_io_m0_cfg_7[`DDR_CA_DQ_TX_IO_M0_CFG_7_RANGE],
         dq_dq_tx_io_m0_cfg_6[`DDR_CA_DQ_TX_IO_M0_CFG_6_RANGE],
         dq_dq_tx_io_m0_cfg_5[`DDR_CA_DQ_TX_IO_M0_CFG_5_RANGE],
         dq_dq_tx_io_m0_cfg_4[`DDR_CA_DQ_TX_IO_M0_CFG_4_RANGE],
         dq_dq_tx_io_m0_cfg_3[`DDR_CA_DQ_TX_IO_M0_CFG_3_RANGE],
         dq_dq_tx_io_m0_cfg_2[`DDR_CA_DQ_TX_IO_M0_CFG_2_RANGE],
         dq_dq_tx_io_m0_cfg_1[`DDR_CA_DQ_TX_IO_M0_CFG_1_RANGE],
         dq_dq_tx_io_m0_cfg_0[`DDR_CA_DQ_TX_IO_M0_CFG_0_RANGE]
      };

   // ---------------------------------------------------------
   // DQS RX
   // ---------------------------------------------------------

   assign dqs_rgb_mode = msr ?
         cast_dgb_t(dq_dqs_rx_m1_cfg[`DDR_CA_DQS_RX_M1_CFG_RGB_MODE_FIELD]):
         cast_dgb_t(dq_dqs_rx_m0_cfg[`DDR_CA_DQS_RX_M0_CFG_RGB_MODE_FIELD]);
   assign o_dqs_fgb_mode = msr ?
         cast_fgb_t(dq_dqs_rx_m1_cfg[`DDR_CA_DQS_RX_M1_CFG_FGB_MODE_FIELD]):
         cast_fgb_t(dq_dqs_rx_m0_cfg[`DDR_CA_DQS_RX_M0_CFG_FGB_MODE_FIELD]);
   assign o_dqs_wck_mode = msr ?
         dq_dqs_rx_m1_cfg[`DDR_CA_DQS_RX_M1_CFG_WCK_MODE_FIELD]:
         dq_dqs_rx_m0_cfg[`DDR_CA_DQS_RX_M0_CFG_WCK_MODE_FIELD];

   always_comb begin
      case(dqs_rgb_mode)
        DGB_8TO1_HF : o_dqs_rgb_mode = {{(DEC_DGBWIDTH-1){1'b0}},1'b1} << `DGB_8TO1_HF_IDX ;
        DGB_8TO1_LF : o_dqs_rgb_mode = {{(DEC_DGBWIDTH-1){1'b0}},1'b1} << `DGB_8TO1_LF_IDX ;
        DGB_4TO1_IR : o_dqs_rgb_mode = {{(DEC_DGBWIDTH-1){1'b0}},1'b1} << `DGB_4TO1_IR_IDX ;
        DGB_4TO1_HF : o_dqs_rgb_mode = {{(DEC_DGBWIDTH-1){1'b0}},1'b1} << `DGB_4TO1_HF_IDX ;
        DGB_4TO1_LF : o_dqs_rgb_mode = {{(DEC_DGBWIDTH-1){1'b0}},1'b1} << `DGB_4TO1_LF_IDX ;
        DGB_2TO1_IR : o_dqs_rgb_mode = {{(DEC_DGBWIDTH-1){1'b0}},1'b1} << `DGB_2TO1_IR_IDX ;
        DGB_2TO1_HF : o_dqs_rgb_mode = {{(DEC_DGBWIDTH-1){1'b0}},1'b1} << `DGB_2TO1_HF_IDX ;
        DGB_1TO1_HF : o_dqs_rgb_mode = {{(DEC_DGBWIDTH-1){1'b0}},1'b1} << `DGB_1TO1_HF_IDX ;
        default     : o_dqs_rgb_mode = {{(DEC_DGBWIDTH-1){1'b0}},1'b1} << `DGB_1TO1_HF_IDX ;
      endcase
   end

   assign dq_dqs_rx_bscan_sta[`DDR_CA_DQS_RX_BSCAN_STA_VAL_FIELD] = i_dqs_ingress_bscan;
   assign o_dqs_sdr_lpde_cfg = msr ? rcs ?
         dq_dqs_rx_sdr_lpde_m1_r1_cfg[`DDR_CA_DQS_RX_SDR_LPDE_M1_R1_CFG_RANGE]:
         dq_dqs_rx_sdr_lpde_m1_r0_cfg[`DDR_CA_DQS_RX_SDR_LPDE_M1_R0_CFG_RANGE]: rcs ?
         dq_dqs_rx_sdr_lpde_m0_r1_cfg[`DDR_CA_DQS_RX_SDR_LPDE_M0_R1_CFG_RANGE]:
         dq_dqs_rx_sdr_lpde_m0_r0_cfg[`DDR_CA_DQS_RX_SDR_LPDE_M0_R0_CFG_RANGE];
   assign o_dqs_pre_filter_sel = msr ?
         dq_dqs_rx_m1_cfg[`DDR_CA_DQS_RX_M1_CFG_PRE_FILTER_SEL_FIELD]:
         dq_dqs_rx_m0_cfg[`DDR_CA_DQS_RX_M0_CFG_PRE_FILTER_SEL_FIELD];
   assign dqs_ren_pi_cfg= msr ? rcs ?
         dq_dqs_rx_ren_pi_m1_r1_cfg[`DDR_CA_DQS_RX_REN_PI_M1_R1_CFG_RANGE]:
         dq_dqs_rx_ren_pi_m1_r0_cfg[`DDR_CA_DQS_RX_REN_PI_M1_R0_CFG_RANGE]: rcs ?
         dq_dqs_rx_ren_pi_m0_r1_cfg[`DDR_CA_DQS_RX_REN_PI_M0_R1_CFG_RANGE]:
         dq_dqs_rx_ren_pi_m0_r0_cfg[`DDR_CA_DQS_RX_REN_PI_M0_R0_CFG_RANGE];
   assign dqs_rcs_pi_cfg = msr ? rcs ?
         dq_dqs_rx_rcs_pi_m1_r1_cfg[`DDR_CA_DQS_RX_RCS_PI_M1_R1_CFG_RANGE]:
         dq_dqs_rx_rcs_pi_m1_r0_cfg[`DDR_CA_DQS_RX_RCS_PI_M1_R0_CFG_RANGE]: rcs ?
         dq_dqs_rx_rcs_pi_m0_r1_cfg[`DDR_CA_DQS_RX_RCS_PI_M0_R1_CFG_RANGE]:
         dq_dqs_rx_rcs_pi_m0_r0_cfg[`DDR_CA_DQS_RX_RCS_PI_M0_R0_CFG_RANGE];
   assign dqs_rdqs_pi_0_cfg= msr ? rcs ?
         dq_dqs_rx_rdqs_pi_0_m1_r1_cfg[`DDR_CA_DQS_RX_RDQS_PI_0_M1_R1_CFG_RANGE]:
         dq_dqs_rx_rdqs_pi_0_m1_r0_cfg[`DDR_CA_DQS_RX_RDQS_PI_0_M1_R0_CFG_RANGE]: rcs ?
         dq_dqs_rx_rdqs_pi_0_m0_r1_cfg[`DDR_CA_DQS_RX_RDQS_PI_0_M0_R1_CFG_RANGE]:
         dq_dqs_rx_rdqs_pi_0_m0_r0_cfg[`DDR_CA_DQS_RX_RDQS_PI_0_M0_R0_CFG_RANGE];
   assign dqs_rdqs_pi_1_cfg = msr ? rcs ?
         dq_dqs_rx_rdqs_pi_1_m1_r1_cfg[`DDR_CA_DQS_RX_RDQS_PI_1_M1_R1_CFG_RANGE]:
         dq_dqs_rx_rdqs_pi_1_m1_r0_cfg[`DDR_CA_DQS_RX_RDQS_PI_1_M1_R0_CFG_RANGE]: rcs ?
         dq_dqs_rx_rdqs_pi_1_m0_r1_cfg[`DDR_CA_DQS_RX_RDQS_PI_1_M0_R1_CFG_RANGE]:
         dq_dqs_rx_rdqs_pi_1_m0_r0_cfg[`DDR_CA_DQS_RX_RDQS_PI_1_M0_R0_CFG_RANGE];

   assign dq_dqs_rx_pi_sta[`DDR_CA_DQS_RX_PI_STA_REN_PI_PHASE_FIELD] = i_dqs_ren_pi_phase_sta;
   assign dq_dqs_rx_pi_sta[`DDR_CA_DQS_RX_PI_STA_RCS_PI_PHASE_FIELD] = i_dqs_rcs_pi_phase_sta;

   assign o_dqs_pad_rx_cfg  = msr ? rcs ?
      {
         dq_dqs_rx_io_m1_r1_cfg_0[`DDR_CA_DQS_RX_IO_M1_R1_CFG_0_RANGE]
      }:
      {
         dq_dqs_rx_io_m1_r0_cfg_0[`DDR_CA_DQS_RX_IO_M1_R0_CFG_0_RANGE]
       } : rcs ?
      {
         dq_dqs_rx_io_m0_r1_cfg_0[`DDR_CA_DQS_RX_IO_M0_R1_CFG_0_RANGE]
      }:
      {
         dq_dqs_rx_io_m0_r0_cfg_0[`DDR_CA_DQS_RX_IO_M0_R0_CFG_0_RANGE]
      };
   assign o_dqs_pad_rx_cmn_cfg  = msr ? rcs ?
         dq_dqs_rx_io_cmn_m1_r1_cfg[`DDR_CA_DQS_RX_IO_CMN_M1_R1_CFG_RANGE]:
         dq_dqs_rx_io_cmn_m1_r0_cfg[`DDR_CA_DQS_RX_IO_CMN_M1_R0_CFG_RANGE]: rcs ?
         dq_dqs_rx_io_cmn_m0_r1_cfg[`DDR_CA_DQS_RX_IO_CMN_M0_R1_CFG_RANGE]:
         dq_dqs_rx_io_cmn_m0_r0_cfg[`DDR_CA_DQS_RX_IO_CMN_M0_R0_CFG_RANGE];
   assign o_dqs_sa_cfg = msr ? rcs ?
      {
         dq_dqs_rx_sa_m1_r1_cfg_0[`DDR_CA_DQS_RX_SA_M1_R1_CFG_0_RANGE]
      }:
      {
         dq_dqs_rx_sa_m1_r0_cfg_0[`DDR_CA_DQS_RX_SA_M1_R0_CFG_0_RANGE]
       } : rcs ?
      {
         dq_dqs_rx_sa_m0_r1_cfg_0[`DDR_CA_DQS_RX_SA_M0_R1_CFG_0_RANGE]
      }:
      {
         dq_dqs_rx_sa_m0_r0_cfg_0[`DDR_CA_DQS_RX_SA_M0_R0_CFG_0_RANGE]
      };
//   assign o_dqs_sa_cmn_cfg = rcs ?
//         dq_dqs_rx_sa_cmn_r1_cfg[`DDR_CA_DQS_RX_SA_CMN_R1_CFG_RANGE]:
//         dq_dqs_rx_sa_cmn_r0_cfg[`DDR_CA_DQS_RX_SA_CMN_R0_CFG_RANGE];
   assign o_dqs_sa_cmn_cfg = dq_dqs_rx_sa_cmn_cfg[`DDR_CA_DQS_RX_SA_CMN_CFG_RANGE];

`ifdef DDR_DQS_VREF
   assign o_dqs_refgen_cfg = msr ? rcs ?
         dq_dqs_rx_refgen_m1_r1_cfg[`DDR_CA_DQS_RX_REFGEN_M1_R1_CFG_RANGE]:
         dq_dqs_rx_refgen_m1_r0_cfg[`DDR_CA_DQS_RX_REFGEN_M1_R0_CFG_RANGE]: rcs ?
         dq_dqs_rx_refgen_m0_r1_cfg[`DDR_CA_DQS_RX_REFGEN_M0_R1_CFG_RANGE]:
         dq_dqs_rx_refgen_m0_r0_cfg[`DDR_CA_DQS_RX_REFGEN_M0_R0_CFG_RANGE];
`endif

   assign dq_dqs_rx_io_sta[`DDR_CA_DQS_RX_IO_STA_RANGE] = i_dqs_io_sta;

   // ---------------------------------------------------------
   // DQS TX
   // ---------------------------------------------------------
   //
   assign dqs_tgb_mode = msr ?
         cast_dgb_t(dq_dqs_tx_m1_cfg[`DDR_CA_DQS_TX_M1_CFG_TGB_MODE_FIELD]):
         cast_dgb_t(dq_dqs_tx_m0_cfg[`DDR_CA_DQS_TX_M0_CFG_TGB_MODE_FIELD]);
   assign dqs_wgb_mode = msr ?
         cast_wgb_t(dq_dqs_tx_m1_cfg[`DDR_CA_DQS_TX_M1_CFG_WGB_MODE_FIELD]):
         cast_wgb_t(dq_dqs_tx_m0_cfg[`DDR_CA_DQS_TX_M0_CFG_WGB_MODE_FIELD]);
   assign dqs_ck2wck_ratio = msr ?
         cast_ck2wck_ratio_t(dq_dqs_tx_m1_cfg[`DDR_CA_DQS_TX_M1_CFG_CK2WCK_RATIO_FIELD]):
         cast_ck2wck_ratio_t(dq_dqs_tx_m0_cfg[`DDR_CA_DQS_TX_M0_CFG_CK2WCK_RATIO_FIELD]);

   always_comb begin
      case(dqs_tgb_mode)
        DGB_8TO1_HF : o_dqs_tgb_mode = {{(DEC_DGBWIDTH-1){1'b0}},1'b1} << `DGB_8TO1_HF_IDX ;
        DGB_8TO1_LF : o_dqs_tgb_mode = {{(DEC_DGBWIDTH-1){1'b0}},1'b1} << `DGB_8TO1_LF_IDX ;
        //DGB_4TO1_IR : o_dqs_tgb_mode = {{(DEC_DGBWIDTH-1){1'b0}},1'b1} << `DGB_4TO1_IR_IDX ;
        DGB_4TO1_HF : o_dqs_tgb_mode = {{(DEC_DGBWIDTH-1){1'b0}},1'b1} << `DGB_4TO1_HF_IDX ;
        DGB_4TO1_LF : o_dqs_tgb_mode = {{(DEC_DGBWIDTH-1){1'b0}},1'b1} << `DGB_4TO1_LF_IDX ;
        //DGB_2TO1_IR : o_dqs_tgb_mode = {{(DEC_DGBWIDTH-1){1'b0}},1'b1} << `DGB_2TO1_IR_IDX ;
        DGB_2TO1_HF : o_dqs_tgb_mode = {{(DEC_DGBWIDTH-1){1'b0}},1'b1} << `DGB_2TO1_HF_IDX ;
        DGB_1TO1_HF : o_dqs_tgb_mode = {{(DEC_DGBWIDTH-1){1'b0}},1'b1} << `DGB_1TO1_HF_IDX ;
        default     : o_dqs_tgb_mode = {{(DEC_DGBWIDTH-1){1'b0}},1'b1} << `DGB_1TO1_HF_IDX ;
      endcase
   end

   always_comb begin
      case(dqs_wgb_mode)
         WGB_16TO8 : o_dqs_wgb_mode = {{(DEC_WGBWIDTH-1){1'b0}},1'b1} << `WGB_16TO8_IDX ;
         WGB_8TO8  : o_dqs_wgb_mode = {{(DEC_WGBWIDTH-1){1'b0}},1'b1} << `WGB_8TO8_IDX ;
         WGB_8TO4  : o_dqs_wgb_mode = {{(DEC_WGBWIDTH-1){1'b0}},1'b1} << `WGB_8TO4_IDX ;
         WGB_4TO4  : o_dqs_wgb_mode = {{(DEC_WGBWIDTH-1){1'b0}},1'b1} << `WGB_4TO4_IDX ;
         WGB_8TO2  : o_dqs_wgb_mode = {{(DEC_WGBWIDTH-1){1'b0}},1'b1} << `WGB_8TO2_IDX ;
         WGB_4TO2  : o_dqs_wgb_mode = {{(DEC_WGBWIDTH-1){1'b0}},1'b1} << `WGB_4TO2_IDX ;
         WGB_2TO2  : o_dqs_wgb_mode = {{(DEC_WGBWIDTH-1){1'b0}},1'b1} << `WGB_2TO2_IDX ;
         WGB_8TO1  : o_dqs_wgb_mode = {{(DEC_WGBWIDTH-1){1'b0}},1'b1} << `WGB_8TO1_IDX ;
         WGB_4TO1  : o_dqs_wgb_mode = {{(DEC_WGBWIDTH-1){1'b0}},1'b1} << `WGB_4TO1_IDX ;
         WGB_2TO1  : o_dqs_wgb_mode = {{(DEC_WGBWIDTH-1){1'b0}},1'b1} << `WGB_2TO1_IDX ;
         WGB_1TO1  : o_dqs_wgb_mode = {{(DEC_WGBWIDTH-1){1'b0}},1'b1} << `WGB_1TO1_IDX ;
         default   : o_dqs_wgb_mode = {{(DEC_WGBWIDTH-1){1'b0}},1'b1} << `WGB_1TO1_IDX ;
      endcase
   end

   always_comb begin
      case(dqs_ck2wck_ratio)
        CK2WCK_1TO4 : o_dqs_ck2wck_ratio = {{(DEC_CK2WCKRWIDTH-1){1'b0}},1'b1} << `CK2WCK_1TO4_IDX ;
        CK2WCK_1TO2 : o_dqs_ck2wck_ratio = {{(DEC_CK2WCKRWIDTH-1){1'b0}},1'b1} << `CK2WCK_1TO2_IDX ;
        CK2WCK_1TO1 : o_dqs_ck2wck_ratio = {{(DEC_CK2WCKRWIDTH-1){1'b0}},1'b1} << `CK2WCK_1TO1_IDX ;
        default     : o_dqs_ck2wck_ratio = {{(DEC_CK2WCKRWIDTH-1){1'b0}},1'b1} << `CK2WCK_1TO1_IDX ;
      endcase
   end

   assign o_dqs_bscan_ctrl = dq_dqs_tx_bscan_ctrl_cfg[`DDR_CA_DQS_TX_BSCAN_CTRL_CFG_RANGE];
   assign o_dqs_egress_bscan = dq_dqs_tx_bscan_cfg[`DDR_CA_DQS_TX_BSCAN_CFG_VAL_FIELD];
   assign o_dqs_egress_mode_ana = i_bscan_mode ? ({{(E0WIDTH-1){1'b0}},1'b1} << `DDR_ANA_EGRESS_BYPASS ) : msr ?
      {
         dq_dqs_tx_egress_ana_m1_cfg_0[`DDR_CA_DQS_TX_EGRESS_ANA_M1_CFG_0_EGRESS_MODE_FIELD]
      }:
      {
         dq_dqs_tx_egress_ana_m0_cfg_0[`DDR_CA_DQS_TX_EGRESS_ANA_M0_CFG_0_EGRESS_MODE_FIELD]
      };
   assign o_dqs_egress_mode_dig = i_bscan_mode ? ({{(E1WIDTH-1){1'b0}},1'b1} << `DDR_DIG_EGRESS_BSCAN ) : msr ?
      {
         dq_dqs_tx_egress_dig_m1_cfg_0[`DDR_CA_DQS_TX_EGRESS_DIG_M1_CFG_0_EGRESS_MODE_FIELD]
      }:
      {
         dq_dqs_tx_egress_dig_m0_cfg_0[`DDR_CA_DQS_TX_EGRESS_DIG_M0_CFG_0_EGRESS_MODE_FIELD]
      };
   assign dqs_qdr_pi_0_cfg = msr ? wcs ?
         dq_dqs_tx_qdr_pi_0_m1_r1_cfg[`DDR_CA_DQS_TX_QDR_PI_0_M1_R1_CFG_RANGE]:
         dq_dqs_tx_qdr_pi_0_m1_r0_cfg[`DDR_CA_DQS_TX_QDR_PI_0_M1_R0_CFG_RANGE]: wcs ?
         dq_dqs_tx_qdr_pi_0_m0_r1_cfg[`DDR_CA_DQS_TX_QDR_PI_0_M0_R1_CFG_RANGE]:
         dq_dqs_tx_qdr_pi_0_m0_r0_cfg[`DDR_CA_DQS_TX_QDR_PI_0_M0_R0_CFG_RANGE];
   assign dqs_qdr_pi_1_cfg = msr ? wcs ?
         dq_dqs_tx_qdr_pi_1_m1_r1_cfg[`DDR_CA_DQS_TX_QDR_PI_1_M1_R1_CFG_RANGE]:
         dq_dqs_tx_qdr_pi_1_m1_r0_cfg[`DDR_CA_DQS_TX_QDR_PI_1_M1_R0_CFG_RANGE]: wcs ?
         dq_dqs_tx_qdr_pi_1_m0_r1_cfg[`DDR_CA_DQS_TX_QDR_PI_1_M0_R1_CFG_RANGE]:
         dq_dqs_tx_qdr_pi_1_m0_r0_cfg[`DDR_CA_DQS_TX_QDR_PI_1_M0_R0_CFG_RANGE];
   assign dqs_ddr_pi_0_cfg = msr ? wcs ?
         dq_dqs_tx_ddr_pi_0_m1_r1_cfg[`DDR_CA_DQS_TX_DDR_PI_0_M1_R1_CFG_RANGE]:
         dq_dqs_tx_ddr_pi_0_m1_r0_cfg[`DDR_CA_DQS_TX_DDR_PI_0_M1_R0_CFG_RANGE]: wcs ?
         dq_dqs_tx_ddr_pi_0_m0_r1_cfg[`DDR_CA_DQS_TX_DDR_PI_0_M0_R1_CFG_RANGE]:
         dq_dqs_tx_ddr_pi_0_m0_r0_cfg[`DDR_CA_DQS_TX_DDR_PI_0_M0_R0_CFG_RANGE];
   assign dqs_ddr_pi_1_cfg = msr ? wcs ?
         dq_dqs_tx_ddr_pi_1_m1_r1_cfg[`DDR_CA_DQS_TX_DDR_PI_1_M1_R1_CFG_RANGE]:
         dq_dqs_tx_ddr_pi_1_m1_r0_cfg[`DDR_CA_DQS_TX_DDR_PI_1_M1_R0_CFG_RANGE]: wcs ?
         dq_dqs_tx_ddr_pi_1_m0_r1_cfg[`DDR_CA_DQS_TX_DDR_PI_1_M0_R1_CFG_RANGE]:
         dq_dqs_tx_ddr_pi_1_m0_r0_cfg[`DDR_CA_DQS_TX_DDR_PI_1_M0_R0_CFG_RANGE];
   assign dqs_sdr_rt_pi_cfg = msr ? wcs ?
         dq_dqs_tx_pi_rt_m1_r1_cfg[`DDR_CA_DQS_TX_PI_RT_M1_R1_CFG_RANGE]:
         dq_dqs_tx_pi_rt_m1_r0_cfg[`DDR_CA_DQS_TX_PI_RT_M1_R0_CFG_RANGE]: wcs ?
         dq_dqs_tx_pi_rt_m0_r1_cfg[`DDR_CA_DQS_TX_PI_RT_M0_R1_CFG_RANGE]:
         dq_dqs_tx_pi_rt_m0_r0_cfg[`DDR_CA_DQS_TX_PI_RT_M0_R0_CFG_RANGE];
   assign sdr_pi_cfg = msr ? wcs ?
         dq_dqs_tx_sdr_pi_m1_r1_cfg[`DDR_CA_DQS_TX_SDR_PI_M1_R1_CFG_RANGE]:
         dq_dqs_tx_sdr_pi_m1_r0_cfg[`DDR_CA_DQS_TX_SDR_PI_M1_R0_CFG_RANGE]: wcs ?
         dq_dqs_tx_sdr_pi_m0_r1_cfg[`DDR_CA_DQS_TX_SDR_PI_M0_R1_CFG_RANGE]:
         dq_dqs_tx_sdr_pi_m0_r0_cfg[`DDR_CA_DQS_TX_SDR_PI_M0_R0_CFG_RANGE];
   assign dfi_pi_cfg = msr ? wcs ?
         dq_dqs_tx_dfi_pi_m1_r1_cfg[`DDR_CA_DQS_TX_DFI_PI_M1_R1_CFG_RANGE]:
         dq_dqs_tx_dfi_pi_m1_r0_cfg[`DDR_CA_DQS_TX_DFI_PI_M1_R0_CFG_RANGE]: wcs ?
         dq_dqs_tx_dfi_pi_m0_r1_cfg[`DDR_CA_DQS_TX_DFI_PI_M0_R1_CFG_RANGE]:
         dq_dqs_tx_dfi_pi_m0_r0_cfg[`DDR_CA_DQS_TX_DFI_PI_M0_R0_CFG_RANGE];
   assign o_dqs_sdr_rt_pipe_en = msr ? wcs ?
         dq_dqs_tx_rt_m1_r1_cfg[`DDR_CA_DQS_TX_RT_M1_R1_CFG_PIPE_EN_FIELD]:
         dq_dqs_tx_rt_m1_r0_cfg[`DDR_CA_DQS_TX_RT_M1_R0_CFG_PIPE_EN_FIELD]: wcs ?
         dq_dqs_tx_rt_m0_r1_cfg[`DDR_CA_DQS_TX_RT_M0_R1_CFG_PIPE_EN_FIELD]:
         dq_dqs_tx_rt_m0_r0_cfg[`DDR_CA_DQS_TX_RT_M0_R0_CFG_PIPE_EN_FIELD];

logic [1-1:0] cs;
genvar i;
generate
  for(i=0; i< 1; i=i+1) begin : SLICE
    if((i == `DDR_DQS_REN_IDX) || (i == `DDR_DQS_RE_IDX) || (i == `DDR_DQS_IE_IDX) || (i == `DDR_DQS_RCS_IDX)) begin : RCS
      assign cs[i] = rcs;
    end else begin : WCS
      assign cs[i] = wcs;
    end
  end
endgenerate

   assign o_dqs_sdr_0_pipe_en = msr ?
      {
         (cs[0] ? dq_dqs_tx_sdr_m1_r1_cfg_0[`DDR_CA_DQS_TX_SDR_M1_R1_CFG_0_PIPE_EN_P0_FIELD] : dq_dqs_tx_sdr_m1_r0_cfg_0[`DDR_CA_DQS_TX_SDR_M1_R0_CFG_0_PIPE_EN_P0_FIELD])
      } :
      {
         (cs[0] ? dq_dqs_tx_sdr_m0_r1_cfg_0[`DDR_CA_DQS_TX_SDR_M0_R1_CFG_0_PIPE_EN_P0_FIELD] : dq_dqs_tx_sdr_m0_r0_cfg_0[`DDR_CA_DQS_TX_SDR_M0_R0_CFG_0_PIPE_EN_P0_FIELD])
      };
   assign o_dqs_sdr_1_pipe_en = msr ?
      {
         (cs[0] ? dq_dqs_tx_sdr_m1_r1_cfg_0[`DDR_CA_DQS_TX_SDR_M1_R1_CFG_0_PIPE_EN_P1_FIELD] : dq_dqs_tx_sdr_m1_r0_cfg_0[`DDR_CA_DQS_TX_SDR_M1_R0_CFG_0_PIPE_EN_P1_FIELD])
      } :
      {
         (cs[0] ? dq_dqs_tx_sdr_m0_r1_cfg_0[`DDR_CA_DQS_TX_SDR_M0_R1_CFG_0_PIPE_EN_P1_FIELD] : dq_dqs_tx_sdr_m0_r0_cfg_0[`DDR_CA_DQS_TX_SDR_M0_R0_CFG_0_PIPE_EN_P1_FIELD])
      };
   assign o_dqs_sdr_2_pipe_en = msr ?
      {
         (cs[0] ? dq_dqs_tx_sdr_m1_r1_cfg_0[`DDR_CA_DQS_TX_SDR_M1_R1_CFG_0_PIPE_EN_P2_FIELD] : dq_dqs_tx_sdr_m1_r0_cfg_0[`DDR_CA_DQS_TX_SDR_M1_R0_CFG_0_PIPE_EN_P2_FIELD])
      } :
      {
         (cs[0] ? dq_dqs_tx_sdr_m0_r1_cfg_0[`DDR_CA_DQS_TX_SDR_M0_R1_CFG_0_PIPE_EN_P2_FIELD] : dq_dqs_tx_sdr_m0_r0_cfg_0[`DDR_CA_DQS_TX_SDR_M0_R0_CFG_0_PIPE_EN_P2_FIELD])
      };
   assign o_dqs_sdr_3_pipe_en = msr ?
      {
         (cs[0] ? dq_dqs_tx_sdr_m1_r1_cfg_0[`DDR_CA_DQS_TX_SDR_M1_R1_CFG_0_PIPE_EN_P3_FIELD] : dq_dqs_tx_sdr_m1_r0_cfg_0[`DDR_CA_DQS_TX_SDR_M1_R0_CFG_0_PIPE_EN_P3_FIELD])
      } :
      {
         (cs[0] ? dq_dqs_tx_sdr_m0_r1_cfg_0[`DDR_CA_DQS_TX_SDR_M0_R1_CFG_0_PIPE_EN_P3_FIELD] : dq_dqs_tx_sdr_m0_r0_cfg_0[`DDR_CA_DQS_TX_SDR_M0_R0_CFG_0_PIPE_EN_P3_FIELD])
      };
   assign dqs_sdr_0_x_sel = msr ?
      {
         (cs[0] ? dq_dqs_tx_sdr_x_sel_m1_r1_cfg_0[`DDR_CA_DQS_TX_SDR_X_SEL_M1_R1_CFG_0_X_SEL_P0_FIELD] : dq_dqs_tx_sdr_x_sel_m1_r0_cfg_0[`DDR_CA_DQS_TX_SDR_X_SEL_M1_R0_CFG_0_X_SEL_P0_FIELD])
      } :
      {
         (cs[0] ? dq_dqs_tx_sdr_x_sel_m0_r1_cfg_0[`DDR_CA_DQS_TX_SDR_X_SEL_M0_R1_CFG_0_X_SEL_P0_FIELD] : dq_dqs_tx_sdr_x_sel_m0_r0_cfg_0[`DDR_CA_DQS_TX_SDR_X_SEL_M0_R0_CFG_0_X_SEL_P0_FIELD])
      };
   assign dqs_sdr_1_x_sel = msr ?
      {
         (cs[0] ? dq_dqs_tx_sdr_x_sel_m1_r1_cfg_0[`DDR_CA_DQS_TX_SDR_X_SEL_M1_R1_CFG_0_X_SEL_P1_FIELD] : dq_dqs_tx_sdr_x_sel_m1_r0_cfg_0[`DDR_CA_DQS_TX_SDR_X_SEL_M1_R0_CFG_0_X_SEL_P1_FIELD])
      } :
      {
         (cs[0] ? dq_dqs_tx_sdr_x_sel_m0_r1_cfg_0[`DDR_CA_DQS_TX_SDR_X_SEL_M0_R1_CFG_0_X_SEL_P1_FIELD] : dq_dqs_tx_sdr_x_sel_m0_r0_cfg_0[`DDR_CA_DQS_TX_SDR_X_SEL_M0_R0_CFG_0_X_SEL_P1_FIELD])
      };
   assign dqs_sdr_2_x_sel = msr ?
      {
         (cs[0] ? dq_dqs_tx_sdr_x_sel_m1_r1_cfg_0[`DDR_CA_DQS_TX_SDR_X_SEL_M1_R1_CFG_0_X_SEL_P2_FIELD] : dq_dqs_tx_sdr_x_sel_m1_r0_cfg_0[`DDR_CA_DQS_TX_SDR_X_SEL_M1_R0_CFG_0_X_SEL_P2_FIELD])
      } :
      {
         (cs[0] ? dq_dqs_tx_sdr_x_sel_m0_r1_cfg_0[`DDR_CA_DQS_TX_SDR_X_SEL_M0_R1_CFG_0_X_SEL_P2_FIELD] : dq_dqs_tx_sdr_x_sel_m0_r0_cfg_0[`DDR_CA_DQS_TX_SDR_X_SEL_M0_R0_CFG_0_X_SEL_P2_FIELD])
      };
   assign dqs_sdr_3_x_sel = msr ?
      {
         (cs[0] ? dq_dqs_tx_sdr_x_sel_m1_r1_cfg_0[`DDR_CA_DQS_TX_SDR_X_SEL_M1_R1_CFG_0_X_SEL_P3_FIELD] : dq_dqs_tx_sdr_x_sel_m1_r0_cfg_0[`DDR_CA_DQS_TX_SDR_X_SEL_M1_R0_CFG_0_X_SEL_P3_FIELD])
      } :
      {
         (cs[0] ? dq_dqs_tx_sdr_x_sel_m0_r1_cfg_0[`DDR_CA_DQS_TX_SDR_X_SEL_M0_R1_CFG_0_X_SEL_P3_FIELD] : dq_dqs_tx_sdr_x_sel_m0_r0_cfg_0[`DDR_CA_DQS_TX_SDR_X_SEL_M0_R0_CFG_0_X_SEL_P3_FIELD])
      };
   assign o_dqs_sdr_0_x_sel = {
         dqs_sdr_0_x_sel[(MAX_MXWIDTH)*0+:MXWIDTH]
      };
   assign o_dqs_sdr_1_x_sel = {
         dqs_sdr_1_x_sel[(MAX_MXWIDTH)*0+:MXWIDTH]
      };
   assign o_dqs_sdr_2_x_sel = {
         dqs_sdr_2_x_sel[(MAX_MXWIDTH)*0+:MXWIDTH]
      };
   assign o_dqs_sdr_3_x_sel = {
         dqs_sdr_3_x_sel[(MAX_MXWIDTH)*0+:MXWIDTH]
      };
   assign o_dqs_sdr_0_fc_dly = msr ?
      {
         (cs[0] ? dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_0[`DDR_CA_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0_DLY_P0_FIELD] : dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_0[`DDR_CA_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0_DLY_P0_FIELD])
      }:
      {
         (cs[0] ? dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_0[`DDR_CA_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0_DLY_P0_FIELD] : dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_0[`DDR_CA_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0_DLY_P0_FIELD])
      };
   assign o_dqs_sdr_1_fc_dly = msr ?
      {
         (cs[0] ? dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_0[`DDR_CA_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0_DLY_P1_FIELD] : dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_0[`DDR_CA_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0_DLY_P1_FIELD])
      }:
      {
         (cs[0] ? dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_0[`DDR_CA_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0_DLY_P1_FIELD] : dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_0[`DDR_CA_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0_DLY_P1_FIELD])
      };
   assign o_dqs_sdr_2_fc_dly = msr ?
      {
         (cs[0] ? dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_0[`DDR_CA_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0_DLY_P2_FIELD] : dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_0[`DDR_CA_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0_DLY_P2_FIELD])
      }:
      {
         (cs[0] ? dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_0[`DDR_CA_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0_DLY_P2_FIELD] : dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_0[`DDR_CA_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0_DLY_P2_FIELD])
      };
   assign o_dqs_sdr_3_fc_dly = msr ?
      {
         (cs[0] ? dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_0[`DDR_CA_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0_DLY_P3_FIELD] : dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_0[`DDR_CA_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0_DLY_P3_FIELD])
      }:
      {
         (cs[0] ? dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_0[`DDR_CA_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0_DLY_P3_FIELD] : dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_0[`DDR_CA_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0_DLY_P3_FIELD])
      };
   assign dqs_ddr_0_x_sel = msr ?
      {
         (cs[0] ? dq_dqs_tx_ddr_x_sel_m1_r1_cfg_0[`DDR_CA_DQS_TX_DDR_X_SEL_M1_R1_CFG_0_X_SEL_P0_FIELD] : dq_dqs_tx_ddr_x_sel_m1_r0_cfg_0[`DDR_CA_DQS_TX_DDR_X_SEL_M1_R0_CFG_0_X_SEL_P0_FIELD])
      }:
      {
         (cs[0] ? dq_dqs_tx_ddr_x_sel_m0_r1_cfg_0[`DDR_CA_DQS_TX_DDR_X_SEL_M0_R1_CFG_0_X_SEL_P0_FIELD] : dq_dqs_tx_ddr_x_sel_m0_r0_cfg_0[`DDR_CA_DQS_TX_DDR_X_SEL_M0_R0_CFG_0_X_SEL_P0_FIELD])
      };
   assign dqs_ddr_1_x_sel = msr ?
      {
         (cs[0] ? dq_dqs_tx_ddr_x_sel_m1_r1_cfg_0[`DDR_CA_DQS_TX_DDR_X_SEL_M1_R1_CFG_0_X_SEL_P1_FIELD] : dq_dqs_tx_ddr_x_sel_m1_r0_cfg_0[`DDR_CA_DQS_TX_DDR_X_SEL_M1_R0_CFG_0_X_SEL_P1_FIELD])
      }:
      {
         (cs[0] ? dq_dqs_tx_ddr_x_sel_m0_r1_cfg_0[`DDR_CA_DQS_TX_DDR_X_SEL_M0_R1_CFG_0_X_SEL_P1_FIELD] : dq_dqs_tx_ddr_x_sel_m0_r0_cfg_0[`DDR_CA_DQS_TX_DDR_X_SEL_M0_R0_CFG_0_X_SEL_P1_FIELD])
      };
   assign o_dqs_ddr_0_x_sel = {
         dqs_ddr_0_x_sel[(MAX_MXWIDTH-1)*0+:(MXWIDTH-1)]
      };
   assign o_dqs_ddr_1_x_sel = {
         dqs_ddr_1_x_sel[(MAX_MXWIDTH-1)*0+:(MXWIDTH-1)]
      };
   assign o_dqs_ddr_0_pipe_en = msr ?
      {
         (cs[0] ? dq_dqs_tx_ddr_m1_r1_cfg_0[`DDR_CA_DQS_TX_DDR_M1_R1_CFG_0_PIPE_EN_P0_FIELD] : dq_dqs_tx_ddr_m1_r0_cfg_0[`DDR_CA_DQS_TX_DDR_M1_R0_CFG_0_PIPE_EN_P0_FIELD])
      }:
      {
         (cs[0] ? dq_dqs_tx_ddr_m0_r1_cfg_0[`DDR_CA_DQS_TX_DDR_M0_R1_CFG_0_PIPE_EN_P0_FIELD] : dq_dqs_tx_ddr_m0_r0_cfg_0[`DDR_CA_DQS_TX_DDR_M0_R0_CFG_0_PIPE_EN_P0_FIELD])
      };
   assign o_dqs_ddr_1_pipe_en = msr ?
      {
         (cs[0] ? dq_dqs_tx_ddr_m1_r1_cfg_0[`DDR_CA_DQS_TX_DDR_M1_R1_CFG_0_PIPE_EN_P1_FIELD] : dq_dqs_tx_ddr_m1_r0_cfg_0[`DDR_CA_DQS_TX_DDR_M1_R0_CFG_0_PIPE_EN_P1_FIELD])
      }:
      {
         (cs[0] ? dq_dqs_tx_ddr_m0_r1_cfg_0[`DDR_CA_DQS_TX_DDR_M0_R1_CFG_0_PIPE_EN_P1_FIELD] : dq_dqs_tx_ddr_m0_r0_cfg_0[`DDR_CA_DQS_TX_DDR_M0_R0_CFG_0_PIPE_EN_P1_FIELD])
      };
   assign o_dqs_xdr_lpde_cfg = msr ? wcs ?
      {
         dq_dqs_tx_lpde_m1_r1_cfg_0[`DDR_CA_DQS_TX_LPDE_M1_R1_CFG_0_RANGE]
      }:
      {
         dq_dqs_tx_lpde_m1_r0_cfg_0[`DDR_CA_DQS_TX_LPDE_M1_R0_CFG_0_RANGE]
       } : wcs ?
      {
         dq_dqs_tx_lpde_m0_r1_cfg_0[`DDR_CA_DQS_TX_LPDE_M0_R1_CFG_0_RANGE]
      }:
      {
         dq_dqs_tx_lpde_m0_r0_cfg_0[`DDR_CA_DQS_TX_LPDE_M0_R0_CFG_0_RANGE]
      };
   //assign o_dqs_pad_tx_cfg  = msr ? wcs ?
   //   {
   //`for (j=`DDR_NUM_TXRX_CK_SLICES-1; j>0; j--)
   //      dq_dqs_tx_io_m1_r1_cfg_`j[`DDR_CA_DQS_TX_IO_M1_R1_CFG_`j::_RANGE],
   //`endfor
   //      dq_dqs_tx_io_m1_r1_cfg_0[`DDR_CA_DQS_TX_IO_M1_R1_CFG_0_RANGE]
   //   }:
   //   {
   //`for (j=`DDR_NUM_TXRX_CK_SLICES-1; j>0; j--)
   //      dq_dqs_tx_io_m1_r0_cfg_`j[`DDR_CA_DQS_TX_IO_M1_R0_CFG_`j::_RANGE],
   //`endfor
   //      dq_dqs_tx_io_m1_r0_cfg_0[`DDR_CA_DQS_TX_IO_M1_R0_CFG_0_RANGE]
   //    } : wcs ?
   //   {
   //`for (j=`DDR_NUM_TXRX_CK_SLICES-1; j>0; j--)
   //      dq_dqs_tx_io_m0_r1_cfg_`j[`DDR_CA_DQS_TX_IO_M0_R1_CFG_`j::_RANGE],
   //`endfor
   //      dq_dqs_tx_io_m0_r1_cfg_0[`DDR_CA_DQS_TX_IO_M0_R1_CFG_0_RANGE]
   //   }:
   //   {
   //`for (j=`DDR_NUM_TXRX_CK_SLICES-1; j>0; j--)
   //      dq_dqs_tx_io_m0_r0_cfg_`j[`DDR_CA_DQS_TX_IO_M0_R0_CFG_`j::_RANGE],
   //`endfor
   //      dq_dqs_tx_io_m0_r0_cfg_0[`DDR_CA_DQS_TX_IO_M0_R0_CFG_0_RANGE]
   //   };
   assign o_dqs_pad_tx_cfg  = msr ?
      {
         dq_dqs_tx_io_m1_cfg_0[`DDR_CA_DQS_TX_IO_M1_CFG_0_RANGE]
      }:
      {
         dq_dqs_tx_io_m0_cfg_0[`DDR_CA_DQS_TX_IO_M0_CFG_0_RANGE]
      };
   assign o_dqs_pad_tx_cmn_cfg = (msr ? wcs ?
         dq_dqs_tx_io_cmn_m1_r1_cfg[`DDR_CA_DQS_TX_IO_CMN_M1_R1_CFG_RANGE]:
         dq_dqs_tx_io_cmn_m1_r0_cfg[`DDR_CA_DQS_TX_IO_CMN_M1_R0_CFG_RANGE]: wcs ?
         dq_dqs_tx_io_cmn_m0_r1_cfg[`DDR_CA_DQS_TX_IO_CMN_M0_R1_CFG_RANGE]:
         dq_dqs_tx_io_cmn_m0_r0_cfg[`DDR_CA_DQS_TX_IO_CMN_M0_R0_CFG_RANGE]);

endmodule
