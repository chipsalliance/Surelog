
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
`include "ddr_dq_csr_defs.vh"

import ddr_global_pkg::*;

module ddr_phy_dq #(
   parameter [0:0]           CA_TYPE              =  1'b0,                                           // CA byte type enable
   parameter                 AHB_AWIDTH           =  32,                                             // AHB Address width
   parameter                 NUM_RDPH             =  (0 == 1) ? 4:
                                                     (4 > 4) ? 4 :
                                                     4 ,                       // Read datapath data phases (includes R/F)
   parameter                 NUM_RPH              =  8,                       // Read fifo data phases (includes R/F)
   parameter                 NUM_WDPH             =  4,                        // Write datapath data phases (includes R/F)
   parameter                 NUM_WPH              =  8,                       // Write gearbox data phases (includes R/F)
   parameter                 DQ_WIDTH             =  9,                             // DQ bus width
   parameter                 DQS_WIDTH            =  9+0,// DQS bus width
   parameter                 FEEDTHR_DQS_WIDTH    =  0,                    // DQS bits that are feedthrough without a slice
   parameter                 DP_DQS_WIDTH         = DQS_WIDTH-FEEDTHR_DQS_WIDTH,                     // DQS bits that are not feedthrough and have TX/RX dp slice
   parameter                 TXRX_DQS_WIDTH       =  2,                       // DQS Slices with TX, RX and LPDE elements
   parameter [0:0]           BYTE_FIFO            =  1'b1,                                           // RX BYTE FIFO enable
   parameter                 DQ_RWIDTH            = NUM_RPH * DQ_WIDTH,                              // DQ read data width
   parameter                 DQS_RWIDTH           = NUM_RPH * DQS_WIDTH,                             // DQS read data width
   parameter                 DQ_WWIDTH            = NUM_WPH * DQ_WIDTH,                              // DQ write data width
   parameter                 DQS_WWIDTH           = NUM_WPH * DQS_WIDTH,                             // DQS write data width
   parameter                 TX0WIDTH             =  12 ,                                            // Tx IO configuration width
   parameter                 TX1WIDTH             =  14,                                             // Tx IO configuration width
   parameter                 RX0WIDTH             =  16,                                             // Rx IO configuration width
   parameter                 RX1WIDTH             =  26,                                             // Rx IO configuration width
   parameter                 A0WIDTH              =  20,                                             // Sense Amp configuration width
   parameter                 A1WIDTH              =  5,                                              // Sense Amp configuration width
   parameter                 A2WIDTH              =  32,                                             // Sense Amp configuration width
`ifdef DDR_DQS_VREF
   parameter                 VWIDTH               =  11,                                             // VREF configuration width
`endif
   parameter                 E0WIDTH              =  6,                                              // TX Egress path mode width (ANA)
   parameter                 E1WIDTH              =  7,                                              // TX Egress path mode width (DIG)
   parameter                 FWIDTH               =  2,                                              // Full cycle delay select width
   parameter                 MXWIDTH              =  3,                                              // Mux-X select width width
   parameter                 LWIDTH               =  9,                                              // LPDE cfg bus width
   parameter                 P0WIDTH              =  15,                                             // PI cfg bus width
   parameter                 P1WIDTH              =  15,                                             // PI Matching cell cfg width
   parameter                 PDWIDTH              =  34,                                             // PI decoded cfg bus width
   parameter                 PS_DLY               =  10,                                             // LPDE NAND delay in picoseconds
   parameter                 FIFO_DEPTH           =  8,                                              // FIFO depth
   parameter                 FREN_WIDTH           =  1*2+1,                                           // RX FIFO Read enable width
   parameter [0:0]           SLICE_FIFO           =  1'b0,                                           // RX SLICE FIFO enable
   parameter                 DFIRDCLKEN_PEXTWIDTH =  4,                                              // DFIRDCLK EN Pulse Extension count width
   parameter [DQ_WIDTH-1:0]  DQ_TX_CKE_MASK       = '1,                                              // TX CKE PAD instance mask
   parameter [DQS_WIDTH-1:0] DQS_TX_DQS_MASK      = '1,                                              // TX DQS PAD instance mask
   parameter [DQS_WIDTH-1:0] DQS_TX_WCK_MASK      = '1                                               // TX WCK PAD instance mask
) (

   // Common Clocks and Reset
   input  logic                            i_rst,

   input  logic                            i_pll_clk_0,                        // External clock - Primary PLL clock ph0
   input  logic                            i_pll_clk_90,                       // External clock - Primary PLL clock ph90
   input  logic                            i_pll_clk_180,                      // External clock - Primary PLL clock ph180
   input  logic                            i_pll_clk_270,                      // External clock - Primary PLL clock ph270
   output logic                            o_phy_clk,                          // External clock - generated by DQS slice

   //Output DFI Clocks generated by DQS Slice
   output logic                            o_dfiwr_clk_1,
   output logic                            o_dfiwr_clk_2,
   output logic                            o_dfird_clk_1,
   output logic                            o_dfird_clk_2,

   //DFI signals
   input  logic                            i_csp_pi_en,
   input  logic                            i_csp_div_rst_n,
   input  logic                            i_dqs_dfi_wrtraffic,
   input  logic                            i_dq_dfi_wrtraffic,
   input  logic [DEC_DFIGBWIDTH-1:0]       i_dfiwrgb_mode,
   input  logic [DEC_DFIGBWIDTH-1:0]       i_dfirdgb_mode,
   input  logic [DFIRDCLKEN_PEXTWIDTH-1:0] i_dfirdclk_en_pulse_ext,
   input  logic                            i_dfirdclk_en_ovr_sel,
   input  logic                            i_dfirdclk_en_ovr,

   // RXFIFO
   output logic                            o_rxfifo_empty_n,
   input  logic [FREN_WIDTH-1:0]           i_rxfifo_read,

   // Mode Select
   input  logic                            i_msr,                              // Mode select

   // Analog
   input  wire                             ana_vref_in,                        // VREF reference

   // TEST
   input  logic                            i_scan_clk,
   input  logic                            i_scan_mode,
   input  logic                            i_scan_en,
   input  logic                            i_scan_cgc_ctrl,
   input  logic                            i_scan_rst_ctrl,
   input  logic                            i_freeze_n,
   input  logic                            i_freeze_n_hv,
   input  logic                            i_hiz_n,
   output logic [3:0]                      o_tst_clk,

   // JTAG Interface
   input  logic                            i_jtag_tck,
   input  logic                            i_jtag_trst_n,
   input  logic                            i_jtag_bsr_mode,
   input  logic                            i_jtag_capture,
   input  logic                            i_jtag_shift,
   input  logic                            i_jtag_update,
   input  logic                            i_jtag_tdi,
   output logic                            o_jtag_tdo,

   // AHB Interface
   input  logic                            i_ahb_clk,
   input  logic                            i_ahb_rst,

   input  logic [AHB_AWIDTH-1:0]           i_ahb_haddr,
   input  logic                            i_ahb_hwrite,
   input  logic                            i_ahb_hsel,
   input  logic [31:0]                     i_ahb_hwdata,
   input  logic [1:0]                      i_ahb_htrans,
   input  logic [2:0]                      i_ahb_hsize,
   input  logic [2:0]                      i_ahb_hburst,
   input  logic                            i_ahb_hreadyin,
   output logic                            o_ahb_hready,
   output logic [31:0]                     o_ahb_hrdata,
   output logic [1:0]                      o_ahb_hresp,

   // DQ Transmitter
   input  logic [DQ_WWIDTH-1:0]            i_dq_sdr,                           // DQ TX data & DBI

   // DQ Receiver
   output logic [DQ_RWIDTH-1:0]            o_dq_sdr,                           // DQ RX data & DBI
   output logic [DQ_WIDTH-1:0]             o_dq_sdr_vld,                       // DQ RX data valid

   // DQS Transmitter
   input  logic [DQS_WWIDTH-1:0]           i_dqs_sdr,                          // DQS TX data & DBI

   // Pads
   inout  wire                             pad_wck_t,                          // WCK
   inout  wire                             pad_wck_c,                          // WCK
   inout  wire                             pad_dqs_t,                          // DQS/RDQS/EDC/PARITY
   inout  wire                             pad_dqs_c,                          // DQS/RDQS/EDC
   inout  wire  [DQ_WIDTH-1:0]             pad_dq                              // DQ/DBI/DM/PARITY

);

   // ------------------------------------------------------------------------
   // CSR - DQ
   // ------------------------------------------------------------------------

   logic [DQS_WIDTH-1:0]               dqs_core_eg;
   logic [4*DQ_WIDTH-1:0]              dq_sa_sta;

   logic [E0WIDTH*DQ_WIDTH-1:0]        dq_egress_mode_ana;
   logic [E1WIDTH*DQ_WIDTH-1:0]        dq_egress_mode_dig;
   logic [DQ_WIDTH-1:0]                dq_sdr_rt_pipe_en;

   logic [FWIDTH*DQ_WIDTH-1:0]         dq_sdr_0_fc_dly;
   logic [MXWIDTH*DQ_WIDTH-1:0]        dq_sdr_0_x_sel;
   logic [DQ_WIDTH-1:0]                dq_sdr_0_pipe_en;
   logic [FWIDTH*DQ_WIDTH-1:0]         dq_sdr_1_fc_dly;
   logic [MXWIDTH*DQ_WIDTH-1:0]        dq_sdr_1_x_sel;
   logic [DQ_WIDTH-1:0]                dq_sdr_1_pipe_en;
   logic [FWIDTH*DQ_WIDTH-1:0]         dq_sdr_2_fc_dly;
   logic [MXWIDTH*DQ_WIDTH-1:0]        dq_sdr_2_x_sel;
   logic [DQ_WIDTH-1:0]                dq_sdr_2_pipe_en;
   logic [FWIDTH*DQ_WIDTH-1:0]         dq_sdr_3_fc_dly;
   logic [MXWIDTH*DQ_WIDTH-1:0]        dq_sdr_3_x_sel;
   logic [DQ_WIDTH-1:0]                dq_sdr_3_pipe_en;
   logic [(MXWIDTH-1)*DQ_WIDTH-1:0]    dq_ddr_0_x_sel;
   logic [DQ_WIDTH-1:0]                dq_ddr_0_pipe_en;
   logic [(MXWIDTH-1)*DQ_WIDTH-1:0]    dq_ddr_1_x_sel;
   logic [DQ_WIDTH-1:0]                dq_ddr_1_pipe_en;
   logic [LWIDTH*DQ_WIDTH-1:0]         dq_xdr_lpde_cfg;
   logic                               dq_fifo_clr;
   logic                               dq_training_mode;
   logic [DEC_DGBWIDTH-1:0]            dq_rgb_mode;
   fgb_t                               dq_fgb_mode;
   logic [RX0WIDTH*DQ_WIDTH-1:0]       dq_pad_rx_cfg;
   logic [TX0WIDTH*DQ_WIDTH-1:0]       dq_pad_tx_cfg;

   logic [E0WIDTH*DP_DQS_WIDTH-1:0]    dqs_egress_mode_ana;
   logic [E1WIDTH*DP_DQS_WIDTH-1:0]    dqs_egress_mode_dig;
   logic [DEC_CK2WCKRWIDTH-1:0]        dqs_ck2wck_ratio;
   logic [DEC_DGBWIDTH-1:0]            dqs_tgb_mode;
   logic [DEC_WGBWIDTH-1:0]            dqs_wgb_mode;
   logic [DEC_DGBWIDTH-1:0]            dqs_rgb_mode;
   fgb_t                               dqs_fgb_mode;
   logic [DP_DQS_WIDTH-1:0]            dqs_sdr_rt_pipe_en;
   logic [FWIDTH*DP_DQS_WIDTH-1:0]     dqs_sdr_0_fc_dly;
   logic [MXWIDTH*DP_DQS_WIDTH-1:0]    dqs_sdr_0_x_sel;
   logic [DP_DQS_WIDTH-1:0]            dqs_sdr_0_pipe_en;
   logic [FWIDTH*DP_DQS_WIDTH-1:0]     dqs_sdr_1_fc_dly;
   logic [MXWIDTH*DP_DQS_WIDTH-1:0]    dqs_sdr_1_x_sel;
   logic [DP_DQS_WIDTH-1:0]            dqs_sdr_1_pipe_en;
   logic [FWIDTH*DP_DQS_WIDTH-1:0]     dqs_sdr_2_fc_dly;
   logic [MXWIDTH*DP_DQS_WIDTH-1:0]    dqs_sdr_2_x_sel;
   logic [DP_DQS_WIDTH-1:0]            dqs_sdr_2_pipe_en;
   logic [FWIDTH*DP_DQS_WIDTH-1:0]     dqs_sdr_3_fc_dly;
   logic [MXWIDTH*DP_DQS_WIDTH-1:0]    dqs_sdr_3_x_sel;
   logic [DP_DQS_WIDTH-1:0]            dqs_sdr_3_pipe_en;
   logic [(MXWIDTH-1)*DP_DQS_WIDTH-1:0]dqs_ddr_0_x_sel;
   logic [DP_DQS_WIDTH-1:0]            dqs_ddr_0_pipe_en;
   logic [(MXWIDTH-1)*DP_DQS_WIDTH-1:0]dqs_ddr_1_x_sel;
   logic [DP_DQS_WIDTH-1:0]            dqs_ddr_1_pipe_en;
   logic [LWIDTH*TXRX_DQS_WIDTH-1:0]   dqs_xdr_lpde_cfg;
   logic [PDWIDTH-1:0]                 dqs_qdr_pi_0_cfg;
   logic [PDWIDTH-1:0]                 dq_qdr_pi_0_cfg;
   logic [PDWIDTH-1:0]                 dqs_qdr_pi_1_cfg;
   logic [PDWIDTH-1:0]                 dq_qdr_pi_1_cfg;
   logic [PDWIDTH-1:0]                 dqs_ddr_pi_0_cfg;
   logic [PDWIDTH-1:0]                 dq_ddr_pi_0_cfg;
   logic [PDWIDTH-1:0]                 dqs_ddr_pi_1_cfg;
   logic [PDWIDTH-1:0]                 dq_ddr_pi_1_cfg;
   logic [PDWIDTH-1:0]                 dqs_sdr_rt_pi_cfg;
   logic [PDWIDTH-1:0]                 dq_sdr_rt_pi_cfg;
   logic [P1WIDTH-1:0]                 sdr_pi_cfg;
   logic [P1WIDTH-1:0]                 dfi_pi_cfg;
   logic [LWIDTH-1:0]                  dqs_sdr_lpde_cfg;
   logic                               dqs_wck_mode;
   logic [1:0]                         dqs_pre_filter_sel;
   logic [PDWIDTH-1:0]                 dqs_ren_pi_cfg;
   logic [PDWIDTH-1:0]                 dqs_rcs_pi_cfg;
   logic [PDWIDTH-1:0]                 dqs_rdqs_pi_0_cfg;
   logic [PDWIDTH-1:0]                 dqs_rdqs_pi_1_cfg;
   logic [RX0WIDTH*TXRX_DQS_WIDTH-1:0] dqs_pad_rx_cfg;
   logic [RX1WIDTH-1:0]                dqs_pad_rx_cmn_cfg;
   logic [TX0WIDTH*TXRX_DQS_WIDTH-1:0] dqs_pad_tx_cfg;
   logic [TX1WIDTH-1:0]                dqs_pad_tx_cmn_cfg;

`ifdef DDR_DQS_VREF
   logic [VWIDTH-1:0]                  dqs_refgen_cfg;
`endif
   logic [A0WIDTH*TXRX_DQS_WIDTH-1:0]  dqs_sa_cfg;
   logic [A1WIDTH-1:0]                 dqs_sa_cmn_cfg;
   logic [A0WIDTH*DQ_WIDTH-1:0]        dq_sa_cfg;
   logic [A2WIDTH*DQ_WIDTH-1:0]        dq_sa_dly_cfg;

   logic [DQ_WIDTH-1:0]                dq_egress_bscan;
   logic [DQ_WIDTH-1:0]                dq_ingress_bscan;
   logic [2*TXRX_DQS_WIDTH-1:0]        dqs_egress_bscan;
   logic [2*TXRX_DQS_WIDTH-1:0]        dqs_ingress_bscan;
   logic [1:0]                         dqs_bscan_ctrl;

   logic [DQ_WIDTH-1:0]                dq_core_ig;
   logic [DP_DQS_WIDTH-1:0]            dqs_core_ig;

`ifndef SYNTHESIS
   wav_ahb_monitor #(
      .AWIDTH                        (AHB_AWIDTH),
      .DWIDTH                        (32)
   ) u_ahb_monitor (
      .i_hclk                        (i_ahb_clk),
      .i_hreset                      (i_ahb_rst),
      .i_hbusreq                     (i_ahb_hsel),
      .i_haddr                       (i_ahb_haddr),
      .i_hwrite                      (i_ahb_hwrite),
      .i_hwdata                      (i_ahb_hwdata),
      .i_htrans                      (i_ahb_htrans),
      .i_hsize                       (i_ahb_hsize),
      .i_hburst                      (i_ahb_hburst),
      .i_hready                      (o_ahb_hready),
      .i_hrdata                      (o_ahb_hrdata),
      .i_hresp                       (o_ahb_hresp)
   );
`endif // SYNTHESIS

   //------------------------------------------------------------------------
   // CSR Wrapper
   // ------------------------------------------------------------------------

   logic wcs;
   logic rcs;
   logic dqs_rcs_pi_phase_sta;
   logic dqs_ren_pi_phase_sta;

   assign wcs = dqs_core_eg[`DDR_DQS_WCS_IDX];

   generate
      if (CA_TYPE) begin : CA_CSR_WRAPPER
         ddr_ca_csr_wrapper #(
            .AHB_AWIDTH                     (AHB_AWIDTH),
            .DQ_WIDTH                       (DQ_WIDTH),
            .DQS_WIDTH                      (DP_DQS_WIDTH),
            .TXRX_DQS_WIDTH                 (TXRX_DQS_WIDTH),
            .TX0WIDTH                       (TX0WIDTH),
            .TX1WIDTH                       (TX1WIDTH),
            .RX0WIDTH                       (RX0WIDTH),
            .RX1WIDTH                       (RX1WIDTH),
            .A0WIDTH                        (A0WIDTH),
            .A1WIDTH                        (A1WIDTH),
            .A2WIDTH                        (A2WIDTH),
         `ifdef DDR_DQS_VREF
            .VWIDTH                         (VWIDTH),
         `endif
            .E0WIDTH                        (E0WIDTH),
            .E1WIDTH                        (E1WIDTH),
            .FWIDTH                         (FWIDTH),
            .MXWIDTH                        (MXWIDTH),
            .LWIDTH                         (LWIDTH),
            .P0WIDTH                        (P0WIDTH),
            .P1WIDTH                        (P1WIDTH),
            .PDWIDTH                        (PDWIDTH)
         ) u_ca_csr_wrapper (

            .i_hclk                         (i_ahb_clk),
            .i_hreset                       (i_ahb_rst),
            .i_haddr                        (i_ahb_haddr),
            .i_hwrite                       (i_ahb_hwrite),
            .i_hsel                         (i_ahb_hsel),
            .i_hwdata                       (i_ahb_hwdata),
            .i_htrans                       (i_ahb_htrans),
            .i_hsize                        (i_ahb_hsize),
            .i_hburst                       (i_ahb_hburst),
            .i_hreadyin                     (i_ahb_hreadyin),
            .o_hready                       (o_ahb_hready),
            .o_hrdata                       (o_ahb_hrdata),
            .o_hresp                        (o_ahb_hresp),

            .i_bscan_mode                   (i_jtag_bsr_mode),
            .i_csp_pi_en                    (i_csp_pi_en),
            .i_wcs                          (1'b0), //wcs),
            .i_rcs                          (1'b0), //rcs),
            .i_msr                          (i_msr),

            // DQ Receiver
            .o_dq_fifo_clr                  (dq_fifo_clr),
            .o_dq_training_mode             (dq_training_mode),
            .i_dq_ingress_bscan             (dq_ingress_bscan),
            .o_dq_rgb_mode                  (),//FIXME:remove
            .o_dq_fgb_mode                  (),//FIXME:remove
            .o_dq_pad_rx_cfg                (dq_pad_rx_cfg),
            .o_dq_pad_tx_cfg                (dq_pad_tx_cfg),
            .o_dq_sa_cfg                    (dq_sa_cfg),
            .o_dq_sa_dly_cfg                (dq_sa_dly_cfg),
            .i_dq_sa_sta                    (dq_sa_sta),
            .i_dq_io_sta                    (dq_core_ig),

            // DQ Transmitter
            .o_dq_egress_bscan              (dq_egress_bscan),
            .o_dq_egress_mode_ana           (dq_egress_mode_ana),
            .o_dq_egress_mode_dig           (dq_egress_mode_dig),
            .o_dq_sdr_rt_pipe_en            (dq_sdr_rt_pipe_en),
            .o_dq_sdr_0_fc_dly              (dq_sdr_0_fc_dly),
            .o_dq_sdr_0_x_sel               (dq_sdr_0_x_sel),
            .o_dq_sdr_0_pipe_en             (dq_sdr_0_pipe_en),
            .o_dq_sdr_1_fc_dly              (dq_sdr_1_fc_dly),
            .o_dq_sdr_1_x_sel               (dq_sdr_1_x_sel),
            .o_dq_sdr_1_pipe_en             (dq_sdr_1_pipe_en),
            .o_dq_sdr_2_fc_dly              (dq_sdr_2_fc_dly),
            .o_dq_sdr_2_x_sel               (dq_sdr_2_x_sel),
            .o_dq_sdr_2_pipe_en             (dq_sdr_2_pipe_en),
            .o_dq_sdr_3_fc_dly              (dq_sdr_3_fc_dly),
            .o_dq_sdr_3_x_sel               (dq_sdr_3_x_sel),
            .o_dq_sdr_3_pipe_en             (dq_sdr_3_pipe_en),
            .o_dq_ddr_0_x_sel               (dq_ddr_0_x_sel),
            .o_dq_ddr_0_pipe_en             (dq_ddr_0_pipe_en),
            .o_dq_ddr_1_x_sel               (dq_ddr_1_x_sel),
            .o_dq_ddr_1_pipe_en             (dq_ddr_1_pipe_en),
            .o_dq_xdr_lpde_cfg              (dq_xdr_lpde_cfg),
            .o_dq_qdr_pi_0_cfg              (dq_qdr_pi_0_cfg),
            .o_dq_qdr_pi_1_cfg              (dq_qdr_pi_1_cfg),  // Floating when not using 4to1 serializer.
            .o_dq_ddr_pi_0_cfg              (dq_ddr_pi_0_cfg),
            .o_dq_ddr_pi_1_cfg              (dq_ddr_pi_1_cfg),  // Floating when not using 4to1 serializer.
            .o_dq_sdr_rt_pi_cfg             (dq_sdr_rt_pi_cfg),
            .o_sdr_pi_cfg                   (sdr_pi_cfg),
            .o_dfi_pi_cfg                   (dfi_pi_cfg),

            // DQS Transmitter
            .o_dqs_bscan_ctrl               (dqs_bscan_ctrl),
            .o_dqs_egress_bscan             (dqs_egress_bscan),
            .o_dqs_egress_mode_ana          (dqs_egress_mode_ana),
            .o_dqs_egress_mode_dig          (dqs_egress_mode_dig),
            .o_dqs_tgb_mode                 (dqs_tgb_mode),
            .o_dqs_wgb_mode                 (dqs_wgb_mode),
            .o_dqs_ck2wck_ratio             (dqs_ck2wck_ratio),
            .o_dqs_sdr_rt_pipe_en           (dqs_sdr_rt_pipe_en),
            .o_dqs_sdr_0_fc_dly             (dqs_sdr_0_fc_dly),
            .o_dqs_sdr_0_x_sel              (dqs_sdr_0_x_sel),
            .o_dqs_sdr_0_pipe_en            (dqs_sdr_0_pipe_en),
            .o_dqs_sdr_1_fc_dly             (dqs_sdr_1_fc_dly),
            .o_dqs_sdr_1_x_sel              (dqs_sdr_1_x_sel),
            .o_dqs_sdr_1_pipe_en            (dqs_sdr_1_pipe_en),
            .o_dqs_sdr_2_fc_dly             (dqs_sdr_2_fc_dly),
            .o_dqs_sdr_2_x_sel              (dqs_sdr_2_x_sel),
            .o_dqs_sdr_2_pipe_en            (dqs_sdr_2_pipe_en),
            .o_dqs_sdr_3_fc_dly             (dqs_sdr_3_fc_dly),
            .o_dqs_sdr_3_x_sel              (dqs_sdr_3_x_sel),
            .o_dqs_sdr_3_pipe_en            (dqs_sdr_3_pipe_en),
            .o_dqs_ddr_0_x_sel              (dqs_ddr_0_x_sel),
            .o_dqs_ddr_0_pipe_en            (dqs_ddr_0_pipe_en),
            .o_dqs_ddr_1_x_sel              (dqs_ddr_1_x_sel),
            .o_dqs_ddr_1_pipe_en            (dqs_ddr_1_pipe_en),
            .o_dqs_xdr_lpde_cfg             (dqs_xdr_lpde_cfg),
            .o_dqs_qdr_pi_0_cfg             (dqs_qdr_pi_0_cfg),
            .o_dqs_qdr_pi_1_cfg             (dqs_qdr_pi_1_cfg), // Floating when not using 4to1 serializer.
            .o_dqs_ddr_pi_0_cfg             (dqs_ddr_pi_0_cfg),
            .o_dqs_ddr_pi_1_cfg             (dqs_ddr_pi_1_cfg), // Floating when not using 4to1 serializer.
            .o_dqs_sdr_rt_pi_cfg            (dqs_sdr_rt_pi_cfg),

            // DQS Receiver
            .i_dqs_ingress_bscan            (dqs_ingress_bscan),
            .o_dqs_rgb_mode                 (dqs_rgb_mode),
            .o_dqs_fgb_mode                 (dqs_fgb_mode),
            .o_dqs_sdr_lpde_cfg             (dqs_sdr_lpde_cfg),
            .o_dqs_wck_mode                 (dqs_wck_mode),
            .o_dqs_pre_filter_sel           (dqs_pre_filter_sel),
            .o_dqs_ren_pi_cfg               (dqs_ren_pi_cfg),
            .o_dqs_rcs_pi_cfg               (dqs_rcs_pi_cfg),
            .o_dqs_rdqs_pi_0_cfg            (dqs_rdqs_pi_0_cfg),
            .o_dqs_rdqs_pi_1_cfg            (dqs_rdqs_pi_1_cfg),
            .i_dqs_io_sta                   (dqs_core_ig),
            .i_dqs_rcs_pi_phase_sta         (dqs_rcs_pi_phase_sta),
            .i_dqs_ren_pi_phase_sta         (dqs_ren_pi_phase_sta),

            // Pads
         `ifdef DDR_DQS_VREF
            .o_dqs_refgen_cfg               (dqs_refgen_cfg),
         `endif
            .o_dqs_sa_cfg                   (dqs_sa_cfg),
            .o_dqs_sa_cmn_cfg               (dqs_sa_cmn_cfg),
            .o_dqs_pad_rx_cfg               (dqs_pad_rx_cfg),
            .o_dqs_pad_rx_cmn_cfg           (dqs_pad_rx_cmn_cfg),
            .o_dqs_pad_tx_cfg               (dqs_pad_tx_cfg),
            .o_dqs_pad_tx_cmn_cfg           (dqs_pad_tx_cmn_cfg)
         );
      end else begin : DQ_CSR_WRAPPER
         ddr_dq_csr_wrapper #(
            .AHB_AWIDTH                     (AHB_AWIDTH),
            .DQ_WIDTH                       (DQ_WIDTH),
            .DQS_WIDTH                      (DP_DQS_WIDTH),
            .TXRX_DQS_WIDTH                 (TXRX_DQS_WIDTH),
            .TX0WIDTH                       (TX0WIDTH),
            .TX1WIDTH                       (TX1WIDTH),
            .RX0WIDTH                       (RX0WIDTH),
            .RX1WIDTH                       (RX1WIDTH),
            .A0WIDTH                        (A0WIDTH),
            .A1WIDTH                        (A1WIDTH),
            .A2WIDTH                        (A2WIDTH),
         `ifdef DDR_DQS_VREF
            .VWIDTH                         (VWIDTH),
         `endif
            .E0WIDTH                        (E0WIDTH),
            .E1WIDTH                        (E1WIDTH),
            .FWIDTH                         (FWIDTH),
            .MXWIDTH                        (MXWIDTH),
            .LWIDTH                         (LWIDTH),
            .P0WIDTH                        (P0WIDTH),
            .P1WIDTH                        (P1WIDTH),
            .PDWIDTH                        (PDWIDTH)
         ) u_dq_csr_wrapper (

            .i_hclk                         (i_ahb_clk),
            .i_hreset                       (i_ahb_rst),
            .i_haddr                        (i_ahb_haddr),
            .i_hwrite                       (i_ahb_hwrite),
            .i_hsel                         (i_ahb_hsel),
            .i_hwdata                       (i_ahb_hwdata),
            .i_htrans                       (i_ahb_htrans),
            .i_hsize                        (i_ahb_hsize),
            .i_hburst                       (i_ahb_hburst),
            .i_hreadyin                     (i_ahb_hreadyin),
            .o_hready                       (o_ahb_hready),
            .o_hrdata                       (o_ahb_hrdata),
            .o_hresp                        (o_ahb_hresp),

            .i_bscan_mode                   (i_jtag_bsr_mode),
            .i_csp_pi_en                    (i_csp_pi_en),
            .i_wcs                          (wcs),
            .i_rcs                          (rcs),
            .i_msr                          (i_msr),

            // DQ Receiver
            .o_dq_fifo_clr                  (dq_fifo_clr),
            .o_dq_training_mode             (dq_training_mode),
            .i_dq_ingress_bscan             (dq_ingress_bscan),
            .o_dq_rgb_mode                  (),//FIXME: Remove
            .o_dq_fgb_mode                  (),//FIXME: Remove
            .o_dq_pad_rx_cfg                (dq_pad_rx_cfg),
            .o_dq_pad_tx_cfg                (dq_pad_tx_cfg),
            .o_dq_sa_cfg                    (dq_sa_cfg),
            .o_dq_sa_dly_cfg                (dq_sa_dly_cfg),
            .i_dq_sa_sta                    (dq_sa_sta),
            .i_dq_io_sta                    (dq_core_ig),

            // DQ Transmitter
            .o_dq_egress_bscan              (dq_egress_bscan),
            .o_dq_egress_mode_ana           (dq_egress_mode_ana),
            .o_dq_egress_mode_dig           (dq_egress_mode_dig),
            .o_dq_sdr_rt_pipe_en            (dq_sdr_rt_pipe_en),
            .o_dq_sdr_0_fc_dly              (dq_sdr_0_fc_dly),
            .o_dq_sdr_0_x_sel               (dq_sdr_0_x_sel),
            .o_dq_sdr_0_pipe_en             (dq_sdr_0_pipe_en),
            .o_dq_sdr_1_fc_dly              (dq_sdr_1_fc_dly),
            .o_dq_sdr_1_x_sel               (dq_sdr_1_x_sel),
            .o_dq_sdr_1_pipe_en             (dq_sdr_1_pipe_en),
            .o_dq_sdr_2_fc_dly              (dq_sdr_2_fc_dly),
            .o_dq_sdr_2_x_sel               (dq_sdr_2_x_sel),
            .o_dq_sdr_2_pipe_en             (dq_sdr_2_pipe_en),
            .o_dq_sdr_3_fc_dly              (dq_sdr_3_fc_dly),
            .o_dq_sdr_3_x_sel               (dq_sdr_3_x_sel),
            .o_dq_sdr_3_pipe_en             (dq_sdr_3_pipe_en),
            .o_dq_ddr_0_x_sel               (dq_ddr_0_x_sel),
            .o_dq_ddr_0_pipe_en             (dq_ddr_0_pipe_en),
            .o_dq_ddr_1_x_sel               (dq_ddr_1_x_sel),
            .o_dq_ddr_1_pipe_en             (dq_ddr_1_pipe_en),
            .o_dq_xdr_lpde_cfg              (dq_xdr_lpde_cfg),
            .o_dq_qdr_pi_0_cfg              (dq_qdr_pi_0_cfg),
            .o_dq_qdr_pi_1_cfg              (dq_qdr_pi_1_cfg),  // Floating when not using 4to1 serializer.
            .o_dq_ddr_pi_0_cfg              (dq_ddr_pi_0_cfg),
            .o_dq_ddr_pi_1_cfg              (dq_ddr_pi_1_cfg),  // Floating when not using 4to1 serializer.
            .o_dq_sdr_rt_pi_cfg             (dq_sdr_rt_pi_cfg),
            .o_sdr_pi_cfg                   (sdr_pi_cfg),
            .o_dfi_pi_cfg                   (dfi_pi_cfg),

            // DQS Transmitter
            .o_dqs_bscan_ctrl               (dqs_bscan_ctrl),
            .o_dqs_egress_bscan             (dqs_egress_bscan),
            .o_dqs_egress_mode_ana          (dqs_egress_mode_ana),
            .o_dqs_egress_mode_dig          (dqs_egress_mode_dig),
            .o_dqs_tgb_mode                 (dqs_tgb_mode),
            .o_dqs_wgb_mode                 (dqs_wgb_mode),
            .o_dqs_ck2wck_ratio             (dqs_ck2wck_ratio),
            .o_dqs_sdr_rt_pipe_en           (dqs_sdr_rt_pipe_en),
            .o_dqs_sdr_0_fc_dly             (dqs_sdr_0_fc_dly),
            .o_dqs_sdr_0_x_sel              (dqs_sdr_0_x_sel),
            .o_dqs_sdr_0_pipe_en            (dqs_sdr_0_pipe_en),
            .o_dqs_sdr_1_fc_dly             (dqs_sdr_1_fc_dly),
            .o_dqs_sdr_1_x_sel              (dqs_sdr_1_x_sel),
            .o_dqs_sdr_1_pipe_en            (dqs_sdr_1_pipe_en),
            .o_dqs_sdr_2_fc_dly             (dqs_sdr_2_fc_dly),
            .o_dqs_sdr_2_x_sel              (dqs_sdr_2_x_sel),
            .o_dqs_sdr_2_pipe_en            (dqs_sdr_2_pipe_en),
            .o_dqs_sdr_3_fc_dly             (dqs_sdr_3_fc_dly),
            .o_dqs_sdr_3_x_sel              (dqs_sdr_3_x_sel),
            .o_dqs_sdr_3_pipe_en            (dqs_sdr_3_pipe_en),
            .o_dqs_ddr_0_x_sel              (dqs_ddr_0_x_sel),
            .o_dqs_ddr_0_pipe_en            (dqs_ddr_0_pipe_en),
            .o_dqs_ddr_1_x_sel              (dqs_ddr_1_x_sel),
            .o_dqs_ddr_1_pipe_en            (dqs_ddr_1_pipe_en),
            .o_dqs_xdr_lpde_cfg             (dqs_xdr_lpde_cfg),
            .o_dqs_qdr_pi_0_cfg             (dqs_qdr_pi_0_cfg),
            .o_dqs_qdr_pi_1_cfg             (dqs_qdr_pi_1_cfg), // Floating when not using 4to1 serializer.
            .o_dqs_ddr_pi_0_cfg             (dqs_ddr_pi_0_cfg),
            .o_dqs_ddr_pi_1_cfg             (dqs_ddr_pi_1_cfg), // Floating when not using 4to1 serializer.
            .o_dqs_sdr_rt_pi_cfg            (dqs_sdr_rt_pi_cfg),

            // DQS Receiver
            .i_dqs_ingress_bscan            (dqs_ingress_bscan),
            .o_dqs_rgb_mode                 (dqs_rgb_mode),
            .o_dqs_fgb_mode                 (dqs_fgb_mode),
            .o_dqs_sdr_lpde_cfg             (dqs_sdr_lpde_cfg),
            .o_dqs_wck_mode                 (dqs_wck_mode),
            .o_dqs_pre_filter_sel           (dqs_pre_filter_sel),
            .o_dqs_ren_pi_cfg               (dqs_ren_pi_cfg),
            .o_dqs_rcs_pi_cfg               (dqs_rcs_pi_cfg),
            .o_dqs_rdqs_pi_0_cfg            (dqs_rdqs_pi_0_cfg),
            .o_dqs_rdqs_pi_1_cfg            (dqs_rdqs_pi_1_cfg),
            .i_dqs_io_sta                   (dqs_core_ig),
            .i_dqs_rcs_pi_phase_sta         (dqs_rcs_pi_phase_sta),
            .i_dqs_ren_pi_phase_sta         (dqs_ren_pi_phase_sta),

            // Pads
         `ifdef DDR_DQS_VREF
            .o_dqs_refgen_cfg               (dqs_refgen_cfg),
         `endif
            .o_dqs_sa_cfg                   (dqs_sa_cfg),
            .o_dqs_sa_cmn_cfg               (dqs_sa_cmn_cfg),
            .o_dqs_pad_rx_cfg               (dqs_pad_rx_cfg),
            .o_dqs_pad_rx_cmn_cfg           (dqs_pad_rx_cmn_cfg),
            .o_dqs_pad_tx_cfg               (dqs_pad_tx_cfg),
            .o_dqs_pad_tx_cmn_cfg           (dqs_pad_tx_cmn_cfg)
         );
      end
   endgenerate

   //------------------------------------------------------------------------
   // JTAG Boundary Scan
   // ------------------------------------------------------------------------

   logic [DQ_WIDTH-1:0]       dq_pad_eg_bscan_t;
   logic [DQ_WIDTH-1:0]       dq_pad_ig_bscan_t;
   logic                      dq_pad_ie_bscan_t;
   logic                      dq_pad_oe_bscan_t;
   logic                      dqs_pad_bscan_n;
   logic                      dqs_pad_bscan_oe;
   logic                      dqs_pad_bscan_ie;
   logic [TXRX_DQS_WIDTH-1:0] dqs_pad_eg_bscan_t;
   logic [TXRX_DQS_WIDTH-1:0] dqs_pad_eg_bscan_c;
   logic [TXRX_DQS_WIDTH-1:0] dqs_pad_ig_bscan_t;
   logic [TXRX_DQS_WIDTH-1:0] dqs_pad_ig_bscan_c;
   logic                      dqs_pad_ie_bscan_t;
   logic                      dqs_pad_oe_bscan_t;

   ddr_dq_bscan #(
      .DQ_WIDTH                      (DQ_WIDTH),
      .DQS_WIDTH                     (TXRX_DQS_WIDTH)
   ) u_dq_bscan (
      .i_jtag_tck                    (i_jtag_tck),
      .i_jtag_trst_n                 (i_jtag_trst_n),
      .i_jtag_bsr_mode               (i_jtag_bsr_mode),
      .i_jtag_capture                (i_jtag_capture),
      .i_jtag_shift                  (i_jtag_shift),
      .i_jtag_update                 (i_jtag_update),
      .i_jtag_tdi                    (i_jtag_tdi),
      .o_jtag_tdo                    (o_jtag_tdo),

      .i_dq_bscan                    (dq_egress_bscan),
      .o_dq_bscan                    (dq_ingress_bscan),
      .i_dq_pad_bscan_t              (dq_pad_eg_bscan_t),
      .o_dq_pad_bscan_t              (dq_pad_ig_bscan_t),

      .i_dqs_bscan_ctrl              (dqs_bscan_ctrl),
      .i_dqs_bscan                   (dqs_egress_bscan),
      .o_dqs_bscan                   (dqs_ingress_bscan),
      .o_dqs_pad_bscan_n             (dqs_pad_bscan_n),
      .o_dqs_pad_bscan_oe            (dqs_pad_bscan_oe),
      .o_dqs_pad_bscan_ie            (dqs_pad_bscan_ie),
      .i_dqs_pad_bscan_t             (dqs_pad_eg_bscan_t),
      .i_dqs_pad_bscan_c             (dqs_pad_eg_bscan_c),
      .o_dqs_pad_bscan_t             (dqs_pad_ig_bscan_t),
      .o_dqs_pad_bscan_c             (dqs_pad_ig_bscan_c)
   );

   // ------------------------------------------------------------------------
   // FIFO
   // ------------------------------------------------------------------------
   //
   localparam DQ_RDWIDTH    = NUM_RDPH * DQ_WIDTH;
   localparam INT_NUM_RPH   = BYTE_FIFO ? NUM_RDPH : NUM_RPH ;
   localparam INT_DQ_RWIDTH = INT_NUM_RPH*DQ_WIDTH ;

   logic [INT_DQ_RWIDTH-1:0] dq_sdr;
   logic [DQ_RWIDTH-1:0]     dq_sdr_pow;
   logic [DQ_WIDTH-1:0]      dq_sdr_vld;
   logic                     rvld;
   logic                     rx_sdr_clk;
   logic [DQ_WIDTH-1:0]      dq_rxfifo_empty_n;
   logic [FREN_WIDTH-1:0]    dq_rxfifo_read;
   logic                     dfirdclk_en;

   generate
      if (BYTE_FIFO) begin : FIFO
         ddr_rx_fifo #(
            .WWIDTH           (DQ_RDWIDTH),
            .RWIDTH           (DQ_RWIDTH),
            .BWIDTH           (1),
            .FREN_WIDTH       (FREN_WIDTH),
            .DEPTH            (FIFO_DEPTH),
            .SYNC             (1'b0),
            .RAM_MODEL        (1'b0)
         ) u_rx_fifo (
            .i_scan_clk       (i_scan_clk),
            .i_scan_en        (i_scan_en),
            .i_scan_mode      (i_scan_mode),
            .i_scan_rst_ctrl  (i_scan_rst_ctrl),
            .i_scan_cgc_ctrl  (i_scan_cgc_ctrl),
            .i_scan           (2'b0),
            .o_scan           (/*OPEN*/),
            .i_clr            (dq_fifo_clr),
            .i_read_mask      (dq_training_mode),
            .i_fgb_mode       (dqs_fgb_mode),
            .i_wclk           (rx_sdr_clk),
            .i_wrst           (i_rst),
            .i_write          (1'b1),
            .i_wdata          (dq_sdr),
            .o_full           (/*OPEN*/),
            .i_rclk           (o_phy_clk),
            .i_rrst           (i_rst),
            .i_csp_div_rst_n  (i_csp_div_rst_n),
            .i_read           (i_rxfifo_read),
            .i_rclk_en_ovr_sel(i_dfirdclk_en_ovr_sel ) ,
            .i_rclk_en_ovr    (i_dfirdclk_en_ovr     ) ,
            .o_rdata          (dq_sdr_pow),
            .o_rvld           (rvld),
            .o_rclk_en        (dfirdclk_en),
            .o_empty_n        (o_rxfifo_empty_n)
         );

         // Convert to Words-Of-Phases (WOP) format
         //    Pn[Wn...W0]...P0[Wn...W0] -> Wn[Pn...P0]...W0[Pn...P0]
         ddr_dp_pow2wop #(.WIDTH(DQ_WIDTH), .NUM_PH(NUM_RPH)) u_dp_pow2wop (.i_d(dq_sdr_pow),.o_d(o_dq_sdr));
         assign o_dq_sdr_vld = {DQ_WIDTH{rvld}};
      end else begin
         // Convert to Words-Of-Phases (WOP) format
         //    Pn[Wn...W0]...P0[Wn...W0] -> Wn[Pn...P0]...W0[Pn...P0]
         ddr_dp_pow2wop #(.WIDTH(DQ_WIDTH), .NUM_PH(NUM_RPH)) u_dp_pow2wop (.i_d(dq_sdr),.o_d(o_dq_sdr));
         assign o_dq_sdr         = dq_sdr;
         assign o_dq_sdr_vld     = dq_sdr_vld ;
         assign o_rxfifo_empty_n = dq_rxfifo_empty_n[0];
      end

      assign o_tst_clk[0]        = rx_sdr_clk;
      assign o_tst_clk[1]        = o_phy_clk;
      assign dq_rxfifo_read      = i_rxfifo_read;

   endgenerate

   // ------------------------------------------------------------------------
   // DQ
   // ------------------------------------------------------------------------

   ddr_dq #(
      .CA_TYPE                        (CA_TYPE),
      .NUM_RDPH                       (NUM_RDPH),
      .NUM_RPH                        (INT_NUM_RPH),
      .NUM_WDPH                       (NUM_WDPH),
      .NUM_WPH                        (NUM_WPH),
      .DQ_WIDTH                       (DQ_WIDTH),
      .DQS_WIDTH                      (DQS_WIDTH),
      .FEEDTHR_DQS_WIDTH              (FEEDTHR_DQS_WIDTH),
      .DP_DQS_WIDTH                   (DP_DQS_WIDTH),
      .TXRX_DQS_WIDTH                 (TXRX_DQS_WIDTH),
      .DQ_RWIDTH                      (INT_DQ_RWIDTH),
      .DQS_RWIDTH                     (DQS_RWIDTH),
      .DQ_WWIDTH                      (DQ_WWIDTH),
      .DQS_WWIDTH                     (DQS_WWIDTH),
      .TX0WIDTH                       (TX0WIDTH),
      .TX1WIDTH                       (TX1WIDTH),
      .RX0WIDTH                       (RX0WIDTH),
      .RX1WIDTH                       (RX1WIDTH),
      .A0WIDTH                        (A0WIDTH),
      .A1WIDTH                        (A1WIDTH),
      .A2WIDTH                        (A2WIDTH),
   `ifdef DDR_DQS_VREF
      .VWIDTH                         (VWIDTH),
   `endif
      .E0WIDTH                        (E0WIDTH),
      .E1WIDTH                        (E1WIDTH),
      .FWIDTH                         (FWIDTH),
      .MXWIDTH                        (MXWIDTH),
      .LWIDTH                         (LWIDTH),
      .P0WIDTH                        (PDWIDTH),
      .P1WIDTH                        (P1WIDTH),
      .PS_DLY                         (PS_DLY),
      .FIFO_DEPTH                     (FIFO_DEPTH),
      .DFIRDCLKEN_PEXTWIDTH           (DFIRDCLKEN_PEXTWIDTH),
      .DQ_TX_CKE_MASK                 (DQ_TX_CKE_MASK),
      .DQS_TX_WCK_MASK                (DQS_TX_WCK_MASK),
      .DQS_TX_DQS_MASK                (DQS_TX_DQS_MASK),
      .FREN_WIDTH                     (FREN_WIDTH),
      .SLICE_FIFO                     (SLICE_FIFO)
   ) u_dq (
      // Test Clock
      .i_scan_clk                     (i_scan_clk      ),
      .i_scan_mode                    (i_scan_mode     ),
      //.i_scan_cgc_ctrl                (i_scan_cgc_ctrl ),
      .o_tst_clk                      (o_tst_clk[3:2]  ),

      // Common Clocks and Reset
      .i_rst                          (i_rst),
      .i_pll_clk_0                    (i_pll_clk_0),
      .i_pll_clk_90                   (i_pll_clk_90),
      .i_pll_clk_180                  (i_pll_clk_180),
      .i_pll_clk_270                  (i_pll_clk_270),

      .o_phy_clk                      (o_phy_clk),
      .o_rx_sdr_clk                   (rx_sdr_clk),
      .o_dfiwr_clk_1                  (o_dfiwr_clk_1),
      .o_dfiwr_clk_2                  (o_dfiwr_clk_2),
      .o_dfird_clk_1                  (o_dfird_clk_1),
      .o_dfird_clk_2                  (o_dfird_clk_2),

      // Chip Select
      .o_rcs                          (rcs),
      // DQ Transmitter
      .i_dq_egress_mode_ana           (dq_egress_mode_ana),
      .i_dq_egress_mode_dig           (dq_egress_mode_dig),
      .i_dq_sdr_rt_pipe_en            (dq_sdr_rt_pipe_en),
      .i_dq_sdr_0_fc_dly              (dq_sdr_0_fc_dly),
      .i_dq_sdr_0_x_sel               (dq_sdr_0_x_sel),
      .i_dq_sdr_0_pipe_en             (dq_sdr_0_pipe_en),
      .i_dq_sdr_1_fc_dly              (dq_sdr_1_fc_dly),
      .i_dq_sdr_1_x_sel               (dq_sdr_1_x_sel),
      .i_dq_sdr_1_pipe_en             (dq_sdr_1_pipe_en),
      .i_dq_sdr_2_fc_dly              (dq_sdr_2_fc_dly),
      .i_dq_sdr_2_x_sel               (dq_sdr_2_x_sel),
      .i_dq_sdr_2_pipe_en             (dq_sdr_2_pipe_en),
      .i_dq_sdr_3_fc_dly              (dq_sdr_3_fc_dly),
      .i_dq_sdr_3_x_sel               (dq_sdr_3_x_sel),
      .i_dq_sdr_3_pipe_en             (dq_sdr_3_pipe_en),
      .i_dq_ddr_0_x_sel               (dq_ddr_0_x_sel),
      .i_dq_ddr_0_pipe_en             (dq_ddr_0_pipe_en),
      .i_dq_ddr_1_x_sel               (dq_ddr_1_x_sel),
      .i_dq_ddr_1_pipe_en             (dq_ddr_1_pipe_en),
      .i_dq_xdr_lpde_cfg              (dq_xdr_lpde_cfg),
      .i_dq_qdr_pi_0_cfg              (dq_qdr_pi_0_cfg),
      .i_dq_ddr_pi_0_cfg              (dq_ddr_pi_0_cfg),
      .i_dq_sdr_rt_pi_cfg             (dq_sdr_rt_pi_cfg),
      .i_sdr_pi_cfg                   (sdr_pi_cfg),
      .i_dfi_pi_cfg                   (dfi_pi_cfg),
      .i_dq_sdr                       (i_dq_sdr),

      // DQ Receiver
      //.i_dq_rgb_mode                  (dq_rgb_mode),
      //.i_dq_fgb_mode                  (dq_fgb_mode),
      .o_dq_sa                        (dq_sa_sta),
      .o_dq_sdr                       (dq_sdr),
      .o_dq_sdr_vld                   (dq_sdr_vld),
      .o_dq_rxfifo_empty_n            (dq_rxfifo_empty_n),
      .i_dq_rxfifo_read               (dq_rxfifo_read),
      .i_dq_rxfifo_clr                (dq_fifo_clr),
      .i_dq_rxfifo_read_mask          (dq_training_mode),

      // DQS Transmitter
      .i_dqs_egress_mode_ana          (dqs_egress_mode_ana),
      .i_dqs_egress_mode_dig          (dqs_egress_mode_dig),

      .i_dqs_tgb_mode                 (dqs_tgb_mode),
      .i_dqs_wgb_mode                 (dqs_wgb_mode),
      .i_dqs_ck2wck_ratio             (dqs_ck2wck_ratio),
      .i_csp_div_rst_n                (i_csp_div_rst_n),
      .i_dqs_dfi_wrtraffic            (i_dqs_dfi_wrtraffic),
      .i_dq_dfi_wrtraffic             (i_dq_dfi_wrtraffic),
      .i_dfiwrgb_mode                 (i_dfiwrgb_mode),
      .i_dfirdgb_mode                 (i_dfirdgb_mode),
      .i_dfirdclk_en                  (dfirdclk_en), //o_dq_sdr_vld[0]),
      .i_dfirdclk_en_pulse_ext        (i_dfirdclk_en_pulse_ext),

      .i_dqs_sdr_rt_pipe_en           (dqs_sdr_rt_pipe_en),
      .i_dqs_sdr_0_fc_dly             (dqs_sdr_0_fc_dly),
      .i_dqs_sdr_0_x_sel              (dqs_sdr_0_x_sel),
      .i_dqs_sdr_0_pipe_en            (dqs_sdr_0_pipe_en),
      .i_dqs_sdr_1_fc_dly             (dqs_sdr_1_fc_dly),
      .i_dqs_sdr_1_x_sel              (dqs_sdr_1_x_sel),
      .i_dqs_sdr_1_pipe_en            (dqs_sdr_1_pipe_en),
      .i_dqs_sdr_2_fc_dly             (dqs_sdr_2_fc_dly),
      .i_dqs_sdr_2_x_sel              (dqs_sdr_2_x_sel),
      .i_dqs_sdr_2_pipe_en            (dqs_sdr_2_pipe_en),
      .i_dqs_sdr_3_fc_dly             (dqs_sdr_3_fc_dly),
      .i_dqs_sdr_3_x_sel              (dqs_sdr_3_x_sel),
      .i_dqs_sdr_3_pipe_en            (dqs_sdr_3_pipe_en),
      .i_dqs_ddr_0_x_sel              (dqs_ddr_0_x_sel),
      .i_dqs_ddr_0_pipe_en            (dqs_ddr_0_pipe_en),
      .i_dqs_ddr_1_x_sel              (dqs_ddr_1_x_sel),
      .i_dqs_ddr_1_pipe_en            (dqs_ddr_1_pipe_en),
      .i_dqs_xdr_lpde_cfg             (dqs_xdr_lpde_cfg),
      .i_dqs_qdr_pi_0_cfg             (dqs_qdr_pi_0_cfg),
      .i_dqs_ddr_pi_0_cfg             (dqs_ddr_pi_0_cfg),
      .i_dqs_sdr_rt_pi_cfg            (dqs_sdr_rt_pi_cfg),
      .i_dqs_sdr                      (i_dqs_sdr),

      // DQS Receiver
      .i_dqs_rgb_mode                 (dqs_rgb_mode),
      .i_dqs_fgb_mode                 (dqs_fgb_mode),
      .i_dqs_sdr_lpde_cfg             (dqs_sdr_lpde_cfg),
      .i_dqs_wck_mode                 (dqs_wck_mode),
      .i_dqs_pre_filter_sel           (dqs_pre_filter_sel),
      .i_dqs_ren_pi_cfg               (dqs_ren_pi_cfg),
      .i_dqs_rcs_pi_cfg               (dqs_rcs_pi_cfg),
      .i_dqs_rdqs_pi_0_cfg            (dqs_rdqs_pi_0_cfg),
      .i_dqs_rdqs_pi_1_cfg            (dqs_rdqs_pi_1_cfg),
      .o_dqs_rcs_pi_phase_sta         (dqs_rcs_pi_phase_sta),
      .o_dqs_ren_pi_phase_sta         (dqs_ren_pi_phase_sta),

      // Pads
      .ana_vref_in                    (ana_vref_in),
      .i_dq_cmn_freeze_n              (i_freeze_n),
      .i_dqs_hiz_n                    (i_hiz_n),
`ifdef DDR_DQS_VREF
      .i_dqs_refgen_cfg               (dqs_refgen_cfg),
`endif
      .i_dqs_sa_cfg                   (dqs_sa_cfg),
      .i_dqs_sa_cmn_cfg               (dqs_sa_cmn_cfg),
      .i_dqs_pad_rx_cfg               (dqs_pad_rx_cfg),
      .i_dqs_pad_rx_cmn_cfg           (dqs_pad_rx_cmn_cfg),
      .i_dqs_pad_tx_cfg               (dqs_pad_tx_cfg),
      .i_dqs_pad_tx_cmn_cfg           (dqs_pad_tx_cmn_cfg),
      .o_dqs_core_ig                  (dqs_core_ig),
      .o_dqs_core_eg                  (dqs_core_eg),

      .i_dq_freeze_n_hv               (i_freeze_n_hv),
      .i_dq_sa_cfg                    (dq_sa_cfg),
      .i_dq_sa_dly_cfg                (dq_sa_dly_cfg),
      .i_dq_pad_rx_cfg                (dq_pad_rx_cfg),
      .i_dq_pad_tx_cfg                (dq_pad_tx_cfg),
      .o_dq_core_ig                   (dq_core_ig),
      .o_dq_core_eg                   (/*OPEN*/),

      .i_dq_pad_bscan_t               (dq_pad_ig_bscan_t),
      .o_dq_pad_bscan_t               (dq_pad_eg_bscan_t),
      .i_dqs_pad_bscan_n              (dqs_pad_bscan_n),
      .i_dqs_pad_bscan_oe             (dqs_pad_bscan_oe),
      .i_dqs_pad_bscan_ie             (dqs_pad_bscan_ie),
      .i_dqs_pad_bscan_t              (dqs_pad_ig_bscan_t),
      .i_dqs_pad_bscan_c              (dqs_pad_ig_bscan_c),
      .o_dqs_pad_bscan_t              (dqs_pad_eg_bscan_t),
      .o_dqs_pad_bscan_c              (dqs_pad_eg_bscan_c),

      .pad_wck_t                      (pad_wck_t),
      .pad_wck_c                      (pad_wck_c),
      .pad_dqs_t                      (pad_dqs_t),
      .pad_dqs_c                      (pad_dqs_c),
      .pad_dq                         (pad_dq)

   );

endmodule

module ddr_dq_bscan #(
   parameter DQ_WIDTH      =  9,
   parameter DQS_WIDTH     =  8
) (

   // JTAG Interface
   input  logic                            i_jtag_tck,
   input  logic                            i_jtag_trst_n,
   input  logic                            i_jtag_bsr_mode,
   input  logic                            i_jtag_capture,
   input  logic                            i_jtag_shift,
   input  logic                            i_jtag_update,
   input  logic                            i_jtag_tdi,
   output logic                            o_jtag_tdo,

   // BSCAN Interface
   input  logic [1:0]                      i_dqs_bscan_ctrl,
   input  logic [DQ_WIDTH-1:0]             i_dq_bscan,
   input  logic [2*DQS_WIDTH-1:0]          i_dqs_bscan,
   input  logic [DQ_WIDTH-1:0]             i_dq_pad_bscan_t,
   input  logic [DQS_WIDTH-1:0]            i_dqs_pad_bscan_t,
   input  logic [DQS_WIDTH-1:0]            i_dqs_pad_bscan_c,

   output logic [DQ_WIDTH-1:0]             o_dq_bscan,
   output logic [DQ_WIDTH-1:0]             o_dq_pad_bscan_t,
   output logic                            o_dqs_pad_bscan_n,
   output logic                            o_dqs_pad_bscan_oe,
   output logic                            o_dqs_pad_bscan_ie,
   output logic [2*DQS_WIDTH-1:0]          o_dqs_bscan,
   output logic [DQS_WIDTH-1:0]            o_dqs_pad_bscan_t,
   output logic [DQS_WIDTH-1:0]            o_dqs_pad_bscan_c

);

   assign o_dqs_pad_bscan_n = ~i_jtag_bsr_mode;

   logic [3:0] td;

   // CTRL - Out Data Register
   wav_jtag_reg #(
      .NO_BYP                        (1),
      .DWIDTH                        (2)
   ) u_dqs_bsr_ctrl (
      .i_tck                         (i_jtag_tck),
      .i_trst_n                      (i_jtag_trst_n),
      .i_bsr_mode                    (i_jtag_bsr_mode),
      .i_capture                     (i_jtag_capture),
      .i_shift                       (i_jtag_shift),
      .i_update                      (i_jtag_update),
      .i_pi                          (i_dqs_bscan_ctrl),
      .o_po                          ({o_dqs_pad_bscan_oe,o_dqs_pad_bscan_ie}),
      .i_tdi                         (i_jtag_tdi),
      .o_tdo                         (td[0])
   );

   // DQ - Out Data Register
   wav_jtag_reg #(
      .NO_BYP                        (1),
      .DWIDTH                        (DQ_WIDTH)
   ) u_dq_bsr_o (
      .i_tck                         (i_jtag_tck),
      .i_trst_n                      (i_jtag_trst_n),
      .i_bsr_mode                    (i_jtag_bsr_mode),
      .i_capture                     (i_jtag_capture),
      .i_shift                       (i_jtag_shift),
      .i_update                      (i_jtag_update),
      .i_pi                          (i_dq_bscan),
      .o_po                          (o_dq_pad_bscan_t),
      .i_tdi                         (td[0]),
      .o_tdo                         (td[1])
   );

   // DQS - Out Data Register
   wav_jtag_reg #(
      .NO_BYP                        (1),
      .DWIDTH                        (2*DQS_WIDTH)
   ) u_dqs_t_bsr_o (
      .i_tck                         (i_jtag_tck),
      .i_trst_n                      (i_jtag_trst_n),
      .i_bsr_mode                    (i_jtag_bsr_mode),
      .i_capture                     (i_jtag_capture),
      .i_shift                       (i_jtag_shift),
      .i_update                      (i_jtag_update),
      .i_pi                          (i_dqs_bscan),
      .o_po                          ({o_dqs_pad_bscan_t, o_dqs_pad_bscan_c}),
      .i_tdi                         (td[1]),
      .o_tdo                         (td[2])
   );

   // DQ - In Data Register
   wav_jtag_reg #(
      .NO_BYP                        (1),
      .DWIDTH                        (DQ_WIDTH)
   ) u_dq_bsr_i (
      .i_tck                         (i_jtag_tck),
      .i_trst_n                      (i_jtag_trst_n),
      .i_bsr_mode                    (i_jtag_bsr_mode),
      .i_capture                     (i_jtag_capture),
      .i_shift                       (i_jtag_shift),
      .i_update                      (i_jtag_update),
      .i_pi                          (i_dq_pad_bscan_t),
      .o_po                          (o_dq_bscan),
      .i_tdi                         (td[2]),
      .o_tdo                         (td[3])
   );

   // DQS - In Data Register
   wav_jtag_reg #(
      .NO_BYP                        (1),
      .DWIDTH                        (2*DQS_WIDTH)
   ) u_dqs_bsr_i (
      .i_tck                         (i_jtag_tck),
      .i_trst_n                      (i_jtag_trst_n),
      .i_bsr_mode                    (i_jtag_bsr_mode),
      .i_capture                     (i_jtag_capture),
      .i_shift                       (i_jtag_shift),
      .i_update                      (i_jtag_update),
      .i_pi                          ({i_dqs_pad_bscan_t, i_dqs_pad_bscan_c}),
      .o_po                          (o_dqs_bscan),
      .i_tdi                         (td[3]),
      .o_tdo                         (o_jtag_tdo)
   );

endmodule

module ddr_dq #(
   parameter [0:0]           CA_TYPE              =  1'b0,                        // CA byte type enable
   parameter                 NUM_RDPH             =  8,                           // Read datapath data phases (includes R/F)
   parameter                 NUM_RPH              =  8,                           // Read fifo data phases (includes R/F)
   parameter                 NUM_WDPH             =  8,                           // Write datapath data phases (includes R/F)
   parameter                 NUM_WPH              =  8,                           // Write gearbox data phases (includes R/F)
   parameter                 DQ_WIDTH             =  9,                           // DQ bus width
   parameter                 DQS_WIDTH            =  8,                           // DQS bus width
   parameter                 FEEDTHR_DQS_WIDTH    =  0,                           // DQS bus width
   parameter                 DP_DQS_WIDTH         =  DQS_WIDTH-FEEDTHR_DQS_WIDTH,
   parameter                 TXRX_DQS_WIDTH       =  2,                           //
   parameter                 DQ_RWIDTH            = NUM_RPH * DQ_WIDTH,           // DQ read data width
   parameter                 DQS_RWIDTH           = NUM_RPH * DQS_WIDTH,          // DQS read data width
   parameter                 DQ_WWIDTH            = NUM_WPH * DQ_WIDTH,           // DQ write data width
   parameter                 DQS_WWIDTH           = NUM_WPH * DQS_WIDTH,          // DQS write data width
   parameter                 TX0WIDTH             =  14,                          // Tx IO configuration width
   parameter                 TX1WIDTH             =  5,                           // Tx IO configuration width
   parameter                 RX0WIDTH             =  8,                           // Rx IO configuration width
   parameter                 RX1WIDTH             =  8,                           // Rx IO configuration width
   parameter                 A0WIDTH              =  24,                          // Sense amp configuration width
   parameter                 A1WIDTH              =  24,                          // Sense amp configuration width
   parameter                 A2WIDTH              =  32,                          // Sense amp configuration width
`ifdef DDR_DQS_VREF
   parameter                 VWIDTH               =  8,                           // Voltage configuration width
`endif
   parameter                 E0WIDTH              =  6,                           // TX Egress path mode width (ANA)
   parameter                 E1WIDTH              =  7,                           // TX Egress path mode width (DIG)
   parameter                 FWIDTH               =  2,                           // Full cycle delay select width
   parameter                 MXWIDTH              =  3,                           // Mux-X select width width
   parameter                 LWIDTH               =  11,                          // LPDE delay select width
   parameter                 P0WIDTH              =  15,                          // PI code select width
   parameter                 P1WIDTH              =  9,                           // PI Matching cell cfg width
   parameter                 PS_DLY               =  10,                          // LPDE NAND delay in picoseconds
   parameter                 FIFO_DEPTH           =  8,                           // FIFO depth
   parameter                 DFIRDCLKEN_PEXTWIDTH =  4,                           // DFIRDCLK EN Pulse Extension count width
   parameter [DQ_WIDTH-1:0]  DQ_TX_CKE_MASK       = '1,                           // TX CKE PAD instance mask
   parameter [DQS_WIDTH-1:0] DQS_TX_WCK_MASK      = '1,                           // TX WCK PAD instance mask
   parameter [DQS_WIDTH-1:0] DQS_TX_DQS_MASK      = '1,                           // TX WCK PAD instance mask
   parameter                 FREN_WIDTH           =  1*2+1,         // RX FIFO Read enable width
   parameter [0:0]           SLICE_FIFO           =  1'b1                         // RX FIFO enable
) (

   // TEST
   input  logic                                i_scan_clk,
   input  logic                                i_scan_mode,
   //input  logic                                i_scan_cgc_ctrl,
   output logic [1:0]                          o_tst_clk,

   // Common Clocks and Reset
   input  logic                                i_rst,
   input  logic                                i_pll_clk_0,                  // External clock - Primary PLL clock ph0
   input  logic                                i_pll_clk_90,                 // External clock - Primary PLL clock ph90
   input  logic                                i_pll_clk_180,                // External clock - Primary PLL clock ph180
   input  logic                                i_pll_clk_270,                // External clock - Primary PLL clock ph270

   output logic                                o_phy_clk,                    // External clock - generated by DQS slice
   output logic                                o_rx_sdr_clk,                 // External clock - generated by DQS slice
   output logic                                o_dfiwr_clk_1,                // External Clock - generated by DQS slice
   output logic                                o_dfiwr_clk_2,                // External clock - generated by DQS slice
   output logic                                o_dfird_clk_1,                // External clock - generated by DQS slice
   output logic                                o_dfird_clk_2,                // External clock - generated by DQS slice

   // Chip Select
   output logic                                o_rcs,                        // Read chip select - Uniphase

   // DQ Transmitter
   input  logic [E0WIDTH*DQ_WIDTH-1:0]         i_dq_egress_mode_ana,         // DQ egress mode (ANA)
   input  logic [E1WIDTH*DQ_WIDTH-1:0]         i_dq_egress_mode_dig,         // DQ egress mode (DIG)
   input  logic [DQ_WIDTH-1:0]                 i_dq_sdr_rt_pipe_en,          // Retimer pipeline enable
   input  logic [FWIDTH*DQ_WIDTH-1:0]          i_dq_sdr_0_fc_dly,           // SDR full-cycle delay select
   input  logic [MXWIDTH*DQ_WIDTH-1:0]         i_dq_sdr_0_x_sel,            // Rise/Fall slice crossing select
   input  logic [DQ_WIDTH-1:0]                 i_dq_sdr_0_pipe_en,          // SDR pipeline enable
   input  logic [FWIDTH*DQ_WIDTH-1:0]          i_dq_sdr_1_fc_dly,           // SDR full-cycle delay select
   input  logic [MXWIDTH*DQ_WIDTH-1:0]         i_dq_sdr_1_x_sel,            // Rise/Fall slice crossing select
   input  logic [DQ_WIDTH-1:0]                 i_dq_sdr_1_pipe_en,          // SDR pipeline enable
   input  logic [FWIDTH*DQ_WIDTH-1:0]          i_dq_sdr_2_fc_dly,           // SDR full-cycle delay select
   input  logic [MXWIDTH*DQ_WIDTH-1:0]         i_dq_sdr_2_x_sel,            // Rise/Fall slice crossing select
   input  logic [DQ_WIDTH-1:0]                 i_dq_sdr_2_pipe_en,          // SDR pipeline enable
   input  logic [FWIDTH*DQ_WIDTH-1:0]          i_dq_sdr_3_fc_dly,           // SDR full-cycle delay select
   input  logic [MXWIDTH*DQ_WIDTH-1:0]         i_dq_sdr_3_x_sel,            // Rise/Fall slice crossing select
   input  logic [DQ_WIDTH-1:0]                 i_dq_sdr_3_pipe_en,          // SDR pipeline enable
   input  logic [(MXWIDTH-1)*DQ_WIDTH-1:0]     i_dq_ddr_0_x_sel,            // Rise/Fall slice crossing select
   input  logic [DQ_WIDTH-1:0]                 i_dq_ddr_0_pipe_en,          // SDR pipeline enable
   input  logic [(MXWIDTH-1)*DQ_WIDTH-1:0]     i_dq_ddr_1_x_sel,            // Rise/Fall slice crossing select
   input  logic [DQ_WIDTH-1:0]                 i_dq_ddr_1_pipe_en,          // SDR pipeline enable
   input  logic [LWIDTH*DQ_WIDTH-1:0]          i_dq_xdr_lpde_cfg,           // TX per-bit LPDE setting
   input  logic [P0WIDTH-1:0]                  i_dq_qdr_pi_0_cfg,           // QDR PI setting
   input  logic [P0WIDTH-1:0]                  i_dq_ddr_pi_0_cfg,           // DDR PI setting
   input  logic [P0WIDTH-1:0]                  i_dq_sdr_rt_pi_cfg,          // SDR Retimer PI setting
   input  logic [P1WIDTH-1:0]                  i_sdr_pi_cfg,                // SDR PI Tmin setting
   input  logic [P1WIDTH-1:0]                  i_dfi_pi_cfg,                // DFI DDR PI Tmin setting
   input  logic [DQ_WWIDTH-1:0]                i_dq_sdr,                    // DQ TX data & DBI

   // DQ Receiver
   //input  logic [DEC_DGBWIDTH-1:0]             i_dq_rgb_mode,               // Receiver datapath gearbox mode
   //input  fgb_t                                i_dq_fgb_mode,               // Receiver fifo gearbox mode
   output logic [4*DQ_WIDTH-1:0]               o_dq_sa,                     // DQ RX Sense Amp output
   output logic [DQ_RWIDTH-1:0]                o_dq_sdr,                    // DQ RX data & DBI
   output logic [DQ_WIDTH-1:0]                 o_dq_sdr_vld,                // DQ RX data valid
   output logic [DQ_WIDTH-1:0]                 o_dq_rxfifo_empty_n,         // DQ RX FIFO not Empty
   input  logic [FREN_WIDTH-1:0]               i_dq_rxfifo_read,            // DQ RX FIFO read
   input  logic                                i_dq_rxfifo_clr,             // DQ RX FIFO clear
   input  logic                                i_dq_rxfifo_read_mask,       // DQ RX FIFO read Mask

   // DQS Transmitter
   input  logic [E0WIDTH*DP_DQS_WIDTH-1:0]     i_dqs_egress_mode_ana,       // DQS egress mode (ANA)
   input  logic [E1WIDTH*DP_DQS_WIDTH-1:0]     i_dqs_egress_mode_dig,       // DQS egress mode (DIG)
   input  logic [DEC_DGBWIDTH-1:0]             i_dqs_tgb_mode,              // Transmitter gearbox mode
   input  logic [DEC_WGBWIDTH-1:0]             i_dqs_wgb_mode,              // Write gearbox mode
   input  logic [DEC_CK2WCKRWIDTH-1:0]         i_dqs_ck2wck_ratio,

   input  logic                                i_csp_div_rst_n,
   input  logic                                i_dqs_dfi_wrtraffic,
   input  logic                                i_dq_dfi_wrtraffic,
   input  logic [DEC_DFIGBWIDTH-1:0]           i_dfiwrgb_mode,
   input  logic [DEC_DFIGBWIDTH-1:0]           i_dfirdgb_mode,
   input  logic                                i_dfirdclk_en,
   input  logic [DFIRDCLKEN_PEXTWIDTH-1:0]     i_dfirdclk_en_pulse_ext,

   input  logic [DP_DQS_WIDTH-1:0]             i_dqs_sdr_rt_pipe_en,        // Retimer pipeline enable
   input  logic [FWIDTH*DP_DQS_WIDTH-1:0]      i_dqs_sdr_0_fc_dly,          // SDR full-cycle delay select
   input  logic [MXWIDTH*DP_DQS_WIDTH-1:0]     i_dqs_sdr_0_x_sel,           // Rise/Fall slice crossing select
   input  logic [DP_DQS_WIDTH-1:0]             i_dqs_sdr_0_pipe_en,         // SDR pipeline enable
   input  logic [FWIDTH*DP_DQS_WIDTH-1:0]      i_dqs_sdr_1_fc_dly,          // SDR full-cycle delay select
   input  logic [MXWIDTH*DP_DQS_WIDTH-1:0]     i_dqs_sdr_1_x_sel,           // Rise/Fall slice crossing select
   input  logic [DP_DQS_WIDTH-1:0]             i_dqs_sdr_1_pipe_en,         // SDR pipeline enable
   input  logic [FWIDTH*DP_DQS_WIDTH-1:0]      i_dqs_sdr_2_fc_dly,          // SDR full-cycle delay select
   input  logic [MXWIDTH*DP_DQS_WIDTH-1:0]     i_dqs_sdr_2_x_sel,           // Rise/Fall slice crossing select
   input  logic [DP_DQS_WIDTH-1:0]             i_dqs_sdr_2_pipe_en,         // SDR pipeline enable
   input  logic [FWIDTH*DP_DQS_WIDTH-1:0]      i_dqs_sdr_3_fc_dly,          // SDR full-cycle delay select
   input  logic [MXWIDTH*DP_DQS_WIDTH-1:0]     i_dqs_sdr_3_x_sel,           // Rise/Fall slice crossing select
   input  logic [DP_DQS_WIDTH-1:0]             i_dqs_sdr_3_pipe_en,         // SDR pipeline enable
   input  logic [(MXWIDTH-1)*DP_DQS_WIDTH-1:0] i_dqs_ddr_0_x_sel,           // Rise/Fall slice crossing select
   input  logic [DP_DQS_WIDTH-1:0]             i_dqs_ddr_0_pipe_en,         // SDR pipeline enable
   input  logic [(MXWIDTH-1)*DP_DQS_WIDTH-1:0] i_dqs_ddr_1_x_sel,           // Rise/Fall slice crossing select
   input  logic [DP_DQS_WIDTH-1:0]             i_dqs_ddr_1_pipe_en,         // SDR pipeline enable
   input  logic [LWIDTH*TXRX_DQS_WIDTH-1:0]    i_dqs_xdr_lpde_cfg,          // TX per-bit LPDE setting
   input  logic [P0WIDTH-1:0]                  i_dqs_qdr_pi_0_cfg,          // QDR PI setting
   input  logic [P0WIDTH-1:0]                  i_dqs_ddr_pi_0_cfg,          // DDR PI setting
   input  logic [P0WIDTH-1:0]                  i_dqs_sdr_rt_pi_cfg,         // SDR Retimer PI setting
   input  logic [DQS_WWIDTH-1:0]               i_dqs_sdr,                   // DQ TX data

   // DQS Receiver
   input  logic [DEC_DGBWIDTH-1:0]             i_dqs_rgb_mode,              // Receiver datapath gearbox mode
   input  fgb_t                                i_dqs_fgb_mode,              // Receiver fifo gearbox mode
   input  logic [LWIDTH-1:0]                   i_dqs_sdr_lpde_cfg,          // RX FIFO LPDE setting
   input  logic                                i_dqs_wck_mode,              // WCK loopback mode (only valid in rdqs_mode)
   input  logic [1:0]                          i_dqs_pre_filter_sel,        // Preamble filter sel
   input  logic [P0WIDTH-1:0]                  i_dqs_ren_pi_cfg,            // REN PI setting
   input  logic [P0WIDTH-1:0]                  i_dqs_rcs_pi_cfg,            // RCS PI setting
   input  logic [P0WIDTH-1:0]                  i_dqs_rdqs_pi_0_cfg,         // RCS PI setting
   input  logic [P0WIDTH-1:0]                  i_dqs_rdqs_pi_1_cfg,         // RCS PI setting
   output logic                                o_dqs_rcs_pi_phase_sta,
   output logic                                o_dqs_ren_pi_phase_sta,

   // Pads
   input  wire                                 ana_vref_in,                 // VREF reference
   input  logic                                i_dq_cmn_freeze_n,              // Freeze IO signal
   input  logic                                i_dqs_hiz_n,                 // HiZ IO signal
`ifdef DDR_DQS_VREF
   input  logic [VWIDTH-1:0]                   i_dqs_refgen_cfg,            // VREF configuration
`endif
   input  logic [A0WIDTH*TXRX_DQS_WIDTH-1:0]   i_dqs_sa_cfg,                // SA configuration
   input  logic [A1WIDTH-1:0]                  i_dqs_sa_cmn_cfg,            // SA configuration
   input  logic [RX0WIDTH*TXRX_DQS_WIDTH-1:0]  i_dqs_pad_rx_cfg,            // Pad Rx configuration
   input  logic [RX1WIDTH-1:0]                 i_dqs_pad_rx_cmn_cfg,        // Pad Rx configuration
   input  logic [TX0WIDTH*TXRX_DQS_WIDTH-1:0]  i_dqs_pad_tx_cfg,            // Pad Tx configuration
   input  logic [TX1WIDTH-1:0]                 i_dqs_pad_tx_cmn_cfg,        // Pad Tx configuration
   output logic [DP_DQS_WIDTH-1:0]             o_dqs_core_ig,               // Core ingress data from pad
   output logic [DQS_WIDTH-1:0]                o_dqs_core_eg,               // Core egress data to pad

   input  logic                                i_dq_freeze_n_hv,            // Freeze IO signal for CKE
   input  logic [A0WIDTH*DQ_WIDTH-1:0]         i_dq_sa_cfg,                 // SA Configuration
   input  logic [A2WIDTH*DQ_WIDTH-1:0]         i_dq_sa_dly_cfg,             // SA Configuration
   input  logic [RX0WIDTH*DQ_WIDTH-1:0]        i_dq_pad_rx_cfg,             // Pad Rx configuration
   input  logic [TX0WIDTH*DQ_WIDTH-1:0]        i_dq_pad_tx_cfg,             // Pad Tx configuration
   output logic [DQ_WIDTH-1:0]                 o_dq_core_ig,                // Core ingress data from pad
   output logic [DQ_WIDTH-1:0]                 o_dq_core_eg,                // Core egress data to pad

   input  logic [DQ_WIDTH-1:0]                 i_dq_pad_bscan_t,            // From BSCAN
   output logic [DQ_WIDTH-1:0]                 o_dq_pad_bscan_t,            // To BSCAN
   input  logic                                i_dqs_pad_bscan_n,
   input  logic                                i_dqs_pad_bscan_oe,
   input  logic                                i_dqs_pad_bscan_ie,
   input  logic [TXRX_DQS_WIDTH-1:0]           i_dqs_pad_bscan_t,           // From BSCAN
   input  logic [TXRX_DQS_WIDTH-1:0]           i_dqs_pad_bscan_c,           // From BSCAN
   output logic [TXRX_DQS_WIDTH-1:0]           o_dqs_pad_bscan_t,           // To BSCAN
   output logic [TXRX_DQS_WIDTH-1:0]           o_dqs_pad_bscan_c,           // To BSCAN

   inout  wire                                 pad_wck_t,                   // Write DQS pad (WCK)
   inout  wire                                 pad_wck_c,                   // Write DQS pad (WCK)
   inout  wire                                 pad_dqs_t,                   // Read/Write DQS pad (WDQS/RDQS/EDC)
   inout  wire                                 pad_dqs_c,                   // Read/Write DQS pad (WDQS/RDQS/EDC)
   inout  wire  [DQ_WIDTH-1:0]                 pad_dq                       // Primary pad (DQ, DBI)

);

   logic dqs_rcs;
   logic dqs_sa_en;
   logic dqs_ren;
   logic dqs_pad_ie;
   logic dqs_pad_re;
   logic dqs_pad_oe;
   logic dqs_pad_wck_oe;

   assign dqs_rcs        = o_dqs_core_eg[`DDR_DQS_RCS_IDX    ];
   assign dqs_sa_en      = o_dqs_core_eg[`DDR_DQS_RE_IDX     ];  // RE is SA Enable.
   assign dqs_ren        = o_dqs_core_eg[`DDR_DQS_REN_IDX    ];
   assign dqs_pad_ie     = o_dqs_core_eg[`DDR_DQS_IE_IDX     ];  // DQS Rcvr enable
   assign dqs_pad_re     = o_dqs_core_eg[`DDR_DQS_RE_IDX     ];
   assign dqs_pad_oe     = o_dqs_core_eg[`DDR_DQS_OE_IDX     ];
   assign dqs_pad_wck_oe = o_dqs_core_eg[`DDR_DQS_WCK_OE_IDX ];

   // ------------------------------------------------------------------------
   // DQS Datapath
   // ------------------------------------------------------------------------

   // Module configuration parameters
   localparam [0:0]           DQS_RX_CC_MASK    = '0;          // RX Control instance mask
   localparam [0:0]           DQS_TX_CC_MASK    = '0;          // TX Control instance mask

   // Enable WCK and DQS TX slices
   localparam [DQS_WIDTH-1:0] DQS_TX_MASK = CA_TYPE ? '1 & ~(1'b1 << (`DDR_CA_CK_IDX)) :
                                                      '1 & ~(1'b1 << (`DDR_DQS_WCK_IDX))
                                                         & ~(1'b1 << (`DDR_DQS_DQS_IDX));

   // Mask all control slices in CK. Mask no slices in DQS
   localparam [DQS_WIDTH-1:0] DQS_TX_SLICE_MASK   = CA_TYPE ? {{(8){1'b1}}, {(1){1'b0}}} : '0;

   // Enable DQS RX slices
   localparam [DQS_WIDTH-1:0] DQS_RX_MASK         = CA_TYPE ? '1 : '1 & ~(1'b1 << (`DDR_DQS_DQS_IDX));

   localparam [DQS_WIDTH-1:0] DQS_LPDE_MASK       = DQS_TX_MASK;    // TX LPDE instance mask
   localparam [DQS_WIDTH-1:0] DQS_TX_PAD_MASK     = DQS_TX_MASK;    // TX PAD instance mask
   localparam [DQS_WIDTH-1:0] DQS_TX_CKE_MASK     = '1;             // TX CKE PAD instance mask
   localparam [DQS_WIDTH-1:0] DQS_RX_PAD_MASK     = DQS_RX_MASK;    // RX PAD instance mask
   localparam [DQS_WIDTH-1:0] DQS_RX_SLICE_MASK   = DQS_RX_MASK;    // RX slice instance mask
   localparam [DQS_WIDTH-1:0] DQS_SE_PAD          = DQS_TX_MASK;    // 1: Single-Ended Pad, 0: Differential Pad

`ifdef DDR_DEBUG
   initial begin
      $display("INFO: DQS_TX_PAD_MASK   =%0h", DQS_TX_PAD_MASK  );
      $display("INFO: DQS_TX_CKE_MASK   =%0h", DQS_TX_CKE_MASK  );
      $display("INFO: DQS_TX_WCK_MASK   =%0h", DQS_TX_WCK_MASK  );
      $display("INFO: DQS_TX_DQS_MASK   =%0h", DQS_TX_DQS_MASK  );
      $display("INFO: DQS_TX_SLICE_MASK =%0h", DQS_TX_SLICE_MASK);
      $display("INFO: DQS_RX_PAD_MASK   =%0h", DQS_RX_PAD_MASK  );
      $display("INFO: DQS_RX_SLICE_MASK =%0h", DQS_RX_SLICE_MASK);
      $display("INFO: DQS_TX_MASK       =%0h", DQS_TX_MASK      );
      $display("INFO: DQS_RX_MASK       =%0h", DQS_RX_MASK      );
      $display("INFO: DQS_WCK_IDX       =%0d", `DDR_DQS_WCK_IDX   );
      $display("INFO: DQS_DQS_IDX       =%0d", `DDR_DQS_DQS_IDX   );
      $display("INFO: DQS_REN_IDX       =%0d", `DDR_DQS_REN_IDX   );
      $display("INFO: DQS_OE_IDX        =%0d", `DDR_DQS_OE_IDX    );
      $display("INFO: DQS_IE_IDX        =%0d", `DDR_DQS_IE_IDX    );
      $display("INFO: DQS_RE_IDX        =%0d", `DDR_DQS_RE_IDX    );
      $display("INFO: DQS_WCK_OE_IDX    =%0d", `DDR_DQS_WCK_OE_IDX);
      $display("INFO: DQS_WCS_IDX       =%0d", `DDR_DQS_WCS_IDX   );
      $display("INFO: DQS_RCS_IDX       =%0d", `DDR_DQS_RCS_IDX   );
   end
`endif

   // Transmitter Clocks
   logic dq_qdr_clk_0;                  // External clock - generated by DQS slice
   logic dq_qdr_clk_180;                // External clock - generated by DQS slice
   logic dq_ddr_clk_0;                  // External clock - generated by DQS slice
   logic dq_ddr_clk_180;                // External clock - generated by DQS slice
   logic dq_sdr_rt_clk;                 // External clock - generated by DQS slice
   logic dq_sdr_rt_clk_b;               // External clock - generated by DQS slice

   logic dqs_qdr_clk_0;                  // External clock - generated by DQS slice
   logic dqs_qdr_clk_180;                // External clock - generated by DQS slice
   logic dqs_ddr_clk_0;                  // External clock - generated by DQS slice
   logic dqs_ddr_clk_180;                // External clock - generated by DQS slice
   logic dqs_sdr_rt_clk;                 // External clock - generated by DQS slice
   logic dqs_sdr_rt_clk_b;               // External clock - generated by DQS slice

   logic sdr_clk;                    // External clock - generated by DQS slice
   logic sdr_clk_b;                  // External clock - generated by DQS slice
   logic sdr_div2_clk;               // External clock - generated by DQS slice
   logic sdr_div2_clk_b;             // External clock - generated by DQS slice

   // Inter-Slice Clocks
   logic rdqs_clk_0;                 // External clock - generated by DQS slice
   logic rdqs_clk_180;               // External clock - generated by DQS slice

   // Pad connections
   wire [DQS_WIDTH-1:0] dqs_t;       // Primary DQS pad (RDQS, WCK, CK)
   wire [DQS_WIDTH-1:0] dqs_c;       // Primary DQS pad (RDQS, WCK, CK)

   logic rst;
   logic wck, wck_b;
   logic rdqs, rdqs_b;
   logic ana_vref;

   // Strobe connections
   logic [DQS_WIDTH-1:0] dqs_pad_lpbk_t;
   logic [DQS_WIDTH-1:0] dqs_pad_lpbk_c;

   logic [DQS_WIDTH-1:0] dqs_core_ig;
   logic [DQS_WIDTH-1:0] dqs_core_ig_b;

   assign o_dqs_core_ig = dqs_core_ig[DP_DQS_WIDTH-1:0];

   // Loopback for WCK transmitter testing
   assign wck   = dqs_pad_lpbk_t[`DDR_DQS_WCK_IDX];
   assign wck_b = dqs_pad_lpbk_c[`DDR_DQS_WCK_IDX];

   // Receiver for RDQS
   assign rdqs   = dqs_core_ig[`DDR_DQS_DQS_IDX];
   assign rdqs_b = dqs_core_ig_b[`DDR_DQS_DQS_IDX];

   // BSCAN output
   assign o_dqs_pad_bscan_t = dqs_pad_lpbk_t[TXRX_DQS_WIDTH-1:0];
   assign o_dqs_pad_bscan_c = dqs_pad_lpbk_c[TXRX_DQS_WIDTH-1:0];

   //// Pad assignment
   //assign pad_wck_t = dqs_t[`DDR_DQS_WCK_IDX];
   //assign pad_wck_c = dqs_c[`DDR_DQS_WCK_IDX];

   //// Pad assignment
   //assign pad_dqs_t = dqs_t[`DDR_DQS_DQS_IDX];
   //assign pad_dqs_c = dqs_c[`DDR_DQS_DQS_IDX];

   logic [RX1WIDTH-1:0] dq_pad_rx_cmn_cfg;
   logic [TX1WIDTH-1:0] dq_pad_tx_cmn_cfg;
   logic [A1WIDTH-1:0]  dq_sa_cmn_cfg;

   logic dq_hiz_cmn_n;
   logic dq_pad_cmn_oe;
   logic dq_pad_cmn_wck_oe;
   logic dq_pad_cmn_ie;
   logic dq_pad_cmn_re;
   logic dq_sa_cmn_en;
   logic dq_pad_bscan_cmn_n;
   logic dq_pad_bscan_cmn_oe;
   logic dq_pad_bscan_cmn_ie;
   logic [DEC_WGBWIDTH-1:0] dq_wgb_mode;
   logic [DEC_DGBWIDTH-1:0] dq_rgb_mode;
   fgb_t                    dq_fgb_mode;

   // Expand the EGRESS, FCDLY, XSEL, PIPE_EN CFG bus to DQS_WIDTH
   logic [E0WIDTH*DQS_WIDTH-1:0] dqs_egress_mode_ana;
   logic [E1WIDTH*DQS_WIDTH-1:0] dqs_egress_mode_dig;
   logic [DQS_WIDTH-1:0]         dqs_sdr_rt_pipe_en;

   logic [FWIDTH*DQS_WIDTH-1:0]  dqs_sdr_0_fc_dly;
   logic [MXWIDTH*DQS_WIDTH-1:0] dqs_sdr_0_x_sel ;
   logic [DQS_WIDTH-1:0]         dqs_sdr_0_pipe_en;
   logic [FWIDTH*DQS_WIDTH-1:0]  dqs_sdr_1_fc_dly;
   logic [MXWIDTH*DQS_WIDTH-1:0] dqs_sdr_1_x_sel ;
   logic [DQS_WIDTH-1:0]         dqs_sdr_1_pipe_en;
   logic [FWIDTH*DQS_WIDTH-1:0]  dqs_sdr_2_fc_dly;
   logic [MXWIDTH*DQS_WIDTH-1:0] dqs_sdr_2_x_sel ;
   logic [DQS_WIDTH-1:0]         dqs_sdr_2_pipe_en;
   logic [FWIDTH*DQS_WIDTH-1:0]  dqs_sdr_3_fc_dly;
   logic [MXWIDTH*DQS_WIDTH-1:0] dqs_sdr_3_x_sel ;
   logic [DQS_WIDTH-1:0]         dqs_sdr_3_pipe_en;
   logic [(MXWIDTH-1)*DQS_WIDTH-1:0] dqs_ddr_0_x_sel;
   logic [DQS_WIDTH-1:0]             dqs_ddr_0_pipe_en;
   logic [(MXWIDTH-1)*DQS_WIDTH-1:0] dqs_ddr_1_x_sel;
   logic [DQS_WIDTH-1:0]             dqs_ddr_1_pipe_en;

   always_comb
   begin
      dqs_egress_mode_ana                           = '0;
      dqs_egress_mode_dig                           = '0;
      dqs_sdr_rt_pipe_en                            = '0;
      dqs_egress_mode_ana[E0WIDTH*DP_DQS_WIDTH-1:0] = i_dqs_egress_mode_ana;
      dqs_egress_mode_dig[E1WIDTH*DP_DQS_WIDTH-1:0] = i_dqs_egress_mode_dig;
      dqs_sdr_rt_pipe_en[DP_DQS_WIDTH-1:0]          = i_dqs_sdr_rt_pipe_en;
   end

   always_comb
   begin
      dqs_sdr_0_fc_dly                           = '0 ;
      dqs_sdr_0_x_sel                            = '0 ;
      dqs_sdr_0_pipe_en                          = '0 ;
      dqs_sdr_1_fc_dly                           = '0 ;
      dqs_sdr_1_x_sel                            = '0 ;
      dqs_sdr_1_pipe_en                          = '0 ;
      dqs_sdr_2_fc_dly                           = '0 ;
      dqs_sdr_2_x_sel                            = '0 ;
      dqs_sdr_2_pipe_en                          = '0 ;
      dqs_sdr_3_fc_dly                           = '0 ;
      dqs_sdr_3_x_sel                            = '0 ;
      dqs_sdr_3_pipe_en                          = '0 ;
      dqs_sdr_0_fc_dly[FWIDTH*DP_DQS_WIDTH-1:0]  = i_dqs_sdr_0_fc_dly;
      dqs_sdr_0_x_sel[MXWIDTH*DP_DQS_WIDTH-1:0]  = i_dqs_sdr_0_x_sel   ;
      dqs_sdr_0_pipe_en[DP_DQS_WIDTH-1:0]        = i_dqs_sdr_0_pipe_en ;
      dqs_sdr_1_fc_dly[FWIDTH*DP_DQS_WIDTH-1:0]  = i_dqs_sdr_1_fc_dly;
      dqs_sdr_1_x_sel[MXWIDTH*DP_DQS_WIDTH-1:0]  = i_dqs_sdr_1_x_sel   ;
      dqs_sdr_1_pipe_en[DP_DQS_WIDTH-1:0]        = i_dqs_sdr_1_pipe_en ;
      dqs_sdr_2_fc_dly[FWIDTH*DP_DQS_WIDTH-1:0]  = i_dqs_sdr_2_fc_dly;
      dqs_sdr_2_x_sel[MXWIDTH*DP_DQS_WIDTH-1:0]  = i_dqs_sdr_2_x_sel   ;
      dqs_sdr_2_pipe_en[DP_DQS_WIDTH-1:0]        = i_dqs_sdr_2_pipe_en ;
      dqs_sdr_3_fc_dly[FWIDTH*DP_DQS_WIDTH-1:0]  = i_dqs_sdr_3_fc_dly;
      dqs_sdr_3_x_sel[MXWIDTH*DP_DQS_WIDTH-1:0]  = i_dqs_sdr_3_x_sel   ;
      dqs_sdr_3_pipe_en[DP_DQS_WIDTH-1:0]        = i_dqs_sdr_3_pipe_en ;
   end

   always_comb
   begin
      dqs_ddr_0_x_sel                                = '0 ;
      dqs_ddr_0_pipe_en                              = '0 ;
      dqs_ddr_1_x_sel                                = '0 ;
      dqs_ddr_1_pipe_en                              = '0 ;
      dqs_ddr_0_x_sel[(MXWIDTH-1)*DP_DQS_WIDTH-1:0]  = i_dqs_ddr_0_x_sel   ;
      dqs_ddr_0_pipe_en[DP_DQS_WIDTH-1:0]            = i_dqs_ddr_0_pipe_en ;
      dqs_ddr_1_x_sel[(MXWIDTH-1)*DP_DQS_WIDTH-1:0]  = i_dqs_ddr_1_x_sel   ;
      dqs_ddr_1_pipe_en[DP_DQS_WIDTH-1:0]            = i_dqs_ddr_1_pipe_en ;
   end

   always_comb
   begin
   end

   //Expand egress BSCAN bus width to DQS_WIDTH
   logic [DQS_WIDTH-1:0]       dqs_pad_bscan_t;
   logic [DQS_WIDTH-1:0]       dqs_pad_bscan_c;

   always_comb
   begin
      dqs_pad_bscan_t                     = '0;
      dqs_pad_bscan_c                     = '0;
      dqs_pad_bscan_t[TXRX_DQS_WIDTH-1:0] = i_dqs_pad_bscan_t;
      dqs_pad_bscan_c[TXRX_DQS_WIDTH-1:0] = i_dqs_pad_bscan_c;
   end

   // Expand TX, RX, SA CFG buses to DQS_WIDTH
   logic [A0WIDTH*DQS_WIDTH-1:0]  dqs_sa_cfg;                // SA configuration
   logic [RX0WIDTH*DQS_WIDTH-1:0] dqs_pad_rx_cfg;            // Pad Rx configuration
   logic [TX0WIDTH*DQS_WIDTH-1:0] dqs_pad_tx_cfg;            // Pad Tx configuration
   logic [LWIDTH*DQS_WIDTH-1:0]   dqs_xdr_lpde_cfg;          // TX per-bit LPDE setting

   always_comb
   begin
      dqs_sa_cfg                                       = '0 ;
      dqs_pad_rx_cfg                                   = '0 ;
      dqs_pad_tx_cfg                                   = '0 ;
      dqs_xdr_lpde_cfg                                 = '0 ;
      dqs_sa_cfg[A0WIDTH*TXRX_DQS_WIDTH-1:0]           =  i_dqs_sa_cfg ;
      dqs_pad_rx_cfg[RX0WIDTH*TXRX_DQS_WIDTH-1:0]      =  i_dqs_pad_rx_cfg ;
      dqs_pad_tx_cfg[TX0WIDTH*TXRX_DQS_WIDTH-1:0]      =  i_dqs_pad_tx_cfg ;
      dqs_xdr_lpde_cfg[LWIDTH*TXRX_DQS_WIDTH-1:0]      =  i_dqs_xdr_lpde_cfg ;
   end

   ddr_dp #(
      .CA_TYPE                     (CA_TYPE),
      .DQS_TYPE                    ('1),
      .WIDTH                       (DQS_WIDTH),
      .NUM_RDPH                    (NUM_RDPH),
      .NUM_RPH                     (NUM_RPH),
      .NUM_WDPH                    (NUM_WDPH),
      .NUM_WPH                     (NUM_WPH),
      .TX0WIDTH                    (TX0WIDTH),
      .TX1WIDTH                    (TX1WIDTH),
      .RX0WIDTH                    (RX0WIDTH),
      .RX1WIDTH                    (RX1WIDTH),
      .A0WIDTH                     (A0WIDTH),
      .A1WIDTH                     (A1WIDTH),
      .A2WIDTH                     (A2WIDTH),
`ifdef DDR_DQS_VREF
      .VWIDTH                      (VWIDTH),
`endif
      .E0WIDTH                     (E0WIDTH),
      .E1WIDTH                     (E1WIDTH),
      .FWIDTH                      (FWIDTH),
      .MXWIDTH                     (MXWIDTH),
      .LWIDTH                      (LWIDTH),
      .P0WIDTH                     (P0WIDTH),
      .P1WIDTH                     (P1WIDTH),
      .DFIRDCLKEN_PEXTWIDTH        (DFIRDCLKEN_PEXTWIDTH),
      .RX_CC_MASK                  (DQS_RX_CC_MASK),
      .TX_CC_MASK                  (DQS_TX_CC_MASK),
      .LPDE_MASK                   (DQS_LPDE_MASK),
      .TX_PAD_MASK                 (DQS_TX_PAD_MASK),
      .TX_CKE_MASK                 (DQS_TX_CKE_MASK),
      .TX_WCK_MASK                 (DQS_TX_WCK_MASK),
      .TX_DQS_MASK                 (DQS_TX_DQS_MASK),
      .TX_SLICE_MASK               (DQS_TX_SLICE_MASK),
      .RX_PAD_MASK                 (DQS_RX_PAD_MASK),
      .RX_SLICE_MASK               (DQS_RX_SLICE_MASK),
      .SE_PAD                      (DQS_SE_PAD),
      .PS_DLY                      (PS_DLY),
      .FIFO_DEPTH                  (FIFO_DEPTH),
      .FREN_WIDTH                  (FREN_WIDTH),
      .SLICE_FIFO                  (SLICE_FIFO)
   ) u_dp_dqs (

      // Test Clock
      .i_scan_clk                  (i_scan_clk      ),
      .i_scan_mode                 (i_scan_mode     ),
      //.i_scan_cgc_ctrl             (i_scan_cgc_ctrl ),
      .o_tst_clk                   (o_tst_clk       ),

      // Common Clocks and Reset
      .i_rst                       (i_rst),
      .o_rst                       (rst),
      .i_pll_clk_0                 (i_pll_clk_0),
      .i_pll_clk_90                (i_pll_clk_90),
      .i_pll_clk_180               (i_pll_clk_180),
      .i_pll_clk_270               (i_pll_clk_270),

      // Transmitter Inter-Slice Clocks
      .i_qdr_clk_0                 (dqs_qdr_clk_0  ),
      .i_qdr_clk_180               (dqs_qdr_clk_180),
      .i_ddr_clk_0                 (dqs_ddr_clk_0  ),
      .i_ddr_clk_180               (dqs_ddr_clk_180),
      .i_sdr_rt_clk                (dqs_sdr_rt_clk  ),
      .i_sdr_rt_clk_b              (dqs_sdr_rt_clk_b),

      .i_sdr_clk                   (sdr_clk       ),
      .i_sdr_clk_b                 (sdr_clk_b     ),
      .i_sdr_div2_clk              (sdr_div2_clk  ),
      .i_sdr_div2_clk_b            (sdr_div2_clk_b),

      .i_phy_clk                   (o_phy_clk),
      .o_dqs_qdr_clk_0             (dqs_qdr_clk_0),
      .o_dqs_qdr_clk_180           (dqs_qdr_clk_180),
      .o_dqs_ddr_clk_0             (dqs_ddr_clk_0),
      .o_dqs_ddr_clk_180           (dqs_ddr_clk_180),
      .o_dqs_sdr_rt_clk            (dqs_sdr_rt_clk),
      .o_dqs_sdr_rt_clk_b          (dqs_sdr_rt_clk_b),

      .o_dq_qdr_clk_0              (dq_qdr_clk_0),
      .o_dq_qdr_clk_180            (dq_qdr_clk_180),
      .o_dq_ddr_clk_0              (dq_ddr_clk_0),
      .o_dq_ddr_clk_180            (dq_ddr_clk_180),
      .o_dq_sdr_rt_clk             (dq_sdr_rt_clk),
      .o_dq_sdr_rt_clk_b           (dq_sdr_rt_clk_b),

      .o_sdr_clk                   (sdr_clk),
      .o_sdr_clk_b                 (sdr_clk_b),
      .o_sdr_div2_clk              (sdr_div2_clk),
      .o_sdr_div2_clk_b            (sdr_div2_clk_b),

      .o_dfiwr_clk_1               (o_dfiwr_clk_1),
      .o_dfiwr_clk_2               (o_dfiwr_clk_2),
      .o_dfird_clk_1               (o_dfird_clk_1),
      .o_dfird_clk_2               (o_dfird_clk_2),
      .o_phy_clk                   (o_phy_clk),

      // Receiver Clocks
      .i_rdqs                      (rdqs),
      .i_rdqs_b                    (rdqs_b),
      .i_wck                       (wck),
      .i_wck_b                     (wck_b),

      // Receiver Inter-Slice Clocks
      .i_rdqs_clk_0                ('0),
      .i_rdqs_clk_180              ('0),
      .i_rx_sdr_clk                ('0),
      .o_rdqs_clk_0                (rdqs_clk_0),
      .o_rdqs_clk_180              (rdqs_clk_180),
      .o_rx_sdr_clk                (o_rx_sdr_clk),

      // Transmitter
      .i_egress_mode_ana           (dqs_egress_mode_ana),
      .i_egress_mode_dig           (dqs_egress_mode_dig),

      .i_tgb_mode                  (i_dqs_tgb_mode),
      .i_wgb_mode                  (i_dqs_wgb_mode),
      .o_wgb_mode                  (dq_wgb_mode),
      .i_ck2wck_ratio              (i_dqs_ck2wck_ratio),

      .i_csp_div_rst_n             (i_csp_div_rst_n),
      .i_dqs_dfi_wrtraffic         (i_dqs_dfi_wrtraffic),
      .i_dq_dfi_wrtraffic          (i_dq_dfi_wrtraffic),
      .i_dfiwrgb_mode              (i_dfiwrgb_mode),
      .i_dfirdgb_mode              (i_dfirdgb_mode),
      .i_dfirdclk_en               (i_dfirdclk_en),
      .i_dfirdclk_en_pulse_ext     (i_dfirdclk_en_pulse_ext),

      .i_sdr_rt_pipe_en            (dqs_sdr_rt_pipe_en),
      .i_sdr_0_fc_dly              (dqs_sdr_0_fc_dly),
      .i_sdr_0_x_sel               (dqs_sdr_0_x_sel),
      .i_sdr_0_pipe_en             (dqs_sdr_0_pipe_en),
      .i_sdr_1_fc_dly              (dqs_sdr_1_fc_dly),
      .i_sdr_1_x_sel               (dqs_sdr_1_x_sel),
      .i_sdr_1_pipe_en             (dqs_sdr_1_pipe_en),
      .i_sdr_2_fc_dly              (dqs_sdr_2_fc_dly),
      .i_sdr_2_x_sel               (dqs_sdr_2_x_sel),
      .i_sdr_2_pipe_en             (dqs_sdr_2_pipe_en),
      .i_sdr_3_fc_dly              (dqs_sdr_3_fc_dly),
      .i_sdr_3_x_sel               (dqs_sdr_3_x_sel),
      .i_sdr_3_pipe_en             (dqs_sdr_3_pipe_en),
      .i_ddr_0_x_sel               (dqs_ddr_0_x_sel),
      .i_ddr_0_pipe_en             (dqs_ddr_0_pipe_en),
      .i_ddr_1_x_sel               (dqs_ddr_1_x_sel),
      .i_ddr_1_pipe_en             (dqs_ddr_1_pipe_en),
      .i_xdr_lpde_cfg              (dqs_xdr_lpde_cfg),
      .i_dqs_qdr_pi_0_cfg          (i_dqs_qdr_pi_0_cfg),
      .i_dq_qdr_pi_0_cfg           (i_dq_qdr_pi_0_cfg),
      .i_dqs_ddr_pi_0_cfg          (i_dqs_ddr_pi_0_cfg),
      .i_dq_ddr_pi_0_cfg           (i_dq_ddr_pi_0_cfg),
      .i_dqs_sdr_rt_pi_cfg         (i_dqs_sdr_rt_pi_cfg),
      .i_dq_sdr_rt_pi_cfg          (i_dq_sdr_rt_pi_cfg),
      .i_sdr_pi_cfg                (i_sdr_pi_cfg),
      .i_dfi_pi_cfg                (i_dfi_pi_cfg),
      .i_sdr                       (i_dqs_sdr),

      // Receiver
      .ana_vref_in                 (ana_vref_in),
      .ana_vref_out                (/*OPEN*/),
`ifdef DDR_DQS_VREF
      .i_refgen_cfg                (i_dqs_refgen_cfg),
`endif
      .i_rgb_mode                  (i_dqs_rgb_mode),
      .i_fgb_mode                  (i_dqs_fgb_mode),
      .o_rgb_mode                  (dq_rgb_mode),
      .o_fgb_mode                  (dq_fgb_mode),
      .i_sdr_lpde_cfg              (i_dqs_sdr_lpde_cfg),
      .i_pre_filter_sel            (i_dqs_pre_filter_sel),
      .i_ren_pi_cfg                (i_dqs_ren_pi_cfg),
      .i_rcs_pi_cfg                (i_dqs_rcs_pi_cfg),
      .i_rdqs_pi_0_cfg             (i_dqs_rdqs_pi_0_cfg),
      .i_rdqs_pi_1_cfg             (i_dqs_rdqs_pi_1_cfg),
      .i_wck_mode                  (i_dqs_wck_mode),
      .i_ren                       (dqs_ren),
      .o_rcs                       (o_rcs),
      .o_rcs_pi_phase_sta          (o_dqs_rcs_pi_phase_sta),
      .o_ren_pi_phase_sta          (o_dqs_ren_pi_phase_sta),
      .i_rcs                       (dqs_rcs),
      .i_sa_cmn_en                 (dqs_sa_en),
      .o_sa_cmn_en                 (dq_sa_cmn_en),
      .o_sa                        (/*OPEN*/),
      .o_sdr                       (/*OPEN*/),
      .o_sdr_vld                   (/*OPEN*/),
      .o_rxfifo_empty_n            (/*OPEN*/),
      .i_rxfifo_read               ('0),
      .i_rxfifo_clr                ('0),
      .i_rxfifo_read_mask          ('0),

      // Pads
      .i_freeze_n_hv               ('1),
      .i_freeze_cmn_n              (i_dq_cmn_freeze_n),
      .i_hiz_cmn_n                 (i_dqs_hiz_n),
      .o_hiz_cmn_n                 (dq_hiz_cmn_n),

      .i_sa_cfg                    (dqs_sa_cfg),
      .i_sa_dly_cfg                ('0),
      .i_sa_cmn_cfg                (i_dqs_sa_cmn_cfg),          // Shared control to DQ SA
      .o_sa_cmn_cfg                (dq_sa_cmn_cfg),
      .i_pad_rx_cfg                (dqs_pad_rx_cfg),
      .i_pad_rx_cmn_cfg            (i_dqs_pad_rx_cmn_cfg),
      .i_pad_tx_cfg                (dqs_pad_tx_cfg),
      .i_pad_tx_cmn_cfg            (i_dqs_pad_tx_cmn_cfg),
      .o_pad_rx_cmn_cfg            (dq_pad_rx_cmn_cfg),         // Shared control to DQ pads
      .o_pad_tx_cmn_cfg            (dq_pad_tx_cmn_cfg),         // Shared control to DQ pads

      .i_pad_cmn_oe                (dqs_pad_oe),
      .o_pad_cmn_oe                (dq_pad_cmn_oe),
      .i_pad_cmn_wck_oe            (dqs_pad_wck_oe),
      .o_pad_cmn_wck_oe            (dq_pad_cmn_wck_oe),
      .i_pad_cmn_ie                (dqs_pad_ie),
      .o_pad_cmn_ie                (dq_pad_cmn_ie),
      .i_pad_cmn_re                (dqs_pad_re),
      .o_pad_cmn_re                (dq_pad_cmn_re),
      .o_core_ig                   (dqs_core_ig),
      .o_core_ig_b                 (dqs_core_ig_b),
      .o_core_eg                   (o_dqs_core_eg),
      .i_pad_bscan_cmn_n           (i_dqs_pad_bscan_n),
      .o_pad_bscan_cmn_n           (dq_pad_bscan_cmn_n),
      .i_pad_bscan_cmn_oe          (i_dqs_pad_bscan_oe),
      .o_pad_bscan_cmn_oe          (dq_pad_bscan_cmn_oe),
      .i_pad_bscan_cmn_ie          (i_dqs_pad_bscan_ie),
      .o_pad_bscan_cmn_ie          (dq_pad_bscan_cmn_ie),
      .i_pad_bscan_t               (dqs_pad_bscan_t),
      .i_pad_bscan_c               (dqs_pad_bscan_c),
      .o_pad_lpbk_t                (dqs_pad_lpbk_t),
      .o_pad_lpbk_c                (dqs_pad_lpbk_c),
    //.pad_t                       (dqs_t),
    //.pad_c                       (dqs_c)
    //.pad_t                       ({dqs_t[DQS_WIDTH-1:2],pad_dqs_t,pad_wck_t}),
    //.pad_c                       ({dqs_c[DQS_WIDTH-1:2],pad_dqs_c,pad_wck_c})
      .pad_t                       ({
                                     dqs_t[8],
                                     dqs_t[7],
                                     dqs_t[6],
                                     dqs_t[5],
                                     dqs_t[4],
                                     dqs_t[3],
                                     dqs_t[2],
                                     pad_dqs_t,
                                     pad_wck_t
                                    }
                                   ),
      .pad_c                       ({
                                     dqs_c[8],
                                     dqs_c[7],
                                     dqs_c[6],
                                     dqs_c[5],
                                     dqs_c[4],
                                     dqs_c[3],
                                     dqs_c[2],
                                     pad_dqs_c,
                                     pad_wck_c
                                    }
                                   )
   );

   // ------------------------------------------------------------------------
   // DQ Datapath
   // ------------------------------------------------------------------------

   // Module configuration parameters
   localparam [0:0]          DQ_RX_CC_MASK      = '1;                  // RX Control instance mask
   localparam [0:0]          DQ_TX_CC_MASK      = '1;                  // TX Control instance mask
   localparam [DQ_WIDTH-1:0] DQ_TX_PAD_MASK     = '0;                  // TX PAD instance mask
   localparam [DQ_WIDTH-1:0] DQ_TX_WCK_MASK     = '1;                  // TX WCK PAD instance mask
   localparam [DQ_WIDTH-1:0] DQ_TX_DQS_MASK     = '1;                  // TX WCK PAD instance mask
   localparam [DQ_WIDTH-1:0] DQ_LPDE_MASK       = '0;                  // TX LPDE instance mask
   localparam [DQ_WIDTH-1:0] DQ_RX_SLICE_MASK   = '0;                  // RX slice instance mask
   localparam [DQ_WIDTH-1:0] DQ_TX_SLICE_MASK   = '0;                  // TX slice instance mask
   localparam [DQ_WIDTH-1:0] DQ_SE_PAD          = '1;                  // 1: Single-Ended Pad, 0: Differential Pad

   // CA byte data does not have a receiver pad. Use the loopback receiver.
   localparam [DQ_WIDTH-1:0] DQ_RX_PAD_MASK     = {DQ_WIDTH{CA_TYPE}}; // RX PAD instance mask

`ifdef DDR_DEBUG
   initial begin
      $display("INFO: DQ_TX_PAD_MASK    =%0h", DQ_TX_PAD_MASK  );
      $display("INFO: DQ_TX_CKE_MASK    =%0h", DQ_TX_CKE_MASK  );
      $display("INFO: DQ_TX_WCK_MASK    =%0h", DQ_TX_WCK_MASK  );
      $display("INFO: DQ_TX_DQS_MASK    =%0h", DQ_TX_DQS_MASK  );
      $display("INFO: DQ_RX_PAD_MASK    =%0h", DQ_RX_PAD_MASK  );
      $display("INFO: DQ_RX_SLICE_MASK  =%0h", DQ_RX_SLICE_MASK);
      $display("INFO: DQ_TX_SLICE_MASK  =%0h", DQ_TX_SLICE_MASK);
   end
`endif

   // Slice Interconnect
   logic [DQ_WIDTH-1:0] dq_sdr_0_tx, dq_sdr_1_tx, dq_sdr_2_tx, dq_sdr_3_tx;

   // Strobe connections
   logic [DQ_WIDTH-1:0] dq_pad_lpbk_t;

   // BSCAN output
   assign o_dq_pad_bscan_t = dq_pad_lpbk_t;

   ddr_dp #(
      .CA_TYPE                     (CA_TYPE),
      .DQS_TYPE                    ('0),
      .WIDTH                       (DQ_WIDTH),
      .NUM_RDPH                    (NUM_RDPH),
      .NUM_RPH                     (NUM_RPH),
      .NUM_WDPH                    (NUM_WDPH),
      .NUM_WPH                     (NUM_WPH),
      .TX0WIDTH                    (TX0WIDTH),
      .TX1WIDTH                    (TX1WIDTH),
      .RX0WIDTH                    (RX0WIDTH),
      .RX1WIDTH                    (RX1WIDTH),
      .A0WIDTH                     (A0WIDTH),
      .A1WIDTH                     (A1WIDTH),
      .A2WIDTH                     (A2WIDTH),
   `ifdef DDR_DQS_VREF
      .VWIDTH                      (VWIDTH),
   `endif
      .E0WIDTH                     (E0WIDTH),
      .E1WIDTH                     (E1WIDTH),
      .FWIDTH                      (FWIDTH),
      .MXWIDTH                     (MXWIDTH),
      .LWIDTH                      (LWIDTH),
      .P0WIDTH                     (P0WIDTH),
      .P1WIDTH                     (P1WIDTH),
      .DFIRDCLKEN_PEXTWIDTH        (DFIRDCLKEN_PEXTWIDTH),
      .RX_CC_MASK                  (DQ_RX_CC_MASK),
      .TX_CC_MASK                  (DQ_TX_CC_MASK),
      .LPDE_MASK                   (DQ_LPDE_MASK),
      .TX_PAD_MASK                 (DQ_TX_PAD_MASK),
      .TX_CKE_MASK                 (DQ_TX_CKE_MASK),
      .TX_WCK_MASK                 (DQ_TX_WCK_MASK),
      .TX_DQS_MASK                 (DQ_TX_DQS_MASK),
      .TX_SLICE_MASK               (DQ_TX_SLICE_MASK),
      .RX_PAD_MASK                 (DQ_RX_PAD_MASK),
      .RX_SLICE_MASK               (DQ_RX_SLICE_MASK),
      .SE_PAD                      (DQ_SE_PAD),
      .PS_DLY                      (PS_DLY),
      .FIFO_DEPTH                  (FIFO_DEPTH),
      .FREN_WIDTH                  (FREN_WIDTH),
      .SLICE_FIFO                  (SLICE_FIFO)
   ) u_dp_dq (

      // Test Clock
      .i_scan_clk                  ('0),
      .i_scan_mode                 ('0),
      //.i_scan_cgc_ctrl             ('0),
      .o_tst_clk                   (/*OPEN*/),

      // Common Clocks and Reset
      .i_rst                       (rst),
      .o_rst                       (/*OPEN*/),
      .i_pll_clk_0                 ('0),
      .i_pll_clk_90                ('0),
      .i_pll_clk_180               ('0),
      .i_pll_clk_270               ('0),

      // Transmitter Inter-Slice Clocks
      .i_qdr_clk_0                 (dq_qdr_clk_0),
      .i_qdr_clk_180               (dq_qdr_clk_180),
      .i_ddr_clk_0                 (dq_ddr_clk_0),
      .i_ddr_clk_180               (dq_ddr_clk_180),
      .i_sdr_rt_clk                (dq_sdr_rt_clk),
      .i_sdr_rt_clk_b              (dq_sdr_rt_clk_b),

      .i_sdr_clk                   (sdr_clk),
      .i_sdr_clk_b                 (sdr_clk_b),
      .i_sdr_div2_clk              (sdr_div2_clk),
      .i_sdr_div2_clk_b            (sdr_div2_clk_b),
      .i_phy_clk                   (o_phy_clk),

      .o_dqs_qdr_clk_0             (/*OPEN*/),
      .o_dqs_qdr_clk_180           (/*OPEN*/),
      .o_dqs_ddr_clk_0             (/*OPEN*/),
      .o_dqs_ddr_clk_180           (/*OPEN*/),
      .o_dqs_sdr_rt_clk            (/*OPEN*/),
      .o_dqs_sdr_rt_clk_b          (/*OPEN*/),

      .o_dq_qdr_clk_0              (/*OPEN*/),
      .o_dq_qdr_clk_180            (/*OPEN*/),
      .o_dq_ddr_clk_0              (/*OPEN*/),
      .o_dq_ddr_clk_180            (/*OPEN*/),
      .o_dq_sdr_rt_clk             (/*OPEN*/),
      .o_dq_sdr_rt_clk_b           (/*OPEN*/),

      .o_sdr_clk                   (/*OPEN*/),
      .o_sdr_clk_b                 (/*OPEN*/),
      .o_sdr_div2_clk              (/*OPEN*/),
      .o_sdr_div2_clk_b            (/*OPEN*/),

      .o_dfiwr_clk_1               (/*OPEN*/),
      .o_dfiwr_clk_2               (/*OPEN*/),
      .o_dfird_clk_1               (/*OPEN*/),
      .o_dfird_clk_2               (/*OPEN*/),
      .o_phy_clk                   (/*OPEN*/),

      // Receiver Clocks
      .i_rdqs                      ('0),
      .i_rdqs_b                    ('0),
      .i_wck                       ('0),
      .i_wck_b                     ('0),

      // Receiver Inter-Slice Clocks
      .i_rdqs_clk_0                (rdqs_clk_0),
      .i_rdqs_clk_180              (rdqs_clk_180),
      .i_rx_sdr_clk                (o_rx_sdr_clk),
      .o_rdqs_clk_0                (/*OPEN*/),
      .o_rdqs_clk_180              (/*OPEN*/),
      .o_rx_sdr_clk                (/*OPEN*/),

      // Transmitter
      .i_egress_mode_ana           (i_dq_egress_mode_ana),
      .i_egress_mode_dig           (i_dq_egress_mode_dig),
      .i_tgb_mode                  ('0),                             // Unused default - no clock gen in DQ
      .i_wgb_mode                  (dq_wgb_mode),
      .o_wgb_mode                  (/*OPEN*/),
      .i_ck2wck_ratio              ('0),                             // Unused - no clock gen in DQ

      .i_csp_div_rst_n             ('0),                             // Unused - no clock gen in DQ
      .i_dqs_dfi_wrtraffic         ('0),
      .i_dq_dfi_wrtraffic          ('0),
      .i_dfiwrgb_mode              ('0),                             // Unused - no clock gen in DQ
      .i_dfirdgb_mode              ('0),                             // Unused - no clock gen in DQ
      .i_dfirdclk_en               ('0),                             // Unused - no clock gen in DQ
      .i_dfirdclk_en_pulse_ext     ('0),                             // Unused - no clock gen in DQ

      .i_sdr_rt_pipe_en            (i_dq_sdr_rt_pipe_en),
      .i_sdr_0_fc_dly              (i_dq_sdr_0_fc_dly),
      .i_sdr_0_x_sel               (i_dq_sdr_0_x_sel),
      .i_sdr_0_pipe_en             (i_dq_sdr_0_pipe_en),
      .i_sdr_1_fc_dly              (i_dq_sdr_1_fc_dly),
      .i_sdr_1_x_sel               (i_dq_sdr_1_x_sel),
      .i_sdr_1_pipe_en             (i_dq_sdr_1_pipe_en),
      .i_sdr_2_fc_dly              (i_dq_sdr_2_fc_dly),
      .i_sdr_2_x_sel               (i_dq_sdr_2_x_sel),
      .i_sdr_2_pipe_en             (i_dq_sdr_2_pipe_en),
      .i_sdr_3_fc_dly              (i_dq_sdr_3_fc_dly),
      .i_sdr_3_x_sel               (i_dq_sdr_3_x_sel),
      .i_sdr_3_pipe_en             (i_dq_sdr_3_pipe_en),
      .i_ddr_0_x_sel               (i_dq_ddr_0_x_sel),
      .i_ddr_0_pipe_en             (i_dq_ddr_0_pipe_en),
      .i_ddr_1_x_sel               (i_dq_ddr_1_x_sel),
      .i_ddr_1_pipe_en             (i_dq_ddr_1_pipe_en),
      .i_xdr_lpde_cfg              (i_dq_xdr_lpde_cfg),
      .i_dqs_qdr_pi_0_cfg          ('0),
      .i_dq_qdr_pi_0_cfg           ('0),
      .i_dqs_ddr_pi_0_cfg          ('0),
      .i_dq_ddr_pi_0_cfg           ('0),
      .i_dqs_sdr_rt_pi_cfg         ('0),
      .i_dq_sdr_rt_pi_cfg          ('0),
      .i_sdr_pi_cfg                ('0),
      .i_dfi_pi_cfg                ('0),
      .i_sdr                       (i_dq_sdr),

      // Receiver
      .ana_vref_in                 (ana_vref_in),          // No DQ internal REFGEN
      .ana_vref_out                (/*OPEN*/),          // No DQ internal REFGEN
`ifdef DDR_DQS_VREF
      .i_refgen_cfg                ('0),
`endif
      .i_rgb_mode                  (dq_rgb_mode),
      .o_rgb_mode                  (/*OPEN*/),
      .i_fgb_mode                  (dq_fgb_mode),
      .o_fgb_mode                  (/*OPEN*/),
      .i_sdr_lpde_cfg              ('0),
      .i_pre_filter_sel            ('0),
      .i_ren_pi_cfg                ('0),
      .i_rcs_pi_cfg                ('0),
      .i_rdqs_pi_0_cfg             ('0),
      .i_rdqs_pi_1_cfg             ('0),
      .i_wck_mode                  ('0),
      .i_ren                       ('0),
      .o_rcs                       (/*OPEN*/),
      .o_rcs_pi_phase_sta          (/*OPEN*/),
      .o_ren_pi_phase_sta          (/*OPEN*/),
      .i_rcs                       (dqs_rcs),
      .i_sa_cmn_en                 (dq_sa_cmn_en),
      .o_sa_cmn_en                 (/*OPEN*/),
      .o_sa                        (o_dq_sa),
      .o_sdr                       (o_dq_sdr),          // POW Format
      .o_sdr_vld                   (o_dq_sdr_vld),
      .o_rxfifo_empty_n            (o_dq_rxfifo_empty_n),
      .i_rxfifo_read               (i_dq_rxfifo_read),
      .i_rxfifo_clr                (i_dq_rxfifo_clr),
      .i_rxfifo_read_mask          (i_dq_rxfifo_read_mask),

      // Pads
      .i_freeze_n_hv               (i_dq_freeze_n_hv),
      .i_freeze_cmn_n              (i_dq_cmn_freeze_n),
      .i_hiz_cmn_n                 (dq_hiz_cmn_n),
      .o_hiz_cmn_n                 (/*OPEN*/),

      .i_sa_cfg                    (i_dq_sa_cfg),
      .i_sa_dly_cfg                (i_dq_sa_dly_cfg),
      .i_sa_cmn_cfg                (dq_sa_cmn_cfg),
      .o_sa_cmn_cfg                (/*OPEN*/),
      .i_pad_rx_cfg                (i_dq_pad_rx_cfg),
      .i_pad_rx_cmn_cfg            (dq_pad_rx_cmn_cfg),
      .i_pad_tx_cfg                (i_dq_pad_tx_cfg),
      .i_pad_tx_cmn_cfg            (dq_pad_tx_cmn_cfg),
      .o_pad_rx_cmn_cfg            (/*OPEN*/),
      .o_pad_tx_cmn_cfg            (/*OPEN*/),

      .i_pad_cmn_oe                (dq_pad_cmn_oe),
      .o_pad_cmn_oe                (/*OPEN*/),
      .i_pad_cmn_wck_oe            (dq_pad_cmn_wck_oe),
      .o_pad_cmn_wck_oe            (/*OPEN*/),
      .i_pad_cmn_ie                (dq_pad_cmn_ie),
      .o_pad_cmn_ie                (/*OPEN*/),
      .i_pad_cmn_re                (dq_pad_cmn_re),
      .o_pad_cmn_re                (/*OPEN*/),
      .o_core_ig                   (o_dq_core_ig),
      .o_core_ig_b                 (/*OPEN*/),
      .o_core_eg                   (o_dq_core_eg),
      .i_pad_bscan_cmn_n           (dq_pad_bscan_cmn_n),
      .o_pad_bscan_cmn_n           (/*OPEN*/),
      .i_pad_bscan_cmn_oe          (dq_pad_bscan_cmn_oe),
      .o_pad_bscan_cmn_oe          (/*OPEN*/),
      .i_pad_bscan_cmn_ie          (dq_pad_bscan_cmn_ie),
      .o_pad_bscan_cmn_ie          (/*OPEN*/),
      .i_pad_bscan_t               (i_dq_pad_bscan_t),
      .i_pad_bscan_c               ('0),
      .o_pad_lpbk_t                (dq_pad_lpbk_t),
      .o_pad_lpbk_c                (/*OPEN*/),
      .pad_t                       (pad_dq),
      .pad_c                       (/*OPEN*/)
   );

`ifndef SYNTHESIS
  `ifdef DDR_SPICE_PRINT
   `include "ddr_dq_task.svh"
  `endif
`endif

endmodule

module ddr_cc #(
   parameter [0:0]       CA_TYPE              =  1'b0,           // CA byte type enable
   parameter             WIDTH                =  9,              // Parallel bus width
`ifdef DDR_DQS_VREF
   parameter             VWIDTH               =  11,             // Vref configuration width
`endif
   parameter             LWIDTH               =  11,             // LPDE delay select width
   parameter             P0WIDTH              =  15,             // PI code select width
   parameter             P1WIDTH              =  9,              // PI Matching cell cfg width
   parameter             DFIRDCLKEN_PEXTWIDTH =  4,              // DFIRDCLK EN Pulse Extension count width
   parameter [0:0]       RX_CC_MASK           = '0,              // RX Control instance mask
   parameter [0:0]       TX_CC_MASK           = '0,              // TX Control instance mask
   parameter             PS_DLY               =  10              // PI code select width
) (

   // TEST
   input  logic                            i_scan_clk,
   input  logic                            i_scan_mode,
   //input  logic                            i_scan_cgc_ctrl,
   output logic [1:0]                      o_tst_clk,

   // Common Clocks and Reset
   input  logic                            i_rst,
   input  logic                            i_pll_clk_0,
   input  logic                            i_pll_clk_90,
   input  logic                            i_pll_clk_180,
   input  logic                            i_pll_clk_270,

   // Transmitter Clocks
   output logic                            o_dq_qdr_clk_0,
   output logic                            o_dq_qdr_clk_180,
   output logic                            o_dq_ddr_clk_0,
   output logic                            o_dq_ddr_clk_180,
   output logic                            o_dq_sdr_rt_clk,
   output logic                            o_dq_sdr_rt_clk_b,

   output logic                            o_sdr_clk,
   output logic                            o_sdr_clk_b,
   output logic                            o_sdr_div2_clk,
   output logic                            o_sdr_div2_clk_b,
   output logic                            o_phy_clk,

   output logic                            o_dqs_qdr_clk_0,
   output logic                            o_dqs_qdr_clk_180,
   output logic                            o_dqs_ddr_clk_0,
   output logic                            o_dqs_ddr_clk_180,
   output logic                            o_dqs_sdr_rt_clk,
   output logic                            o_dqs_sdr_rt_clk_b,

   output logic                            o_dfiwr_clk_1,
   output logic                            o_dfiwr_clk_2,
   output logic                            o_dfird_clk_1,
   output logic                            o_dfird_clk_2,

   // Receiver Clocks
   input  logic                            i_rdqs,
   input  logic                            i_rdqs_b,
   input  logic                            i_wck,
   input  logic                            i_wck_b,

   // Inter-Slice Clocks
   input  logic                            i_rdqs_clk_0,
   input  logic                            i_rdqs_clk_180,
   input  logic                            i_rx_sdr_clk,
   output logic                            o_rdqs_clk_0,
   output logic                            o_rdqs_clk_180,
   output logic                            o_rx_sdr_clk,

   // Transmitter
   input  logic [DEC_DGBWIDTH-1:0]         i_tgb_mode,
   input  logic [DEC_WGBWIDTH-1:0]         i_wgb_mode,
   input  logic [DEC_CK2WCKRWIDTH-1:0]     i_ck2wck_ratio,

   input  logic                            i_csp_div_rst_n,
   input  logic                            i_dqs_dfi_wrtraffic,
   input  logic                            i_dq_dfi_wrtraffic,
   input  logic [DEC_DFIGBWIDTH-1:0]       i_dfiwrgb_mode,
   input  logic [DEC_DFIGBWIDTH-1:0]       i_dfirdgb_mode,
   input  logic                            i_dfirdclk_en,
   input  logic [DFIRDCLKEN_PEXTWIDTH-1:0] i_dfirdclk_en_pulse_ext,

   input  logic [P0WIDTH-1:0]              i_dqs_qdr_pi_0_cfg,
   input  logic [P0WIDTH-1:0]              i_dq_qdr_pi_0_cfg,
   input  logic [P0WIDTH-1:0]              i_dqs_ddr_pi_0_cfg,
   input  logic [P0WIDTH-1:0]              i_dq_ddr_pi_0_cfg,
   input  logic [P0WIDTH-1:0]              i_dqs_sdr_rt_pi_cfg,
   input  logic [P0WIDTH-1:0]              i_dq_sdr_rt_pi_cfg,
   input  logic [P1WIDTH-1:0]              i_sdr_pi_cfg,
   input  logic [P1WIDTH-1:0]              i_dfi_pi_cfg,

   // Receiver
   input  logic [DEC_DGBWIDTH-1:0]         i_rgb_mode,
   input  fgb_t                            i_fgb_mode,
   input  logic                            i_wck_mode,
   input  logic                            i_ren,
   input  logic [1:0]                      i_pre_filter_sel,
   output logic                            o_rcs_pi_phase_sta,
   output logic                            o_ren_pi_phase_sta,
   output logic                            o_rcs,
   input  logic                            i_rcs,
   input  logic [P0WIDTH-1:0]              i_ren_pi_cfg,
   input  logic [P0WIDTH-1:0]              i_rcs_pi_cfg,
   input  logic [P0WIDTH-1:0]              i_rdqs_pi_0_cfg,
   input  logic [P0WIDTH-1:0]              i_rdqs_pi_1_cfg,
   input  logic [LWIDTH-1:0]               i_sdr_lpde_cfg

);

   // ------------------------------------------------------------------------
   // Transmit Clocking
   // ------------------------------------------------------------------------

   generate
      if (!TX_CC_MASK) begin : TX_CC
         ddr_tx_cc #(
            .P0WIDTH                 (P0WIDTH),
            .P1WIDTH                 (P1WIDTH),
            .DFIRDCLKEN_PEXTWIDTH    (DFIRDCLKEN_PEXTWIDTH)
         ) u_tx_cc (
            // Test Clock
            .i_scan_clk              (i_scan_clk      ),
            .i_scan_mode             (i_scan_mode     ),
            //.i_scan_cgc_ctrl         (i_scan_cgc_ctrl ),
            .o_tst_clk               (o_tst_clk       ),

            .i_pll_clk_0             (i_pll_clk_0),
            .i_pll_clk_90            (i_pll_clk_90),
            .i_pll_clk_180           (i_pll_clk_180),
            .i_pll_clk_270           (i_pll_clk_270),

            .i_tgb_mode              (i_tgb_mode),
            .i_wgb_mode              (i_wgb_mode),
            .i_ck2wck_ratio          (i_ck2wck_ratio),
            .i_csp_div_rst_n         (i_csp_div_rst_n),
            .i_dqs_dfi_wrtraffic     (i_dqs_dfi_wrtraffic),
            .i_dq_dfi_wrtraffic      (i_dq_dfi_wrtraffic),
            .i_dfiwrgb_mode          (i_dfiwrgb_mode),
            .i_dfirdgb_mode          (i_dfirdgb_mode),
            .i_dfirdclk_en           (i_dfirdclk_en),
            .i_dfirdclk_en_pulse_ext (i_dfirdclk_en_pulse_ext),

            .i_dqs_qdr_pi_0_cfg      (i_dqs_qdr_pi_0_cfg),
            .i_dq_qdr_pi_0_cfg       (i_dq_qdr_pi_0_cfg),
            .i_dqs_ddr_pi_0_cfg      (i_dqs_ddr_pi_0_cfg),
            .i_dq_ddr_pi_0_cfg       (i_dq_ddr_pi_0_cfg),
            .i_dqs_sdr_rt_pi_cfg     (i_dqs_sdr_rt_pi_cfg),
            .i_dq_sdr_rt_pi_cfg      (i_dq_sdr_rt_pi_cfg),
            .i_sdr_pi_cfg            (i_sdr_pi_cfg),
            .i_dfi_pi_cfg            (i_dfi_pi_cfg),

            .o_dqs_qdr_clk_0         (o_dqs_qdr_clk_0),
            .o_dqs_qdr_clk_180       (o_dqs_qdr_clk_180),
            .o_dq_qdr_clk_0          (o_dq_qdr_clk_0),
            .o_dq_qdr_clk_180        (o_dq_qdr_clk_180),
            .o_dqs_ddr_clk_0         (o_dqs_ddr_clk_0),
            .o_dqs_ddr_clk_180       (o_dqs_ddr_clk_180),
            .o_dq_ddr_clk_0          (o_dq_ddr_clk_0),
            .o_dq_ddr_clk_180        (o_dq_ddr_clk_180),
            .o_dqs_sdr_rt_clk        (o_dqs_sdr_rt_clk),
            .o_dqs_sdr_rt_clk_b      (o_dqs_sdr_rt_clk_b),
            .o_dq_sdr_rt_clk         (o_dq_sdr_rt_clk),
            .o_dq_sdr_rt_clk_b       (o_dq_sdr_rt_clk_b),

            .o_sdr_clk               (o_sdr_clk),
            .o_sdr_clk_b             (o_sdr_clk_b),
            .o_sdr_div2_clk          (o_sdr_div2_clk),
            .o_sdr_div2_clk_b        (o_sdr_div2_clk_b),

            .o_dfiwr_clk_1           (o_dfiwr_clk_1),
            .o_dfiwr_clk_2           (o_dfiwr_clk_2),
            .o_dfird_clk_1           (o_dfird_clk_1),
            .o_dfird_clk_2           (o_dfird_clk_2),
            .o_phy_clk               (o_phy_clk)
         );

      end else begin : NO_TX_CC

         // Local signals
         assign o_dqs_qdr_clk_0      = '0;
         assign o_dqs_qdr_clk_180    = '0;
         assign o_dqs_ddr_clk_0      = '0;
         assign o_dqs_ddr_clk_180    = '0;
         assign o_dqs_sdr_rt_clk     = '0;
         assign o_dqs_sdr_rt_clk_b   = '0;

         assign o_sdr_clk            = '0;
         assign o_sdr_clk_b          = '0;
         assign o_sdr_div2_clk       = '0;
         assign o_sdr_div2_clk_b     = '0;
         assign o_phy_clk            = '0;

         assign o_dfiwr_clk_1        = '0;
         assign o_dfiwr_clk_2        = '0;
         assign o_dfird_clk_1        = '0;
         assign o_dfird_clk_2        = '0;

         // Output signals
         assign o_dq_qdr_clk_0      = '0;
         assign o_dq_qdr_clk_180    = '0;
         assign o_dq_ddr_clk_0      = '0;
         assign o_dq_ddr_clk_180    = '0;
         assign o_dq_sdr_rt_clk     = '0;
         assign o_dq_sdr_rt_clk_b   = '0;
      end
   endgenerate

   // ------------------------------------------------------------------------
   // Receive Clocking
   // ------------------------------------------------------------------------

   generate
      if (!RX_CC_MASK) begin : RX_CC
         ddr_rx_cc #(
            .CA_TYPE            (CA_TYPE),
            .LWIDTH             (LWIDTH),
         `ifdef DDR_DQS_VREF
            .VWIDTH             (VWIDTH),
         `endif
            .PWIDTH             (P0WIDTH),
            .PS_DLY             (PS_DLY)
         ) u_rx_cc (
            .i_rst              (i_rst),
            .i_tgb_mode         (i_tgb_mode),
            .i_rgb_mode         (i_rgb_mode),
`ifdef DDR_DQS_VREF
            .i_refgen_cfg       (i_refgen_cfg),
            .ana_vref           (/*OPEN*/),         // VREF gnerated in CMN block
`endif
            .i_rdqs             (i_rdqs),
            .i_rdqs_b           (i_rdqs_b),
            .i_wck              (i_wck),
            .i_wck_b            (i_wck_b),
            .i_pll_clk_0        (i_pll_clk_0),
            .i_pll_clk_90       (i_pll_clk_90),
            .i_pll_clk_180      (i_pll_clk_180),
            .i_pll_clk_270      (i_pll_clk_270),
            .i_csp_div_rst_n    (i_csp_div_rst_n),
            .i_wck_mode         (i_wck_mode),
            .i_ren              (i_ren),
            .i_pre_filter_sel   (i_pre_filter_sel),
            .o_rcs              (o_rcs),
            .i_rcs              (i_rcs),
            .i_rcs_pi_cfg       (i_rcs_pi_cfg),
            .i_ren_pi_cfg       (i_ren_pi_cfg),
            .i_rdqs_pi_0_cfg    (i_rdqs_pi_0_cfg),
            .i_rdqs_pi_1_cfg    (i_rdqs_pi_1_cfg),
            .o_rdqs_clk_0       (o_rdqs_clk_0),
            .o_rdqs_clk_180     (o_rdqs_clk_180),
            .o_rcs_pi_phase_sta (o_rcs_pi_phase_sta),
            .o_ren_pi_phase_sta (o_ren_pi_phase_sta),
            .i_sdr_lpde_cfg     (i_sdr_lpde_cfg),
            .o_sdr_clk          (o_rx_sdr_clk)
         );
      end else begin : NO_RX_CC
         assign o_rcs              = i_rcs;
         assign o_rdqs_clk_0       = i_rdqs_clk_0;
         assign o_rdqs_clk_180     = i_rdqs_clk_180;
         assign o_rcs_pi_phase_sta = '0;
         assign o_ren_pi_phase_sta = '0;
         assign o_rx_sdr_clk   = i_rx_sdr_clk;
      end
   endgenerate

endmodule

module ddr_dp #(
   parameter [0:0]       CA_TYPE              =  1'b0,           // CA byte type enable
   parameter [0:0]       DQS_TYPE             =  1'b0,           // DQS type enable
   parameter             WIDTH                =  9,              // Parallel bus width
   parameter             NUM_RDPH             =  8,              // Read datapath data phases (includes R/F)
   parameter             NUM_RPH              =  8,              // Read fifo data phases (includes R/F)
   parameter             NUM_WDPH             =  8,              // Write datapath data phases (includes R/F)
   parameter             NUM_WPH              =  8,              // Write gearbox data phases (includes R/F)
   parameter             RWIDTH               = NUM_RPH * WIDTH, // Read data width
   parameter             WWIDTH               = NUM_WPH * WIDTH, // Write data width
   parameter             TX0WIDTH             =  14,             // Tx IO configuration width
   parameter             TX1WIDTH             =  5,              // Tx IO configuration width
   parameter             RX0WIDTH             =  8,              // Rx IO configuration width
   parameter             RX1WIDTH             =  8,              // Rx IO configuration width
   parameter             A0WIDTH              =  24,             // Sense amp configuration width
   parameter             A1WIDTH              =  24,             // Sense amp configuration width
   parameter             A2WIDTH              =  32,             // Sense amp configuration width
`ifdef DDR_DQS_VREF
   parameter             VWIDTH               =  11,             // Vref configuration width
`endif
   parameter             E0WIDTH              =  6,              // Tx egress mode width (ANA)
   parameter             E1WIDTH              =  7,              // Tx egress mode width (DIG)
   parameter             FWIDTH               =  2,              // Full cycle delay select width
   parameter             MXWIDTH              =  3,              // Mux-X select width width
   parameter             LWIDTH               =  11,             // LPDE delay select width
   parameter             P0WIDTH              =  15,             // PI code select width
   parameter             P1WIDTH              =  9,              // PI Matching cell cfg width
   parameter             DFIRDCLKEN_PEXTWIDTH =  4,              // DFIRDCLK EN Pulse Extension count width
   parameter [0:0]       RX_CC_MASK           = '0,              // RX Control instance mask
   parameter [0:0]       TX_CC_MASK           = '0,              // TX Control instance mask
   parameter [WIDTH-1:0] LPDE_MASK            = '0,              // TX LPDE instance mask
   parameter [WIDTH-1:0] TX_PAD_MASK          = '0,              // TX PAD instance mask
   parameter [WIDTH-1:0] TX_CKE_MASK          = '0,              // TX PAD instance mask
   parameter [WIDTH-1:0] TX_WCK_MASK          = '0,              // TX PAD instance mask
   parameter [WIDTH-1:0] TX_DQS_MASK          = '0,              // TX PAD instance mask
   parameter [WIDTH-1:0] RX_PAD_MASK          = '0,              // RX PAD instance mask
   parameter [WIDTH-1:0] RX_SLICE_MASK        = '0,              // RX slice instance mask
   parameter [WIDTH-1:0] TX_SLICE_MASK        = '0,              // TX slice instance mask
   parameter [WIDTH-1:0] SE_PAD               = '0,              // 1: Single-Ended Pad, 0: Differential Pad
   parameter             PS_DLY               =  10,             // PI code select width
   parameter             FREN_WIDTH           =  1*2+1,           // RX FIFO Read enable width
   parameter             FIFO_DEPTH           =  8,              // FIFO depth
   parameter [0:0]       SLICE_FIFO           =  1'b1            // RX FIFO enable
) (

   // TEST
   input  logic                            i_scan_clk,
   input  logic                            i_scan_mode,
   //input  logic                            i_scan_cgc_ctrl,
   output logic [1:0]                      o_tst_clk,

   // Common Clocks and Reset
   input  logic                            i_rst,
   output logic                            o_rst,
   input  logic                            i_pll_clk_0,
   input  logic                            i_pll_clk_90,
   input  logic                            i_pll_clk_180,
   input  logic                            i_pll_clk_270,

   // Transmitter Clocks
   input  logic                            i_qdr_clk_0,
   input  logic                            i_qdr_clk_180,
   input  logic                            i_ddr_clk_0,
   input  logic                            i_ddr_clk_180,
   input  logic                            i_sdr_rt_clk,
   input  logic                            i_sdr_rt_clk_b,
   input  logic                            i_sdr_clk,
   input  logic                            i_sdr_clk_b,
   input  logic                            i_sdr_div2_clk,
   input  logic                            i_sdr_div2_clk_b,
   input  logic                            i_phy_clk,

   output logic                            o_dqs_qdr_clk_0,
   output logic                            o_dqs_qdr_clk_180,
   output logic                            o_dqs_ddr_clk_0,
   output logic                            o_dqs_ddr_clk_180,
   output logic                            o_dqs_sdr_rt_clk,
   output logic                            o_dqs_sdr_rt_clk_b,

   output logic                            o_dq_qdr_clk_0,
   output logic                            o_dq_qdr_clk_180,
   output logic                            o_dq_ddr_clk_0,
   output logic                            o_dq_ddr_clk_180,
   output logic                            o_dq_sdr_rt_clk,
   output logic                            o_dq_sdr_rt_clk_b,

   output logic                            o_sdr_clk,
   output logic                            o_sdr_clk_b,
   output logic                            o_sdr_div2_clk,
   output logic                            o_sdr_div2_clk_b,
   output logic                            o_phy_clk,

   output logic                            o_dfiwr_clk_1,
   output logic                            o_dfiwr_clk_2,
   output logic                            o_dfird_clk_1,
   output logic                            o_dfird_clk_2,

   // Receiver Clocks
   input  logic                            i_rdqs,
   input  logic                            i_rdqs_b,
   input  logic                            i_wck,
   input  logic                            i_wck_b,

   // Inter-Slice Clocks
   input  logic                            i_rdqs_clk_0,
   input  logic                            i_rdqs_clk_180,
   input  logic                            i_rx_sdr_clk,

   output logic                            o_rdqs_clk_0,
   output logic                            o_rdqs_clk_180,
   output logic                            o_rx_sdr_clk,

   // Transmitter
   input  logic [E0WIDTH*WIDTH-1:0]        i_egress_mode_ana,
   input  logic [E1WIDTH*WIDTH-1:0]        i_egress_mode_dig,

   input  logic [DEC_DGBWIDTH-1:0]         i_tgb_mode,
   input  logic [DEC_WGBWIDTH-1:0]         i_wgb_mode,
   output logic [DEC_WGBWIDTH-1:0]         o_wgb_mode,
   input  logic [DEC_CK2WCKRWIDTH-1:0]     i_ck2wck_ratio,

   input  logic                            i_csp_div_rst_n,
   input  logic                            i_dqs_dfi_wrtraffic,
   input  logic                            i_dq_dfi_wrtraffic,
   input  logic [DEC_DFIGBWIDTH-1:0]       i_dfiwrgb_mode,
   input  logic [DEC_DFIGBWIDTH-1:0]       i_dfirdgb_mode,
   input  logic                            i_dfirdclk_en,
   input  logic [DFIRDCLKEN_PEXTWIDTH-1:0] i_dfirdclk_en_pulse_ext,

   input  logic [WIDTH-1:0]                i_sdr_rt_pipe_en,
   input  logic [FWIDTH*WIDTH-1:0]         i_sdr_0_fc_dly,
   input  logic [MXWIDTH*WIDTH-1:0]        i_sdr_0_x_sel,
   input  logic [WIDTH-1:0]                i_sdr_0_pipe_en,
   input  logic [FWIDTH*WIDTH-1:0]         i_sdr_1_fc_dly,
   input  logic [MXWIDTH*WIDTH-1:0]        i_sdr_1_x_sel,
   input  logic [WIDTH-1:0]                i_sdr_1_pipe_en,
   input  logic [FWIDTH*WIDTH-1:0]         i_sdr_2_fc_dly,
   input  logic [MXWIDTH*WIDTH-1:0]        i_sdr_2_x_sel,
   input  logic [WIDTH-1:0]                i_sdr_2_pipe_en,
   input  logic [FWIDTH*WIDTH-1:0]         i_sdr_3_fc_dly,
   input  logic [MXWIDTH*WIDTH-1:0]        i_sdr_3_x_sel,
   input  logic [WIDTH-1:0]                i_sdr_3_pipe_en,
   input  logic [(MXWIDTH-1)*WIDTH-1:0]    i_ddr_0_x_sel,
   input  logic [WIDTH-1:0]                i_ddr_0_pipe_en,
   input  logic [(MXWIDTH-1)*WIDTH-1:0]    i_ddr_1_x_sel,
   input  logic [WIDTH-1:0]                i_ddr_1_pipe_en,
   input  logic [LWIDTH*WIDTH-1:0]         i_xdr_lpde_cfg,
   input  logic [P0WIDTH-1:0]              i_dqs_qdr_pi_0_cfg,
   input  logic [P0WIDTH-1:0]              i_dq_qdr_pi_0_cfg,
   input  logic [P0WIDTH-1:0]              i_dqs_ddr_pi_0_cfg,
   input  logic [P0WIDTH-1:0]              i_dq_ddr_pi_0_cfg,
   input  logic [P0WIDTH-1:0]              i_dqs_sdr_rt_pi_cfg,
   input  logic [P0WIDTH-1:0]              i_dq_sdr_rt_pi_cfg,
   input  logic [P1WIDTH-1:0]              i_sdr_pi_cfg,
   input  logic [P1WIDTH-1:0]              i_dfi_pi_cfg,
   input  logic [WWIDTH-1:0]               i_sdr,

   // Receiver
   input  logic [DEC_DGBWIDTH-1:0]         i_rgb_mode,
   output logic [DEC_DGBWIDTH-1:0]         o_rgb_mode,
   input  fgb_t                            i_fgb_mode,
   output fgb_t                            o_fgb_mode,
   input  logic                            ana_vref_in,
   output logic                            ana_vref_out,
`ifdef DDR_DQS_VREF
   input  logic [VWIDTH-1:0]               i_refgen_cfg,
`endif
   input  logic                            i_wck_mode,
   input  logic                            i_ren,
   input  logic [1:0]                      i_pre_filter_sel,
   output logic                            o_rcs,
   output logic                            o_rcs_pi_phase_sta,
   output logic                            o_ren_pi_phase_sta,
   input  logic                            i_rcs,
   input  logic [P0WIDTH-1:0]              i_ren_pi_cfg,
   input  logic [P0WIDTH-1:0]              i_rcs_pi_cfg,
   input  logic [P0WIDTH-1:0]              i_rdqs_pi_0_cfg,
   input  logic [P0WIDTH-1:0]              i_rdqs_pi_1_cfg,
   input  logic [LWIDTH-1:0]               i_sdr_lpde_cfg,
   input  logic                            i_sa_cmn_en,
   output logic                            o_sa_cmn_en,
   output logic [4*WIDTH-1:0]              o_sa,
   output logic [RWIDTH-1:0]               o_sdr,
   output logic [WIDTH-1:0]                o_sdr_vld,
   output logic [WIDTH-1:0]                o_rxfifo_empty_n,
   input  logic [FREN_WIDTH-1:0]           i_rxfifo_read,
   input  logic                            i_rxfifo_clr,
   input  logic                            i_rxfifo_read_mask,

   // Pads
   input  logic                            i_freeze_n_hv,
   input  logic                            i_freeze_cmn_n,
   input  logic                            i_hiz_cmn_n,
   output logic                            o_hiz_cmn_n,

   input  logic [A0WIDTH*WIDTH-1:0]        i_sa_cfg,            // Per SA configuration
   input  logic [A1WIDTH-1:0]              i_sa_cmn_cfg,        // Shared configuration
   output logic [A1WIDTH-1:0]              o_sa_cmn_cfg,      // Shared configuration
   input  logic [A2WIDTH*WIDTH-1:0]        i_sa_dly_cfg,        // Per SA configuration

   input  logic [RX0WIDTH*WIDTH-1:0]       i_pad_rx_cfg,        // Per pad configuration
   input  logic [TX0WIDTH*WIDTH-1:0]       i_pad_tx_cfg,        // Per pad configuration
   input  logic [RX1WIDTH-1:0]             i_pad_rx_cmn_cfg,    // Shared configuration
   input  logic [TX1WIDTH-1:0]             i_pad_tx_cmn_cfg,    // Shared configuration

   output logic [RX1WIDTH-1:0]             o_pad_rx_cmn_cfg,    // Shared configuration
   output logic [TX1WIDTH-1:0]             o_pad_tx_cmn_cfg,    // Shared configuration

   input  logic                            i_pad_cmn_oe,
   output logic                            o_pad_cmn_oe,
   input  logic                            i_pad_cmn_wck_oe,
   output logic                            o_pad_cmn_wck_oe,
   input  logic                            i_pad_cmn_ie,
   output logic                            o_pad_cmn_ie,
   input  logic                            i_pad_cmn_re,
   output logic                            o_pad_cmn_re,
   output logic [WIDTH-1:0]                o_core_ig,
   output logic [WIDTH-1:0]                o_core_ig_b,
   output logic [WIDTH-1:0]                o_core_eg,
   input  logic                            i_pad_bscan_cmn_n,
   output logic                            o_pad_bscan_cmn_n,
   input  logic                            i_pad_bscan_cmn_oe,
   output logic                            o_pad_bscan_cmn_oe,
   input  logic                            i_pad_bscan_cmn_ie,
   output logic                            o_pad_bscan_cmn_ie,
   input  logic [WIDTH-1:0]                i_pad_bscan_t,       // From BSCAN
   input  logic [WIDTH-1:0]                i_pad_bscan_c,       // From BSCAN
   output logic [WIDTH-1:0]                o_pad_lpbk_t,        // To CA clkmux and BSCAN
   output logic [WIDTH-1:0]                o_pad_lpbk_c,        // To CA clkmux and BSCAN
   inout  wire  [WIDTH-1:0]                pad_t,
   inout  wire  [WIDTH-1:0]                pad_c
);

   // ------------------------------------------------------------------------
   // Pad abutment routing
   // ------------------------------------------------------------------------
   logic [DEC_WGBWIDTH-1:0]         wgb_mode ;

   // High-Fanout drivers
   ddr_wcm_bufx8 u_bufx8_0  (.i_a(i_pad_bscan_cmn_n), .o_z(o_pad_bscan_cmn_n));
   ddr_wcm_bufx8 u_bufx8_2  (.i_a(i_hiz_cmn_n),       .o_z(o_hiz_cmn_n));

   ddr_wcm_bufx8 u_bufx8_3  (.i_a(i_pad_cmn_oe),      .o_z(o_pad_cmn_oe)    );
   ddr_wcm_bufx8 u_bufx8_4  (.i_a(i_pad_cmn_wck_oe),  .o_z(o_pad_cmn_wck_oe));
   ddr_wcm_bufx8 u_bufx8_5  (.i_a(i_pad_cmn_ie),      .o_z(o_pad_cmn_ie)    );
   ddr_wcm_bufx8 u_bufx8_6  (.i_a(i_pad_cmn_re),      .o_z(o_pad_cmn_re)    );
   ddr_wcm_bufx8 u_bufx8_7  (.i_a(i_sa_cmn_en),       .o_z(o_sa_cmn_en)     );
   ddr_wcm_bufx8 u_bufx8_8 [DEC_WGBWIDTH-1:0] (.i_a(i_wgb_mode),         .o_z(wgb_mode));

   // Low-Speed drivers
   ddr_wcm_buf   u_buf_8                     (.i_a(i_pad_bscan_cmn_oe), .o_z(o_pad_bscan_cmn_oe));
   ddr_wcm_buf   u_buf_9                     (.i_a(i_pad_bscan_cmn_ie), .o_z(o_pad_bscan_cmn_ie));
   ddr_wcm_buf   u_buf_10                    (.i_a(i_rst),              .o_z(o_rst));
   ddr_wcm_buf   u_buf_11 [DEC_WGBWIDTH-1:0] (.i_a(i_wgb_mode),         .o_z(o_wgb_mode));
   ddr_wcm_buf   u_buf_12 [DEC_DGBWIDTH-1:0] (.i_a(i_rgb_mode),         .o_z(o_rgb_mode));
   ddr_wcm_buf   u_buf_13 [FGBWIDTH-1:0]     (.i_a(i_fgb_mode),         .o_z(o_fgb_mode));
   ddr_wcm_buf   u_buf_14 [RX1WIDTH-1:0]     (.i_a(i_pad_rx_cmn_cfg),   .o_z(o_pad_rx_cmn_cfg));
   ddr_wcm_buf   u_buf_15 [TX1WIDTH-1:0]     (.i_a(i_pad_tx_cmn_cfg),   .o_z(o_pad_tx_cmn_cfg));
   ddr_wcm_buf   u_buf_16 [A1WIDTH-1:0]      (.i_a(i_sa_cmn_cfg),       .o_z(o_sa_cmn_cfg));

   // ------------------------------------------------------------------------
   // Clock Control
   // ------------------------------------------------------------------------
   ddr_cc #(
      .CA_TYPE                 (CA_TYPE),
   `ifdef DDR_DQS_VREF
      .VWIDTH                  (VWIDTH),
   `endif
      .LWIDTH                  (LWIDTH),
      .P0WIDTH                 (P0WIDTH),
      .P1WIDTH                 (P1WIDTH),
      .DFIRDCLKEN_PEXTWIDTH    (DFIRDCLKEN_PEXTWIDTH),
      .RX_CC_MASK              (RX_CC_MASK),
      .TX_CC_MASK              (TX_CC_MASK),
      .PS_DLY                  (PS_DLY)
   ) u_cc (
      // Test Clock
      .i_scan_clk              (i_scan_clk      ),
      .i_scan_mode             (i_scan_mode     ),
      //.i_scan_cgc_ctrl         (i_scan_cgc_ctrl ),
      .o_tst_clk               (o_tst_clk),

      .i_rst                   (i_rst),
      .i_pll_clk_0             (i_pll_clk_0),
      .i_pll_clk_90            (i_pll_clk_90),
      .i_pll_clk_180           (i_pll_clk_180),
      .i_pll_clk_270           (i_pll_clk_270),

      .o_dq_qdr_clk_0          (o_dq_qdr_clk_0),
      .o_dq_qdr_clk_180        (o_dq_qdr_clk_180),
      .o_dq_ddr_clk_0          (o_dq_ddr_clk_0),
      .o_dq_ddr_clk_180        (o_dq_ddr_clk_180),
      .o_dq_sdr_rt_clk         (o_dq_sdr_rt_clk),
      .o_dq_sdr_rt_clk_b       (o_dq_sdr_rt_clk_b),

      .o_sdr_clk               (o_sdr_clk),
      .o_sdr_clk_b             (o_sdr_clk_b),
      .o_sdr_div2_clk          (o_sdr_div2_clk),
      .o_sdr_div2_clk_b        (o_sdr_div2_clk_b),
      .o_phy_clk               (o_phy_clk),

      .o_dqs_qdr_clk_0         (o_dqs_qdr_clk_0),
      .o_dqs_qdr_clk_180       (o_dqs_qdr_clk_180),
      .o_dqs_ddr_clk_0         (o_dqs_ddr_clk_0),
      .o_dqs_ddr_clk_180       (o_dqs_ddr_clk_180),
      .o_dqs_sdr_rt_clk        (o_dqs_sdr_rt_clk),
      .o_dqs_sdr_rt_clk_b      (o_dqs_sdr_rt_clk_b),

      .o_dfiwr_clk_1           (o_dfiwr_clk_1),
      .o_dfiwr_clk_2           (o_dfiwr_clk_2),
      .o_dfird_clk_1           (o_dfird_clk_1),
      .o_dfird_clk_2           (o_dfird_clk_2),

      .i_rdqs                  (i_rdqs),
      .i_rdqs_b                (i_rdqs_b),
      .i_wck                   (i_wck),
      .i_wck_b                 (i_wck_b),

      .i_rdqs_clk_0            (i_rdqs_clk_0),
      .i_rdqs_clk_180          (i_rdqs_clk_180),
      .i_rx_sdr_clk            (i_rx_sdr_clk),

      .o_ren_pi_phase_sta      (o_ren_pi_phase_sta),
      .o_rcs_pi_phase_sta      (o_rcs_pi_phase_sta),
      .o_rcs                   (o_rcs),
      .o_rdqs_clk_0            (o_rdqs_clk_0),
      .o_rdqs_clk_180          (o_rdqs_clk_180),
      .o_rx_sdr_clk            (o_rx_sdr_clk),

      .i_tgb_mode              (i_tgb_mode),
      .i_wgb_mode              (wgb_mode),
      .i_ck2wck_ratio          (i_ck2wck_ratio),

      .i_csp_div_rst_n         (i_csp_div_rst_n),
      .i_dqs_dfi_wrtraffic     (i_dqs_dfi_wrtraffic),
      .i_dq_dfi_wrtraffic      (i_dq_dfi_wrtraffic),
      .i_dfiwrgb_mode          (i_dfiwrgb_mode),
      .i_dfirdgb_mode          (i_dfirdgb_mode),
      .i_dfirdclk_en           (i_dfirdclk_en),
      .i_dfirdclk_en_pulse_ext (i_dfirdclk_en_pulse_ext),

      .i_dqs_qdr_pi_0_cfg      (i_dqs_qdr_pi_0_cfg),
      .i_dq_qdr_pi_0_cfg       (i_dq_qdr_pi_0_cfg),
      .i_dqs_ddr_pi_0_cfg      (i_dqs_ddr_pi_0_cfg),
      .i_dq_ddr_pi_0_cfg       (i_dq_ddr_pi_0_cfg),
      .i_dqs_sdr_rt_pi_cfg     (i_dqs_sdr_rt_pi_cfg),
      .i_dq_sdr_rt_pi_cfg      (i_dq_sdr_rt_pi_cfg),
      .i_sdr_pi_cfg            (i_sdr_pi_cfg),
      .i_dfi_pi_cfg            (i_dfi_pi_cfg),

      .i_rgb_mode              (i_rgb_mode),
      .i_fgb_mode              (i_fgb_mode),
      .i_wck_mode              (i_wck_mode),
      .i_ren                   (i_ren),
      .i_pre_filter_sel        (i_pre_filter_sel),
      .i_rcs                   (i_rcs),
      .i_ren_pi_cfg            (i_ren_pi_cfg),
      .i_rcs_pi_cfg            (i_rcs_pi_cfg),
      .i_rdqs_pi_0_cfg         (i_rdqs_pi_0_cfg),
      .i_rdqs_pi_1_cfg         (i_rdqs_pi_1_cfg),
      .i_sdr_lpde_cfg          (i_sdr_lpde_cfg)
   );

   // ------------------------------------------------------------------------
   // Datapath
   // ------------------------------------------------------------------------

   logic [WIDTH-1:0]   sdr_rx_vld;
   logic [WWIDTH-1:0]  sdr_tx_wop;
   logic [RWIDTH-1:0]  sdr_rx, sdr_rx_wop;
   logic [4*WIDTH-1:0] sa_rx;

   genvar j;
   generate

      // Convert to Words-Of-Phases (WOP) format
      //    Pn[Wn...W0]...P0[Wn...W0] -> Wn[Pn...P0]...W0[Pn...P0]
      //ddr_dp_pow2wop #(.WIDTH(WIDTH), .NUM_PH(NUM_WPH)) u_dp_pow2wop (.i_d(i_sdr),.o_d(sdr_tx_wop));
      assign sdr_tx_wop = i_sdr;

      for (j=0; j<WIDTH; j=j+1) begin: DSLICE
         ddr_dp_txrx #(
            .CA_TYPE                     (CA_TYPE),
            .DQS_TYPE                    (DQS_TYPE),
            .WIDTH                       (1),
            .NUM_RDPH                    (NUM_RDPH),
            .NUM_RPH                     (NUM_RPH),
            .NUM_WDPH                    (NUM_WDPH),
            .NUM_WPH                     (NUM_WPH),
            .LPDE_MASK                   (LPDE_MASK[j]),
            .TX_PAD_MASK                 (TX_PAD_MASK[j]),
            .TX_CKE_MASK                 (TX_CKE_MASK[j]),
            .TX_WCK_MASK                 (TX_WCK_MASK[j]),
            .TX_DQS_MASK                 (TX_DQS_MASK[j]),
            .TX_SLICE_MASK               (TX_SLICE_MASK[j]),
            .RX_PAD_MASK                 (RX_PAD_MASK[j]),
            .RX_SLICE_MASK               (RX_SLICE_MASK[j]),
            .TX0WIDTH                    (TX0WIDTH),
            .TX1WIDTH                    (TX1WIDTH),
            .RX0WIDTH                    (RX0WIDTH),
            .RX1WIDTH                    (RX1WIDTH),
            .A0WIDTH                     (A0WIDTH),
            .A1WIDTH                     (A1WIDTH),
            .A2WIDTH                     (A2WIDTH),
            .E0WIDTH                     (E0WIDTH),
            .E1WIDTH                     (E1WIDTH),
            .FWIDTH                      (FWIDTH),
            .MXWIDTH                     (MXWIDTH),
            .LWIDTH                      (LWIDTH),
            .SE_PAD                      (SE_PAD[j]),
            .FIFO_DEPTH                  (FIFO_DEPTH),
            .FREN_WIDTH                  (FREN_WIDTH),
            .SLICE_FIFO                  (SLICE_FIFO)
         ) u_dp_tx_rx (

            // Transmit
            .i_wgb_mode                  (wgb_mode),
            .i_egress_mode_ana           (i_egress_mode_ana[E0WIDTH*j+:E0WIDTH]),
            .i_egress_mode_dig           (i_egress_mode_dig[E1WIDTH*j+:E1WIDTH]),
            .i_qdr_clk_0                 (i_qdr_clk_0),
            .i_qdr_clk_180               (i_qdr_clk_180),
            .i_ddr_clk_0                 (i_ddr_clk_0),
            .i_ddr_clk_180               (i_ddr_clk_180),
            .i_sdr_clk                   (i_sdr_clk),
            .i_sdr_clk_b                 (i_sdr_clk_b),
            .i_sdr_div2_clk              (i_sdr_div2_clk),
            .i_sdr_div2_clk_b            (i_sdr_div2_clk_b),
            .i_sdr_rt_clk                (i_sdr_rt_clk),
            .i_sdr_rt_clk_b              (i_sdr_rt_clk_b),
            .i_sdr_rt_pipe_en            (i_sdr_rt_pipe_en[j]),
            .i_sdr_0_fc_dly              (i_sdr_0_fc_dly[FWIDTH*j+:FWIDTH]),
            .i_sdr_0_x_sel               (i_sdr_0_x_sel[MXWIDTH*j+:MXWIDTH]),
            .i_sdr_0_pipe_en             (i_sdr_0_pipe_en[j]),
            .i_sdr_1_fc_dly              (i_sdr_1_fc_dly[FWIDTH*j+:FWIDTH]),
            .i_sdr_1_x_sel               (i_sdr_1_x_sel[MXWIDTH*j+:MXWIDTH]),
            .i_sdr_1_pipe_en             (i_sdr_1_pipe_en[j]),
            .i_sdr_2_fc_dly              (i_sdr_2_fc_dly[FWIDTH*j+:FWIDTH]),
            .i_sdr_2_x_sel               (i_sdr_2_x_sel[MXWIDTH*j+:MXWIDTH]),
            .i_sdr_2_pipe_en             (i_sdr_2_pipe_en[j]),
            .i_sdr_3_fc_dly              (i_sdr_3_fc_dly[FWIDTH*j+:FWIDTH]),
            .i_sdr_3_x_sel               (i_sdr_3_x_sel[MXWIDTH*j+:MXWIDTH]),
            .i_sdr_3_pipe_en             (i_sdr_3_pipe_en[j]),
            .i_ddr_0_x_sel               (i_ddr_0_x_sel[(MXWIDTH-1)*j+:(MXWIDTH-1)]),
            .i_ddr_0_pipe_en             (i_ddr_0_pipe_en[j]),
            .i_ddr_1_x_sel               (i_ddr_1_x_sel[(MXWIDTH-1)*j+:(MXWIDTH-1)]),
            .i_ddr_1_pipe_en             (i_ddr_1_pipe_en[j]),
            .i_xdr_lpde_cfg              (i_xdr_lpde_cfg[LWIDTH*j+:LWIDTH]),
            .i_sdr                       (sdr_tx_wop[NUM_WPH*j+:NUM_WPH]),

            // Receive
            .i_rst                       (i_rst),
            .i_csp_div_rst_n             (i_csp_div_rst_n),
            .i_rdqs_clk_0                (o_rdqs_clk_0),
            .i_rdqs_clk_180              (o_rdqs_clk_180),
            .i_rx_sdr_clk                (i_rx_sdr_clk),
            .i_phy_clk                   (i_phy_clk),
            .i_rgb_mode                  (i_rgb_mode),
            .i_fgb_mode                  (i_fgb_mode),
            .ana_vref                    (ana_vref_in),
            .i_sa_cmn_en                 (i_sa_cmn_en),
            .o_sa                        (sa_rx[j*4+:4]),                    // WOP Format
            .o_sdr                       (sdr_rx_wop[j*NUM_RPH+:NUM_RPH]),   // WOP Format
            .o_sdr_vld                   (sdr_rx_vld[j]),
            .o_rxfifo_empty_n            (o_rxfifo_empty_n[j]),
            .i_rxfifo_read               (i_rxfifo_read),
            .i_rxfifo_clr                (i_rxfifo_clr),
            .i_rxfifo_read_mask          (i_rxfifo_read_mask),

            // Pads
            .i_freeze_cmn_n              (i_freeze_cmn_n),
            .i_freeze_n_hv               (i_freeze_n_hv),
            .i_hiz_cmn_n                 (i_hiz_cmn_n),
            .i_sa_cfg                    (i_sa_cfg[j*A0WIDTH+:A0WIDTH]),
            .i_sa_cmn_cfg                (i_sa_cmn_cfg),
            .i_sa_dly_cfg                (i_sa_dly_cfg[j*A2WIDTH+:A2WIDTH]),
            .i_pad_rx_cfg                (i_pad_rx_cfg[j*RX0WIDTH+:RX0WIDTH]),
            .i_pad_rx_cmn_cfg            (i_pad_rx_cmn_cfg),
            .i_pad_tx_cfg                (i_pad_tx_cfg[j*TX0WIDTH+:TX0WIDTH]),
            .i_pad_tx_cmn_cfg            (i_pad_tx_cmn_cfg),
            .i_pad_cmn_oe                (i_pad_cmn_oe),
            .i_pad_cmn_wck_oe            (i_pad_cmn_wck_oe),
            .i_pad_cmn_ie                (i_pad_cmn_ie),
            .i_pad_cmn_re                (i_pad_cmn_re),
            .o_core_ig                   (o_core_ig[j]),
            .o_core_ig_b                 (o_core_ig_b[j]),
            .o_core_eg                   (o_core_eg[j]),
            .i_pad_bscan_cmn_n           (i_pad_bscan_cmn_n),
            .i_pad_bscan_cmn_oe          (i_pad_bscan_cmn_oe),
            .i_pad_bscan_cmn_ie          (i_pad_bscan_cmn_ie),
            .i_pad_bscan_t               (i_pad_bscan_t[j]),
            .i_pad_bscan_c               (i_pad_bscan_c[j]),
            .o_pad_lpbk_t                (o_pad_lpbk_t[j]),
            .o_pad_lpbk_c                (o_pad_lpbk_c[j]),
            .pad_t                       (pad_t[j]),
            .pad_c                       (pad_c[j])
         );
      end

      // Convert to Phases-Of-Words (POW) format
      //    Wn[Pn...P0]...W0[Pn...P0] -> Pn[Wn...W0]...P0[Wn...W0]
      ddr_dp_wop2pow #(.WIDTH(WIDTH), .NUM_PH(NUM_RPH)) u_dp_wop2pow (.i_d(sdr_rx_wop),.o_d(sdr_rx));
      //assign sdr_rx = sdr_rx_wop; // FIXME - Need WOP for the UPHY

      assign o_sa = sa_rx;

   endgenerate

   assign o_sdr = sdr_rx;
   assign o_sdr_vld = sdr_rx_vld;

endmodule

module ddr_dp_txrx #(
   parameter [0:0]       CA_TYPE       =  1'b0,            // CA byte type enable
   parameter [0:0]       DQS_TYPE      =  1'b0,            // DQS type enable
   parameter             WIDTH         =  9,               // Parallel bus width
   parameter             NUM_RDPH      =  8,               // Read datapath data phases (includes R/F)
   parameter             NUM_RPH       =  8,               // Read fifo data phases (includes R/F)
   parameter             NUM_WDPH      =  8,               // Write datapath data phases (includes R/F)
   parameter             NUM_WPH       =  8,               // Write gearbox data phases (includes R/F)
   parameter             RWIDTH        = NUM_RPH  * WIDTH, // Read data width
   parameter             WWIDTH        = NUM_WPH  * WIDTH, // Write data width
   parameter             TX0WIDTH      =  14,              // Tx IO configuration width
   parameter             TX1WIDTH      =  5,               // Tx IO configuration width
   parameter             RX0WIDTH      =  8,               // Rx IO configuration width
   parameter             RX1WIDTH      =  8,               // Rx IO configuration width
   parameter             A0WIDTH       =  24,              // Sense amp configuration width
   parameter             A1WIDTH       =  24,              // Sense amp configuration width
   parameter             A2WIDTH       =  32,              // Sense amp configuration width
   parameter             E0WIDTH       =  6,               // Tx egress mode width (ANA)
   parameter             E1WIDTH       =  7,               // Tx egress mode width (DIG)
   parameter             FWIDTH        =  2,               // Full cycle delay select width
   parameter             MXWIDTH       =  3,               // Mux-X select width width
   parameter             LWIDTH        =  11,              // LPDE delay select width
   parameter [WIDTH-1:0] RX_PAD_MASK   = '0,               // RX pad instance mask
   parameter [WIDTH-1:0] TX_SLICE_MASK = '0,               // TX slice instance mask
   parameter [WIDTH-1:0] RX_SLICE_MASK = '0,               // RX slice instance mask
   parameter [WIDTH-1:0] LPDE_MASK     = '0,               // TX LPDE instance mask
   parameter [WIDTH-1:0] TX_PAD_MASK   = '0,               // TX PAD instance mask
   parameter [WIDTH-1:0] TX_CKE_MASK   = '0,               // TX PAD instance mask
   parameter [WIDTH-1:0] TX_WCK_MASK   = '0,               // TX PAD instance mask
   parameter [WIDTH-1:0] TX_DQS_MASK   = '0,               // TX PAD instance mask
   parameter [WIDTH-1:0] SE_PAD        = '0,               // 1: Single-Ended Pad, 0: Differential Pad
   parameter             FIFO_DEPTH    =  8,               // FIFO depth
   parameter             FREN_WIDTH    =  1*2+1,           // RX FIFO Read enable width
   parameter [0:0]       SLICE_FIFO    =  1'b1             // RX FIFO enable
) (

   // Transmitter Clocks and reset
   input  logic                            i_rst,
   input  logic [WIDTH-1:0]                i_qdr_clk_0,
   input  logic [WIDTH-1:0]                i_qdr_clk_180,
   input  logic [WIDTH-1:0]                i_ddr_clk_0,
   input  logic [WIDTH-1:0]                i_ddr_clk_180,
   input  logic [WIDTH-1:0]                i_sdr_clk,
   input  logic [WIDTH-1:0]                i_sdr_clk_b,
   input  logic [WIDTH-1:0]                i_sdr_div2_clk,
   input  logic [WIDTH-1:0]                i_sdr_div2_clk_b,
   input  logic [WIDTH-1:0]                i_sdr_rt_clk,
   input  logic [WIDTH-1:0]                i_sdr_rt_clk_b,

   // Receiver Clocks and reset
   input  logic                            i_csp_div_rst_n,
   input  logic                            i_rdqs_clk_0,
   input  logic                            i_rdqs_clk_180,
   input  logic                            i_rx_sdr_clk,
   input  logic                            i_phy_clk,

   // Transmitter
   input  logic [DEC_WGBWIDTH-1:0]         i_wgb_mode,
   input  logic [E0WIDTH*WIDTH-1:0]        i_egress_mode_ana,
   input  logic [E1WIDTH*WIDTH-1:0]        i_egress_mode_dig,
   input  logic [WIDTH-1:0]                i_sdr_rt_pipe_en,
   input  logic [FWIDTH*WIDTH-1:0]         i_sdr_0_fc_dly,
   input  logic [MXWIDTH*WIDTH-1:0]        i_sdr_0_x_sel,
   input  logic [WIDTH-1:0]                i_sdr_0_pipe_en,
   input  logic [FWIDTH*WIDTH-1:0]         i_sdr_1_fc_dly,
   input  logic [MXWIDTH*WIDTH-1:0]        i_sdr_1_x_sel,
   input  logic [WIDTH-1:0]                i_sdr_1_pipe_en,
   input  logic [FWIDTH*WIDTH-1:0]         i_sdr_2_fc_dly,
   input  logic [MXWIDTH*WIDTH-1:0]        i_sdr_2_x_sel,
   input  logic [WIDTH-1:0]                i_sdr_2_pipe_en,
   input  logic [FWIDTH*WIDTH-1:0]         i_sdr_3_fc_dly,
   input  logic [MXWIDTH*WIDTH-1:0]        i_sdr_3_x_sel,
   input  logic [WIDTH-1:0]                i_sdr_3_pipe_en,
   input  logic [(MXWIDTH-1)*WIDTH-1:0]    i_ddr_0_x_sel,
   input  logic [WIDTH-1:0]                i_ddr_0_pipe_en,
   input  logic [(MXWIDTH-1)*WIDTH-1:0]    i_ddr_1_x_sel,
   input  logic [WIDTH-1:0]                i_ddr_1_pipe_en,
   input  logic [LWIDTH*WIDTH-1:0]         i_xdr_lpde_cfg,
   input  logic [WWIDTH-1:0]               i_sdr,

   // Receiver
   input  logic [DEC_DGBWIDTH-1:0]         i_rgb_mode,
   input  fgb_t                            i_fgb_mode,
   input  logic                            ana_vref,
   input  logic                            i_sa_cmn_en,
   input  logic [A0WIDTH*WIDTH-1:0]        i_sa_cfg,
   input  logic [A1WIDTH-1:0]              i_sa_cmn_cfg,
   input  logic [A2WIDTH*WIDTH-1:0]        i_sa_dly_cfg,
   output logic [4*WIDTH-1:0]              o_sa,
   output logic [RWIDTH-1:0]               o_sdr,
   output logic [WIDTH-1:0]                o_sdr_vld,
   output logic [WIDTH-1:0]                o_rxfifo_empty_n,
   input  logic [FREN_WIDTH-1:0]           i_rxfifo_read,
   input  logic                            i_rxfifo_clr,
   input  logic                            i_rxfifo_read_mask,

   // Pads
   input  logic                            i_freeze_cmn_n,
   input  logic                            i_freeze_n_hv,
   input  logic                            i_hiz_cmn_n,
   input  logic [RX0WIDTH*WIDTH-1:0]       i_pad_rx_cfg,
   input  logic [RX1WIDTH-1:0]             i_pad_rx_cmn_cfg,
   input  logic [TX0WIDTH*WIDTH-1:0]       i_pad_tx_cfg,
   input  logic [TX1WIDTH-1:0]             i_pad_tx_cmn_cfg,
   input  logic                            i_pad_cmn_oe,
   input  logic                            i_pad_cmn_wck_oe,
   input  logic                            i_pad_cmn_ie,
   input  logic                            i_pad_cmn_re,
   output logic [WIDTH-1:0]                o_core_ig,
   output logic [WIDTH-1:0]                o_core_ig_b,
   output logic [WIDTH-1:0]                o_core_eg,
   input  logic                            i_pad_bscan_cmn_n,
   input  logic                            i_pad_bscan_cmn_oe,
   input  logic                            i_pad_bscan_cmn_ie,
   input  logic [WIDTH-1:0]                i_pad_bscan_t,  // From BSCAN
   input  logic [WIDTH-1:0]                i_pad_bscan_c,  // From BSCAN
   output logic [WIDTH-1:0]                o_pad_lpbk_t,   // To CA clkmux and BSCAN
   output logic [WIDTH-1:0]                o_pad_lpbk_c,   // To CA clkmux and BSCAN
   inout  wire  [WIDTH-1:0]                pad_t,
   inout  wire  [WIDTH-1:0]                pad_c

);

   wire [WIDTH-1:0] pad_eg_t;
   wire [WIDTH-1:0] pad_eg_c;

   // ------------------------------------------------------------------------
   // Transit
   // ------------------------------------------------------------------------

   genvar j;
   generate
      for (j=0; j<WIDTH; j=j+1) begin: TX_SLICE
         if (!TX_SLICE_MASK[j]) begin : TX_SLICE_MSK
            ddr_tx #(
               .WIDTH                       (1),
               .NUM_WDPH                    (NUM_WDPH),
               .NUM_WPH                     (NUM_WPH),
               .SLICE_MASK                  ('0),
               .LPDE_MASK                   (LPDE_MASK[j]),
               .PAD_MASK                    (TX_PAD_MASK[j]),
               .CKE_MASK                    (TX_CKE_MASK[j]),
               .WCK_MASK                    (TX_WCK_MASK[j]),
               .DQS_MASK                    (TX_DQS_MASK[j]),
               .TX0WIDTH                    (TX0WIDTH),
               .TX1WIDTH                    (TX1WIDTH),
               .E0WIDTH                     (E0WIDTH),
               .E1WIDTH                     (E1WIDTH),
               .FWIDTH                      (FWIDTH),
               .MXWIDTH                     (MXWIDTH),
               .LWIDTH                      (LWIDTH),
               .SE_PAD                      (SE_PAD[j])
            ) u_ddr_tx (
               .i_wgb_mode                  (i_wgb_mode),
               .i_egress_mode_ana           (i_egress_mode_ana[E0WIDTH*j+:E0WIDTH]),
               .i_egress_mode_dig           (i_egress_mode_dig[E1WIDTH*j+:E1WIDTH]),
               .i_qdr_clk_0                 (i_qdr_clk_0[j]),
               .i_qdr_clk_180               (i_qdr_clk_180[j]),
               .i_ddr_clk_0                 (i_ddr_clk_0[j]),
               .i_ddr_clk_180               (i_ddr_clk_180[j]),
               .i_sdr_clk                   (i_sdr_clk[j]),
               .i_sdr_clk_b                 (i_sdr_clk_b[j]),
               .i_sdr_div2_clk              (i_sdr_div2_clk[j]),
               .i_sdr_div2_clk_b            (i_sdr_div2_clk_b[j]),
               .i_sdr_rt_clk                (i_sdr_rt_clk[j]),
               .i_sdr_rt_clk_b              (i_sdr_rt_clk_b[j]),
               .i_sdr_rt_pipe_en            (i_sdr_rt_pipe_en[j]),
               .i_sdr_0_fc_dly              (i_sdr_0_fc_dly[FWIDTH*j+:FWIDTH]),
               .i_sdr_0_x_sel               (i_sdr_0_x_sel[MXWIDTH*j+:MXWIDTH]),
               .i_sdr_0_pipe_en             (i_sdr_0_pipe_en[j]),
               .i_sdr_1_fc_dly              (i_sdr_1_fc_dly[FWIDTH*j+:FWIDTH]),
               .i_sdr_1_x_sel               (i_sdr_1_x_sel[MXWIDTH*j+:MXWIDTH]),
               .i_sdr_1_pipe_en             (i_sdr_1_pipe_en[j]),
               .i_sdr_2_fc_dly              (i_sdr_2_fc_dly[FWIDTH*j+:FWIDTH]),
               .i_sdr_2_x_sel               (i_sdr_2_x_sel[MXWIDTH*j+:MXWIDTH]),
               .i_sdr_2_pipe_en             (i_sdr_2_pipe_en[j]),
               .i_sdr_3_fc_dly              (i_sdr_3_fc_dly[FWIDTH*j+:FWIDTH]),
               .i_sdr_3_x_sel               (i_sdr_3_x_sel[MXWIDTH*j+:MXWIDTH]),
               .i_sdr_3_pipe_en             (i_sdr_3_pipe_en[j]),
               .i_ddr_0_x_sel               (i_ddr_0_x_sel[(MXWIDTH-1)*j+:(MXWIDTH-1)]),
               .i_ddr_0_pipe_en             (i_ddr_0_pipe_en[j]),
               .i_ddr_1_x_sel               (i_ddr_1_x_sel[(MXWIDTH-1)*j+:(MXWIDTH-1)]),
               .i_ddr_1_pipe_en             (i_ddr_1_pipe_en[j]),
               .i_xdr_lpde_cfg              (i_xdr_lpde_cfg[LWIDTH*j+:LWIDTH]),
               .i_sdr                       (i_sdr[NUM_WPH*j+:NUM_WPH]),
               .i_freeze_cmn_n              (i_freeze_cmn_n),
               .i_freeze_n_hv               (i_freeze_n_hv),
               .i_hiz_cmn_n                 (i_hiz_cmn_n),
               .i_pad_cfg                   (i_pad_tx_cfg[j*TX0WIDTH+:TX0WIDTH]),
               .i_pad_cmn_cfg               (i_pad_tx_cmn_cfg),
               .i_pad_cmn_oe                (i_pad_cmn_oe),
               .i_pad_cmn_wck_oe            (i_pad_cmn_wck_oe),
               .i_pad_cmn_ie                (i_pad_cmn_ie),
               .o_core_eg                   (o_core_eg[j]),
               .i_pad_bscan_cmn_n           (i_pad_bscan_cmn_n),
               .i_pad_bscan_cmn_oe          (i_pad_bscan_cmn_oe),
               .i_pad_bscan_cmn_ie          (i_pad_bscan_cmn_ie),
               .i_pad_bscan_t               (i_pad_bscan_t[j]),
               .i_pad_bscan_c               (i_pad_bscan_c[j]),
               .o_pad_lpbk_t                (o_pad_lpbk_t[j]),
               .o_pad_lpbk_c                (o_pad_lpbk_c[j]),
               .o_pad_eg_t                  (pad_eg_t[j]),
               .o_pad_eg_c                  (pad_eg_c[j]),
               .pad_t                       (pad_t[j]),
               .pad_c                       (pad_c[j])
            );
         end else begin : NO_TX_SLICE
            ddr_wcm_buf u_buf_tx_0 (.i_a(i_sdr[NUM_WPH*j]), .o_z(o_core_eg[j]));
            ddr_wcm_buf u_buf_tx_1 (.i_a(i_sdr[NUM_WPH*j]), .o_z(o_pad_lpbk_t[j]));
            ddr_wcm_inv u_inv_tx_1 (.i_a(i_sdr[NUM_WPH*j]), .o_z(o_pad_lpbk_c[j]));
         end
      end
   endgenerate

   // ------------------------------------------------------------------------
   // Receive
   // ------------------------------------------------------------------------

   logic [WIDTH-1:0] sdr_vld;

   genvar i;
   generate
      for (i=0; i<WIDTH; i=i+1) begin: RX_SLICE
         if (!RX_SLICE_MASK[i]) begin : RX_SLICE_MSK
            if (CA_TYPE) begin: CA_RX
               // CA byte data does not have a receiver pad, so use the loopback receiver
               ddr_rx #(
                  .WIDTH                 (1),
                  .A0WIDTH               (A0WIDTH),
                  .A1WIDTH               (A1WIDTH),
                  .A2WIDTH               (A2WIDTH),
                  .RX0WIDTH              (RX0WIDTH),
                  .RX1WIDTH              (RX1WIDTH),
                  .NUM_RDPH              (NUM_RDPH),
                  .NUM_RPH               (NUM_RPH),
                  .PAD_MASK              (RX_PAD_MASK[i]),
                  .SLICE_MASK            ('0),
                  .SE_PAD                (SE_PAD[i]),
                  .FIFO_DEPTH            (FIFO_DEPTH),
                  .FREN_WIDTH            (FREN_WIDTH),
                  .SLICE_FIFO            (SLICE_FIFO)
               ) u_ddr_rx (
                  .i_rst                 (i_rst),
                  .i_csp_div_rst_n       (i_csp_div_rst_n),
                  .i_rdqs_clk_0          (i_rdqs_clk_0),
                  .i_rdqs_clk_180        (i_rdqs_clk_180),
                  .i_sdr_clk             (i_rx_sdr_clk),
                  .i_phy_clk             (i_phy_clk),
                  .i_rgb_mode            (i_rgb_mode),
                  .i_fgb_mode            (i_fgb_mode),
                  .ana_vref              (ana_vref),
                  .i_sa_cmn_en           (i_sa_cmn_en),
                  .i_sa_cfg              (i_sa_cfg),
                  .i_sa_cmn_cfg          (i_sa_cmn_cfg),
                  .i_sa_dly_cfg          (i_sa_dly_cfg),
                  .o_core_ig             (o_core_ig[i]),
                  .o_core_ig_b           (o_core_ig_b[i]),
                  .i_pad_cfg             (i_pad_rx_cfg[i*RX0WIDTH+:RX0WIDTH]),
                  .i_pad_cmn_cfg         (i_pad_rx_cmn_cfg),
                  .i_pad_cmn_ie          (i_pad_cmn_ie),
                  .i_pad_cmn_re          (i_pad_cmn_re),
                  .pad_t                 (o_pad_lpbk_t[i]),
                  .pad_c                 (o_pad_lpbk_c[i]),
                  .o_sa                  (o_sa[i*4+:4]),
                  .o_empty_n             (o_rxfifo_empty_n[i]),
                  .i_read                (i_rxfifo_read),
                  .i_clr                 (i_rxfifo_clr),
                  .i_read_mask           (i_rxfifo_read_mask),
                  .o_sdr                 (o_sdr[i*NUM_RPH+:NUM_RPH]),
                  .o_sdr_vld             (sdr_vld[i])
               );
            end else begin : DQ_RX
               ddr_rx #(
                  .DQS_TYPE              (DQS_TYPE),
                  .WIDTH                 (1),
                  .A0WIDTH               (A0WIDTH),
                  .A1WIDTH               (A1WIDTH),
                  .A2WIDTH               (A2WIDTH),
                  .RX0WIDTH              (RX0WIDTH),
                  .RX1WIDTH              (RX1WIDTH),
                  .NUM_RDPH              (NUM_RDPH),
                  .NUM_RPH               (NUM_RPH),
                  .PAD_MASK              (RX_PAD_MASK[i]),
                  .SLICE_MASK            ('0),
                  .SE_PAD                (SE_PAD[i]),
                  .FIFO_DEPTH            (FIFO_DEPTH),
                  .FREN_WIDTH            (FREN_WIDTH),
                  .SLICE_FIFO            (SLICE_FIFO)
               ) u_ddr_rx (
                  .i_rst                 (i_rst),
                  .i_csp_div_rst_n       (i_csp_div_rst_n),
                  .i_rdqs_clk_0          (i_rdqs_clk_0),
                  .i_rdqs_clk_180        (i_rdqs_clk_180),
                  .i_sdr_clk             (i_rx_sdr_clk),
                  .i_phy_clk             (i_phy_clk),
                  .i_rgb_mode            (i_rgb_mode),
                  .i_fgb_mode            (i_fgb_mode),
                  .ana_vref              (ana_vref),
                  .i_sa_cmn_en           (i_sa_cmn_en),
                  .i_sa_cfg              (i_sa_cfg),
                  .i_sa_cmn_cfg          (i_sa_cmn_cfg),
                  .i_sa_dly_cfg          (i_sa_dly_cfg),
                  .o_core_ig             (o_core_ig[i]),
                  .o_core_ig_b           (o_core_ig_b[i]),
                  .i_pad_cfg             (i_pad_rx_cfg[i*RX0WIDTH+:RX0WIDTH]),
                  .i_pad_cmn_cfg         (i_pad_rx_cmn_cfg),
                  .i_pad_cmn_ie          (i_pad_cmn_ie),
                  .i_pad_cmn_re          (i_pad_cmn_re),
                  .pad_t                 (pad_eg_t[i]),
                  .pad_c                 (pad_eg_c[i]),
                  .o_sa                  (o_sa[i*4+:4]),
                  .o_empty_n             (o_rxfifo_empty_n[i]),
                  .i_read                (i_rxfifo_read),
                  .i_clr                 (i_rxfifo_clr),
                  .i_read_mask           (i_rxfifo_read_mask),
                  .o_sdr                 (o_sdr[i*NUM_RPH+:NUM_RPH]),
                  .o_sdr_vld             (sdr_vld[i])
               );
            end
         end else begin : NO_RX_SLICE
            ddr_wcm_tielo u_tielo_0 (.o_z(o_core_ig[i]));
            ddr_wcm_tielo u_tielo_1 (.o_z(o_core_ig_b[i]));
            ddr_wcm_tielo u_tielo_2 [3:0] (.o_z(o_sa[i*4+:4]));
            ddr_wcm_tielo u_tielo_3 [NUM_RPH-1:0] (.o_z(o_sdr[i*NUM_RPH+:NUM_RPH]));
            ddr_wcm_tielo u_tielo_4 (.o_z(sdr_vld[i]));
            ddr_wcm_tielo u_tielo_5 (.o_z(o_rxfifo_empty_n));
         end
      end
   endgenerate

   ddr_wcm_buf u_buf_0 (.i_a(sdr_vld), .o_z(o_sdr_vld));

endmodule
