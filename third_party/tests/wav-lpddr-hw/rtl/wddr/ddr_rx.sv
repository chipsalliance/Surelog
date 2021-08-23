
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

import ddr_global_pkg::*;

module ddr_rx #(
   parameter             DQS_TYPE   =  0,               // DQS TYPE is set to remove all RX digital
   parameter             WIDTH      =  1,               // Parallel bus width
   parameter             A0WIDTH    =  20,              // Sense amp configuration width
   parameter             A1WIDTH    =  4,               // Sense amp configuration width
   parameter             A2WIDTH    =  32,              // Sense amp configuration width
   parameter             NUM_RDPH   =  8,               // Read datapath data phases (includes R/F)
   parameter             NUM_RPH    =  8,               // Read fifo data phases (includes R/F)
   parameter             RDWIDTH    = NUM_RDPH * WIDTH, // Read data width
   parameter             RWIDTH     = NUM_RPH  * WIDTH, // Read data width
   parameter             RX0WIDTH   =  8,               // Rx Single-Ended IO configuration width
   parameter             RX1WIDTH   =  8,               // Rx Single-Ended IO configuration width
   parameter [WIDTH-1:0] PAD_MASK   =  '0,              // Pad instance mask
   parameter [WIDTH-1:0] SLICE_MASK =  '0,              // Slice instance mask
   parameter [WIDTH-1:0] SE_PAD     =  '0,              // 1: Single-Ended Pad, 0: Differential Pad
   parameter             PS_DLY     =  10,              // Programmable delay in picoseconds
   parameter             FIFO_DEPTH =  8,               // FIFO depth
   parameter             FREN_WIDTH =  1*2+1,           // RX FIFO Read enable width
   parameter [0:0]       SLICE_FIFO =  1'b1             // Enable FIFO
) (
   input  logic                       i_rst,
   input  logic                       i_csp_div_rst_n,
   input  logic                       i_rdqs_clk_0,
   input  logic                       i_rdqs_clk_180,
   input  logic                       i_sdr_clk,
   input  logic                       i_phy_clk,

   input  logic [DEC_DGBWIDTH-1:0]    i_rgb_mode,
   input  fgb_t                       i_fgb_mode,

   input  logic                       ana_vref,
   input  logic                       i_sa_cmn_en,
   input  logic [A0WIDTH*WIDTH-1:0]   i_sa_cfg,
   input  logic [A1WIDTH-1:0]         i_sa_cmn_cfg,
   input  logic [A2WIDTH*WIDTH-1:0]   i_sa_dly_cfg,

   output logic [4*WIDTH-1:0]         o_sa,
   output logic [RWIDTH-1:0]          o_sdr,
   output logic                       o_sdr_vld,
   output logic                       o_empty_n,
   input  logic [FREN_WIDTH-1:0]      i_read,
   input  logic                       i_clr,
   input  logic                       i_read_mask,

   input  logic [RX0WIDTH*WIDTH-1:0]  i_pad_cfg,
   input  logic [RX1WIDTH-1:0]        i_pad_cmn_cfg,
   input  logic                       i_pad_cmn_ie,
   input  logic                       i_pad_cmn_re,
   output logic [WIDTH-1:0]           o_core_ig,
   output logic [WIDTH-1:0]           o_core_ig_b,
   input  wire  [WIDTH-1:0]           pad_t,
   input  wire  [WIDTH-1:0]           pad_c
);

   logic [WIDTH-1:0] xdr_0, xdr_180;

   logic                       rdqs_clk_0  ;
   logic                       rdqs_clk_180;

   logic                       pad_cmn_ie;
   logic                       pad_cmn_re;

  ddr_wcm_bufx8 u_rdqs_clk_0_buf   (.i_a(i_rdqs_clk_0),   .o_z(rdqs_clk_0));
  ddr_wcm_bufx8 u_rdqs_clk_180_buf (.i_a(i_rdqs_clk_180), .o_z(rdqs_clk_180));

  ddr_wcm_bufx8 u_pad_cmn_ie       (.i_a(i_pad_cmn_ie), .o_z(pad_cmn_ie));
  ddr_wcm_bufx8 u_pad_cmn_re       (.i_a(i_pad_cmn_re), .o_z(pad_cmn_re));

   ddr_rx_ana #(
      .WIDTH            (WIDTH),
      .A0WIDTH          (A0WIDTH),
      .A1WIDTH          (A1WIDTH),
      .A2WIDTH          (A2WIDTH),
      .RX0WIDTH         (RX0WIDTH),
      .RX1WIDTH         (RX1WIDTH),
      .PAD_MASK         (PAD_MASK),
      .SE_PAD           (SE_PAD)
   ) u_rx_ana (
`ifdef DDR_ECO_CM_RX_CLK
      .i_rdqs_clk_0     (i_rdqs_clk_0),
      .i_rdqs_clk_180   (i_rdqs_clk_180),
`else
      .i_rdqs_clk_0     (rdqs_clk_0),
      .i_rdqs_clk_180   (rdqs_clk_180),
`endif

      .ana_vref         (ana_vref),
      .i_sa_cmn_en      (i_sa_cmn_en),
      .i_sa_cfg         (i_sa_cfg),
      .i_sa_cmn_cfg     (i_sa_cmn_cfg),
      .i_sa_dly_cfg     (i_sa_dly_cfg),

      .o_xdr_0          (xdr_0),
      .o_xdr_180        (xdr_180),
      .o_core_ig        (o_core_ig),
      .o_core_ig_b      (o_core_ig_b),

      .i_pad_cfg        (i_pad_cfg),
      .i_pad_cmn_cfg    (i_pad_cmn_cfg),
      .i_pad_cmn_ie     (pad_cmn_ie),
      .i_pad_cmn_re     (pad_cmn_re),

      .pad_t            (pad_t),
      .pad_c            (pad_c)
   );

   generate
   if(DQS_TYPE) begin: NO_RX_DIG
      ddr_wcm_tielo u_tielo_0 [4*WIDTH-1:0] (.o_z(o_sa));
      ddr_wcm_tielo u_tielo_1 [RWIDTH-1:0]  (.o_z(o_sdr));
      ddr_wcm_tielo u_tielo_2               (.o_z(o_sdr_vld));
      ddr_wcm_tielo u_tielo_3               (.o_z(o_empty_n));
   end
   else begin : RX_DIG
      ddr_rx_dig #(
         .WIDTH            (WIDTH),
         .NUM_RDPH         (NUM_RDPH),
         .NUM_RPH          (NUM_RPH),
         .SLICE_MASK       (SLICE_MASK),
         .FIFO_DEPTH       (FIFO_DEPTH),
         .FREN_WIDTH       (FREN_WIDTH),
         .SLICE_FIFO       (SLICE_FIFO)
      ) u_rx_dig (
         .i_rdqs_clk_0     (rdqs_clk_0),
         .i_rdqs_clk_180   (rdqs_clk_180),
         .i_sdr_clk        (i_sdr_clk),
         .i_phy_clk        (i_phy_clk),
         .i_rgb_mode       (i_rgb_mode),
         .i_fgb_mode       (i_fgb_mode),
         .i_rst            (i_rst),
         .i_csp_div_rst_n  (i_csp_div_rst_n),
         .i_xdr_0          (xdr_0),
         .i_xdr_180        (xdr_180),
         .o_sa             (o_sa),
         .o_empty_n        (o_empty_n),
         .i_read           (i_read),
         .i_clr            (i_clr),
         .i_read_mask      (i_read_mask),
         .o_sdr            (o_sdr),
         .o_sdr_vld        (o_sdr_vld)
      );
   end
   endgenerate

endmodule

module ddr_rx_ana #(
   parameter             WIDTH      =  1,               // Parallel bus width
   parameter             A0WIDTH    =  20,              // Sense amp configuration width
   parameter             A1WIDTH    =  4,               // Sense amp configuration width
   parameter             A2WIDTH    =  32,              // Sense amp configuration width
   parameter             RX0WIDTH   =  8,               // Rx Single-Ended IO configuration width
   parameter             RX1WIDTH   =  8,               // Rx Single-Ended IO configuration width
   parameter [WIDTH-1:0] PAD_MASK   =  '0,              // Pad instance mask
   parameter [WIDTH-1:0] SE_PAD     =  '0               // 1: Single-Ended Pad, 0: Differential Pad
) (
   input  logic                       i_rdqs_clk_0,
   input  logic                       i_rdqs_clk_180,

   input  logic                       ana_vref,
   input  logic                       i_sa_cmn_en,
   input  logic [A0WIDTH*WIDTH-1:0]   i_sa_cfg,
   input  logic [A1WIDTH-1:0]         i_sa_cmn_cfg,
   input  logic [A2WIDTH*WIDTH-1:0]   i_sa_dly_cfg,

   output logic [WIDTH-1:0]           o_xdr_0,
   output logic [WIDTH-1:0]           o_xdr_180,

   output logic [WIDTH-1:0]           o_core_ig,
   output logic [WIDTH-1:0]           o_core_ig_b,

   input  logic [RX0WIDTH*WIDTH-1:0]  i_pad_cfg,
   input  logic [RX1WIDTH-1:0]        i_pad_cmn_cfg,
   input  logic                       i_pad_cmn_ie,
   input  logic                       i_pad_cmn_re,

   input  wire  [WIDTH-1:0]           pad_t,
   input  wire  [WIDTH-1:0]           pad_c
);

   genvar i;
   generate
      for (i=0; i<WIDTH; i=i+1) begin: PSLICE
         if (!PAD_MASK[i]) begin : PAD
            // Primary RX pad
            if (SE_PAD[i]) begin: SE_PAD_I

               /* Commented code - input goes directly to Sense Amplifier, no
               // pad required.
               ddr_pad_rx_se #(
                  .P0WIDTH            (RX0WIDTH),
                  .P1WIDTH            (RX1WIDTH)
               ) u_pad (
                  .i_pad_ie           (i_pad_cmn_ie),
                  .i_pad_re           (i_pad_cmn_re),
                  .o_core_ig          (xdr[i]),
                  .i_pad_cfg          (i_pad_cfg[RX0WIDTH*i+:RX0WIDTH]),
                  .i_pad_cmn_cfg      (i_pad_cmn_cfg),
                  .pad                (pad_t[i])
               );
               */

               ddr_deserializer #(
                  .DWIDTH             (1),
                  .A0WIDTH            (A0WIDTH),
                  .A1WIDTH            (A1WIDTH),
                  .A2WIDTH            (A2WIDTH)
               ) u_deserializer (
                  .i_rdqs_clk_0       (i_rdqs_clk_0),
                  .i_rdqs_clk_180     (i_rdqs_clk_180),
                  .i_xdr              (pad_t[i]),
                  .ana_vref           (ana_vref),
                  .i_sa_en            (i_sa_cmn_en),
                  .i_sa_cfg           (i_sa_cfg[i*A0WIDTH+:A0WIDTH]),
                  .i_sa_cmn_cfg       (i_sa_cmn_cfg),
                  .i_sa_dly_cfg       (i_sa_dly_cfg[i*A2WIDTH+:A2WIDTH]),
                  .o_sdr_0            (o_xdr_0[i]),
                  .o_sdr_180          (o_xdr_180[i])
               );

               ddr_wcm_buf u_buf_2 (.i_a(o_xdr_0[i]),   .o_z(o_core_ig  ));
               ddr_wcm_buf u_buf_3 (.i_a(o_xdr_180[i]), .o_z(o_core_ig_b));
            end else begin : DIFF_PAD
            `ifdef DDR_PAD_RX_BEHAV
               ddr_pad_rx_diff #(
                  .P0WIDTH            (RX0WIDTH),
                  .P1WIDTH            (RX1WIDTH)
               ) u_pad (
                  .i_pad_ie           (i_pad_cmn_ie),
                  .i_pad_re           (i_pad_cmn_re),
                  .o_core_ig          (o_core_ig),
                  .o_core_ig_b        (o_core_ig_b),
                  .i_pad_cfg          (i_pad_cfg[RX0WIDTH*i+:RX0WIDTH]),
                  .i_pad_cmn_cfg      (i_pad_cmn_cfg),
                  .pad_t              (pad_t[i]),
                  .pad_c              (pad_c[i])
               );
            `else
               ddr_dqs_rcvr_no_esd_wrapper #(
                  .P0WIDTH            (RX0WIDTH),
                  .P1WIDTH            (RX1WIDTH)
               ) dqs_rcvr (
                  .i_ie               (i_pad_cmn_ie),
                  .i_re               (i_pad_cmn_re),
                  .o_dqs_t            (o_core_ig  ),
                  .o_dqs_c            (o_core_ig_b),
                  .i_rcvr_cfg         (i_pad_cfg[RX0WIDTH*i+:RX0WIDTH]),
                  .i_rcvr_cmn_cfg     (i_pad_cmn_cfg),
                  .pad_t              (pad_t[i]),
                  .pad_c              (pad_c[i])
               );
            `endif

               ddr_wcm_buf u_buf_0 (.i_a(o_core_ig),   .o_z(o_xdr_0[i]));
               ddr_wcm_buf u_buf_1 (.i_a(o_core_ig_b), .o_z(o_xdr_180[i]));


            end
         end else begin : NO_SLICE
            //assign o_xdr_0[i]   = pad_t[i];
            ddr_wcm_buf u_buf_0 (.i_a(pad_t[i]), .o_z(o_xdr_0[i]));
            //assign o_xdr_180[i] = pad_c[i];
            ddr_wcm_buf u_buf_1 (.i_a(pad_c[i]), .o_z(o_xdr_180[i]));
            //assign o_core_ig   = o_xdr_0;
            ddr_wcm_buf u_buf_2 (.i_a(pad_t[i]), .o_z(o_core_ig  ));
            //assign o_core_ig_b = o_xdr_180;
            ddr_wcm_buf u_buf_3 (.i_a(pad_c[i]), .o_z(o_core_ig_b));
         end
      end
   endgenerate

endmodule

module ddr_rx_dig #(
   parameter             WIDTH      =  1,               // Parallel bus width
   parameter             NUM_RDPH   =  8,               // Read datapath data phases (includes R/F)
   parameter             NUM_RPH    =  8,               // Read fifo data phases (includes R/F)
   parameter             RDWIDTH    = NUM_RDPH * WIDTH, // Read data width
   parameter             RWIDTH     = NUM_RPH  * WIDTH, // Read data width
   parameter [WIDTH-1:0] SLICE_MASK = '0,               // Slice instance mask
   parameter             FREN_WIDTH =  1*2+1,           // RX FIFO Read enable width
   parameter             FIFO_DEPTH =  8,               // FIFO depth
   parameter [0:0]       SLICE_FIFO =  1'b1             // Enable FIFO
) (

   input  logic                     i_sdr_clk,
   input  logic                     i_phy_clk,
   input  logic                     i_rdqs_clk_0,
   input  logic                     i_rdqs_clk_180,

   input  logic [DEC_DGBWIDTH-1:0]  i_rgb_mode,
   input  fgb_t                     i_fgb_mode,
   input  logic                     i_rst,
   input  logic                     i_csp_div_rst_n,

   input  logic [WIDTH-1:0]         i_xdr_0,
   input  logic [WIDTH-1:0]         i_xdr_180,

   output logic [4*WIDTH-1:0]       o_sa,
   output logic [RWIDTH-1:0]        o_sdr,
   input  logic [FREN_WIDTH-1:0]    i_read,
   input  logic                     i_clr,
   input  logic                     i_read_mask,
   output logic                     o_empty_n,
   output logic                     o_sdr_vld
);

   logic [WIDTH-1:0] sdr_vld;
   logic [WIDTH-1:0] empty_n;

   genvar i;
   generate
      for (i=0; i<WIDTH; i=i+1) begin: DSLICE
         if (!SLICE_MASK[i]) begin : SLICE
            ddr_rx_sdr #(
               .DWIDTH           (1),
               .NUM_RDPH         (NUM_RDPH),
               .NUM_RPH          (NUM_RPH),
               .FIFO_DEPTH       (FIFO_DEPTH),
               .FREN_WIDTH       (FREN_WIDTH),
               .SLICE_FIFO       (SLICE_FIFO)
            ) u_rx_sdr (
               .i_rgb_mode       (i_rgb_mode),
               .i_fgb_mode       (i_fgb_mode),
               .i_rdqs_clk_0     (i_rdqs_clk_0),
               .i_rdqs_clk_180   (i_rdqs_clk_180),
               .i_sdr_clk        (i_sdr_clk),
               .i_phy_clk        (i_phy_clk),
               .i_csp_div_rst_n  (i_csp_div_rst_n),
               .i_rst            (i_rst),
               .i_xdr_0          (i_xdr_0[i]),
               .i_xdr_180        (i_xdr_180[i]),
               .o_sa             (o_sa[i*4+:4]),
               .o_sdr            (o_sdr[i*NUM_RPH+:NUM_RPH]),
               .o_sdr_vld        (sdr_vld[i]),
               .i_read           (i_read),
               .i_clr            (i_clr),
               .i_read_mask      (i_read_mask),
               .o_full           (/*OPEN*/),
               .o_empty_n        (empty_n[i])
            );
         end else begin
            assign o_sdr[i*NUM_RPH+:NUM_RPH] = '0;
            assign sdr_vld[i] = '0;
            assign empty_n[i] = '1;
         end
      end
   endgenerate

   //assign o_sdr_vld = |sdr_vld;
   // Simplify the aggregation and only look at one bit
   ddr_wcm_buf u_buf_0 (.i_a(sdr_vld[0]), .o_z(o_sdr_vld));

   //assign o_empty_n = &empty_n;
   // Simplify the aggregation and only look at one bit
   ddr_wcm_buf u_buf_1 (.i_a(empty_n[0]), .o_z(o_empty_n));

endmodule

module ddr_rx_sdr #(
   parameter       DWIDTH     = 1,                   // Data width slice
   parameter       NUM_RDPH   = 8,                   // Read datapath data phases (includes R/F)
   parameter       NUM_RPH    = 8,                   // Read fifo data phases (includes R/F)
   parameter       RDWIDTH    = NUM_RDPH * DWIDTH,   // Read datapath data width
   parameter       RWIDTH     = NUM_RPH  * DWIDTH,   // Read fifo data width
   parameter       FREN_WIDTH =  1*2+1,           // RX FIFO Read enable width
   parameter       FIFO_DEPTH = 8,                   // FIFO depth
   parameter [0:0] SLICE_FIFO = 1'b1                 // Enable FIFO
) (
   input  logic [DEC_DGBWIDTH-1:0]   i_rgb_mode,    // Phy read datapath gearbox mode
   input  fgb_t                      i_fgb_mode,    // Fifo gearbox mode
   input  logic                      i_rdqs_clk_0,
   input  logic                      i_rdqs_clk_180,
   input  logic                      i_sdr_clk,
   input  logic                      i_phy_clk,
   input  logic                      i_csp_div_rst_n,
   input  logic                      i_rst,
   input  logic [DWIDTH-1:0]         i_xdr_0,
   input  logic [DWIDTH-1:0]         i_xdr_180,
   output logic [RWIDTH-1:0]         o_sdr,
   output logic [4*DWIDTH-1:0]       o_sa,
   output logic                      o_sdr_vld,
   input  logic [FREN_WIDTH-1:0]     i_read,
   input  logic                      i_clr,
   input  logic                      i_read_mask,
   output logic                      o_full,
   output logic                      o_empty_n
);

   // ------------------------------------------------------------------------
   // SA Observability
   // ------------------------------------------------------------------------

   ddr_wcm_buf u_buf_0 [DWIDTH-1:0] (.i_a(i_xdr_0  ), .o_z(o_sa[0*DWIDTH+:DWIDTH]));
   ddr_wcm_buf u_buf_1 [DWIDTH-1:0] (.i_a(i_xdr_180), .o_z(o_sa[2*DWIDTH+:DWIDTH]));
   //assign o_sa[1*DWIDTH+:DWIDTH] = '0;
   ddr_wcm_buf u_buf_4 [DWIDTH-1:0] (.i_a('0       ), .o_z(o_sa[1*DWIDTH+:DWIDTH]));
   //assign o_sa[3*DWIDTH+:DWIDTH] = '0;
   ddr_wcm_buf u_buf_5 [DWIDTH-1:0] (.i_a('0       ), .o_z(o_sa[3*DWIDTH+:DWIDTH]));

   // ------------------------------------------------------------------------
   // Staging Flops
   // ------------------------------------------------------------------------

   // Phase 0
   logic [DWIDTH-1:0] sdr_0_q0;
   ddr_wcm_dff u_dff_sdr_0_q0   [DWIDTH-1:0] (.i_clk(i_rdqs_clk_180), .i_clk_b(i_rdqs_clk_0  ), .i_d(i_xdr_0    ), .o_q(sdr_0_q0  ));

   // Phase 180
   logic [DWIDTH-1:0] sdr_0_q1, sdr_180_q0;
   ddr_wcm_dff u_dff_sdr_0_q1   [DWIDTH-1:0] (.i_clk(i_rdqs_clk_180), .i_clk_b(i_rdqs_clk_0  ), .i_d(sdr_0_q0   ), .o_q(sdr_0_q1  ));
   ddr_wcm_dff u_dff_sdr_180_q0 [DWIDTH-1:0] (.i_clk(i_rdqs_clk_180), .i_clk_b(i_rdqs_clk_0  ), .i_d(i_xdr_180  ), .o_q(sdr_180_q0));


   // ------------------------------------------------------------------------
   // Mode bit muxing
   // ------------------------------------------------------------------------

   logic sdr_0_sel;
   //assign sdr_0_sel = i_rgb_mode[`DGB_4TO1_HF_IDX];
   ddr_wcm_buf u_buf_6 (.i_a(i_rgb_mode[`DGB_4TO1_HF_IDX]), .o_z(sdr_0_sel));

   logic [DWIDTH-1:0] sdr_0;
   ddr_wcm_mux u_mux_sdr_0   [DWIDTH-1:0] (.i_sel(sdr_0_sel  ), .i_a(sdr_0_q0  ), .i_b(sdr_0_q1  ), .o_z(sdr_0  ));

   logic sdr_1_sel_0;
   //assign sdr_1_sel_0 = i_rgb_mode[`DGB_4TO1_HF_IDX];
   ddr_wcm_buf u_buf_8 (.i_a(i_rgb_mode[`DGB_4TO1_HF_IDX]), .o_z(sdr_1_sel_0));
   logic [DWIDTH-1:0] sdr_1_0;
   ddr_wcm_mux u_mux_sdr_1_0 [DWIDTH-1:0] (.i_sel(sdr_1_sel_0), .i_a(i_xdr_180 ), .i_b(sdr_180_q0), .o_z(sdr_1_0));

   logic [DWIDTH-1:0] sdr_1;
   //assign sdr_1 = sdr_1_0;
   ddr_wcm_buf u_buf_10 [DWIDTH-1:0] (.i_a(sdr_1_0), .o_z(sdr_1));

   logic [DWIDTH-1:0] sdr_2, sdr_3;
   //assign sdr_2 = sdr_0_q0;
   ddr_wcm_buf u_buf_14 [DWIDTH-1:0] (.i_a(sdr_0_q0), .o_z(sdr_2));
   //assign sdr_3 = i_xdr_180;
   ddr_wcm_buf u_buf_15 [DWIDTH-1:0] (.i_a(i_xdr_180), .o_z(sdr_3));


   // ------------------------------------------------------------------------
   // FIFO
   // ------------------------------------------------------------------------
   generate
      if (SLICE_FIFO) begin : FIFO

         ddr_rx_fifo #(
            .WWIDTH           (RDWIDTH),
            .RWIDTH           (RWIDTH),
            .BWIDTH           (1),
            .DEPTH            (FIFO_DEPTH),
            .FREN_WIDTH       (FREN_WIDTH),
            .SYNC             (1'b0),
            .RAM_MODEL        (1'b0)
         ) u_rx_fifo (
            .i_scan_clk       (1'b0),        // Assumes no scan in custom macro
            .i_scan_en        (1'b0),        // Assumes no scan in custom macro
            .i_scan_mode      (1'b0),        // Assumes no scan in custom macro
            .i_scan           (2'b0),        // Assumes no scan in custom macro
            .o_scan           (/*OPEN*/),    // Assumes no scan in custom macro
            .i_scan_rst_ctrl  (1'b0),        // Assumes no scan in custom macro
            .i_scan_cgc_ctrl  (1'b0),        // Assumes no scan in custom macro
            .i_fgb_mode       (i_fgb_mode),
            .i_wclk           (i_sdr_clk),
            .i_wrst           (i_rst),
            .i_write          (1'b1),
            .i_wdata          ({
                                sdr_3,
                                sdr_2,
                                sdr_1,
                                sdr_0
                               }),
            .o_full           (o_full),
            .i_rclk           (i_phy_clk),
            .i_csp_div_rst_n  (i_csp_div_rst_n),
            .i_rrst           (i_rst),
            .i_read           (i_read),
            .i_clr            (i_clr),
            .i_read_mask      (i_read_mask),
            .i_rclk_en_ovr_sel(/*OPEN*/) ,
            .i_rclk_en_ovr    (/*OPEN*/) ,
            .o_rdata          (o_sdr),
            .o_rvld           (o_sdr_vld),
            .o_rclk_en        (/*OPEN*/),
            .o_empty_n        (o_empty_n)
         );
      end else begin : NO_FIFO
         assign o_sdr     = {
                              sdr_3,
                              sdr_2,
                              sdr_1,
                              sdr_0
                            };

         //assign o_full    = 'b0;
         ddr_wcm_tielo u_tielo_0 (.o_z(o_full));
         //assign o_empty_n = 'b1;
         ddr_wcm_tiehi u_tiehi_0 (.o_z(o_empty_n));
         //assign o_sdr_vld = 'b1;
         ddr_wcm_tiehi u_tiehi_1 (.o_z(o_sdr_vld));
      end
   endgenerate

endmodule

module ddr_deserializer #(
   parameter DWIDTH  = 1,
   parameter A0WIDTH = 20,
   parameter A1WIDTH = 4,
   parameter A2WIDTH = 32
) (
   input  logic                      i_rdqs_clk_0,
   input  logic                      i_rdqs_clk_180,
   input  logic [DWIDTH-1:0]         i_xdr,
   input  logic                      ana_vref,
   input  logic                      i_sa_en,
   input  logic [A0WIDTH*DWIDTH-1:0] i_sa_cfg,
   input  logic [A1WIDTH-1:0]        i_sa_cmn_cfg,
   input  logic [A2WIDTH*DWIDTH-1:0] i_sa_dly_cfg,
   output logic [DWIDTH-1:0]         o_sdr_0,
   output logic [DWIDTH-1:0]         o_sdr_180
);

`ifdef DDR_SA_BEHAV
   ddr_sense_amp #(.DWIDTH(DWIDTH)) u_sa_0   (.i_clk(i_rdqs_clk_0  ), .i_en({DWIDTH{i_sa_en}}), .i_d(i_xdr), .o_q(o_sdr_0  ));
   ddr_sense_amp #(.DWIDTH(DWIDTH)) u_sa_90  (.i_clk(i_rdqs_clk_90 ), .i_en({DWIDTH{i_sa_en}}), .i_d(i_xdr), .o_q(o_sdr_90 ));
`else
   genvar i;
   generate
      for (i=0; i<DWIDTH; i=i+1) begin: SA_SLICE
         ddr_sa_2ph_pdly_no_esd_wrapper #(
            .P0WIDTH       (A0WIDTH),
            .P1WIDTH       (A1WIDTH),
            .P2WIDTH       (A2WIDTH)
         ) u_sa_wrapper (
            .ana_vref      (ana_vref),
            .i_clk_0       (i_rdqs_clk_0),
            .i_clk_180     (i_rdqs_clk_180),
            .i_sa_en       (i_sa_en),
            .i_sa_cfg      (i_sa_cfg[i*A0WIDTH+:A0WIDTH]),
            .i_sa_cmn_cfg  (i_sa_cmn_cfg),
            .i_sa_dly_cfg  (i_sa_dly_cfg[i*A2WIDTH+:A2WIDTH]),
            .o_data_0      (o_sdr_0[i]),
            .o_data_0_b    (/*OPEN*/),
            .o_data_180    (o_sdr_180[i]),
            .o_data_180_b  (/*OPEN*/),
            .pad           (i_xdr[i])
         );
      end
   endgenerate
`endif
endmodule

module ddr_rx_fifo #(
   parameter       WWIDTH    = 32,
   parameter       RWIDTH    = 32,
   parameter       BWIDTH    = 8,
   parameter       FREN_WIDTH =  1*2+1,           // RX FIFO Read enable width
   parameter       DEPTH     = 8,
   parameter [0:0] SYNC      = 'b0,
   parameter [0:0] RAM_MODEL = 'b0,
   parameter       AWIDTH    = $clog2(DEPTH)
) (
   input  logic                 i_scan_clk,
   input  logic                 i_scan_en,
   input  logic                 i_scan_mode,
   input  logic                 i_scan_rst_ctrl,
   input  logic                 i_scan_cgc_ctrl,
   input  logic [1:0]           i_scan,
   output logic [1:0]           o_scan,

   input   logic                i_clr,
   input   fgb_t                i_fgb_mode,

   input   logic                i_wclk,
   input   logic                i_wrst,
   input   logic                i_write,
   input   logic [WWIDTH-1:0]   i_wdata,
   output  logic                o_full,

   input   logic                i_csp_div_rst_n,
   input   logic                i_rclk,
   input   logic                i_rrst,
   input   logic [FREN_WIDTH-1:0] i_read,
   input   logic                  i_read_mask,
   input   logic                i_rclk_en_ovr_sel,
   input   logic                i_rclk_en_ovr,

   output  logic [RWIDTH-1:0]   o_rdata,
   output  logic                o_rvld,
   output  logic                o_rclk_en,
   output  logic                o_empty_n
);

   logic [  AWIDTH:0] rbin_d , wbin_d;
   logic [  AWIDTH:0] rbin_q , wbin_q;
   logic [  AWIDTH:0] rgray_d, wgray_d;
   logic [  AWIDTH:0] rgray_q, wgray_q;
   logic [  AWIDTH:0] rgray_sync, wgray_sync;
   logic [AWIDTH-1:0] raddr, waddr;
   logic read;
   logic empty_n;

   assign o_scan    = 2'b0;

`ifdef DDR_ECO_RXFIFO_HOLD_FIX
   logic empty_dly;
   ddr_dly_buf u_dly_cell_holdfix (.i_a(empty_n), .o_z(empty_dly));
   assign read      = (&i_read | i_read_mask ) & empty_dly;
`else
   assign read      = (&i_read | i_read_mask ) & empty_n;
`endif
   assign o_rvld    = read;
   assign o_empty_n = empty_n | i_read_mask ;
   assign o_rclk_en = i_rclk_en_ovr_sel ? i_rclk_en_ovr : read ;
   // ------------------------------------------------------------------------
   // Clock Gate
   // ------------------------------------------------------------------------

   logic rclk_g, wclk;

   ddr_cgc_rl u_cgc_rl (.i_clk(i_rclk), .i_clk_en(empty_n),  .i_cgc_en(i_scan_cgc_ctrl), .o_clk(rclk_g));
   ddr_scan_clk_mux u_wclk_scan_mux (.i_scan_mode(i_scan_mode), .i_scan_clk(i_rclk),  .i_clk(i_wclk), .o_clk(wclk));

   // ------------------------------------------------------------------------
   // Reset
   // ------------------------------------------------------------------------

   logic rrst, rrst_scan;
   logic wrst, wrst_scan;

   assign rrst = i_rrst | ~i_csp_div_rst_n | i_clr;
   assign wrst = i_wrst | ~i_csp_div_rst_n | i_clr;

   ddr_scan_rst u_scan_rrst ( .i_scan_rst_ctrl(i_scan_rst_ctrl), .i_rst(rrst),   .o_rst(rrst_scan));
   ddr_scan_rst u_scan_wrst ( .i_scan_rst_ctrl(i_scan_rst_ctrl), .i_rst(wrst),   .o_rst(wrst_scan));

   // ------------------------------------------------------------------------
   // FIFO Memory
   // ------------------------------------------------------------------------

   logic        [1:0] wcnt_max;
   logic [RWIDTH-1:0] rdata_mask;

   always_comb
      case (i_fgb_mode)
         FGB_1TO1  : begin
                     wcnt_max   = 'd0;
                     rdata_mask = '0 | {(WWIDTH){1'b1}} ;
         end
         FGB_1TO2  : begin
                     wcnt_max   = 'd1;
                     rdata_mask = '0 | {(2*WWIDTH){1'b1}} ;
         end
         FGB_1TO4  : begin
                     wcnt_max   = 'd2;
                     rdata_mask = '0 | {(3*WWIDTH){1'b1}} ;
         end
         FGB_1TO8  : begin
                     wcnt_max   = 'd3;
                     rdata_mask = '0 | {(4*WWIDTH){1'b1}} ;
         end
         FGB_2TO2  : begin
                     wcnt_max   = 'd0;
                     rdata_mask = '0 | {(WWIDTH){1'b1}} ;
         end
         FGB_2TO4  : begin
                     wcnt_max   = 'd1;
                     rdata_mask = '0 | {(2*WWIDTH){1'b1}} ;
         end
         FGB_2TO8  : begin
                     wcnt_max   = 'd2;
                     rdata_mask = '0 | {(3*WWIDTH){1'b1}} ;
         end
         FGB_4TO4  : begin
                     wcnt_max   = 'd0;
                     rdata_mask = '0 | {(WWIDTH){1'b1}} ;
         end
         FGB_4TO8  : begin
                     wcnt_max   = 'd1;
                     rdata_mask = '0 | {(2*WWIDTH){1'b1}} ;
         end
         default   : begin
                     wcnt_max   = 'd0;
                     rdata_mask = '0 | {(WWIDTH){1'b1}} ;
         end
      endcase

   // Write WORD count
   logic [1:0] wcnt;
   always_ff @(posedge wclk, posedge wrst_scan)
      if (wrst_scan)
         wcnt <= 'd0;
      else
         if (i_write) begin
            if (wcnt == wcnt_max)
               wcnt <= 'd0;
            else
               wcnt <= wcnt + 'd1;
         end

   // FIFO regfile
   logic [RWIDTH-1:0] mem [DEPTH-1:0];
   always_ff @(posedge wclk, posedge wrst_scan)
      if (wrst_scan) begin
         // Reset address = 0 when the pointers are reset
         mem[0] <= '0;
      end else
         if (i_write) begin
            case (i_fgb_mode)
               FGB_1TO1  : mem[waddr][wcnt*(RWIDTH >> 0)+:(RWIDTH >> 0)] <= i_wdata;
               FGB_1TO2  : mem[waddr][wcnt*(RWIDTH >> 1)+:(RWIDTH >> 1)] <= i_wdata;
               FGB_1TO4  : mem[waddr][wcnt*(RWIDTH >> 2)+:(RWIDTH >> 2)] <= i_wdata;
               FGB_1TO8  : mem[waddr][wcnt*(RWIDTH >> 3)+:(RWIDTH >> 3)] <= i_wdata;
               FGB_2TO2  : mem[waddr][wcnt*(RWIDTH >> 0)+:(RWIDTH >> 0)] <= i_wdata;
               FGB_2TO4  : mem[waddr][wcnt*(RWIDTH >> 1)+:(RWIDTH >> 1)] <= i_wdata;
               FGB_2TO8  : mem[waddr][wcnt*(RWIDTH >> 2)+:(RWIDTH >> 2)] <= i_wdata;
               FGB_4TO4  : mem[waddr][wcnt*(RWIDTH >> 0)+:(RWIDTH >> 0)] <= i_wdata;
               FGB_4TO8  : mem[waddr][wcnt*(RWIDTH >> 1)+:(RWIDTH >> 1)] <= i_wdata;
               default   : mem[waddr][wcnt*(RWIDTH >> 0)+:(RWIDTH >> 0)] <= i_wdata;
            endcase
         end

   assign o_rdata = mem[raddr] & rdata_mask ;

   // ------------------------------------------------------------------------
   // Write Counter
   // ------------------------------------------------------------------------

   // In gearbox mode, only update once all write sub-cycle are complete
   assign wbin_d  = i_write & (wcnt == wcnt_max) ? wbin_q + 'b1 : wbin_q;
   assign wgray_d = (wbin_d >> 1) ^ wbin_d;

   always_ff @(posedge wclk, posedge wrst_scan) begin
      if (wrst_scan) begin
         wbin_q  <= '0;
         wgray_q <= '0;
      end else begin
         if (i_write) begin
            wbin_q  <= wbin_d;
            wgray_q <= wgray_d;
         end
      end
   end

   assign o_full = wgray_q == {~rgray_sync[AWIDTH:AWIDTH-1],rgray_sync[AWIDTH-2:0]};
   assign waddr = wbin_q[AWIDTH-1:0];

   // ------------------------------------------------------------------------
   // Read Counter
   // ------------------------------------------------------------------------

`ifdef DDR_ECO_RXFIFO_RD_FIX
   assign rbin_d  = read ? rbin_q + 'b1 : rbin_q;
`else
   assign rbin_d  = i_read ? rbin_q + 'b1 : rbin_q;
`endif
   assign rgray_d = (rbin_d >> 1) ^ rbin_d;

   always_ff @(posedge rclk_g, posedge rrst_scan) begin
      if (rrst_scan) begin
         rbin_q  <= '0;
         rgray_q <= '0;
      end else begin
`ifdef DDR_ECO_RXFIFO_RD_FIX
         if (read) begin
`else
         if (i_read) begin
`endif
            rbin_q  <= rbin_d;
            rgray_q <= rgray_d;
         end
      end
   end

   assign empty_n = rgray_q != wgray_sync;
   assign raddr = rbin_q[AWIDTH-1:0];

   // ------------------------------------------------------------------------
   // Synchronizers
   // ------------------------------------------------------------------------

   generate
     if (SYNC) begin : WR_SYNC
         assign wgray_sync = wgray_q;
     end else begin : WR_DEMET
         ddr_demet_r wsync [AWIDTH+1] (
            .i_clk   (i_rclk),
            .i_rst   (rrst_scan),
            .i_d     (wgray_q),
            .o_q     (wgray_sync)
         );
     end
   endgenerate

   generate
     if (SYNC) begin : RD_SYNC
         assign rgray_sync = rgray_q;
     end else begin : RD_DEMET
         ddr_demet_r rsync [AWIDTH+1] (
            .i_clk   (wclk),
            .i_rst   (wrst_scan),
            .i_d     (rgray_q),
            .o_q     (rgray_sync)
         );
     end
   endgenerate

endmodule

module ddr_rx_cc #(
   parameter CA_TYPE  = 1'b0,
   parameter LWIDTH   = 4,
   parameter PWIDTH   = 15,
   parameter PDAWIDTH = 25,
`ifdef DDR_DQS_VREF
   parameter VWIDTH   = 11,
`endif
   parameter PS_DLY   = 10
) (

   input  logic                    i_csp_div_rst_n,
   input  logic                    i_rst,
   input  logic [DEC_DGBWIDTH-1:0] i_tgb_mode,
   input  logic [DEC_DGBWIDTH-1:0] i_rgb_mode,
`ifdef DDR_DQS_VREF
   input  logic [VWIDTH-1:0]       i_refgen_cfg,
   output logic                    ana_vref,
`endif
   input  logic                    i_rdqs,
   input  logic                    i_rdqs_b,
   input  logic                    i_wck,
   input  logic                    i_wck_b,
   input  logic                    i_pll_clk_0,
   input  logic                    i_pll_clk_90,
   input  logic                    i_pll_clk_180,
   input  logic                    i_pll_clk_270,
   input  logic                    i_wck_mode,
   input  logic                    i_ren,
   input  logic [1:0]              i_pre_filter_sel,
   input  logic [PWIDTH-1:0]       i_ren_pi_cfg,
   output logic                    o_rcs,
   input  logic                    i_rcs,
   input  logic [PWIDTH-1:0]       i_rcs_pi_cfg,
   input  logic [PWIDTH-1:0]       i_rdqs_pi_0_cfg,
   input  logic [PWIDTH-1:0]       i_rdqs_pi_1_cfg,
   output logic                    o_rdqs_clk_0,
   output logic                    o_rdqs_clk_180,
   input  logic [LWIDTH-1:0]       i_sdr_lpde_cfg,
   output logic                    o_rcs_pi_phase_sta,
   output logic                    o_ren_pi_phase_sta,
   output logic                    o_sdr_clk
);

   logic rst_n;
   ddr_wcm_inv u_inv_rst (.i_a(i_rst), .o_z(rst_n));

   // ------------------------------------------------------------------------
   // VREF Logic
   // ------------------------------------------------------------------------

`ifdef DDR_DQS_VREF
   ddr_refgen_wrapper #(
      .PWIDTH           (VWIDTH)
   ) u_regen_wrapper (
      .i_refgen_cfg     (i_refgen_cfg),
      .i_ivqr50u_n      ('0),             // IFR - Connect to current source [HBM]
      .o_vref           (ana_vref)
   );
`endif

   // ------------------------------------------------------------------------
   // 4-Phase clock divider
   // ------------------------------------------------------------------------

   logic rdqs_div_en, rdqs_div_byp ;
   logic gb_4to1;
   logic gb_8to1;
   logic gb_mode;

   // If the Tx is using a high speed clock, then divide the Rx clock for 4-phase iRDQS
   ddr_wcm_and u_and0         (.o_z(gb_4to1), .i_a(i_tgb_mode[`DGB_4TO1_HF_IDX]), .i_b(i_rgb_mode[`DGB_4TO1_LF_IDX]));
   ddr_wcm_and u_and1         (.o_z(gb_8to1), .i_a(i_tgb_mode[`DGB_8TO1_HF_IDX]), .i_b(i_rgb_mode[`DGB_8TO1_LF_IDX]));
   ddr_wcm_or  u_or           (.o_z(gb_mode), .i_a(gb_4to1), .i_b(gb_8to1));
   ddr_wcm_and u_rdqs_div_en  (.o_z(rdqs_div_en), .i_a(gb_mode), .i_b(i_csp_div_rst_n));

   // Bypass the clock divider if no division is required
   ddr_wcm_inv u_inv_div_byp  (.i_a(gb_mode), .o_z(rdqs_div_byp));

   logic rdqs_clk_0, rdqs_clk_90, rdqs_clk_180, rdqs_clk_270;
   logic rdqs_clk_0_, rdqs_clk_90_, rdqs_clk_180_, rdqs_clk_270_;

   // 4-phase clock divider
   ddr_wcm_div2_4ph u_div2_4ph (
      .i_clk_0    (i_pll_clk_0),
      .i_clk_90   (i_pll_clk_90),
      .i_clk_180  (i_pll_clk_180),
      .i_clk_270  (i_pll_clk_270),
      .i_div_en   (rdqs_div_en),
      .i_div_byp  (rdqs_div_byp),
      .o_clk_0    (rdqs_clk_0_),
      .o_clk_90   (rdqs_clk_90_),
      .o_clk_180  (rdqs_clk_180_),
      .o_clk_270  (rdqs_clk_270_)
   );

   // ------------------------------------------------------------------------
   // Phase Detection and Alignment (PDA) Logic
   // ------------------------------------------------------------------------

`ifdef DDR_DQS_PDA
   ddr_pda_wrapper #(
      .PWIDTH        (PDAWIDTH)
   ) u_pda_wrapper (
      .i_reset       (i_rst),
      .i_data        (/*EDC*/),              // IFR - Need to connect to a ddr_deserializer for GDDR6
      .i_clk0        (rdqs_clk_0_),
      .i_clk90       (rdqs_clk_90_),
      .i_clk180      (rdqs_clk_180_),
      .i_clk270      (rdqs_clk_270_),
      .i_clk0_div2   (rdqs_clk_0_),
      .i_pda_cfg     (/*CFG*/),              // IFR - Add config the CSRs
      .o_clk_0       (rdqs_clk_0),
      .o_clk_90      (rdqs_clk_90),
      .o_clk_180     (rdqs_clk_180),
      .o_clk_270     (rdqs_clk_270)
   );
`else
   assign rdqs_clk_0   = rdqs_clk_0_;
   assign rdqs_clk_90  = rdqs_clk_90_;
   assign rdqs_clk_180 = rdqs_clk_180_;
   assign rdqs_clk_270 = rdqs_clk_270_;
`endif

   // ------------------------------------------------------------------------
   // REN and RCS (Read Chip Select - Rank) Logic
   // ------------------------------------------------------------------------

   logic ren;
   logic ren_pi, ren_pi_b;
   logic rcs_pi, rcs_pi_b;

   // REN PI
   generate
     if (CA_TYPE) begin : NO_REN_PI
         assign ren_pi    = rdqs_clk_0 ;
         assign ren_pi_b  = rdqs_clk_180 ;
     end else begin : REN_PI
      `ifdef DDR_REN_PI_SMALL
         ddr_pi_small_wrapper #(
      `else
         ddr_pi_wrapper #(
      `endif
            .PWIDTH     (PWIDTH)
         ) u_ren_pi (
            .i_clk0        (rdqs_clk_0),
            .i_clk90       (rdqs_clk_90),
            .i_clk180      (rdqs_clk_180),
            .i_clk270      (rdqs_clk_270),
            .i_pi_cfg      (i_ren_pi_cfg),
            .o_clk         (ren_pi),
            .o_clk_b       (ren_pi_b)
         );
        end
      endgenerate

   // REN PI Capture flop
   ddr_wcm_dff u_dff_ren (.i_clk(ren_pi), .i_clk_b(ren_pi_b), .i_d(i_ren),  .o_q(ren));
   logic ren_n;
   ddr_wcm_inv u_ren_n         (.i_a(i_ren), .o_z(ren_n));
   ddr_wcm_dff u_dff_ren_pi_pd (.i_clk(i_ren),  .i_clk_b(ren_n),    .i_d(ren_pi), .o_q(o_ren_pi_phase_sta));

   generate
     if (CA_TYPE) begin : NO_RCS_PI
         assign rcs_pi    = rdqs_clk_0 ;
         assign rcs_pi_b  = rdqs_clk_180 ;
     end else begin : RCS_PI
         // RCS PI
      `ifdef DDR_RCS_PI_SMALL
         ddr_pi_small_wrapper #(
      `else
         ddr_pi_wrapper #(
      `endif
            .PWIDTH     (PWIDTH)
         ) u_rcs_pi (
            .i_clk0        (rdqs_clk_0),
            .i_clk90       (rdqs_clk_90),
            .i_clk180      (rdqs_clk_180),
            .i_clk270      (rdqs_clk_270),
            .i_pi_cfg      (i_rcs_pi_cfg),
            .o_clk         (rcs_pi),
            .o_clk_b       (rcs_pi_b)
         );
        end
      endgenerate

   // RCS PI Capture flop
   ddr_wcm_dff_r u_dff_rcs (.i_clk(rcs_pi), .i_clk_b(rcs_pi_b), .i_rst(i_rst), .i_d(i_rcs), .o_q(o_rcs));
   logic rcs_n;
   ddr_wcm_inv u_rcs_inv    (.i_a(i_rcs), .o_z(rcs_n));
   ddr_wcm_dff u_dff_rcs_pd (.i_clk(i_rcs),  .i_clk_b(rcs_n),    .i_d(rcs_pi), .o_q(o_rcs_pi_phase_sta));

   // ------------------------------------------------------------------------
   // RDQS Logic
   // ------------------------------------------------------------------------

   logic dqs_mode, dqs_mode_n, rdqs_mode_n, wck_mode_n, lf_mode, ir_mode;

   // In LF mode the clock is generated internally and not from the external RDQS
   ddr_wcm_or or2 (.o_z(lf_mode), .i_a(i_rgb_mode[`DGB_4TO1_LF_IDX]), .i_b(i_rgb_mode[`DGB_8TO1_LF_IDX]));
   // In IR mode the clock is generated internally and not from the external RDQS
   ddr_wcm_or or3 (.o_z(ir_mode), .i_a(i_rgb_mode[`DGB_2TO1_IR_IDX]), .i_b(i_rgb_mode[`DGB_4TO1_IR_IDX]));
   // Bypass external DQS in LF or IR modes
   ddr_wcm_or or4 (.o_z(dqs_mode_n), .i_a(lf_mode), .i_b(ir_mode));

   // Build clock mux control vector
   ddr_wcm_inv  u_inv_dqs_mode_n (.i_a(dqs_mode_n), .o_z(dqs_mode ));
   ddr_wcm_inv  u_inv_wck_mode    (.i_a(i_wck_mode ), .o_z(wck_mode_n));
   ddr_wcm_nand u_nand_rdqs_mode  (.i_a(dqs_mode), .i_b(wck_mode_n), .o_z(rdqs_mode_n));

   logic pi_rdqs_clk_0, pi_rdqs_clk_180;
   logic mux_rdqs_clk_0, mux_rdqs_clk_180;

   generate
     if (CA_TYPE) begin : NO_RDQS_PI
         assign pi_rdqs_clk_0    = rdqs_clk_0 ;
         assign pi_rdqs_clk_180  = rdqs_clk_180 ;
     end else begin : RDQS_PI_0
         // RDQS PI
         ddr_pi_wrapper #(
            .PWIDTH     (PWIDTH)
         ) u_rdqs_pi_0 (
            .i_clk0        (rdqs_clk_0),
            .i_clk90       (rdqs_clk_90),
            .i_clk180      (rdqs_clk_180),
            .i_clk270      (rdqs_clk_270),
            .i_pi_cfg      (i_rdqs_pi_0_cfg),
            .o_clk         (pi_rdqs_clk_0),
            .o_clk_b       (pi_rdqs_clk_180)
         );
       end
     endgenerate


   generate
   if (CA_TYPE) begin : CA_MUX  // High speed clock mux
   ddr_clkmux_3to1_diff_wrapper
     u_clkmux_diff_wrapper (
      .o_c           (mux_rdqs_clk_180),
      .o_t           (mux_rdqs_clk_0),
      .i_01_c        (i_rdqs_b),
      .i_01_t        (i_rdqs),
      .i_10_c        (i_wck_b),
      .i_10_t        (i_wck),
      .i_11_c        (pi_rdqs_clk_180),
      .i_11_t        (pi_rdqs_clk_0),
      .i_sel         ({rdqs_mode_n, wck_mode_n})
   );
   ddr_wcm_bufx8 u_rdqs_clk_0_buf   (.i_a(mux_rdqs_clk_0),   .o_z(o_rdqs_clk_0));
   ddr_wcm_bufx8 u_rdqs_clk_180_buf (.i_a(mux_rdqs_clk_180), .o_z(o_rdqs_clk_180));
   end else begin : DQ_MUX
`ifdef DDR_ECO_CM_RX_CLK
   ddr_clkmux_3to1_diff_wrapper # (
     .SLVT_TYPE (1)
   )  u_clkmux_diff_wrapper (
      .o_c           (o_rdqs_clk_180),
      .o_t           (o_rdqs_clk_0),
`else
   ddr_clkmux_3to1_diff_wrapper
      u_clkmux_diff_wrapper (
      .o_c           (mux_rdqs_clk_180),
      .o_t           (mux_rdqs_clk_0),
`endif
      .i_01_c        (i_rdqs_b),
      .i_01_t        (i_rdqs),
      .i_10_c        (i_wck_b),
      .i_10_t        (i_wck),
      .i_11_c        (pi_rdqs_clk_180),
      .i_11_t        (pi_rdqs_clk_0),
      .i_sel         ({rdqs_mode_n, wck_mode_n})
   );
`ifndef DDR_ECO_CM_RX_CLK
   ddr_wcm_bufx8 u_rdqs_clk_0_buf   (.i_a(mux_rdqs_clk_0),   .o_z(o_rdqs_clk_0));
   ddr_wcm_bufx8 u_rdqs_clk_180_buf (.i_a(mux_rdqs_clk_180), .o_z(o_rdqs_clk_180));
`endif
   end
   endgenerate

   // Preamble filter
   logic ren_inv;
   ddr_wcm_inv u_ren_inv (.i_a(ren), .o_z(ren_inv));

   logic filter_q0, filter_q1;
   generate
   if (CA_TYPE) begin : CA_FILTER
   ddr_wcm_dff_r u_filter_dff0 (.i_clk(mux_rdqs_clk_180), .i_clk_b(mux_rdqs_clk_0), .i_rst(ren_inv), .i_d(1'b1     ), .o_q(filter_q0));
   ddr_wcm_dff_r u_filter_dff1 (.i_clk(mux_rdqs_clk_180), .i_clk_b(mux_rdqs_clk_0), .i_rst(ren_inv), .i_d(filter_q0), .o_q(filter_q1));
   end else begin :  DQ_FILTER
`ifdef DDR_ECO_CM_RX_CLK
   ddr_wcm_dff_r u_filter_dff0 (.i_clk(o_rdqs_clk_180), .i_clk_b(o_rdqs_clk_0), .i_rst(ren_inv), .i_d(1'b1     ), .o_q(filter_q0));
   ddr_wcm_dff_r u_filter_dff1 (.i_clk(o_rdqs_clk_180), .i_clk_b(o_rdqs_clk_0), .i_rst(ren_inv), .i_d(filter_q0), .o_q(filter_q1));
`else
   ddr_wcm_dff_r u_filter_dff0 (.i_clk(mux_rdqs_clk_180), .i_clk_b(mux_rdqs_clk_0), .i_rst(ren_inv), .i_d(1'b1     ), .o_q(filter_q0));
   ddr_wcm_dff_r u_filter_dff1 (.i_clk(mux_rdqs_clk_180), .i_clk_b(mux_rdqs_clk_0), .i_rst(ren_inv), .i_d(filter_q0), .o_q(filter_q1));
`endif
   end
   endgenerate

   logic filter_mux0, filter_mux1;
   ddr_wcm_mux u_filter_mux0 (.i_sel(i_pre_filter_sel[0]), .i_a(ren), .i_b(filter_q0), .o_z(filter_mux0));
   ddr_wcm_mux u_filter_mux1 (.i_sel(i_pre_filter_sel[1]), .i_a(filter_mux0), .i_b(filter_q1), .o_z(filter_mux1));

   logic rdqs_clk_180_filter, rdqs_clk_180_filter_b;
   generate
   if (CA_TYPE) begin : CA_FILTER_CGC
   ddr_wcm_cgc_rh_2ph u_cgc_rdqs_filter (
      .i_clk         (mux_rdqs_clk_180),
      .i_clk_b       (mux_rdqs_clk_0),
      .i_en          (filter_mux1),
      .o_clk         (rdqs_clk_180_filter),
      .o_clk_b       (rdqs_clk_180_filter_b)
   );
   end else begin :  DQ_FILTER_CGC
`ifdef DDR_ECO_CM_RX_CLK
   ddr_wcm_cgc_rh_2ph u_cgc_rdqs_filter (
      .i_clk         (o_rdqs_clk_180),
      .i_clk_b       (o_rdqs_clk_0),
      .i_en          (filter_mux1),
      .o_clk         (rdqs_clk_180_filter),
      .o_clk_b       (rdqs_clk_180_filter_b)
   );
`else
   ddr_wcm_cgc_rh_2ph u_cgc_rdqs_filter (
      .i_clk         (mux_rdqs_clk_180),
      .i_clk_b       (mux_rdqs_clk_0),
      .i_en          (filter_mux1),
      .o_clk         (rdqs_clk_180_filter),
      .o_clk_b       (rdqs_clk_180_filter_b)
   );
`endif
   end
   endgenerate

   // Various clocking options
   logic clk_inv_div_byp, clk_inv_div_byp_or, clk_inv_div_en_int, clk_inv_div_en;
   ddr_wcm_or or5   (.o_z(clk_inv_div_byp_or), .i_a(i_rgb_mode[`DGB_1TO1_HF_IDX]), .i_b(i_rgb_mode[`DGB_2TO1_HF_IDX]));
   ddr_wcm_or or6   (.o_z(clk_inv_div_byp), .i_a(clk_inv_div_byp_or), .i_b(i_rgb_mode[`DGB_2TO1_IR_IDX]));
   ddr_wcm_inv u_div_byp_inv (.i_a(clk_inv_div_byp), .o_z(clk_inv_div_en_int));
   ddr_wcm_and and4 (.o_z(clk_inv_div_en), .i_a(clk_inv_div_en_int), .i_b(i_csp_div_rst_n));

   logic clk_inv_div, clk_inv_div_b;
   ddr_wcm_div2_2ph  u_clk_inv_div (
      .i_clk_0    (rdqs_clk_180_filter),
      .i_clk_180  (rdqs_clk_180_filter_b),
      .i_div_en   (clk_inv_div_en),
      .i_div_byp  (clk_inv_div_byp),
      .o_clk_0    (clk_inv_div),
      .o_clk_180  (clk_inv_div_b)
   );

   logic clk_inv_div_d0, clk_inv_div_d0_inv;
`ifdef DDR_LPDE_BEHAV
   ddr_lpde #(.LWIDTH(LWIDTH), .PS_DLY(PS_DLY)) u_sdr_lpde (.i_d(clk_inv_div), .i_delay(i_sdr_lpde_cfg), .o_d(clk_inv_div_d0));
   ddr_wcm_inv  u_clk_inv_div_d0_inv (.i_a(clk_inv_div_d0), .o_z(clk_inv_div_d0_inv));
`else
`ifdef DDR_ENABLE_RX_SDRLPDE_SMALL
   ddr_prog_dly_se_small_wrapper #(
`else
   ddr_prog_dly_se_wrapper #(
`endif
      .PWIDTH     (LWIDTH)
   ) u_sdr_prog_dly (
      .o_clk_b    (clk_inv_div_d0_inv),
      .i_prog_dly_cfg(i_sdr_lpde_cfg),
      .i_clk      (clk_inv_div)
   );
   ddr_wcm_inv  u_clk_inv_div_d0_inv (.i_a(clk_inv_div_d0_inv), .o_z(clk_inv_div_d0));
`endif

   logic sdr_clk;

   // 3-input clock mux - to FIFO
   ddr_wcm_mux_3to1 u_sdr_clk_mux (
      .i_sel      ({i_rgb_mode[`DGB_8TO1_HF_IDX],clk_inv_div_byp}),
      .i_0        (clk_inv_div_d0_inv),
      .i_1        (clk_inv_div_d0),
      .i_2        (clk_inv_div),
      .o_z        (sdr_clk)
   );

   ddr_wcm_bufx8 u_sdr_clk_buf          (.i_a(sdr_clk),          .o_z(o_sdr_clk));

endmodule
