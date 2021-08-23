
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

module ddr_tx #(
   parameter             WIDTH      =  1,
   parameter             NUM_WDPH   =  8,                   // Write datapath data phases
   parameter             NUM_WPH    =  8,                   // Write gearbox data phases
   parameter             WWIDTH     = NUM_WPH * WIDTH,      // Write datapath width
   parameter [WIDTH-1:0] SLICE_MASK = '0,                   // Slice instance mask
   parameter [WIDTH-1:0] LPDE_MASK  = '0,                   // LPDE instance mask
   parameter [WIDTH-1:0] PAD_MASK   = '0,                   // PAD instance mask
   parameter [WIDTH-1:0] CKE_MASK   = '0,                   // CKE PAD instance mask
   parameter [WIDTH-1:0] WCK_MASK   = '0,                   // WCK PAD instance mask
   parameter [WIDTH-1:0] DQS_MASK   = '0,                   // DQS PAD instance mask
   parameter             E0WIDTH    =  6,                   // Egress buffer control width (ANA)
   parameter             E1WIDTH    =  7,                   // Egress buffer control width (DIG)
   parameter             FWIDTH     =  2,
   parameter             MXWIDTH    =  3,
   parameter             XWIDTH     =  $clog2(NUM_WDPH),
   parameter             OWIDTH     =  3,
   parameter             LWIDTH     =  4,
   parameter             TX0WIDTH   =  16,
   parameter             TX1WIDTH   =  5,
   parameter [WIDTH-1:0] SE_PAD     = '0,
   parameter             PS_DLY     = 10
) (

   input  logic [DEC_WGBWIDTH-1:0]     i_wgb_mode,
   input  logic [E0WIDTH*WIDTH-1:0]    i_egress_mode_ana,
   input  logic [E1WIDTH*WIDTH-1:0]    i_egress_mode_dig,

   input  logic [WIDTH-1:0]            i_qdr_clk_0,
   input  logic [WIDTH-1:0]            i_qdr_clk_180,
   input  logic [WIDTH-1:0]            i_ddr_clk_0,
   input  logic [WIDTH-1:0]            i_ddr_clk_180,
   input  logic [WIDTH-1:0]            i_sdr_clk,
   input  logic [WIDTH-1:0]            i_sdr_clk_b,
   input  logic [WIDTH-1:0]            i_sdr_div2_clk,
   input  logic [WIDTH-1:0]            i_sdr_div2_clk_b,
   input  logic [WIDTH-1:0]            i_sdr_rt_clk,
   input  logic [WIDTH-1:0]            i_sdr_rt_clk_b,

   input  logic [WIDTH-1:0]            i_sdr_rt_pipe_en,

   input  logic [FWIDTH*WIDTH-1:0]     i_sdr_0_fc_dly,
   input  logic [MXWIDTH*WIDTH-1:0]    i_sdr_0_x_sel,
   input  logic [WIDTH-1:0]            i_sdr_0_pipe_en,
   input  logic [FWIDTH*WIDTH-1:0]     i_sdr_1_fc_dly,
   input  logic [MXWIDTH*WIDTH-1:0]    i_sdr_1_x_sel,
   input  logic [WIDTH-1:0]            i_sdr_1_pipe_en,
   input  logic [FWIDTH*WIDTH-1:0]     i_sdr_2_fc_dly,
   input  logic [MXWIDTH*WIDTH-1:0]    i_sdr_2_x_sel,
   input  logic [WIDTH-1:0]            i_sdr_2_pipe_en,
   input  logic [FWIDTH*WIDTH-1:0]     i_sdr_3_fc_dly,
   input  logic [MXWIDTH*WIDTH-1:0]    i_sdr_3_x_sel,
   input  logic [WIDTH-1:0]            i_sdr_3_pipe_en,

   input  logic [(MXWIDTH-1)*WIDTH-1:0]i_ddr_0_x_sel,
   input  logic [WIDTH-1:0]            i_ddr_0_pipe_en,
   input  logic [(MXWIDTH-1)*WIDTH-1:0]i_ddr_1_x_sel,
   input  logic [WIDTH-1:0]            i_ddr_1_pipe_en,

   input  logic [LWIDTH*WIDTH-1:0]     i_xdr_lpde_cfg,

   input  logic [WWIDTH-1:0]           i_sdr,
   input  logic                        i_freeze_cmn_n,
   input  logic                        i_freeze_n_hv,
   input  logic                        i_hiz_cmn_n,
   input  logic [TX0WIDTH*WIDTH-1:0]   i_pad_cfg,
   input  logic [TX1WIDTH-1:0]         i_pad_cmn_cfg,
   input  logic                        i_pad_cmn_oe,
   input  logic                        i_pad_cmn_wck_oe,
   input  logic                        i_pad_cmn_ie,
   output logic [WIDTH-1:0]            o_core_eg,
   input  logic                        i_pad_bscan_cmn_n,
   input  logic                        i_pad_bscan_cmn_oe,
   input  logic                        i_pad_bscan_cmn_ie,
   input  logic [WIDTH-1:0]            i_pad_bscan_t,       // From BSCAN
   input  logic [WIDTH-1:0]            i_pad_bscan_c,       // From BSCAN
   output logic [WIDTH-1:0]            o_pad_lpbk_t,        // To CA clkmux and BSCAN
   output logic [WIDTH-1:0]            o_pad_lpbk_c,        // To CA clkmux and BSCAN
   output logic [WIDTH-1:0]            o_pad_eg_t,          // To DQS receiver
   output logic [WIDTH-1:0]            o_pad_eg_c,          // To DQS receiver
   inout  wire  [WIDTH-1:0]            pad_t,
   inout  wire  [WIDTH-1:0]            pad_c
);

   logic [WIDTH-1:0] xdr_0, xdr_1, xdr_2, xdr_3;

  // Clock Tree Buffering
   logic [WIDTH-1:0]            qdr_clk_0;
   logic [WIDTH-1:0]            qdr_clk_180;
   logic [WIDTH-1:0]            ddr_clk_0;
   logic [WIDTH-1:0]            ddr_clk_180;
   logic [WIDTH-1:0]            sdr_clk;
   logic [WIDTH-1:0]            sdr_clk_b;
   logic [WIDTH-1:0]            sdr_div2_clk;
   logic [WIDTH-1:0]            sdr_div2_clk_b;
   logic [WIDTH-1:0]            sdr_rt_clk;
   logic [WIDTH-1:0]            sdr_rt_clk_b;

   ddr_wcm_bufx8 u_qdr_clk_0      (.i_a(i_qdr_clk_0),   .o_z(qdr_clk_0 ));
   ddr_wcm_bufx8 u_qdr_clk_180    (.i_a(i_qdr_clk_180), .o_z(qdr_clk_180 ));
   ddr_wcm_bufx8 u_ddr_clk_0      (.i_a(i_ddr_clk_0),   .o_z(ddr_clk_0 ));
   ddr_wcm_bufx8 u_ddr_clk_180    (.i_a(i_ddr_clk_180),  .o_z(ddr_clk_180 ));
   ddr_wcm_bufx8 u_sdr_clk        (.i_a(i_sdr_clk       ),  .o_z(sdr_clk       ));
   ddr_wcm_bufx8 u_sdr_clk_b      (.i_a(i_sdr_clk_b     ),  .o_z(sdr_clk_b     ));
   ddr_wcm_bufx8 u_sdr_div2_clk   (.i_a(i_sdr_div2_clk  ),  .o_z(sdr_div2_clk  ));
   ddr_wcm_bufx8 u_sdr_div2_clk_b (.i_a(i_sdr_div2_clk_b),  .o_z(sdr_div2_clk_b));
   ddr_wcm_bufx8 u_sdr_rt_clk     (.i_a(i_sdr_rt_clk    ),  .o_z(sdr_rt_clk    ));
   ddr_wcm_bufx8 u_sdr_rt_clk_b   (.i_a(i_sdr_rt_clk_b  ),  .o_z(sdr_rt_clk_b  ));

   logic pad_cmn_oe    ;
   logic pad_cmn_wck_oe;
   logic pad_cmn_ie    ;

   ddr_wcm_bufx8 u_pad_cmn_oe     (.i_a(i_pad_cmn_oe    ),  .o_z(pad_cmn_oe    ));
   ddr_wcm_bufx8 u_pad_cmn_wck_oe (.i_a(i_pad_cmn_wck_oe),  .o_z(pad_cmn_wck_oe));
   ddr_wcm_bufx8 u_pad_cmn_ie     (.i_a(i_pad_cmn_ie    ),  .o_z(pad_cmn_ie    ));

   // Digital block
   ddr_tx_dig #(
      .WIDTH                      (WIDTH),
      .NUM_WDPH                   (NUM_WDPH),
      .NUM_WPH                    (NUM_WPH),
      .WWIDTH                     (WWIDTH),
      .E0WIDTH                    (E0WIDTH),
      .E1WIDTH                    (E1WIDTH),
      .FWIDTH                     (FWIDTH),
      .MXWIDTH                    (MXWIDTH),
      .XWIDTH                     (XWIDTH),
      .SLICE_MASK                 (SLICE_MASK)
   ) u_tx_dig (

      .i_wgb_mode                 (i_wgb_mode),
      .i_egress_mode_dig          (i_egress_mode_dig),
      .i_egress_mode_ana          (i_egress_mode_ana),
      .i_bscan                    (i_pad_bscan_t),

      .i_qdr_clk_0                (qdr_clk_0),
      .i_qdr_clk_180              (qdr_clk_180),
      .i_ddr_clk_0                (ddr_clk_0),
      .i_ddr_clk_180              (ddr_clk_180),
      .i_sdr_clk                  (sdr_clk),
      .i_sdr_clk_b                (sdr_clk_b),
      .i_sdr_div2_clk             (sdr_div2_clk),
      .i_sdr_div2_clk_b           (sdr_div2_clk_b),
      .i_sdr_rt_clk               (sdr_rt_clk),
      .i_sdr_rt_clk_b             (sdr_rt_clk_b),
      .i_sdr_rt_pipe_en           (i_sdr_rt_pipe_en),

      .i_sdr_0_fc_dly             (i_sdr_0_fc_dly),
      .i_sdr_0_x_sel              (i_sdr_0_x_sel),
      .i_sdr_0_pipe_en            (i_sdr_0_pipe_en),
      .i_sdr_1_fc_dly             (i_sdr_1_fc_dly),
      .i_sdr_1_x_sel              (i_sdr_1_x_sel),
      .i_sdr_1_pipe_en            (i_sdr_1_pipe_en),
      .i_sdr_2_fc_dly             (i_sdr_2_fc_dly),
      .i_sdr_2_x_sel              (i_sdr_2_x_sel),
      .i_sdr_2_pipe_en            (i_sdr_2_pipe_en),
      .i_sdr_3_fc_dly             (i_sdr_3_fc_dly),
      .i_sdr_3_x_sel              (i_sdr_3_x_sel),
      .i_sdr_3_pipe_en            (i_sdr_3_pipe_en),

      .i_ddr_0_x_sel              (i_ddr_0_x_sel),
      .i_ddr_0_pipe_en            (i_ddr_0_pipe_en),
      .i_ddr_1_x_sel              (i_ddr_1_x_sel),
      .i_ddr_1_pipe_en            (i_ddr_1_pipe_en),

      .i_sdr                      (i_sdr),
      .o_xdr_0                    (xdr_0),
      .o_xdr_1                    (xdr_1),
      .o_xdr_2                    (xdr_2),
      .o_xdr_3                    (xdr_3)
   );

   // Analog block
   ddr_tx_ana #(
      .WIDTH                      (WIDTH),
      .LPDE_MASK                  (LPDE_MASK),
      .PAD_MASK                   (PAD_MASK),
      .CKE_MASK                   (CKE_MASK),
      .WCK_MASK                   (WCK_MASK),
      .DQS_MASK                   (DQS_MASK),
      .SLICE_MASK                 (SLICE_MASK),
      .LWIDTH                     (LWIDTH),
      .EWIDTH                     (E0WIDTH),
      .TX0WIDTH                   (TX0WIDTH),
      .TX1WIDTH                   (TX1WIDTH),
      .SE_PAD                     (SE_PAD)
   ) u_tx_ana (

      .i_qdr_clk_0                (qdr_clk_0),
      .i_qdr_clk_180              (qdr_clk_180),
      .i_ddr_clk_0                (ddr_clk_0),
      .i_ddr_clk_180              (ddr_clk_180),

      .i_xdr_0                    (xdr_0),
      .i_xdr_1                    (xdr_1),
      .i_xdr_2                    (xdr_2),
      .i_xdr_3                    (xdr_3),

      .i_xdr_lpde_cfg             (i_xdr_lpde_cfg),
      .i_egress_mode              (i_egress_mode_ana),

      .i_freeze_cmn_n             (i_freeze_cmn_n),
      .i_freeze_n_hv              (i_freeze_n_hv),
      .i_hiz_cmn_n                (i_hiz_cmn_n),
      .i_pad_cfg                  (i_pad_cfg),
      .i_pad_cmn_cfg              (i_pad_cmn_cfg),
      .i_pad_cmn_oe               (pad_cmn_oe),
      .i_pad_cmn_wck_oe           (pad_cmn_wck_oe),
      .i_pad_cmn_ie               (pad_cmn_ie),
      .o_core_eg                  (o_core_eg),

      .i_pad_bscan_cmn_n          (i_pad_bscan_cmn_n),
      .i_pad_bscan_cmn_oe         (i_pad_bscan_cmn_oe),
      .i_pad_bscan_cmn_ie         (i_pad_bscan_cmn_ie),
      .i_pad_bscan_t              (i_pad_bscan_t),
      .i_pad_bscan_c              (i_pad_bscan_c),
      .o_pad_lpbk_t               (o_pad_lpbk_t),
      .o_pad_lpbk_c               (o_pad_lpbk_c),
      .o_pad_eg_t                 (o_pad_eg_t),
      .o_pad_eg_c                 (o_pad_eg_c),
      .pad_t                      (pad_t),
      .pad_c                      (pad_c)
   );

endmodule

module ddr_tx_ana #(
   parameter             WIDTH       =  1,
   parameter [WIDTH-1:0] LPDE_MASK   = '0,                   // LPDE instance mask
   parameter [WIDTH-1:0] PAD_MASK    = '0,                   // PAD instance mask
   parameter [WIDTH-1:0] CKE_MASK    = '0,                   // CKE PAD instance mask
   parameter [WIDTH-1:0] WCK_MASK    = '0,                   // WCK PAD instance mask
   parameter [WIDTH-1:0] DQS_MASK    = '0,                   // DQS PAD instance mask
   parameter [WIDTH-1:0] SLICE_MASK  = '0,                   // Slice PAD instance mask
   parameter             LWIDTH      =  4,
   parameter             EWIDTH      =  6,                   // Egress buffer control width
   parameter             TX0WIDTH    =  16,
   parameter             TX1WIDTH    =  5,
   parameter [WIDTH-1:0] SE_PAD      = '0
) (

   input  logic [WIDTH-1:0]            i_qdr_clk_0,
   input  logic [WIDTH-1:0]            i_qdr_clk_180,
   input  logic [WIDTH-1:0]            i_ddr_clk_0,
   input  logic [WIDTH-1:0]            i_ddr_clk_180,

   input  logic [WIDTH-1:0]            i_xdr_0,
   input  logic [WIDTH-1:0]            i_xdr_1,
   input  logic [WIDTH-1:0]            i_xdr_2,
   input  logic [WIDTH-1:0]            i_xdr_3,

   input  logic [EWIDTH*WIDTH-1:0]     i_egress_mode,
   input  logic [LWIDTH*WIDTH-1:0]     i_xdr_lpde_cfg,

   input  logic                        i_freeze_cmn_n,
   input  logic                        i_freeze_n_hv,
   input  logic                        i_hiz_cmn_n,
   input  logic [TX0WIDTH*WIDTH-1:0]   i_pad_cfg,
   input  logic [TX1WIDTH-1:0]         i_pad_cmn_cfg,
   input  logic                        i_pad_cmn_oe,
   input  logic                        i_pad_cmn_wck_oe,
   input  logic                        i_pad_cmn_ie,
   output logic [WIDTH-1:0]            o_core_eg,

   input  logic                        i_pad_bscan_cmn_n,
   input  logic                        i_pad_bscan_cmn_oe,
   input  logic                        i_pad_bscan_cmn_ie,
   input  logic [WIDTH-1:0]            i_pad_bscan_t,      // From BSCAN
   input  logic [WIDTH-1:0]            i_pad_bscan_c,      // From BSCAN
   output logic [WIDTH-1:0]            o_pad_lpbk_t,       // To CA clkmux and BSCAN
   output logic [WIDTH-1:0]            o_pad_lpbk_c,       // To CA clkmux and BSCAN
   output logic [WIDTH-1:0]            o_pad_eg_t,         // To DQS receiver
   output logic [WIDTH-1:0]            o_pad_eg_c,         // To DQS receiver
   inout  wire  [WIDTH-1:0]            pad_t,
   inout  wire  [WIDTH-1:0]            pad_c
);

   logic [WIDTH-1:0] pad_cmn_oe;

   logic [WIDTH-1:0] ddr_2to1;
   ddr_2to1_wrapper u_ddr_serializer_2to1 [WIDTH-1:0] (
       .o_z                   (ddr_2to1),
       .i_clk                 (i_ddr_clk_0),
       .i_clk_b               (i_ddr_clk_180),
       .i_even                (i_xdr_0),
       .i_odd                 (i_xdr_1)
   );

   logic [WIDTH-1:0] qdr_2to1;
   ddr_2to1_wrapper u_qdr_serializer_2to1 [WIDTH-1:0] (
       .o_z                   (qdr_2to1),
       .i_clk                 (i_qdr_clk_0),
       .i_clk_b               (i_qdr_clk_180),
       .i_even                (i_xdr_0),
       .i_odd                 (i_xdr_1)
   );




   wire [WIDTH-1:0]  xdr, xdr_b;

   genvar i;
   // Wire-Or'd output connections
   generate
      for (i=0; i<WIDTH; i=i+1) begin : BUFT
         if (!SLICE_MASK[i]) begin : EGRESS_BUFT
            logic [EWIDTH-1:0] egress_mode;
            assign egress_mode = i_egress_mode[EWIDTH*i+:EWIDTH];

            // Custom aggregation modes
            ddr_wcm_buft u_buft_bypass   (.i_a(i_xdr_0[i] ), .i_en(egress_mode[`DDR_ANA_EGRESS_BYPASS  ]), .o_z(xdr[i]));
            ddr_wcm_buft u_buft_ddr_2to1 (.i_a(ddr_2to1[i]), .i_en(egress_mode[`DDR_ANA_EGRESS_DDR_2TO1]), .o_z(xdr[i]));
            ddr_wcm_buft u_buft_qdr_2to1 (.i_a(qdr_2to1[i]), .i_en(egress_mode[`DDR_ANA_EGRESS_QDR_2TO1]), .o_z(xdr[i]));
         end else begin : EGRESS_FEEDTHROUGH
           ddr_wcm_buf u_buf [i] (.i_a(i_xdr_0[i]), .o_z(xdr[i]));
         end
      end
   endgenerate

   logic [WIDTH-1:0] xdr_lpde, xdr_lpde_b;

   genvar k;
   generate

      for (k=0; k<WIDTH; k=k+1) begin: PSLICE
         if (!WCK_MASK[k]) begin : WCK_OE
            assign pad_cmn_oe[k] = i_pad_cmn_wck_oe;
         end else if (!DQS_MASK[k]) begin : DQS_OE_DISABLE
            assign pad_cmn_oe[k] = '0; // Disable DQS TX
         end else begin : OE
            assign pad_cmn_oe[k] = i_pad_cmn_oe;
         end

         if (!LPDE_MASK[k]) begin : LPDE
      `ifdef DDR_LPDE_BEHAV
            ddr_lpde #(
               .LWIDTH        (LWIDTH),
               .PS_DLY        (PS_DLY)
            ) u_lpde (
               .o_d           (xdr_lpde[k]),
               .i_delay       (i_xdr_lpde_cfg[LWIDTH*k+:LWIDTH]),
               .i_d           (xdr[k])
            );
            ddr_wcm_inv u_xdr_lpde_inv (.i_a(xdr_lpde[k]), .o_z(xdr_lpde_b[k]));
      `else
         `ifdef DDR_LPDE_SE
            ddr_prog_dly_se_wrapper #(
               .PWIDTH        (LWIDTH)
            ) u_tx_prog_dly (
               .o_clk_b       (xdr_lpde_b[k]),
               .i_prog_dly_cfg(i_xdr_lpde_cfg[LWIDTH*k+:LWIDTH]),
               .i_clk         (xdr[k])
            );
            ddr_wcm_inv u_xdr_lpde_inv (.i_a(xdr_lpde_b[k]), .o_z(xdr_lpde[k]));
         `else
            ddr_wcm_inv u_xdr_inv [WIDTH-1:0] (.i_a(xdr), .o_z(xdr_b));
            ddr_prog_dly_wrapper #(
               .PWIDTH        (LWIDTH)
            ) u_tx_prog_dly (
               .o_clk         (xdr_lpde[k]),
               .o_clk_b       (xdr_lpde_b[k]),
               .i_dly_cfg     (i_xdr_lpde_cfg[LWIDTH*k+:LWIDTH]),
               .i_clk         (xdr[k]),
               .i_clk_b       (xdr_b[k])
            );
         `endif
      `endif
         end else begin: NO_LPDE
            ddr_wcm_inv u_xdr_inv (.i_a(xdr[k]), .o_z(xdr_b[k]));
            assign xdr_lpde[k]   = xdr[k];
            assign xdr_lpde_b[k] = xdr_b[k];
         end

         if (!PAD_MASK[k]) begin : PAD
            if (SE_PAD[k]) begin : SE_PAD_I
`ifdef DDR_PAD_TX_BEHAV
               ddr_pad_tx_se #(
                  .P0WIDTH     (TX0WIDTH),
                  .P1WIDTH     (TX1WIDTH)
               ) u_pad (
                  .i_freeze_n         (i_freeze_cmn_n),
                  .i_hiz_n            (i_hiz_cmn_n),
                  .i_pad_cfg          (i_pad_cfg[TX0WIDTH*k+:TX0WIDTH]),
                  .i_pad_cmn_cfg      (i_pad_cmn_cfg),
                  .i_core_eg          (xdr_lpde[k]),
                  .i_pad_oe           (pad_cmn_oe[k]),
                  .pad                (pad_t[k])
               );
`else

               if (!CKE_MASK[k]) begin : CKE_PAD

                  ddr_cke_drvr_lpbk_wrapper #(
                     .P0WIDTH            (TX0WIDTH),
                     .P1WIDTH            (TX1WIDTH)
                  ) cke_drvr (
                     .i_freeze_n_hv      (i_freeze_n_hv),
                     .i_freeze_n         (i_freeze_cmn_n),
                     .i_hiz_n            (i_hiz_cmn_n),
                     .i_d_n              (xdr_lpde_b[k]),
                     .i_oe               (pad_cmn_oe[k]),
                     .i_bs_mode_n        (i_pad_bscan_cmn_n),
                     .i_bs_oe            (i_pad_bscan_cmn_oe),
                     .i_bs_ie            (i_pad_bscan_cmn_ie),
                     .i_drvr_cfg         (i_pad_cfg[TX0WIDTH*k+:TX0WIDTH]),
                     .i_drvr_cmn_cfg     (i_pad_cmn_cfg),
                     .i_d_bs             (i_pad_bscan_t[k]),
                     .o_d_lpbk           (o_pad_lpbk_t[k]),
                     .pad                (pad_t[k])
                  );

                  //assign o_pad_eg_t[k] = '0;
                  ddr_wcm_tielo u_tielo_0 (.o_z(o_pad_eg_t[k]));

               end else begin : DQ_PAD
                  ddr_dq_drvr_lpbk_wrapper #(
                     .P0WIDTH            (TX0WIDTH),
                     .P1WIDTH            (TX1WIDTH)
                  ) dq_drvr (
                     .i_freeze_n         (i_freeze_cmn_n),
                     .i_hiz_n            (i_hiz_cmn_n),
                     .i_d_n              (xdr_lpde_b[k]),
                     .i_oe               (pad_cmn_oe[k]),
                     .i_bs_mode_n        (i_pad_bscan_cmn_n),
                     .i_bs_oe            (i_pad_bscan_cmn_oe),
                     .i_bs_ie            (i_pad_bscan_cmn_ie),
                     .i_drvr_cfg         (i_pad_cfg[TX0WIDTH*k+:TX0WIDTH]),
                     .i_drvr_cmn_cfg     (i_pad_cmn_cfg),
                     .i_d_bs             (i_pad_bscan_t[k]),
                     .o_d_lpbk           (o_pad_lpbk_t[k]),
                     .o_rx_in            (o_pad_eg_t[k]),
                     .pad                (pad_t[k])
                  );
               end

               //assign o_pad_lpbk_c[k] = '0;
               ddr_wcm_tielo u_tielo_0 (.o_z(o_pad_lpbk_c[k]));
               //assign o_pad_eg_c[k] = '0;
               ddr_wcm_tielo u_tielo_1 (.o_z(o_pad_eg_c[k]));
`endif
            end else begin : DIFF_PAD
`ifdef DDR_PAD_TX_BEHAV
               ddr_pad_tx_diff #(
                  .P0WIDTH            (TX0WIDTH),
                  .P1WIDTH            (TX1WIDTH)
               ) u_pad (
                  .i_freeze_n         (i_freeze_cmn_n),
                  .i_hiz_n            (i_hiz_cmn_n),
                  .i_pad_cfg          (i_pad_cfg[TX0WIDTH*k+:TX0WIDTH]),
                  .i_pad_cmn_cfg      (i_pad_cmn_cfg),
                  .i_core_eg          (xdr_lpde[k]),
                  .i_pad_oe           (pad_cmn_oe[k]),
                  .pad_t              (pad_t[k]),
                  .pad_c              (pad_c[k])
               );
`else

               ddr_dqs_drvr_lpbk_wrapper #(
                  .P0WIDTH            (TX0WIDTH),
                  .P1WIDTH            (TX1WIDTH)
               ) dqs_drvr (
                  .i_freeze_n         (i_freeze_cmn_n),
                  .i_hiz_n            (i_hiz_cmn_n),
                  .i_d_n              (xdr_lpde_b[k]),
                  .i_oe               (pad_cmn_oe[k]),
                  .i_ie               (i_pad_cmn_ie),
                  .i_bs_mode_n        (i_pad_bscan_cmn_n),
                  .i_bs_oe            (i_pad_bscan_cmn_oe),
                  .i_bs_ie            (i_pad_bscan_cmn_ie),
                  .i_drvr_cfg         (i_pad_cfg[TX0WIDTH*k+:TX0WIDTH]),
                  .i_drvr_cmn_cfg     (i_pad_cmn_cfg),
                  .i_d_bs_t           (i_pad_bscan_t[k]),
                  .i_d_bs_c           (i_pad_bscan_c[k]),
                  .o_d_lpbk_t         (o_pad_lpbk_t[k]),
                  .o_d_lpbk_c         (o_pad_lpbk_c[k]),
                  .o_rx_in_t          (o_pad_eg_t[k]),
                  .o_rx_in_c          (o_pad_eg_c[k]),
                  .pad_t              (pad_t[k]),
                  .pad_c              (pad_c[k])
               );
`endif
            end
         end else begin: NO_PAD
            assign pad_t[k] = 1'bz;
            assign pad_c[k] = 1'bz;
         end
      end

      //assign o_core_eg = xdr_lpde;
      ddr_wcm_buf u_buf [WIDTH-1:0] (.i_a(xdr_lpde), .o_z(o_core_eg));

   endgenerate

endmodule

module ddr_tx_dig #(
   parameter             WIDTH       =  1,
   parameter             NUM_WDPH    =  8,               // Write datapath data phases
   parameter             NUM_WPH     =  8,               // Write gearbox data phases
   parameter             WWIDTH      = NUM_WPH * WIDTH,  // Write datapath width
   parameter             E0WIDTH     =  6,               // Egress buffer control width
   parameter             E1WIDTH     =  7,               // Egress buffer control width
   parameter             FWIDTH      =  2,
   parameter             MXWIDTH     =  3,
   parameter             XWIDTH      =  $clog2(NUM_WDPH),
   parameter [WIDTH-1:0] SLICE_MASK  = '0                // Slice instance mask
) (

   input  logic [DEC_WGBWIDTH-1:0]     i_wgb_mode,
   input  logic [E0WIDTH*WIDTH-1:0]    i_egress_mode_ana,
   input  logic [E1WIDTH*WIDTH-1:0]    i_egress_mode_dig,
   input  logic [WIDTH-1:0]            i_bscan,

   input  logic [WIDTH-1:0]            i_qdr_clk_0,
   input  logic [WIDTH-1:0]            i_qdr_clk_180,
   input  logic [WIDTH-1:0]            i_ddr_clk_0,
   input  logic [WIDTH-1:0]            i_ddr_clk_180,
   input  logic [WIDTH-1:0]            i_sdr_clk,
   input  logic [WIDTH-1:0]            i_sdr_clk_b,
   input  logic [WIDTH-1:0]            i_sdr_div2_clk,
   input  logic [WIDTH-1:0]            i_sdr_div2_clk_b,
   input  logic [WIDTH-1:0]            i_sdr_rt_clk,
   input  logic [WIDTH-1:0]            i_sdr_rt_clk_b,

   input  logic [WIDTH-1:0]            i_sdr_rt_pipe_en,

   input  logic [FWIDTH*WIDTH-1:0]     i_sdr_0_fc_dly,
   input  logic [MXWIDTH*WIDTH-1:0]    i_sdr_0_x_sel,
   input  logic [WIDTH-1:0]            i_sdr_0_pipe_en,
   input  logic [FWIDTH*WIDTH-1:0]     i_sdr_1_fc_dly,
   input  logic [MXWIDTH*WIDTH-1:0]    i_sdr_1_x_sel,
   input  logic [WIDTH-1:0]            i_sdr_1_pipe_en,
   input  logic [FWIDTH*WIDTH-1:0]     i_sdr_2_fc_dly,
   input  logic [MXWIDTH*WIDTH-1:0]    i_sdr_2_x_sel,
   input  logic [WIDTH-1:0]            i_sdr_2_pipe_en,
   input  logic [FWIDTH*WIDTH-1:0]     i_sdr_3_fc_dly,
   input  logic [MXWIDTH*WIDTH-1:0]    i_sdr_3_x_sel,
   input  logic [WIDTH-1:0]            i_sdr_3_pipe_en,

   input  logic [(MXWIDTH-1)*WIDTH-1:0]i_ddr_0_x_sel,
   input  logic [WIDTH-1:0]            i_ddr_0_pipe_en,
   input  logic [(MXWIDTH-1)*WIDTH-1:0]i_ddr_1_x_sel,
   input  logic [WIDTH-1:0]            i_ddr_1_pipe_en,

   input  logic [WWIDTH-1:0]           i_sdr,
   output logic [WIDTH-1:0]            o_xdr_0,
   output logic [WIDTH-1:0]            o_xdr_1,
   output logic [WIDTH-1:0]            o_xdr_2,
   output logic [WIDTH-1:0]            o_xdr_3
);

   logic [WIDTH-1:0]            ig_sdr_0_x;
   logic [WIDTH-1:0]            eg_sdr_0_x;
   logic [WIDTH-1:0]            ig_sdr_1_x;
   logic [WIDTH-1:0]            eg_sdr_1_x;
   logic [WIDTH-1:0]            ig_sdr_2_x;
   logic [WIDTH-1:0]            eg_sdr_2_x;
   logic [WIDTH-1:0]            ig_sdr_3_x;
   logic [WIDTH-1:0]            eg_sdr_3_x;
   logic [WIDTH-1:0]            ig_ddr_0_x;
   logic [WIDTH-1:0]            eg_ddr_0_x;
   logic [WIDTH-1:0]            ig_ddr_1_x;
   logic [WIDTH-1:0]            eg_ddr_1_x;

   genvar i,j;
   generate
      for (j=0; j<WIDTH; j=j+1) begin: CSLICE
         if (!SLICE_MASK[j]) begin : SLICE

            ddr_wcm_mux_4to1 #(
               .DWIDTH               (1)
            ) u_sdr_mux4to1_0 (
               .i_sel                (i_sdr_0_x_sel[MXWIDTH*j+:XWIDTH]),
               .i_0                  (eg_sdr_0_x[j]),
               .i_1                  (eg_sdr_1_x[j]),
               .i_2                  (eg_sdr_2_x[j]),
               .i_3                  (eg_sdr_3_x[j]),
               .o_z                  (ig_sdr_0_x[j])
            );
            ddr_wcm_mux_4to1 #(
               .DWIDTH               (1)
            ) u_sdr_mux4to1_1 (
               .i_sel                (i_sdr_1_x_sel[MXWIDTH*j+:XWIDTH]),
               .i_0                  (eg_sdr_0_x[j]),
               .i_1                  (eg_sdr_1_x[j]),
               .i_2                  (eg_sdr_2_x[j]),
               .i_3                  (eg_sdr_3_x[j]),
               .o_z                  (ig_sdr_1_x[j])
            );
            ddr_wcm_mux_4to1 #(
               .DWIDTH               (1)
            ) u_sdr_mux4to1_2 (
               .i_sel                (i_sdr_2_x_sel[MXWIDTH*j+:XWIDTH]),
               .i_0                  (eg_sdr_0_x[j]),
               .i_1                  (eg_sdr_1_x[j]),
               .i_2                  (eg_sdr_2_x[j]),
               .i_3                  (eg_sdr_3_x[j]),
               .o_z                  (ig_sdr_2_x[j])
            );
            ddr_wcm_mux_4to1 #(
               .DWIDTH               (1)
            ) u_sdr_mux4to1_3 (
               .i_sel                (i_sdr_3_x_sel[MXWIDTH*j+:XWIDTH]),
               .i_0                  (eg_sdr_0_x[j]),
               .i_1                  (eg_sdr_1_x[j]),
               .i_2                  (eg_sdr_2_x[j]),
               .i_3                  (eg_sdr_3_x[j]),
               .o_z                  (ig_sdr_3_x[j])
            );

            ddr_wcm_mux_2to1 #(
               .DWIDTH               (1)
            ) u_ddr_mux2to1_0 (
               .i_sel                (i_ddr_0_x_sel[(MXWIDTH-1)*j+:(XWIDTH-1)]),
               .i_0                  (eg_ddr_0_x[j]),
               .i_1                  (eg_ddr_1_x[j]),
               .o_z                  (ig_ddr_0_x[j])
            );
            ddr_wcm_mux_2to1 #(
               .DWIDTH               (1)
            ) u_ddr_mux2to1_1 (
               .i_sel                (i_ddr_1_x_sel[(MXWIDTH-1)*j+:(XWIDTH-1)]),
               .i_0                  (eg_ddr_0_x[j]),
               .i_1                  (eg_ddr_1_x[j]),
               .o_z                  (ig_ddr_1_x[j])
            );

         end
      end

      for (i=0; i<WIDTH; i=i+1) begin: DSLICE
         if (!SLICE_MASK[i]) begin : SLICE
            ddr_tx_xdr #(
               .SLICE_MASK                 ('0),
               .DWIDTH                     (1),
               .NUM_WPH                    (NUM_WPH),
               .E0WIDTH                    (E0WIDTH),
               .E1WIDTH                    (E1WIDTH),
               .FWIDTH                     (FWIDTH)
            ) u_tx_xdr (
               .i_wgb_mode                 (i_wgb_mode),
               .i_egress_mode_dig          (i_egress_mode_dig[E1WIDTH*i+:E1WIDTH]),
               .i_egress_mode_ana          (i_egress_mode_ana[E0WIDTH*i+:E0WIDTH]),
               .i_bscan                    (i_bscan[i]),

               .i_qdr_clk_0                (i_qdr_clk_0[i]),
               .i_qdr_clk_180              (i_qdr_clk_180[i]),
               .i_ddr_clk_0                (i_ddr_clk_0[i]),
               .i_ddr_clk_180              (i_ddr_clk_180[i]),
               .i_sdr_clk                  (i_sdr_clk[i]),
               .i_sdr_clk_b                (i_sdr_clk_b[i]),
               .i_sdr_div2_clk             (i_sdr_div2_clk[i]),
               .i_sdr_div2_clk_b           (i_sdr_div2_clk_b[i]),
               .i_sdr_rt_clk               (i_sdr_rt_clk[i]),
               .i_sdr_rt_clk_b             (i_sdr_rt_clk_b[i]),
               .i_sdr_rt_pipe_en           (i_sdr_rt_pipe_en[i]),
               .i_sdr                         (i_sdr[NUM_WPH*i+:NUM_WPH]),
               .i_sdr_0_pipe_en            (i_sdr_0_pipe_en[i]),
               .i_sdr_0_fc_dly             (i_sdr_0_fc_dly[FWIDTH*i+:FWIDTH]),
               .i_sdr_0_x                  (ig_sdr_0_x[i]),
               .o_sdr_0_x                  (eg_sdr_0_x[i]),
               .i_sdr_1_pipe_en            (i_sdr_1_pipe_en[i]),
               .i_sdr_1_fc_dly             (i_sdr_1_fc_dly[FWIDTH*i+:FWIDTH]),
               .i_sdr_1_x                  (ig_sdr_1_x[i]),
               .o_sdr_1_x                  (eg_sdr_1_x[i]),
               .i_sdr_2_pipe_en            (i_sdr_2_pipe_en[i]),
               .i_sdr_2_fc_dly             (i_sdr_2_fc_dly[FWIDTH*i+:FWIDTH]),
               .i_sdr_2_x                  (ig_sdr_2_x[i]),
               .o_sdr_2_x                  (eg_sdr_2_x[i]),
               .i_sdr_3_pipe_en            (i_sdr_3_pipe_en[i]),
               .i_sdr_3_fc_dly             (i_sdr_3_fc_dly[FWIDTH*i+:FWIDTH]),
               .i_sdr_3_x                  (ig_sdr_3_x[i]),
               .o_sdr_3_x                  (eg_sdr_3_x[i]),
               .i_ddr_0_pipe_en            (i_ddr_0_pipe_en[i]),
               .i_ddr_0_x                  (ig_ddr_0_x[i]),
               .o_ddr_0_x                  (eg_ddr_0_x[i]),
               .i_ddr_1_pipe_en            (i_ddr_1_pipe_en[i]),
               .i_ddr_1_x                  (ig_ddr_1_x[i]),
               .o_ddr_1_x                  (eg_ddr_1_x[i]),
               .o_xdr_0                    (o_xdr_0[i]),
               .o_xdr_1                    (o_xdr_1[i]),
               .o_xdr_2                    (o_xdr_2[i]),
               .o_xdr_3                    (o_xdr_3[i])
            );
         end else begin: FEEDTHROUGH
            ddr_wcm_buf u_buf_0 [i] (.i_a(i_sdr[NUM_WPH*i]), .o_z(o_xdr_0[i]));
            ddr_wcm_buf u_buf_1 [i] (.i_a(i_sdr[NUM_WPH*i]), .o_z(o_xdr_1[i]));
            ddr_wcm_buf u_buf_2 [i] (.i_a(i_sdr[NUM_WPH*i]), .o_z(o_xdr_2[i]));
            ddr_wcm_buf u_buf_3 [i] (.i_a(i_sdr[NUM_WPH*i]), .o_z(o_xdr_3[i]));
         end
      end

   endgenerate

endmodule

module ddr_tx_xdr #(
   parameter              DWIDTH      = 1,
   parameter [DWIDTH-1:0] SLICE_MASK  = '0,
   parameter              NUM_WPH     = 8,
   parameter              WWIDTH      = NUM_WPH * DWIDTH,
   parameter              E0WIDTH     = 6,
   parameter              E1WIDTH     = 7,
   parameter              FWIDTH      = 2
) (
   input  logic [DEC_WGBWIDTH-1:0]    i_wgb_mode,
   input  logic [E0WIDTH*DWIDTH-1:0]  i_egress_mode_ana,
   input  logic [E1WIDTH*DWIDTH-1:0]  i_egress_mode_dig,
   input  logic [DWIDTH-1:0]          i_bscan,

   input  logic [DWIDTH-1:0]          i_qdr_clk_0,
   input  logic [DWIDTH-1:0]          i_qdr_clk_180,
   input  logic [DWIDTH-1:0]          i_ddr_clk_0,
   input  logic [DWIDTH-1:0]          i_ddr_clk_180,
   input  logic [DWIDTH-1:0]          i_sdr_clk,
   input  logic [DWIDTH-1:0]          i_sdr_clk_b,
   input  logic [DWIDTH-1:0]          i_sdr_div2_clk,
   input  logic [DWIDTH-1:0]          i_sdr_div2_clk_b,
   input  logic [DWIDTH-1:0]          i_sdr_rt_clk,
   input  logic [DWIDTH-1:0]          i_sdr_rt_clk_b,
   input  logic [DWIDTH-1:0]          i_sdr_rt_pipe_en,

   input  logic [WWIDTH-1:0]          i_sdr,
   input  logic [DWIDTH-1:0]          i_sdr_0_pipe_en,
   input  logic [FWIDTH*DWIDTH-1:0]   i_sdr_0_fc_dly,
   input  logic [DWIDTH-1:0]          i_sdr_0_x,
   output logic [DWIDTH-1:0]          o_sdr_0_x,
   input  logic [DWIDTH-1:0]          i_sdr_1_pipe_en,
   input  logic [FWIDTH*DWIDTH-1:0]   i_sdr_1_fc_dly,
   input  logic [DWIDTH-1:0]          i_sdr_1_x,
   output logic [DWIDTH-1:0]          o_sdr_1_x,
   input  logic [DWIDTH-1:0]          i_sdr_2_pipe_en,
   input  logic [FWIDTH*DWIDTH-1:0]   i_sdr_2_fc_dly,
   input  logic [DWIDTH-1:0]          i_sdr_2_x,
   output logic [DWIDTH-1:0]          o_sdr_2_x,
   input  logic [DWIDTH-1:0]          i_sdr_3_pipe_en,
   input  logic [FWIDTH*DWIDTH-1:0]   i_sdr_3_fc_dly,
   input  logic [DWIDTH-1:0]          i_sdr_3_x,
   output logic [DWIDTH-1:0]          o_sdr_3_x,
   input  logic [DWIDTH-1:0]          i_ddr_0_pipe_en,
   input  logic [DWIDTH-1:0]          i_ddr_0_x,
   output logic [DWIDTH-1:0]          o_ddr_0_x,
   input  logic [DWIDTH-1:0]          i_ddr_1_pipe_en,
   input  logic [DWIDTH-1:0]          i_ddr_1_x,
   output logic [DWIDTH-1:0]          o_ddr_1_x,
   output wire  [DWIDTH-1:0]          o_xdr_0,
   output wire  [DWIDTH-1:0]          o_xdr_1,
   output wire  [DWIDTH-1:0]          o_xdr_2,
   output wire  [DWIDTH-1:0]          o_xdr_3
);

   logic [DWIDTH-1:0] sdr_0_gb;
   logic [DWIDTH-1:0] sdr_1_gb;
   logic [DWIDTH-1:0] sdr_2_gb;
   logic [DWIDTH-1:0] sdr_3_gb;

   //IFR_FIXME: When GB is enable the data output needs to be converted from pow to wop inside the tx_sdr_gearbox.
   ddr_tx_sdr_gearbox #(
      .NUM_WPH              (NUM_WPH)
   ) u_tx_sdr_gearbox (
      .i_clk                (i_sdr_div2_clk),
      .i_clk_b              (i_sdr_div2_clk_b),
      .i_wgb_mode           (i_wgb_mode),
      .o_sdr_0              (sdr_0_gb),                   // 1-bit phase
      .o_sdr_1              (sdr_1_gb),                   // 1-bit phase
      .o_sdr_2              (sdr_2_gb),                   // 1-bit phase
      .o_sdr_3              (sdr_3_gb),                   // 1-bit phase
      .i_sdr                (i_sdr)                       // WOP format
   );

   logic [DWIDTH-1:0] sdr_0;

   ddr_tx_sdr #(
      .DWIDTH                     (DWIDTH)
   ) u_tx_sdr_0 (
      .i_sdr_clk                  (i_sdr_clk),
      .i_sdr_clk_b                (i_sdr_clk_b),
      .i_sdr_rt_clk               (i_sdr_rt_clk),
      .i_sdr_rt_clk_b             (i_sdr_rt_clk_b),
      .i_sdr_rt_pipe_en           (i_sdr_rt_pipe_en),
      .i_sdr_fc_dly               (i_sdr_0_fc_dly),
      .i_sdr_d                    (sdr_0_gb),
      .o_sdr_q                    (sdr_0)
   );
   logic [DWIDTH-1:0] sdr_1;

   ddr_tx_sdr #(
      .DWIDTH                     (DWIDTH)
   ) u_tx_sdr_1 (
      .i_sdr_clk                  (i_sdr_clk),
      .i_sdr_clk_b                (i_sdr_clk_b),
      .i_sdr_rt_clk               (i_sdr_rt_clk),
      .i_sdr_rt_clk_b             (i_sdr_rt_clk_b),
      .i_sdr_rt_pipe_en           (i_sdr_rt_pipe_en),
      .i_sdr_fc_dly               (i_sdr_1_fc_dly),
      .i_sdr_d                    (sdr_1_gb),
      .o_sdr_q                    (sdr_1)
   );
   logic [DWIDTH-1:0] sdr_2;

   ddr_tx_sdr #(
      .DWIDTH                     (DWIDTH)
   ) u_tx_sdr_2 (
      .i_sdr_clk                  (i_sdr_clk),
      .i_sdr_clk_b                (i_sdr_clk_b),
      .i_sdr_rt_clk               (i_sdr_rt_clk),
      .i_sdr_rt_clk_b             (i_sdr_rt_clk_b),
      .i_sdr_rt_pipe_en           (i_sdr_rt_pipe_en),
      .i_sdr_fc_dly               (i_sdr_2_fc_dly),
      .i_sdr_d                    (sdr_2_gb),
      .o_sdr_q                    (sdr_2)
   );
   logic [DWIDTH-1:0] sdr_3;

   ddr_tx_sdr #(
      .DWIDTH                     (DWIDTH)
   ) u_tx_sdr_3 (
      .i_sdr_clk                  (i_sdr_clk),
      .i_sdr_clk_b                (i_sdr_clk_b),
      .i_sdr_rt_clk               (i_sdr_rt_clk),
      .i_sdr_rt_clk_b             (i_sdr_rt_clk_b),
      .i_sdr_rt_pipe_en           (i_sdr_rt_pipe_en),
      .i_sdr_fc_dly               (i_sdr_3_fc_dly),
      .i_sdr_d                    (sdr_3_gb),
      .o_sdr_q                    (sdr_3)
   );

   logic [DWIDTH-1:0] ddr_2to1_0;

   ddr_serializer_2to1 #(
      .DWIDTH                     (DWIDTH)
   ) u_ddr_serializer_2to1_0 (
      .i_sdr_clk_0                (i_ddr_clk_0),
      .i_sdr_clk_180              (i_ddr_clk_180),
      .i_ddr_clk_0                (i_ddr_clk_0),
      .i_ddr_clk_180              (i_ddr_clk_180),
      .i_sdr_0_pipe_en            (i_sdr_0_pipe_en),
      .i_sdr_0                    (sdr_0),
      .i_sdr_0_x                  (i_sdr_0_x),
      .o_sdr_0_x                  (o_sdr_0_x),
      .i_sdr_1_pipe_en            (i_sdr_1_pipe_en),
      .i_sdr_1                    (sdr_1),
      .i_sdr_1_x                  (i_sdr_1_x),
      .o_sdr_1_x                  (o_sdr_1_x),
      .o_ddr                      (ddr_2to1_0)
   );
   logic [DWIDTH-1:0] ddr_2to1_1;

   ddr_serializer_2to1 #(
      .DWIDTH                     (DWIDTH)
   ) u_ddr_serializer_2to1_1 (
      .i_sdr_clk_0                (i_ddr_clk_0),
      .i_sdr_clk_180              (i_ddr_clk_180),
      .i_ddr_clk_0                (i_ddr_clk_0),
      .i_ddr_clk_180              (i_ddr_clk_180),
      .i_sdr_0_pipe_en            (i_sdr_2_pipe_en),
      .i_sdr_0                    (sdr_2),
      .i_sdr_0_x                  (i_sdr_2_x),
      .o_sdr_0_x                  (o_sdr_2_x),
      .i_sdr_1_pipe_en            (i_sdr_3_pipe_en),
      .i_sdr_1                    (sdr_3),
      .i_sdr_1_x                  (i_sdr_3_x),
      .o_sdr_1_x                  (o_sdr_3_x),
      .o_ddr                      (ddr_2to1_1)
   );

   logic [DWIDTH-1:0] qdr_2to1_0;

   ddr_serializer_2to1 #(
      .DWIDTH                     (DWIDTH)
   ) u_qdr_serializer_2to1_0 (
      .i_sdr_clk_0                (i_qdr_clk_0),
      .i_sdr_clk_180              (i_qdr_clk_180),
      .i_ddr_clk_0                (i_qdr_clk_0),
      .i_ddr_clk_180              (i_qdr_clk_180),
      .i_sdr_0_pipe_en            (i_ddr_0_pipe_en),
      .i_sdr_0                    (ddr_2to1_0),
      .i_sdr_0_x                  (i_ddr_0_x),
      .o_sdr_0_x                  (o_ddr_0_x),
      .i_sdr_1_pipe_en            (i_ddr_1_pipe_en),
      .i_sdr_1                    (ddr_2to1_1),
      .i_sdr_1_x                  (i_ddr_1_x),
      .o_sdr_1_x                  (o_ddr_1_x),
      .o_ddr                      (qdr_2to1_0)
   );

   logic [DWIDTH-1:0] odr_2to1_0;
   assign odr_2to1_0 = 'bz;

   logic [DWIDTH-1:0] qdr_4to1;
   assign qdr_4to1 = 'bz;

   logic [DWIDTH-1:0] odr_4to1;
   assign odr_4to1 = 'bz;

   genvar i;
   // Wire-Or'd output connections
   generate
      for (i=0; i<DWIDTH; i=i+1) begin : BUFT
         if(!SLICE_MASK[i]) begin : EGRESS_BUFT
            logic [E1WIDTH-1:0] egress_mode;
            logic [E0WIDTH-1:0] egress_mode_ana;
            logic               egress_mode_sdr , eg_byp_n ;
            assign egress_mode     = i_egress_mode_dig[E1WIDTH*i+:E1WIDTH];
            assign egress_mode_ana = i_egress_mode_ana[E0WIDTH*i+:E0WIDTH];
            ddr_wcm_inv    u_eg_byp_inv   (.i_a(egress_mode_ana[`DDR_ANA_EGRESS_BYPASS]),      .o_z(eg_byp_n));
            ddr_wcm_and    u_eg_sdr       (.o_z(egress_mode_sdr), .i_a(egress_mode[`DDR_DIG_EGRESS_SDR]), .i_b(eg_byp_n)) ;
            ddr_wcm_buft u_buft_bscan_0    (.i_a(i_bscan[i]   ), .i_en(egress_mode[`DDR_DIG_EGRESS_BSCAN   ]), .o_z(o_xdr_0[i]));
            ddr_wcm_buft u_buft_sdr_0      (.i_a(i_sdr_0_x[i] ), .i_en(egress_mode_sdr                                   ), .o_z(o_xdr_0[i]));
            ddr_wcm_buft u_buft_ddr_2to1_0 (.i_a(i_ddr_0_x[i]), .i_en(egress_mode[`DDR_DIG_EGRESS_DDR_2TO1]), .o_z(o_xdr_0[i]));
            ddr_wcm_buft u_buft_sdr_1      (.i_a(i_sdr_1_x[i]   ), .i_en(egress_mode_sdr                                ), .o_z(o_xdr_1[i]));
            ddr_wcm_buft u_buft_ddr_2to1_1 (.i_a(i_ddr_1_x[i]   ), .i_en(egress_mode[`DDR_DIG_EGRESS_DDR_2TO1]), .o_z(o_xdr_1[i]));



         end else begin : EGRESS_FEEDTHROUGH
           ddr_wcm_buf u_buf_0 (.i_a(i_sdr[NUM_WPH*i+0]), .o_z(o_xdr_0[i]));
           ddr_wcm_buf u_buf_1 (.i_a(i_sdr[NUM_WPH*i+1]), .o_z(o_xdr_1[i]));
           ddr_wcm_buf u_buf_2 (.i_a(i_sdr[NUM_WPH*i+2]), .o_z(o_xdr_2[i]));
           ddr_wcm_buf u_buf_3 (.i_a(i_sdr[NUM_WPH*i+3]), .o_z(o_xdr_3[i]));
         end
      end
   endgenerate

endmodule

module ddr_serializer_2to1 #(
   parameter DWIDTH = 1
) (
   input  logic [DWIDTH-1:0]        i_sdr_clk_0,
   input  logic [DWIDTH-1:0]        i_sdr_clk_180,
   input  logic [DWIDTH-1:0]        i_ddr_clk_0,
   input  logic [DWIDTH-1:0]        i_ddr_clk_180,
   input  logic [DWIDTH-1:0]        i_sdr_0_pipe_en,
   input  logic [DWIDTH-1:0]        i_sdr_0,
   input  logic [DWIDTH-1:0]        i_sdr_0_x,
   output logic [DWIDTH-1:0]        o_sdr_0_x,
   input  logic [DWIDTH-1:0]        i_sdr_1_pipe_en,
   input  logic [DWIDTH-1:0]        i_sdr_1,
   input  logic [DWIDTH-1:0]        i_sdr_1_x,
   output logic [DWIDTH-1:0]        o_sdr_1_x,
   output logic [DWIDTH-1:0]        o_ddr
);

   logic [DWIDTH-1:0] sdr_1_pipe, sdr_1_pipe_mux;
   logic [DWIDTH-1:0] sdr_0_pipe, sdr_0_pipe_mux;

   ddr_wcm_dff  u_sdr_0_dff   [DWIDTH-1:0] (.i_clk(i_sdr_clk_0), .i_clk_b(i_sdr_clk_180), .i_d(i_sdr_0), .o_q(sdr_0_pipe));
   ddr_wcm_mux  u_sdr_0_p_mux [DWIDTH-1:0] (.i_sel(i_sdr_0_pipe_en), .i_a(i_sdr_0), .i_b(sdr_0_pipe), .o_z(sdr_0_pipe_mux));

   ddr_wcm_dff  u_sdr_1_dff   [DWIDTH-1:0] (.i_clk(i_sdr_clk_0), .i_clk_b(i_sdr_clk_180), .i_d(i_sdr_1), .o_q(sdr_1_pipe));
   ddr_wcm_mux  u_sdr_1_p_mux [DWIDTH-1:0] (.i_sel(i_sdr_1_pipe_en), .i_a(i_sdr_1), .i_b(sdr_1_pipe), .o_z(sdr_1_pipe_mux));

   ddr_2to1_wrapper u_ddr_serializer_2to1 [DWIDTH-1:0] (.o_z(o_ddr), .i_clk(i_ddr_clk_0), .i_clk_b(i_ddr_clk_180), .i_even(i_sdr_0_x), .i_odd(i_sdr_1_x));

   assign o_sdr_0_x = sdr_0_pipe_mux;
   assign o_sdr_1_x = sdr_1_pipe_mux;

endmodule

// Tx datapath SDR full-cycle delay
module ddr_tx_sdr #(
   parameter DWIDTH = 1,
   parameter FWIDTH = 2
) (
   input  logic [DWIDTH-1:0]        i_sdr_clk,
   input  logic [DWIDTH-1:0]        i_sdr_clk_b,
   input  logic [DWIDTH-1:0]        i_sdr_rt_clk,
   input  logic [DWIDTH-1:0]        i_sdr_rt_clk_b,
   input  logic [DWIDTH-1:0]        i_sdr_rt_pipe_en,
   input  logic [FWIDTH*DWIDTH-1:0] i_sdr_fc_dly,
   input  logic [DWIDTH-1:0]        i_sdr_d,
   output logic [DWIDTH-1:0]        o_sdr_q
);

   logic [DWIDTH-1:0] sdr_fc_pipe,  sdr_rt_pipe;
   logic [DWIDTH-1:0] sdr_clk,      sdr_clk_b;

   ddr_wcm_inv    u_sdr_clk_inv   [DWIDTH-1:0] (.i_a(i_sdr_clk),      .o_z(sdr_clk_b));
   ddr_wcm_inv    u_sdr_clk_b_inv [DWIDTH-1:0] (.i_a(i_sdr_clk_b),    .o_z(sdr_clk));
   ddr_wcm_fc_dly u_sdr_fc_dly    [DWIDTH-1:0] (.i_clk(sdr_clk),      .i_clk_b(sdr_clk_b),      .i_delay(i_sdr_fc_dly), .i_d(i_sdr_d), .o_q(sdr_fc_pipe));
   ddr_wcm_dff    u_sdr_rt_dff    [DWIDTH-1:0] (.i_clk(i_sdr_rt_clk), .i_clk_b(i_sdr_rt_clk_b), .i_d(sdr_fc_pipe), .o_q(sdr_rt_pipe));
   ddr_wcm_mux    u_sdr_rt_mux    [DWIDTH-1:0] (.i_sel(i_sdr_rt_pipe_en), .i_a(sdr_fc_pipe),    .i_b(sdr_rt_pipe), .o_z(o_sdr_q));

endmodule

// Write datapath gearbox
module ddr_tx_sdr_gearbox #(
   parameter NUM_WPH = 8
) (
   input  logic                     i_clk,
   input  logic                     i_clk_b,
   input  logic [DEC_WGBWIDTH-1:0]  i_wgb_mode,
   output logic                     o_sdr_0,
   output logic                     o_sdr_1,
   output logic                     o_sdr_2,
   output logic                     o_sdr_3,
   input  logic [NUM_WPH-1:0]       i_sdr

);

   // ------------------------------------------------------------------------
   // Gearbox mapping
   // ------------------------------------------------------------------------

   integer i,j,k,l;


   //integer map_8to4 [7:0] = {7,3,6,2,5,1,4,0};
   logic [31:0] map_8to4 [7:0];
   always_comb begin
      for (k=0; k<8; k=k+2) begin
         map_8to4[k  ] = k/2;
         map_8to4[k+1] = k/2 + 4;
      end
   end

   logic [7:0] d_8to4;
   always_comb begin
      for (l=0; l<8; l=l+1)
         d_8to4[l] = i_sdr[map_8to4[l]];
   end

   logic gb_en;
   assign gb_en = i_wgb_mode[`WGB_8TO4_IDX];

   logic [NUM_WPH-1:0] d_int;

   logic clk_cgc, clk_b_cgc;

   // Only enable clock in appropriate mode
   ddr_wcm_cgc_rl_2ph u_cgc_rl_2ph (.i_clk(i_clk  ), .i_clk_b(i_clk_b), .i_en(gb_en), .o_clk(clk_cgc  ), .o_clk_b(clk_b_cgc));

   //ddr_wcm_func_mux_2to1 u_gb_mux_`k (.i_clk_0(clk_cgc), .i_clk_180(clk_b_cgc), .i_d1(d_8to4[`i] ), .i_d0(d_8to4[`j] ), .o_q(d_int[`k]));
   ddr_2to1_wrapper u_gb_mux_0 (.o_z(d_int[0]), .i_clk(clk_cgc), .i_clk_b(clk_b_cgc), .i_even(d_8to4[0]), .i_odd(d_8to4[1]));
   //ddr_wcm_func_mux_2to1 u_gb_mux_`k (.i_clk_0(clk_cgc), .i_clk_180(clk_b_cgc), .i_d1(d_8to4[`i] ), .i_d0(d_8to4[`j] ), .o_q(d_int[`k]));
   ddr_2to1_wrapper u_gb_mux_1 (.o_z(d_int[1]), .i_clk(clk_cgc), .i_clk_b(clk_b_cgc), .i_even(d_8to4[2]), .i_odd(d_8to4[3]));
   //ddr_wcm_func_mux_2to1 u_gb_mux_`k (.i_clk_0(clk_cgc), .i_clk_180(clk_b_cgc), .i_d1(d_8to4[`i] ), .i_d0(d_8to4[`j] ), .o_q(d_int[`k]));
   ddr_2to1_wrapper u_gb_mux_2 (.o_z(d_int[2]), .i_clk(clk_cgc), .i_clk_b(clk_b_cgc), .i_even(d_8to4[4]), .i_odd(d_8to4[5]));
   //ddr_wcm_func_mux_2to1 u_gb_mux_`k (.i_clk_0(clk_cgc), .i_clk_180(clk_b_cgc), .i_d1(d_8to4[`i] ), .i_d0(d_8to4[`j] ), .o_q(d_int[`k]));
   ddr_2to1_wrapper u_gb_mux_3 (.o_z(d_int[3]), .i_clk(clk_cgc), .i_clk_b(clk_b_cgc), .i_even(d_8to4[6]), .i_odd(d_8to4[7]));

   ddr_wcm_mux u_byp_mux_0 (.i_sel(gb_en), .i_a(i_sdr[0]), .i_b(d_int[0]), .o_z(o_sdr_0));
   ddr_wcm_mux u_byp_mux_1 (.i_sel(gb_en), .i_a(i_sdr[1]), .i_b(d_int[1]), .o_z(o_sdr_1));
   ddr_wcm_mux u_byp_mux_2 (.i_sel(gb_en), .i_a(i_sdr[2]), .i_b(d_int[2]), .o_z(o_sdr_2));
   ddr_wcm_mux u_byp_mux_3 (.i_sel(gb_en), .i_a(i_sdr[3]), .i_b(d_int[3]), .o_z(o_sdr_3));

endmodule

module ddr_tx_cc #(
   parameter P0WIDTH = 15,
   parameter P1WIDTH = 9,
   parameter DFIRDCLKEN_PEXTWIDTH = 4
) (
   input  logic                            i_scan_clk,
   input  logic                            i_scan_mode,
   //input  logic                            i_scan_cgc_ctrl,
   output logic [1:0]                      o_tst_clk,

   input  logic                            i_pll_clk_0,
   input  logic                            i_pll_clk_90,
   input  logic                            i_pll_clk_180,
   input  logic                            i_pll_clk_270,

   input  logic [DEC_CK2WCKRWIDTH-1:0]     i_ck2wck_ratio,
   input  logic                            i_dqs_dfi_wrtraffic,  //ASYNC
   input  logic                            i_dq_dfi_wrtraffic,   //ASYNC
   input  logic                            i_csp_div_rst_n,      //ASYNC Reset

   input  logic [DEC_DGBWIDTH-1:0]         i_tgb_mode,
   input  logic [DEC_WGBWIDTH-1:0]         i_wgb_mode,
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

   output logic                            o_dqs_qdr_clk_0,
   output logic                            o_dq_qdr_clk_0,
   output logic                            o_dqs_qdr_clk_180,
   output logic                            o_dq_qdr_clk_180,
   output logic                            o_dqs_ddr_clk_0,
   output logic                            o_dq_ddr_clk_0,
   output logic                            o_dqs_ddr_clk_180,
   output logic                            o_dq_ddr_clk_180,
   output logic                            o_dqs_sdr_rt_clk,
   output logic                            o_dqs_sdr_rt_clk_b,
   output logic                            o_dq_sdr_rt_clk,
   output logic                            o_dq_sdr_rt_clk_b,
   output logic                            o_sdr_clk,
   output logic                            o_sdr_clk_b,
   output logic                            o_sdr_div2_clk,
   output logic                            o_sdr_div2_clk_b,
   output logic                            o_dfiwr_clk_1,
   output logic                            o_dfiwr_clk_2,
   output logic                            o_dfird_clk_1,
   output logic                            o_dfird_clk_2,
   output logic                            o_phy_clk
);

   // ------------------------------------------------------------------------
   // WCK2CK Ratio DIV - used in LP5 CA : CK2WCK=1:4 ratio. Bypass for all other cases.
   // ------------------------------------------------------------------------
   logic pll_div_clk_0, pll_div_clk_90, pll_div_clk_180, pll_div_clk_270;
   logic ca_div_en, ca_div_byp ;

   // If CKTOWCK is 1:4, use below div2
   ddr_wcm_and u_ca_div_en (.o_z(ca_div_en), .i_a(i_ck2wck_ratio[`CK2WCK_1TO4_IDX]), .i_b(i_csp_div_rst_n)) ;

   // Bypass the clock divider if no division is required
   ddr_wcm_inv u_ca_div_byp  (.i_a(i_ck2wck_ratio[`CK2WCK_1TO4_IDX]), .o_z(ca_div_byp));

   // 4-phase clock divider
   ddr_wcm_div2_4ph u_ca_div2_4ph (
      .i_clk_0    (i_pll_clk_0),
      .i_clk_90   (i_pll_clk_90),
      .i_clk_180  (i_pll_clk_180),
      .i_clk_270  (i_pll_clk_270),
      .i_div_en   (ca_div_en),
      .i_div_byp  (ca_div_byp),
      .o_clk_0    (pll_div_clk_0),
      .o_clk_90   (pll_div_clk_90),
      .o_clk_180  (pll_div_clk_180),
      .o_clk_270  (pll_div_clk_270)
   );

   // ------------------------------------------------------------------------
   // PLL Clock
   // ------------------------------------------------------------------------

   logic pll_clk_0, pll_clk_90, pll_clk_180, pll_clk_270;

   assign pll_clk_0   = pll_div_clk_0 ;
   assign pll_clk_90  = pll_div_clk_90 ;
   assign pll_clk_180 = pll_div_clk_180 ;
   assign pll_clk_270 = pll_div_clk_270 ;



   logic qdr_clk_0, qdr_clk_90, qdr_clk_180, qdr_clk_270;

   assign qdr_clk_0   = pll_clk_0;
   assign qdr_clk_90  = pll_clk_90;
   assign qdr_clk_180 = pll_clk_180;
   assign qdr_clk_270 = pll_clk_270;

   // ------------------------------------------------------------------------
   // QDR PI
   // ------------------------------------------------------------------------
   logic pi_dqs_qdr_clk_0, pi_dqs_qdr_clk_b_0;
   logic pi_dq_qdr_clk_0,  pi_dq_qdr_clk_b_0;

   logic qdr_clk_0_dly0 , qdr_clk_180_dly0;
   logic qdr_clk_90_dly0, qdr_clk_270_dly0;

   // delay match DDR 4-phase clock divider
   ddr_wcm_div2_4ph_dlymatch u_qdr_div2_4ph_dlymatch0 (
      .i_clk_0    (qdr_clk_0),
      .i_clk_90   (qdr_clk_90),
      .i_clk_180  (qdr_clk_180),
      .i_clk_270  (qdr_clk_270),
      .i_div_byp  (ddr_div_byp),
      .o_clk_0    (qdr_clk_0_dly0),
      .o_clk_90   (qdr_clk_90_dly0),
      .o_clk_180  (qdr_clk_180_dly0),
      .o_clk_270  (qdr_clk_270_dly0)
   );

    ddr_pi_wrapper #(
      .PWIDTH     (P0WIDTH)
   ) u_dqs_qdr_pi_0 (
      .i_clk0     (qdr_clk_0_dly0),
      .i_clk90    (qdr_clk_90_dly0),
      .i_clk180   (qdr_clk_180_dly0),
      .i_clk270   (qdr_clk_270_dly0),
      .i_pi_cfg   (i_dqs_qdr_pi_0_cfg),
      .o_clk      (pi_dqs_qdr_clk_0),
      .o_clk_b    (pi_dqs_qdr_clk_b_0)
   );

   ddr_pi_wrapper #(
      .PWIDTH     (P0WIDTH)
   ) u_dq_qdr_pi_0 (
      .i_clk0     (qdr_clk_0_dly0),
      .i_clk90    (qdr_clk_90_dly0),
      .i_clk180   (qdr_clk_180_dly0),
      .i_clk270   (qdr_clk_270_dly0),
      .i_pi_cfg   (i_dq_qdr_pi_0_cfg),
      .o_clk      (pi_dq_qdr_clk_0),
      .o_clk_b    (pi_dq_qdr_clk_b_0)
   );

   logic qdr_mode;
   logic qdr_mode_int;
   // High frequency clock is required in QDR 2to1 mux mode, otherwise use DDR
   // clock with 4to1 mux and gate this clock
   ddr_wcm_or u_qdr_mode_or1 (.o_z(qdr_mode_int), .i_a(i_tgb_mode[`DGB_8TO1_HF_IDX]), .i_b(i_tgb_mode[`DGB_8TO1_LF_IDX]));
   ddr_wcm_or u_qdr_mode_or2 (.o_z(qdr_mode),     .i_a(qdr_mode_int),                              .i_b(i_tgb_mode[`DGB_4TO1_HF_IDX]));

   // Reset low CGCs for non-QDR modes to bypass the QDR mux
   logic dqs_qdr_clk_0_cgc, dqs_qdr_clk_180_cgc;
   logic dq_qdr_clk_0_cgc,  dq_qdr_clk_180_cgc;
   logic dqs_qdr_cgc_en,    dqs_qdr_cgc_en_sync ;
   logic dq_qdr_cgc_en,     dq_qdr_cgc_en_sync ;
   logic dqs_qdr_clk_0,     dqs_qdr_clk_180;
   logic dq_qdr_clk_0,      dq_qdr_clk_180;

   ddr_wcm_and u_dqs_qdr_cgc_en (.o_z(dqs_qdr_cgc_en), .i_a(qdr_mode), .i_b(i_dqs_dfi_wrtraffic)) ;
   ddr_wcm_and u_dq_qdr_cgc_en  (.o_z(dq_qdr_cgc_en ), .i_a(qdr_mode), .i_b(i_dq_dfi_wrtraffic ));

   ddr_wcm_demet u_qdr_demet_dqs_0 (.i_clk(pi_dqs_qdr_clk_0), .i_clk_b(pi_dqs_qdr_clk_b_0), .i_d(dqs_qdr_cgc_en), .o_q(dqs_qdr_cgc_en_sync));
   ddr_wcm_demet u_qdr_demet_dq_0  (.i_clk(pi_dq_qdr_clk_0 ), .i_clk_b(pi_dq_qdr_clk_b_0 ), .i_d(dq_qdr_cgc_en ), .o_q(dq_qdr_cgc_en_sync ));

   ddr_wcm_cgc_rl_2ph u_dqs_qdr_cgc_2ph_0 (
      .i_clk      (pi_dqs_qdr_clk_0),
      .i_clk_b    (pi_dqs_qdr_clk_b_0),
      .i_en       (dqs_qdr_cgc_en_sync),
      .o_clk      (dqs_qdr_clk_0),
      .o_clk_b    (dqs_qdr_clk_180)
   );

   ddr_wcm_cgc_rl_2ph u_dq_qdr_cgc_2ph_0 (
      .i_clk      (pi_dq_qdr_clk_0),
      .i_clk_b    (pi_dq_qdr_clk_b_0),
      .i_en       (dq_qdr_cgc_en_sync),
      .o_clk      (dq_qdr_clk_0),
      .o_clk_b    (dq_qdr_clk_180)
   );

  `ifdef DDR_ECO_CM_TSTCLK_DRVR_UPSIZE
   ddr_wcm_bufx8 u_dqs_qdr_tstclk_buf0  (.i_a(pi_dqs_qdr_clk_0),.o_z(o_tst_clk[0]));
   ddr_wcm_bufx8 u_dqs_qdr_tstclk_buf1  (.i_a(dqs_qdr_clk_0),   .o_z(o_tst_clk[1]));
  `else
   ddr_wcm_buf   u_dqs_qdr_tstclk_buf0  (.i_a(pi_dqs_qdr_clk_0),.o_z(o_tst_clk[0]));
   ddr_wcm_buf   u_dqs_qdr_tstclk_buf1  (.i_a(dqs_qdr_clk_0),   .o_z(o_tst_clk[1]));
  `endif //DDR_ECO_CM_TSTCLK_DRVR_UPSIZE

   ddr_wcm_bufx8 u_dqs_qdr_clk_0_buf   (.i_a(dqs_qdr_clk_0),   .o_z(o_dqs_qdr_clk_0));
   ddr_wcm_bufx8 u_dqs_qdr_clk_180_buf (.i_a(dqs_qdr_clk_180), .o_z(o_dqs_qdr_clk_180));
   ddr_wcm_bufx8 u_dq_qdr_clk_0_buf    (.i_a(dq_qdr_clk_0),    .o_z(o_dq_qdr_clk_0));
   ddr_wcm_bufx8 u_dq_qdr_clk_180_buf  (.i_a(dq_qdr_clk_180),  .o_z(o_dq_qdr_clk_180));


   // ------------------------------------------------------------------------
   // DDR DIV
   // ------------------------------------------------------------------------

   logic ddr_clk_0, ddr_clk_90, ddr_clk_180, ddr_clk_270;
   logic ddr_div_en;

   // If the ODR clock is enabled or the QDR clock is in high freq mode,
   // divide the DDR clock, otherwise the QDR clock will be the 4ph DDR clock
   // Enable divider in CK 1:2 or 1:4 mode.
   logic ddr_div_en_int0 ;
   logic ddr_div_en_int1 ;
   logic ddr_div_en_int2 ;
   logic ddr_div_en_int3 ;

   ddr_wcm_or u_ddr_div_en0  (.o_z(ddr_div_en_int0), .i_a(i_tgb_mode[`DGB_8TO1_HF_IDX]    ), .i_b(i_tgb_mode[`DGB_8TO1_LF_IDX]));
   ddr_wcm_or u_ddr_div_en1  (.o_z(ddr_div_en_int1), .i_a(i_tgb_mode[`DGB_4TO1_HF_IDX]    ), .i_b(ddr_div_en_int0));
   ddr_wcm_or u_ddr_div_en2  (.o_z(ddr_div_en_int2), .i_a(i_ck2wck_ratio[`CK2WCK_1TO2_IDX]), .i_b(ddr_div_en_int1));
   ddr_wcm_or u_ddr_div_en3  (.o_z(ddr_div_en_int3), .i_a(i_ck2wck_ratio[`CK2WCK_1TO4_IDX]), .i_b(ddr_div_en_int2));
   ddr_wcm_and u_ddr_div_en4 (.o_z(ddr_div_en),      .i_a(ddr_div_en_int3),  .i_b(i_csp_div_rst_n)) ;

   // Bypass the clock divider if no division is required
   ddr_wcm_inv u_ddr_div_byp (.o_z(ddr_div_byp), .i_a(ddr_div_en_int3));

   // 4-phase clock divider
   ddr_wcm_div2_4ph u_ddr_div2_4ph (
      .i_clk_0    (qdr_clk_0),
      .i_clk_90   (qdr_clk_90),
      .i_clk_180  (qdr_clk_180),
      .i_clk_270  (qdr_clk_270),
      .i_div_en   (ddr_div_en),
      .i_div_byp  (ddr_div_byp),
      .o_clk_0    (ddr_clk_0),
      .o_clk_90   (ddr_clk_90),
      .o_clk_180  (ddr_clk_180),
      .o_clk_270  (ddr_clk_270)
   );



   // ------------------------------------------------------------------------
   // DDR PI
   // ------------------------------------------------------------------------

   logic pi_dqs_ddr_clk_0, pi_dqs_ddr_clk_b_0;
   logic pi_dq_ddr_clk_0, pi_dq_ddr_clk_b_0;

   ddr_pi_wrapper #(
      .PWIDTH     (P0WIDTH)
   ) u_dqs_ddr_pi_0 (
      .i_clk0     (ddr_clk_0),
      .i_clk90    (ddr_clk_90),
      .i_clk180   (ddr_clk_180),
      .i_clk270   (ddr_clk_270),
      .i_pi_cfg   (i_dqs_ddr_pi_0_cfg),
      .o_clk      (pi_dqs_ddr_clk_0),
      .o_clk_b    (pi_dqs_ddr_clk_b_0)
   );

   ddr_pi_wrapper #(
      .PWIDTH     (P0WIDTH)
   ) u_dq_ddr_pi_0 (
      .i_clk0     (ddr_clk_0),
      .i_clk90    (ddr_clk_90),
      .i_clk180   (ddr_clk_180),
      .i_clk270   (ddr_clk_270),
      .i_pi_cfg   (i_dq_ddr_pi_0_cfg),
      .o_clk      (pi_dq_ddr_clk_0),
      .o_clk_b    (pi_dq_ddr_clk_b_0)
   );

   logic dqs_ddr_cgc_en_sync;
   logic dq_ddr_cgc_en_sync;
   logic dqs_ddr_clk_0,     dqs_ddr_clk_180;
   logic dq_ddr_clk_0,      dq_ddr_clk_180;

   ddr_wcm_demet u_dqs_ddr_demet_0 (.i_clk(pi_dqs_ddr_clk_0), .i_clk_b(pi_dqs_ddr_clk_b_0), .i_d(i_dqs_dfi_wrtraffic), .o_q(dqs_ddr_cgc_en_sync));
   ddr_wcm_demet u_dq_ddr_demet_0  (.i_clk(pi_dq_ddr_clk_0 ), .i_clk_b(pi_dq_ddr_clk_b_0 ), .i_d(i_dq_dfi_wrtraffic ), .o_q(dq_ddr_cgc_en_sync ));

   ddr_wcm_cgc_rl_2ph u_dqs_ddr_cgc_2ph_0 (
      .i_clk      (pi_dqs_ddr_clk_0 ),
      .i_clk_b    (pi_dqs_ddr_clk_b_0),
      .i_en       (dqs_ddr_cgc_en_sync),
      .o_clk      (dqs_ddr_clk_0),
      .o_clk_b    (dqs_ddr_clk_180)
   );

   ddr_wcm_cgc_rl_2ph u_dq_ddr_cgc_2ph_0 (
      .i_clk      (pi_dq_ddr_clk_0 ),
      .i_clk_b    (pi_dq_ddr_clk_b_0),
      .i_en       (dq_ddr_cgc_en_sync),
      .o_clk      (dq_ddr_clk_0),
      .o_clk_b    (dq_ddr_clk_180)
   );

   ddr_wcm_bufx8 u_dqs_ddr_clk_0_buf   (.i_a(dqs_ddr_clk_0),   .o_z(o_dqs_ddr_clk_0));
   ddr_wcm_bufx8 u_dqs_ddr_clk_180_buf (.i_a(dqs_ddr_clk_180), .o_z(o_dqs_ddr_clk_180));
   ddr_wcm_bufx8 u_dq_ddr_clk_0_buf    (.i_a(dq_ddr_clk_0),    .o_z(o_dq_ddr_clk_0));
   ddr_wcm_bufx8 u_dq_ddr_clk_180_buf  (.i_a(dq_ddr_clk_180),  .o_z(o_dq_ddr_clk_180));


   // ------------------------------------------------------------------------
   // SDR RT PI
   // ------------------------------------------------------------------------

   logic sdr_clk_0, sdr_clk_90, sdr_clk_180, sdr_clk_270;

   assign sdr_clk_0   = ddr_clk_0;
   assign sdr_clk_90  = ddr_clk_90;
   assign sdr_clk_180 = ddr_clk_180;
   assign sdr_clk_270 = ddr_clk_270;

   // SDR ReTimer PI
   logic pi_dqs_rt_clk, pi_dqs_rt_clk_b;
   logic pi_dq_rt_clk, pi_dq_rt_clk_b;

   ddr_pi_wrapper #(
      .PWIDTH     (P0WIDTH)
   ) u_dqs_rt_pi (
      .i_clk0     (sdr_clk_0),
      .i_clk90    (sdr_clk_90),
      .i_clk180   (sdr_clk_180),
      .i_clk270   (sdr_clk_270),
      .i_pi_cfg   (i_dqs_sdr_rt_pi_cfg),
      .o_clk      (pi_dqs_rt_clk),
      .o_clk_b    (pi_dqs_rt_clk_b)
   );

   ddr_pi_wrapper #(
      .PWIDTH     (P0WIDTH)
   ) u_dq_rt_pi (
      .i_clk0     (sdr_clk_0),
      .i_clk90    (sdr_clk_90),
      .i_clk180   (sdr_clk_180),
      .i_clk270   (sdr_clk_270),
      .i_pi_cfg   (i_dq_sdr_rt_pi_cfg),
      .o_clk      (pi_dq_rt_clk),
      .o_clk_b    (pi_dq_rt_clk_b)
   );

   logic dqs_sdr_rt_cgc_en_sync;
   logic dq_sdr_rt_cgc_en_sync;
   logic dq_sdr_rt_clk,   dq_sdr_rt_clk_b ;
   logic dqs_sdr_rt_clk,  dqs_sdr_rt_clk_b ;

   ddr_wcm_demet u_dqs_sdr_demet_0 (.i_clk(pi_dqs_rt_clk), .i_clk_b(pi_dqs_rt_clk_b), .i_d(i_dqs_dfi_wrtraffic), .o_q(dqs_sdr_rt_cgc_en_sync));
   ddr_wcm_demet u_dq_sdr_demet_0  (.i_clk(pi_dq_rt_clk ), .i_clk_b(pi_dq_rt_clk_b ), .i_d(i_dq_dfi_wrtraffic ), .o_q(dq_sdr_rt_cgc_en_sync ));

   ddr_wcm_cgc_rl_2ph u_dqs_sdr_rt_cgc_2ph (.i_clk(pi_dqs_rt_clk), .i_clk_b(pi_dqs_rt_clk_b), .i_en(dqs_sdr_rt_cgc_en_sync), .o_clk(dqs_sdr_rt_clk), .o_clk_b(dqs_sdr_rt_clk_b) );
   ddr_wcm_cgc_rl_2ph u_dq_sdr_rt_cgc_2ph  (.i_clk(pi_dq_rt_clk),  .i_clk_b(pi_dq_rt_clk_b),  .i_en(dq_sdr_rt_cgc_en_sync),  .o_clk(dq_sdr_rt_clk),  .o_clk_b(dq_sdr_rt_clk_b) );

   ddr_wcm_bufx8 u_dq_sdr_rt_clk_buf    (.i_a(dq_sdr_rt_clk),    .o_z(o_dq_sdr_rt_clk));
   ddr_wcm_bufx8 u_dq_sdr_rt_clk_b_buf  (.i_a(dq_sdr_rt_clk_b),  .o_z(o_dq_sdr_rt_clk_b));
   ddr_wcm_bufx8 u_dqs_sdr_rt_clk_buf   (.i_a(dqs_sdr_rt_clk),   .o_z(o_dqs_sdr_rt_clk));
   ddr_wcm_bufx8 u_dqs_sdr_rt_clk_b_buf (.i_a(dqs_sdr_rt_clk_b), .o_z(o_dqs_sdr_rt_clk_b));

   // ------------------------------------------------------------------------
   // SDR Clock and SDR DIV2 Clock PI Match
   // ------------------------------------------------------------------------

   // PI Matching cell to match PI Tmin.
   logic pi_sdr_clk, pi_sdr_clk_b ;
   logic pi_sdr_clk_int, pi_sdr_clk_b_int ;
   `ifdef DDR_PI_MATCH_EN
   ddr_pi_match_wrapper #(
      .PWIDTH     (P1WIDTH)
   ) u_sdr_pi_match (
      .i_clk0     (sdr_clk_0),
      .i_clk180   (sdr_clk_180),
      .i_pi_cfg   (i_sdr_pi_cfg),
      .o_clk      (pi_sdr_clk_int),
      .o_clk_b    (pi_sdr_clk_b_int)
   );
   `else
     assign pi_sdr_clk_int   = sdr_clk_0 ;
     assign pi_sdr_clk_b_int = sdr_clk_180 ;
   `endif

   //Matching Scan Mux
   logic tilo, scan_pi_sdr_clk_n,scan_pi_sdr_clk_b_n  ;
   ddr_wcm_tielo  u_tielo                (.o_z(tielo));
   ddr_wcm_nmux   u_match_sdr_scan_clk_mux0    (.i_a(pi_sdr_clk_int),   .i_b(tielo), .i_sel(tielo), .o_z_b(scan_pi_sdr_clk_n));
   ddr_wcm_nmux   u_match_sdr_scan_clkb_mux0   (.i_a(pi_sdr_clk_b_int), .i_b(tielo), .i_sel(tielo), .o_z_b(scan_pi_sdr_clk_b_n));
   ddr_wcm_inv    u_sdr_clk_0_inv              (.i_a(scan_pi_sdr_clk_n),   .o_z(pi_sdr_clk));
   ddr_wcm_inv    u_sdr_clk_1_inv              (.i_a(scan_pi_sdr_clk_b_n), .o_z(pi_sdr_clk_b));

   logic sdr_cgc_en;
   //IFR_FIXME: split dq vs dqs cgc for power.
   ddr_wcm_or u_sdr_cgc_en (.o_z(sdr_cgc_en), .i_a(i_dqs_dfi_wrtraffic), .i_b(i_dq_dfi_wrtraffic)) ;

   logic sdr_cgc_en_sync;
   logic sdr_clk,  sdr_clk_b ;

   ddr_wcm_demet u_sdr_demet_1     (.i_clk(pi_sdr_clk),     .i_clk_b(pi_sdr_clk_b),     .i_d(sdr_cgc_en),          .o_q(sdr_cgc_en_sync));

   ddr_wcm_cgc_rl_2ph u_sdr_cgc_2ph        (.i_clk(pi_sdr_clk),     .i_clk_b(pi_sdr_clk_b),     .i_en(sdr_cgc_en_sync),        .o_clk(sdr_clk),        .o_clk_b(sdr_clk_b) );

   ddr_wcm_invx8 u_sdr_clk_inv          (.i_a(sdr_clk),          .o_z(o_sdr_clk_b));
   ddr_wcm_invx8 u_sdr_clk_b_inv        (.i_a(sdr_clk_b),        .o_z(o_sdr_clk));

   // ------------------------------------------------------------------------
   // SDR DIV2 GB Clock
   // ------------------------------------------------------------------------

   logic sdr_div2_clk,   sdr_div2_clk_b;
   logic sdr_div2_clk_g, sdr_div2_clk_b_g;
   logic sdr_div_en, sdr_div_byp;

   ddr_wcm_and u_sdr_div_en  (.o_z(sdr_div_en), .i_a(i_wgb_mode[`WGB_8TO4_IDX] ), .i_b(i_csp_div_rst_n));
   ddr_wcm_inv u_sdr_div_byp (.o_z(sdr_div_byp), .i_a(i_wgb_mode[`WGB_8TO4_IDX]));
   ddr_wcm_div2_2ph   u_sdr_clk_div (
      .i_clk_0    (pi_sdr_clk),
      .i_clk_180  (pi_sdr_clk_b),
      .i_div_en   (sdr_div_en),
      .i_div_byp  (sdr_div_byp),
      .o_clk_0    (sdr_div2_clk),
      .o_clk_180  (sdr_div2_clk_b)
   );

   logic sdr_div2_cgc_en, sdr_div2_cgc_en_sync ;
   logic wr_traffic;

   //IFR_FIXME: split dq vs dqs cgc for power.i_dfi_wrtraffic ;

   ddr_wcm_or  u_traffic_or      (.o_z(wr_traffic), .i_a(i_dqs_dfi_wrtraffic), .i_b(i_dq_dfi_wrtraffic)) ;
   ddr_wcm_and u_sdr_div2_cgc_en (.o_z(sdr_div2_cgc_en), .i_a(i_wgb_mode[`WGB_8TO4_IDX]), .i_b(wr_traffic)) ;
   ddr_wcm_demet u_sdr_demet_3 (.i_clk(sdr_div2_clk), .i_clk_b(sdr_div2_clk_b), .i_d(sdr_div2_cgc_en), .o_q(sdr_div2_cgc_en_sync));

   ddr_wcm_cgc_rl_2ph u_sdr_div2_cgc_2ph (
      .i_clk      (sdr_div2_clk),
      .i_clk_b    (sdr_div2_clk_b),
      .i_en       (sdr_div2_cgc_en_sync),
      .o_clk      (sdr_div2_clk_g),
      .o_clk_b    (sdr_div2_clk_b_g)
   );

   ddr_wcm_bufx8 u_sdr_div2_clk_buf    (.i_a(sdr_div2_clk_g),    .o_z(o_sdr_div2_clk));
   ddr_wcm_bufx8 u_sdr_div2_clk_b_buf  (.i_a(sdr_div2_clk_b_g),  .o_z(o_sdr_div2_clk_b));

   // ------------------------------------------------------------------------
   // DFI Clocks
   // ------------------------------------------------------------------------
   logic dfi_sdrdiv_clk_0,   dfi_sdrdiv_clk_180;
   logic dfird_sdrdiv_clk_0, dfird_sdrdiv_clk_180;
   logic dfi_ddr_clk_0,      dfi_ddr_clk_180;
   logic dfird_div_0_en,     dfird_div_0_byp;
   logic dfird_div_1_en,     dfird_div_1_byp;
   logic dfiwr_div_0_en,     dfiwr_div_0_byp;
   logic dfiwr_div_1_en,     dfiwr_div_1_byp;
   logic dfi_ddrdiv_en,      dfi_ddrdiv_byp ;
   logic dfiwr_clk_1;
   logic dfiwr_clk_1_b;
   logic dfiwr_clk_2;

   //Divide if DP is in QDR mode.
   ddr_wcm_and u_dfi_ddrdiv_en  (.o_z(dfi_ddrdiv_en),  .i_a(qdr_mode),           .i_b(i_csp_div_rst_n));
   ddr_wcm_inv u_dfi_ddrdiv_byp (.o_z(dfi_ddrdiv_byp), .i_a(qdr_mode));

   ddr_wcm_div2_2ph u_dfiqdr_div (
      .i_clk_0    (i_pll_clk_0),
      .i_clk_180  (i_pll_clk_180),
      .i_div_en   (dfi_ddrdiv_en),
      .i_div_byp  (dfi_ddrdiv_byp),
      .o_clk_0    (dfi_ddr_clk_0),
      .o_clk_180  (dfi_ddr_clk_180)
   );

   // PI Matching cell to match PI Tmin.
   logic pi_dfi_ddr_clk_0 , pi_dfi_ddr_clk_180 ;
   `ifdef DDR_PI_MATCH_EN
   ddr_pi_match_wrapper #(
      .PWIDTH     (P1WIDTH)
   ) u_dfi_pi_match (
      .i_clk0     (dfi_ddr_clk_0),
      .i_clk180   (dfi_ddr_clk_180),
      .i_pi_cfg   (i_dfi_pi_cfg),
      .o_clk      (pi_dfi_ddr_clk_0),
      .o_clk_b    (pi_dfi_ddr_clk_180)
   );
   `else
     assign pi_dfi_ddr_clk_0   = dfi_ddr_clk_0 ;
     assign pi_dfi_ddr_clk_180 = dfi_ddr_clk_180 ;
   `endif

   //Divide if DP has GB enabled.
   ddr_wcm_div2_2ph u_dfisdr_div (
      .i_clk_0    (pi_dfi_ddr_clk_0),
      .i_clk_180  (pi_dfi_ddr_clk_180),
      .i_div_en   (sdr_div_en),
      .i_div_byp  (sdr_div_byp),
      .o_clk_0    (dfi_sdrdiv_clk_0),
      .o_clk_180  (dfi_sdrdiv_clk_180)
   );

   // Use buffer to isolate internal and external clocks.
   logic scan_phy_clk_n;
   ddr_wcm_nmux   u_phy_scan_mux      (.i_a(dfi_sdrdiv_clk_0), .i_b(i_scan_clk), .i_sel(i_scan_mode), .o_z_b(scan_phy_clk_n));
   ddr_wcm_invx8  u_phy_clk_inv   (.i_a(scan_phy_clk_n),    .o_z(o_phy_clk));

   logic scan_dfi_sdrdiv_clk_n;
   ddr_wcm_nmux   u_dfi_scan_mux       (.i_a(dfi_sdrdiv_clk_0), .i_b(i_scan_clk), .i_sel(i_scan_mode), .o_z_b(scan_dfi_sdrdiv_clk_n));
   ddr_wcm_inv    u_dfiwr_clk_1_inv    (.i_a(scan_dfi_sdrdiv_clk_n),    .o_z(o_dfiwr_clk_1));
   ddr_wcm_inv    u_dfiwr_clk_2_inv    (.i_a(scan_dfi_sdrdiv_clk_n),    .o_z(o_dfiwr_clk_2));

   // RD Clock gating and Dividers
   logic dfirdclk_en_extended;

   logic csp_div_rst;
   ddr_wcm_inv u_rst_inv (.i_a(i_csp_div_rst_n), .o_z(csp_div_rst));

   ddr_dp_pulse_extender #(
      .WIDTH        (DFIRDCLKEN_PEXTWIDTH)
   ) u_dfird_clk_en_pulse_ext (
      .i_clk        (dfi_sdrdiv_clk_0),
      .i_clk_b      (dfi_sdrdiv_clk_180),
      .i_rst        (csp_div_rst),
      .i_d          (i_dfirdclk_en),
      .i_num_pulses (i_dfirdclk_en_pulse_ext),
      .o_d          (dfirdclk_en_extended)
   );

   ddr_wcm_cgc_rl_2ph u_dfird_cgc_2ph (
      .i_clk        (dfi_sdrdiv_clk_0),
      .i_clk_b      (dfi_sdrdiv_clk_180),
      .i_en         (dfirdclk_en_extended),
      .o_clk        (dfird_sdrdiv_clk_0),
      .o_clk_b      (dfird_sdrdiv_clk_180)
   );

   logic scan_dfird_sdrdiv_clk_n;
   ddr_wcm_nmux   u_dfird_scan_mux     (.i_a(dfird_sdrdiv_clk_0), .i_b(i_scan_clk), .i_sel(i_scan_mode), .o_z_b(scan_dfird_sdrdiv_clk_n));
   ddr_wcm_inv    u_dfird_clk_1_inv    (.i_a(scan_dfird_sdrdiv_clk_n),    .o_z(o_dfird_clk_1));
   ddr_wcm_inv    u_dfird_clk_2_inv    (.i_a(scan_dfird_sdrdiv_clk_n),    .o_z(o_dfird_clk_2));

endmodule

module ddr_dp_pulse_extender # (
   parameter  WIDTH         = 4
) (
   input  logic             i_d,
   input  logic             i_clk,
   input  logic             i_clk_b,
   input  logic             i_rst,
   input  logic [WIDTH-1:0] i_num_pulses,
   output logic             o_d
);

`ifdef DDR_DP_PULSE_EXT_BEHAV
   logic [WIDTH-1:0] cnt_q, cnt_d;
   logic d_q, d_d ;
   logic d_asserted   ;

   assign cnt_d = d_asserted              ? i_num_pulses :
                  (~i_d && (cnt_q != '0)) ? cnt_q - 1'd1 :
                  i_num_pulses ;

   assign d_d = (i_d || ~i_d && (cnt_q == '0)) ? i_d : d_q;

   ddr_wcm_dff_r #(.DWIDTH(WIDTH)) u_cnt_dff  ( .i_clk(i_clk), .i_clk_b(i_clk_b), .i_rst(i_rst), .i_d(cnt_d), .o_q(cnt_q));
   ddr_wcm_dff_r #(.DWIDTH(1'b1))  u_data_dff ( .i_clk(i_clk), .i_clk_b(i_clk_b), .i_rst(i_rst), .i_d(d_d  ), .o_q(d_q  ));

   assign d_asserted = i_d & ~d_q  ;

   assign o_d = i_d | d_q ;
`else
   wire [3:0] cnt_q, cnt_d ;
   wire d_q, d_d, d_n, n_0, n_1, n_2, n_3, n_4, n_5, n_6;
   wire y0, y1, y2, y3, y4, y5, y6, y7, y8, y9 , y10 ;

  ddr_wcm_dff_r u_cnt_dff_0  ( .i_clk(i_clk), .i_clk_b(i_clk_b), .i_rst(i_rst), .i_d(cnt_d[0]), .o_q(cnt_q[0]));
  ddr_wcm_dff_r u_cnt_dff_1  ( .i_clk(i_clk), .i_clk_b(i_clk_b), .i_rst(i_rst), .i_d(cnt_d[1]), .o_q(cnt_q[1]));
  ddr_wcm_dff_r u_cnt_dff_2  ( .i_clk(i_clk), .i_clk_b(i_clk_b), .i_rst(i_rst), .i_d(cnt_d[2]), .o_q(cnt_q[2]));
  ddr_wcm_dff_r u_cnt_dff_3  ( .i_clk(i_clk), .i_clk_b(i_clk_b), .i_rst(i_rst), .i_d(cnt_d[3]), .o_q(cnt_q[3]));

  ddr_wcm_dff_r u_data_dff   ( .i_clk(i_clk), .i_clk_b(i_clk_b), .i_rst(i_rst), .i_d(d_d), .o_q(d_q));

  ddr_wcm_or  u_or_1         (.i_a(d_q), .i_b(i_d), .o_z(o_d));

  //AO21_X0P7N_A7P5PP84TH_C18 g336__8428(.A0 (n_3), .A1 (d_q), .B0 (i_d), Y (d_d)); -> AND+OR
  ddr_wcm_nand u_nand_1      (.i_a(n_3), .i_b(d_q), .o_z(y0));
  ddr_wcm_inv  u_inv_0       (.i_a(i_d), .o_z(d_n));
  ddr_wcm_nand u_nand_2      (.i_a(d_n), .i_b(y0), .o_z(d_d));

  //OAI2BB1_X0P7N_A7P5PP84TH_C18 g332__2398(.A0N (n_4), .A1N(i_num_pulses[3]), .B0 (n_6), .Y (cnt_d[3])); OR with inv inputs + NAND
  ddr_wcm_nand u_nand_3      (.i_a(n_4), .i_b(i_num_pulses[3]), .o_z(y1));
  ddr_wcm_nand u_nand_4      (.i_a(y1),  .i_b(n_6),             .o_z(cnt_d[3]));

  //OAI2BB1_X0P7N_A7P5PP84TH_C18 g333__5107(.A0N (n_4), .A1N(i_num_pulses[1]), .B0 (n_5), .Y (cnt_d[1])); OR with inv inputs + NAND
  ddr_wcm_nand u_nand_5      (.i_a(n_4), .i_b(i_num_pulses[1]), .o_z(y2));
  ddr_wcm_nand u_nand_6      (.i_a(y2),  .i_b(n_5),             .o_z(cnt_d[1]));

  //OAI22BB_X0P7N_A7P5PP84TH_C18 g334__6260(.A0 (n_4), .A1 (cnt_q[0]), .B0N (n_4), .B1N (i_num_pulses[0]), .Y (cnt_d[0])); OR on A* + NAND on B* + NAND
  ddr_wcm_or   u_or_0        (.i_a(n_4), .i_b(cnt_q[0]),        .o_z(y3));
  ddr_wcm_nand u_nand_7      (.i_a(n_4), .i_b(i_num_pulses[0]), .o_z(y4));
  ddr_wcm_nand u_nand_8      (.i_a(y3),  .i_b(y4),               .o_z(cnt_d[0]));

  //MXT2_X0P7N_A7P5PP84TH_C18 g335__4319(.A (n_2), .B (i_num_pulses[2]), .S0 (n_4), .Y (cnt_d[2]));
  ddr_wcm_mux u_mux_1        (.i_a(n_2), .i_b(i_num_pulses[2]), .i_sel(n_4), .o_z(cnt_d[2]));

  //NAND3_X0P7R_A7P5PP84TH_C18 g337__5526(.A (n_3), .B (n_1), .C(cnt_q[3]), .Y (n_6));
  ddr_wcm_nand3 u_nand3_1    (.i_a(n_3), .i_b(n_1), .i_c(cnt_q[3]), .o_z(n_6));

  //AO21A1AI2_X0P7N_A7P5PP84TH_C18 g338__6783(.A0 (cnt_q[0]), .A1(cnt_q[1]), .B0 (n_0), .C0 (n_3), .Y (n_5));
  ddr_wcm_nand u_nand_9      (.i_a(cnt_q[0]), .i_b(cnt_q[1]), .o_z(y5));
  ddr_wcm_inv  u_inv_1       (.i_a(n_0),      .o_z(y6));
  ddr_wcm_nand u_nand_10     (.i_a(y5),       .i_b(y6),       .o_z(y7));
  ddr_wcm_nand u_nand_11     (.i_a(y7),       .i_b(n_3),      .o_z(n_5));

  //INV_X1P5N_A7P5PP84TH_C18 g339(.A (n_4), .Y (n_3));
  ddr_wcm_inv  u_inv_2       (.i_a (n_4), .o_z(n_3));

  //OAI21B_X0P7N_A7P5PP84TH_C18 g340__3680 (.A0 (n_1), .A1 (cnt_q[3]),  .B0N (i_d), .Y (n_4));
  ddr_wcm_nor  u_nor_2        (.i_a(n_1), .i_b(cnt_q[3]), .o_z(y8));
  ddr_wcm_or   u_or_2         (.i_a(i_d), .i_b(y8),       .o_z(n_4));

  //OAI2XB1_X0P7N_A7P5PP84TH_C18 g341__1617(.A0 (n_0), .A1N (cnt_q[2]),.B0 (n_1), .Y (n_2));
  ddr_wcm_inv  u_inv_3       (.i_a (cnt_q[2]), .o_z(y9));
  ddr_wcm_or   u_or_3        (.i_a(n_0), .i_b(y9),     .o_z(y10));
  ddr_wcm_nand u_nand_12     (.i_a(y10), .i_b(n_1),    .o_z(n_2));

  //NAND2XB_X0P7N_A7P5PP84TH_C18 g342__2802(.A (n_0), .BN (cnt_q[2]), .Y(n_1));
  ddr_wcm_nand u_nand_13     (.i_a(y9), .i_b(n_0),    .o_z(n_1));

  //NOR2_X0P7N_A7P5PP84TH_C18 g343__1705(.A (cnt_q[0]), .B (cnt_q[1]), .Y(n_0));
  ddr_wcm_nor  u_nor_3        (.i_a(cnt_q[0]), .i_b(cnt_q[1]),     .o_z(n_0));

`endif

endmodule
