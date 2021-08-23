
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
`include "ddr_cke_drvr_lpbk_wrapper_define.vh"
`include "ddr_cke_drvr_lpbk_wrapper_cmn_define.vh"

import ddr_global_pkg::*;

module ddr_cke_drvr_lpbk_wrapper #(
   parameter P0WIDTH = 6,
   parameter P1WIDTH = 19
)
(
   input  logic [P0WIDTH-1:0] i_drvr_cfg,
   input  logic [P1WIDTH-1:0] i_drvr_cmn_cfg,
   input  logic i_freeze_n_hv,
   input  logic i_freeze_n,
   input  logic i_hiz_n,
   input  logic i_d_n,
   input  logic i_oe,
   input  logic i_bs_mode_n,
   input  logic i_bs_oe,
   input  logic i_bs_ie,
   input  logic i_d_bs,
   inout  wire  pad,
   output wire  o_d_lpbk
);

`ifndef WLOGIC_NO_PG
   wire vdda, vdda1p2, vss;
   assign vdda = 1'b1;
   assign vdda1p2 = 1'b1;
   assign vss  = 1'b0;
`endif

   logic lpbk_ena;
`ifndef DDR_IO_WRAPPER_BEHAV
   ddr_wcm_mux #(.DWIDTH(1)) u_mux_lpbk_ena (.i_sel(i_bs_mode_n), .i_a(i_bs_ie), .i_b(i_drvr_cmn_cfg[`DDR_ANA_CKE_DRVR_LPBK_LPBK_EN_FIELD]), .o_z(lpbk_ena));
`else
   assign lpbk_ena =  i_bs_mode_n ? i_drvr_cmn_cfg[`DDR_ANA_CKE_DRVR_LPBK_LPBK_EN_FIELD] : i_bs_ie;
`endif

   logic bs_ena;
`ifndef DDR_IO_WRAPPER_BEHAV
   ddr_wcm_mux #(.DWIDTH(1)) u_mux_bs_ena (.i_sel(i_bs_mode_n), .i_a(i_bs_oe), .i_b(i_drvr_cmn_cfg[`DDR_ANA_CKE_DRVR_LPBK_BS_EN_FIELD]), .o_z(bs_ena));
`else
   assign bs_ena   =  i_bs_mode_n ? i_drvr_cmn_cfg[`DDR_ANA_CKE_DRVR_LPBK_BS_EN_FIELD]   : i_bs_oe;
`endif

   // See wphy_lp4x5_dq_drv.doc, section 1.7.1 for details on driver configuration
   // for freeze and hiz ...
   //   if (freeze)   {d_drv_impd, d_ovrd, d_ovrd_val} = {2’h1, 3’h1, 1’b0}
   //   else if (hiz) {d_drv_impd, d_ovrd, d_ovrd_val} = {2’h0, 3’h1, 1’b0}

   logic [2:0] ovrd;
   // See wphy_lp4x5_dq_drv.doc, section 1.7.1 for details on driver configuration
`ifndef DDR_IO_WRAPPER_BEHAV
   logic [2:0] lpbk_ovrd_sel_oe;
   logic [2:0] oe_bus_b;
   logic [2:0] ovrd_mux_1;
   logic [2:0] ovrd_mux_2;
   logic [2:0] ovrd_mux_3;

   ddr_wcm_inv u_inv_oe_int_0  ( .i_a(i_oe), .o_z(oe_bus_b[0]));
   ddr_wcm_inv u_inv_oe_int_1  ( .i_a(i_oe), .o_z(oe_bus_b[1]));
   ddr_wcm_inv u_inv_oe_int_2  ( .i_a(i_oe), .o_z(oe_bus_b[2]));

  //TODO - add tiehi/lo
   ddr_wcm_and #(.DWIDTH(3)) u_and_ovrd_oe ( .i_a(oe_bus_b), .i_b(i_drvr_cfg[`DDR_ANA_CKE_DRVR_LPBK_OVRD_SEL_FIELD]), .o_z(lpbk_ovrd_sel_oe));
   ddr_wcm_mux #(.DWIDTH(3)) u_mux_ovrd_1 (.i_sel(i_drvr_cfg[`DDR_ANA_CKE_DRVR_LPBK_SW_OVR_FIELD]), .i_a(lpbk_ovrd_sel_oe), .i_b(i_drvr_cfg[`DDR_ANA_CKE_DRVR_LPBK_OVRD_SEL_FIELD]), .o_z(ovrd_mux_1));
   ddr_wcm_mux #(.DWIDTH(3)) u_mux_ovrd_2 (.i_sel(i_bs_mode_n), .i_a(3'h1), .i_b(ovrd_mux_1), .o_z(ovrd_mux_2));
   ddr_wcm_mux #(.DWIDTH(3)) u_mux_ovrd_3 (.i_sel(i_hiz_n), .i_a(3'h1), .i_b(ovrd_mux_2), .o_z(ovrd_mux_3));
   ddr_wcm_mux #(.DWIDTH(3)) u_mux_ovrd_4 (.i_sel(i_freeze_n), .i_a(3'h1), .i_b(ovrd_mux_3), .o_z(ovrd));
`else
   assign ovrd = i_freeze_n ? i_hiz_n ? i_bs_mode_n ?
                    i_drvr_cfg[`DDR_ANA_CKE_DRVR_LPBK_SW_OVR_FIELD] ?
                    i_drvr_cfg[`DDR_ANA_CKE_DRVR_LPBK_OVRD_SEL_FIELD] :
                    {3{~i_oe}} & i_drvr_cfg[`DDR_ANA_CKE_DRVR_LPBK_OVRD_SEL_FIELD]
                 : 3'h1 : 3'h1 : 3'h1;
`endif

   /*
   logic [2:0] impd;
   assign impd = i_freeze_n ? i_hiz_n ? i_bs_mode_n ?
                    i_oe | i_drvr_cfg[`DDR_ANA_CKE_DRVR_LPBK_SW_OVR_FIELD] ?
                    i_drvr_cfg[`DDR_ANA_CKE_DRVR_LPBK_TX_IMPD_FIELD]:
                    i_drvr_cfg[`DDR_ANA_CKE_DRVR_LPBK_RX_IMPD_FIELD]
                 : 3'h0 : 3'h0 : 3'h1;
   */

   logic ovrd_val;
`ifndef DDR_IO_WRAPPER_BEHAV
   logic  val_mux_1;
   logic  val_mux_2;
   logic  val_mux_3;

  //TODO - add tiehi/lo
   ddr_wcm_mux  u_mux_val_1 (.i_sel(i_bs_mode_n), .i_a(1'h0), .i_b(i_drvr_cfg[`DDR_ANA_CKE_DRVR_LPBK_OVRD_VAL_FIELD]), .o_z(val_mux_1));
   ddr_wcm_mux  u_mux_val_2 (.i_sel(i_hiz_n), .i_a(1'h0), .i_b(val_mux_1), .o_z(val_mux_2));
   ddr_wcm_mux  u_mux_val_3 (.i_sel(i_freeze_n), .i_a(1'h0), .i_b(val_mux_2), .o_z(ovrd_val));
`else
   assign ovrd_val = i_freeze_n ? i_hiz_n ? i_bs_mode_n ?
                    i_drvr_cfg[`DDR_ANA_CKE_DRVR_LPBK_OVRD_VAL_FIELD]
                 : 1'h0 : 1'h0 : 1'h0;
`endif

   wphy_lp4x5_cke_drvr_w_lpbk u_cke_drvr_w_lpbk (
      .pad_cke_out   (pad),
      //.d_in_t        (i_d),
      .d_in_c        (i_d_n),
      .d_bs_din      (i_d_bs),
      .d_bs_ena      (bs_ena),
      .d_lpbk_ena    (lpbk_ena),
      .freeze_n_hv   (i_freeze_n_hv),
      .d_lpbk_out    (o_d_lpbk),
      .d_ovrd        (ovrd),
      .d_ovrd_val    (ovrd_val)
`ifndef WLOGIC_NO_PG
      ,.vdda         (vdda),
      .vdda1p2       (vdda1p2),
      .vss           (vss)
`endif
   );

endmodule
