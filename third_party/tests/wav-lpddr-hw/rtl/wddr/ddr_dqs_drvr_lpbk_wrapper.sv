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
`include "ddr_dqs_drvr_lpbk_wrapper_define.vh"
`include "ddr_dqs_drvr_lpbk_wrapper_cmn_define.vh"

import ddr_global_pkg::*;

module ddr_dqs_drvr_lpbk_wrapper #(
   parameter P0WIDTH = 6,
   parameter P1WIDTH = 20
)(
   input  logic [P0WIDTH-1:0] i_drvr_cfg,
   input  logic [P1WIDTH-1:0] i_drvr_cmn_cfg,
   input  logic i_freeze_n,
   input  logic i_hiz_n,
   input  logic i_d_n,
   input  logic i_oe,
   input  logic i_ie,
   input  logic i_bs_mode_n,
   input  logic i_bs_oe,
   input  logic i_bs_ie,
   input  logic i_d_bs_t,
   input  logic i_d_bs_c,
   inout  wire  pad_t,
   inout  wire  pad_c,
   output wire  o_d_lpbk_t,
   output wire  o_d_lpbk_c,
   output wire  o_rx_in_t,
   output wire  o_rx_in_c
);

`ifndef WLOGIC_NO_PG
   wire vdda, vdd_aon, vddq, vss;
   assign vdda    = 1'b1;
   assign vdd_aon = 1'b1;
   assign vddq    = 1'b1;
   assign vss     = 1'b0;
`endif

   logic lpbk_ena;
`ifndef DDR_IO_WRAPPER_BEHAV
   ddr_wcm_mux #(.DWIDTH(1)) u_mux_lpbk_ena (.i_sel(i_bs_mode_n), .i_a(i_bs_ie), .i_b(i_drvr_cmn_cfg[`DDR_ANA_DQS_DRVR_LPBK_LPBK_EN_FIELD]), .o_z(lpbk_ena));
`else
   assign lpbk_ena =  i_bs_mode_n ? i_drvr_cmn_cfg[`DDR_ANA_DQS_DRVR_LPBK_LPBK_EN_FIELD] : i_bs_ie;
`endif

   logic bs_ena;
`ifndef DDR_IO_WRAPPER_BEHAV
   ddr_wcm_mux #(.DWIDTH(1)) u_mux_bs_ena (.i_sel(i_bs_mode_n), .i_a(i_bs_oe), .i_b(i_drvr_cmn_cfg[`DDR_ANA_DQS_DRVR_LPBK_BS_EN_FIELD]), .o_z(bs_ena));
`else
   assign bs_ena   =  i_bs_mode_n ? i_drvr_cmn_cfg[`DDR_ANA_DQS_DRVR_LPBK_BS_EN_FIELD]   : i_bs_oe;
`endif

   logic rx_unterm;
   // RX termination definition, see wphy_lp4x5_dqs_*_drv.doc, section 1.7.1 for details on driver configuration
`ifndef DDR_IO_WRAPPER_BEHAV
   logic [2:0] ovrd_sel;
   logic ovrd_sel_and, ovrd_sel_nor;
   logic [2:0] rx_impd;
   logic rx_impd_nor, rx_impd_or;
   logic rx_unterm_and1, rx_unterm_and2;
   logic ovrd_val_t_b;

   assign ovrd_sel = i_drvr_cfg[`DDR_ANA_DQS_DRVR_LPBK_OVRD_SEL_FIELD];
   assign rx_impd  = i_drvr_cfg[`DDR_ANA_DQS_DRVR_LPBK_RX_IMPD_FIELD];

   ddr_wcm_nor  u_nor_ovrd_sel      ( .i_a(ovrd_sel[1]), .i_b(ovrd_sel[2]),  .o_z(ovrd_sel_nor));
   ddr_wcm_and  u_and_ovrd_sel      ( .i_a(ovrd_sel[0]), .i_b(ovrd_sel_nor), .o_z(ovrd_sel_and));

   ddr_wcm_or   u_or_rx_impd        ( .i_a(rx_impd[0]), .i_b(rx_impd[1]),  .o_z(rx_impd_or));
   ddr_wcm_nor  u_nor_rx_impd       ( .i_a(rx_impd[2]), .i_b(rx_impd_or),  .o_z(rx_impd_nor));

//   ddr_wcm_inv  u_inv_ovrd_val_c    ( .i_a(i_drvr_cfg[`DDR_ANA_DQS_DRVR_LPBK_OVRD_VAL_C_FIELD]), .o_z(ovrd_val_c_b));
   ddr_wcm_inv  u_inv_ovrd_val_t    ( .i_a(i_drvr_cfg[`DDR_ANA_DQS_DRVR_LPBK_OVRD_VAL_T_FIELD]), .o_z(ovrd_val_t_b));

   ddr_wcm_and  u_and_rx_unterm_1   ( .i_a(ovrd_sel_and), .i_b(rx_impd_nor),  .o_z(rx_unterm_and1));
//   ddr_wcm_and  u_and_rx_unterm_2   ( .i_a(ovrd_val_c_b), .i_b(ovrd_val_t_b), .o_z(rx_unterm_and2));
   ddr_wcm_and  u_and_rx_unterm_2   ( .i_a(i_drvr_cfg[`DDR_ANA_DQS_DRVR_LPBK_OVRD_VAL_C_FIELD]), .i_b(ovrd_val_t_b), .o_z(rx_unterm_and2));
   ddr_wcm_and  u_and_rx_unterm_out ( .i_a(rx_unterm_and1), .i_b(rx_unterm_and2), .o_z(rx_unterm));
`else
   assign rx_unterm = (i_drvr_cfg[`DDR_ANA_DQS_DRVR_LPBK_OVRD_SEL_FIELD]    == 3'h1) &
                      (i_drvr_cfg[`DDR_ANA_DQS_DRVR_LPBK_RX_IMPD_FIELD]     == 3'h0) &
                      (i_drvr_cfg[`DDR_ANA_DQS_DRVR_LPBK_OVRD_VAL_C_FIELD]  == 1'h1) &
                      (i_drvr_cfg[`DDR_ANA_DQS_DRVR_LPBK_OVRD_VAL_T_FIELD]  == 1'h0);
`endif

   logic oe;
   // In RX unterminated mode, enable the OE when not reading in order drive the DQS
`ifndef DDR_IO_WRAPPER_BEHAV
   logic oe_b, ie_b, oe_nand1;
   ddr_wcm_inv    u_inv_oe_1  ( .i_a(i_oe), .o_z(oe_b));
   ddr_wcm_inv    u_inv_oe_2  ( .i_a(i_ie), .o_z(ie_b));
   ddr_wcm_nand   u_nand_oe_1 (.i_a(rx_unterm),.i_b(ie_b),.o_z(oe_nand1));
   ddr_wcm_nand   u_nand_oe_2 (.i_a(oe_b),.i_b(oe_nand1),.o_z(oe));
`else
   assign oe = i_oe | (rx_unterm & ~i_ie);
`endif
   // See wphy_lp4x5_dqs_*_drv.doc, section 1.7.1 for details on driver configuration
   // for freeze and hiz ...
   //   if (freeze)   {d_drv_impd, d_ovrd, d_ovrd_val} = {2’h1, 3’h1, 1’b0}
   //   else if (hiz) {d_drv_impd, d_ovrd, d_ovrd_val} = {2’h0, 3’h1, 1’b0}

   logic [2:0] ovrd;
   // See wphy_lp4x5_dqs_drv.doc, section 1.7.1 for details on driver configuration
`ifndef DDR_IO_WRAPPER_BEHAV
   logic [2:0] lpbk_ovrd_sel_oe;
   logic [2:0] oe_bus_b;
   logic [2:0] ovrd_mux_1;
   logic [2:0] ovrd_mux_2;
   logic [2:0] ovrd_mux_3;

   ddr_wcm_inv u_inv_oe_int_0  ( .i_a(oe), .o_z(oe_bus_b[0]));
   ddr_wcm_inv u_inv_oe_int_1  ( .i_a(oe), .o_z(oe_bus_b[1]));
   ddr_wcm_inv u_inv_oe_int_2  ( .i_a(oe), .o_z(oe_bus_b[2]));

  //TODO - add tiehi/lo
   ddr_wcm_and #(.DWIDTH(3)) u_and_ovrd_oe ( .i_a(oe_bus_b), .i_b(i_drvr_cfg[`DDR_ANA_DQS_DRVR_LPBK_OVRD_SEL_FIELD]), .o_z(lpbk_ovrd_sel_oe));
   ddr_wcm_mux #(.DWIDTH(3)) u_mux_ovrd_1 (.i_sel(i_drvr_cfg[`DDR_ANA_DQS_DRVR_LPBK_SW_OVR_FIELD]), .i_a(lpbk_ovrd_sel_oe), .i_b(i_drvr_cfg[`DDR_ANA_DQS_DRVR_LPBK_OVRD_SEL_FIELD]), .o_z(ovrd_mux_1));
   ddr_wcm_mux #(.DWIDTH(3)) u_mux_ovrd_2 (.i_sel(i_bs_mode_n), .i_a(3'h1), .i_b(ovrd_mux_1), .o_z(ovrd_mux_2));
   ddr_wcm_mux #(.DWIDTH(3)) u_mux_ovrd_3 (.i_sel(i_hiz_n), .i_a(3'h1), .i_b(ovrd_mux_2), .o_z(ovrd_mux_3));
   ddr_wcm_mux #(.DWIDTH(3)) u_mux_ovrd_4 (.i_sel(i_freeze_n), .i_a(3'h1), .i_b(ovrd_mux_3), .o_z(ovrd));
`else
   assign ovrd = i_freeze_n ? i_hiz_n ? i_bs_mode_n ?
                    i_drvr_cfg[`DDR_ANA_DQS_DRVR_LPBK_SW_OVR_FIELD]   ?
                    i_drvr_cfg[`DDR_ANA_DQS_DRVR_LPBK_OVRD_SEL_FIELD] :
                    {3{~oe}} & i_drvr_cfg[`DDR_ANA_DQS_DRVR_LPBK_OVRD_SEL_FIELD]
                 : 3'h1 : 3'h1 : 3'h1;
`endif

   logic [2:0] impd;
`ifndef DDR_IO_WRAPPER_BEHAV
   logic lpbk_sw_ovrd;
   logic [2:0] oe_bus;
   logic [2:0] impd_mux_1;
   logic [2:0] impd_mux_2;
   logic [2:0] impd_mux_3;

   //assign oe_bus[0] = oe;
   //assign oe_bus[1] = oe;
   //assign oe_bus[2] = oe;

  //TODO - add tiehi/lo
   ddr_wcm_or   u_or_sw_ovrd (.i_a(oe), .i_b(i_drvr_cfg[`DDR_ANA_DQS_DRVR_LPBK_SW_OVR_FIELD]), .o_z(lpbk_sw_ovrd));
   ddr_wcm_mux #(.DWIDTH(3)) u_mux_impd_1 (.i_sel(lpbk_sw_ovrd), .i_a(i_drvr_cfg[`DDR_ANA_DQS_DRVR_LPBK_RX_IMPD_FIELD]), .i_b(i_drvr_cfg[`DDR_ANA_DQS_DRVR_LPBK_TX_IMPD_FIELD]), .o_z(impd_mux_1));
   ddr_wcm_mux #(.DWIDTH(3)) u_mux_impd_2 (.i_sel(i_bs_mode_n), .i_a(3'h0), .i_b(impd_mux_1), .o_z(impd_mux_2));
   ddr_wcm_mux #(.DWIDTH(3)) u_mux_impd_3 (.i_sel(i_hiz_n), .i_a(3'h0), .i_b(impd_mux_2), .o_z(impd_mux_3));
   ddr_wcm_mux #(.DWIDTH(3)) u_mux_impd_4 (.i_sel(i_freeze_n), .i_a(3'h1), .i_b(impd_mux_3), .o_z(impd));
`else
   assign impd = i_freeze_n ? i_hiz_n ? i_bs_mode_n ?
                    oe | i_drvr_cfg[`DDR_ANA_DQS_DRVR_LPBK_SW_OVR_FIELD] ?
                    i_drvr_cfg[`DDR_ANA_DQS_DRVR_LPBK_TX_IMPD_FIELD] :
                    i_drvr_cfg[`DDR_ANA_DQS_DRVR_LPBK_RX_IMPD_FIELD]
                 : 3'h0 : 3'h0 : 3'h1;
`endif

   logic ovrd_val_c;
`ifndef DDR_IO_WRAPPER_BEHAV
   logic  val_c_mux_1;
   logic  val_c_mux_2;
   logic  val_c_mux_3;

  //TODO - add tiehi/lo
   ddr_wcm_mux  u_mux_val_c_1 (.i_sel(i_bs_mode_n), .i_a(1'h0), .i_b(i_drvr_cfg[`DDR_ANA_DQS_DRVR_LPBK_OVRD_VAL_C_FIELD]), .o_z(val_c_mux_1));
   ddr_wcm_mux  u_mux_val_c_2 (.i_sel(i_hiz_n), .i_a(1'h0), .i_b(val_c_mux_1), .o_z(val_c_mux_2));
   ddr_wcm_mux  u_mux_val_c_3 (.i_sel(i_freeze_n), .i_a(1'h0), .i_b(val_c_mux_2), .o_z(ovrd_val_c));
`else
   assign ovrd_val_c = i_freeze_n ? i_hiz_n ? i_bs_mode_n ?
                    i_drvr_cfg[`DDR_ANA_DQS_DRVR_LPBK_OVRD_VAL_C_FIELD]
                 : 1'h0 : 1'h0 : 1'h0;
`endif

   logic ovrd_val_t;
`ifndef DDR_IO_WRAPPER_BEHAV
   logic  val_t_mux_1;
   logic  val_t_mux_2;
   logic  val_t_mux_3;

  //TODO - add tiehi/lo
   ddr_wcm_mux  u_mux_val_t_1 (.i_sel(i_bs_mode_n), .i_a(1'h0), .i_b(i_drvr_cfg[`DDR_ANA_DQS_DRVR_LPBK_OVRD_VAL_T_FIELD]), .o_z(val_t_mux_1));
   ddr_wcm_mux  u_mux_val_t_2 (.i_sel(i_hiz_n), .i_a(1'h0), .i_b(val_t_mux_1), .o_z(val_t_mux_2));
   ddr_wcm_mux  u_mux_val_t_3 (.i_sel(i_freeze_n), .i_a(1'h0), .i_b(val_t_mux_2), .o_z(ovrd_val_t));
`else
   assign ovrd_val_t = i_freeze_n ? i_hiz_n ? i_bs_mode_n ?
                    i_drvr_cfg[`DDR_ANA_DQS_DRVR_LPBK_OVRD_VAL_T_FIELD]
                 : 1'h0 : 1'h0 : 1'h0;
`endif

   wphy_lp4x5_dqs_drvr_w_lpbk u_dqs_drvr_lpbk (
      .pad_c         (pad_c),
      .pad_t         (pad_t),
      //.d_in          (i_d),
      .d_in_c        (i_d_n),
      .d_ovrd        (ovrd),
      .d_ovrd_val_c  (ovrd_val_c),
      .d_ovrd_val_t  (ovrd_val_t),
      .d_drv_impd    (impd),
      .d_ncal        (i_drvr_cmn_cfg[`DDR_ANA_DQS_DRVR_LPBK_NCAL_FIELD]),
      .d_pcal        (i_drvr_cmn_cfg[`DDR_ANA_DQS_DRVR_LPBK_PCAL_FIELD]),
      .d_bs_din_c    (i_d_bs_c),
      .d_bs_din_t    (i_d_bs_t),
      .freeze_n      (i_freeze_n),
      .d_lpbk_ena    (lpbk_ena),
      .d_bs_ena      (bs_ena),
      .d_se_mode     (i_drvr_cmn_cfg[`DDR_ANA_DQS_DRVR_LPBK_SE_MODE_FIELD]),
      .lpbk_out_c    (o_d_lpbk_c),
      .lpbk_out_t    (o_d_lpbk_t),
      .dqs_rx_in_t   (o_rx_in_t),
      .dqs_rx_in_c   (o_rx_in_c)
`ifndef WLOGIC_NO_PG
      ,.vdda         (vdda),
      .vdd_aon       (vdd_aon),
      .vddq          (vddq),
      .vss           (vss)
`endif
   );

endmodule
