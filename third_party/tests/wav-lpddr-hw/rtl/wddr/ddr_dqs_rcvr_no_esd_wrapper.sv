
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
`include "ddr_dqs_rcvr_wrapper_define.vh"
`include "ddr_dqs_rcvr_wrapper_cmn_define.vh"

import ddr_global_pkg::*;

module ddr_dqs_rcvr_no_esd_wrapper #(
   parameter P0WIDTH = 16,
   parameter P1WIDTH = 26
)
(
   output logic o_dqs_c,
   output logic o_dqs_t,
   input logic pad_c,
   input logic pad_t,
   input logic i_ie,
   input logic i_re,
   input logic [P0WIDTH-1:0] i_rcvr_cfg,
   input logic [P1WIDTH-1:0] i_rcvr_cmn_cfg
);

`ifndef WLOGIC_NO_PG
   wire vdda, vddq, vss;
   assign vdda = 1'b1;
   assign vddq = 1'b1;
   assign vss  = 1'b0;
`endif

   logic ena;
`ifndef DDR_IO_WRAPPER_BEHAV
   logic ena_or_2;

   ddr_wcm_or   u_or_ena_2   ( .i_a(i_rcvr_cmn_cfg[`DDR_ANA_DQS_RCVR_EN_RANGE]), .i_b(i_ie), .o_z(ena_or_2));
   ddr_wcm_mux  u_mux_ena    ( .i_sel(i_rcvr_cmn_cfg[`DDR_ANA_DQS_RCVR_SW_OVR_RANGE]), .i_a(ena_or_2), .i_b(i_rcvr_cmn_cfg[`DDR_ANA_DQS_RCVR_EN_RANGE]), .o_z(ena));

`else
   assign ena = i_rcvr_cmn_cfg[`DDR_ANA_DQS_RCVR_SW_OVR_RANGE] ?
                i_rcvr_cmn_cfg[`DDR_ANA_DQS_RCVR_EN_RANGE]     :
                //i_re | i_ie | i_rcvr_cmn_cfg[`DDR_ANA_DQS_RCVR_EN_RANGE];
                i_ie | i_rcvr_cmn_cfg[`DDR_ANA_DQS_RCVR_EN_RANGE];
`endif

   wphy_lp4x5_dqs_rcvr_no_esd u_dqs_rcvr_no_esd (
      .d_dqs_out_c        (o_dqs_c),
      .d_dqs_out_t        (o_dqs_t),
      .d_cal_n_c          (i_rcvr_cmn_cfg[`DDR_ANA_DQS_RCVR_CAL_N_C_RANGE]),
      .d_cal_n_t          (i_rcvr_cmn_cfg[`DDR_ANA_DQS_RCVR_CAL_N_T_RANGE]),
      .d_cal_p_c          (i_rcvr_cmn_cfg[`DDR_ANA_DQS_RCVR_CAL_P_C_RANGE]),
      .d_cal_p_t          (i_rcvr_cmn_cfg[`DDR_ANA_DQS_RCVR_CAL_P_T_RANGE]),
      .d_dcpath_ena       (i_rcvr_cmn_cfg[`DDR_ANA_DQS_RCVR_DCPATH_EN_RANGE]),
      .d_dly_ctrl_c       (i_rcvr_cfg[`DDR_ANA_DQS_RCVR_DLY_CTRL_C_RANGE]),
      .d_dly_ctrl_t       (i_rcvr_cfg[`DDR_ANA_DQS_RCVR_DLY_CTRL_T_RANGE]),
      .d_edge_det_byp     (i_rcvr_cmn_cfg[`DDR_ANA_DQS_RCVR_EDGE_DET_BYP_RANGE]),
      .d_edge_det_refsel  (i_rcvr_cmn_cfg[`DDR_ANA_DQS_RCVR_EDGE_DET_REFSEL_RANGE]),
      .d_edge_det_ena     (ena),
      .d_ena              (ena),
      .d_fb_ena           (i_rcvr_cmn_cfg[`DDR_ANA_DQS_RCVR_FB_EN_RANGE]),
      .d_rxcal_ena        (i_rcvr_cmn_cfg[`DDR_ANA_DQS_RCVR_RXCAL_EN_RANGE]),
      .d_se_mode          (i_rcvr_cmn_cfg[`DDR_ANA_DQS_RCVR_SE_MODE_RANGE]),
      .dqs_in_c           (pad_c),
      .dqs_in_t           (pad_t)
`ifndef WLOGIC_NO_PG
      ,.vdda              (vdda),
      .vddq               (vddq),
      .vss                (vss)
`endif
   );

endmodule
