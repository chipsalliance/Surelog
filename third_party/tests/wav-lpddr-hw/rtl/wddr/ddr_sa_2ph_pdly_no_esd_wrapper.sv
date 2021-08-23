
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
`include "ddr_sa_2ph_wrapper_define.vh"
`include "ddr_sa_2ph_wrapper_cmn_define.vh"
`include "ddr_sa_2ph_pdly_wrapper_define.vh"

module ddr_sa_2ph_pdly_no_esd_wrapper #(
   parameter P0WIDTH = 20,
   parameter P1WIDTH = 5,
   parameter P2WIDTH = 32
) (
   input  logic pad,
   input  logic ana_vref,
   input  logic i_clk_0,
   input  logic i_clk_180,
   input  logic i_sa_en,
   input  logic [P0WIDTH-1:0] i_sa_cfg,
   input  logic [P1WIDTH-1:0] i_sa_cmn_cfg,
   input  logic [P2WIDTH-1:0] i_sa_dly_cfg,
   output logic o_data_0,
   output logic o_data_0_b,
   output logic o_data_180,
   output logic o_data_180_b
);

`ifndef WLOGIC_NO_PG
   wire vdda, vss;
   assign vdda = 1'b1;
   assign vss  = 1'b0;
`endif

   logic sa_ena_0_180;
`ifndef DDR_IO_WRAPPER_BEHAV
   ddr_wcm_mux  u_mux_ena (.i_sel(i_sa_cmn_cfg[`DDR_ANA_SA_2PH_SW_OVR_RANGE]), .i_a(i_sa_en), .i_b(i_sa_cmn_cfg[`DDR_ANA_SA_2PH_OVR_EN_0_180_RANGE]), .o_z(sa_ena_0_180));
`else
   assign sa_ena_0_180 = i_sa_cmn_cfg[`DDR_ANA_SA_2PH_SW_OVR_RANGE] ? i_sa_cmn_cfg[`DDR_ANA_SA_2PH_OVR_EN_0_180_RANGE] : i_sa_en;
`endif

   wphy_sa_4g_2ph_pdly_no_esd u_sa_4g_2ph_pdly (
      .d_data_c         (o_data_180),
      .d_datab_c        (o_data_180_b),
      .d_data_t         (o_data_0),
      .d_datab_t        (o_data_0_b),
      .d_dly_gear_t     (i_sa_dly_cfg[`DDR_ANA_SA_2PH_PDLY_DLY_GEAR_0_RANGE]),
      .d_dly_gear_c     (i_sa_dly_cfg[`DDR_ANA_SA_2PH_PDLY_DLY_GEAR_180_RANGE]),
      .d_dly_ctrl_t     (i_sa_dly_cfg[`DDR_ANA_SA_2PH_PDLY_DLY_CTRL_0_RANGE]),
      .d_dly_ctrl_c     (i_sa_dly_cfg[`DDR_ANA_SA_2PH_PDLY_DLY_CTRL_180_RANGE]),
      .d_cal_c          (i_sa_cfg[`DDR_ANA_SA_2PH_CAL_CODE_180_RANGE]),
      .d_cal_dir_c      (i_sa_cfg[`DDR_ANA_SA_2PH_CAL_DIR_180_RANGE]),
      .d_cal_dir_t      (i_sa_cfg[`DDR_ANA_SA_2PH_CAL_DIR_0_RANGE]),
      .d_cal_t          (i_sa_cfg[`DDR_ANA_SA_2PH_CAL_CODE_0_RANGE]),
      .d_clk_c          (i_clk_180),
      .d_clk_t          (i_clk_0),
      .d_sa_ena         (sa_ena_0_180),
      .d_sacal_ena      (i_sa_cmn_cfg[`DDR_ANA_SA_2PH_CAL_EN_0_180_RANGE]),
      .rxin             (pad),
      .vref             (ana_vref)
`ifndef WLOGIC_NO_PG
      ,.vdda            (vdda),
      .vss              (vss)
`endif
   );

endmodule
