
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
`include "ddr_cmn_wrapper_define.vh"
`include "ddr_cmn_csr_defs.vh"

import ddr_global_pkg::*;

module ddr_cmn_wrapper #(
   parameter P0WIDTH = `DDR_CMN_PLL_CFG_BUS_WIDTH
) (

   input  logic [P0WIDTH-1:0]                 i_pll_cfg,

   //ZQCAL
   inout  wire                                pad_rext,
   output logic                               o_zqcal_comp,

   //REFGEN
   output wire                                ana_vref,

   //TEST
   inout  wire                                pad_atb,
   input  wire    [3:0]                       ana_atst_in,
   input  logic                               i_scan_clk,
   input  logic                               i_scan_mode,

   //Freeze
   input  logic                               i_freeze_n,

   //PLL
   input  logic                               i_rst,
   input  logic                               i_refclk,
   input  logic                               i_refclk_alt,
   output logic                               o_fbclk,
   output logic                               o_refclk,
   output logic                               o_vco_clk0,
   output logic                               o_vco_clk90,
   output logic                               o_vco_clk180,
   output logic                               o_vco_clk270,
   output logic                               o_vco0_div2_clk,
   output logic                               o_vco1_div2_clk,
   output logic                               o_vco2_div2_clk,
   output logic                               o_vco0_clk,
   input  logic                               i_gfcm_clksel,

   input  logic                               i_phy_clk_ena,
   input  logic                               i_gfcm_ena,

   input  logic                               i_pll0_div_clk_rst,
   input  logic                               i_pll0_div_clk_ena,
   input  logic                               i_pll0_div_clk_byp,

   output logic                               o_pll0_div_clk,

   output logic                               o_freeze_n_aon,
   output logic                               o_freeze_n_hv,

   output logic                               o_pmon_nand_clk,
   output logic                               o_pmon_nor_clk,
   output logic                               o_gfcm0_clka_sel,
   output logic                               o_gfcm0_clkb_sel,
   output logic                               o_gfcm1_clka_sel,
   output logic                               o_gfcm1_clkb_sel,

   // TEST Clocks
   input  logic [3:0]                         i_dtst,
   input  logic [4:0]                         i_dtst_sel,
   output logic                               o_dtst,

   input  logic                               i_ddr_rstn,
   input  logic                               i_ddr_rstn_bs_din,
   input  logic                               i_ddr_rstn_bs_ena,
   input  logic                               i_ddr_rstn_lpbk_ena,
   output logic                               o_ddr_rstn_lpbk_out,
   inout  wire                                pad_reset_n,

   input  logic [`DDR_CMN_VREF_M0_CFG_RANGE]  i_cmn_vref_cfg,
   input  logic [`DDR_CMN_ZQCAL_CFG_RANGE]    i_cmn_zqcal_cfg,
   input  logic [`DDR_CMN_IBIAS_CFG_RANGE]    i_cmn_ibias_cfg,
   input  logic [`DDR_CMN_TEST_CFG_RANGE]     i_cmn_test_cfg,
   input  logic [`DDR_CMN_LDO_M0_CFG_RANGE]   i_cmn_ldo_cfg,
   input  logic [`DDR_CMN_CLK_CTRL_CFG_RANGE] i_cmn_clk_ctrl_cfg,
   input  logic [`DDR_CMN_PMON_ANA_CFG_RANGE] i_cmn_pmon_ana_cfg

);

`ifndef WLOGIC_NO_PG
   wire vdda1p2, vddq, vss;
   wire vdd_aon, vdd_phy;
   assign vdd_aon = 1'b1;
   assign vdd_phy = 1'b1;
   assign vdda1p2 = 1'b1;
   assign vddq = 1'b1;
   assign vss  = 1'b0;
`endif

wire ana_vco1_clk0   ;
wire ana_vco1_clk90  ;
wire ana_vco1_clk180 ;
wire ana_vco1_clk270 ;

wire ana_vco2_clk0   ;
wire ana_vco2_clk90  ;
wire ana_vco2_clk180 ;
wire ana_vco2_clk270 ;
logic scan_refclk_alt ;

ddr_wcm_mux u_scan_refclk_alt_mux (.i_sel(i_scan_mode), .i_b(i_scan_clk), .i_a(i_refclk_alt), .o_z(scan_refclk_alt));

   // ------------------------------------------------------------------------
   // Test Clocks
   // ------------------------------------------------------------------------

   //13 clocks
   logic dtst_l0_0 , dtst_l1_0, dtst_l2_0;
   logic dtst_l0_1 , dtst_l1_1, dtst_l2_1;
   logic dtst_l0_2 , dtst_l1_2;
   logic dtst_l0_3 , dtst_l1_3;
   logic dtst_l0_4;
   logic dtst_l0_5;
   /*
     0 0 0 0 i_dtst[0]
     0 0 0 1 i_dtst[1]
     0 0 1 0 i_dtst[2]
     0 0 1 1 i_dtst[3]
     0 1 0 0 i_refclk
     0 1 0 1 '0
     0 1 1 0 o_vco_clk0
     0 1 1 1 o_pll0_div_clk
     1 0 0 0 o_vco0_clk
     1 0 0 1 o_vco0_div2_clk
     1 0 1 0 o_vco1_div2_clk
     1 0 1 1 o_vco2_div2_clk
     1 1 0 x ana_vco1_clk0
     1 1 1 x ana_vco2_clk0
   */

   // Level 0 Muxig - 6
   ddr_wcm_mux u_dtst_l0_mux0 (
      .i_a   (i_dtst[0]),
      .i_b   (i_dtst[1]),
      .i_sel (i_dtst_sel[0]),
      .o_z   (dtst_l0_0)
   );

   ddr_wcm_mux u_dtst_l0_mux1 (
      .i_a   (i_dtst[2]),
      .i_b   (i_dtst[3]),
      .i_sel (i_dtst_sel[0]),
      .o_z   (dtst_l0_1)
   );

   ddr_wcm_mux u_dtst_l0_mux2 (
      .i_a   (i_refclk),
      .i_b   ('0),
      .i_sel (i_dtst_sel[0]),
      .o_z   (dtst_l0_2)
   );

    ddr_wcm_mux u_dtst_l0_mux3 (
      .i_a   (o_vco_clk0),
      .i_b   (o_pll0_div_clk),
      .i_sel (i_dtst_sel[0]),
      .o_z   (dtst_l0_3)
   );

    ddr_wcm_mux u_dtst_l0_mux4 (
      .i_a   (o_vco0_clk),
      .i_b   (o_vco0_div2_clk),
      .i_sel (i_dtst_sel[0]),
      .o_z   (dtst_l0_4)
   );

   ddr_wcm_mux u_dtst_l0_mux5 (
      .i_a   (o_vco1_div2_clk),
      .i_b   (o_vco2_div2_clk),
      .i_sel (i_dtst_sel[0]),
      .o_z   (dtst_l0_5)
   );

   // Level 1 Muxig - 3
   ddr_wcm_mux u_dtst_l1_mux0 (
      .i_a   (dtst_l0_0),
      .i_b   (dtst_l0_1),
      .i_sel (i_dtst_sel[1]),
      .o_z   (dtst_l1_0)
   );

   ddr_wcm_mux u_dtst_l1_mux1 (
      .i_a   (dtst_l0_2),
      .i_b   (dtst_l0_3),
      .i_sel (i_dtst_sel[1]),
      .o_z   (dtst_l1_1)
   );

   ddr_wcm_mux u_dtst_l1_mux2 (
      .i_a   (dtst_l0_4),
      .i_b   (dtst_l0_5),
      .i_sel (i_dtst_sel[1]),
      .o_z   (dtst_l1_2)
   );

   ddr_wcm_mux u_dtst_l1_mux3 (
      .i_a   (ana_vco1_clk0),
      .i_b   (ana_vco2_clk0),
      .i_sel (i_dtst_sel[1]),
      .o_z   (dtst_l1_3)
   );

   // Level 2 Muxig - 2
   ddr_wcm_mux u_dtst_l2_mux0 (
      .i_a   (dtst_l1_0),
      .i_b   (dtst_l1_1),
      .i_sel (i_dtst_sel[2]),
      .o_z   (dtst_l2_0)
   );

   ddr_wcm_mux u_dtst_l2_mux1 (
      .i_a   (dtst_l1_2),
      .i_b   (dtst_l1_3),
      .i_sel (i_dtst_sel[2]),
      .o_z   (dtst_l2_1)
   );

   // Level 3 Muxig - 1

   ddr_wcm_mux u_dtst_l3_mux0 (
      .i_a   (dtst_l2_0),
      .i_b   (dtst_l2_1),
      .i_sel (i_dtst_sel[3]),
      .o_z   (o_dtst)
   );

wphy_lp4x5_cmn u_cmn_ana (
    .ldo_tran_enh_ena              (i_cmn_ldo_cfg[`DDR_CMN_LDO_M0_CFG_TRAN_ENH_EN_FIELD]),
    .ldo_phy_ena                   (i_cmn_ldo_cfg[`DDR_CMN_LDO_M0_CFG_EN_FIELD]),
    .ldo_phy_hiz                   (i_cmn_ldo_cfg[`DDR_CMN_LDO_M0_CFG_HIZ_FIELD]),
    .ldo_atst_sel                  (i_cmn_ldo_cfg[`DDR_CMN_LDO_M0_CFG_ATST_SEL_FIELD]),
    .ldo_vref_ctrl                 (i_cmn_ldo_cfg[`DDR_CMN_LDO_M0_CFG_VREF_CTRL_FIELD]),
    .pmon_nand_ena                 (i_cmn_pmon_ana_cfg[`DDR_CMN_PMON_ANA_CFG_NAND_EN_FIELD]),
    .pmon_nor_ena                  (i_cmn_pmon_ana_cfg[`DDR_CMN_PMON_ANA_CFG_NOR_EN_FIELD]),
    .pmon_nand_fout                (o_pmon_nand_clk),
    .pmon_nor_fout                 (o_pmon_nor_clk),
    .freeze_n                      (i_freeze_n),
    .freeze_n_aon                  (o_freeze_n_aon),
    .freeze_n_hv                   (o_freeze_n_hv),
    .pad_atb                       (pad_atb),
    .pad_rext                      (pad_rext),
    .pad_reset_n                   (pad_reset_n),
    .vref_ctrl                     (i_cmn_vref_cfg[`DDR_CMN_VREF_M0_CFG_CTRL_FIELD]),
    .vref_ena                      (i_cmn_vref_cfg[`DDR_CMN_VREF_M0_CFG_EN_FIELD]),
    .vref_hiz                      (i_cmn_vref_cfg[`DDR_CMN_VREF_M0_CFG_HIZ_FIELD]),
    .vref_pwr                      (i_cmn_vref_cfg[`DDR_CMN_VREF_M0_CFG_PWR_FIELD]),
    .zqcal_cal_ena                 (i_cmn_zqcal_cfg[`DDR_CMN_ZQCAL_CFG_CAL_EN_FIELD]),
    .zqcal_ncal                    (i_cmn_zqcal_cfg[`DDR_CMN_ZQCAL_CFG_NCAL_FIELD]),
    .zqcal_pcal                    (i_cmn_zqcal_cfg[`DDR_CMN_ZQCAL_CFG_PCAL_FIELD]),
    .zqcal_pd_sel                  (i_cmn_zqcal_cfg[`DDR_CMN_ZQCAL_CFG_PD_SEL_FIELD]),
    .zqcal_vol_0p6_sel             (i_cmn_zqcal_cfg[`DDR_CMN_ZQCAL_CFG_VOL_0P6_SEL_FIELD]),
    .vref                          (ana_vref),
    .zacal_comp_out                (o_zqcal_comp),
    .atst_in                       (ana_atst_in),
    .atst_sel                      (i_cmn_test_cfg[`DDR_CMN_TEST_CFG_ATST_SEL_FIELD]),
    .dtst_in                       (o_dtst),
    .dtst_drv_impd                 (i_cmn_test_cfg[`DDR_CMN_TEST_CFG_DTST_DRVR_IMPD_FIELD]),
    .ddr_rstn_bs_din               (i_ddr_rstn_bs_din),
    .ddr_rstn_bs_ena               (i_ddr_rstn_bs_ena),
    .ddr_rstn_din                  (i_ddr_rstn),
    .ddr_rstn_lpbk_ena             (i_ddr_rstn_lpbk_ena),
    .ddr_rstn_lpbk_out             (o_ddr_rstn_lpbk_out)
`ifndef WLOGIC_NO_PG
    ,.vdda1p2                      (vdda1p2),
    .vdd_aon                       (vdd_aon),
    .vdd_phy                       (vdd_phy),
    .vddq                          (vddq),
    .vss                           (vss)
`endif
);

wphy_lp4x5_cmn_clks_svt u_cmn_clks_ana (
    .phy_clk0         (o_vco_clk0),
    .phy_clk90        (o_vco_clk90),
    .phy_clk180       (o_vco_clk180),
    .phy_clk270       (o_vco_clk270),
    .pll0_div_clk     (o_pll0_div_clk),

    .gfcm0_clka_sel   (o_gfcm0_clka_sel),
    .gfcm0_clkb_sel   (o_gfcm0_clkb_sel),
    .gfcm1_clka_sel   (o_gfcm1_clka_sel),
    .gfcm1_clkb_sel   (o_gfcm1_clkb_sel),
    .gfcm_clksel      (i_gfcm_clksel),
    .phy_clk_ena      (i_phy_clk_ena),
    .gfcm_ena         (i_gfcm_ena),
    .pll0_div_clk_byp (i_pll0_div_clk_byp),
    .pll0_div_clk_ena (i_pll0_div_clk_ena),
    .pll0_div_clk_rst (i_pll0_div_clk_rst),
    .vco1_clk0        (ana_vco1_clk0   ),
    .vco1_clk90       (ana_vco1_clk90  ),
    .vco1_clk180      (ana_vco1_clk180 ),
    .vco1_clk270      (ana_vco1_clk270 ),
    .vco2_clk0        (ana_vco2_clk0   ),
    .vco2_clk90       (ana_vco2_clk90  ),
    .vco2_clk180      (ana_vco2_clk180 ),
    .vco2_clk270      (ana_vco2_clk270 )
`ifndef WLOGIC_NO_PG
   ,.vdd_phy          (vdd_aon)
   ,.vss              (vss)
`endif //WLOGIC_NO_PG
);

wphy_rpll_mvp_4g u_wphy_rpll_mvp_4g (
  .fbclk             ( o_fbclk                ),
  .refclk_out        ( o_refclk               ),
  .vco0_clk          ( o_vco0_clk             ),
  .vco0_div2_clk     ( o_vco0_div2_clk        ),
  .vco1_clk0         ( ana_vco1_clk0          ),
  .vco1_clk90        ( ana_vco1_clk90         ),
  .vco1_clk180       ( ana_vco1_clk180        ),
  .vco1_clk270       ( ana_vco1_clk270        ),
  .vco1_div2_clk     ( o_vco1_div2_clk        ),
  .vco1_div16_clk    ( /*OPEN*/               ),
  .vco2_clk0         ( ana_vco2_clk0          ),
  .vco2_clk90        ( ana_vco2_clk90         ),
  .vco2_clk180       ( ana_vco2_clk180        ),
  .vco2_clk270       ( ana_vco2_clk270        ),
  .vco2_div2_clk     ( o_vco2_div2_clk        ),
  .vco2_div16_clk    ( /*OPEN*/               ),
  .bias_lvl          (i_pll_cfg[`DDR_CMN_PLL_BIAS_LVL_FIELD]),
  .cp_int_mode       (i_pll_cfg[`DDR_CMN_PLL_CP_INT_MODE_FIELD]),
  .div16_ena         (i_pll_cfg[`DDR_CMN_PLL_DIV16_EN_FIELD]),
  .ena               (i_pll_cfg[`DDR_CMN_PLL_EN_FIELD]),
  .fbdiv_sel         (i_pll_cfg[`DDR_CMN_PLL_FBDIV_SEL_FIELD]),
  .int_ctrl          (i_pll_cfg[`DDR_CMN_PLL_INT_CTRL_FIELD]), //[4:0]
  .pfd_mode          (i_pll_cfg[`DDR_CMN_PLL_PFD_MODE_FIELD]),
  .prop_c_ctrl       (i_pll_cfg[`DDR_CMN_PLL_PROP_C_CTRL_FIELD]),
  .prop_ctrl         (i_pll_cfg[`DDR_CMN_PLL_PROP_CTRL_FIELD]), //[4:0]
  .prop_r_ctrl       (i_pll_cfg[`DDR_CMN_PLL_PROP_R_CTRL_FIELD]),
  .refclk            (i_refclk),
  .refclk_alt        (scan_refclk_alt),
  .reset             (i_rst),
  .sel_refclk_alt    (i_pll_cfg[`DDR_CMN_PLL_SEL_REFCLK_ALT_FIELD]),
  .vco0_band         (i_pll_cfg[`DDR_CMN_PLL_VCO0_BAND_FIELD]),
  .vco0_byp_clk_sel  (i_pll_cfg[`DDR_CMN_PLL_VCO0_BYP_CLK_SEL_FIELD]),
  .vco0_ena          (i_pll_cfg[`DDR_CMN_PLL_VCO0_ENA_FIELD]),
  .vco0_fine         (i_pll_cfg[`DDR_CMN_PLL_VCO0_FINE_FIELD]), //[5:0]
  .vco1_band         (i_pll_cfg[`DDR_CMN_PLL_VCO1_BAND_FIELD]),
  .vco1_byp_clk_sel  (i_pll_cfg[`DDR_CMN_PLL_VCO1_BYP_CLK_SEL_FIELD]),
  .vco1_ena          (i_pll_cfg[`DDR_CMN_PLL_VCO1_ENA_FIELD]),
  .vco1_fine         (i_pll_cfg[`DDR_CMN_PLL_VCO1_FINE_FIELD]), //[5:0]
  .vco1_post_div     (i_pll_cfg[`DDR_CMN_PLL_VCO1_POST_DIV_FIELD]),
  .vco2_band         (i_pll_cfg[`DDR_CMN_PLL_VCO2_BAND_FIELD]),
  .vco2_byp_clk_sel  (i_pll_cfg[`DDR_CMN_PLL_VCO2_BYP_CLK_SEL_FIELD]),
  .vco2_ena          (i_pll_cfg[`DDR_CMN_PLL_VCO2_ENA_FIELD]),
  .vco2_fine         (i_pll_cfg[`DDR_CMN_PLL_VCO2_FINE_FIELD]), //[5:0]
  .vco2_post_div     (i_pll_cfg[`DDR_CMN_PLL_VCO2_POST_DIV_FIELD]),
  .vco_sel           (i_pll_cfg[`DDR_CMN_PLL_VCO_SEL_FIELD])
`ifndef WLOGIC_NO_PG
  ,.vdda              ( vdd_aon                )
  ,.vss               ( vss                    )
`endif
);

endmodule
