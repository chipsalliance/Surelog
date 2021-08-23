
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
`include "ddr_cmn_csr_defs.vh"
`include "ddr_fsw_csr_defs.vh"
`include "ddr_cmn_wrapper_define.vh"

import ddr_global_pkg::*;

module ddr_cmn #(
   parameter       AWIDTH        = 32,
   parameter       DWIDTH        = 32,
   parameter [0:0] SECONDARY_PHY = 1'b0
) (

   // Test
   input  logic        [3:0]                       i_dtst,
   output logic                                    o_dtst,
   input               [3:0]                       ana_atst_in,

   //DDR Reset
   input  logic                                    i_ddr_rstn,
   input  logic                                    i_jtag_tck,
   input  logic                                    i_jtag_trst_n,
   input  logic                                    i_jtag_bsr_mode,
   input  logic                                    i_jtag_capture,
   input  logic                                    i_jtag_shift  ,
   input  logic                                    i_jtag_update ,
   input  logic                                    i_jtag_tdi    ,
   output logic                                    o_jtag_tdo    ,

   // Freeze
   input                                           i_freeze_n,
   input  logic                                    i_freeze_n_aon,
   input  logic                                    i_freeze_n_hv,
   output logic                                    o_freeze_n_aon,
   output logic                                    o_freeze_n_hv,

   // VREF
   input  wire                                     ana_vref_in,
   output wire                                     ana_vref_out,

   // Clocks and reset
   input  logic                                    i_rst,
`ifdef DDR_ECO_ANA_REF_CLK
   input  logic                                    i_ana_refclk,
`endif
   input  logic                                    i_refclk,
   input  logic                                    i_refclk_alt,
   output logic                                    o_pll0_div_clk,

   input  logic                                    i_pll_clk_0,
   input  logic                                    i_pll_clk_1,
   input  logic                                    i_pll_clk_2,
   input  logic                                    i_pll_clk_3,
   input  logic                                    i_vco0_clk,

   output logic                                    o_pll_clk_0,
   output logic                                    o_pll_clk_1,
   output logic                                    o_pll_clk_2,
   output logic                                    o_pll_clk_3,
   output logic                                    o_vco0_clk,

   // IRQ
   output  logic                                   o_pll_irq,

   // Frequency Switch
   input  logic                                    i_dfi_clk,
   input  logic                                    i_dfi_clk_on,
   input  logic                                    i_dfi_init_start,
   input  logic                                    i_cmn_switch_done,
   output logic                                    o_cmn_switch_done,
   output logic                                    o_cmn_init_complete,
   output logic                                    o_cmn_msr,
   input  logic                                    i_csp_pi_en,
   input  logic                                    i_csp_div_rst_n,
   output logic                                    o_csp_pi_en,
   output logic                                    o_csp_div_rst_n,

   // PLL boundary scan ports
   input  wire                                     i_bscan_mode,
   input  wire                                     i_bscan_tck,
   input  wire                                     i_bscan_trst_n,
   input  wire                                     i_bscan_capturedr,
   input  wire                                     i_bscan_shiftdr,
   input  wire                                     i_bscan_updatedr,
   input  wire                                     i_bscan_tdi,
   output wire                                     o_bscan_tdo,
   input  wire                                     i_iddq_mode,

   // PLL and PMON dig scan ports
   input  logic                                    i_scan_rst_ctrl,
   input  logic                                    i_scan_cgc_ctrl,
   input  logic                                    i_scan_clk,
   input  logic                                    i_scan_mode,
   input  logic [7:0]                              i_scan_freq_en,

   // PMON DIG additional scan ports
   input  logic                                    i_scan_in,
   input  logic                                    i_scan_shift,
   output logic                                    o_scan_out,

   // PLL AHB Slave ports
   input   logic                                   i_ahb_csr_rst,
   input   logic                                   i_hclk,
   input   logic                                   i_hreset,
   input   logic [AWIDTH-1:0]                      i_haddr,
   input   logic                                   i_hwrite,
   input   logic                                   i_hsel,
   input   logic [DWIDTH-1:0]                      i_hwdata,
   input   logic [1:0]                             i_htrans,
   input   logic [2:0]                             i_hsize,
   input   logic [2:0]                             i_hburst,
   input   logic                                   i_hreadyin,
   output  logic                                   o_hready,
   output  logic [DWIDTH-1:0]                      o_hrdata,
   output  logic [1:0]                             o_hresp,

   //Pad
   inout                                           pad_reset_n,
   inout                                           pad_rext,
   inout                                           pad_atb,

   // Debug
   output logic [31:0]                             o_debug
);

   logic vco0_div2_clk , vco1_div2_clk,  vco2_div2_clk;
   logic refclk;
   logic mvp_reset;

   logic [`DDR_FSW_DEBUG_CFG_WIDTH-1:0]    fsw_debug_cfg;
   logic [`DDR_FSW_CSP_0_CFG_WIDTH-1:0]    fsw_csp_0_cfg;
   logic [`DDR_FSW_CSP_1_CFG_WIDTH-1:0]    fsw_csp_1_cfg;
   logic [`DDR_FSW_CSP_STA_WIDTH-1:0]      fsw_csp_sta;
   logic [`DDR_CMN_PLL_CFG_BUS_WIDTH-1:0]  pll_cfg;
   logic [`DDR_FSW_CTRL_CFG_RANGE]         fsw_ctrl_cfg;
   logic [`DDR_FSW_CTRL_STA_RANGE]         fsw_ctrl_sta;
   logic [`DDR_CMN_ZQCAL_STA_RANGE]        zqcal_sta;
   logic [`DDR_CMN_CLK_STA_RANGE]          clk_sta;
   logic [`DDR_CMN_PMON_NAND_STA_RANGE]    cmn_pmon_nand_sta;
   logic [`DDR_CMN_PMON_NOR_STA_RANGE]     cmn_pmon_nor_sta;

   logic [`DDR_CMN_VREF_M0_CFG_RANGE]      cmn_vref_cfg;
   logic [`DDR_CMN_ZQCAL_CFG_RANGE]        cmn_zqcal_cfg;
   logic [`DDR_CMN_IBIAS_CFG_RANGE]        cmn_ibias_cfg;
   logic [`DDR_CMN_TEST_CFG_RANGE]         cmn_test_cfg;
   logic [`DDR_CMN_LDO_M0_CFG_RANGE]       cmn_ldo_cfg;
   logic [`DDR_CMN_CLK_CTRL_CFG_RANGE]     cmn_clk_ctrl_cfg;
   logic [`DDR_CMN_PMON_ANA_CFG_RANGE]     cmn_pmon_ana_cfg;
   logic [`DDR_CMN_PMON_DIG_CFG_RANGE]     cmn_pmon_dig_cfg;
   logic [`DDR_CMN_PMON_DIG_NAND_CFG_RANGE]cmn_pmon_dig_nand_cfg;
   logic [`DDR_CMN_PMON_DIG_NOR_CFG_RANGE] cmn_pmon_dig_nor_cfg;
   logic [`DDR_CMN_RSTN_CFG_RANGE]         ddr_rstn_cfg;
   logic [`DDR_CMN_RSTN_STA_RANGE]         ddr_rstn_sta;

   logic                                   core_reset;
   logic [1:0]                             core_vco_sel;
   logic                                   core_gfm_sel;
   logic                                   core_ready;
   logic                                   core_switch_vco;
   logic [31:0]                            core_debug_bus_ctrl_status;
   logic                                   fbclk;

   logic [31:0]                            pll_haddr;
   logic                                   pll_hwrite;
   logic                                   pll_hsel;
   logic [31:0]                            pll_hwdata;
   logic [1:0]                             pll_htrans;
   logic [2:0]                             pll_hsize;
   logic [2:0]                             pll_hburst;
   logic                                   pll_hready;
   logic                                   pll_hreadyin;
   logic [31:0]                            pll_hrdata;
   logic [1:0]                             pll_hresp;
   logic                                   csp_clk_en;
   logic                                   phy_clk_ena;
   logic                                   gfcm_ena;

   assign core_reset   = 1'b1;        // Force to reset at boot and leverage the SW reset
                                      // to ensure that the PLL is programmed properly
   // ------------------------------------------------------------------------
   // Test Clocks
   // ------------------------------------------------------------------------
   logic [4:0] dtst_sel;
   logic       dtst ;
   assign dtst_sel = cmn_test_cfg[`DDR_CMN_TEST_CFG_DTST_EXT_SEL_FIELD];

   ddr_div2_rst u_div2_rst (
      .i_clk                        (dtst),
      .i_rst                        (i_rst),
      .i_div_en                     (cmn_test_cfg[`DDR_CMN_TEST_CFG_DTST_DIV_EN_FIELD]),
      .i_div_byp                    (i_scan_mode),
      .o_div2_clk                   (o_dtst)
   );

   // ------------------------------------------------------------------------
   // CMN Block
   // ------------------------------------------------------------------------
   logic                 pll0_div_clk_rst_int ;
   logic                 pll0_div_clk_rst;
   logic                 pll0_div_clk_ena;
   logic                 pll0_div_clk_byp;
   logic                 pll0_div_clk;
   logic                 csp_clk_on;
   logic                 pmon_nand_clk;
   logic                 pmon_nor_clk;
   logic                 ddr_rstn;
   logic                 ddr_rstn_bs_din;
   logic                 ddr_rstn_bs_ena;
   logic                 scan_clk0;
   logic                 scan_clk1;

   assign pll0_div_clk_rst_int = i_rst | cmn_clk_ctrl_cfg[`DDR_CMN_CLK_CTRL_CFG_PLL0_DIV_CLK_RST_FIELD];
   assign pll0_div_clk_ena     = (cmn_clk_ctrl_cfg[`DDR_CMN_CLK_CTRL_CFG_PLL0_DIV_CLK_EN_FIELD] | csp_clk_on ) ;
   assign pll0_div_clk_byp     = cmn_clk_ctrl_cfg[`DDR_CMN_CLK_CTRL_CFG_PLL0_DIV_CLK_BYP_FIELD] | i_scan_mode;
   assign gfcm_ena             = cmn_clk_ctrl_cfg[`DDR_CMN_CLK_CTRL_CFG_GFCM_EN_FIELD]  | i_scan_cgc_ctrl;
   assign ddr_rst             = ddr_rstn_cfg[`DDR_CMN_RSTN_CFG_RSTN_OVR_SEL_FIELD] ? ~ddr_rstn_cfg[`DDR_CMN_RSTN_CFG_RSTN_OVR_VAL_FIELD] : ~i_ddr_rstn ;

   //DFT Clk/Rst muxing & Freq En CGC

   ddr_cgc_rl  u_cgc0 (.i_clk(i_scan_clk),    .i_clk_en(1'b1), .i_cgc_en(i_scan_freq_en[`DDR_FREQ_EN_FSW]),    .o_clk(scan_clk0));
   ddr_cgc_rl  u_cgc1 (.i_clk(i_scan_clk),    .i_clk_en(1'b1), .i_cgc_en(i_scan_freq_en[`DDR_FREQ_EN_CMN]),    .o_clk(scan_clk1));

   ddr_scan_rst u_scan_pll0_div_rst (
      .i_scan_rst_ctrl  (i_scan_rst_ctrl),
      .i_rst            (pll0_div_clk_rst_int),
      .o_rst            (pll0_div_clk_rst)
   );

   ddr_scan_clk_mux u_scan_pll0_div_clk_mux (
      .i_scan_mode      (i_scan_mode),
      .i_scan_clk       (scan_clk0),
      .i_clk            (pll0_div_clk),
      .o_clk            (o_pll0_div_clk)
   );

`ifdef DDR_FASTx16_REFCLK
   logic refclk_div16 ;
   logic refclk_div8 ;
   logic refclk_div4 ;
   logic refclk_div2 ;
   initial begin
      refclk_div2 = '0;
      refclk_div4 = '0;
      refclk_div8 = '0;
      refclk_div16 = '0;
   end
   always @(posedge i_refclk)    refclk_div2  = ~refclk_div2;
   always @(posedge refclk_div2) refclk_div4  = ~refclk_div4;
   always @(posedge refclk_div4) refclk_div8  = ~refclk_div8;
   always @(posedge refclk_div8) refclk_div16 = ~refclk_div16;
`endif

  generate
      if (!SECONDARY_PHY) begin: CMN

         ddr_rstn_bscan #(
            .WIDTH         (1)
         ) u_rstn_bscan (
            .i_jtag_tck                   (i_jtag_tck    ),
            .i_jtag_trst_n                (i_jtag_trst_n ),
            .i_jtag_bsr_mode              (i_jtag_bsr_mode),
            .i_jtag_capture               (i_jtag_capture ),
            .i_jtag_shift                 (i_jtag_shift   ),
            .i_jtag_update                (i_jtag_update  ),
            .i_jtag_tdi                   (i_jtag_tdi     ),
            .o_jtag_tdo                   (o_jtag_tdo     ),

            .i_bscan_ctrl                 (ddr_rstn_cfg[`DDR_CMN_RSTN_CFG_RSTN_BS_ENA_FIELD]),
            .i_bscan                      (ddr_rstn_cfg[`DDR_CMN_RSTN_CFG_RSTN_BS_DIN_FIELD]),

            .o_pad_bscan                  (ddr_rstn_bs_din),
            .o_pad_bscan_oe               (ddr_rstn_bs_ena)
         );

         ddr_cmn_wrapper #(
            .P0WIDTH                      (`DDR_CMN_PLL_CFG_BUS_WIDTH)
         ) u_cmn_wrapper (
            .i_pll_cfg                    (pll_cfg),
            .pad_rext                     (pad_rext),
            .o_zqcal_comp                 (zqcal_sta[`DDR_CMN_ZQCAL_STA_COMP_FIELD]),
            .ana_vref                     (ana_vref_out),
            .pad_atb                      (pad_atb),
            .ana_atst_in                  (ana_atst_in),
            .i_dtst                       (i_dtst),
            .o_dtst                       (dtst),
            .i_dtst_sel                   (dtst_sel),
            .i_scan_clk                   (i_scan_clk),
            .i_scan_mode                  (i_scan_mode),
            .i_freeze_n                   (i_freeze_n),
            .i_rst                        (mvp_reset),
`ifdef DDR_ECO_ANA_REF_CLK
`ifdef DDR_FASTx16_REFCLK
            .i_refclk                     (refclk_div16),
`else // DDR_FASTx16_REFCLK
            .i_refclk                     (i_ana_refclk),
`endif
`else
`ifdef DDR_FASTx16_REFCLK
            .i_refclk                     (refclk_div16),
`else // DDR_FASTx16_REFCLK
            .i_refclk                     (i_refclk),
`endif
`endif
            .i_refclk_alt                 (i_refclk_alt),
            .o_fbclk                      (fbclk),
            .o_refclk                     (refclk),
            .o_vco_clk0                   (o_pll_clk_0),
            .o_vco_clk90                  (o_pll_clk_1),
            .o_vco_clk180                 (o_pll_clk_2),
            .o_vco_clk270                 (o_pll_clk_3),
            .o_vco0_div2_clk              (vco0_div2_clk),
            .o_vco1_div2_clk              (vco1_div2_clk),
            .o_vco2_div2_clk              (vco2_div2_clk),
            .o_vco0_clk                   (o_vco0_clk),
            .o_gfcm0_clka_sel             (clk_sta[`DDR_CMN_CLK_STA_GFCM0_CLKA_SEL_FIELD]),
            .o_gfcm0_clkb_sel             (clk_sta[`DDR_CMN_CLK_STA_GFCM0_CLKB_SEL_FIELD]),
            .o_gfcm1_clka_sel             (clk_sta[`DDR_CMN_CLK_STA_GFCM1_CLKA_SEL_FIELD]),
            .o_gfcm1_clkb_sel             (clk_sta[`DDR_CMN_CLK_STA_GFCM1_CLKB_SEL_FIELD]),
            .i_gfcm_clksel                (core_gfm_sel),
            .i_phy_clk_ena                (phy_clk_ena),
            .i_gfcm_ena                   (gfcm_ena),
            .i_pll0_div_clk_byp           (pll0_div_clk_byp),
            .i_pll0_div_clk_rst           (pll0_div_clk_rst),
            .i_pll0_div_clk_ena           (pll0_div_clk_ena),
            .o_freeze_n_aon               (o_freeze_n_aon),
            .o_freeze_n_hv                (o_freeze_n_hv),
            .o_pll0_div_clk               (pll0_div_clk),
            .o_pmon_nand_clk              (pmon_nand_clk),
            .o_pmon_nor_clk               (pmon_nor_clk),

            .i_ddr_rstn                   (ddr_rst),
            .i_ddr_rstn_bs_din            (ddr_rstn_bs_din),
            .i_ddr_rstn_bs_ena            (ddr_rstn_bs_ena),
            .i_ddr_rstn_lpbk_ena          (ddr_rstn_cfg[`DDR_CMN_RSTN_CFG_RSTN_LPBK_ENA_FIELD]),
            .o_ddr_rstn_lpbk_out          (ddr_rstn_sta[`DDR_CMN_RSTN_STA_RSTN_LPBK_FIELD]),
            .pad_reset_n                  (pad_reset_n),

            .i_cmn_vref_cfg               (cmn_vref_cfg),
            .i_cmn_zqcal_cfg              (cmn_zqcal_cfg),
            .i_cmn_ibias_cfg              (cmn_ibias_cfg),
            .i_cmn_test_cfg               (cmn_test_cfg),
            .i_cmn_ldo_cfg                (cmn_ldo_cfg),
            .i_cmn_clk_ctrl_cfg           (cmn_clk_ctrl_cfg),
            .i_cmn_pmon_ana_cfg           (cmn_pmon_ana_cfg)
         );
      end else begin: NO_CMN
         assign o_pll_clk_0    = i_pll_clk_0;
         assign o_pll_clk_1    = i_pll_clk_1;
         assign o_pll_clk_2    = i_pll_clk_2;
         assign o_pll_clk_3    = i_pll_clk_3;
         assign o_vco0_clk     = i_vco0_clk;
         assign ana_vref_out   = ana_vref_in;
         assign o_freeze_n_aon = i_freeze_n_aon;
         assign o_freeze_n_hv  = i_freeze_n_hv;
         assign fbclk          = '0;
         assign refclk         = '0;
         assign vco0_div2_clk  = '0;
         assign vco1_div2_clk  = '0;
         assign vco2_div2_clk  = '0;
         assign pll0_div_clk   = '0;

         assign ddr_rstn_sta[`DDR_CMN_RSTN_STA_RSTN_LPBK_FIELD]     = '0;
         assign zqcal_sta[`DDR_CMN_ZQCAL_STA_COMP_FIELD]            = '0;
         assign clk_sta[`DDR_CMN_CLK_STA_GFCM0_CLKA_SEL_FIELD]      = '0;
         assign clk_sta[`DDR_CMN_CLK_STA_GFCM0_CLKB_SEL_FIELD]      = '0;
         assign clk_sta[`DDR_CMN_CLK_STA_GFCM1_CLKA_SEL_FIELD]      = '0;
         assign clk_sta[`DDR_CMN_CLK_STA_GFCM1_CLKB_SEL_FIELD]      = '0;
      end
   endgenerate

   // ------------------------------------------------------------------------
   // PLL Digital
   // ------------------------------------------------------------------------
   logic sel_refclk_alt ;
   logic mvp_vco0_byp_clk_sel;
   logic mvp_vco1_byp_clk_sel;
   logic mvp_vco2_byp_clk_sel;

   assign pll_cfg[`DDR_CMN_PLL_SEL_REFCLK_ALT_FIELD]    = sel_refclk_alt       | i_scan_mode ;
   assign pll_cfg[`DDR_CMN_PLL_VCO0_BYP_CLK_SEL_FIELD]  = mvp_vco0_byp_clk_sel | i_scan_mode ;
   assign pll_cfg[`DDR_CMN_PLL_VCO1_BYP_CLK_SEL_FIELD]  = mvp_vco1_byp_clk_sel | i_scan_mode ;
   assign pll_cfg[`DDR_CMN_PLL_VCO2_BYP_CLK_SEL_FIELD]  = mvp_vco2_byp_clk_sel | i_scan_mode ;

   generate
      if (!SECONDARY_PHY) begin: PLL_DIG
         mvp_pll_dig u_mvp_pll_dig (
            .core_scan_asyncrst_ctrl      (i_scan_rst_ctrl),
            .core_scan_clk                (scan_clk1),
            .core_scan_mode               (i_scan_mode),
            .core_scan_in                 (1'b0),                       // FIXME
            .core_scan_out                (),                           // FIXME

            .iddq_mode                    (i_iddq_mode),

            .bscan_mode                   (i_bscan_mode),
            .bscan_tck                    (i_bscan_tck),
            .bscan_trst_n                 (i_bscan_trst_n),
            .bscan_capturedr              (i_bscan_capturedr),
            .bscan_shiftdr                (i_bscan_shiftdr),
            .bscan_updatedr               (i_bscan_updatedr),
            .bscan_tdi                    (i_bscan_tdi),
            .bscan_tdo                    (o_bscan_tdo),

            // AHB Slave
            .hclk                         (i_hclk),
            .hreset                       (i_hreset),
            .hsel                         (pll_hsel),
            .hwrite                       (pll_hwrite),
            .htrans                       (pll_htrans),
            .hsize                        (pll_hsize),
            .hburst                       (pll_hburst),
            .haddr                        (pll_haddr[7:0]),
            .hwdata                       (pll_hwdata),
            .hrdata                       (pll_hrdata),
            .hresp                        (pll_hresp),
            .hready                       (pll_hready),

            //Core
            .core_reset                   (core_reset),                   // input
            .core_vco_sel                 (core_vco_sel),                 // input [1:0] - 2'b10 (VCO2), 2'b01 (VCO1), 2'b00 (VCO0)
                                                                          //    * The VCO_SEL can be static for back-to-back swithes.
            .core_switch_vco              (core_switch_vco),              // input
            .core_gfcm_sel                (/*OPEN*/),                     // output
            .core_initial_switch_done     (o_cmn_switch_done),            // output - FLL locked
            .core_ready                   (core_ready),                   // output - PLL locked
            .core_debug_bus_ctrl_status   (core_debug_bus_ctrl_status),   // output

            .interrupt                    (o_pll_irq),

            // Analog
            .mvp_bias_lvl                 (pll_cfg[`DDR_CMN_PLL_BIAS_LVL_FIELD]),
            .mvp_bias_sel                 (/*OPEN*/),
            .mvp_cp_int_mode              (pll_cfg[`DDR_CMN_PLL_CP_INT_MODE_FIELD]),

            .mvp_en                       (pll_cfg[`DDR_CMN_PLL_EN_FIELD]),
            .mvp_fbclk                    (fbclk),
            .mvp_fbdiv_sel                (pll_cfg[`DDR_CMN_PLL_FBDIV_SEL_FIELD]),
            .mvp_int_ctrl                 (pll_cfg[`DDR_CMN_PLL_INT_CTRL_FIELD]),
            .mvp_prop_ctrl                (pll_cfg[`DDR_CMN_PLL_PROP_CTRL_FIELD]),
            .mvp_pfd_mode                 (pll_cfg[`DDR_CMN_PLL_PFD_MODE_FIELD]),
            .mvp_prop_c_ctrl              (pll_cfg[`DDR_CMN_PLL_PROP_C_CTRL_FIELD]),
            .mvp_prop_r_ctrl              (pll_cfg[`DDR_CMN_PLL_PROP_R_CTRL_FIELD]),
            .mvp_refclk                   (refclk),
            .mvp_reset                    (mvp_reset),
            .mvp_sel_refclk_alt           (sel_refclk_alt),
            .mvp_div16_ena                (pll_cfg[`DDR_CMN_PLL_DIV16_EN_FIELD]),

            .mvp_vco0_div2clk             (vco0_div2_clk),
            .mvp_vco0_band                (pll_cfg[`DDR_CMN_PLL_VCO0_BAND_FIELD]),
            .mvp_vco0_fine                (pll_cfg[`DDR_CMN_PLL_VCO0_FINE_FIELD]),
            .mvp_vco0_byp_clk_sel         (mvp_vco0_byp_clk_sel),
            .mvp_vco0_ena                 (pll_cfg[`DDR_CMN_PLL_VCO0_ENA_FIELD]),

            .mvp_vco1_div2clk             (vco1_div2_clk),
            .mvp_vco1_band                (pll_cfg[`DDR_CMN_PLL_VCO1_BAND_FIELD]),
            .mvp_vco1_fine                (pll_cfg[`DDR_CMN_PLL_VCO1_FINE_FIELD]),
            .mvp_vco1_byp_clk_sel         (mvp_vco1_byp_clk_sel),
            .mvp_vco1_ena                 (pll_cfg[`DDR_CMN_PLL_VCO1_ENA_FIELD]),
            .mvp_vco1_post_div            (pll_cfg[`DDR_CMN_PLL_VCO1_POST_DIV_FIELD]),

            .mvp_vco2_div2clk             (vco2_div2_clk),
            .mvp_vco2_band                (pll_cfg[`DDR_CMN_PLL_VCO2_BAND_FIELD]),
            .mvp_vco2_fine                (pll_cfg[`DDR_CMN_PLL_VCO2_FINE_FIELD]),
            .mvp_vco2_byp_clk_sel         (mvp_vco2_byp_clk_sel),
            .mvp_vco2_ena                 (pll_cfg[`DDR_CMN_PLL_VCO2_ENA_FIELD]),
            .mvp_vco2_post_div            (pll_cfg[`DDR_CMN_PLL_VCO2_POST_DIV_FIELD]),
            .mvp_vco_sel                  (pll_cfg[`DDR_CMN_PLL_VCO_SEL_FIELD])
         );
      end else begin: NO_PLL_DIG
         assign o_bscan_tdo                                  = i_bscan_tdi;
         assign pll_hrdata                                   = '0;
         assign pll_hresp                                    = '0;
         assign pll_hready                                   = '0;
         assign o_cmn_switch_done                            = i_cmn_switch_done;
         assign core_ready                                   = '0;
         assign core_debug_bus_ctrl_status                   = '0;
         assign o_pll_irq                                    = '0;
         assign mvp_reset                                    = '0;
         assign pll_cfg[`DDR_CMN_PLL_BIAS_LVL_FIELD]         = '0;
         assign pll_cfg[`DDR_CMN_PLL_CP_INT_MODE_FIELD]      = '0;
         assign pll_cfg[`DDR_CMN_PLL_EN_FIELD]               = '0;
         assign pll_cfg[`DDR_CMN_PLL_FBDIV_SEL_FIELD]        = '0;
         assign pll_cfg[`DDR_CMN_PLL_PFD_MODE_FIELD]         = '0;
         assign pll_cfg[`DDR_CMN_PLL_PROP_C_CTRL_FIELD]      = '0;
         assign pll_cfg[`DDR_CMN_PLL_PROP_R_CTRL_FIELD]      = '0;
         assign pll_cfg[`DDR_CMN_PLL_SEL_REFCLK_ALT_FIELD]   = '0;
         assign pll_cfg[`DDR_CMN_PLL_VCO0_BAND_FIELD]        = '0;
         assign pll_cfg[`DDR_CMN_PLL_VCO0_ENA_FIELD]         = '0;
         assign pll_cfg[`DDR_CMN_PLL_VCO1_BAND_FIELD]        = '0;
         assign pll_cfg[`DDR_CMN_PLL_VCO1_BYP_CLK_SEL_FIELD] = '0;
         assign pll_cfg[`DDR_CMN_PLL_VCO1_ENA_FIELD]         = '0;
         assign pll_cfg[`DDR_CMN_PLL_VCO1_POST_DIV_FIELD]    = '0;
         assign pll_cfg[`DDR_CMN_PLL_VCO2_BAND_FIELD]        = '0;
         assign pll_cfg[`DDR_CMN_PLL_VCO2_BYP_CLK_SEL_FIELD] = '0;
         assign pll_cfg[`DDR_CMN_PLL_VCO2_ENA_FIELD]         = '0;
         assign pll_cfg[`DDR_CMN_PLL_VCO2_POST_DIV_FIELD]    = '0;
         assign pll_cfg[`DDR_CMN_PLL_VCO_SEL_FIELD]          = '0;
         assign pll_cfg[`DDR_CMN_PLL_DIV16_EN_FIELD]         = '0;
         assign pll_cfg[`DDR_CMN_PLL_VCO0_BYP_CLK_SEL_FIELD] = '0;
         assign pll_cfg[`DDR_CMN_PLL_INT_CTRL_FIELD]         = '0;
         assign pll_cfg[`DDR_CMN_PLL_PROP_CTRL_FIELD]        = '0;
         assign pll_cfg[`DDR_CMN_PLL_VCO0_FINE_FIELD]        = '0;
         assign pll_cfg[`DDR_CMN_PLL_VCO1_FINE_FIELD]        = '0;
         assign pll_cfg[`DDR_CMN_PLL_VCO2_FINE_FIELD]        = '0;
      end
   endgenerate

   // ------------------------------------------------------------------------
   // PMON digital
   // ------------------------------------------------------------------------

   ddr_pmon_dig u_pmon_dig (
                     .core_scan_asyncrst_ctrl         (i_scan_rst_ctrl),
                     .core_scan_mode                  (i_scan_mode),
                     .core_scan_in                    (i_scan_in),
                     .core_scan_shift                 (i_scan_shift),
                     .core_scan_clk                   (scan_clk1),
                     .core_scan_out                   (o_scan_out),

                     .i_pmon_nand_clk                 (pmon_nand_clk),
                     .i_pmon_nor_clk                  (pmon_nor_clk),
                     .i_pmon_en_nor                   (cmn_pmon_dig_nor_cfg[`DDR_CMN_PMON_DIG_NOR_CFG_COUNT_EN_FIELD]),
                     .i_pmon_en_nand                  (cmn_pmon_dig_nand_cfg[`DDR_CMN_PMON_DIG_NAND_CFG_COUNT_EN_FIELD]),
                     .i_refclk                        (i_refclk),
                     .i_refclk_rst                    (cmn_pmon_dig_cfg[`DDR_CMN_PMON_DIG_CFG_REFCLK_RST_FIELD]),
                     .i_initwait                      (cmn_pmon_dig_cfg[`DDR_CMN_PMON_DIG_CFG_INITWAIT_FIELD]),
                     .i_pmon_refcount_nor             (cmn_pmon_dig_nor_cfg[`DDR_CMN_PMON_DIG_NOR_CFG_REFCOUNT_FIELD]),
                     .i_pmon_refcount_nand            (cmn_pmon_dig_nand_cfg[`DDR_CMN_PMON_DIG_NAND_CFG_REFCOUNT_FIELD]),
                     .o_pmon_done_nor                 (cmn_pmon_nor_sta[`DDR_CMN_PMON_NOR_STA_DONE_FIELD]),
                     .o_pmon_done_nand                (cmn_pmon_nand_sta[`DDR_CMN_PMON_NAND_STA_DONE_FIELD]),
                     .o_pmon_count_nor                (cmn_pmon_nor_sta[`DDR_CMN_PMON_NOR_STA_COUNT_FIELD]),
                     .o_pmon_count_nand               (cmn_pmon_nand_sta[`DDR_CMN_PMON_NAND_STA_COUNT_FIELD])
                     //output o_ana_nand_en,
                     //output o_ana_nor_en
   );

   // ------------------------------------------------------------------------
   // CSR Wrapper
   // ------------------------------------------------------------------------

   ddr_cmn_csr_wrapper #(
      .AWIDTH                       (AWIDTH),
      .DWIDTH                       (DWIDTH)
   ) u_cmn_csr_wrapper (
      .i_hclk                       (i_hclk),
      .i_hreset                     (i_hreset),
      .i_ahb_csr_rst                (i_ahb_csr_rst),

      .i_haddr                      (i_haddr),
      .i_hwrite                     (i_hwrite),
      .i_hsel                       (i_hsel),
      .i_hwdata                     (i_hwdata),
      .i_htrans                     (i_htrans),
      .i_hsize                      (i_hsize),
      .i_hburst                     (i_hburst),
      .i_hreadyin                   (i_hreadyin),
      .o_hready                     (o_hready),
      .o_hrdata                     (o_hrdata),
      .o_hresp                      (o_hresp ),

      .o_pll_haddr                  (pll_haddr),
      .o_pll_hwrite                 (pll_hwrite),
      .o_pll_hsel                   (pll_hsel),
      .o_pll_hwdata                 (pll_hwdata),
      .o_pll_htrans                 (pll_htrans),
      .o_pll_hsize                  (pll_hsize),
      .o_pll_hburst                 (pll_hburst),
      .o_pll_hreadyin               (pll_hreadyin),
      .i_pll_hready                 (pll_hready),
      .i_pll_hrdata                 (pll_hrdata),
      .i_pll_hresp                  (pll_hresp),

      .i_msr                        (o_cmn_msr),

      .o_fsw_debug_cfg              (fsw_debug_cfg),
      .o_fsw_csp_0_cfg              (fsw_csp_0_cfg),
      .o_fsw_csp_1_cfg              (fsw_csp_1_cfg),
      .i_fsw_csp_sta                (fsw_csp_sta),
      .o_fsw_ctrl_cfg               (fsw_ctrl_cfg),
      .i_fsw_ctrl_sta               (fsw_ctrl_sta),
      .i_cmn_zqcal_sta              (zqcal_sta),
      .i_cmn_clk_sta                (clk_sta),
      .o_cmn_vref_cfg               (cmn_vref_cfg),
      .o_cmn_zqcal_cfg              (cmn_zqcal_cfg),
      .o_cmn_ibias_cfg              (cmn_ibias_cfg),
      .o_cmn_test_cfg               (cmn_test_cfg),
      .o_cmn_ldo_cfg                (cmn_ldo_cfg),
      .o_cmn_clk_ctrl_cfg           (cmn_clk_ctrl_cfg),
      .i_cmn_pmon_nand_sta          (cmn_pmon_nand_sta),
      .i_cmn_pmon_nor_sta           (cmn_pmon_nor_sta),
      .o_cmn_pmon_dig_nand_cfg      (cmn_pmon_dig_nand_cfg),
      .o_cmn_pmon_dig_nor_cfg       (cmn_pmon_dig_nor_cfg),
      .o_cmn_pmon_ana_cfg           (cmn_pmon_ana_cfg),
      .o_cmn_pmon_dig_cfg           (cmn_pmon_dig_cfg),
      .i_ddr_rstn_sta               (ddr_rstn_sta),
      .o_ddr_rstn_cfg               (ddr_rstn_cfg)
   );

   // ------------------------------------------------------------------------
   // Clock Stop
   // ------------------------------------------------------------------------

   logic csp_req, csp_req_complete;
   logic [2:0] sta_csp_fsm_state;

   ddr_clk_stop_sync u_csp_sync (
     .i_clk                         (o_pll0_div_clk),
     .i_rst                         (i_rst),
     .i_scan_mode                   (i_scan_mode),
     .i_scan_rst_ctrl               (i_scan_rst_ctrl),
     .i_scan_cgc_ctrl               (i_scan_cgc_ctrl),
     .i_dfi_clk_on                  (i_dfi_clk_on),
     .i_csp_0_cfg                   (fsw_csp_0_cfg),
     .i_csp_1_cfg                   (fsw_csp_1_cfg),
     .o_csp_sta                     (fsw_csp_sta),
     .i_csp_req                     (csp_req),
     .o_csp_req_complete            (csp_req_complete),
     .o_csp_clk_en                  (csp_clk_en),
     .o_csp_div_rst_n               (o_csp_div_rst_n),
     .o_csp_pi_en                   (o_csp_pi_en),
     .o_sta_fsm_state               (sta_csp_fsm_state),
     .o_csp_clk_on                  (csp_clk_on)
   );

   assign phy_clk_ena = csp_clk_en | i_scan_cgc_ctrl ;

   // ------------------------------------------------------------------------
   // Frequency Switch
   // ------------------------------------------------------------------------

   logic vco_sel;
   logic cmn_msr;
   logic [2:0] sta_fsw_fsm_state;

   ddr_freq_sw u_freq_sw (
      .i_clk                        (o_pll0_div_clk),
      .i_rst                        (i_rst),
      .i_dfi_init_start             (i_dfi_init_start),
      .i_prep_done                  (fsw_ctrl_cfg[`DDR_FSW_CTRL_CFG_PREP_DONE_FIELD]),
      .i_pstwork_done               (fsw_ctrl_cfg[`DDR_FSW_CTRL_CFG_PSTWORK_DONE_FIELD]),
      .i_pstwork_done_ovr           (fsw_ctrl_cfg[`DDR_FSW_CTRL_CFG_PSTWORK_DONE_OVR_FIELD]),
      .i_switch_done                (o_cmn_switch_done),
      .i_switch_done_ovr            (fsw_ctrl_cfg[`DDR_FSW_CTRL_CFG_SWITCH_DONE_OVR_FIELD]),
      .i_csp_req_complete           (csp_req_complete),
      .i_vco_toggle_en              (fsw_ctrl_cfg[`DDR_FSW_CTRL_CFG_VCO_TOGGLE_EN_FIELD]),
      .i_msr_toggle_en              (fsw_ctrl_cfg[`DDR_FSW_CTRL_CFG_MSR_TOGGLE_EN_FIELD]),
      .i_csr_post_gfmsel_wait       (fsw_ctrl_cfg[`DDR_FSW_CTRL_CFG_POST_GFMSEL_WAIT_FIELD]),
      .o_vco_sel                    (vco_sel),
      .o_switch_vco                 (core_switch_vco),
      .o_msr                        (cmn_msr),
      .o_csp_req                    (csp_req),
      .o_init_complete              (o_cmn_init_complete),
      .o_sta_fsm_state              (sta_fsw_fsm_state)
   );

   assign core_vco_sel = fsw_ctrl_cfg[`DDR_FSW_CTRL_CFG_VCO_SEL_OVR_FIELD] ?
                         fsw_ctrl_cfg[`DDR_FSW_CTRL_CFG_VCO_SEL_OVR_VAL_FIELD] :
                         vco_sel ? 2'b10 : 2'b01 ;
   assign o_cmn_msr    = fsw_ctrl_cfg[`DDR_FSW_CTRL_CFG_MSR_OVR_FIELD] ?
                         fsw_ctrl_cfg[`DDR_FSW_CTRL_CFG_MSR_OVR_VAL_FIELD] :
                         cmn_msr ;

   assign core_gfm_sel = ((core_vco_sel == 2'b10) & (i_scan_mode == 1'b0)) ? 1'b1 : 1'b0 ;

   logic cmn_switch_done_sticky;
   ddr_sticky_reg u_stick_reg (
      .i_clk                        (i_hclk),
      .i_rst                        (i_hreset),
      .i_clr                        (fsw_ctrl_cfg[`DDR_FSW_CTRL_CFG_SWITCH_DONE_STICKY_CLR_FIELD]),
      .i_d                          (o_cmn_switch_done),
      .o_q                          (cmn_switch_done_sticky)
   );

   assign fsw_ctrl_sta[`DDR_FSW_CTRL_STA_VCO_SEL_FIELD    ] = core_vco_sel;
   assign fsw_ctrl_sta[`DDR_FSW_CTRL_STA_SWITCH_DONE_FIELD] = cmn_switch_done_sticky;
   assign fsw_ctrl_sta[`DDR_FSW_CTRL_STA_CMN_MSR_FIELD    ] = o_cmn_msr;
   assign fsw_ctrl_sta[`DDR_FSW_CTRL_STA_CORE_READY_FIELD ] = core_ready;

   // ------------------------------------------------------------------------
   // Debug
   // ------------------------------------------------------------------------
   logic [3:0] debug_bus_sel ;
   logic [31:0] fsw_debug ;

   assign debug_bus_sel = fsw_debug_cfg[`DDR_FSW_DEBUG_CFG_DEBUG_BUS_SEL_FIELD];

   assign o_debug = (debug_bus_sel == 4'd0) ? '0 :
                    (debug_bus_sel == 4'd1) ? core_debug_bus_ctrl_status :
                    (debug_bus_sel == 4'd2) ? fsw_debug :
                    32'd0 ;

   assign fsw_debug = { 16'b0,
                        cmn_msr,
                        vco_sel,
                        sta_csp_fsm_state,
                        csp_req_complete,
                        csp_req,
                        o_cmn_switch_done,
                        fsw_ctrl_cfg[`DDR_FSW_CTRL_CFG_PSTWORK_DONE_FIELD],
                        fsw_ctrl_cfg[`DDR_FSW_CTRL_CFG_PREP_DONE_FIELD],
                        o_cmn_init_complete,
                        i_dfi_init_start,
                        sta_fsw_fsm_state
                      };

endmodule

module ddr_freq_sw (
   input  logic       i_clk,
   input  logic       i_rst,
   input  logic       i_dfi_init_start,
   input  logic       i_prep_done,
   input  logic       i_pstwork_done,
   input  logic       i_pstwork_done_ovr,
   input  logic       i_switch_done,
   input  logic       i_switch_done_ovr,
   input  logic       i_csp_req_complete,
   input  logic       i_vco_toggle_en,
   input  logic       i_msr_toggle_en,
   input  logic [3:0] i_csr_post_gfmsel_wait,
   output logic       o_vco_sel,
   output logic       o_switch_vco,
   output logic       o_msr,
   output logic       o_csp_req,
   output logic       o_init_complete,
   output logic [2:0] o_sta_fsm_state
);

   logic pstwork_done_sync, pstwork_done_ovr_sync ;
   logic prep_done_sync, switch_done_sync, switch_done_sync_hold, switch_done_ovr_sync;
   logic msr_toggle_en_sync, vco_toggle_en_sync, csp_req_complete_sync;
   logic dfi_init_start_sync, dfi_init_start_sync_hold;

   // AHB clock is slower than DFI clock so use demet
   ddr_demet_r u_demet_0 (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_prep_done      ),  .o_q(prep_done_sync       )); // AHB clock
   ddr_demet_r u_demet_1 (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_pstwork_done   ),  .o_q(pstwork_done_sync    )); // AHB clock
   ddr_demet_r u_demet_2 (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_pstwork_done_ovr), .o_q(pstwork_done_ovr_sync)); // AHB clock
   ddr_demet_r u_demet_3 (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_switch_done_ovr),  .o_q(switch_done_ovr_sync )); // AHB clock
   ddr_demet_r u_demet_4 (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_msr_toggle_en  ),  .o_q(msr_toggle_en_sync   )); // AHB clock
   ddr_demet_r u_demet_5 (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_vco_toggle_en  ),  .o_q(vco_toggle_en_sync   )); // AHB clock
   ddr_demet_r u_demet_6 (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_dfi_init_start ),  .o_q(dfi_init_start_sync  )); // DFI clock

   // PLL lock should be held multiple cycles to meet clock nyquist so use demet
   ddr_demet_r u_demet_7 (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_switch_done ), .o_q(switch_done_sync )); // PLL clock

   // CSP clock is faster than DFI clock so use edge detect
   ddr_edge_det u_edge_det_0 (.i_clk(i_clk),.i_rst(i_rst),.i_async(i_csp_req_complete),.o_sync(csp_req_complete_sync),.o_sync_pulse());

   // ------------------------------------------------------------------------
   // FSM
   // ------------------------------------------------------------------------

   typedef enum logic [2:0] {
      PREP    ,
      PREWORK ,
      WORK_STG0,
      WORK_STG1,
      PSTWORK
   } fsm_t;

   fsm_t fsm_state_q, fsm_state_d;

   always_ff @(posedge i_clk, posedge i_rst)
      if (i_rst)
         fsm_state_q <= PREP;
      else
         fsm_state_q <= fsm_state_d;

   assign o_sta_fsm_state = fsm_state_q;

   logic csp_req, msr_toggle, vco_toggle, switch_vco;
   logic msr_q, vco_sel_q, csp_req_q, switch_vco_q;
   logic init_complete, init_complete_q;
   logic [3:0] cnt_d ;
   logic [3:0] cnt_q ;
   logic cnt_tc;

   assign cnt_tc = (cnt_q == '0) ;

   always_comb begin
      csp_req        = 1'b0;
      msr_toggle     = 1'b0;
      vco_toggle     = 1'b0;
      switch_vco     = 1'b0;
      init_complete  = 1'b0;
      fsm_state_d    = fsm_state_q;
      cnt_d          = cnt_q;

      case(fsm_state_q)
         PREP    : begin
                      if (dfi_init_start_sync_hold && prep_done_sync) begin
                         fsm_state_d = PREWORK;
                      end
                   end
         PREWORK : begin
                      fsm_state_d = WORK_STG0;
                      vco_toggle  = vco_toggle_en_sync;
                      msr_toggle  = msr_toggle_en_sync;
                      switch_vco = 1'b1;
                      cnt_d      = i_csr_post_gfmsel_wait ;
                   end
         WORK_STG0 : begin
                      switch_vco = 1'b1;
                      if (cnt_tc) begin
                         csp_req = 1'b1;
                         if(csp_req_complete_sync)
                            fsm_state_d = WORK_STG1;
                      end else begin
                         cnt_d = cnt_q - 'b1;
                      end
                   end
         WORK_STG1 : begin
                      switch_vco = 1'b1;
                      if ((switch_done_sync_hold || switch_done_ovr_sync)) begin
                         fsm_state_d = PSTWORK;
                      end
                   end
          PSTWORK : begin
                      if (!dfi_init_start_sync && (pstwork_done_sync | pstwork_done_ovr_sync) ) begin
                         fsm_state_d = PREP;
                         init_complete = 1'b1;
                      end else begin
                         switch_vco = 1'b1;
                      end
                   end
      endcase
   end

   always_ff @(posedge i_clk, posedge i_rst) begin
      if (i_rst) begin
         csp_req_q                <= '0;
         init_complete_q          <= '0;
         switch_vco_q             <= '0;
         cnt_q                    <= '0;
         switch_done_sync_hold    <= '0;
         dfi_init_start_sync_hold <= '0;
      end else begin
         cnt_q                    <= cnt_d;
         csp_req_q                <= csp_req;
         init_complete_q          <= init_complete;
         switch_vco_q             <= switch_vco;
         if (dfi_init_start_sync || (fsm_state_q != PREP))
            dfi_init_start_sync_hold <= dfi_init_start_sync ;
         if (switch_done_sync || (fsm_state_d == PREP))
            switch_done_sync_hold    <= switch_done_sync ;
      end
   end

   always_ff @(posedge i_clk, posedge i_rst) begin
      if (i_rst)
         msr_q <= '0;
      else if (msr_toggle)
            msr_q <= ~msr_q;
   end

   always_ff @(posedge i_clk, posedge i_rst) begin
      if (i_rst)
         vco_sel_q <= '0;
      else if (vco_toggle)
            vco_sel_q <= ~vco_sel_q;
   end

   assign o_msr           = msr_q;
   assign o_vco_sel       = vco_sel_q;
   assign o_switch_vco    = switch_vco_q;
   assign o_csp_req       = csp_req_q;
   assign o_init_complete = init_complete_q;

endmodule

module ddr_clk_stop_sync (
  input  logic                                i_clk,
  input  logic                                i_rst,
  input  logic                                i_scan_mode,
  input  logic                                i_scan_rst_ctrl,
  input  logic                                i_scan_cgc_ctrl,
  input  logic                                i_dfi_clk_on,
  input  logic                                i_csp_req,
  output logic                                o_csp_req_complete,
  output logic                                o_csp_clk_en,
  output logic                                o_csp_div_rst_n,
  output logic                                o_csp_pi_en,
  output logic                                o_csp_clk_on,
  output logic [2:0]                          o_sta_fsm_state,
  input  logic [`DDR_FSW_CSP_0_CFG_WIDTH-1:0] i_csp_0_cfg,
  input  logic [`DDR_FSW_CSP_1_CFG_WIDTH-1:0] i_csp_1_cfg,
  output logic [`DDR_FSW_CSP_STA_WIDTH-1:0]   o_csp_sta
);

   typedef enum logic [2:0] {
      IDLE       ,
      PI_DISABLE ,
      CLK_STOP   ,
      RST_HIGH   ,
      RST_LOW    ,
      CLK_START  ,
      PI_ENABLE
   } state_t;

   state_t state_q, state_d ;
   logic csp_req_asserted, csp_req;
   logic csp_busy_d, csp_busy_q;
   logic csp_req_q;
   logic csp_pi_en_d, csp_pi_en_q;
   logic csp_div_rst_d, csp_div_rst_q;
   logic csp_clk_en_d, csp_clk_en_q;
   logic dfi_clk_on_sync;
   logic csp_req_complete_d, csp_req_complete_q;
   logic cgc_en;
   logic [3:0] cnt_load_val, cnt_q, cnt_d;
   logic cnt_load_d;
   logic clkg;

   logic [3:0] csp_preclkdis_wait;
   logic [3:0] csp_prerst_wait;
   logic [3:0] csp_rst_pulse_width;
   logic [3:0] csp_pstrst_wait;
   logic [3:0] csp_pstclken_wait;
   logic [3:0] csp_pstpien_wait;
   logic       csp_req_complete_ovr;
   logic       csp_req_complete_ovr_val;
   logic       csp_req_ovr;
   logic       csp_req_ovr_val;
   logic       csp_cgc_en_ovr;
   logic       csp_cgc_en_ovr_val;
   logic       csp_pi_disable_ovr_val;
   logic       csp_div_rst_ovr_val;
   logic       csp_clk_disable_ovr_val;
   logic       csp_req_complete_sta_clr;

   logic       csp_req_sync;
   logic       csp_req_complete_ovr_sync;
   logic       csp_req_complete_ovr_val_sync;
   logic       csp_cgc_en_ovr_sync;
   logic       csp_cgc_en_ovr_val_sync;
   logic       csp_pi_disable_ovr_val_sync;
   logic       csp_div_rst_ovr_val_sync;
   logic       csp_clk_disable_ovr_val_sync;
   logic       csp_req_complete_sta_clr_sync;
   logic       csp_req_complete_hold_q;
   logic       csp_req_complete_hold_d;

   // Split CFG bus
   assign csp_preclkdis_wait         = i_csp_0_cfg[`DDR_FSW_CSP_0_CFG_PRECLKDIS_WAIT_FIELD];
   assign csp_prerst_wait            = i_csp_0_cfg[`DDR_FSW_CSP_0_CFG_PRERST_WAIT_FIELD];
   assign csp_rst_pulse_width        = i_csp_0_cfg[`DDR_FSW_CSP_0_CFG_RST_PULSE_WIDTH_FIELD];
   assign csp_pstrst_wait            = i_csp_0_cfg[`DDR_FSW_CSP_0_CFG_PSTRST_WAIT_FIELD];
   assign csp_pstclken_wait          = i_csp_0_cfg[`DDR_FSW_CSP_0_CFG_PSTCLKEN_WAIT_FIELD];
   assign csp_pstpien_wait           = i_csp_0_cfg[`DDR_FSW_CSP_0_CFG_PSTPIEN_WAIT_FIELD];
   assign csp_req_complete_ovr       = i_csp_1_cfg[`DDR_FSW_CSP_1_CFG_REQ_COMPLETE_OVR_FIELD];
   assign csp_req_complete_ovr_val   = i_csp_1_cfg[`DDR_FSW_CSP_1_CFG_REQ_COMPLETE_OVR_VAL_FIELD];
   assign csp_req_ovr                = i_csp_1_cfg[`DDR_FSW_CSP_1_CFG_REQ_OVR_FIELD];
   assign csp_req_ovr_val            = i_csp_1_cfg[`DDR_FSW_CSP_1_CFG_REQ_OVR_VAL_FIELD];
   assign csp_cgc_en_ovr             = i_csp_1_cfg[`DDR_FSW_CSP_1_CFG_CGC_EN_OVR_FIELD];
   assign csp_cgc_en_ovr_val         = i_csp_1_cfg[`DDR_FSW_CSP_1_CFG_CGC_EN_OVR_VAL_FIELD];
   assign csp_pi_disable_ovr_val     = i_csp_1_cfg[`DDR_FSW_CSP_1_CFG_PI_DISABLE_OVR_VAL_FIELD];
   assign csp_div_rst_ovr_val        = i_csp_1_cfg[`DDR_FSW_CSP_1_CFG_DIV_RST_OVR_VAL_FIELD];
   assign csp_clk_disable_ovr_val    = i_csp_1_cfg[`DDR_FSW_CSP_1_CFG_CLK_DISABLE_OVR_VAL_FIELD];
   assign csp_req_complete_sta_clr   = i_csp_1_cfg[`DDR_FSW_CSP_1_CFG_REQ_COMPLETE_STA_CLR_FIELD];

   assign o_csp_sta[`DDR_FSW_CSP_STA_REQ_COMPLETE_FIELD] = csp_req_complete_hold_q;
   // Sync CSR overrides.
   assign csp_req  = csp_req_ovr  ? csp_req_ovr_val: i_csp_req ;

   ddr_demet_r u_demet_0 (.i_clk(i_clk), .i_rst(i_rst), .i_d(csp_req                 ), .o_q(csp_req_sync                 ));
   ddr_demet_r u_demet_1 (.i_clk(i_clk), .i_rst(i_rst), .i_d(csp_cgc_en_ovr          ), .o_q(csp_cgc_en_ovr_sync          ));
   ddr_demet_r u_demet_2 (.i_clk(i_clk), .i_rst(i_rst), .i_d(csp_cgc_en_ovr_val      ), .o_q(csp_cgc_en_ovr_val_sync      ));
   ddr_demet_r u_demet_3 (.i_clk(i_clk), .i_rst(i_rst), .i_d(csp_pi_disable_ovr_val  ), .o_q(csp_pi_disable_ovr_val_sync  ));
   ddr_demet_r u_demet_4 (.i_clk(i_clk), .i_rst(i_rst), .i_d(csp_div_rst_ovr_val     ), .o_q(csp_div_rst_ovr_val_sync     ));
   ddr_demet_s u_demet_5 (.i_clk(i_clk), .i_set(i_rst), .i_d(csp_clk_disable_ovr_val ), .o_q(csp_clk_disable_ovr_val_sync ));
   ddr_demet_r u_demet_6 (.i_clk(i_clk), .i_rst(i_rst), .i_d(csp_req_complete_sta_clr), .o_q(csp_req_complete_sta_clr_sync));
   ddr_demet_r u_demet_7 (.i_clk(i_clk), .i_rst(i_rst), .i_d(csp_req_complete_ovr    ), .o_q(csp_req_complete_ovr_sync    ));
   ddr_demet_r u_demet_8 (.i_clk(i_clk), .i_rst(i_rst), .i_d(csp_req_complete_ovr_val), .o_q(csp_req_complete_ovr_val_sync));
   ddr_demet_r u_demet_9 (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_dfi_clk_on            ), .o_q(dfi_clk_on_sync              ));

   assign cgc_en       = csp_cgc_en_ovr_sync ? csp_cgc_en_ovr_val_sync : (csp_req_asserted | csp_busy_q | csp_req_complete_q) ;
   ddr_cgc_rl u_cgc_rl (.i_clk(i_clk), .i_clk_en(cgc_en), .i_cgc_en(i_scan_cgc_ctrl), .o_clk(clkg));

   // Outputs
   logic csp_div_rst, scan_csp_div_rst ;

   assign csp_div_rst             = (csp_div_rst_q | csp_div_rst_ovr_val_sync | i_rst)  ;

   ddr_scan_rst u_scan_csp_rst ( .i_scan_rst_ctrl(i_scan_rst_ctrl), .i_rst(csp_div_rst), .o_rst(scan_csp_div_rst));

   assign o_csp_clk_on            = cgc_en;
   assign o_csp_clk_en            = (csp_clk_en_q  & ~csp_clk_disable_ovr_val_sync) | i_scan_cgc_ctrl ;
   assign o_csp_div_rst_n         = ~scan_csp_div_rst ;
   assign o_csp_pi_en             = csp_pi_en_q   & ~csp_pi_disable_ovr_val_sync ;
   assign o_csp_req_complete      = csp_req_complete_ovr_sync ? csp_req_complete_ovr_val_sync : csp_req_complete_q ;

   // FSM
   assign csp_req_complete_hold_d = csp_req_complete_sta_clr_sync ? '0 : o_csp_req_complete ? o_csp_req_complete : csp_req_complete_hold_q ;

   always_ff @(posedge i_clk, posedge i_rst) begin
      if(i_rst) begin
         csp_req_q               <= '0;
         csp_clk_en_q            <= '1;
         csp_req_complete_hold_q <= '0;
      end else begin
         csp_req_q                <= csp_req_sync;
         csp_clk_en_q             <= dfi_clk_on_sync | csp_clk_en_d;
         csp_req_complete_hold_q  <= csp_req_complete_hold_d;
      end
   end

   always_ff @(posedge clkg, posedge i_rst) begin
      if(i_rst)
         state_q <= IDLE;
      else
         state_q <= state_d;
   end

   assign o_sta_fsm_state = state_q;

   assign csp_req_asserted    = csp_req_sync & ~csp_req_q ;

   always_comb begin
      state_d                 = state_q;
      csp_busy_d              = csp_busy_q | csp_req_asserted;
      csp_pi_en_d             = csp_pi_en_q;
      csp_div_rst_d           = csp_div_rst_q;
      csp_clk_en_d            = csp_clk_en_q;
      csp_req_complete_d      = '0;
      cnt_load_d              = csp_req_asserted;
      case(state_q)
         IDLE: begin
            if(csp_busy_q) begin
              state_d             = PI_DISABLE;
              csp_pi_en_d         = 1'b0;
              cnt_load_d          = 1'b1;
            end
         end
         PI_DISABLE: begin
            if(cnt_q == '0) begin
               state_d            = CLK_STOP;
               csp_pi_en_d        = 1'b0;
               csp_clk_en_d       = 1'b0;
               cnt_load_d         = 1'b1;
            end
         end
         CLK_STOP : begin
            if(cnt_q == '0) begin
               state_d            = RST_HIGH;
               csp_pi_en_d        = 1'b0;
               csp_clk_en_d       = 1'b0;
               csp_div_rst_d      = 1'b1;
               cnt_load_d         = 1'b1;
            end
         end
         RST_HIGH : begin
            if(cnt_q == '0) begin
               state_d            = RST_LOW;
               csp_pi_en_d        = 1'b0;
               csp_clk_en_d       = 1'b0;
               csp_div_rst_d      = 1'b0;
               cnt_load_d         = 1'b1;
            end
         end
         RST_LOW : begin
            if(cnt_q == '0) begin
               state_d            = CLK_START;
               csp_pi_en_d        = 1'b0;
               csp_clk_en_d       = 1'b1;
               csp_div_rst_d      = 1'b0;
               cnt_load_d         = 1'b1;
            end
         end
         CLK_START : begin
            if(cnt_q == '0) begin
               state_d            = PI_ENABLE;
               csp_pi_en_d        = 1'b1;
               csp_clk_en_d       = 1'b1;
               csp_div_rst_d      = 1'b0;
               cnt_load_d         = 1'b1;
            end
         end
         PI_ENABLE : begin
            if(cnt_q == '0) begin
               state_d            = IDLE;
               csp_pi_en_d        = 1'b1;
               csp_clk_en_d       = 1'b1;
               csp_div_rst_d      = 1'b0;
               csp_busy_d         = 1'b0;
               csp_req_complete_d = 1'b1;
               cnt_load_d         = 1'b0;
            end
         end
      endcase
   end

   always_ff @(posedge clkg, posedge i_rst) begin
      if(i_rst) begin
         csp_busy_q          <= '0;
         csp_pi_en_q         <= '1;
         csp_div_rst_q       <= '0;
         csp_req_complete_q  <= '0;
      end else begin
         csp_busy_q          <= csp_busy_d;
         csp_pi_en_q         <= csp_pi_en_d;
         csp_div_rst_q       <= csp_div_rst_d;
         csp_req_complete_q  <= csp_req_complete_d;
      end
   end

   always_comb begin
      case(state_d)
         PI_DISABLE : cnt_load_val = csp_preclkdis_wait ;
         CLK_STOP   : cnt_load_val = csp_prerst_wait    ;
         RST_HIGH   : cnt_load_val = csp_rst_pulse_width;
         RST_LOW    : cnt_load_val = csp_pstrst_wait    ;
         CLK_START  : cnt_load_val = csp_pstclken_wait  ;
         PI_ENABLE  : cnt_load_val = csp_pstpien_wait   ;
         default    : cnt_load_val = csp_preclkdis_wait ;
      endcase
   end

   always_ff @ (posedge clkg, posedge i_rst) begin
      if(i_rst)
         cnt_q <= '0;
      else
         cnt_q <= cnt_d;
   end

   assign cnt_d = cnt_load_d ? cnt_load_val : (cnt_q !='0) ? cnt_q - 'b1 : cnt_q ;

endmodule

module ddr_cmn_csr_wrapper #(
   parameter AWIDTH = 32,
   parameter DWIDTH = 32
) (

   input   logic                i_ahb_csr_rst,
   input   logic                i_hclk,
   input   logic                i_hreset,
   input   logic [AWIDTH-1:0]   i_haddr,
   input   logic                i_hwrite,
   input   logic                i_hsel,
   input   logic [DWIDTH-1:0]   i_hwdata,
   input   logic [1:0]          i_htrans,
   input   logic [2:0]          i_hsize,
   input   logic [2:0]          i_hburst,
   input   logic                i_hreadyin,
   output  logic                o_hready,
   output  logic [DWIDTH-1:0]   o_hrdata,
   output  logic [1:0]          o_hresp,

   output  logic [AWIDTH-1:0]   o_pll_haddr,
   output  logic                o_pll_hwrite,
   output  logic                o_pll_hsel,
   output  logic                o_pll_hreadyin,
   output  logic [DWIDTH-1:0]   o_pll_hwdata,
   output  logic [1:0]          o_pll_htrans,
   output  logic [2:0]          o_pll_hsize,
   output  logic [2:0]          o_pll_hburst,
   input   logic                i_pll_hready,
   input   logic [DWIDTH-1:0]   i_pll_hrdata,
   input   logic [1:0]          i_pll_hresp,

   input   logic                i_msr,

   output  logic [`DDR_FSW_DEBUG_CFG_WIDTH-1:0]     o_fsw_debug_cfg,
   output  logic [`DDR_FSW_CSP_0_CFG_WIDTH-1:0]     o_fsw_csp_0_cfg,
   output  logic [`DDR_FSW_CSP_1_CFG_WIDTH-1:0]     o_fsw_csp_1_cfg,
   input   logic [`DDR_FSW_CSP_STA_WIDTH-1:0]       i_fsw_csp_sta,
   output  logic [`DDR_FSW_CTRL_CFG_RANGE]          o_fsw_ctrl_cfg,
   input   logic [`DDR_FSW_CTRL_STA_RANGE]          i_fsw_ctrl_sta,

   input   logic [`DDR_CMN_CLK_STA_RANGE]           i_cmn_clk_sta,
   input   logic [`DDR_CMN_ZQCAL_STA_RANGE]         i_cmn_zqcal_sta,
   input   logic [`DDR_CMN_PMON_NAND_STA_RANGE]     i_cmn_pmon_nand_sta,
   input   logic [`DDR_CMN_PMON_NOR_STA_RANGE]      i_cmn_pmon_nor_sta,
   output  logic [`DDR_CMN_VREF_M0_CFG_RANGE]       o_cmn_vref_cfg,
   output  logic [`DDR_CMN_ZQCAL_CFG_RANGE]         o_cmn_zqcal_cfg,
   output  logic [`DDR_CMN_IBIAS_CFG_RANGE]         o_cmn_ibias_cfg,
   output  logic [`DDR_CMN_TEST_CFG_RANGE]          o_cmn_test_cfg,
   output  logic [`DDR_CMN_LDO_M0_CFG_RANGE]        o_cmn_ldo_cfg,
   output  logic [`DDR_CMN_CLK_CTRL_CFG_RANGE]      o_cmn_clk_ctrl_cfg,
   output  logic [`DDR_CMN_PMON_ANA_CFG_RANGE]      o_cmn_pmon_ana_cfg,
   output  logic [`DDR_CMN_PMON_DIG_CFG_RANGE]      o_cmn_pmon_dig_cfg,
   output  logic [`DDR_CMN_PMON_DIG_NAND_CFG_RANGE] o_cmn_pmon_dig_nand_cfg,
   output  logic [`DDR_CMN_PMON_DIG_NOR_CFG_RANGE]  o_cmn_pmon_dig_nor_cfg,
   output  logic [`DDR_CMN_RSTN_CFG_RANGE]          o_ddr_rstn_cfg,
   input   logic [`DDR_CMN_RSTN_STA_RANGE]          i_ddr_rstn_sta
);

   localparam NUM_INTF_SLVS = 3;
   localparam INTF_SWIDTH   = $clog2(NUM_INTF_SLVS)+1;
   localparam CMN_SLV_IDX   = 0 ;
   localparam PLL_SLV_IDX   = 1 ;
   localparam FSW_SLV_IDX   = 2 ;

   logic [AWIDTH*NUM_INTF_SLVS-1:0]         int_slv_mux_haddr ;
   logic [NUM_INTF_SLVS-1:0]                int_slv_mux_hwrite;
   logic [NUM_INTF_SLVS-1:0]                int_slv_mux_hsel  ;
   logic [DWIDTH*NUM_INTF_SLVS-1:0]         int_slv_mux_hwdata;
   logic [2*NUM_INTF_SLVS-1:0]              int_slv_mux_htrans;
   logic [3*NUM_INTF_SLVS-1:0]              int_slv_mux_hsize ;
   logic [3*NUM_INTF_SLVS-1:0]              int_slv_mux_hburst;
   logic [NUM_INTF_SLVS-1:0]                int_slv_mux_hready;
   logic [NUM_INTF_SLVS-1:0]                int_slv_mux_hreadyin;
   logic [DWIDTH*NUM_INTF_SLVS-1:0]         int_slv_mux_hrdata;
   logic [2*NUM_INTF_SLVS-1:0]              int_slv_mux_hresp ;
   logic [INTF_SWIDTH-1:0]                  slv_sel ;

   logic [`DDR_CMN_VREF_M0_CFG_RANGE]       cmn_vref_cfg;
   logic [`DDR_CMN_VREF_M0_CFG_RANGE]       cmn_vref_m0_cfg;
   logic [`DDR_CMN_VREF_M1_CFG_RANGE]       cmn_vref_m1_cfg;
   logic [`DDR_CMN_ZQCAL_CFG_RANGE]         cmn_zqcal_cfg;
   logic [`DDR_CMN_TEST_CFG_RANGE]          cmn_test_cfg;
   logic [`DDR_CMN_IBIAS_CFG_RANGE]         cmn_ibias_cfg;
   logic [`DDR_CMN_LDO_M0_CFG_RANGE]        cmn_ldo_cfg;
   logic [`DDR_CMN_LDO_M0_CFG_RANGE]        cmn_ldo_m0_cfg;
   logic [`DDR_CMN_LDO_M1_CFG_RANGE]        cmn_ldo_m1_cfg;
   logic [`DDR_CMN_CLK_CTRL_CFG_RANGE]      cmn_clk_ctrl_cfg;
   logic [`DDR_CMN_PMON_ANA_CFG_RANGE]      cmn_pmon_ana_cfg;
   logic [`DDR_CMN_PMON_DIG_CFG_RANGE]      cmn_pmon_dig_cfg;
   logic [`DDR_CMN_PMON_DIG_NAND_CFG_RANGE] cmn_pmon_dig_nand_cfg;
   logic [`DDR_CMN_PMON_DIG_NOR_CFG_RANGE]  cmn_pmon_dig_nor_cfg;

   assign cmn_vref_cfg =  i_msr ? cmn_vref_m1_cfg : cmn_vref_m0_cfg;
   assign cmn_ldo_cfg  =  i_msr ? cmn_ldo_m1_cfg  : cmn_ldo_m0_cfg;

   assign o_cmn_vref_cfg          = cmn_vref_cfg;
   assign o_cmn_zqcal_cfg         = cmn_zqcal_cfg;
   assign o_cmn_ibias_cfg         = cmn_ibias_cfg;
   assign o_cmn_test_cfg          = cmn_test_cfg;
   assign o_cmn_ldo_cfg           = cmn_ldo_cfg;
   assign o_cmn_clk_ctrl_cfg      = cmn_clk_ctrl_cfg;
   assign o_cmn_pmon_ana_cfg      = cmn_pmon_ana_cfg;
   assign o_cmn_pmon_dig_cfg      = cmn_pmon_dig_cfg;
   assign o_cmn_pmon_dig_nand_cfg = cmn_pmon_dig_nand_cfg;
   assign o_cmn_pmon_dig_nor_cfg  = cmn_pmon_dig_nor_cfg;

   logic [AWIDTH-1:0]   fsw_haddr;
   logic                fsw_hwrite;
   logic                fsw_hsel;
   logic [DWIDTH-1:0]   fsw_hwdata;
   logic [1:0]          fsw_htrans;
   logic [2:0]          fsw_hsize;
   logic [2:0]          fsw_hburst;
   logic                fsw_hready;
   logic                fsw_hreadyin;
   logic [DWIDTH-1:0]   fsw_hrdata;
   logic [1:0]          fsw_hresp;

   logic [AWIDTH-1:0]   cmn_haddr;
   logic                cmn_hwrite;
   logic                cmn_hsel;
   logic [DWIDTH-1:0]   cmn_hwdata;
   logic [1:0]          cmn_htrans;
   logic [2:0]          cmn_hsize;
   logic [2:0]          cmn_hburst;
   logic                cmn_hready;
   logic                cmn_hreadyin;
   logic [DWIDTH-1:0]   cmn_hrdata;
   logic [1:0]          cmn_hresp;
   logic [AWIDTH-1:0]   haddr_offset;
   logic [AWIDTH-1:0]   haddr_local;

   assign {fsw_haddr   , o_pll_haddr   ,  cmn_haddr    } =  int_slv_mux_haddr ;
   assign {fsw_hwrite  , o_pll_hwrite  ,  cmn_hwrite   } =  int_slv_mux_hwrite;
   assign {fsw_hsel    , o_pll_hsel    ,  cmn_hsel     } =  int_slv_mux_hsel  ;
   assign {fsw_hreadyin, o_pll_hreadyin,  cmn_hreadyin } =  int_slv_mux_hreadyin  ;
   assign {fsw_hwdata  , o_pll_hwdata  ,  cmn_hwdata   } =  int_slv_mux_hwdata;
   assign {fsw_htrans  , o_pll_htrans  ,  cmn_htrans   } =  int_slv_mux_htrans;
   assign {fsw_hsize   , o_pll_hsize   ,  cmn_hsize    } =  int_slv_mux_hsize ;
   assign {fsw_hburst  , o_pll_hburst  ,  cmn_hburst   } =  int_slv_mux_hburst;

   assign int_slv_mux_hready  = {fsw_hready, i_pll_hready,  cmn_hready};
   assign int_slv_mux_hrdata  = {fsw_hrdata, i_pll_hrdata,  cmn_hrdata};
   assign int_slv_mux_hresp   = {fsw_hresp,  i_pll_hresp,   cmn_hresp };

   //Slave sel and slave decode
   assign slv_sel = (i_haddr < (DDR_PLL_OFFSET-DDR_CMN_OFFSET)) ? ('b1+CMN_SLV_IDX) :
                    (( i_haddr >= (DDR_PLL_OFFSET-DDR_CMN_OFFSET)) && (i_haddr < (DDR_FSW_OFFSET-DDR_CMN_OFFSET)))  ? ('b1+PLL_SLV_IDX) :
                    (( i_haddr >= (DDR_FSW_OFFSET-DDR_CMN_OFFSET)) && (i_haddr < (DDR_CTRL_OFFSET-DDR_CMN_OFFSET))) ? ('b1+FSW_SLV_IDX) :
                     '0 ;

   assign haddr_offset = (slv_sel == ('b1+PLL_SLV_IDX )) ? (DDR_PLL_OFFSET-DDR_CMN_OFFSET)  :
                         (slv_sel == ('b1+FSW_SLV_IDX )) ? (DDR_FSW_OFFSET-DDR_CMN_OFFSET)  :
                         '0;

  assign haddr_local  = i_haddr - haddr_offset;

   wav_ahb_slave_mux #(
      .DWIDTH                (32),
      .AWIDTH                (32),
      .NUM_SLV               (NUM_INTF_SLVS )
   ) u_int_slv_mux (

      .i_hclk                (i_hclk  ),
      .i_hreset              (i_hreset),

      .i_slv_sel             (slv_sel),
      .i_hbusreq             (i_hsel),
      .i_haddr               (haddr_local ),
      .i_hwrite              (i_hwrite),
      .i_hwdata              (i_hwdata),
      .i_htrans              (i_htrans),
      .i_hsize               (i_hsize ),
      .i_hburst              (i_hburst),
      .i_hreadyin            (i_hreadyin),
      .o_hready              (o_hready),
      .o_hrdata              (o_hrdata),
      .o_hresp               (o_hresp ),

      .o_haddr               (int_slv_mux_haddr ),
      .o_hwrite              (int_slv_mux_hwrite),
      .o_hsel                (int_slv_mux_hsel  ),
      .o_hwdata              (int_slv_mux_hwdata),
      .o_htrans              (int_slv_mux_htrans),
      .o_hsize               (int_slv_mux_hsize ),
      .o_hburst              (int_slv_mux_hburst),
      .o_hreadyin            (int_slv_mux_hreadyin),
      .i_hready              (int_slv_mux_hready),
      .i_hrdata              (int_slv_mux_hrdata),
      .i_hresp               (int_slv_mux_hresp )
   );

   ddr_cmn_ahb_csr #(
      .AWIDTH(AWIDTH),
      .DWIDTH(DWIDTH)
   ) u_cmn_ahb_csr (
      .i_hclk                (i_hclk  ),
      .i_hreset              (i_ahb_csr_rst),
      .i_haddr               (cmn_haddr ),
      .i_hwrite              (cmn_hwrite),
      .i_hsel                (cmn_hsel  ),
      .i_hwdata              (cmn_hwdata),
      .i_htrans              (cmn_htrans),
      .i_hsize               (cmn_hsize ),
      .i_hburst              (cmn_hburst),
      .i_hreadyin            (cmn_hreadyin),
      .o_hready              (cmn_hready),
      .o_hrdata              (cmn_hrdata),
      .o_hresp               (cmn_hresp ),
      .o_cmn_vref_m0_cfg     (cmn_vref_m0_cfg),
      .o_cmn_vref_m1_cfg     (cmn_vref_m1_cfg),
      .o_cmn_zqcal_cfg       (cmn_zqcal_cfg),
      .o_cmn_ibias_cfg       (cmn_ibias_cfg),
      .o_cmn_test_cfg        (cmn_test_cfg),
      .o_cmn_ldo_m0_cfg      (cmn_ldo_m0_cfg),
      .o_cmn_ldo_m1_cfg      (cmn_ldo_m1_cfg),
      .o_cmn_clk_ctrl_cfg    (cmn_clk_ctrl_cfg),
      .i_cmn_zqcal_sta       (i_cmn_zqcal_sta),
      .i_cmn_clk_sta         (i_cmn_clk_sta),
      .i_cmn_pmon_nand_sta   (i_cmn_pmon_nand_sta),
      .i_cmn_pmon_nor_sta    (i_cmn_pmon_nor_sta),
      .o_cmn_pmon_ana_cfg    (cmn_pmon_ana_cfg),
      .o_cmn_pmon_dig_cfg    (cmn_pmon_dig_cfg),
      .o_cmn_pmon_dig_nand_cfg (cmn_pmon_dig_nand_cfg),
      .o_cmn_pmon_dig_nor_cfg (cmn_pmon_dig_nor_cfg),
      .o_cmn_rstn_cfg        (o_ddr_rstn_cfg),
      .i_cmn_rstn_sta        (i_ddr_rstn_sta)
   );

   ddr_fsw_ahb_csr #(
      .AWIDTH(AWIDTH),
      .DWIDTH(DWIDTH)
   ) u_fsw_ahb_csr (
      .i_hclk                (i_hclk  ),
      .i_hreset              (i_ahb_csr_rst),
      .i_haddr               (fsw_haddr ),
      .i_hwrite              (fsw_hwrite),
      .i_hsel                (fsw_hsel  ),
      .i_hwdata              (fsw_hwdata),
      .i_htrans              (fsw_htrans),
      .i_hsize               (fsw_hsize ),
      .i_hburst              (fsw_hburst),
      .i_hreadyin            (fsw_hreadyin),
      .o_hready              (fsw_hready),
      .o_hrdata              (fsw_hrdata),
      .o_hresp               (fsw_hresp ),
      .o_fsw_debug_cfg       (o_fsw_debug_cfg),
      .o_fsw_csp_0_cfg       (o_fsw_csp_0_cfg),
      .o_fsw_csp_1_cfg       (o_fsw_csp_1_cfg),
      .i_fsw_csp_sta         (i_fsw_csp_sta),
      .o_fsw_ctrl_cfg        (o_fsw_ctrl_cfg),
      .i_fsw_ctrl_sta        (i_fsw_ctrl_sta)
   );

endmodule

module ddr_rstn_bscan #(
   parameter WIDTH      =  1
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
   input  logic                            i_bscan_ctrl,
   input  logic [WIDTH-1:0]                i_bscan,

   output logic [WIDTH-1:0]                o_pad_bscan,
   output logic                            o_pad_bscan_oe
);

   logic [1:0] td;

   // CTRL - Out Data Register
   wav_jtag_reg #(
      .NO_BYP                        (1),
      .DWIDTH                        (1)
   ) u_bsr_ctrl (
      .i_tck                         (i_jtag_tck),
      .i_trst_n                      (i_jtag_trst_n),
      .i_bsr_mode                    (i_jtag_bsr_mode),
      .i_capture                     (i_jtag_capture),
      .i_shift                       (i_jtag_shift),
      .i_update                      (i_jtag_update),
      .i_pi                          (i_bscan_ctrl),
      .o_po                          (o_pad_bscan_oe),
      .i_tdi                         (i_jtag_tdi),
      .o_tdo                         (td[0])
   );

   // DQ - Out Data Register
   wav_jtag_reg #(
      .NO_BYP                        (1),
      .DWIDTH                        (WIDTH)
   ) u_bsr_o (
      .i_tck                         (i_jtag_tck),
      .i_trst_n                      (i_jtag_trst_n),
      .i_bsr_mode                    (i_jtag_bsr_mode),
      .i_capture                     (i_jtag_capture),
      .i_shift                       (i_jtag_shift),
      .i_update                      (i_jtag_update),
      .i_pi                          (i_bscan),
      .o_po                          (o_pad_bscan),
      .i_tdi                         (td[0]),
      .o_tdo                         (o_jtag_tdo)
   );

endmodule
