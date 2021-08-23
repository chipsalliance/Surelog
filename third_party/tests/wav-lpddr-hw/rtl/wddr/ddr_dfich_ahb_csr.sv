
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
`include "ddr_dfich_csr_defs.vh"

import ddr_global_pkg::*;

module ddr_dfich_ahb_csr #(
   parameter AWIDTH = 32,
   parameter DWIDTH = 32
) (

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
   output  logic [`DDR_DFICH_TOP_1_CFG_RANGE] o_dfich_top_1_cfg,
   output  logic [`DDR_DFICH_TOP_2_CFG_RANGE] o_dfich_top_2_cfg,
   output  logic [`DDR_DFICH_TOP_3_CFG_RANGE] o_dfich_top_3_cfg,
   input   logic [`DDR_DFICH_TOP_STA_RANGE] i_dfich_top_sta,
   output  logic [`DDR_DFICH_IG_DATA_CFG_RANGE] o_dfich_ig_data_cfg,
   input   logic [`DDR_DFICH_EG_DATA_STA_RANGE] i_dfich_eg_data_sta,
   output  logic [`DDR_DFICH_WRC_M0_CFG_RANGE] o_dfich_wrc_m0_cfg,
   output  logic [`DDR_DFICH_WRC_M1_CFG_RANGE] o_dfich_wrc_m1_cfg,
   output  logic [`DDR_DFICH_WRCCTRL_M0_CFG_RANGE] o_dfich_wrcctrl_m0_cfg,
   output  logic [`DDR_DFICH_WRCCTRL_M1_CFG_RANGE] o_dfich_wrcctrl_m1_cfg,
   output  logic [`DDR_DFICH_CKCTRL_M0_CFG_RANGE] o_dfich_ckctrl_m0_cfg,
   output  logic [`DDR_DFICH_CKCTRL_M1_CFG_RANGE] o_dfich_ckctrl_m1_cfg,
   output  logic [`DDR_DFICH_RDC_M0_CFG_RANGE] o_dfich_rdc_m0_cfg,
   output  logic [`DDR_DFICH_RDC_M1_CFG_RANGE] o_dfich_rdc_m1_cfg,
   output  logic [`DDR_DFICH_RCTRL_M0_CFG_RANGE] o_dfich_rctrl_m0_cfg,
   output  logic [`DDR_DFICH_RCTRL_M1_CFG_RANGE] o_dfich_rctrl_m1_cfg,
   output  logic [`DDR_DFICH_WCTRL_M0_CFG_RANGE] o_dfich_wctrl_m0_cfg,
   output  logic [`DDR_DFICH_WCTRL_M1_CFG_RANGE] o_dfich_wctrl_m1_cfg,
   output  logic [`DDR_DFICH_WENCTRL_M0_CFG_RANGE] o_dfich_wenctrl_m0_cfg,
   output  logic [`DDR_DFICH_WENCTRL_M1_CFG_RANGE] o_dfich_wenctrl_m1_cfg,
   output  logic [`DDR_DFICH_WCKCTRL_M0_CFG_RANGE] o_dfich_wckctrl_m0_cfg,
   output  logic [`DDR_DFICH_WCKCTRL_M1_CFG_RANGE] o_dfich_wckctrl_m1_cfg,
   output  logic [`DDR_DFICH_WRD_M0_CFG_RANGE] o_dfich_wrd_m0_cfg,
   output  logic [`DDR_DFICH_WRD_M1_CFG_RANGE] o_dfich_wrd_m1_cfg,
   output  logic [`DDR_DFICH_RDD_M0_CFG_RANGE] o_dfich_rdd_m0_cfg,
   output  logic [`DDR_DFICH_RDD_M1_CFG_RANGE] o_dfich_rdd_m1_cfg,
   output  logic [`DDR_DFICH_CTRL0_M0_CFG_RANGE] o_dfich_ctrl0_m0_cfg,
   output  logic [`DDR_DFICH_CTRL0_M1_CFG_RANGE] o_dfich_ctrl0_m1_cfg,
   output  logic [`DDR_DFICH_CTRL1_M0_CFG_RANGE] o_dfich_ctrl1_m0_cfg,
   output  logic [`DDR_DFICH_CTRL1_M1_CFG_RANGE] o_dfich_ctrl1_m1_cfg,
   output  logic [`DDR_DFICH_CTRL2_M0_CFG_RANGE] o_dfich_ctrl2_m0_cfg,
   output  logic [`DDR_DFICH_CTRL2_M1_CFG_RANGE] o_dfich_ctrl2_m1_cfg,
   output  logic [`DDR_DFICH_CTRL3_M0_CFG_RANGE] o_dfich_ctrl3_m0_cfg,
   output  logic [`DDR_DFICH_CTRL3_M1_CFG_RANGE] o_dfich_ctrl3_m1_cfg,
   output  logic [`DDR_DFICH_CTRL4_M0_CFG_RANGE] o_dfich_ctrl4_m0_cfg,
   output  logic [`DDR_DFICH_CTRL4_M1_CFG_RANGE] o_dfich_ctrl4_m1_cfg,
   output  logic [`DDR_DFICH_CTRL5_M0_CFG_RANGE] o_dfich_ctrl5_m0_cfg,
   output  logic [`DDR_DFICH_CTRL5_M1_CFG_RANGE] o_dfich_ctrl5_m1_cfg
);

   logic                slv_write;
   logic                slv_read;
   logic                slv_error;
   logic [AWIDTH-1:0]   slv_addr;
   logic [DWIDTH-1:0]   slv_wdata;
   logic [DWIDTH-1:0]   slv_rdata;
   logic                slv_ready;

   ddr_ahb_slave #(
      .AWIDTH(AWIDTH),
      .DWIDTH(DWIDTH)
   ) ahb_slave (
      .i_hclk     (i_hclk),
      .i_hreset   (i_hreset),
      .i_haddr    (i_haddr),
      .i_hwrite   (i_hwrite),
      .i_hsel     (i_hsel),
      .i_hwdata   (i_hwdata),
      .i_htrans   (i_htrans),
      .i_hsize    (i_hsize),
      .i_hburst   (i_hburst),
      .i_hreadyin (i_hreadyin),
      .o_hready   (o_hready),
      .o_hrdata   (o_hrdata),
      .o_hresp    (o_hresp),
      .o_write    (slv_write),
      .o_read     (slv_read),
      .o_wdata    (slv_wdata),
      .o_addr     (slv_addr),
      .i_rdata    (slv_rdata),
      .i_error    (slv_error),
      .i_ready    (slv_ready)
   );

   ddr_dfich_csr #(
      .AWIDTH(AWIDTH),
      .DWIDTH(DWIDTH)
   ) dfich_csr (
      .i_hclk   (i_hclk),
      .i_hreset (i_hreset),
      .i_write  (slv_write),
      .i_read   (slv_read),
      .i_wdata  (slv_wdata),
      .i_addr   (slv_addr),
      .o_rdata  (slv_rdata),
      .o_error  (slv_error),
      .o_ready  (slv_ready),
      .o_dfich_top_1_cfg (o_dfich_top_1_cfg),
      .o_dfich_top_2_cfg (o_dfich_top_2_cfg),
      .o_dfich_top_3_cfg (o_dfich_top_3_cfg),
      .i_dfich_top_sta (i_dfich_top_sta),
      .o_dfich_ig_data_cfg (o_dfich_ig_data_cfg),
      .i_dfich_eg_data_sta (i_dfich_eg_data_sta),
      .o_dfich_wrc_m0_cfg (o_dfich_wrc_m0_cfg),
      .o_dfich_wrc_m1_cfg (o_dfich_wrc_m1_cfg),
      .o_dfich_wrcctrl_m0_cfg (o_dfich_wrcctrl_m0_cfg),
      .o_dfich_wrcctrl_m1_cfg (o_dfich_wrcctrl_m1_cfg),
      .o_dfich_ckctrl_m0_cfg (o_dfich_ckctrl_m0_cfg),
      .o_dfich_ckctrl_m1_cfg (o_dfich_ckctrl_m1_cfg),
      .o_dfich_rdc_m0_cfg (o_dfich_rdc_m0_cfg),
      .o_dfich_rdc_m1_cfg (o_dfich_rdc_m1_cfg),
      .o_dfich_rctrl_m0_cfg (o_dfich_rctrl_m0_cfg),
      .o_dfich_rctrl_m1_cfg (o_dfich_rctrl_m1_cfg),
      .o_dfich_wctrl_m0_cfg (o_dfich_wctrl_m0_cfg),
      .o_dfich_wctrl_m1_cfg (o_dfich_wctrl_m1_cfg),
      .o_dfich_wenctrl_m0_cfg (o_dfich_wenctrl_m0_cfg),
      .o_dfich_wenctrl_m1_cfg (o_dfich_wenctrl_m1_cfg),
      .o_dfich_wckctrl_m0_cfg (o_dfich_wckctrl_m0_cfg),
      .o_dfich_wckctrl_m1_cfg (o_dfich_wckctrl_m1_cfg),
      .o_dfich_wrd_m0_cfg (o_dfich_wrd_m0_cfg),
      .o_dfich_wrd_m1_cfg (o_dfich_wrd_m1_cfg),
      .o_dfich_rdd_m0_cfg (o_dfich_rdd_m0_cfg),
      .o_dfich_rdd_m1_cfg (o_dfich_rdd_m1_cfg),
      .o_dfich_ctrl0_m0_cfg (o_dfich_ctrl0_m0_cfg),
      .o_dfich_ctrl0_m1_cfg (o_dfich_ctrl0_m1_cfg),
      .o_dfich_ctrl1_m0_cfg (o_dfich_ctrl1_m0_cfg),
      .o_dfich_ctrl1_m1_cfg (o_dfich_ctrl1_m1_cfg),
      .o_dfich_ctrl2_m0_cfg (o_dfich_ctrl2_m0_cfg),
      .o_dfich_ctrl2_m1_cfg (o_dfich_ctrl2_m1_cfg),
      .o_dfich_ctrl3_m0_cfg (o_dfich_ctrl3_m0_cfg),
      .o_dfich_ctrl3_m1_cfg (o_dfich_ctrl3_m1_cfg),
      .o_dfich_ctrl4_m0_cfg (o_dfich_ctrl4_m0_cfg),
      .o_dfich_ctrl4_m1_cfg (o_dfich_ctrl4_m1_cfg),
      .o_dfich_ctrl5_m0_cfg (o_dfich_ctrl5_m0_cfg),
      .o_dfich_ctrl5_m1_cfg (o_dfich_ctrl5_m1_cfg)
   );

endmodule
