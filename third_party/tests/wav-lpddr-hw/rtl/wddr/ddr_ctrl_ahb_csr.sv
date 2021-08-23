
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
`include "ddr_ctrl_csr_defs.vh"

import ddr_global_pkg::*;

module ddr_ctrl_ahb_csr #(
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
   output  logic [`DDR_CTRL_CLK_CFG_RANGE] o_ctrl_clk_cfg,
   input   logic [`DDR_CTRL_CLK_STA_RANGE] i_ctrl_clk_sta,
   output  logic [`DDR_CTRL_AHB_SNOOP_CFG_RANGE] o_ctrl_ahb_snoop_cfg,
   input   logic [`DDR_CTRL_AHB_SNOOP_STA_RANGE] i_ctrl_ahb_snoop_sta,
   input   logic [`DDR_CTRL_AHB_SNOOP_DATA_STA_RANGE] i_ctrl_ahb_snoop_data_sta,
   output  logic [`DDR_CTRL_AHB_SNOOP_PATTERN_CFG_RANGE] o_ctrl_ahb_snoop_pattern_cfg,
   output  logic [`DDR_CTRL_AHB_SNOOP_PATTERN_0_CFG_RANGE] o_ctrl_ahb_snoop_pattern_0_cfg,
   output  logic [`DDR_CTRL_AHB_SNOOP_PATTERN_1_CFG_RANGE] o_ctrl_ahb_snoop_pattern_1_cfg,
   input   logic [`DDR_CTRL_AHB_SNOOP_PATTERN_STA_RANGE] i_ctrl_ahb_snoop_pattern_sta,
   output  logic [`DDR_CTRL_DEBUG_CFG_RANGE] o_ctrl_debug_cfg,
   output  logic [`DDR_CTRL_DEBUG1_CFG_RANGE] o_ctrl_debug1_cfg
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

   ddr_ctrl_csr #(
      .AWIDTH(AWIDTH),
      .DWIDTH(DWIDTH)
   ) ctrl_csr (
      .i_hclk   (i_hclk),
      .i_hreset (i_hreset),
      .i_write  (slv_write),
      .i_read   (slv_read),
      .i_wdata  (slv_wdata),
      .i_addr   (slv_addr),
      .o_rdata  (slv_rdata),
      .o_error  (slv_error),
      .o_ready  (slv_ready),
      .o_ctrl_clk_cfg (o_ctrl_clk_cfg),
      .i_ctrl_clk_sta (i_ctrl_clk_sta),
      .o_ctrl_ahb_snoop_cfg (o_ctrl_ahb_snoop_cfg),
      .i_ctrl_ahb_snoop_sta (i_ctrl_ahb_snoop_sta),
      .i_ctrl_ahb_snoop_data_sta (i_ctrl_ahb_snoop_data_sta),
      .o_ctrl_ahb_snoop_pattern_cfg (o_ctrl_ahb_snoop_pattern_cfg),
      .o_ctrl_ahb_snoop_pattern_0_cfg (o_ctrl_ahb_snoop_pattern_0_cfg),
      .o_ctrl_ahb_snoop_pattern_1_cfg (o_ctrl_ahb_snoop_pattern_1_cfg),
      .i_ctrl_ahb_snoop_pattern_sta (i_ctrl_ahb_snoop_pattern_sta),
      .o_ctrl_debug_cfg (o_ctrl_debug_cfg),
      .o_ctrl_debug1_cfg (o_ctrl_debug1_cfg)
   );

endmodule
