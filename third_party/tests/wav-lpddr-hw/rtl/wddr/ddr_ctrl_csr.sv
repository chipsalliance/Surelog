
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

module ddr_ctrl_csr #(
   parameter AWIDTH = 32,
   parameter DWIDTH = 32
) (

   input   logic                i_hclk,
   input   logic                i_hreset,
   input   logic                i_write,
   input   logic                i_read,
   input   logic [AWIDTH-1:0]   i_addr,
   input   logic [DWIDTH-1:0]   i_wdata,
   output  logic [DWIDTH-1:0]   o_rdata,
   output  logic                o_error,
   output  logic                o_ready,
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

   typedef enum logic [4:0] {
      DECODE_DDR_CTRL_CLK_CFG,
      DECODE_DDR_CTRL_CLK_STA,
      DECODE_DDR_CTRL_AHB_SNOOP_CFG,
      DECODE_DDR_CTRL_AHB_SNOOP_STA,
      DECODE_DDR_CTRL_AHB_SNOOP_DATA_STA,
      DECODE_DDR_CTRL_AHB_SNOOP_PATTERN_CFG,
      DECODE_DDR_CTRL_AHB_SNOOP_PATTERN_0_CFG,
      DECODE_DDR_CTRL_AHB_SNOOP_PATTERN_1_CFG,
      DECODE_DDR_CTRL_AHB_SNOOP_PATTERN_STA,
      DECODE_DDR_CTRL_DEBUG_CFG,
      DECODE_DDR_CTRL_DEBUG1_CFG,
      DECODE_NOOP
   } DECODE_T;

   DECODE_T decode;

   assign o_ready = 1'b1;

   always_comb begin
      o_error = 1'b0;
      case (i_addr)
         `DDR_CTRL_CLK_CFG_ADR : decode = DECODE_DDR_CTRL_CLK_CFG;
         `DDR_CTRL_CLK_STA_ADR : decode = DECODE_DDR_CTRL_CLK_STA;
         `DDR_CTRL_AHB_SNOOP_CFG_ADR : decode = DECODE_DDR_CTRL_AHB_SNOOP_CFG;
         `DDR_CTRL_AHB_SNOOP_STA_ADR : decode = DECODE_DDR_CTRL_AHB_SNOOP_STA;
         `DDR_CTRL_AHB_SNOOP_DATA_STA_ADR : decode = DECODE_DDR_CTRL_AHB_SNOOP_DATA_STA;
         `DDR_CTRL_AHB_SNOOP_PATTERN_CFG_ADR : decode = DECODE_DDR_CTRL_AHB_SNOOP_PATTERN_CFG;
         `DDR_CTRL_AHB_SNOOP_PATTERN_0_CFG_ADR : decode = DECODE_DDR_CTRL_AHB_SNOOP_PATTERN_0_CFG;
         `DDR_CTRL_AHB_SNOOP_PATTERN_1_CFG_ADR : decode = DECODE_DDR_CTRL_AHB_SNOOP_PATTERN_1_CFG;
         `DDR_CTRL_AHB_SNOOP_PATTERN_STA_ADR : decode = DECODE_DDR_CTRL_AHB_SNOOP_PATTERN_STA;
         `DDR_CTRL_DEBUG_CFG_ADR : decode = DECODE_DDR_CTRL_DEBUG_CFG;
         `DDR_CTRL_DEBUG1_CFG_ADR : decode = DECODE_DDR_CTRL_DEBUG1_CFG;
         default : begin 
            decode = DECODE_NOOP;
            o_error = 1'b1;
         end
      endcase
   end

   logic [31:0] ctrl_clk_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         ctrl_clk_cfg_q <= `DDR_CTRL_CLK_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_CTRL_CLK_CFG)
               ctrl_clk_cfg_q <= i_wdata;

   assign o_ctrl_clk_cfg = ctrl_clk_cfg_q & `DDR_CTRL_CLK_CFG_MSK;

   logic [31:0] ctrl_clk_sta_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         ctrl_clk_sta_q <= `DDR_CTRL_CLK_STA_POR;
      else
         ctrl_clk_sta_q <= i_ctrl_clk_sta;

   logic [31:0] ctrl_ahb_snoop_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         ctrl_ahb_snoop_cfg_q <= `DDR_CTRL_AHB_SNOOP_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_CTRL_AHB_SNOOP_CFG)
               ctrl_ahb_snoop_cfg_q <= i_wdata;

   assign o_ctrl_ahb_snoop_cfg = ctrl_ahb_snoop_cfg_q & `DDR_CTRL_AHB_SNOOP_CFG_MSK;

   logic [31:0] ctrl_ahb_snoop_sta_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         ctrl_ahb_snoop_sta_q <= `DDR_CTRL_AHB_SNOOP_STA_POR;
      else
         ctrl_ahb_snoop_sta_q <= i_ctrl_ahb_snoop_sta;

   logic [31:0] ctrl_ahb_snoop_data_sta_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         ctrl_ahb_snoop_data_sta_q <= `DDR_CTRL_AHB_SNOOP_DATA_STA_POR;
      else
         ctrl_ahb_snoop_data_sta_q <= i_ctrl_ahb_snoop_data_sta;

   logic [31:0] ctrl_ahb_snoop_pattern_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         ctrl_ahb_snoop_pattern_cfg_q <= `DDR_CTRL_AHB_SNOOP_PATTERN_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_CTRL_AHB_SNOOP_PATTERN_CFG)
               ctrl_ahb_snoop_pattern_cfg_q <= i_wdata;

   assign o_ctrl_ahb_snoop_pattern_cfg = ctrl_ahb_snoop_pattern_cfg_q & `DDR_CTRL_AHB_SNOOP_PATTERN_CFG_MSK;

   logic [31:0] ctrl_ahb_snoop_pattern_0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         ctrl_ahb_snoop_pattern_0_cfg_q <= `DDR_CTRL_AHB_SNOOP_PATTERN_0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_CTRL_AHB_SNOOP_PATTERN_0_CFG)
               ctrl_ahb_snoop_pattern_0_cfg_q <= i_wdata;

   assign o_ctrl_ahb_snoop_pattern_0_cfg = ctrl_ahb_snoop_pattern_0_cfg_q & `DDR_CTRL_AHB_SNOOP_PATTERN_0_CFG_MSK;

   logic [31:0] ctrl_ahb_snoop_pattern_1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         ctrl_ahb_snoop_pattern_1_cfg_q <= `DDR_CTRL_AHB_SNOOP_PATTERN_1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_CTRL_AHB_SNOOP_PATTERN_1_CFG)
               ctrl_ahb_snoop_pattern_1_cfg_q <= i_wdata;

   assign o_ctrl_ahb_snoop_pattern_1_cfg = ctrl_ahb_snoop_pattern_1_cfg_q & `DDR_CTRL_AHB_SNOOP_PATTERN_1_CFG_MSK;

   logic [31:0] ctrl_ahb_snoop_pattern_sta_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         ctrl_ahb_snoop_pattern_sta_q <= `DDR_CTRL_AHB_SNOOP_PATTERN_STA_POR;
      else
         if (i_write) begin
            if (decode == DECODE_DDR_CTRL_AHB_SNOOP_PATTERN_STA)
               ctrl_ahb_snoop_pattern_sta_q <= ctrl_ahb_snoop_pattern_sta_q & ~i_wdata;
         end else begin
            ctrl_ahb_snoop_pattern_sta_q <= ctrl_ahb_snoop_pattern_sta_q | i_ctrl_ahb_snoop_pattern_sta;
         end

   logic [31:0] ctrl_debug_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         ctrl_debug_cfg_q <= `DDR_CTRL_DEBUG_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_CTRL_DEBUG_CFG)
               ctrl_debug_cfg_q <= i_wdata;

   assign o_ctrl_debug_cfg = ctrl_debug_cfg_q & `DDR_CTRL_DEBUG_CFG_MSK;

   logic [31:0] ctrl_debug1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         ctrl_debug1_cfg_q <= `DDR_CTRL_DEBUG1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_CTRL_DEBUG1_CFG)
               ctrl_debug1_cfg_q <= i_wdata;

   assign o_ctrl_debug1_cfg = ctrl_debug1_cfg_q & `DDR_CTRL_DEBUG1_CFG_MSK;

   always_comb
      if (i_read)
         case (decode)
            DECODE_DDR_CTRL_CLK_CFG : o_rdata = o_ctrl_clk_cfg;
            DECODE_DDR_CTRL_CLK_STA : o_rdata = ctrl_clk_sta_q;
            DECODE_DDR_CTRL_AHB_SNOOP_CFG : o_rdata = o_ctrl_ahb_snoop_cfg;
            DECODE_DDR_CTRL_AHB_SNOOP_STA : o_rdata = ctrl_ahb_snoop_sta_q;
            DECODE_DDR_CTRL_AHB_SNOOP_DATA_STA : o_rdata = ctrl_ahb_snoop_data_sta_q;
            DECODE_DDR_CTRL_AHB_SNOOP_PATTERN_CFG : o_rdata = o_ctrl_ahb_snoop_pattern_cfg;
            DECODE_DDR_CTRL_AHB_SNOOP_PATTERN_0_CFG : o_rdata = o_ctrl_ahb_snoop_pattern_0_cfg;
            DECODE_DDR_CTRL_AHB_SNOOP_PATTERN_1_CFG : o_rdata = o_ctrl_ahb_snoop_pattern_1_cfg;
            DECODE_DDR_CTRL_AHB_SNOOP_PATTERN_STA : o_rdata = ctrl_ahb_snoop_pattern_sta_q;
            DECODE_DDR_CTRL_DEBUG_CFG : o_rdata = o_ctrl_debug_cfg;
            DECODE_DDR_CTRL_DEBUG1_CFG : o_rdata = o_ctrl_debug1_cfg;
            default : o_rdata = '0;
         endcase
      else
         o_rdata = '0;

endmodule
