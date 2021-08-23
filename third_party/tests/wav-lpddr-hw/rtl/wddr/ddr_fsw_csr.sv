
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
`include "ddr_fsw_csr_defs.vh"

import ddr_global_pkg::*;

module ddr_fsw_csr #(
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
   output  logic [`DDR_FSW_CTRL_CFG_RANGE] o_fsw_ctrl_cfg,
   input   logic [`DDR_FSW_CTRL_STA_RANGE] i_fsw_ctrl_sta,
   output  logic [`DDR_FSW_DEBUG_CFG_RANGE] o_fsw_debug_cfg,
   output  logic [`DDR_FSW_CSP_0_CFG_RANGE] o_fsw_csp_0_cfg,
   output  logic [`DDR_FSW_CSP_1_CFG_RANGE] o_fsw_csp_1_cfg,
   input   logic [`DDR_FSW_CSP_STA_RANGE] i_fsw_csp_sta
);

   typedef enum logic [3:0] {
      DECODE_DDR_FSW_CTRL_CFG,
      DECODE_DDR_FSW_CTRL_STA,
      DECODE_DDR_FSW_DEBUG_CFG,
      DECODE_DDR_FSW_CSP_0_CFG,
      DECODE_DDR_FSW_CSP_1_CFG,
      DECODE_DDR_FSW_CSP_STA,
      DECODE_NOOP
   } DECODE_T;

   DECODE_T decode;

   assign o_ready = 1'b1;

   always_comb begin
      o_error = 1'b0;
      case (i_addr)
         `DDR_FSW_CTRL_CFG_ADR : decode = DECODE_DDR_FSW_CTRL_CFG;
         `DDR_FSW_CTRL_STA_ADR : decode = DECODE_DDR_FSW_CTRL_STA;
         `DDR_FSW_DEBUG_CFG_ADR : decode = DECODE_DDR_FSW_DEBUG_CFG;
         `DDR_FSW_CSP_0_CFG_ADR : decode = DECODE_DDR_FSW_CSP_0_CFG;
         `DDR_FSW_CSP_1_CFG_ADR : decode = DECODE_DDR_FSW_CSP_1_CFG;
         `DDR_FSW_CSP_STA_ADR : decode = DECODE_DDR_FSW_CSP_STA;
         default : begin 
            decode = DECODE_NOOP;
            o_error = 1'b1;
         end
      endcase
   end

   logic [31:0] fsw_ctrl_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         fsw_ctrl_cfg_q <= `DDR_FSW_CTRL_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_FSW_CTRL_CFG)
               fsw_ctrl_cfg_q <= i_wdata;

   assign o_fsw_ctrl_cfg = fsw_ctrl_cfg_q & `DDR_FSW_CTRL_CFG_MSK;

   logic [31:0] fsw_ctrl_sta_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         fsw_ctrl_sta_q <= `DDR_FSW_CTRL_STA_POR;
      else
         fsw_ctrl_sta_q <= i_fsw_ctrl_sta;

   logic [31:0] fsw_debug_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         fsw_debug_cfg_q <= `DDR_FSW_DEBUG_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_FSW_DEBUG_CFG)
               fsw_debug_cfg_q <= i_wdata;

   assign o_fsw_debug_cfg = fsw_debug_cfg_q & `DDR_FSW_DEBUG_CFG_MSK;

   logic [31:0] fsw_csp_0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         fsw_csp_0_cfg_q <= `DDR_FSW_CSP_0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_FSW_CSP_0_CFG)
               fsw_csp_0_cfg_q <= i_wdata;

   assign o_fsw_csp_0_cfg = fsw_csp_0_cfg_q & `DDR_FSW_CSP_0_CFG_MSK;

   logic [31:0] fsw_csp_1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         fsw_csp_1_cfg_q <= `DDR_FSW_CSP_1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_FSW_CSP_1_CFG)
               fsw_csp_1_cfg_q <= i_wdata;

   assign o_fsw_csp_1_cfg = fsw_csp_1_cfg_q & `DDR_FSW_CSP_1_CFG_MSK;

   logic [31:0] fsw_csp_sta_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         fsw_csp_sta_q <= `DDR_FSW_CSP_STA_POR;
      else
         fsw_csp_sta_q <= i_fsw_csp_sta;

   always_comb
      if (i_read)
         case (decode)
            DECODE_DDR_FSW_CTRL_CFG : o_rdata = o_fsw_ctrl_cfg;
            DECODE_DDR_FSW_CTRL_STA : o_rdata = fsw_ctrl_sta_q;
            DECODE_DDR_FSW_DEBUG_CFG : o_rdata = o_fsw_debug_cfg;
            DECODE_DDR_FSW_CSP_0_CFG : o_rdata = o_fsw_csp_0_cfg;
            DECODE_DDR_FSW_CSP_1_CFG : o_rdata = o_fsw_csp_1_cfg;
            DECODE_DDR_FSW_CSP_STA : o_rdata = fsw_csp_sta_q;
            default : o_rdata = '0;
         endcase
      else
         o_rdata = '0;

endmodule
