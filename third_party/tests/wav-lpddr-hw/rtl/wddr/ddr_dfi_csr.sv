
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
`include "ddr_dfi_csr_defs.vh"

import ddr_global_pkg::*;

module ddr_dfi_csr #(
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
   output  logic [`DDR_DFI_TOP_0_CFG_RANGE] o_dfi_top_0_cfg,
   output  logic [`DDR_DFI_DATA_BIT_ENABLE_CFG_RANGE] o_dfi_data_bit_enable_cfg,
   output  logic [`DDR_DFI_PHYFREQ_RANGE_CFG_RANGE] o_dfi_phyfreq_range_cfg,
   output  logic [`DDR_DFI_STATUS_IF_CFG_RANGE] o_dfi_status_if_cfg,
   input   logic [`DDR_DFI_STATUS_IF_STA_RANGE] i_dfi_status_if_sta,
   output  logic [`DDR_DFI_STATUS_IF_EVENT_0_CFG_RANGE] o_dfi_status_if_event_0_cfg,
   output  logic [`DDR_DFI_STATUS_IF_EVENT_1_CFG_RANGE] o_dfi_status_if_event_1_cfg,
   output  logic [`DDR_DFI_CTRLUPD_IF_CFG_RANGE] o_dfi_ctrlupd_if_cfg,
   input   logic [`DDR_DFI_CTRLUPD_IF_STA_RANGE] i_dfi_ctrlupd_if_sta,
   output  logic [`DDR_DFI_CTRLUPD_IF_EVENT_0_CFG_RANGE] o_dfi_ctrlupd_if_event_0_cfg,
   output  logic [`DDR_DFI_CTRLUPD_IF_EVENT_1_CFG_RANGE] o_dfi_ctrlupd_if_event_1_cfg,
   output  logic [`DDR_DFI_LP_CTRL_IF_CFG_RANGE] o_dfi_lp_ctrl_if_cfg,
   input   logic [`DDR_DFI_LP_CTRL_IF_STA_RANGE] i_dfi_lp_ctrl_if_sta,
   output  logic [`DDR_DFI_LP_CTRL_IF_EVENT_0_CFG_RANGE] o_dfi_lp_ctrl_if_event_0_cfg,
   output  logic [`DDR_DFI_LP_CTRL_IF_EVENT_1_CFG_RANGE] o_dfi_lp_ctrl_if_event_1_cfg,
   output  logic [`DDR_DFI_LP_DATA_IF_CFG_RANGE] o_dfi_lp_data_if_cfg,
   input   logic [`DDR_DFI_LP_DATA_IF_STA_RANGE] i_dfi_lp_data_if_sta,
   output  logic [`DDR_DFI_LP_DATA_IF_EVENT_0_CFG_RANGE] o_dfi_lp_data_if_event_0_cfg,
   output  logic [`DDR_DFI_LP_DATA_IF_EVENT_1_CFG_RANGE] o_dfi_lp_data_if_event_1_cfg,
   output  logic [`DDR_DFI_PHYUPD_IF_CFG_RANGE] o_dfi_phyupd_if_cfg,
   input   logic [`DDR_DFI_PHYUPD_IF_STA_RANGE] i_dfi_phyupd_if_sta,
   output  logic [`DDR_DFI_PHYMSTR_IF_CFG_RANGE] o_dfi_phymstr_if_cfg,
   input   logic [`DDR_DFI_PHYMSTR_IF_STA_RANGE] i_dfi_phymstr_if_sta,
   output  logic [`DDR_DFI_DEBUG_CFG_RANGE] o_dfi_debug_cfg
);

   typedef enum logic [5:0] {
      DECODE_DDR_DFI_TOP_0_CFG,
      DECODE_DDR_DFI_DATA_BIT_ENABLE_CFG,
      DECODE_DDR_DFI_PHYFREQ_RANGE_CFG,
      DECODE_DDR_DFI_STATUS_IF_CFG,
      DECODE_DDR_DFI_STATUS_IF_STA,
      DECODE_DDR_DFI_STATUS_IF_EVENT_0_CFG,
      DECODE_DDR_DFI_STATUS_IF_EVENT_1_CFG,
      DECODE_DDR_DFI_CTRLUPD_IF_CFG,
      DECODE_DDR_DFI_CTRLUPD_IF_STA,
      DECODE_DDR_DFI_CTRLUPD_IF_EVENT_0_CFG,
      DECODE_DDR_DFI_CTRLUPD_IF_EVENT_1_CFG,
      DECODE_DDR_DFI_LP_CTRL_IF_CFG,
      DECODE_DDR_DFI_LP_CTRL_IF_STA,
      DECODE_DDR_DFI_LP_CTRL_IF_EVENT_0_CFG,
      DECODE_DDR_DFI_LP_CTRL_IF_EVENT_1_CFG,
      DECODE_DDR_DFI_LP_DATA_IF_CFG,
      DECODE_DDR_DFI_LP_DATA_IF_STA,
      DECODE_DDR_DFI_LP_DATA_IF_EVENT_0_CFG,
      DECODE_DDR_DFI_LP_DATA_IF_EVENT_1_CFG,
      DECODE_DDR_DFI_PHYUPD_IF_CFG,
      DECODE_DDR_DFI_PHYUPD_IF_STA,
      DECODE_DDR_DFI_PHYMSTR_IF_CFG,
      DECODE_DDR_DFI_PHYMSTR_IF_STA,
      DECODE_DDR_DFI_DEBUG_CFG,
      DECODE_NOOP
   } DECODE_T;

   DECODE_T decode;

   assign o_ready = 1'b1;

   always_comb begin
      o_error = 1'b0;
      case (i_addr)
         `DDR_DFI_TOP_0_CFG_ADR : decode = DECODE_DDR_DFI_TOP_0_CFG;
         `DDR_DFI_DATA_BIT_ENABLE_CFG_ADR : decode = DECODE_DDR_DFI_DATA_BIT_ENABLE_CFG;
         `DDR_DFI_PHYFREQ_RANGE_CFG_ADR : decode = DECODE_DDR_DFI_PHYFREQ_RANGE_CFG;
         `DDR_DFI_STATUS_IF_CFG_ADR : decode = DECODE_DDR_DFI_STATUS_IF_CFG;
         `DDR_DFI_STATUS_IF_STA_ADR : decode = DECODE_DDR_DFI_STATUS_IF_STA;
         `DDR_DFI_STATUS_IF_EVENT_0_CFG_ADR : decode = DECODE_DDR_DFI_STATUS_IF_EVENT_0_CFG;
         `DDR_DFI_STATUS_IF_EVENT_1_CFG_ADR : decode = DECODE_DDR_DFI_STATUS_IF_EVENT_1_CFG;
         `DDR_DFI_CTRLUPD_IF_CFG_ADR : decode = DECODE_DDR_DFI_CTRLUPD_IF_CFG;
         `DDR_DFI_CTRLUPD_IF_STA_ADR : decode = DECODE_DDR_DFI_CTRLUPD_IF_STA;
         `DDR_DFI_CTRLUPD_IF_EVENT_0_CFG_ADR : decode = DECODE_DDR_DFI_CTRLUPD_IF_EVENT_0_CFG;
         `DDR_DFI_CTRLUPD_IF_EVENT_1_CFG_ADR : decode = DECODE_DDR_DFI_CTRLUPD_IF_EVENT_1_CFG;
         `DDR_DFI_LP_CTRL_IF_CFG_ADR : decode = DECODE_DDR_DFI_LP_CTRL_IF_CFG;
         `DDR_DFI_LP_CTRL_IF_STA_ADR : decode = DECODE_DDR_DFI_LP_CTRL_IF_STA;
         `DDR_DFI_LP_CTRL_IF_EVENT_0_CFG_ADR : decode = DECODE_DDR_DFI_LP_CTRL_IF_EVENT_0_CFG;
         `DDR_DFI_LP_CTRL_IF_EVENT_1_CFG_ADR : decode = DECODE_DDR_DFI_LP_CTRL_IF_EVENT_1_CFG;
         `DDR_DFI_LP_DATA_IF_CFG_ADR : decode = DECODE_DDR_DFI_LP_DATA_IF_CFG;
         `DDR_DFI_LP_DATA_IF_STA_ADR : decode = DECODE_DDR_DFI_LP_DATA_IF_STA;
         `DDR_DFI_LP_DATA_IF_EVENT_0_CFG_ADR : decode = DECODE_DDR_DFI_LP_DATA_IF_EVENT_0_CFG;
         `DDR_DFI_LP_DATA_IF_EVENT_1_CFG_ADR : decode = DECODE_DDR_DFI_LP_DATA_IF_EVENT_1_CFG;
         `DDR_DFI_PHYUPD_IF_CFG_ADR : decode = DECODE_DDR_DFI_PHYUPD_IF_CFG;
         `DDR_DFI_PHYUPD_IF_STA_ADR : decode = DECODE_DDR_DFI_PHYUPD_IF_STA;
         `DDR_DFI_PHYMSTR_IF_CFG_ADR : decode = DECODE_DDR_DFI_PHYMSTR_IF_CFG;
         `DDR_DFI_PHYMSTR_IF_STA_ADR : decode = DECODE_DDR_DFI_PHYMSTR_IF_STA;
         `DDR_DFI_DEBUG_CFG_ADR : decode = DECODE_DDR_DFI_DEBUG_CFG;
         default : begin 
            decode = DECODE_NOOP;
            o_error = 1'b1;
         end
      endcase
   end

   logic [31:0] dfi_top_0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfi_top_0_cfg_q <= `DDR_DFI_TOP_0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFI_TOP_0_CFG)
               dfi_top_0_cfg_q <= i_wdata;

   assign o_dfi_top_0_cfg = dfi_top_0_cfg_q & `DDR_DFI_TOP_0_CFG_MSK;

   logic [31:0] dfi_data_bit_enable_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfi_data_bit_enable_cfg_q <= `DDR_DFI_DATA_BIT_ENABLE_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFI_DATA_BIT_ENABLE_CFG)
               dfi_data_bit_enable_cfg_q <= i_wdata;

   assign o_dfi_data_bit_enable_cfg = dfi_data_bit_enable_cfg_q & `DDR_DFI_DATA_BIT_ENABLE_CFG_MSK;

   logic [31:0] dfi_phyfreq_range_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfi_phyfreq_range_cfg_q <= `DDR_DFI_PHYFREQ_RANGE_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFI_PHYFREQ_RANGE_CFG)
               dfi_phyfreq_range_cfg_q <= i_wdata;

   assign o_dfi_phyfreq_range_cfg = dfi_phyfreq_range_cfg_q & `DDR_DFI_PHYFREQ_RANGE_CFG_MSK;

   logic [31:0] dfi_status_if_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfi_status_if_cfg_q <= `DDR_DFI_STATUS_IF_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFI_STATUS_IF_CFG)
               dfi_status_if_cfg_q <= i_wdata;

   assign o_dfi_status_if_cfg = dfi_status_if_cfg_q & `DDR_DFI_STATUS_IF_CFG_MSK;

   logic [31:0] dfi_status_if_sta_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfi_status_if_sta_q <= `DDR_DFI_STATUS_IF_STA_POR;
      else
         dfi_status_if_sta_q <= i_dfi_status_if_sta;

   logic [31:0] dfi_status_if_event_0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfi_status_if_event_0_cfg_q <= `DDR_DFI_STATUS_IF_EVENT_0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFI_STATUS_IF_EVENT_0_CFG)
               dfi_status_if_event_0_cfg_q <= i_wdata;

   assign o_dfi_status_if_event_0_cfg = dfi_status_if_event_0_cfg_q & `DDR_DFI_STATUS_IF_EVENT_0_CFG_MSK;

   logic [31:0] dfi_status_if_event_1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfi_status_if_event_1_cfg_q <= `DDR_DFI_STATUS_IF_EVENT_1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFI_STATUS_IF_EVENT_1_CFG)
               dfi_status_if_event_1_cfg_q <= i_wdata;

   assign o_dfi_status_if_event_1_cfg = dfi_status_if_event_1_cfg_q & `DDR_DFI_STATUS_IF_EVENT_1_CFG_MSK;

   logic [31:0] dfi_ctrlupd_if_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfi_ctrlupd_if_cfg_q <= `DDR_DFI_CTRLUPD_IF_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFI_CTRLUPD_IF_CFG)
               dfi_ctrlupd_if_cfg_q <= i_wdata;

   assign o_dfi_ctrlupd_if_cfg = dfi_ctrlupd_if_cfg_q & `DDR_DFI_CTRLUPD_IF_CFG_MSK;

   logic [31:0] dfi_ctrlupd_if_sta_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfi_ctrlupd_if_sta_q <= `DDR_DFI_CTRLUPD_IF_STA_POR;
      else
         dfi_ctrlupd_if_sta_q <= i_dfi_ctrlupd_if_sta;

   logic [31:0] dfi_ctrlupd_if_event_0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfi_ctrlupd_if_event_0_cfg_q <= `DDR_DFI_CTRLUPD_IF_EVENT_0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFI_CTRLUPD_IF_EVENT_0_CFG)
               dfi_ctrlupd_if_event_0_cfg_q <= i_wdata;

   assign o_dfi_ctrlupd_if_event_0_cfg = dfi_ctrlupd_if_event_0_cfg_q & `DDR_DFI_CTRLUPD_IF_EVENT_0_CFG_MSK;

   logic [31:0] dfi_ctrlupd_if_event_1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfi_ctrlupd_if_event_1_cfg_q <= `DDR_DFI_CTRLUPD_IF_EVENT_1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFI_CTRLUPD_IF_EVENT_1_CFG)
               dfi_ctrlupd_if_event_1_cfg_q <= i_wdata;

   assign o_dfi_ctrlupd_if_event_1_cfg = dfi_ctrlupd_if_event_1_cfg_q & `DDR_DFI_CTRLUPD_IF_EVENT_1_CFG_MSK;

   logic [31:0] dfi_lp_ctrl_if_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfi_lp_ctrl_if_cfg_q <= `DDR_DFI_LP_CTRL_IF_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFI_LP_CTRL_IF_CFG)
               dfi_lp_ctrl_if_cfg_q <= i_wdata;

   assign o_dfi_lp_ctrl_if_cfg = dfi_lp_ctrl_if_cfg_q & `DDR_DFI_LP_CTRL_IF_CFG_MSK;

   logic [31:0] dfi_lp_ctrl_if_sta_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfi_lp_ctrl_if_sta_q <= `DDR_DFI_LP_CTRL_IF_STA_POR;
      else
         dfi_lp_ctrl_if_sta_q <= i_dfi_lp_ctrl_if_sta;

   logic [31:0] dfi_lp_ctrl_if_event_0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfi_lp_ctrl_if_event_0_cfg_q <= `DDR_DFI_LP_CTRL_IF_EVENT_0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFI_LP_CTRL_IF_EVENT_0_CFG)
               dfi_lp_ctrl_if_event_0_cfg_q <= i_wdata;

   assign o_dfi_lp_ctrl_if_event_0_cfg = dfi_lp_ctrl_if_event_0_cfg_q & `DDR_DFI_LP_CTRL_IF_EVENT_0_CFG_MSK;

   logic [31:0] dfi_lp_ctrl_if_event_1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfi_lp_ctrl_if_event_1_cfg_q <= `DDR_DFI_LP_CTRL_IF_EVENT_1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFI_LP_CTRL_IF_EVENT_1_CFG)
               dfi_lp_ctrl_if_event_1_cfg_q <= i_wdata;

   assign o_dfi_lp_ctrl_if_event_1_cfg = dfi_lp_ctrl_if_event_1_cfg_q & `DDR_DFI_LP_CTRL_IF_EVENT_1_CFG_MSK;

   logic [31:0] dfi_lp_data_if_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfi_lp_data_if_cfg_q <= `DDR_DFI_LP_DATA_IF_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFI_LP_DATA_IF_CFG)
               dfi_lp_data_if_cfg_q <= i_wdata;

   assign o_dfi_lp_data_if_cfg = dfi_lp_data_if_cfg_q & `DDR_DFI_LP_DATA_IF_CFG_MSK;

   logic [31:0] dfi_lp_data_if_sta_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfi_lp_data_if_sta_q <= `DDR_DFI_LP_DATA_IF_STA_POR;
      else
         dfi_lp_data_if_sta_q <= i_dfi_lp_data_if_sta;

   logic [31:0] dfi_lp_data_if_event_0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfi_lp_data_if_event_0_cfg_q <= `DDR_DFI_LP_DATA_IF_EVENT_0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFI_LP_DATA_IF_EVENT_0_CFG)
               dfi_lp_data_if_event_0_cfg_q <= i_wdata;

   assign o_dfi_lp_data_if_event_0_cfg = dfi_lp_data_if_event_0_cfg_q & `DDR_DFI_LP_DATA_IF_EVENT_0_CFG_MSK;

   logic [31:0] dfi_lp_data_if_event_1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfi_lp_data_if_event_1_cfg_q <= `DDR_DFI_LP_DATA_IF_EVENT_1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFI_LP_DATA_IF_EVENT_1_CFG)
               dfi_lp_data_if_event_1_cfg_q <= i_wdata;

   assign o_dfi_lp_data_if_event_1_cfg = dfi_lp_data_if_event_1_cfg_q & `DDR_DFI_LP_DATA_IF_EVENT_1_CFG_MSK;

   logic [31:0] dfi_phyupd_if_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfi_phyupd_if_cfg_q <= `DDR_DFI_PHYUPD_IF_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFI_PHYUPD_IF_CFG)
               dfi_phyupd_if_cfg_q <= i_wdata;

   assign o_dfi_phyupd_if_cfg = dfi_phyupd_if_cfg_q & `DDR_DFI_PHYUPD_IF_CFG_MSK;

   logic [31:0] dfi_phyupd_if_sta_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfi_phyupd_if_sta_q <= `DDR_DFI_PHYUPD_IF_STA_POR;
      else
         dfi_phyupd_if_sta_q <= i_dfi_phyupd_if_sta;

   logic [31:0] dfi_phymstr_if_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfi_phymstr_if_cfg_q <= `DDR_DFI_PHYMSTR_IF_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFI_PHYMSTR_IF_CFG)
               dfi_phymstr_if_cfg_q <= i_wdata;

   assign o_dfi_phymstr_if_cfg = dfi_phymstr_if_cfg_q & `DDR_DFI_PHYMSTR_IF_CFG_MSK;

   logic [31:0] dfi_phymstr_if_sta_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfi_phymstr_if_sta_q <= `DDR_DFI_PHYMSTR_IF_STA_POR;
      else
         dfi_phymstr_if_sta_q <= i_dfi_phymstr_if_sta;

   logic [31:0] dfi_debug_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfi_debug_cfg_q <= `DDR_DFI_DEBUG_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFI_DEBUG_CFG)
               dfi_debug_cfg_q <= i_wdata;

   assign o_dfi_debug_cfg = dfi_debug_cfg_q & `DDR_DFI_DEBUG_CFG_MSK;

   always_comb
      if (i_read)
         case (decode)
            DECODE_DDR_DFI_TOP_0_CFG : o_rdata = o_dfi_top_0_cfg;
            DECODE_DDR_DFI_DATA_BIT_ENABLE_CFG : o_rdata = o_dfi_data_bit_enable_cfg;
            DECODE_DDR_DFI_PHYFREQ_RANGE_CFG : o_rdata = o_dfi_phyfreq_range_cfg;
            DECODE_DDR_DFI_STATUS_IF_CFG : o_rdata = o_dfi_status_if_cfg;
            DECODE_DDR_DFI_STATUS_IF_STA : o_rdata = dfi_status_if_sta_q;
            DECODE_DDR_DFI_STATUS_IF_EVENT_0_CFG : o_rdata = o_dfi_status_if_event_0_cfg;
            DECODE_DDR_DFI_STATUS_IF_EVENT_1_CFG : o_rdata = o_dfi_status_if_event_1_cfg;
            DECODE_DDR_DFI_CTRLUPD_IF_CFG : o_rdata = o_dfi_ctrlupd_if_cfg;
            DECODE_DDR_DFI_CTRLUPD_IF_STA : o_rdata = dfi_ctrlupd_if_sta_q;
            DECODE_DDR_DFI_CTRLUPD_IF_EVENT_0_CFG : o_rdata = o_dfi_ctrlupd_if_event_0_cfg;
            DECODE_DDR_DFI_CTRLUPD_IF_EVENT_1_CFG : o_rdata = o_dfi_ctrlupd_if_event_1_cfg;
            DECODE_DDR_DFI_LP_CTRL_IF_CFG : o_rdata = o_dfi_lp_ctrl_if_cfg;
            DECODE_DDR_DFI_LP_CTRL_IF_STA : o_rdata = dfi_lp_ctrl_if_sta_q;
            DECODE_DDR_DFI_LP_CTRL_IF_EVENT_0_CFG : o_rdata = o_dfi_lp_ctrl_if_event_0_cfg;
            DECODE_DDR_DFI_LP_CTRL_IF_EVENT_1_CFG : o_rdata = o_dfi_lp_ctrl_if_event_1_cfg;
            DECODE_DDR_DFI_LP_DATA_IF_CFG : o_rdata = o_dfi_lp_data_if_cfg;
            DECODE_DDR_DFI_LP_DATA_IF_STA : o_rdata = dfi_lp_data_if_sta_q;
            DECODE_DDR_DFI_LP_DATA_IF_EVENT_0_CFG : o_rdata = o_dfi_lp_data_if_event_0_cfg;
            DECODE_DDR_DFI_LP_DATA_IF_EVENT_1_CFG : o_rdata = o_dfi_lp_data_if_event_1_cfg;
            DECODE_DDR_DFI_PHYUPD_IF_CFG : o_rdata = o_dfi_phyupd_if_cfg;
            DECODE_DDR_DFI_PHYUPD_IF_STA : o_rdata = dfi_phyupd_if_sta_q;
            DECODE_DDR_DFI_PHYMSTR_IF_CFG : o_rdata = o_dfi_phymstr_if_cfg;
            DECODE_DDR_DFI_PHYMSTR_IF_STA : o_rdata = dfi_phymstr_if_sta_q;
            DECODE_DDR_DFI_DEBUG_CFG : o_rdata = o_dfi_debug_cfg;
            default : o_rdata = '0;
         endcase
      else
         o_rdata = '0;

endmodule
