
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

module ddr_dfich_csr #(
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

   typedef enum logic [6:0] {
      DECODE_DDR_DFICH_TOP_1_CFG,
      DECODE_DDR_DFICH_TOP_2_CFG,
      DECODE_DDR_DFICH_TOP_3_CFG,
      DECODE_DDR_DFICH_TOP_STA,
      DECODE_DDR_DFICH_IG_DATA_CFG,
      DECODE_DDR_DFICH_EG_DATA_STA,
      DECODE_DDR_DFICH_WRC_M0_CFG,
      DECODE_DDR_DFICH_WRC_M1_CFG,
      DECODE_DDR_DFICH_WRCCTRL_M0_CFG,
      DECODE_DDR_DFICH_WRCCTRL_M1_CFG,
      DECODE_DDR_DFICH_CKCTRL_M0_CFG,
      DECODE_DDR_DFICH_CKCTRL_M1_CFG,
      DECODE_DDR_DFICH_RDC_M0_CFG,
      DECODE_DDR_DFICH_RDC_M1_CFG,
      DECODE_DDR_DFICH_RCTRL_M0_CFG,
      DECODE_DDR_DFICH_RCTRL_M1_CFG,
      DECODE_DDR_DFICH_WCTRL_M0_CFG,
      DECODE_DDR_DFICH_WCTRL_M1_CFG,
      DECODE_DDR_DFICH_WENCTRL_M0_CFG,
      DECODE_DDR_DFICH_WENCTRL_M1_CFG,
      DECODE_DDR_DFICH_WCKCTRL_M0_CFG,
      DECODE_DDR_DFICH_WCKCTRL_M1_CFG,
      DECODE_DDR_DFICH_WRD_M0_CFG,
      DECODE_DDR_DFICH_WRD_M1_CFG,
      DECODE_DDR_DFICH_RDD_M0_CFG,
      DECODE_DDR_DFICH_RDD_M1_CFG,
      DECODE_DDR_DFICH_CTRL0_M0_CFG,
      DECODE_DDR_DFICH_CTRL0_M1_CFG,
      DECODE_DDR_DFICH_CTRL1_M0_CFG,
      DECODE_DDR_DFICH_CTRL1_M1_CFG,
      DECODE_DDR_DFICH_CTRL2_M0_CFG,
      DECODE_DDR_DFICH_CTRL2_M1_CFG,
      DECODE_DDR_DFICH_CTRL3_M0_CFG,
      DECODE_DDR_DFICH_CTRL3_M1_CFG,
      DECODE_DDR_DFICH_CTRL4_M0_CFG,
      DECODE_DDR_DFICH_CTRL4_M1_CFG,
      DECODE_DDR_DFICH_CTRL5_M0_CFG,
      DECODE_DDR_DFICH_CTRL5_M1_CFG,
      DECODE_NOOP
   } DECODE_T;

   DECODE_T decode;

   assign o_ready = 1'b1;

   always_comb begin
      o_error = 1'b0;
      case (i_addr)
         `DDR_DFICH_TOP_1_CFG_ADR : decode = DECODE_DDR_DFICH_TOP_1_CFG;
         `DDR_DFICH_TOP_2_CFG_ADR : decode = DECODE_DDR_DFICH_TOP_2_CFG;
         `DDR_DFICH_TOP_3_CFG_ADR : decode = DECODE_DDR_DFICH_TOP_3_CFG;
         `DDR_DFICH_TOP_STA_ADR : decode = DECODE_DDR_DFICH_TOP_STA;
         `DDR_DFICH_IG_DATA_CFG_ADR : decode = DECODE_DDR_DFICH_IG_DATA_CFG;
         `DDR_DFICH_EG_DATA_STA_ADR : decode = DECODE_DDR_DFICH_EG_DATA_STA;
         `DDR_DFICH_WRC_M0_CFG_ADR : decode = DECODE_DDR_DFICH_WRC_M0_CFG;
         `DDR_DFICH_WRC_M1_CFG_ADR : decode = DECODE_DDR_DFICH_WRC_M1_CFG;
         `DDR_DFICH_WRCCTRL_M0_CFG_ADR : decode = DECODE_DDR_DFICH_WRCCTRL_M0_CFG;
         `DDR_DFICH_WRCCTRL_M1_CFG_ADR : decode = DECODE_DDR_DFICH_WRCCTRL_M1_CFG;
         `DDR_DFICH_CKCTRL_M0_CFG_ADR : decode = DECODE_DDR_DFICH_CKCTRL_M0_CFG;
         `DDR_DFICH_CKCTRL_M1_CFG_ADR : decode = DECODE_DDR_DFICH_CKCTRL_M1_CFG;
         `DDR_DFICH_RDC_M0_CFG_ADR : decode = DECODE_DDR_DFICH_RDC_M0_CFG;
         `DDR_DFICH_RDC_M1_CFG_ADR : decode = DECODE_DDR_DFICH_RDC_M1_CFG;
         `DDR_DFICH_RCTRL_M0_CFG_ADR : decode = DECODE_DDR_DFICH_RCTRL_M0_CFG;
         `DDR_DFICH_RCTRL_M1_CFG_ADR : decode = DECODE_DDR_DFICH_RCTRL_M1_CFG;
         `DDR_DFICH_WCTRL_M0_CFG_ADR : decode = DECODE_DDR_DFICH_WCTRL_M0_CFG;
         `DDR_DFICH_WCTRL_M1_CFG_ADR : decode = DECODE_DDR_DFICH_WCTRL_M1_CFG;
         `DDR_DFICH_WENCTRL_M0_CFG_ADR : decode = DECODE_DDR_DFICH_WENCTRL_M0_CFG;
         `DDR_DFICH_WENCTRL_M1_CFG_ADR : decode = DECODE_DDR_DFICH_WENCTRL_M1_CFG;
         `DDR_DFICH_WCKCTRL_M0_CFG_ADR : decode = DECODE_DDR_DFICH_WCKCTRL_M0_CFG;
         `DDR_DFICH_WCKCTRL_M1_CFG_ADR : decode = DECODE_DDR_DFICH_WCKCTRL_M1_CFG;
         `DDR_DFICH_WRD_M0_CFG_ADR : decode = DECODE_DDR_DFICH_WRD_M0_CFG;
         `DDR_DFICH_WRD_M1_CFG_ADR : decode = DECODE_DDR_DFICH_WRD_M1_CFG;
         `DDR_DFICH_RDD_M0_CFG_ADR : decode = DECODE_DDR_DFICH_RDD_M0_CFG;
         `DDR_DFICH_RDD_M1_CFG_ADR : decode = DECODE_DDR_DFICH_RDD_M1_CFG;
         `DDR_DFICH_CTRL0_M0_CFG_ADR : decode = DECODE_DDR_DFICH_CTRL0_M0_CFG;
         `DDR_DFICH_CTRL0_M1_CFG_ADR : decode = DECODE_DDR_DFICH_CTRL0_M1_CFG;
         `DDR_DFICH_CTRL1_M0_CFG_ADR : decode = DECODE_DDR_DFICH_CTRL1_M0_CFG;
         `DDR_DFICH_CTRL1_M1_CFG_ADR : decode = DECODE_DDR_DFICH_CTRL1_M1_CFG;
         `DDR_DFICH_CTRL2_M0_CFG_ADR : decode = DECODE_DDR_DFICH_CTRL2_M0_CFG;
         `DDR_DFICH_CTRL2_M1_CFG_ADR : decode = DECODE_DDR_DFICH_CTRL2_M1_CFG;
         `DDR_DFICH_CTRL3_M0_CFG_ADR : decode = DECODE_DDR_DFICH_CTRL3_M0_CFG;
         `DDR_DFICH_CTRL3_M1_CFG_ADR : decode = DECODE_DDR_DFICH_CTRL3_M1_CFG;
         `DDR_DFICH_CTRL4_M0_CFG_ADR : decode = DECODE_DDR_DFICH_CTRL4_M0_CFG;
         `DDR_DFICH_CTRL4_M1_CFG_ADR : decode = DECODE_DDR_DFICH_CTRL4_M1_CFG;
         `DDR_DFICH_CTRL5_M0_CFG_ADR : decode = DECODE_DDR_DFICH_CTRL5_M0_CFG;
         `DDR_DFICH_CTRL5_M1_CFG_ADR : decode = DECODE_DDR_DFICH_CTRL5_M1_CFG;
         default : begin 
            decode = DECODE_NOOP;
            o_error = 1'b1;
         end
      endcase
   end

   logic [31:0] dfich_top_1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_top_1_cfg_q <= `DDR_DFICH_TOP_1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_TOP_1_CFG)
               dfich_top_1_cfg_q <= i_wdata;

   assign o_dfich_top_1_cfg = dfich_top_1_cfg_q & `DDR_DFICH_TOP_1_CFG_MSK;

   logic [31:0] dfich_top_2_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_top_2_cfg_q <= `DDR_DFICH_TOP_2_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_TOP_2_CFG)
               dfich_top_2_cfg_q <= i_wdata;

   assign o_dfich_top_2_cfg = dfich_top_2_cfg_q & `DDR_DFICH_TOP_2_CFG_MSK;

   logic [31:0] dfich_top_3_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_top_3_cfg_q <= `DDR_DFICH_TOP_3_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_TOP_3_CFG)
               dfich_top_3_cfg_q <= i_wdata;

   assign o_dfich_top_3_cfg = dfich_top_3_cfg_q & `DDR_DFICH_TOP_3_CFG_MSK;

   logic [31:0] dfich_top_sta_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_top_sta_q <= `DDR_DFICH_TOP_STA_POR;
      else
         dfich_top_sta_q <= i_dfich_top_sta;

   logic [31:0] dfich_ig_data_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_ig_data_cfg_q <= `DDR_DFICH_IG_DATA_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_IG_DATA_CFG)
               dfich_ig_data_cfg_q <= i_wdata;

   assign o_dfich_ig_data_cfg = dfich_ig_data_cfg_q & `DDR_DFICH_IG_DATA_CFG_MSK;

   logic [31:0] dfich_eg_data_sta_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_eg_data_sta_q <= `DDR_DFICH_EG_DATA_STA_POR;
      else
         dfich_eg_data_sta_q <= i_dfich_eg_data_sta;

   logic [31:0] dfich_wrc_m0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_wrc_m0_cfg_q <= `DDR_DFICH_WRC_M0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_WRC_M0_CFG)
               dfich_wrc_m0_cfg_q <= i_wdata;

   assign o_dfich_wrc_m0_cfg = dfich_wrc_m0_cfg_q & `DDR_DFICH_WRC_M0_CFG_MSK;

   logic [31:0] dfich_wrc_m1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_wrc_m1_cfg_q <= `DDR_DFICH_WRC_M1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_WRC_M1_CFG)
               dfich_wrc_m1_cfg_q <= i_wdata;

   assign o_dfich_wrc_m1_cfg = dfich_wrc_m1_cfg_q & `DDR_DFICH_WRC_M1_CFG_MSK;

   logic [31:0] dfich_wrcctrl_m0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_wrcctrl_m0_cfg_q <= `DDR_DFICH_WRCCTRL_M0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_WRCCTRL_M0_CFG)
               dfich_wrcctrl_m0_cfg_q <= i_wdata;

   assign o_dfich_wrcctrl_m0_cfg = dfich_wrcctrl_m0_cfg_q & `DDR_DFICH_WRCCTRL_M0_CFG_MSK;

   logic [31:0] dfich_wrcctrl_m1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_wrcctrl_m1_cfg_q <= `DDR_DFICH_WRCCTRL_M1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_WRCCTRL_M1_CFG)
               dfich_wrcctrl_m1_cfg_q <= i_wdata;

   assign o_dfich_wrcctrl_m1_cfg = dfich_wrcctrl_m1_cfg_q & `DDR_DFICH_WRCCTRL_M1_CFG_MSK;

   logic [31:0] dfich_ckctrl_m0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_ckctrl_m0_cfg_q <= `DDR_DFICH_CKCTRL_M0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_CKCTRL_M0_CFG)
               dfich_ckctrl_m0_cfg_q <= i_wdata;

   assign o_dfich_ckctrl_m0_cfg = dfich_ckctrl_m0_cfg_q & `DDR_DFICH_CKCTRL_M0_CFG_MSK;

   logic [31:0] dfich_ckctrl_m1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_ckctrl_m1_cfg_q <= `DDR_DFICH_CKCTRL_M1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_CKCTRL_M1_CFG)
               dfich_ckctrl_m1_cfg_q <= i_wdata;

   assign o_dfich_ckctrl_m1_cfg = dfich_ckctrl_m1_cfg_q & `DDR_DFICH_CKCTRL_M1_CFG_MSK;

   logic [31:0] dfich_rdc_m0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_rdc_m0_cfg_q <= `DDR_DFICH_RDC_M0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_RDC_M0_CFG)
               dfich_rdc_m0_cfg_q <= i_wdata;

   assign o_dfich_rdc_m0_cfg = dfich_rdc_m0_cfg_q & `DDR_DFICH_RDC_M0_CFG_MSK;

   logic [31:0] dfich_rdc_m1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_rdc_m1_cfg_q <= `DDR_DFICH_RDC_M1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_RDC_M1_CFG)
               dfich_rdc_m1_cfg_q <= i_wdata;

   assign o_dfich_rdc_m1_cfg = dfich_rdc_m1_cfg_q & `DDR_DFICH_RDC_M1_CFG_MSK;

   logic [31:0] dfich_rctrl_m0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_rctrl_m0_cfg_q <= `DDR_DFICH_RCTRL_M0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_RCTRL_M0_CFG)
               dfich_rctrl_m0_cfg_q <= i_wdata;

   assign o_dfich_rctrl_m0_cfg = dfich_rctrl_m0_cfg_q & `DDR_DFICH_RCTRL_M0_CFG_MSK;

   logic [31:0] dfich_rctrl_m1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_rctrl_m1_cfg_q <= `DDR_DFICH_RCTRL_M1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_RCTRL_M1_CFG)
               dfich_rctrl_m1_cfg_q <= i_wdata;

   assign o_dfich_rctrl_m1_cfg = dfich_rctrl_m1_cfg_q & `DDR_DFICH_RCTRL_M1_CFG_MSK;

   logic [31:0] dfich_wctrl_m0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_wctrl_m0_cfg_q <= `DDR_DFICH_WCTRL_M0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_WCTRL_M0_CFG)
               dfich_wctrl_m0_cfg_q <= i_wdata;

   assign o_dfich_wctrl_m0_cfg = dfich_wctrl_m0_cfg_q & `DDR_DFICH_WCTRL_M0_CFG_MSK;

   logic [31:0] dfich_wctrl_m1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_wctrl_m1_cfg_q <= `DDR_DFICH_WCTRL_M1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_WCTRL_M1_CFG)
               dfich_wctrl_m1_cfg_q <= i_wdata;

   assign o_dfich_wctrl_m1_cfg = dfich_wctrl_m1_cfg_q & `DDR_DFICH_WCTRL_M1_CFG_MSK;

   logic [31:0] dfich_wenctrl_m0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_wenctrl_m0_cfg_q <= `DDR_DFICH_WENCTRL_M0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_WENCTRL_M0_CFG)
               dfich_wenctrl_m0_cfg_q <= i_wdata;

   assign o_dfich_wenctrl_m0_cfg = dfich_wenctrl_m0_cfg_q & `DDR_DFICH_WENCTRL_M0_CFG_MSK;

   logic [31:0] dfich_wenctrl_m1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_wenctrl_m1_cfg_q <= `DDR_DFICH_WENCTRL_M1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_WENCTRL_M1_CFG)
               dfich_wenctrl_m1_cfg_q <= i_wdata;

   assign o_dfich_wenctrl_m1_cfg = dfich_wenctrl_m1_cfg_q & `DDR_DFICH_WENCTRL_M1_CFG_MSK;

   logic [31:0] dfich_wckctrl_m0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_wckctrl_m0_cfg_q <= `DDR_DFICH_WCKCTRL_M0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_WCKCTRL_M0_CFG)
               dfich_wckctrl_m0_cfg_q <= i_wdata;

   assign o_dfich_wckctrl_m0_cfg = dfich_wckctrl_m0_cfg_q & `DDR_DFICH_WCKCTRL_M0_CFG_MSK;

   logic [31:0] dfich_wckctrl_m1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_wckctrl_m1_cfg_q <= `DDR_DFICH_WCKCTRL_M1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_WCKCTRL_M1_CFG)
               dfich_wckctrl_m1_cfg_q <= i_wdata;

   assign o_dfich_wckctrl_m1_cfg = dfich_wckctrl_m1_cfg_q & `DDR_DFICH_WCKCTRL_M1_CFG_MSK;

   logic [31:0] dfich_wrd_m0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_wrd_m0_cfg_q <= `DDR_DFICH_WRD_M0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_WRD_M0_CFG)
               dfich_wrd_m0_cfg_q <= i_wdata;

   assign o_dfich_wrd_m0_cfg = dfich_wrd_m0_cfg_q & `DDR_DFICH_WRD_M0_CFG_MSK;

   logic [31:0] dfich_wrd_m1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_wrd_m1_cfg_q <= `DDR_DFICH_WRD_M1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_WRD_M1_CFG)
               dfich_wrd_m1_cfg_q <= i_wdata;

   assign o_dfich_wrd_m1_cfg = dfich_wrd_m1_cfg_q & `DDR_DFICH_WRD_M1_CFG_MSK;

   logic [31:0] dfich_rdd_m0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_rdd_m0_cfg_q <= `DDR_DFICH_RDD_M0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_RDD_M0_CFG)
               dfich_rdd_m0_cfg_q <= i_wdata;

   assign o_dfich_rdd_m0_cfg = dfich_rdd_m0_cfg_q & `DDR_DFICH_RDD_M0_CFG_MSK;

   logic [31:0] dfich_rdd_m1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_rdd_m1_cfg_q <= `DDR_DFICH_RDD_M1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_RDD_M1_CFG)
               dfich_rdd_m1_cfg_q <= i_wdata;

   assign o_dfich_rdd_m1_cfg = dfich_rdd_m1_cfg_q & `DDR_DFICH_RDD_M1_CFG_MSK;

   logic [31:0] dfich_ctrl0_m0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_ctrl0_m0_cfg_q <= `DDR_DFICH_CTRL0_M0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_CTRL0_M0_CFG)
               dfich_ctrl0_m0_cfg_q <= i_wdata;

   assign o_dfich_ctrl0_m0_cfg = dfich_ctrl0_m0_cfg_q & `DDR_DFICH_CTRL0_M0_CFG_MSK;

   logic [31:0] dfich_ctrl0_m1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_ctrl0_m1_cfg_q <= `DDR_DFICH_CTRL0_M1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_CTRL0_M1_CFG)
               dfich_ctrl0_m1_cfg_q <= i_wdata;

   assign o_dfich_ctrl0_m1_cfg = dfich_ctrl0_m1_cfg_q & `DDR_DFICH_CTRL0_M1_CFG_MSK;

   logic [31:0] dfich_ctrl1_m0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_ctrl1_m0_cfg_q <= `DDR_DFICH_CTRL1_M0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_CTRL1_M0_CFG)
               dfich_ctrl1_m0_cfg_q <= i_wdata;

   assign o_dfich_ctrl1_m0_cfg = dfich_ctrl1_m0_cfg_q & `DDR_DFICH_CTRL1_M0_CFG_MSK;

   logic [31:0] dfich_ctrl1_m1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_ctrl1_m1_cfg_q <= `DDR_DFICH_CTRL1_M1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_CTRL1_M1_CFG)
               dfich_ctrl1_m1_cfg_q <= i_wdata;

   assign o_dfich_ctrl1_m1_cfg = dfich_ctrl1_m1_cfg_q & `DDR_DFICH_CTRL1_M1_CFG_MSK;

   logic [31:0] dfich_ctrl2_m0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_ctrl2_m0_cfg_q <= `DDR_DFICH_CTRL2_M0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_CTRL2_M0_CFG)
               dfich_ctrl2_m0_cfg_q <= i_wdata;

   assign o_dfich_ctrl2_m0_cfg = dfich_ctrl2_m0_cfg_q & `DDR_DFICH_CTRL2_M0_CFG_MSK;

   logic [31:0] dfich_ctrl2_m1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_ctrl2_m1_cfg_q <= `DDR_DFICH_CTRL2_M1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_CTRL2_M1_CFG)
               dfich_ctrl2_m1_cfg_q <= i_wdata;

   assign o_dfich_ctrl2_m1_cfg = dfich_ctrl2_m1_cfg_q & `DDR_DFICH_CTRL2_M1_CFG_MSK;

   logic [31:0] dfich_ctrl3_m0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_ctrl3_m0_cfg_q <= `DDR_DFICH_CTRL3_M0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_CTRL3_M0_CFG)
               dfich_ctrl3_m0_cfg_q <= i_wdata;

   assign o_dfich_ctrl3_m0_cfg = dfich_ctrl3_m0_cfg_q & `DDR_DFICH_CTRL3_M0_CFG_MSK;

   logic [31:0] dfich_ctrl3_m1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_ctrl3_m1_cfg_q <= `DDR_DFICH_CTRL3_M1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_CTRL3_M1_CFG)
               dfich_ctrl3_m1_cfg_q <= i_wdata;

   assign o_dfich_ctrl3_m1_cfg = dfich_ctrl3_m1_cfg_q & `DDR_DFICH_CTRL3_M1_CFG_MSK;

   logic [31:0] dfich_ctrl4_m0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_ctrl4_m0_cfg_q <= `DDR_DFICH_CTRL4_M0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_CTRL4_M0_CFG)
               dfich_ctrl4_m0_cfg_q <= i_wdata;

   assign o_dfich_ctrl4_m0_cfg = dfich_ctrl4_m0_cfg_q & `DDR_DFICH_CTRL4_M0_CFG_MSK;

   logic [31:0] dfich_ctrl4_m1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_ctrl4_m1_cfg_q <= `DDR_DFICH_CTRL4_M1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_CTRL4_M1_CFG)
               dfich_ctrl4_m1_cfg_q <= i_wdata;

   assign o_dfich_ctrl4_m1_cfg = dfich_ctrl4_m1_cfg_q & `DDR_DFICH_CTRL4_M1_CFG_MSK;

   logic [31:0] dfich_ctrl5_m0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_ctrl5_m0_cfg_q <= `DDR_DFICH_CTRL5_M0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_CTRL5_M0_CFG)
               dfich_ctrl5_m0_cfg_q <= i_wdata;

   assign o_dfich_ctrl5_m0_cfg = dfich_ctrl5_m0_cfg_q & `DDR_DFICH_CTRL5_M0_CFG_MSK;

   logic [31:0] dfich_ctrl5_m1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dfich_ctrl5_m1_cfg_q <= `DDR_DFICH_CTRL5_M1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DFICH_CTRL5_M1_CFG)
               dfich_ctrl5_m1_cfg_q <= i_wdata;

   assign o_dfich_ctrl5_m1_cfg = dfich_ctrl5_m1_cfg_q & `DDR_DFICH_CTRL5_M1_CFG_MSK;

   always_comb
      if (i_read)
         case (decode)
            DECODE_DDR_DFICH_TOP_1_CFG : o_rdata = o_dfich_top_1_cfg;
            DECODE_DDR_DFICH_TOP_2_CFG : o_rdata = o_dfich_top_2_cfg;
            DECODE_DDR_DFICH_TOP_3_CFG : o_rdata = o_dfich_top_3_cfg;
            DECODE_DDR_DFICH_TOP_STA : o_rdata = dfich_top_sta_q;
            DECODE_DDR_DFICH_IG_DATA_CFG : o_rdata = o_dfich_ig_data_cfg;
            DECODE_DDR_DFICH_EG_DATA_STA : o_rdata = dfich_eg_data_sta_q;
            DECODE_DDR_DFICH_WRC_M0_CFG : o_rdata = o_dfich_wrc_m0_cfg;
            DECODE_DDR_DFICH_WRC_M1_CFG : o_rdata = o_dfich_wrc_m1_cfg;
            DECODE_DDR_DFICH_WRCCTRL_M0_CFG : o_rdata = o_dfich_wrcctrl_m0_cfg;
            DECODE_DDR_DFICH_WRCCTRL_M1_CFG : o_rdata = o_dfich_wrcctrl_m1_cfg;
            DECODE_DDR_DFICH_CKCTRL_M0_CFG : o_rdata = o_dfich_ckctrl_m0_cfg;
            DECODE_DDR_DFICH_CKCTRL_M1_CFG : o_rdata = o_dfich_ckctrl_m1_cfg;
            DECODE_DDR_DFICH_RDC_M0_CFG : o_rdata = o_dfich_rdc_m0_cfg;
            DECODE_DDR_DFICH_RDC_M1_CFG : o_rdata = o_dfich_rdc_m1_cfg;
            DECODE_DDR_DFICH_RCTRL_M0_CFG : o_rdata = o_dfich_rctrl_m0_cfg;
            DECODE_DDR_DFICH_RCTRL_M1_CFG : o_rdata = o_dfich_rctrl_m1_cfg;
            DECODE_DDR_DFICH_WCTRL_M0_CFG : o_rdata = o_dfich_wctrl_m0_cfg;
            DECODE_DDR_DFICH_WCTRL_M1_CFG : o_rdata = o_dfich_wctrl_m1_cfg;
            DECODE_DDR_DFICH_WENCTRL_M0_CFG : o_rdata = o_dfich_wenctrl_m0_cfg;
            DECODE_DDR_DFICH_WENCTRL_M1_CFG : o_rdata = o_dfich_wenctrl_m1_cfg;
            DECODE_DDR_DFICH_WCKCTRL_M0_CFG : o_rdata = o_dfich_wckctrl_m0_cfg;
            DECODE_DDR_DFICH_WCKCTRL_M1_CFG : o_rdata = o_dfich_wckctrl_m1_cfg;
            DECODE_DDR_DFICH_WRD_M0_CFG : o_rdata = o_dfich_wrd_m0_cfg;
            DECODE_DDR_DFICH_WRD_M1_CFG : o_rdata = o_dfich_wrd_m1_cfg;
            DECODE_DDR_DFICH_RDD_M0_CFG : o_rdata = o_dfich_rdd_m0_cfg;
            DECODE_DDR_DFICH_RDD_M1_CFG : o_rdata = o_dfich_rdd_m1_cfg;
            DECODE_DDR_DFICH_CTRL0_M0_CFG : o_rdata = o_dfich_ctrl0_m0_cfg;
            DECODE_DDR_DFICH_CTRL0_M1_CFG : o_rdata = o_dfich_ctrl0_m1_cfg;
            DECODE_DDR_DFICH_CTRL1_M0_CFG : o_rdata = o_dfich_ctrl1_m0_cfg;
            DECODE_DDR_DFICH_CTRL1_M1_CFG : o_rdata = o_dfich_ctrl1_m1_cfg;
            DECODE_DDR_DFICH_CTRL2_M0_CFG : o_rdata = o_dfich_ctrl2_m0_cfg;
            DECODE_DDR_DFICH_CTRL2_M1_CFG : o_rdata = o_dfich_ctrl2_m1_cfg;
            DECODE_DDR_DFICH_CTRL3_M0_CFG : o_rdata = o_dfich_ctrl3_m0_cfg;
            DECODE_DDR_DFICH_CTRL3_M1_CFG : o_rdata = o_dfich_ctrl3_m1_cfg;
            DECODE_DDR_DFICH_CTRL4_M0_CFG : o_rdata = o_dfich_ctrl4_m0_cfg;
            DECODE_DDR_DFICH_CTRL4_M1_CFG : o_rdata = o_dfich_ctrl4_m1_cfg;
            DECODE_DDR_DFICH_CTRL5_M0_CFG : o_rdata = o_dfich_ctrl5_m0_cfg;
            DECODE_DDR_DFICH_CTRL5_M1_CFG : o_rdata = o_dfich_ctrl5_m1_cfg;
            default : o_rdata = '0;
         endcase
      else
         o_rdata = '0;

endmodule
