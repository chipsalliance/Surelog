
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

import ddr_global_pkg::*;

module ddr_cmn_csr #(
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
   output  logic [`DDR_CMN_VREF_M0_CFG_RANGE] o_cmn_vref_m0_cfg,
   output  logic [`DDR_CMN_VREF_M1_CFG_RANGE] o_cmn_vref_m1_cfg,
   output  logic [`DDR_CMN_ZQCAL_CFG_RANGE] o_cmn_zqcal_cfg,
   input   logic [`DDR_CMN_ZQCAL_STA_RANGE] i_cmn_zqcal_sta,
   output  logic [`DDR_CMN_IBIAS_CFG_RANGE] o_cmn_ibias_cfg,
   output  logic [`DDR_CMN_TEST_CFG_RANGE] o_cmn_test_cfg,
   output  logic [`DDR_CMN_LDO_M0_CFG_RANGE] o_cmn_ldo_m0_cfg,
   output  logic [`DDR_CMN_LDO_M1_CFG_RANGE] o_cmn_ldo_m1_cfg,
   output  logic [`DDR_CMN_CLK_CTRL_CFG_RANGE] o_cmn_clk_ctrl_cfg,
   output  logic [`DDR_CMN_PMON_ANA_CFG_RANGE] o_cmn_pmon_ana_cfg,
   output  logic [`DDR_CMN_PMON_DIG_CFG_RANGE] o_cmn_pmon_dig_cfg,
   output  logic [`DDR_CMN_PMON_DIG_NAND_CFG_RANGE] o_cmn_pmon_dig_nand_cfg,
   output  logic [`DDR_CMN_PMON_DIG_NOR_CFG_RANGE] o_cmn_pmon_dig_nor_cfg,
   input   logic [`DDR_CMN_PMON_NAND_STA_RANGE] i_cmn_pmon_nand_sta,
   input   logic [`DDR_CMN_PMON_NOR_STA_RANGE] i_cmn_pmon_nor_sta,
   input   logic [`DDR_CMN_CLK_STA_RANGE] i_cmn_clk_sta,
   output  logic [`DDR_CMN_RSTN_CFG_RANGE] o_cmn_rstn_cfg,
   input   logic [`DDR_CMN_RSTN_STA_RANGE] i_cmn_rstn_sta
);

   typedef enum logic [5:0] {
      DECODE_DDR_CMN_VREF_M0_CFG,
      DECODE_DDR_CMN_VREF_M1_CFG,
      DECODE_DDR_CMN_ZQCAL_CFG,
      DECODE_DDR_CMN_ZQCAL_STA,
      DECODE_DDR_CMN_IBIAS_CFG,
      DECODE_DDR_CMN_TEST_CFG,
      DECODE_DDR_CMN_LDO_M0_CFG,
      DECODE_DDR_CMN_LDO_M1_CFG,
      DECODE_DDR_CMN_CLK_CTRL_CFG,
      DECODE_DDR_CMN_PMON_ANA_CFG,
      DECODE_DDR_CMN_PMON_DIG_CFG,
      DECODE_DDR_CMN_PMON_DIG_NAND_CFG,
      DECODE_DDR_CMN_PMON_DIG_NOR_CFG,
      DECODE_DDR_CMN_PMON_NAND_STA,
      DECODE_DDR_CMN_PMON_NOR_STA,
      DECODE_DDR_CMN_CLK_STA,
      DECODE_DDR_CMN_RSTN_CFG,
      DECODE_DDR_CMN_RSTN_STA,
      DECODE_NOOP
   } DECODE_T;

   DECODE_T decode;

   assign o_ready = 1'b1;

   always_comb begin
      o_error = 1'b0;
      case (i_addr)
         `DDR_CMN_VREF_M0_CFG_ADR : decode = DECODE_DDR_CMN_VREF_M0_CFG;
         `DDR_CMN_VREF_M1_CFG_ADR : decode = DECODE_DDR_CMN_VREF_M1_CFG;
         `DDR_CMN_ZQCAL_CFG_ADR : decode = DECODE_DDR_CMN_ZQCAL_CFG;
         `DDR_CMN_ZQCAL_STA_ADR : decode = DECODE_DDR_CMN_ZQCAL_STA;
         `DDR_CMN_IBIAS_CFG_ADR : decode = DECODE_DDR_CMN_IBIAS_CFG;
         `DDR_CMN_TEST_CFG_ADR : decode = DECODE_DDR_CMN_TEST_CFG;
         `DDR_CMN_LDO_M0_CFG_ADR : decode = DECODE_DDR_CMN_LDO_M0_CFG;
         `DDR_CMN_LDO_M1_CFG_ADR : decode = DECODE_DDR_CMN_LDO_M1_CFG;
         `DDR_CMN_CLK_CTRL_CFG_ADR : decode = DECODE_DDR_CMN_CLK_CTRL_CFG;
         `DDR_CMN_PMON_ANA_CFG_ADR : decode = DECODE_DDR_CMN_PMON_ANA_CFG;
         `DDR_CMN_PMON_DIG_CFG_ADR : decode = DECODE_DDR_CMN_PMON_DIG_CFG;
         `DDR_CMN_PMON_DIG_NAND_CFG_ADR : decode = DECODE_DDR_CMN_PMON_DIG_NAND_CFG;
         `DDR_CMN_PMON_DIG_NOR_CFG_ADR : decode = DECODE_DDR_CMN_PMON_DIG_NOR_CFG;
         `DDR_CMN_PMON_NAND_STA_ADR : decode = DECODE_DDR_CMN_PMON_NAND_STA;
         `DDR_CMN_PMON_NOR_STA_ADR : decode = DECODE_DDR_CMN_PMON_NOR_STA;
         `DDR_CMN_CLK_STA_ADR : decode = DECODE_DDR_CMN_CLK_STA;
         `DDR_CMN_RSTN_CFG_ADR : decode = DECODE_DDR_CMN_RSTN_CFG;
         `DDR_CMN_RSTN_STA_ADR : decode = DECODE_DDR_CMN_RSTN_STA;
         default : begin 
            decode = DECODE_NOOP;
            o_error = 1'b1;
         end
      endcase
   end

   logic [31:0] cmn_vref_m0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         cmn_vref_m0_cfg_q <= `DDR_CMN_VREF_M0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_CMN_VREF_M0_CFG)
               cmn_vref_m0_cfg_q <= i_wdata;

   assign o_cmn_vref_m0_cfg = cmn_vref_m0_cfg_q & `DDR_CMN_VREF_M0_CFG_MSK;

   logic [31:0] cmn_vref_m1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         cmn_vref_m1_cfg_q <= `DDR_CMN_VREF_M1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_CMN_VREF_M1_CFG)
               cmn_vref_m1_cfg_q <= i_wdata;

   assign o_cmn_vref_m1_cfg = cmn_vref_m1_cfg_q & `DDR_CMN_VREF_M1_CFG_MSK;

   logic [31:0] cmn_zqcal_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         cmn_zqcal_cfg_q <= `DDR_CMN_ZQCAL_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_CMN_ZQCAL_CFG)
               cmn_zqcal_cfg_q <= i_wdata;

   assign o_cmn_zqcal_cfg = cmn_zqcal_cfg_q & `DDR_CMN_ZQCAL_CFG_MSK;

   logic [31:0] cmn_zqcal_sta_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         cmn_zqcal_sta_q <= `DDR_CMN_ZQCAL_STA_POR;
      else
         cmn_zqcal_sta_q <= i_cmn_zqcal_sta;

   logic [31:0] cmn_ibias_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         cmn_ibias_cfg_q <= `DDR_CMN_IBIAS_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_CMN_IBIAS_CFG)
               cmn_ibias_cfg_q <= i_wdata;

   assign o_cmn_ibias_cfg = cmn_ibias_cfg_q & `DDR_CMN_IBIAS_CFG_MSK;

   logic [31:0] cmn_test_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         cmn_test_cfg_q <= `DDR_CMN_TEST_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_CMN_TEST_CFG)
               cmn_test_cfg_q <= i_wdata;

   assign o_cmn_test_cfg = cmn_test_cfg_q & `DDR_CMN_TEST_CFG_MSK;

   logic [31:0] cmn_ldo_m0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         cmn_ldo_m0_cfg_q <= `DDR_CMN_LDO_M0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_CMN_LDO_M0_CFG)
               cmn_ldo_m0_cfg_q <= i_wdata;

   assign o_cmn_ldo_m0_cfg = cmn_ldo_m0_cfg_q & `DDR_CMN_LDO_M0_CFG_MSK;

   logic [31:0] cmn_ldo_m1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         cmn_ldo_m1_cfg_q <= `DDR_CMN_LDO_M1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_CMN_LDO_M1_CFG)
               cmn_ldo_m1_cfg_q <= i_wdata;

   assign o_cmn_ldo_m1_cfg = cmn_ldo_m1_cfg_q & `DDR_CMN_LDO_M1_CFG_MSK;

   logic [31:0] cmn_clk_ctrl_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         cmn_clk_ctrl_cfg_q <= `DDR_CMN_CLK_CTRL_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_CMN_CLK_CTRL_CFG)
               cmn_clk_ctrl_cfg_q <= i_wdata;

   assign o_cmn_clk_ctrl_cfg = cmn_clk_ctrl_cfg_q & `DDR_CMN_CLK_CTRL_CFG_MSK;

   logic [31:0] cmn_pmon_ana_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         cmn_pmon_ana_cfg_q <= `DDR_CMN_PMON_ANA_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_CMN_PMON_ANA_CFG)
               cmn_pmon_ana_cfg_q <= i_wdata;

   assign o_cmn_pmon_ana_cfg = cmn_pmon_ana_cfg_q & `DDR_CMN_PMON_ANA_CFG_MSK;

   logic [31:0] cmn_pmon_dig_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         cmn_pmon_dig_cfg_q <= `DDR_CMN_PMON_DIG_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_CMN_PMON_DIG_CFG)
               cmn_pmon_dig_cfg_q <= i_wdata;

   assign o_cmn_pmon_dig_cfg = cmn_pmon_dig_cfg_q & `DDR_CMN_PMON_DIG_CFG_MSK;

   logic [31:0] cmn_pmon_dig_nand_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         cmn_pmon_dig_nand_cfg_q <= `DDR_CMN_PMON_DIG_NAND_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_CMN_PMON_DIG_NAND_CFG)
               cmn_pmon_dig_nand_cfg_q <= i_wdata;

   assign o_cmn_pmon_dig_nand_cfg = cmn_pmon_dig_nand_cfg_q & `DDR_CMN_PMON_DIG_NAND_CFG_MSK;

   logic [31:0] cmn_pmon_dig_nor_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         cmn_pmon_dig_nor_cfg_q <= `DDR_CMN_PMON_DIG_NOR_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_CMN_PMON_DIG_NOR_CFG)
               cmn_pmon_dig_nor_cfg_q <= i_wdata;

   assign o_cmn_pmon_dig_nor_cfg = cmn_pmon_dig_nor_cfg_q & `DDR_CMN_PMON_DIG_NOR_CFG_MSK;

   logic [31:0] cmn_pmon_nand_sta_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         cmn_pmon_nand_sta_q <= `DDR_CMN_PMON_NAND_STA_POR;
      else
         cmn_pmon_nand_sta_q <= i_cmn_pmon_nand_sta;

   logic [31:0] cmn_pmon_nor_sta_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         cmn_pmon_nor_sta_q <= `DDR_CMN_PMON_NOR_STA_POR;
      else
         cmn_pmon_nor_sta_q <= i_cmn_pmon_nor_sta;

   logic [31:0] cmn_clk_sta_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         cmn_clk_sta_q <= `DDR_CMN_CLK_STA_POR;
      else
         cmn_clk_sta_q <= i_cmn_clk_sta;

   logic [31:0] cmn_rstn_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         cmn_rstn_cfg_q <= `DDR_CMN_RSTN_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_CMN_RSTN_CFG)
               cmn_rstn_cfg_q <= i_wdata;

   assign o_cmn_rstn_cfg = cmn_rstn_cfg_q & `DDR_CMN_RSTN_CFG_MSK;

   logic [31:0] cmn_rstn_sta_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         cmn_rstn_sta_q <= `DDR_CMN_RSTN_STA_POR;
      else
         cmn_rstn_sta_q <= i_cmn_rstn_sta;

   always_comb
      if (i_read)
         case (decode)
            DECODE_DDR_CMN_VREF_M0_CFG : o_rdata = o_cmn_vref_m0_cfg;
            DECODE_DDR_CMN_VREF_M1_CFG : o_rdata = o_cmn_vref_m1_cfg;
            DECODE_DDR_CMN_ZQCAL_CFG : o_rdata = o_cmn_zqcal_cfg;
            DECODE_DDR_CMN_ZQCAL_STA : o_rdata = cmn_zqcal_sta_q;
            DECODE_DDR_CMN_IBIAS_CFG : o_rdata = o_cmn_ibias_cfg;
            DECODE_DDR_CMN_TEST_CFG : o_rdata = o_cmn_test_cfg;
            DECODE_DDR_CMN_LDO_M0_CFG : o_rdata = o_cmn_ldo_m0_cfg;
            DECODE_DDR_CMN_LDO_M1_CFG : o_rdata = o_cmn_ldo_m1_cfg;
            DECODE_DDR_CMN_CLK_CTRL_CFG : o_rdata = o_cmn_clk_ctrl_cfg;
            DECODE_DDR_CMN_PMON_ANA_CFG : o_rdata = o_cmn_pmon_ana_cfg;
            DECODE_DDR_CMN_PMON_DIG_CFG : o_rdata = o_cmn_pmon_dig_cfg;
            DECODE_DDR_CMN_PMON_DIG_NAND_CFG : o_rdata = o_cmn_pmon_dig_nand_cfg;
            DECODE_DDR_CMN_PMON_DIG_NOR_CFG : o_rdata = o_cmn_pmon_dig_nor_cfg;
            DECODE_DDR_CMN_PMON_NAND_STA : o_rdata = cmn_pmon_nand_sta_q;
            DECODE_DDR_CMN_PMON_NOR_STA : o_rdata = cmn_pmon_nor_sta_q;
            DECODE_DDR_CMN_CLK_STA : o_rdata = cmn_clk_sta_q;
            DECODE_DDR_CMN_RSTN_CFG : o_rdata = o_cmn_rstn_cfg;
            DECODE_DDR_CMN_RSTN_STA : o_rdata = cmn_rstn_sta_q;
            default : o_rdata = '0;
         endcase
      else
         o_rdata = '0;

endmodule
