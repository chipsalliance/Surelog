


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

`include "wav_mcu_csr_defs.vh"



module wav_mcu_csr #(
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
   output  logic [`WAV_MCU_IRQ_FAST_CLR_CFG_RANGE] o_mcu_irq_fast_clr_cfg,
   output  logic [`WAV_MCU_IRQ_FAST_STICKY_CFG_RANGE] o_mcu_irq_fast_sticky_cfg,
   output  logic [`WAV_MCU_IRQ_FAST_MSK_CFG_RANGE] o_mcu_irq_fast_msk_cfg,
   output  logic [`WAV_MCU_IRQ_FAST_SYNC_CFG_RANGE] o_mcu_irq_fast_sync_cfg,
   output  logic [`WAV_MCU_IRQ_FAST_EDGE_CFG_RANGE] o_mcu_irq_fast_edge_cfg,
   input   logic [`WAV_MCU_IRQ_FAST_STA_RANGE] i_mcu_irq_fast_sta,
   output  logic [`WAV_MCU_MSIP_CFG_RANGE] o_mcu_msip_cfg,
   input   logic [`WAV_MCU_MTIME_LO_STA_RANGE] i_mcu_mtime_lo_sta,
   input   logic [`WAV_MCU_MTIME_HI_STA_RANGE] i_mcu_mtime_hi_sta,
   output  logic [`WAV_MCU_MTIMECMP_LO_CFG_RANGE] o_mcu_mtimecmp_lo_cfg,
   output  logic [`WAV_MCU_MTIMECMP_HI_CFG_RANGE] o_mcu_mtimecmp_hi_cfg,
   output  logic [`WAV_MCU_MTIMECMP_CFG_RANGE] o_mcu_mtimecmp_cfg,
   output  logic [`WAV_MCU_MTIME_CFG_RANGE] o_mcu_mtime_cfg,
   output  logic [`WAV_MCU_GP0_CFG_RANGE] o_mcu_gp0_cfg,
   output  logic [`WAV_MCU_GP1_CFG_RANGE] o_mcu_gp1_cfg,
   output  logic [`WAV_MCU_GP2_CFG_RANGE] o_mcu_gp2_cfg,
   output  logic [`WAV_MCU_GP3_CFG_RANGE] o_mcu_gp3_cfg,
   output  logic [`WAV_MCU_DEBUG_CFG_RANGE] o_mcu_debug_cfg,
   output  logic [`WAV_MCU_ITCM_CFG_RANGE] o_mcu_itcm_cfg,
   output  logic [`WAV_MCU_DTCM_CFG_RANGE] o_mcu_dtcm_cfg
);

   typedef enum logic [5:0] {
      DECODE_WAV_MCU_IRQ_FAST_CLR_CFG,
      DECODE_WAV_MCU_IRQ_FAST_STICKY_CFG,
      DECODE_WAV_MCU_IRQ_FAST_MSK_CFG,
      DECODE_WAV_MCU_IRQ_FAST_SYNC_CFG,
      DECODE_WAV_MCU_IRQ_FAST_EDGE_CFG,
      DECODE_WAV_MCU_IRQ_FAST_STA,
      DECODE_WAV_MCU_MSIP_CFG,
      DECODE_WAV_MCU_MTIME_LO_STA,
      DECODE_WAV_MCU_MTIME_HI_STA,
      DECODE_WAV_MCU_MTIMECMP_LO_CFG,
      DECODE_WAV_MCU_MTIMECMP_HI_CFG,
      DECODE_WAV_MCU_MTIMECMP_CFG,
      DECODE_WAV_MCU_MTIME_CFG,
      DECODE_WAV_MCU_GP0_CFG,
      DECODE_WAV_MCU_GP1_CFG,
      DECODE_WAV_MCU_GP2_CFG,
      DECODE_WAV_MCU_GP3_CFG,
      DECODE_WAV_MCU_DEBUG_CFG,
      DECODE_WAV_MCU_ITCM_CFG,
      DECODE_WAV_MCU_DTCM_CFG,
      DECODE_NOOP
   } DECODE_T;

   DECODE_T decode;

   assign o_ready = 1'b1;

   always_comb begin
      o_error = 1'b0;
      case (i_addr)
         `WAV_MCU_IRQ_FAST_CLR_CFG_ADR : decode = DECODE_WAV_MCU_IRQ_FAST_CLR_CFG;
         `WAV_MCU_IRQ_FAST_STICKY_CFG_ADR : decode = DECODE_WAV_MCU_IRQ_FAST_STICKY_CFG;
         `WAV_MCU_IRQ_FAST_MSK_CFG_ADR : decode = DECODE_WAV_MCU_IRQ_FAST_MSK_CFG;
         `WAV_MCU_IRQ_FAST_SYNC_CFG_ADR : decode = DECODE_WAV_MCU_IRQ_FAST_SYNC_CFG;
         `WAV_MCU_IRQ_FAST_EDGE_CFG_ADR : decode = DECODE_WAV_MCU_IRQ_FAST_EDGE_CFG;
         `WAV_MCU_IRQ_FAST_STA_ADR : decode = DECODE_WAV_MCU_IRQ_FAST_STA;
         `WAV_MCU_MSIP_CFG_ADR : decode = DECODE_WAV_MCU_MSIP_CFG;
         `WAV_MCU_MTIME_LO_STA_ADR : decode = DECODE_WAV_MCU_MTIME_LO_STA;
         `WAV_MCU_MTIME_HI_STA_ADR : decode = DECODE_WAV_MCU_MTIME_HI_STA;
         `WAV_MCU_MTIMECMP_LO_CFG_ADR : decode = DECODE_WAV_MCU_MTIMECMP_LO_CFG;
         `WAV_MCU_MTIMECMP_HI_CFG_ADR : decode = DECODE_WAV_MCU_MTIMECMP_HI_CFG;
         `WAV_MCU_MTIMECMP_CFG_ADR : decode = DECODE_WAV_MCU_MTIMECMP_CFG;
         `WAV_MCU_MTIME_CFG_ADR : decode = DECODE_WAV_MCU_MTIME_CFG;
         `WAV_MCU_GP0_CFG_ADR : decode = DECODE_WAV_MCU_GP0_CFG;
         `WAV_MCU_GP1_CFG_ADR : decode = DECODE_WAV_MCU_GP1_CFG;
         `WAV_MCU_GP2_CFG_ADR : decode = DECODE_WAV_MCU_GP2_CFG;
         `WAV_MCU_GP3_CFG_ADR : decode = DECODE_WAV_MCU_GP3_CFG;
         `WAV_MCU_DEBUG_CFG_ADR : decode = DECODE_WAV_MCU_DEBUG_CFG;
         `WAV_MCU_ITCM_CFG_ADR : decode = DECODE_WAV_MCU_ITCM_CFG;
         `WAV_MCU_DTCM_CFG_ADR : decode = DECODE_WAV_MCU_DTCM_CFG;
         default : begin 
            decode = DECODE_NOOP;
            o_error = 1'b1;
         end
      endcase
   end

   logic [31:0] mcu_irq_fast_clr_cfg_q;
   logic mcu_irq_fast_clr_cfg_write_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset) begin
         mcu_irq_fast_clr_cfg_q <= `WAV_MCU_IRQ_FAST_CLR_CFG_POR;
         mcu_irq_fast_clr_cfg_write_q <= 1'b0;
      end else begin
         mcu_irq_fast_clr_cfg_write_q <= i_wdata;
         if (!i_write && mcu_irq_fast_clr_cfg_write_q)
            mcu_irq_fast_clr_cfg_q <= '0;
         else if (i_write)
            if (decode == DECODE_WAV_MCU_IRQ_FAST_CLR_CFG)
               mcu_irq_fast_clr_cfg_q <= i_wdata;
         end

   assign o_mcu_irq_fast_clr_cfg = mcu_irq_fast_clr_cfg_q & `WAV_MCU_IRQ_FAST_CLR_CFG_MSK;

   logic [31:0] mcu_irq_fast_sticky_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         mcu_irq_fast_sticky_cfg_q <= `WAV_MCU_IRQ_FAST_STICKY_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_WAV_MCU_IRQ_FAST_STICKY_CFG)
               mcu_irq_fast_sticky_cfg_q <= i_wdata;

   assign o_mcu_irq_fast_sticky_cfg = mcu_irq_fast_sticky_cfg_q & `WAV_MCU_IRQ_FAST_STICKY_CFG_MSK;

   logic [31:0] mcu_irq_fast_msk_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         mcu_irq_fast_msk_cfg_q <= `WAV_MCU_IRQ_FAST_MSK_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_WAV_MCU_IRQ_FAST_MSK_CFG)
               mcu_irq_fast_msk_cfg_q <= i_wdata;

   assign o_mcu_irq_fast_msk_cfg = mcu_irq_fast_msk_cfg_q & `WAV_MCU_IRQ_FAST_MSK_CFG_MSK;

   logic [31:0] mcu_irq_fast_sync_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         mcu_irq_fast_sync_cfg_q <= `WAV_MCU_IRQ_FAST_SYNC_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_WAV_MCU_IRQ_FAST_SYNC_CFG)
               mcu_irq_fast_sync_cfg_q <= i_wdata;

   assign o_mcu_irq_fast_sync_cfg = mcu_irq_fast_sync_cfg_q & `WAV_MCU_IRQ_FAST_SYNC_CFG_MSK;

   logic [31:0] mcu_irq_fast_edge_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         mcu_irq_fast_edge_cfg_q <= `WAV_MCU_IRQ_FAST_EDGE_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_WAV_MCU_IRQ_FAST_EDGE_CFG)
               mcu_irq_fast_edge_cfg_q <= i_wdata;

   assign o_mcu_irq_fast_edge_cfg = mcu_irq_fast_edge_cfg_q & `WAV_MCU_IRQ_FAST_EDGE_CFG_MSK;

   logic [31:0] mcu_irq_fast_sta_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         mcu_irq_fast_sta_q <= `WAV_MCU_IRQ_FAST_STA_POR;
      else
         mcu_irq_fast_sta_q <= i_mcu_irq_fast_sta;

   logic [31:0] mcu_msip_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         mcu_msip_cfg_q <= `WAV_MCU_MSIP_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_WAV_MCU_MSIP_CFG)
               mcu_msip_cfg_q <= i_wdata;

   assign o_mcu_msip_cfg = mcu_msip_cfg_q & `WAV_MCU_MSIP_CFG_MSK;

   logic [31:0] mcu_mtime_lo_sta_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         mcu_mtime_lo_sta_q <= `WAV_MCU_MTIME_LO_STA_POR;
      else
         mcu_mtime_lo_sta_q <= i_mcu_mtime_lo_sta;

   logic [31:0] mcu_mtime_hi_sta_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         mcu_mtime_hi_sta_q <= `WAV_MCU_MTIME_HI_STA_POR;
      else
         mcu_mtime_hi_sta_q <= i_mcu_mtime_hi_sta;

   logic [31:0] mcu_mtimecmp_lo_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         mcu_mtimecmp_lo_cfg_q <= `WAV_MCU_MTIMECMP_LO_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_WAV_MCU_MTIMECMP_LO_CFG)
               mcu_mtimecmp_lo_cfg_q <= i_wdata;

   assign o_mcu_mtimecmp_lo_cfg = mcu_mtimecmp_lo_cfg_q & `WAV_MCU_MTIMECMP_LO_CFG_MSK;

   logic [31:0] mcu_mtimecmp_hi_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         mcu_mtimecmp_hi_cfg_q <= `WAV_MCU_MTIMECMP_HI_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_WAV_MCU_MTIMECMP_HI_CFG)
               mcu_mtimecmp_hi_cfg_q <= i_wdata;

   assign o_mcu_mtimecmp_hi_cfg = mcu_mtimecmp_hi_cfg_q & `WAV_MCU_MTIMECMP_HI_CFG_MSK;

   logic [31:0] mcu_mtimecmp_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         mcu_mtimecmp_cfg_q <= `WAV_MCU_MTIMECMP_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_WAV_MCU_MTIMECMP_CFG)
               mcu_mtimecmp_cfg_q <= mcu_mtimecmp_cfg_q ^ i_wdata;

   assign o_mcu_mtimecmp_cfg = mcu_mtimecmp_cfg_q & `WAV_MCU_MTIMECMP_CFG_MSK;

   logic [31:0] mcu_mtime_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         mcu_mtime_cfg_q <= `WAV_MCU_MTIME_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_WAV_MCU_MTIME_CFG)
               mcu_mtime_cfg_q <= i_wdata;

   assign o_mcu_mtime_cfg = mcu_mtime_cfg_q & `WAV_MCU_MTIME_CFG_MSK;

   logic [31:0] mcu_gp0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         mcu_gp0_cfg_q <= `WAV_MCU_GP0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_WAV_MCU_GP0_CFG)
               mcu_gp0_cfg_q <= i_wdata;

   assign o_mcu_gp0_cfg = mcu_gp0_cfg_q & `WAV_MCU_GP0_CFG_MSK;

   logic [31:0] mcu_gp1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         mcu_gp1_cfg_q <= `WAV_MCU_GP1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_WAV_MCU_GP1_CFG)
               mcu_gp1_cfg_q <= i_wdata;

   assign o_mcu_gp1_cfg = mcu_gp1_cfg_q & `WAV_MCU_GP1_CFG_MSK;

   logic [31:0] mcu_gp2_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         mcu_gp2_cfg_q <= `WAV_MCU_GP2_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_WAV_MCU_GP2_CFG)
               mcu_gp2_cfg_q <= i_wdata;

   assign o_mcu_gp2_cfg = mcu_gp2_cfg_q & `WAV_MCU_GP2_CFG_MSK;

   logic [31:0] mcu_gp3_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         mcu_gp3_cfg_q <= `WAV_MCU_GP3_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_WAV_MCU_GP3_CFG)
               mcu_gp3_cfg_q <= i_wdata;

   assign o_mcu_gp3_cfg = mcu_gp3_cfg_q & `WAV_MCU_GP3_CFG_MSK;

   logic [31:0] mcu_debug_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         mcu_debug_cfg_q <= `WAV_MCU_DEBUG_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_WAV_MCU_DEBUG_CFG)
               mcu_debug_cfg_q <= i_wdata;

   assign o_mcu_debug_cfg = mcu_debug_cfg_q & `WAV_MCU_DEBUG_CFG_MSK;

   logic [31:0] mcu_itcm_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         mcu_itcm_cfg_q <= `WAV_MCU_ITCM_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_WAV_MCU_ITCM_CFG)
               mcu_itcm_cfg_q <= i_wdata;

   assign o_mcu_itcm_cfg = mcu_itcm_cfg_q & `WAV_MCU_ITCM_CFG_MSK;

   logic [31:0] mcu_dtcm_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         mcu_dtcm_cfg_q <= `WAV_MCU_DTCM_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_WAV_MCU_DTCM_CFG)
               mcu_dtcm_cfg_q <= i_wdata;

   assign o_mcu_dtcm_cfg = mcu_dtcm_cfg_q & `WAV_MCU_DTCM_CFG_MSK;

   always_comb
      if (i_read)
         case (decode)
            DECODE_WAV_MCU_IRQ_FAST_CLR_CFG : o_rdata = o_mcu_irq_fast_clr_cfg;
            DECODE_WAV_MCU_IRQ_FAST_STICKY_CFG : o_rdata = o_mcu_irq_fast_sticky_cfg;
            DECODE_WAV_MCU_IRQ_FAST_MSK_CFG : o_rdata = o_mcu_irq_fast_msk_cfg;
            DECODE_WAV_MCU_IRQ_FAST_SYNC_CFG : o_rdata = o_mcu_irq_fast_sync_cfg;
            DECODE_WAV_MCU_IRQ_FAST_EDGE_CFG : o_rdata = o_mcu_irq_fast_edge_cfg;
            DECODE_WAV_MCU_IRQ_FAST_STA : o_rdata = mcu_irq_fast_sta_q;
            DECODE_WAV_MCU_MSIP_CFG : o_rdata = o_mcu_msip_cfg;
            DECODE_WAV_MCU_MTIME_LO_STA : o_rdata = mcu_mtime_lo_sta_q;
            DECODE_WAV_MCU_MTIME_HI_STA : o_rdata = mcu_mtime_hi_sta_q;
            DECODE_WAV_MCU_MTIMECMP_LO_CFG : o_rdata = o_mcu_mtimecmp_lo_cfg;
            DECODE_WAV_MCU_MTIMECMP_HI_CFG : o_rdata = o_mcu_mtimecmp_hi_cfg;
            DECODE_WAV_MCU_MTIMECMP_CFG : o_rdata = o_mcu_mtimecmp_cfg;
            DECODE_WAV_MCU_MTIME_CFG : o_rdata = o_mcu_mtime_cfg;
            DECODE_WAV_MCU_GP0_CFG : o_rdata = o_mcu_gp0_cfg;
            DECODE_WAV_MCU_GP1_CFG : o_rdata = o_mcu_gp1_cfg;
            DECODE_WAV_MCU_GP2_CFG : o_rdata = o_mcu_gp2_cfg;
            DECODE_WAV_MCU_GP3_CFG : o_rdata = o_mcu_gp3_cfg;
            DECODE_WAV_MCU_DEBUG_CFG : o_rdata = o_mcu_debug_cfg;
            DECODE_WAV_MCU_ITCM_CFG : o_rdata = o_mcu_itcm_cfg;
            DECODE_WAV_MCU_DTCM_CFG : o_rdata = o_mcu_dtcm_cfg;
            default : o_rdata = '0;
         endcase
      else
         o_rdata = '0;

endmodule
