


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



module wav_mcu_ahb_csr #(
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

   logic                slv_write;
   logic                slv_read;
   logic                slv_error;
   logic [AWIDTH-1:0]   slv_addr;
   logic [DWIDTH-1:0]   slv_wdata;
   logic [DWIDTH-1:0]   slv_rdata;
   logic                slv_ready;

   wav_ahb_slave #(
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

   wav_mcu_csr #(
      .AWIDTH(AWIDTH),
      .DWIDTH(DWIDTH)
   ) mcu_csr (
      .i_hclk   (i_hclk),
      .i_hreset (i_hreset),
      .i_write  (slv_write),
      .i_read   (slv_read),
      .i_wdata  (slv_wdata),
      .i_addr   (slv_addr),
      .o_rdata  (slv_rdata),
      .o_error  (slv_error),
      .o_ready  (slv_ready),
      .o_mcu_irq_fast_clr_cfg (o_mcu_irq_fast_clr_cfg),
      .o_mcu_irq_fast_sticky_cfg (o_mcu_irq_fast_sticky_cfg),
      .o_mcu_irq_fast_msk_cfg (o_mcu_irq_fast_msk_cfg),
      .o_mcu_irq_fast_sync_cfg (o_mcu_irq_fast_sync_cfg),
      .o_mcu_irq_fast_edge_cfg (o_mcu_irq_fast_edge_cfg),
      .i_mcu_irq_fast_sta (i_mcu_irq_fast_sta),
      .o_mcu_msip_cfg (o_mcu_msip_cfg),
      .i_mcu_mtime_lo_sta (i_mcu_mtime_lo_sta),
      .i_mcu_mtime_hi_sta (i_mcu_mtime_hi_sta),
      .o_mcu_mtimecmp_lo_cfg (o_mcu_mtimecmp_lo_cfg),
      .o_mcu_mtimecmp_hi_cfg (o_mcu_mtimecmp_hi_cfg),
      .o_mcu_mtimecmp_cfg (o_mcu_mtimecmp_cfg),
      .o_mcu_mtime_cfg (o_mcu_mtime_cfg),
      .o_mcu_gp0_cfg (o_mcu_gp0_cfg),
      .o_mcu_gp1_cfg (o_mcu_gp1_cfg),
      .o_mcu_gp2_cfg (o_mcu_gp2_cfg),
      .o_mcu_gp3_cfg (o_mcu_gp3_cfg),
      .o_mcu_debug_cfg (o_mcu_debug_cfg),
      .o_mcu_itcm_cfg (o_mcu_itcm_cfg),
      .o_mcu_dtcm_cfg (o_mcu_dtcm_cfg)
   );

endmodule
