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
`include "wav_mcuintf_csr_defs.vh"
`include "wav_mcutop_csr_defs.vh"

import wav_ahb_pkg::*;
import wav_mcu_pkg::*;

module wav_mcu_ibex #(
   parameter AWIDTH            = 32,
   parameter DWIDTH            = 32,
   parameter ITCM_SIZE         = WAV_MCU_ITCM_SIZE, // ITCM size in bytes
   parameter DTCM_SIZE         = WAV_MCU_DTCM_SIZE, // DTCM size in bytes
   parameter NUM_INT_IRQ       = WAV_NUM_IRQ
) (

   // Clock and reset
   input  logic                  i_ahb_clk,
   input  logic                  i_ahb_csr_rst,

   input  logic                  i_mcu_clk,
   input  logic                  i_mcu_rst,

   input  logic                  i_ref_clk,
   input  logic                  i_ref_rst,
   // Modes
   input  logic                  i_scan_mode,

   // HOST<->MCU Messaging
   output logic                  o_irq_host2mcu_msg_req,
   output logic                  o_irq_mcu2host_msg_ack,

   // Ibex Interrupts
   input  logic                  i_irq_external,
   input  logic                  i_irq_nm,
   input  logic [14:0]           i_irq_fast,
   input  logic [NUM_INT_IRQ-1:0]i_irq_fast_int,
   output logic [NUM_INT_IRQ-1:0]o_irq_fast_int,
   output logic [1:0]            o_irq_ext,

   output logic                  o_core_sleep,

   // AHB Slave For Memory Load - mcu clock domain
   input  logic [AWIDTH-1:0]     i_ahbs_haddr,
   input  logic                  i_ahbs_hwrite,
   input  logic                  i_ahbs_hsel,
   input  logic                  i_ahbs_hreadyin,
   input  logic [31:0]           i_ahbs_hwdata,
   input  logic [1:0]            i_ahbs_htrans,
   input  logic [2:0]            i_ahbs_hsize,
   input  logic [2:0]            i_ahbs_hburst,
   output logic                  o_ahbs_hready,
   output logic [31:0]           o_ahbs_hrdata,
   output logic [1:0]            o_ahbs_hresp,
   output logic                  o_ahbs_hgrant,

   // AHB Slave to Enable MCU - ahb clock domain - pre MCU AHBM Arbitration
   input  logic [AWIDTH-1:0]     i_mcutop_ahbs_haddr,
   input  logic                  i_mcutop_ahbs_hwrite,
   input  logic                  i_mcutop_ahbs_hsel,
   input  logic                  i_mcutop_ahbs_hreadyin,
   input  logic [31:0]           i_mcutop_ahbs_hwdata,
   input  logic [1:0]            i_mcutop_ahbs_htrans,
   input  logic [2:0]            i_mcutop_ahbs_hsize,
   input  logic [2:0]            i_mcutop_ahbs_hburst,
   output logic                  o_mcutop_ahbs_hready,
   output logic [31:0]           o_mcutop_ahbs_hrdata,
   output logic [1:0]            o_mcutop_ahbs_hresp,

   // AHB Slave to Enable MCU - ahb clock domain
   input  logic [AWIDTH-1:0]     i_mcu_cfg_ahbs_haddr,
   input  logic                  i_mcu_cfg_ahbs_hwrite,
   input  logic                  i_mcu_cfg_ahbs_hsel,
   input  logic                  i_mcu_cfg_ahbs_hreadyin,
   input  logic [31:0]           i_mcu_cfg_ahbs_hwdata,
   input  logic [1:0]            i_mcu_cfg_ahbs_htrans,
   input  logic [2:0]            i_mcu_cfg_ahbs_hsize,
   input  logic [2:0]            i_mcu_cfg_ahbs_hburst,
   output logic                  o_mcu_cfg_ahbs_hready,
   output logic [31:0]           o_mcu_cfg_ahbs_hrdata,
   output logic [1:0]            o_mcu_cfg_ahbs_hresp,

   // AHB Master Data Output - mcu clock domain
   output logic [AWIDTH-1:0]     o_ahbm_haddr,
   output logic                  o_ahbm_hreadyin,
   output logic                  o_ahbm_hbusreq,
   input  logic                  i_ahbm_hgrant,
   output logic                  o_ahbm_hwrite,
   output logic [31:0]           o_ahbm_hwdata,
   output logic [1:0]            o_ahbm_htrans,
   output logic [2:0]            o_ahbm_hsize,
   output logic [2:0]            o_ahbm_hburst,
   input  logic                  i_ahbm_hready,
   input  logic [31:0]           i_ahbm_hrdata,
   input  logic [1:0]            i_ahbm_hresp

);
   localparam HART_ID           = 0 ;
   localparam BOOT_ADDR         = WAV_MCU_ITCM_OFFSET ;             // IBEX PC boot address + 0x80
   localparam ITCM_ADDR_START   = WAV_MCU_ITCM_OFFSET ;             // ITCM start address
   localparam ITCM_ADDR_END     = ITCM_ADDR_START + ITCM_SIZE - 1 ; // ITCM end address
   localparam DTCM_ADDR_START   = WAV_MCU_DTCM_OFFSET ;             // DTCM start address
   localparam DTCM_ADDR_END     = DTCM_ADDR_START + DTCM_SIZE - 1 ; // DTCM end address
   localparam RV32M             = 1;                                // Base integer IS, 32-bit, Mult/DIV
   localparam RV32E             = 1'b0;                             // Base integer IS, 32-bit, 16 reg
   //localparam RVFI              =0;                               // Base integer IS, 32-bit, 32 reg

   // ------------------------------------------------------------------------
   // CSRs
   // ------------------------------------------------------------------------

   logic [AWIDTH-1:0]     mcu_csr_ahbs_haddr ;
   logic [AWIDTH-1:0]     mcu_csr_ahbs_haddr_local ;
   logic                  mcu_csr_ahbs_hwrite;
   logic                  mcu_csr_ahbs_hsel  ;
   logic                  mcu_csr_ahbs_hreadyin;
   logic                  mcu_csr_ahbs_hbusreq;
   logic [31:0]           mcu_csr_ahbs_hwdata;
   logic [1:0]            mcu_csr_ahbs_htrans;
   logic [2:0]            mcu_csr_ahbs_hsize ;
   logic [2:0]            mcu_csr_ahbs_hburst;
   logic                  mcu_csr_ahbs_hready;
   logic [31:0]           mcu_csr_ahbs_hrdata;
   logic [1:0]            mcu_csr_ahbs_hresp ;

   logic [`WAV_MCUTOP_CFG_RANGE] mcutop_cfg;
   logic [`WAV_MCUTOP_STA_RANGE] mcutop_sta;

   logic [`WAV_MCU_MTIME_LO_STA_RANGE]        mcu_mtime_lo_sta ;
   logic [`WAV_MCU_MTIME_HI_STA_RANGE]        mcu_mtime_hi_sta ;
   logic [`WAV_MCU_MTIMECMP_LO_CFG_RANGE]     mcu_mtimecmp_lo_cfg ;
   logic [`WAV_MCU_MTIMECMP_HI_CFG_RANGE]     mcu_mtimecmp_hi_cfg ;
   logic [`WAV_MCU_MTIMECMP_CFG_RANGE]        mcu_mtimecmp_cfg ;
   logic [`WAV_MCU_MTIME_CFG_RANGE]           mcu_mtime_cfg ;
   logic [`WAV_MCU_DEBUG_CFG_RANGE]           mcu_debug_cfg ;
   logic [`WAV_MCU_ITCM_CFG_RANGE]            mcu_itcm_cfg ;
   logic [`WAV_MCU_DTCM_CFG_RANGE]            mcu_dtcm_cfg ;
   logic [`WAV_MCU_MSIP_CFG_RANGE]            mcu_msip_cfg ;
   logic [`WAV_MCU_IRQ_FAST_SYNC_CFG_RANGE]   mcu_irq_fast_sync_cfg;
   logic [`WAV_MCU_IRQ_FAST_EDGE_CFG_RANGE]   mcu_irq_fast_edge_cfg;
   logic [`WAV_MCU_IRQ_FAST_CLR_CFG_RANGE]    mcu_irq_fast_clr_cfg;
   logic [`WAV_MCU_IRQ_FAST_STICKY_CFG_RANGE] mcu_irq_fast_sticky_cfg;
   logic [`WAV_MCU_IRQ_FAST_MSK_CFG_RANGE]    mcu_irq_fast_msk_cfg;
   logic [`WAV_MCU_IRQ_FAST_STA_RANGE]        mcu_irq_fast_sta;

   logic en_fetch;
   logic en_debug;

   assign en_fetch = mcutop_cfg[`WAV_MCUTOP_CFG_FETCH_EN_FIELD];
   assign en_debug = mcutop_cfg[`WAV_MCUTOP_CFG_DEBUG_EN_FIELD] & mcu_debug_cfg[`WAV_MCU_DEBUG_CFG_INTR_FIELD];

   wav_mcutop_ahb_csr #(
      .AWIDTH (32),
      .DWIDTH (32)
   ) u_mcutop_csr (
      .i_hclk               (i_ahb_clk            ),
      .i_hreset             (i_ahb_csr_rst        ),
      .i_haddr              (i_mcutop_ahbs_haddr  ),
      .i_hwrite             (i_mcutop_ahbs_hwrite ),
      .i_hsel               (i_mcutop_ahbs_hsel   ),
      .i_hreadyin           (i_mcutop_ahbs_hreadyin),
      .i_hwdata             (i_mcutop_ahbs_hwdata ),
      .i_htrans             (i_mcutop_ahbs_htrans ),
      .i_hsize              (i_mcutop_ahbs_hsize  ),
      .i_hburst             (i_mcutop_ahbs_hburst ),
      .o_hready             (o_mcutop_ahbs_hready ),
      .o_hrdata             (o_mcutop_ahbs_hrdata ),
      .o_hresp              (o_mcutop_ahbs_hresp  ),
      .o_mcutop_rsvd        (/*OPEN*/         ),
      .o_mcutop_cfg         (mcutop_cfg       ),
      .i_mcutop_sta         (mcutop_sta       )
   );
   assign mcutop_sta = '0 ;

   wav_mcu_ahb_csr #(
      .AWIDTH (32),
      .DWIDTH (32)
   ) u_mcu_csr (
      .i_hclk                      (i_ahb_clk         ),
      .i_hreset                    (i_ahb_csr_rst     ),
      .i_haddr                     (mcu_csr_ahbs_haddr_local),
      .i_hwrite                    (mcu_csr_ahbs_hwrite ),
      .i_hsel                      (mcu_csr_ahbs_hsel   ),
      .i_hreadyin                  (mcu_csr_ahbs_hreadyin),
      .i_hwdata                    (mcu_csr_ahbs_hwdata ),
      .i_htrans                    (mcu_csr_ahbs_htrans ),
      .i_hsize                     (mcu_csr_ahbs_hsize  ),
      .i_hburst                    (mcu_csr_ahbs_hburst ),
      .o_hready                    (mcu_csr_ahbs_hready ),
      .o_hrdata                    (mcu_csr_ahbs_hrdata ),
      .o_hresp                     (mcu_csr_ahbs_hresp  ),
      .i_mcu_mtime_lo_sta          (mcu_mtime_lo_sta),
      .i_mcu_mtime_hi_sta          (mcu_mtime_hi_sta),
      .o_mcu_mtimecmp_lo_cfg       (mcu_mtimecmp_lo_cfg),
      .o_mcu_mtimecmp_hi_cfg       (mcu_mtimecmp_hi_cfg),
      .o_mcu_mtimecmp_cfg          (mcu_mtimecmp_cfg),
      .o_mcu_mtime_cfg             (mcu_mtime_cfg),
      .o_mcu_msip_cfg              (mcu_msip_cfg),
      .o_mcu_gp0_cfg               (/*OPEN*/),
      .o_mcu_gp1_cfg               (/*OPEN*/),
      .o_mcu_gp2_cfg               (/*OPEN*/),
      .o_mcu_gp3_cfg               (/*OPEN*/),
      .o_mcu_debug_cfg             (mcu_debug_cfg),
      .o_mcu_itcm_cfg              (mcu_itcm_cfg),
      .o_mcu_dtcm_cfg              (mcu_dtcm_cfg),
      .o_mcu_irq_fast_clr_cfg      (mcu_irq_fast_clr_cfg),
      .o_mcu_irq_fast_sticky_cfg   (mcu_irq_fast_sticky_cfg),
      .o_mcu_irq_fast_msk_cfg      (mcu_irq_fast_msk_cfg),
      .o_mcu_irq_fast_sync_cfg     (mcu_irq_fast_sync_cfg),
      .o_mcu_irq_fast_edge_cfg     (mcu_irq_fast_edge_cfg),
      .i_mcu_irq_fast_sta          (mcu_irq_fast_sta)
   );

   // ------------------------------------------------------------------------
   // HOST Interface CSRs
   // ------------------------------------------------------------------------
   logic [AWIDTH-1:0]     mcuintf_ahbs_haddr ;
   logic [AWIDTH-1:0]     mcuintf_ahbs_haddr_local ;
   logic                  mcuintf_ahbs_hwrite;
   logic                  mcuintf_ahbs_hsel  ;
   logic                  mcuintf_ahbs_hreadyin;
   logic                  mcuintf_ahbs_hbusreq ;
   logic [31:0]           mcuintf_ahbs_hwdata;
   logic [1:0]            mcuintf_ahbs_htrans;
   logic [2:0]            mcuintf_ahbs_hsize ;
   logic [2:0]            mcuintf_ahbs_hburst;
   logic                  mcuintf_ahbs_hready;
   logic [31:0]           mcuintf_ahbs_hrdata;
   logic [1:0]            mcuintf_ahbs_hresp ;

   logic [`WAV_MCUINTF_HOST2MCU_MSG_REQ_RANGE] intf_host2mcu_msg_req;
   logic [`WAV_MCUINTF_HOST2MCU_MSG_ACK_RANGE] intf_host2mcu_msg_ack;
   logic [`WAV_MCUINTF_MCU2HOST_MSG_REQ_RANGE] intf_mcu2host_msg_req;
   logic [`WAV_MCUINTF_MCU2HOST_MSG_ACK_RANGE] intf_mcu2host_msg_ack;

   wav_mcuintf_ahb_csr #(
      .AWIDTH                         (AWIDTH),
      .DWIDTH                         (DWIDTH)
   ) u_mcuintf_csr (
      .i_hclk                         (i_ahb_clk),
      .i_hreset                       (i_ahb_csr_rst),
      .i_haddr                        (mcuintf_ahbs_haddr_local ),
      .i_hwrite                       (mcuintf_ahbs_hwrite),
      .i_hsel                         (mcuintf_ahbs_hsel  ),
      .i_hreadyin                     (mcuintf_ahbs_hreadyin),
      .i_hwdata                       (mcuintf_ahbs_hwdata),
      .i_htrans                       (mcuintf_ahbs_htrans),
      .i_hsize                        (mcuintf_ahbs_hsize ),
      .i_hburst                       (mcuintf_ahbs_hburst),
      .o_hready                       (mcuintf_ahbs_hready),
      .o_hrdata                       (mcuintf_ahbs_hrdata),
      .o_hresp                        (mcuintf_ahbs_hresp ),

      .o_mcuintf_host2mcu_msg_data    (/*OPEN*/),
      .o_mcuintf_host2mcu_msg_id      (/*OPEN*/),
      .o_mcuintf_host2mcu_msg_req     (intf_host2mcu_msg_req),
      .o_mcuintf_host2mcu_msg_ack     (intf_host2mcu_msg_ack),

      .o_mcuintf_mcu2host_msg_data    (/*OPEN*/),
      .o_mcuintf_mcu2host_msg_id      (/*OPEN*/),
      .o_mcuintf_mcu2host_msg_req     (intf_mcu2host_msg_req),
      .o_mcuintf_mcu2host_msg_ack     (intf_mcu2host_msg_ack)
   );

   assign o_irq_ext = { |intf_host2mcu_msg_ack ,
                        |intf_mcu2host_msg_req };

   assign o_irq_host2mcu_msg_req = |intf_host2mcu_msg_req;
   assign o_irq_mcu2host_msg_ack = |intf_mcu2host_msg_ack;

   // ------------------------------------------------------------------------
   // Timer Logic
   // ------------------------------------------------------------------------
   logic [63:0]  mtimecmp_val;
   logic [63:0]  mtimecmp_val_q;
   logic [63:0]  timer_cnt;
   logic         mtimecmp_load;
   logic         mtimecmp_load_sync;
   logic         mtimecmp_load_sync_q;
   logic         mtimecmp_valid;
   logic         mtime_irq;
   logic         mtime_en;
   logic         mtime_en_sync;

   assign mtimecmp_val        = { mcu_mtimecmp_hi_cfg[`WAV_MCU_MTIMECMP_HI_CFG_TIMECMP_HI_FIELD],mcu_mtimecmp_lo_cfg[`WAV_MCU_MTIMECMP_LO_CFG_TIMECMP_LO_FIELD]};
   assign mtimecmp_load       = mcu_mtimecmp_cfg[`WAV_MCU_MTIMECMP_CFG_LOAD_FIELD];
   assign mtime_en            = mcu_mtime_cfg[`WAV_MCU_MTIME_CFG_ENABLE_FIELD];

   //Always running timer
   //Timer interrupt asserted when timer value matches mtimecmp value. IRQ is reset when mtimecmp value is written.
   //mtimecmp_load bit toggled to indicate a new mtimecmp value is available.
   wav_demet_r  u_demet_0  (.i_rst(i_ref_rst), .i_clk(i_ref_clk), .i_d(mtimecmp_load),  .o_q(mtimecmp_load_sync));
   wav_demet_r  u_demet_1  (.i_rst(i_ref_rst), .i_clk(i_ref_clk), .i_d(mtime_en),       .o_q(mtime_en_sync));

   assign mtimecmp_valid = mtimecmp_load_sync ^ mtimecmp_load_sync_q ;

   always_ff @(posedge i_ref_clk, posedge i_ref_rst) begin
     if(i_ref_rst) begin
       timer_cnt            <= '0;
       mtimecmp_load_sync_q <= '0;
       mtimecmp_val_q       <= '0;
       mtime_irq            <= '0;
     end else begin
       timer_cnt            <= mtime_en_sync ? timer_cnt + 1'b1 : '0 ;
       mtimecmp_load_sync_q <= mtimecmp_load_sync ;
       if(mtimecmp_valid) begin
          mtimecmp_val_q    <= mtimecmp_val ;
       end
       if(mtimecmp_valid) begin
          mtime_irq         <= 1'b0;
       end else if (timer_cnt >= mtimecmp_val_q) begin
          mtime_irq         <= 1'b1;
       end
     end
   end

   wav_demet_r  u_demet_2  (.i_rst(i_mcu_rst), .i_clk(i_mcu_clk), .i_d(mtime_irq),  .o_q(ibex_irq_timer_i));

   assign mcu_mtime_lo_sta[`WAV_MCU_MTIME_LO_STA_TIME_LO_FIELD] = timer_cnt[31:0];
   assign mcu_mtime_hi_sta[`WAV_MCU_MTIME_HI_STA_TIME_HI_FIELD] = timer_cnt[63:32];

   //--------------------------------------------------------------------------
   // IRQ
   //--------------------------------------------------------------------------
   // IRQ edge detection, synchronization, hold and mask functionality
   wav_irq_intf #(
      .WIDTH                     (NUM_INT_IRQ),
      .MAX_WIDTH                 (32)
   ) u_irq_fast (
      .i_clk                     (i_mcu_clk),
      .i_rst                     (i_mcu_rst),
      .i_irq_sync_en             (mcu_irq_fast_sync_cfg[`WAV_MCU_IRQ_FAST_SYNC_CFG_EN_FIELD]),
      .i_irq_edge_en             (mcu_irq_fast_edge_cfg[`WAV_MCU_IRQ_FAST_EDGE_CFG_EN_FIELD]),
      .i_irq_clr                 (mcu_irq_fast_clr_cfg[`WAV_MCU_IRQ_FAST_CLR_CFG_CLR_FIELD]),
      .i_irq_sticky_en           (mcu_irq_fast_sticky_cfg[`WAV_MCU_IRQ_FAST_STICKY_CFG_EN_FIELD]),
      .i_irq_msk                 (mcu_irq_fast_msk_cfg[`WAV_MCU_IRQ_FAST_MSK_CFG_MSK_FIELD]),
      .i_irq                     (i_irq_fast_int),
      .o_irq                     (o_irq_fast_int)
   );

   assign mcu_irq_fast_sta      = o_irq_fast_int;

   // ------------------------------------------------------------------------
   // IBEX Core
   // ------------------------------------------------------------------------

   logic        ibex_inst_req_o;
   logic        ibex_inst_gnt_i;
   logic [31:0] ibex_inst_addr_o;
   logic [31:0] ibex_inst_rdata_i;
   logic        ibex_inst_rvalid_i;
   logic        ibex_inst_err_i;

   logic        ibex_data_req_o;
   logic        ibex_data_gnt_i;
   logic        ibex_data_we_o;
   logic [3:0]  ibex_data_be_o;
   logic [31:0] ibex_data_addr_o;
   logic [31:0] ibex_data_wdata_o;
   logic [31:0] ibex_data_rdata_i;
   logic        ibex_data_rvalid_i;
   logic        ibex_data_err_i;
   logic        ibex_debug_req_i;
   logic        ibex_fetch_enable_i;
   logic        mcu_rst_n;

   assign mcu_rst_n = ~i_mcu_rst;

   wav_demet_r u_demet [1:0] (
     .i_clk              (i_mcu_clk),
     .i_rst              (i_mcu_rst),
     .i_d                ({en_debug,en_fetch}),
     .o_q                ({ibex_debug_req_i,ibex_fetch_enable_i})
   );

   ibex_core #(
     .PMPEnable          ( 1'b0                      ),
     .DmHaltAddr         ( ITCM_ADDR_START + ITCM_SIZE - 'h100         ), //Set to end of instruction - x100
     .RV32M              ( RV32M                     ),
     .MHPMCounterWidth   ( 40                        ),
     .MHPMCounterNum     ( 2                         ),
     .DmExceptionAddr    ( ITCM_ADDR_START + ITCM_SIZE - 'h80          ), //Set to end of instruction - x80
     .RV32E              ( RV32E                     )
   ) u_ibex_core (
     .clk_i              ( i_mcu_clk                 ),
     .rst_ni             ( mcu_rst_n                 ),
     .test_en_i          ( i_scan_mode               ),
     .hart_id_i          ( HART_ID                   ),
     .boot_addr_i        ( BOOT_ADDR                 ),

     .instr_req_o        ( ibex_inst_req_o           ),
     .instr_gnt_i        ( ibex_inst_gnt_i           ),
     .instr_rvalid_i     ( ibex_inst_rvalid_i        ),
     .instr_addr_o       ( ibex_inst_addr_o          ),
     .instr_rdata_i      ( ibex_inst_rdata_i         ),
     .instr_err_i        ( ibex_inst_err_i           ),

     .data_req_o         ( ibex_data_req_o           ),
     .data_gnt_i         ( ibex_data_gnt_i           ),
     .data_rvalid_i      ( ibex_data_rvalid_i        ),
     .data_we_o          ( ibex_data_we_o            ),
     .data_be_o          ( ibex_data_be_o            ),
     .data_addr_o        ( ibex_data_addr_o          ),
     .data_wdata_o       ( ibex_data_wdata_o         ),
     .data_rdata_i       ( ibex_data_rdata_i         ),
     .data_err_i         ( ibex_data_err_i           ),

     .irq_software_i     ( mcu_msip_cfg[`WAV_MCU_MSIP_CFG_INTERRUPT_FIELD]),
     .irq_timer_i        ( ibex_irq_timer_i          ),
     .irq_external_i     ( i_irq_external            ),
     .irq_fast_i         ( i_irq_fast                ),
     .irq_nm_i           ( i_irq_nm                  ),
     .debug_req_i        ( ibex_debug_req_i          ),
     .fetch_enable_i     ( ibex_fetch_enable_i       ),
     .core_sleep_o       ( o_core_sleep              ),
     .alert_minor_o      ( /*OPEN*/                  ),
     .alert_major_o      ( /*OPEN*/                  )
   );

   // ------------------------------------------------------------------------
   // Instruction AHB Logic
   // ------------------------------------------------------------------------

   logic [AWIDTH-1:0]     ibex_inst_ahbm_haddr;
   logic                  ibex_inst_ahbm_hbusreq;
   logic                  ibex_inst_ahbm_hgrant;
   logic                  ibex_inst_ahbm_hwrite;
   logic [31:0]           ibex_inst_ahbm_hwdata;
   logic [1:0]            ibex_inst_ahbm_htrans;
   logic [2:0]            ibex_inst_ahbm_hsize;
   logic [2:0]            ibex_inst_ahbm_hburst;
   logic                  ibex_inst_ahbm_hready;
   logic [31:0]           ibex_inst_ahbm_hrdata;
   logic [1:0]            ibex_inst_ahbm_hresp;

   // IBEX master to AHB master
   wav_ahbm_ibex #(
      .AWIDTH            (AWIDTH)
   ) u_inst_ahbm (
      .i_hclk            (i_mcu_clk),
      .i_hreset          (i_mcu_rst),
      .o_haddr           (ibex_inst_ahbm_haddr),
      .o_hbusreq         (ibex_inst_ahbm_hbusreq),
      .i_hgrant          (ibex_inst_ahbm_hgrant),
      .o_hwrite          (ibex_inst_ahbm_hwrite),
      .o_hwdata          (ibex_inst_ahbm_hwdata),
      .o_htrans          (ibex_inst_ahbm_htrans),
      .o_hsize           (ibex_inst_ahbm_hsize),
      .o_hburst          (ibex_inst_ahbm_hburst),
      .i_hready          (ibex_inst_ahbm_hready),
      .i_hrdata          (ibex_inst_ahbm_hrdata),
      .i_hresp           (ibex_inst_ahbm_hresp),

      .i_req             (ibex_inst_req_o),
      .o_gnt             (ibex_inst_gnt_i),
      .i_addr            (ibex_inst_addr_o),
      .i_we              ('0),
      .i_be              ('0),
      .i_wdata           ('0),
      .o_error           (ibex_inst_err_i),
      .o_rdata           (ibex_inst_rdata_i),
      .o_rvalid          (ibex_inst_rvalid_i)
   );

`ifndef SYNTHESIS
   // AHB Monitor
   wav_ahb_monitor #(
      .DWIDTH            (32),
      .AWIDTH            (AWIDTH)
   ) ibex_inst_ahbm_monitor (
      .i_hclk            (i_mcu_clk),
      .i_hreset          (i_mcu_rst),
      .i_haddr           (ibex_inst_ahbm_haddr),
      .i_hbusreq         (ibex_inst_ahbm_hbusreq),
      .i_hwrite          (ibex_inst_ahbm_hwrite),
      .i_hwdata          (ibex_inst_ahbm_hwdata),
      .i_htrans          (ibex_inst_ahbm_htrans),
      .i_hsize           (ibex_inst_ahbm_hsize),
      .i_hburst          (ibex_inst_ahbm_hburst),
      .i_hready          (ibex_inst_ahbm_hready),
      .i_hrdata          (ibex_inst_ahbm_hrdata),
      .i_hresp           (ibex_inst_ahbm_hresp)
   );
`endif

   // ------------------------------------------------------------------------
   // Data AHB Logic
   // ------------------------------------------------------------------------

   logic [AWIDTH-1:0]     ibex_data_ahbm_haddr;
   logic                  ibex_data_ahbm_hbusreq;
   logic                  ibex_data_ahbm_hgrant;
   logic                  ibex_data_ahbm_hwrite;
   logic [31:0]           ibex_data_ahbm_hwdata;
   logic [1:0]            ibex_data_ahbm_htrans;
   logic [2:0]            ibex_data_ahbm_hsize;
   logic [2:0]            ibex_data_ahbm_hburst;
   logic                  ibex_data_ahbm_hready;
   logic [31:0]           ibex_data_ahbm_hrdata;
   logic [1:0]            ibex_data_ahbm_hresp;

   // IBEX master to AHB master
   wav_ahbm_ibex #(
      .AWIDTH            (AWIDTH)
   ) u_data_ahbm (
      .i_hclk            (i_mcu_clk),
      .i_hreset          (i_mcu_rst),
      .o_haddr           (ibex_data_ahbm_haddr),
      .o_hbusreq         (ibex_data_ahbm_hbusreq),
      .i_hgrant          (ibex_data_ahbm_hgrant),
      .o_hwrite          (ibex_data_ahbm_hwrite),
      .o_hwdata          (ibex_data_ahbm_hwdata),
      .o_htrans          (ibex_data_ahbm_htrans),
      .o_hsize           (ibex_data_ahbm_hsize),
      .o_hburst          (ibex_data_ahbm_hburst),
      .i_hready          (ibex_data_ahbm_hready),
      .i_hrdata          (ibex_data_ahbm_hrdata),
      .i_hresp           (ibex_data_ahbm_hresp),

      .i_req             (ibex_data_req_o),
      .o_gnt             (ibex_data_gnt_i),
      .i_addr            (ibex_data_addr_o),
      .i_we              (ibex_data_we_o),
      .i_be              (ibex_data_be_o),
      .i_wdata           (ibex_data_wdata_o),
      .o_rdata           (ibex_data_rdata_i),
      .o_error           (ibex_data_err_i),
      .o_rvalid          (ibex_data_rvalid_i)
   );

`ifndef SYNTHESIS
   // AHB Monitor
   wav_ahb_monitor #(
      .DWIDTH            (32),
      .AWIDTH            (AWIDTH)
   ) ibex_data_ahbm_monitor (
      .i_hclk            (i_mcu_clk),
      .i_hreset          (i_mcu_rst),
      .i_haddr           (ibex_data_ahbm_haddr),
      .i_hbusreq         (ibex_data_ahbm_hbusreq),
      .i_hwrite          (ibex_data_ahbm_hwrite),
      .i_hwdata          (ibex_data_ahbm_hwdata),
      .i_htrans          (ibex_data_ahbm_htrans),
      .i_hsize           (ibex_data_ahbm_hsize),
      .i_hburst          (ibex_data_ahbm_hburst),
      .i_hready          (ibex_data_ahbm_hready),
      .i_hrdata          (ibex_data_ahbm_hrdata),
      .i_hresp           (ibex_data_ahbm_hresp)
   );
`endif

   //----------------------------------------------------------------------
   // IBEX Data AHBM slave mux
   //----------------------------------------------------------------------
   logic [AWIDTH-1:0]     int_data_ahbm_haddr;
   logic                  int_data_ahbm_hreadyin;
   logic                  int_data_ahbm_hbusreq;
   logic                  int_data_ahbm_hgrant;
   logic                  int_data_ahbm_hwrite;
   logic [31:0]           int_data_ahbm_hwdata;
   logic [1:0]            int_data_ahbm_htrans;
   logic [2:0]            int_data_ahbm_hsize;
   logic [2:0]            int_data_ahbm_hburst;
   logic                  int_data_ahbm_hready;
   logic [31:0]           int_data_ahbm_hrdata;
   logic [1:0]            int_data_ahbm_hresp;

   localparam NUM_DM_SLVS = 2;
   localparam DM_SWIDTH   = $clog2(NUM_DM_SLVS)+'b1;

   localparam AHBM_SLV_IDX = 1 ;
   localparam INT_SLV_IDX  = 0 ;

   logic [AWIDTH*NUM_DM_SLVS-1:0]    data_slv_mux_haddr ;
   logic [NUM_DM_SLVS-1:0]           data_slv_mux_hwrite;
   logic [NUM_DM_SLVS-1:0]           data_slv_mux_hreadyin;
   logic [NUM_DM_SLVS-1:0]           data_slv_mux_hsel  ;
   logic [DWIDTH*NUM_DM_SLVS-1:0]    data_slv_mux_hwdata;
   logic [2*NUM_DM_SLVS-1:0]         data_slv_mux_htrans;
   logic [3*NUM_DM_SLVS-1:0]         data_slv_mux_hsize ;
   logic [3*NUM_DM_SLVS-1:0]         data_slv_mux_hburst;
   logic [NUM_DM_SLVS-1:0]           data_slv_mux_hready;
   logic [DWIDTH*NUM_DM_SLVS-1:0]    data_slv_mux_hrdata;
   logic [2*NUM_DM_SLVS-1:0]         data_slv_mux_hresp ;
   logic [DM_SWIDTH-1:0]             data_slv_sel ;

   // AHB Master Data Output
   assign {o_ahbm_haddr,   int_data_ahbm_haddr   }  =  data_slv_mux_haddr ;
   assign {o_ahbm_hreadyin,int_data_ahbm_hreadyin}  =  data_slv_mux_hreadyin;
   assign {o_ahbm_hwrite,  int_data_ahbm_hwrite  }  =  data_slv_mux_hwrite;
   assign {o_ahbm_hbusreq, int_data_ahbm_hbusreq }  =  data_slv_mux_hsel  ;
   assign {o_ahbm_hwdata,  int_data_ahbm_hwdata  }  =  data_slv_mux_hwdata;
   assign {o_ahbm_htrans,  int_data_ahbm_htrans  }  =  data_slv_mux_htrans;
   assign {o_ahbm_hsize,   int_data_ahbm_hsize   }  =  data_slv_mux_hsize ;
   assign {o_ahbm_hburst,  int_data_ahbm_hburst  }  =  data_slv_mux_hburst;

   assign data_slv_mux_hready = {i_ahbm_hready, int_data_ahbm_hready};
   assign data_slv_mux_hrdata = {i_ahbm_hrdata, int_data_ahbm_hrdata};
   assign data_slv_mux_hresp  = {i_ahbm_hresp,  int_data_ahbm_hresp };

   //Slave sel and slave decode
   assign data_slv_sel        = ((ibex_data_ahbm_haddr >= DTCM_ADDR_START)   & (ibex_data_ahbm_haddr <= DTCM_ADDR_END)) ? ('b1+INT_SLV_IDX) :
                                ('b1+AHBM_SLV_IDX) ;

   assign ibex_data_ahbm_hgrant = (data_slv_sel == (INT_SLV_IDX +'b1)) ? int_data_ahbm_hgrant :
                                  (data_slv_sel == (AHBM_SLV_IDX+'b1)) ? i_ahbm_hgrant : 'b1 ;

   wav_ahb_slave_mux #(
      .DWIDTH           (32),
      .AWIDTH           (32),
      .NUM_SLV          (NUM_DM_SLVS )
   ) u_data_ahbm_slv_mux (

      .i_hclk           (i_mcu_clk),
      .i_hreset         (i_mcu_rst),

      .i_slv_sel        (data_slv_sel),
      .i_hbusreq        (ibex_data_ahbm_hbusreq),
      .i_hreadyin       (1'b1),
      .i_haddr          (ibex_data_ahbm_haddr),
      .i_hwrite         (ibex_data_ahbm_hwrite),
      .i_hwdata         (ibex_data_ahbm_hwdata),
      .i_htrans         (ibex_data_ahbm_htrans),
      .i_hsize          (ibex_data_ahbm_hsize),
      .i_hburst         (ibex_data_ahbm_hburst),
      .o_hready         (ibex_data_ahbm_hready),
      .o_hrdata         (ibex_data_ahbm_hrdata),
      .o_hresp          (ibex_data_ahbm_hresp),

      .o_haddr          (data_slv_mux_haddr ),
      .o_hreadyin       (data_slv_mux_hreadyin ),
      .o_hwrite         (data_slv_mux_hwrite),
      .o_hsel           (data_slv_mux_hsel  ),
      .o_hwdata         (data_slv_mux_hwdata),
      .o_htrans         (data_slv_mux_htrans),
      .o_hsize          (data_slv_mux_hsize ),
      .o_hburst         (data_slv_mux_hburst),
      .i_hready         (data_slv_mux_hready),
      .i_hrdata         (data_slv_mux_hrdata),
      .i_hresp          (data_slv_mux_hresp )
   );

   // ------------------------------------------------------------------------
   // Instruction Memory
   // ------------------------------------------------------------------------

   logic                itcm_ahbs_req;
   logic                itcm_ahbs_we;
   logic [AWIDTH-1:0]   itcm_ahbs_addr;
   logic [31:0]         itcm_ahbs_wdata;
   logic [3:0]          itcm_ahbs_be;
   logic [31:0]         itcm_ahbs_rdata;
   logic                itcm_ahbs_rvalid;
   logic                itcm_ahbs_error;
   logic                itcm_ahbs_wait;

   wav_tcm_sp #(
      .AWIDTH            (AWIDTH),
      .DWIDTH            (32),           // SRAM Width in Bits
      .DEPTH             (2048),         // Maximum SRAM WORDS
      .SIZE              (ITCM_SIZE),    // TCM Size in KB
      .PIPELINE          ('0)
   ) u_itcm (
      .i_clk             (i_mcu_clk),
      .i_reset           (i_mcu_rst),
      .i_cs              (itcm_ahbs_req),
      .i_addr            (itcm_ahbs_addr),
      .i_wr              (itcm_ahbs_we),
      .i_byte_wr         (itcm_ahbs_be),
      .i_wdata           (itcm_ahbs_wdata),
      .i_sleep           ('0),
      .i_tcm_cfg         (mcu_itcm_cfg),
      .o_rdata           (itcm_ahbs_rdata),
      .o_wait            (itcm_ahbs_wait),
      .o_error           (itcm_ahbs_error)
   );

   assign itcm_ahbs_rvalid = ~itcm_ahbs_wait;

   // ------------------------------------------------------------------------
   // Instruction TCM AHB Logic
   // ------------------------------------------------------------------------

   logic [AWIDTH-1:0]   itcm_ahbs_haddr;
   logic [AWIDTH-1:0]   itcm_ahbs_haddr_local;
   logic                itcm_ahbs_hwrite;
   logic                itcm_ahbs_hsel;
   logic [31:0]         itcm_ahbs_hwdata;
   logic [1:0]          itcm_ahbs_htrans;
   logic [2:0]          itcm_ahbs_hsize;
   logic [2:0]          itcm_ahbs_hburst;
   logic                itcm_ahbs_hready;
   logic [31:0]         itcm_ahbs_hrdata;
   logic [1:0]          itcm_ahbs_hresp;
   logic                itcm_ahbs_hbusreq;

   wav_ahbs_ibex #(
      .AWIDTH            (AWIDTH)
   ) u_itcm_ahbs (
      .i_hclk            (i_mcu_clk),
      .i_hreset          (i_mcu_rst),
      .i_haddr           (itcm_ahbs_haddr_local),
      .i_hwrite          (itcm_ahbs_hwrite),
      .i_hsel            (itcm_ahbs_hsel),
      .i_hwdata          (itcm_ahbs_hwdata),
      .i_htrans          (itcm_ahbs_htrans),
      .i_hsize           (itcm_ahbs_hsize),
      .i_hburst          (itcm_ahbs_hburst),
      .o_hready          (itcm_ahbs_hready),
      .o_hrdata          (itcm_ahbs_hrdata),
      .o_hresp           (itcm_ahbs_hresp),

      .o_req             (itcm_ahbs_req),
      .o_we              (itcm_ahbs_we),
      .o_addr            (itcm_ahbs_addr),
      .o_wdata           (itcm_ahbs_wdata),
      .o_be              (itcm_ahbs_be),
      .i_rdata           (itcm_ahbs_rdata),
      .i_rvalid          (itcm_ahbs_rvalid),
      .i_error           (itcm_ahbs_error)
   );

`ifndef SYNTHESIS
   // AHB Monitor
   wav_ahb_monitor #(
      .DWIDTH            (32),
      .AWIDTH            (AWIDTH)
   ) itcm_ahbs_monitor (
      .i_hclk            (i_mcu_clk),
      .i_hreset          (i_mcu_rst),
      .i_haddr           (itcm_ahbs_haddr_local),
      .i_hbusreq         (itcm_ahbs_hbusreq),
      .i_hwrite          (itcm_ahbs_hwrite),
      .i_hwdata          (itcm_ahbs_hwdata),
      .i_htrans          (itcm_ahbs_htrans),
      .i_hsize           (itcm_ahbs_hsize),
      .i_hburst          (itcm_ahbs_hburst),
      .i_hready          (itcm_ahbs_hready),
      .i_hrdata          (itcm_ahbs_hrdata),
      .i_hresp           (itcm_ahbs_hresp)
   );
`endif

   // ------------------------------------------------------------------------
   // Data Memory
   // ------------------------------------------------------------------------

   logic                dtcm_ahbs_req;
   logic                dtcm_ahbs_we;
   logic [AWIDTH-1:0]   dtcm_ahbs_addr;
   logic [31:0]         dtcm_ahbs_wdata;
   logic [3:0]          dtcm_ahbs_be;
   logic [31:0]         dtcm_ahbs_rdata;
   logic                dtcm_ahbs_rvalid;
   logic                dtcm_ahbs_error;

   logic dtcm_ahbs_wait;

   wav_tcm_sp #(
      .AWIDTH            (AWIDTH),
      .DWIDTH            (32),           // SRAM Width in Bits
      .DEPTH             (2048),         // Maximum SRAM WORDS
      .SIZE              (DTCM_SIZE),    // TCM Size in KB
      .PIPELINE          ('0)
   ) u_dtcm (
      .i_clk             (i_mcu_clk),
      .i_reset           (i_mcu_rst),
      .i_cs              (dtcm_ahbs_req),
      .i_addr            (dtcm_ahbs_addr),
      .i_wr              (dtcm_ahbs_we),
      .i_byte_wr         (dtcm_ahbs_be),
      .i_wdata           (dtcm_ahbs_wdata),
      .i_sleep           ('0),
      .i_tcm_cfg         (mcu_dtcm_cfg),
      .o_rdata           (dtcm_ahbs_rdata),
      .o_wait            (dtcm_ahbs_wait),
      .o_error           (dtcm_ahbs_error)
   );

   assign dtcm_ahbs_rvalid = ~dtcm_ahbs_wait;

   // ------------------------------------------------------------------------
   // Data TCM AHB Logic
   // ------------------------------------------------------------------------

   logic [AWIDTH-1:0]   dtcm_ahbs_haddr;
   logic [AWIDTH-1:0]   dtcm_ahbs_haddr_local;
   logic                dtcm_ahbs_hwrite;
   logic                dtcm_ahbs_hsel;
   logic [31:0]         dtcm_ahbs_hwdata;
   logic [1:0]          dtcm_ahbs_htrans;
   logic [2:0]          dtcm_ahbs_hsize;
   logic [2:0]          dtcm_ahbs_hburst;
   logic                dtcm_ahbs_hready;
   logic [31:0]         dtcm_ahbs_hrdata;
   logic [1:0]          dtcm_ahbs_hresp;
   logic                dtcm_ahbs_hbusreq;

   wav_ahbs_ibex #(
      .AWIDTH            (AWIDTH)
   ) u_dtcm_ahbs (
      .i_hclk            (i_mcu_clk),
      .i_hreset          (i_mcu_rst),
      .i_haddr           (dtcm_ahbs_haddr_local),
      .i_hwrite          (dtcm_ahbs_hwrite),
      .i_hsel            (dtcm_ahbs_hsel),
      .i_hwdata          (dtcm_ahbs_hwdata),
      .i_htrans          (dtcm_ahbs_htrans),
      .i_hsize           (dtcm_ahbs_hsize),
      .i_hburst          (dtcm_ahbs_hburst),
      .o_hready          (dtcm_ahbs_hready),
      .o_hrdata          (dtcm_ahbs_hrdata),
      .o_hresp           (dtcm_ahbs_hresp),

      .o_req             (dtcm_ahbs_req),
      .o_we              (dtcm_ahbs_we),
      .o_addr            (dtcm_ahbs_addr),
      .o_wdata           (dtcm_ahbs_wdata),
      .o_be              (dtcm_ahbs_be),
      .i_rdata           (dtcm_ahbs_rdata),
      .i_rvalid          (dtcm_ahbs_rvalid),
      .i_error           (dtcm_ahbs_error)
   );

`ifndef SYNTHESIS
   // AHB Monitor
   wav_ahb_monitor #(
      .DWIDTH            (32),
      .AWIDTH            (AWIDTH)
   ) dtcm_ahbs_monitor (
      .i_hclk            (i_mcu_clk),
      .i_hreset          (i_mcu_rst),
      .i_haddr           (dtcm_ahbs_haddr_local),
      .i_hbusreq         (dtcm_ahbs_hbusreq),
      .i_hwrite          (dtcm_ahbs_hwrite),
      .i_hwdata          (dtcm_ahbs_hwdata),
      .i_htrans          (dtcm_ahbs_htrans),
      .i_hsize           (dtcm_ahbs_hsize),
      .i_hburst          (dtcm_ahbs_hburst),
      .i_hready          (dtcm_ahbs_hready),
      .i_hrdata          (dtcm_ahbs_hrdata),
      .i_hresp           (dtcm_ahbs_hresp)
   );
`endif

   // ------------------------------------------------------------------------
   // Port Interface AHB
   // ------------------------------------------------------------------------

   // APB Master Data Output
   logic [AWIDTH-1:0]     intf_ahbm_haddr;
   logic                  intf_ahbm_hbusreq;
   logic                  intf_ahbm_hgrant;
   logic                  intf_ahbm_hwrite;
   logic [31:0]           intf_ahbm_hwdata;
   logic [1:0]            intf_ahbm_htrans;
   logic [2:0]            intf_ahbm_hsize;
   logic [2:0]            intf_ahbm_hburst;
   logic                  intf_ahbm_hready;
   logic [31:0]           intf_ahbm_hrdata;
   logic [1:0]            intf_ahbm_hresp;

   logic [1:0]            inst_ahbm_hready;
   logic [2*32-1:0]       inst_ahbm_hrdata;
   logic [2*2-1:0]        inst_ahbm_hresp;

   wav_ahb_slave2master #(
      .AWIDTH            (AWIDTH)
   ) u_ahb_s2m (
      .i_hclk            (i_mcu_clk),
      .i_hreset          (i_mcu_rst),
      .i_ahbs_haddr      (i_ahbs_haddr),
      .i_ahbs_hwrite     (i_ahbs_hwrite),
      .i_ahbs_hsel       (i_ahbs_hsel),
      .i_ahbs_hreadyin   (i_ahbs_hreadyin),
      .i_ahbs_hwdata     (i_ahbs_hwdata),
      .i_ahbs_htrans     (i_ahbs_htrans),
      .i_ahbs_hsize      (i_ahbs_hsize),
      .i_ahbs_hburst     (i_ahbs_hburst),
      .o_ahbs_hready     (o_ahbs_hready),
      .o_ahbs_hrdata     (o_ahbs_hrdata),
      .o_ahbs_hresp      (o_ahbs_hresp),

      .o_ahbm_haddr      (intf_ahbm_haddr),
      .o_ahbm_hbusreq    (intf_ahbm_hbusreq),
      .i_ahbm_hgrant     (intf_ahbm_hgrant),
      .o_ahbm_hwrite     (intf_ahbm_hwrite),
      .o_ahbm_hwdata     (intf_ahbm_hwdata),
      .o_ahbm_htrans     (intf_ahbm_htrans),
      .o_ahbm_hsize      (intf_ahbm_hsize),
      .o_ahbm_hburst     (intf_ahbm_hburst),
      .i_ahbm_hready     (intf_ahbm_hready),
      .i_ahbm_hrdata     (intf_ahbm_hrdata),
      .i_ahbm_hresp      (intf_ahbm_hresp)
   );

   assign o_ahbs_hgrant    =  intf_ahbm_hgrant ;

   //----------------------------------------------------------------------
   // Intf AHBM slave mux -> split to instr and data tcms
   //----------------------------------------------------------------------
   logic [AWIDTH-1:0]     intf_data_ahbm_haddr;
   logic [AWIDTH-1:0]     intf_data_ahbm_haddr_global;
   logic                  intf_data_ahbm_hbusreq;
   logic                  intf_data_ahbm_hreadyin;
   logic                  intf_data_ahbm_hgrant;
   logic                  intf_data_ahbm_hwrite;
   logic [31:0]           intf_data_ahbm_hwdata;
   logic [1:0]            intf_data_ahbm_htrans;
   logic [2:0]            intf_data_ahbm_hsize;
   logic [2:0]            intf_data_ahbm_hburst;
   logic                  intf_data_ahbm_hready;
   logic [31:0]           intf_data_ahbm_hrdata;
   logic [1:0]            intf_data_ahbm_hresp;

   logic [AWIDTH-1:0]     intf_inst_ahbm_haddr;
   logic [AWIDTH-1:0]     intf_inst_ahbm_haddr_global;
   logic                  intf_inst_ahbm_hbusreq;
   logic                  intf_inst_ahbm_hreadyin;
   logic                  intf_inst_ahbm_hgrant;
   logic                  intf_inst_ahbm_hwrite;
   logic [31:0]           intf_inst_ahbm_hwdata;
   logic [1:0]            intf_inst_ahbm_htrans;
   logic [2:0]            intf_inst_ahbm_hsize;
   logic [2:0]            intf_inst_ahbm_hburst;
   logic                  intf_inst_ahbm_hready;
   logic [31:0]           intf_inst_ahbm_hrdata;
   logic [1:0]            intf_inst_ahbm_hresp;

   localparam NUM_SLVS = 3;
   localparam SWIDTH   = $clog2(NUM_SLVS)+'b1;

   localparam DEFAULT_SLV_IDX  = 2 ;
   localparam DATA_SLV_IDX     = 1 ;
   localparam INST_SLV_IDX     = 0 ;

   logic [AWIDTH*NUM_SLVS-1:0]    intf_slv_mux_haddr ;
   logic [NUM_SLVS-1:0]           intf_slv_mux_hwrite;
   logic [NUM_SLVS-1:0]           intf_slv_mux_hsel  ;
   logic [NUM_SLVS-1:0]           intf_slv_mux_hreadyin ;
   logic [DWIDTH*NUM_SLVS-1:0]    intf_slv_mux_hwdata;
   logic [2*NUM_SLVS-1:0]         intf_slv_mux_htrans;
   logic [3*NUM_SLVS-1:0]         intf_slv_mux_hsize ;
   logic [3*NUM_SLVS-1:0]         intf_slv_mux_hburst;
   logic [NUM_SLVS-1:0]           intf_slv_mux_hready;
   logic [DWIDTH*NUM_SLVS-1:0]    intf_slv_mux_hrdata;
   logic [2*NUM_SLVS-1:0]         intf_slv_mux_hresp ;
   logic [SWIDTH-1:0]             intf_slv_sel ;

   logic [AWIDTH-1:0]             default_ahbs_haddr;
   logic                          default_ahbs_hwrite;
   logic                          default_ahbs_hsel;
   logic                          default_ahbs_hreadyin;
   logic [31:0]                   default_ahbs_hwdata;
   logic [1:0]                    default_ahbs_htrans;
   logic [2:0]                    default_ahbs_hsize;
   logic [2:0]                    default_ahbs_hburst;
   logic                          default_ahbs_hready;
   logic [DWIDTH-1:0]             default_ahbs_hrdata;
   logic [1:0]                    default_ahbs_hresp;

   // AHB Master Data Output
   assign {default_ahbs_haddr,   intf_data_ahbm_haddr,   intf_inst_ahbm_haddr   }  =  intf_slv_mux_haddr ;
   assign {default_ahbs_hwrite,  intf_data_ahbm_hwrite,  intf_inst_ahbm_hwrite  }  =  intf_slv_mux_hwrite;
   assign {default_ahbs_hreadyin,intf_data_ahbm_hreadyin,intf_inst_ahbm_hreadyin}  =  intf_slv_mux_hreadyin;
   assign {default_ahbs_hsel,    intf_data_ahbm_hbusreq, intf_inst_ahbm_hbusreq }  =  intf_slv_mux_hsel  ;
   assign {default_ahbs_hwdata,  intf_data_ahbm_hwdata,  intf_inst_ahbm_hwdata  }  =  intf_slv_mux_hwdata;
   assign {default_ahbs_htrans,  intf_data_ahbm_htrans,  intf_inst_ahbm_htrans  }  =  intf_slv_mux_htrans;
   assign {default_ahbs_hsize,   intf_data_ahbm_hsize,   intf_inst_ahbm_hsize   }  =  intf_slv_mux_hsize ;
   assign {default_ahbs_hburst,  intf_data_ahbm_hburst,  intf_inst_ahbm_hburst  }  =  intf_slv_mux_hburst;

   assign intf_slv_mux_hready = {default_ahbs_hready, intf_data_ahbm_hready, intf_inst_ahbm_hready};
   assign intf_slv_mux_hrdata = {default_ahbs_hrdata, intf_data_ahbm_hrdata, intf_inst_ahbm_hrdata};
   assign intf_slv_mux_hresp  = {default_ahbs_hresp,  intf_data_ahbm_hresp,  intf_inst_ahbm_hresp };

   //Slave sel and slave decode
   assign intf_slv_sel       = ((intf_ahbm_haddr >= DTCM_ADDR_START - ITCM_ADDR_START) & (intf_ahbm_haddr <= DTCM_ADDR_END - ITCM_ADDR_START))   ? ('b1+DATA_SLV_IDX) :
                                (intf_ahbm_haddr <= (ITCM_ADDR_END  - ITCM_ADDR_START)) ? ('b1+INST_SLV_IDX) :
                                ('b1+DEFAULT_SLV_IDX) ;

   assign intf_data_ahbm_haddr_global = intf_data_ahbm_haddr + ITCM_ADDR_START ;
   assign intf_inst_ahbm_haddr_global = intf_inst_ahbm_haddr + ITCM_ADDR_START ;

   assign intf_ahbm_hgrant = (intf_slv_sel == (INST_SLV_IDX+'b1)) ? intf_inst_ahbm_hgrant :
                             (intf_slv_sel == (DATA_SLV_IDX+'b1)) ? intf_data_ahbm_hgrant : 'b1 ;

   wav_ahb_slave_mux #(
      .DWIDTH           (32),
      .AWIDTH           (32),
      .NUM_SLV          (NUM_SLVS )
   ) u_intf_ahbm_slv_mux (

      .i_hclk           (i_ahb_clk),
      .i_hreset         (i_ahb_csr_rst),

      .i_slv_sel        (intf_slv_sel),
      .i_hbusreq        (intf_ahbm_hbusreq),
      .i_hreadyin       (1'b1),
      .i_haddr          (intf_ahbm_haddr),
      .i_hwrite         (intf_ahbm_hwrite),
      .i_hwdata         (intf_ahbm_hwdata),
      .i_htrans         (intf_ahbm_htrans),
      .i_hsize          (intf_ahbm_hsize),
      .i_hburst         (intf_ahbm_hburst),
      .o_hready         (intf_ahbm_hready),
      .o_hrdata         (intf_ahbm_hrdata),
      .o_hresp          (intf_ahbm_hresp),

      .o_haddr          (intf_slv_mux_haddr ),
      .o_hwrite         (intf_slv_mux_hwrite),
      .o_hsel           (intf_slv_mux_hsel  ),
      .o_hreadyin       (intf_slv_mux_hreadyin),
      .o_hwdata         (intf_slv_mux_hwdata),
      .o_htrans         (intf_slv_mux_htrans),
      .o_hsize          (intf_slv_mux_hsize ),
      .o_hburst         (intf_slv_mux_hburst),
      .i_hready         (intf_slv_mux_hready),
      .i_hrdata         (intf_slv_mux_hrdata),
      .i_hresp          (intf_slv_mux_hresp )
   );

   wav_default_ahb_slave u_default_ahb_slave (
      .i_hclk           (i_ahb_clk),
      .i_hreset         (i_ahb_csr_rst),
      .i_haddr          (default_ahbs_haddr),
      .i_hwrite         (default_ahbs_hwrite),
      .i_hsel           (default_ahbs_hsel),
      .i_hreadyin       (default_ahbs_hreadyin),
      .i_hwdata         (default_ahbs_hwdata),
      .i_htrans         (default_ahbs_htrans),
      .i_hsize          (default_ahbs_hsize),
      .i_hburst         (default_ahbs_hburst),
      .o_hready         (default_ahbs_hready),
      .o_hrdata         (default_ahbs_hrdata),
      .o_hresp          (default_ahbs_hresp)
   );

   // ------------------------------------------------------------------------
   // Instruction AHB mux
   // ------------------------------------------------------------------------

   localparam NUM_MSTR   = 2;
   localparam NUM_SLAVE  = 1;

   localparam INST_AHB_INTF_MUX_IDX = 1;
   localparam INST_AHB_IBEX_MUX_IDX = 0;

   logic [32*NUM_MSTR-1:0] inst_ahbm_hwdata;
   logic [32*NUM_MSTR-1:0] inst_ahbm_haddr;
   logic [2*NUM_MSTR-1:0]  inst_ahbm_htrans;
   logic [3*NUM_MSTR-1:0]  inst_ahbm_hsize;
   logic [3*NUM_MSTR-1:0]  inst_ahbm_hburst;
   logic [NUM_MSTR-1:0]    inst_ahbm_hwrite;
   logic [NUM_MSTR-1:0]    inst_ahbm_hbusreq;
   logic [NUM_MSTR-1:0]    inst_ahbm_hgrant;

   assign inst_ahbm_haddr   = {intf_inst_ahbm_haddr_global , ibex_inst_ahbm_haddr  };
   assign inst_ahbm_hbusreq = {intf_inst_ahbm_hbusreq      , ibex_inst_ahbm_hbusreq};
   assign inst_ahbm_hwrite  = {intf_inst_ahbm_hwrite       , ibex_inst_ahbm_hwrite };
   assign inst_ahbm_hwdata  = {intf_inst_ahbm_hwdata       , ibex_inst_ahbm_hwdata };
   assign inst_ahbm_htrans  = {intf_inst_ahbm_htrans       , ibex_inst_ahbm_htrans };
   assign inst_ahbm_hsize   = {intf_inst_ahbm_hsize        , ibex_inst_ahbm_hsize  };
   assign inst_ahbm_hburst  = {intf_inst_ahbm_hburst       , ibex_inst_ahbm_hburst };

   assign {intf_inst_ahbm_hready , ibex_inst_ahbm_hready } =  inst_ahbm_hready ;
   assign {intf_inst_ahbm_hrdata , ibex_inst_ahbm_hrdata } =  inst_ahbm_hrdata ;
   assign {intf_inst_ahbm_hresp  , ibex_inst_ahbm_hresp  } =  inst_ahbm_hresp  ;
   assign {intf_inst_ahbm_hgrant , ibex_inst_ahbm_hgrant } =  inst_ahbm_hgrant ;

   wav_ahb_master_arbiter_mux #(
      .AWIDTH            (AWIDTH),
      .DWIDTH            (32),
      .NUM_MSTR          (NUM_MSTR)
   ) u_inst_ahbm_arbiter_mux (
      .i_hclk            (i_mcu_clk),
      .i_hreset          (i_mcu_rst),

      .i_ahbm_haddr      (inst_ahbm_haddr),
      .i_ahbm_hwrite     (inst_ahbm_hwrite),
      .i_ahbm_hwdata     (inst_ahbm_hwdata),
      .i_ahbm_htrans     (inst_ahbm_htrans),
      .i_ahbm_hsize      (inst_ahbm_hsize),
      .i_ahbm_hburst     (inst_ahbm_hburst),
      .i_ahbm_hbusreq    (inst_ahbm_hbusreq),
      .o_ahbm_hgrant     (inst_ahbm_hgrant),
      .o_ahbm_hrdata     (inst_ahbm_hrdata),
      .o_ahbm_hresp      (inst_ahbm_hresp ),
      .o_ahbm_hready     (inst_ahbm_hready),

      .o_ahbm_haddr      (itcm_ahbs_haddr),
      .o_ahbm_hwrite     (itcm_ahbs_hwrite),
      .o_ahbm_hwdata     (itcm_ahbs_hwdata),
      .o_ahbm_htrans     (itcm_ahbs_htrans),
      .o_ahbm_hsize      (itcm_ahbs_hsize),
      .o_ahbm_hburst     (itcm_ahbs_hburst),
      .o_ahbm_hbusreq    (itcm_ahbs_hbusreq),
      .i_ahbm_hready     (itcm_ahbs_hready),
      .i_ahbm_hrdata     (itcm_ahbs_hrdata),
      .i_ahbm_hresp      (itcm_ahbs_hresp),
      .o_ahbm_hmaster    (/*OPEN*/),
      .o_ahbm_hmastlock  (/*OPEN*/)
   );

   // AHB Slave Decoder
   assign itcm_ahbs_hsel        = itcm_ahbs_hbusreq & (itcm_ahbs_haddr >= ITCM_ADDR_START) & (itcm_ahbs_haddr <= ITCM_ADDR_END);
   assign itcm_ahbs_haddr_local = itcm_ahbs_haddr - ITCM_ADDR_START ;

   // ------------------------------------------------------------------------
   // Data AHB mux
   // ------------------------------------------------------------------------

   localparam DATA_AHB_INTF_MUX_IDX = 1;
   localparam DATA_AHB_IBEX_MUX_IDX = 0;

   logic [32*NUM_MSTR-1:0] data_ahbm_hwdata;
   logic [32*NUM_MSTR-1:0] data_ahbm_haddr;
   logic [2*NUM_MSTR-1:0]  data_ahbm_htrans;
   logic [3*NUM_MSTR-1:0]  data_ahbm_hsize;
   logic [3*NUM_MSTR-1:0]  data_ahbm_hburst;
   logic [NUM_MSTR-1:0]    data_ahbm_hwrite;
   logic [NUM_MSTR-1:0]    data_ahbm_hbusreq;
   logic [NUM_MSTR-1:0]    data_ahbm_hgrant;
   logic [NUM_MSTR-1:0]    data_ahbm_hready;
   logic [2*NUM_MSTR-1:0]  data_ahbm_hresp;
   logic [32*NUM_MSTR-1:0] data_ahbm_hrdata;

   assign data_ahbm_haddr   = {intf_data_ahbm_haddr_global , int_data_ahbm_haddr  };
   assign data_ahbm_hbusreq = {intf_data_ahbm_hbusreq      , int_data_ahbm_hbusreq};
   assign data_ahbm_hwrite  = {intf_data_ahbm_hwrite       , int_data_ahbm_hwrite };
   assign data_ahbm_hwdata  = {intf_data_ahbm_hwdata       , int_data_ahbm_hwdata };
   assign data_ahbm_htrans  = {intf_data_ahbm_htrans       , int_data_ahbm_htrans };
   assign data_ahbm_hsize   = {intf_data_ahbm_hsize        , int_data_ahbm_hsize  };
   assign data_ahbm_hburst  = {intf_data_ahbm_hburst       , int_data_ahbm_hburst };

   assign  {intf_data_ahbm_hgrant , int_data_ahbm_hgrant } = data_ahbm_hgrant ;
   assign  {intf_data_ahbm_hready , int_data_ahbm_hready } = data_ahbm_hready ;
   assign  {intf_data_ahbm_hresp  , int_data_ahbm_hresp  } = data_ahbm_hresp  ;
   assign  {intf_data_ahbm_hrdata , int_data_ahbm_hrdata } = data_ahbm_hrdata ;

   wav_ahb_master_arbiter_mux #(
      .AWIDTH            (AWIDTH),
      .DWIDTH            (32),
      .NUM_MSTR          (NUM_MSTR)
   ) u_data_ahbm_arbiter_mux (
      .i_hclk            (i_mcu_clk),
      .i_hreset          (i_mcu_rst),

      .i_ahbm_haddr      (data_ahbm_haddr),
      .i_ahbm_hwrite     (data_ahbm_hwrite),
      .i_ahbm_hwdata     (data_ahbm_hwdata),
      .i_ahbm_htrans     (data_ahbm_htrans),
      .i_ahbm_hsize      (data_ahbm_hsize),
      .i_ahbm_hburst     (data_ahbm_hburst),
      .i_ahbm_hbusreq    (data_ahbm_hbusreq),
      .o_ahbm_hgrant     (data_ahbm_hgrant),
      .o_ahbm_hrdata     (data_ahbm_hrdata),
      .o_ahbm_hresp      (data_ahbm_hresp ),
      .o_ahbm_hready     (data_ahbm_hready),

      .o_ahbm_haddr      (dtcm_ahbs_haddr),
      .o_ahbm_hwrite     (dtcm_ahbs_hwrite),
      .o_ahbm_hwdata     (dtcm_ahbs_hwdata),
      .o_ahbm_htrans     (dtcm_ahbs_htrans),
      .o_ahbm_hsize      (dtcm_ahbs_hsize),
      .o_ahbm_hburst     (dtcm_ahbs_hburst),
      .o_ahbm_hbusreq    (dtcm_ahbs_hbusreq),
      .i_ahbm_hready     (dtcm_ahbs_hready),
      .i_ahbm_hrdata     (dtcm_ahbs_hrdata),
      .i_ahbm_hresp      (dtcm_ahbs_hresp),
      .o_ahbm_hmaster    (/*OPEN*/),
      .o_ahbm_hmastlock  (/*OPEN*/)
   );

   assign dtcm_ahbs_hsel           = dtcm_ahbs_hbusreq & ((dtcm_ahbs_haddr >= DTCM_ADDR_START) & (dtcm_ahbs_haddr <= DTCM_ADDR_END)) ;
   assign dtcm_ahbs_haddr_local    = dtcm_ahbs_haddr    - DTCM_ADDR_START ;

   // ------------------------------------------------------------------------
   // MCU CSR AHB slave Mux
   // ------------------------------------------------------------------------

   localparam NUM_MCUCFG_SLVS = 3;
   localparam MCUCFG_SWIDTH   = $clog2(NUM_MCUCFG_SLVS)+'b1;

   localparam DEFAULT_CFG_SLV_IDX = 2 ;
   localparam MCUCFG_SLV_IDX      = 1 ;
   localparam MCUINTF_SLV_IDX     = 0 ;

   logic [AWIDTH*NUM_MCUCFG_SLVS-1:0]    int_mcucfg_slv_mux_haddr ;
   logic [NUM_MCUCFG_SLVS-1:0]           int_mcucfg_slv_mux_hwrite;
   logic [NUM_MCUCFG_SLVS-1:0]           int_mcucfg_slv_mux_hsel  ;
   logic [NUM_MCUCFG_SLVS-1:0]           int_mcucfg_slv_mux_hreadyin;
   logic [DWIDTH*NUM_MCUCFG_SLVS-1:0]    int_mcucfg_slv_mux_hwdata;
   logic [2*NUM_MCUCFG_SLVS-1:0]         int_mcucfg_slv_mux_htrans;
   logic [3*NUM_MCUCFG_SLVS-1:0]         int_mcucfg_slv_mux_hsize ;
   logic [3*NUM_MCUCFG_SLVS-1:0]         int_mcucfg_slv_mux_hburst;
   logic [NUM_MCUCFG_SLVS-1:0]           int_mcucfg_slv_mux_hready;
   logic [DWIDTH*NUM_MCUCFG_SLVS-1:0]    int_mcucfg_slv_mux_hrdata;
   logic [2*NUM_MCUCFG_SLVS-1:0]         int_mcucfg_slv_mux_hresp ;
   logic [MCUCFG_SWIDTH-1:0]             int_mcucfg_slv_sel ;

   logic [AWIDTH-1:0]             default_cfg_ahbs_haddr;
   logic                          default_cfg_ahbs_hwrite;
   logic                          default_cfg_ahbs_hsel;
   logic                          default_cfg_ahbs_hreadyin;
   logic [31:0]                   default_cfg_ahbs_hwdata;
   logic [1:0]                    default_cfg_ahbs_htrans;
   logic [2:0]                    default_cfg_ahbs_hsize;
   logic [2:0]                    default_cfg_ahbs_hburst;
   logic                          default_cfg_ahbs_hready;
   logic [DWIDTH-1:0]             default_cfg_ahbs_hrdata;
   logic [1:0]                    default_cfg_ahbs_hresp;

   // AHB Master Data Output
   assign { default_cfg_ahbs_haddr,   mcu_csr_ahbs_haddr,   mcuintf_ahbs_haddr   }  =  int_mcucfg_slv_mux_haddr ;
   assign { default_cfg_ahbs_hwrite,  mcu_csr_ahbs_hwrite,  mcuintf_ahbs_hwrite  }  =  int_mcucfg_slv_mux_hwrite;
   assign { default_cfg_ahbs_hbusreq, mcu_csr_ahbs_hbusreq, mcuintf_ahbs_hbusreq }  =  int_mcucfg_slv_mux_hsel  ;
   assign { default_cfg_ahbs_hreadyin,mcu_csr_ahbs_hreadyin,mcuintf_ahbs_hreadyin}  =  int_mcucfg_slv_mux_hreadyin;
   assign { default_cfg_ahbs_hwdata,  mcu_csr_ahbs_hwdata,  mcuintf_ahbs_hwdata  }  =  int_mcucfg_slv_mux_hwdata;
   assign { default_cfg_ahbs_htrans,  mcu_csr_ahbs_htrans,  mcuintf_ahbs_htrans  }  =  int_mcucfg_slv_mux_htrans;
   assign { default_cfg_ahbs_hsize,   mcu_csr_ahbs_hsize,   mcuintf_ahbs_hsize   }  =  int_mcucfg_slv_mux_hsize ;
   assign { default_cfg_ahbs_hburst,  mcu_csr_ahbs_hburst,  mcuintf_ahbs_hburst  }  =  int_mcucfg_slv_mux_hburst;

   assign int_mcucfg_slv_mux_hready = {default_cfg_ahbs_hready, mcu_csr_ahbs_hready, mcuintf_ahbs_hready};
   assign int_mcucfg_slv_mux_hrdata = {default_cfg_ahbs_hrdata, mcu_csr_ahbs_hrdata, mcuintf_ahbs_hrdata};
   assign int_mcucfg_slv_mux_hresp  = {default_cfg_ahbs_hresp , mcu_csr_ahbs_hresp , mcuintf_ahbs_hresp };

   //Slave sel and slave decode
   assign int_mcucfg_slv_sel     =  (i_mcu_cfg_ahbs_haddr < (WAV_MCUCSR_OFFSET-WAV_MCUINTF_OFFSET)) ? ('b1+MCUINTF_SLV_IDX) :
                                    (i_mcu_cfg_ahbs_haddr >= (WAV_MCUCSR_OFFSET-WAV_MCUINTF_OFFSET))  & (i_mcu_cfg_ahbs_haddr < (WAV_MCU_ITCM_OFFSET-WAV_MCUINTF_OFFSET)) ? ('b1+MCUCFG_SLV_IDX) :
                                    ('b1+DEFAULT_CFG_SLV_IDX) ;

   wav_ahb_slave_mux #(
      .DWIDTH           (32),
      .AWIDTH           (32),
      .NUM_SLV          (NUM_MCUCFG_SLVS )
   ) u_int_mcucfg_ahbs_slv_mux (

      .i_hclk           (i_ahb_clk),
      .i_hreset         (i_ahb_csr_rst),

      .i_slv_sel        (int_mcucfg_slv_sel),
      .i_hbusreq        (i_mcu_cfg_ahbs_hsel),
      .i_hreadyin       (1'b1), //i_mcu_cfg_ahbs_hreadyin),
      .i_haddr          (i_mcu_cfg_ahbs_haddr),
      .i_hwrite         (i_mcu_cfg_ahbs_hwrite),
      .i_hwdata         (i_mcu_cfg_ahbs_hwdata),
      .i_htrans         (i_mcu_cfg_ahbs_htrans),
      .i_hsize          (i_mcu_cfg_ahbs_hsize),
      .i_hburst         (i_mcu_cfg_ahbs_hburst),
      .o_hready         (o_mcu_cfg_ahbs_hready),
      .o_hrdata         (o_mcu_cfg_ahbs_hrdata),
      .o_hresp          (o_mcu_cfg_ahbs_hresp),

      .o_haddr          (int_mcucfg_slv_mux_haddr ),
      .o_hwrite         (int_mcucfg_slv_mux_hwrite),
      .o_hsel           (int_mcucfg_slv_mux_hsel  ),
      .o_hreadyin       (int_mcucfg_slv_mux_hreadyin),
      .o_hwdata         (int_mcucfg_slv_mux_hwdata),
      .o_htrans         (int_mcucfg_slv_mux_htrans),
      .o_hsize          (int_mcucfg_slv_mux_hsize ),
      .o_hburst         (int_mcucfg_slv_mux_hburst),
      .i_hready         (int_mcucfg_slv_mux_hready),
      .i_hrdata         (int_mcucfg_slv_mux_hrdata),
      .i_hresp          (int_mcucfg_slv_mux_hresp )
   );

   // AHB Slave Decoder
   assign mcuintf_ahbs_hsel        = mcuintf_ahbs_hbusreq & (mcuintf_ahbs_haddr   < (WAV_MCUCSR_OFFSET   - WAV_MCUINTF_OFFSET)) ;
   assign mcu_csr_ahbs_hsel        = mcu_csr_ahbs_hbusreq & ((mcu_csr_ahbs_haddr >= (WAV_MCUCSR_OFFSET   - WAV_MCUINTF_OFFSET)) &
                                                             (mcu_csr_ahbs_haddr  < (WAV_MCU_ITCM_OFFSET - WAV_MCUINTF_OFFSET))) ;
   assign default_cfg_ahbs_hsel    = default_cfg_ahbs_hbusreq & (default_cfg_ahbs_haddr >= WAV_MCU_ITCM_OFFSET-WAV_MCUINTF_OFFSET);

   assign mcuintf_ahbs_haddr_local = mcuintf_ahbs_haddr ;
   assign mcu_csr_ahbs_haddr_local = mcu_csr_ahbs_haddr - (WAV_MCUCSR_OFFSET - WAV_MCUINTF_OFFSET) ;

   wav_default_ahb_slave u_default_cfg_ahb_slave (
      .i_hclk           (i_ahb_clk),
      .i_hreset         (i_ahb_csr_rst),
      .i_haddr          (default_cfg_ahbs_haddr),
      .i_hwrite         (default_cfg_ahbs_hwrite),
      .i_hsel           (default_cfg_ahbs_hsel),
      .i_hreadyin       (default_cfg_ahbs_hreadyin),
      .i_hwdata         (default_cfg_ahbs_hwdata),
      .i_htrans         (default_cfg_ahbs_htrans),
      .i_hsize          (default_cfg_ahbs_hsize),
      .i_hburst         (default_cfg_ahbs_hburst),
      .o_hready         (default_cfg_ahbs_hready),
      .o_hrdata         (default_cfg_ahbs_hrdata),
      .o_hresp          (default_cfg_ahbs_hresp)
   );

endmodule

module wav_irq_intf #(
   parameter WIDTH               = 22,
   parameter MAX_WIDTH           = 32
) (
   input  logic  i_clk,
   input  logic  i_rst,
   input  logic  [MAX_WIDTH-1:0]  i_irq_clr,
   input  logic  [MAX_WIDTH-1:0]  i_irq_sticky_en,
   input  logic  [MAX_WIDTH-1:0]  i_irq_msk,
   input  logic  [MAX_WIDTH-1:0]  i_irq_edge_en,
   input  logic  [MAX_WIDTH-1:0]  i_irq_sync_en,
   input  logic  [WIDTH-1:0]  i_irq,
   output logic  [WIDTH-1:0]  o_irq
);

   logic [WIDTH-1:0] irq_edge;
   logic [WIDTH-1:0] irq_sync;
   logic [WIDTH-1:0] irq_d;
   logic [WIDTH-1:0] irq_q;
   logic [WIDTH-1:0] clr_sync;
   logic [WIDTH-1:0] msk_sync;

   wav_edge_det u_edge_det [WIDTH-1:0] (.i_clk({WIDTH{i_clk}}), .i_rst({WIDTH{i_rst}}), .i_async(i_irq), .o_sync(), .o_sync_pulse(irq_edge));
   wav_demet_r u_demet_0   [WIDTH-1:0] (.i_clk({WIDTH{i_clk}}), .i_rst({WIDTH{i_rst}}), .i_d(i_irq),                .o_q(irq_sync));
   wav_demet_r u_demet_1   [WIDTH-1:0] (.i_clk({WIDTH{i_clk}}), .i_rst({WIDTH{i_rst}}), .i_d(i_irq_clr[WIDTH-1:0]), .o_q(clr_sync));
   wav_demet_r u_demet_2   [WIDTH-1:0] (.i_clk({WIDTH{i_clk}}), .i_rst({WIDTH{i_rst}}), .i_d(i_irq_msk[WIDTH-1:0]), .o_q(msk_sync));

   genvar i;
   generate
      for (i=0; i < WIDTH; i++) begin
         assign irq_d[i] = (i_irq_edge_en[i] ? irq_edge[i]  : i_irq_sync_en[i] ? irq_sync[i] : i_irq[i] ) | (~clr_sync[i] & irq_q[i] & i_irq_sticky_en[i]);
      end
   endgenerate

   always_ff @(posedge i_clk, posedge i_rst) begin
      if (i_rst)
         irq_q <= '0;
      else
         irq_q <= irq_d;
   end

   assign o_irq = ~msk_sync & irq_q;

endmodule

module wav_ahbs_ibex #(
   parameter AWIDTH = 32,
   parameter DWIDTH = 32,
   parameter BWIDTH = DWIDTH/8
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
   output  logic                o_hready,
   output  logic [DWIDTH-1:0]   o_hrdata,
   output  logic [1:0]          o_hresp,

   output  logic                o_req,
   output  logic                o_we,
   output  logic [AWIDTH-1:0]   o_addr,
   output  logic [DWIDTH-1:0]   o_wdata,
   output  logic [BWIDTH-1:0]   o_be,
   input   logic [DWIDTH-1:0]   i_rdata,
   input   logic                i_rvalid,
   input   logic                i_error
);

   logic [AWIDTH-1:0] haddr, addr_d, addr_q;
   logic req_d, req_q ;
   logic write_d, write_q, wr_q;
   logic [DWIDTH-1:0] wdata_d, wdata_q;
   logic [1:0] bnum, bnum_q0, bnum_q1 ;

   assign req_d    =  i_hsel & ((i_htrans == AHB_TRANS_SEQ) | (i_htrans == AHB_TRANS_NONSEQ));
   assign write_d  =  i_hwrite & req_d;
   assign addr_d   =  req_d ? haddr : addr_q;
   assign bnum     =  i_haddr[1:0];

   always_comb begin
      case (i_hsize)
         AHB_SIZE_BYTE  : haddr  = {i_haddr[31:2], 2'b0};
         AHB_SIZE_HWORD : haddr  = {i_haddr[31:1], 1'b0};
         AHB_SIZE_WORD  : haddr  = i_haddr;
         default        : haddr  = i_haddr;
      endcase
   end

   logic [BWIDTH-1:0] be_d, be_q;
   always_comb begin
      case (i_hsize)
         AHB_SIZE_BYTE  : be_d = 'b1  << i_haddr[1:0];
         AHB_SIZE_HWORD : be_d = 'b11 << i_haddr[0];
         AHB_SIZE_WORD  : be_d = 'b1111;
         default        : be_d = 'b1111;
      endcase
   end

   always_ff @(posedge i_hclk, posedge i_hreset) begin
      if (i_hreset) begin
         addr_q   <= '0;
         write_q  <= '0;
         be_q     <= '0;
         req_q    <= '0;
         wr_q     <= '0;
         wdata_q  <= '0;
         bnum_q0  <= '0;
         bnum_q1  <= '0;
      end
      else begin
         // Write or Read to start the transaction, ready to keep the command
         // on the output. A slave must only sample the address and control
         // signals and hsel when HREADY is asserted.
         if (i_rvalid || req_d) begin
            addr_q   <= addr_d;
            write_q  <= write_d ;
            be_q     <= be_d;
            bnum_q0  <= bnum;
         end
            req_q    <= req_d;
            bnum_q1  <= bnum_q0;

         // Write signal delayed one cycle to align with data
         wr_q <= write_d;

         // Capture data if not ready and previous cycle was a write
         if (wr_q && !i_rvalid) begin
            wdata_q <= i_hwdata << (bnum_q0*8) ;
         end
      end
   end

   // Previous cycle was not command cycle, but slave may not be ready so
   // select the captured data
   assign wdata_d = !wr_q ? wdata_q : (i_hwdata << (bnum_q0*8));

   // Delay the write address by one cycle to align to data
   assign o_req    = req_q;
   assign o_we     = write_q;
   assign o_be     = be_q;
   assign o_addr   = addr_q;
   assign o_wdata  = wdata_d;
   assign o_hrdata = i_rdata >> (bnum_q1*8) ;
   assign o_hready = ~req_q | i_rvalid ;
   assign o_hresp  = i_error ? AHB_RESP_ERROR : AHB_RESP_OK;

endmodule

module wav_ahbm_ibex #(
   parameter AWIDTH = 32,
   parameter DWIDTH = 32,
   parameter BWIDTH = DWIDTH/8
) (
   input   logic                i_hclk,
   input   logic                i_hreset,
   output  logic [AWIDTH-1:0]   o_haddr,
   output  logic                o_hbusreq,
   input   logic                i_hgrant,
   output  logic                o_hwrite,
   output  logic [DWIDTH-1:0]   o_hwdata,
   output  logic [1:0]          o_htrans,
   output  logic [2:0]          o_hsize,
   output  logic [2:0]          o_hburst,
   input   logic                i_hready,
   input   logic [DWIDTH-1:0]   i_hrdata,
   input   logic [1:0]          i_hresp,

   input   logic                i_req,
   output  logic                o_gnt,
   input   logic [AWIDTH-1:0]   i_addr,
   input   logic                i_we,
   input   logic [BWIDTH-1:0]   i_be,
   input   logic [DWIDTH-1:0]   i_wdata,
   output  logic [DWIDTH-1:0]   o_rdata,
   output  logic                o_rvalid,
   output  logic                o_error
);

   logic [DWIDTH-1:0] hwdata_q;
   logic [2:0] rreq_q0;
   logic wreq_q0;
   logic [1:0] bnum , bnum_q0; //, bnum_q1 ;

   always_ff @(posedge i_hclk, posedge i_hreset) begin
      if (i_hreset)
         hwdata_q <= '0;
      else
         hwdata_q <= i_wdata >> (bnum*8);
   end

   //rreq_q0: count pending read requests.
   //Hold curent state if there is read data and new read req in same cycle.
   //Incr if there is new Read req.
   //Descremenrt if read data is received.
   // Hold state if no activity.

   always_ff @(posedge i_hclk, posedge i_hreset) begin
      if (i_hreset) begin
         rreq_q0       <= '0;
         wreq_q0       <= '0;
         bnum_q0       <= '0;
         //bnum_q1       <= '0;
      end else begin
         wreq_q0   <= i_req & i_we ? 1'b1 : (wreq_q0 & i_hready) ? 1'b0 : wreq_q0 ;
         // count number of pending reads.
         rreq_q0   <= (i_req & ~i_we & (rreq_q0!='0) & i_hready) ? rreq_q0 :
                      (i_req & ~i_we & i_hready)                 ?  rreq_q0 +'b1 :
                      ((rreq_q0!='0) & i_hready)                 ?  rreq_q0 -'b1 :
                      rreq_q0 ;
         bnum_q0   <= (i_req & ~i_we)          ? bnum :
                      ((rreq_q0!='0)&i_hready) ? '0 : bnum_q0 ;
         //bnum_q1   <= bnum_q0;
      end
   end

   localparam CWIDTH = $clog2(BWIDTH) + 'd1;
   logic [CWIDTH-1:0] count;
   // Count the number of ones or zeros
   integer i;
   always_comb begin
      count = '0;                              // Initialize count variable.
      for(i=0; i<BWIDTH; i++)                  // For all the bits...
         count = count + i_be[i];              // Add the bit to the count.
   end

   logic [AWIDTH-1:0]   addr;
   assign bnum = (i_be[0] == 1'b1) ? 2'd0 :
                 (i_be[1] == 1'b1) ? 2'd1 :
                 (i_be[2] == 1'b1) ? 2'd2 :
                 (i_be[3] == 1'b1) ? 2'd3 :
                 2'd0 ;

   logic [2:0] size;
   always_comb begin
      case (count)
         3'd1    : size = AHB_SIZE_BYTE;
         3'd2    : size = AHB_SIZE_HWORD;
         3'd4    : size = AHB_SIZE_WORD;
         default : size = AHB_SIZE_WORD;
      endcase
   end

   assign o_gnt     = i_hgrant & i_req & i_hready ;
   assign o_rvalid  = ((i_hready & (rreq_q0!='0)) | (i_hready & wreq_q0));
   assign o_hwdata  = hwdata_q;
   assign o_haddr   = i_addr + bnum ;
   assign o_hwrite  = i_we & i_req ;
   assign o_hbusreq = i_req;
   assign o_htrans  = i_req ? AHB_TRANS_NONSEQ : AHB_TRANS_IDLE;
   assign o_rdata   = i_hrdata << (bnum_q0*8);
   assign o_error   = (i_hresp != AHB_RESP_OK) ? 1'b1 : 1'b0 ;
   assign o_hsize   = size;
   assign o_hburst  = AHB_BURST_INCR;

endmodule
