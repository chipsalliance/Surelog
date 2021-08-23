
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

module ddr_ctrl_plane #(
   parameter AWIDTH          = 32,
   parameter DWIDTH          = 32,
   parameter NUM_IRQ         = 32
) (

   // Scan
   input  logic                   i_scan_mode,
   input  logic                   i_scan_en,
   input  logic                   i_scan_clk,
   input  logic                   i_scan_cgc_ctrl,
   input  logic                   i_scan_rst_ctrl,
   input  logic [7:0]             i_scan_freq_en,

   // JTAG Interface
   input  logic                   i_jtag_tck,
   input  logic                   i_jtag_trst_n,
   input  logic                   i_jtag_tms,
   input  logic                   i_jtag_tdi,
   output logic                   o_jtag_tdo,

   input  logic                   i_jtag_dsr_tdo,
   output logic                   o_jtag_dsr_tdo,
   output logic                   o_jtag_dsr_shift,
   output logic                   o_jtag_dsr_capture,
   output logic                   o_jtag_dsr_capture_ck,
   output logic                   o_jtag_dsr_update,
   output logic                   o_jtag_dsr_update_ck,
   output logic                   o_jtag_dsr_mode,

   input  logic                   i_jtag_bsr_tdo,
   output logic                   o_jtag_bsr_tdo,
   output logic                   o_jtag_bsr_shift,
   output logic                   o_jtag_bsr_capture,
   output logic                   o_jtag_bsr_update,
   output logic                   o_jtag_bsr_mode,

   input  logic                   i_freeze_n,
   input  logic                   i_hiz_n,
   input  logic                   i_iddq_mode,

   output logic                   o_freeze_n,
   output logic                   o_hiz_n,
   output logic                   o_iddq_mode,

    // Clock and reset
   input  logic                   i_refclk,
   input  logic                   i_refclk_alt,
   input  logic                   i_pll_clk,
   input  logic                   i_ahb_extclk,

   input  logic                   i_phy_rst,
   input  logic                   i_ahb_extrst,
   input  logic                   i_ahb_csr_extrst,

   output logic                   o_phy_rst,
   output logic                   o_ref_rst,
   output logic                   o_mcu_rst,
   output logic                   o_ahb_rst,
   output logic                   o_ahb_csr_rst,

   output logic                   o_ref_clk,
   output logic                   o_mcu_clk,
   output logic                   o_ahb_clk,
   output logic                   o_ahb_extclk,

   output logic                   o_ahb_clk_on,
   output logic                   o_ref_clk_on,
   input  logic                   i_dfi_clk_on,

   input  logic [31:0]            i_debug_0,
   input  logic [31:0]            i_debug_1,
   output logic [31:0]            o_debug,

   // Ibex Interrupts
   output logic                   o_irq_external,
   input  logic [NUM_IRQ-1:0]     i_irq_fast_int,
   output logic [NUM_IRQ-1:0]     o_irq_fast_int,
   output logic [14:0]            o_irq_fast,
   output logic                   o_irq_nm,
   input  logic                   i_irq_pll,
   input  logic                   i_irq_ch0_ibuf_empty,
   input  logic                   i_irq_ch0_ibuf_full,
   input  logic                   i_irq_ch0_ibuf_overflow,
   input  logic                   i_irq_ch0_ebuf_empty,
   input  logic                   i_irq_ch0_ebuf_full,
   input  logic                   i_irq_ch0_ebuf_overflow,
   input  logic                   i_irq_ch1_ibuf_empty,
   input  logic                   i_irq_ch1_ibuf_full,
   input  logic                   i_irq_ch1_ibuf_overflow,
   input  logic                   i_irq_ch1_ebuf_empty,
   input  logic                   i_irq_ch1_ebuf_full,
   input  logic                   i_irq_ch1_ebuf_overflow,
   input  logic                   i_irq_init_start,
   input  logic                   i_irq_init_complete,
   input  logic                   i_irq_ctrlupd_req,
   input  logic                   i_irq_phyupd_ack,
   input  logic                   i_irq_phymstr_ack,
   input  logic                   i_irq_lp_ctrl_req,
   input  logic                   i_irq_lp_data_req,
   input  logic                   i_irq_host2mcu_msg_req,
   input  logic                   i_irq_mcu2host_msg_ack,

   input  logic [3:0]             i_irq_ext,

   // Intf AHB Slave Port
   input  logic [AWIDTH-1:0]      i_intf_ahb_haddr,
   input  logic                   i_intf_ahb_hwrite,
   input  logic                   i_intf_ahb_hsel,
   input  logic                   i_intf_ahb_hreadyin,

   // AHB Slave For top CTRL CSRs
   input  logic  [AWIDTH-1:0]     i_ctrl_ahb_haddr,
   input  logic                   i_ctrl_ahb_hwrite,
   input  logic                   i_ctrl_ahb_hsel,
   input  logic                   i_ctrl_ahb_hreadyin,
   input  logic  [DWIDTH-1:0]     i_ctrl_ahb_hwdata,
   input  logic  [1:0]            i_ctrl_ahb_htrans,
   input  logic  [2:0]            i_ctrl_ahb_hsize,
   input  logic  [2:0]            i_ctrl_ahb_hburst,
   output logic                   o_ctrl_ahb_hready,
   output logic  [DWIDTH-1:0]     o_ctrl_ahb_hrdata,
   output logic  [1:0]            o_ctrl_ahb_hresp

);

   // ------------------------------------------------------------------------
   // Control Plane CSRs
   // ------------------------------------------------------------------------

   logic [`DDR_CTRL_CLK_CFG_RANGE] ctrl_clk_cfg;
   logic [`DDR_CTRL_CLK_STA_RANGE] ctrl_clk_sta;
   logic [`DDR_CTRL_AHB_SNOOP_CFG_RANGE] ctrl_ahb_snoop_cfg;
   logic [`DDR_CTRL_AHB_SNOOP_STA_RANGE] ctrl_ahb_snoop_sta;
   logic [`DDR_CTRL_AHB_SNOOP_DATA_STA_RANGE] ctrl_ahb_snoop_data_sta;
   logic [`DDR_CTRL_AHB_SNOOP_PATTERN_CFG_RANGE] ctrl_ahb_snoop_pattern_cfg;
   logic [`DDR_CTRL_AHB_SNOOP_PATTERN_0_CFG_RANGE] ctrl_ahb_snoop_pattern_0_cfg;
   logic [`DDR_CTRL_AHB_SNOOP_PATTERN_1_CFG_RANGE] ctrl_ahb_snoop_pattern_1_cfg;
   logic [`DDR_CTRL_AHB_SNOOP_PATTERN_STA_RANGE] ctrl_ahb_snoop_pattern_sta;
   logic [`DDR_CTRL_DEBUG_CFG_RANGE]  ctrl_debug_cfg;
   logic [`DDR_CTRL_DEBUG1_CFG_RANGE] ctrl_debug1_cfg;

   ddr_ctrl_ahb_csr #(
      .AWIDTH                           (AWIDTH),
      .DWIDTH                           (DWIDTH)
   ) u_ctrl_plane_csr (
      .i_hclk                           (o_ahb_clk),
      .i_hreset                         (o_ahb_csr_rst),
      .i_haddr                          (i_ctrl_ahb_haddr),
      .i_hwrite                         (i_ctrl_ahb_hwrite),
      .i_hsel                           (i_ctrl_ahb_hsel),
      .i_hwdata                         (i_ctrl_ahb_hwdata),
      .i_htrans                         (i_ctrl_ahb_htrans),
      .i_hsize                          (i_ctrl_ahb_hsize),
      .i_hburst                         (i_ctrl_ahb_hburst),
      .i_hreadyin                       (i_ctrl_ahb_hreadyin),
      .o_hready                         (o_ctrl_ahb_hready),
      .o_hrdata                         (o_ctrl_ahb_hrdata),
      .o_hresp                          (o_ctrl_ahb_hresp),

      .o_ctrl_clk_cfg                   (ctrl_clk_cfg),
      .i_ctrl_clk_sta                   (ctrl_clk_sta),
      .o_ctrl_ahb_snoop_cfg             (ctrl_ahb_snoop_cfg),
      .i_ctrl_ahb_snoop_sta             (ctrl_ahb_snoop_sta),
      .i_ctrl_ahb_snoop_data_sta        (ctrl_ahb_snoop_data_sta),
      .o_ctrl_ahb_snoop_pattern_cfg     (ctrl_ahb_snoop_pattern_cfg),
      .o_ctrl_ahb_snoop_pattern_0_cfg   (ctrl_ahb_snoop_pattern_0_cfg),
      .o_ctrl_ahb_snoop_pattern_1_cfg   (ctrl_ahb_snoop_pattern_1_cfg),
      .i_ctrl_ahb_snoop_pattern_sta     (ctrl_ahb_snoop_pattern_sta),
      .o_ctrl_debug1_cfg                (ctrl_debug1_cfg),
      .o_ctrl_debug_cfg                 (ctrl_debug_cfg)

   );

   // ------------------------------------------------------------------------
   // JTAG Interface
   // ------------------------------------------------------------------------

   wav_jtag_top #(
     .IDCODE_RESET                    (32'h7270_6897)
   ) u_jtag_top (
     .i_tck                           (i_jtag_tck),
     .i_trst_n                        (i_jtag_trst_n),
     .i_tms                           (i_jtag_tms),
     .i_tdi                           (i_jtag_tdi),
     .o_tdo                           (o_jtag_tdo),

     .o_dsr_tdo                       (o_jtag_dsr_tdo),
     .i_dsr_tdo                       (i_jtag_dsr_tdo),
     .o_dsr_shift                     (o_jtag_dsr_shift),
     .o_dsr_capture                   (o_jtag_dsr_capture),
     .o_dsr_update                    (o_jtag_dsr_update),
     .o_dsr_mode                      (o_jtag_dsr_mode),

     .o_bsr_tdo                       (o_jtag_bsr_tdo),
     .i_bsr_tdo                       (i_jtag_bsr_tdo),
     .o_bsr_shift                     (o_jtag_bsr_shift),
     .o_bsr_capture                   (o_jtag_bsr_capture),
     .o_bsr_update                    (o_jtag_bsr_update),
     .o_bsr_mode                      (o_jtag_bsr_mode),

     .o_stap_enable                   (/*OPEN*/),
     .o_stap_sel                      (/*OPEN*/),
     .o_stap_rti_or_tlr               (/*OPEN*/),
     .o_stap_tdi_sk                   (/*OPEN*/),
     .i_stap_tdo_s1                   ('0),

     .i_freeze_n                      ('0),
     .i_highz_n                       ('0),
     .i_iddq_mode                     ('0),

     .o_freeze_n                      (/*OPEN*/),
     .o_highz_n                       (/*OPEN*/),
     .o_iddq_mode                     (/*OPEN*/),

     .o_scan_freq_en                  (/*OPEN*/),
     .o_scan_cgc_ctrl                 (/*OPEN*/),
     .o_scan_rst_ctrl                 (/*OPEN*/),
     .o_scan_set_ctrl                 (/*OPEN*/),

     .i_apb_clk                       ('0),
     .i_apb_reset                     ('0),
     .o_apb_psel                      (/*OPEN*/),
     .o_apb_penable                   (/*OPEN*/),
     .o_apb_pwrite                    (/*OPEN*/),
     .o_apb_pwdata                    (/*OPEN*/),
     .o_apb_paddr                     (/*OPEN*/),
     .i_apb_pslverr                   ('0),
     .i_apb_pready                    ('0),
     .i_apb_prdata                    ('0)

   );

   ddr_cgc_rl u_cgc_dsr_capture (.i_clk(i_jtag_tck), .i_clk_en(o_jtag_dsr_capture), .i_cgc_en(1'b0), .o_clk(o_jtag_dsr_capture_ck));
   ddr_cgc_rl u_cgc_dsr_update  (.i_clk(i_jtag_tck), .i_clk_en(o_jtag_dsr_update ), .i_cgc_en(1'b0), .o_clk(o_jtag_dsr_update_ck ));

   assign o_freeze_n  = i_freeze_n;
   assign o_hiz_n     = i_hiz_n;
   assign o_iddq_mode = i_iddq_mode;

   // ------------------------------------------------------------------------
   // Debug
   // ------------------------------------------------------------------------
   logic [31:0] debug ;
   assign debug = ctrl_debug1_cfg[`DDR_CTRL_DEBUG1_CFG_OVR_SEL_FIELD] ? ctrl_debug_cfg[`DDR_CTRL_DEBUG_CFG_VAL_FIELD]  :  (i_debug_0 | i_debug_1) ;

   always_ff @ (posedge o_ahb_clk, posedge o_ahb_csr_rst) begin
     if ( o_ahb_csr_rst )
        o_debug  <= 31'b0;
     else
        o_debug  <= debug;
   end

   // ------------------------------------------------------------------------
   // AHB Address Snooper
   // ------------------------------------------------------------------------

   logic [AWIDTH-1:0] snoop_ahb_haddr;
   logic ahb_pat_0_detect, ahb_pat_1_detect;

   // Filter snoop address based on slave select and write
   assign snoop_ahb_haddr = i_intf_ahb_hwrite & i_intf_ahb_hsel & i_intf_ahb_hreadyin ? i_intf_ahb_haddr : '0;

   ddr_snoop #(
      .PWIDTH                    (AWIDTH),
      .AHB_DWIDTH                (DWIDTH),
      .EG_DEPTH                  (16),
      .TSWIDTH                   (16)
   ) u_ahb_snoop (
      .i_clk                     (o_ahb_clk),
      .i_rst                     (o_ahb_rst),
      .i_scan_mode               (i_scan_mode),
      .i_scan_rst_ctrl           (i_scan_rst_ctrl),
      .i_scan_cgc_ctrl           (i_scan_cgc_ctrl),
      .i_snoop_mode              (ctrl_ahb_snoop_cfg[`DDR_CTRL_AHB_SNOOP_CFG_SNOOP_MODE_FIELD]),
      .i_ts_enable               (ctrl_ahb_snoop_cfg[`DDR_CTRL_AHB_SNOOP_CFG_TS_ENABLE_FIELD]),
      .i_ts_reset                (ctrl_ahb_snoop_cfg[`DDR_CTRL_AHB_SNOOP_CFG_TS_RESET_FIELD]),
      .i_data                    (snoop_ahb_haddr),
      .i_pattern_0_en            (ctrl_ahb_snoop_pattern_cfg[`DDR_CTRL_AHB_SNOOP_PATTERN_CFG_PAT_0_EN_FIELD]),
      .i_pattern_0_polarity      (ctrl_ahb_snoop_pattern_cfg[`DDR_CTRL_AHB_SNOOP_PATTERN_CFG_PAT_0_POLARITY_FIELD]),
      .i_pattern_0_mode          (ctrl_ahb_snoop_pattern_cfg[`DDR_CTRL_AHB_SNOOP_PATTERN_CFG_PAT_0_MODE_FIELD]),
      .i_pattern_0_val           (ctrl_ahb_snoop_pattern_0_cfg[`DDR_CTRL_AHB_SNOOP_PATTERN_0_CFG_PAT_VAL_FIELD]),
      .o_pattern_0_detect        (ahb_pat_0_detect),
      .i_pattern_1_en            (ctrl_ahb_snoop_pattern_cfg[`DDR_CTRL_AHB_SNOOP_PATTERN_CFG_PAT_1_EN_FIELD]),
      .i_pattern_1_polarity      (ctrl_ahb_snoop_pattern_cfg[`DDR_CTRL_AHB_SNOOP_PATTERN_CFG_PAT_1_POLARITY_FIELD]),
      .i_pattern_1_mode          (ctrl_ahb_snoop_pattern_cfg[`DDR_CTRL_AHB_SNOOP_PATTERN_CFG_PAT_1_MODE_FIELD]),
      .i_pattern_1_val           (ctrl_ahb_snoop_pattern_1_cfg[`DDR_CTRL_AHB_SNOOP_PATTERN_1_CFG_PAT_VAL_FIELD]),
      .o_pattern_1_detect        (ahb_pat_1_detect),
      .i_eg_rdata_clr            (ctrl_ahb_snoop_cfg[`DDR_CTRL_AHB_SNOOP_CFG_RDATA_CLR_FIELD]),
      .i_eg_rdata_upd            (ctrl_ahb_snoop_cfg[`DDR_CTRL_AHB_SNOOP_CFG_RDATA_UPDATE_FIELD]),
      .o_eg_rdata                (ctrl_ahb_snoop_data_sta[`DDR_CTRL_AHB_SNOOP_DATA_STA_RDATA_FIELD]),
      .o_eg_empty                (ctrl_ahb_snoop_sta[`DDR_CTRL_AHB_SNOOP_STA_EMPTY_FIELD]),
      .o_eg_full                 (ctrl_ahb_snoop_sta[`DDR_CTRL_AHB_SNOOP_STA_FULL_FIELD])
   );

   always_comb begin
      ctrl_ahb_snoop_pattern_sta = '0;
      // Pattern detection is a W1C register. It is assumed that the Snoop clock and CSR clock are balanced
      // so no synchronization is required. If these clocks are not balanced, then a demet is required.
      ctrl_ahb_snoop_pattern_sta[`DDR_CTRL_AHB_SNOOP_PATTERN_STA_PAT_0_DETECT_FIELD] = ahb_pat_0_detect;
      ctrl_ahb_snoop_pattern_sta[`DDR_CTRL_AHB_SNOOP_PATTERN_STA_PAT_1_DETECT_FIELD] = ahb_pat_1_detect;
   end

   // ------------------------------------------------------------------------
   // Digital Clock Control
   // ------------------------------------------------------------------------

   ddr_clk_ctrl u_clk_ctrl (

      .i_scan_mode               (i_scan_mode),
      .i_scan_clk                (i_scan_clk),
      .i_scan_en                 (i_scan_en),
      .i_scan_cgc_ctrl           (i_scan_cgc_ctrl),
      .i_scan_rst_ctrl           (i_scan_rst_ctrl),
      .i_scan_freq_en            (i_scan_freq_en),

      .i_refclk                  (i_refclk),
      .i_refclk_alt              (i_refclk_alt),
      .i_pll_clk                 (i_pll_clk),
      .i_ahb_extclk              (i_ahb_extclk),

      .i_phy_rst                 (i_phy_rst),
      .i_ahb_extrst              (i_ahb_extrst),
      .i_ahb_csr_extrst          (i_ahb_csr_extrst),

      .i_mcu_clk_cgc_en          (ctrl_clk_cfg[`DDR_CTRL_CLK_CFG_MCU_CLK_CGC_EN_FIELD]),
      .i_ref_clk_cgc_en          (ctrl_clk_cfg[`DDR_CTRL_CLK_CFG_REF_CLK_CGC_EN_FIELD]),
      .i_pll_clk_en              (ctrl_clk_cfg[`DDR_CTRL_CLK_CFG_PLL_CLK_EN_FIELD]),
      .i_ref_clk_sel             (ctrl_clk_cfg[`DDR_CTRL_CLK_CFG_REF_CLK_SEL_FIELD]),
      .i_mcu_gfm_sel             (ctrl_clk_cfg[`DDR_CTRL_CLK_CFG_MCU_GFM_SEL_FIELD]),
      .i_ahb_clk_div_en          (ctrl_clk_cfg[`DDR_CTRL_CLK_CFG_AHBCLK_DIV2_EN_FIELD]),
      .o_mcuclk_gfm_sel0         (ctrl_clk_sta[`DDR_CTRL_CLK_STA_MCU_GFM_SEL0_FIELD]),
      .o_mcuclk_gfm_sel1         (ctrl_clk_sta[`DDR_CTRL_CLK_STA_MCU_GFM_SEL1_FIELD]),

      .o_phy_rst                 (o_phy_rst),
      .o_ref_rst                 (o_ref_rst),
      .o_mcu_rst                 (o_mcu_rst),
      .o_ahb_rst                 (o_ahb_rst),
      .o_ahb_csr_rst             (o_ahb_csr_rst),

      .o_ref_clk                 (o_ref_clk),
      .o_mcu_clk                 (o_mcu_clk),
      .o_ahb_clk                 (o_ahb_clk),
      .o_ahb_extclk              (o_ahb_extclk)

   );

   // ------------------------------------------------------------------------
   // Clock On
   // ------------------------------------------------------------------------

   assign o_ahb_clk_on = ctrl_clk_cfg[`DDR_CTRL_CLK_CFG_AHB_CLK_ON_FIELD];
   assign o_ref_clk_on = ctrl_clk_cfg[`DDR_CTRL_CLK_CFG_REF_CLK_ON_FIELD];

   assign ctrl_clk_sta[`DDR_CTRL_CLK_STA_DFI_CLK_ON_FIELD] = i_dfi_clk_on;

   // ------------------------------------------------------------------------
   // IRQ
   // ------------------------------------------------------------------------

   /* IRQ MAP
   ----------------------------------------------------------------------
   BIT 31    (1)  irq_nm_i       : Non-maskable interrupt (NMI)
   BIT 30:16 (15) irq_fast_i     : Fast, local interrupts
   BIT 11    (1)  irq_external_i : Connected to platform-level interrupt
                                   controller
   BIT 7     (1)  irq_timer_i    : Connected to timer module
   BIT 3     (1)  irq_software_i : Connected to memory-mapped (inter-
                                   processor) interrupt register
   */
   assign o_irq_external = '0 ;
   assign o_irq_nm       = '0 ;

   // IRQ - FAST
   logic irq_ibuf;
   logic irq_ebuf;
   logic irq_ahb_det;
   logic irq_lp_req;
   logic irq_ch1;
   logic irq_ctrlupd_req;

   always_comb begin
      o_irq_fast_int = '0;
      o_irq_fast_int[`DDR_INT_IRQ_HOST2MCU_MSG_REQ_IDX]  =  i_irq_host2mcu_msg_req; // host2mcu MSG Request
      o_irq_fast_int[`DDR_INT_IRQ_MCU2HOST_MSG_ACK_IDX]  =  i_irq_mcu2host_msg_ack; // mcu2host MSG Acknowledge
      o_irq_fast_int[`DDR_INT_IRQ_CH0_IBUF_EMPTY_IDX   ] =  i_irq_ch0_ibuf_empty;     // CH0 WRITE BUFFER
      o_irq_fast_int[`DDR_INT_IRQ_CH0_IBUF_FULL_IDX    ] =  i_irq_ch0_ibuf_full;      // CH0 WRITE BUFFER
      o_irq_fast_int[`DDR_INT_IRQ_CH0_IBUF_OVERFLOW_IDX] =  i_irq_ch0_ibuf_overflow;  // CH0 WRITE BUFFER
      o_irq_fast_int[`DDR_INT_IRQ_CH0_EBUF_EMPTY_N_IDX ] = ~i_irq_ch0_ebuf_empty;     // CH0 READ BUFFER
      o_irq_fast_int[`DDR_INT_IRQ_CH0_EBUF_FULL_IDX    ] =  i_irq_ch0_ebuf_full;      // CH0 READ BUFFER
      o_irq_fast_int[`DDR_INT_IRQ_CH0_EBUF_OVERFLOW_IDX] =  i_irq_ch0_ebuf_overflow;  // CH0 READ BUFFER
      o_irq_fast_int[`DDR_INT_IRQ_CH1_IBUF_EMPTY_IDX   ] =  i_irq_ch1_ibuf_empty;     // CH1 WRITE BUFFER
      o_irq_fast_int[`DDR_INT_IRQ_CH1_IBUF_FULL_IDX    ] =  i_irq_ch1_ibuf_full;      // CH1 WRITE BUFFER
      o_irq_fast_int[`DDR_INT_IRQ_CH1_IBUF_OVERFLOW_IDX] =  i_irq_ch1_ibuf_overflow;  // CH1 WRITE BUFFER
      o_irq_fast_int[`DDR_INT_IRQ_CH1_EBUF_EMPTY_N_IDX ] = ~i_irq_ch1_ebuf_empty;     // CH1 READ BUFFER
      o_irq_fast_int[`DDR_INT_IRQ_CH1_EBUF_FULL_IDX    ] =  i_irq_ch1_ebuf_full;      // CH1 READ BUFFER
      o_irq_fast_int[`DDR_INT_IRQ_CH1_EBUF_OVERFLOW_IDX] =  i_irq_ch1_ebuf_overflow;  // CH1 READ BUFFER
      o_irq_fast_int[`DDR_INT_IRQ_INIT_START_IDX      ]  =  i_irq_init_start;       // Status interface
      o_irq_fast_int[`DDR_INT_IRQ_INIT_COMPLETE_IDX   ]  =  i_irq_init_complete;    // Status interface
      o_irq_fast_int[`DDR_INT_IRQ_LP_DATA_REQ         ]  =  i_irq_lp_data_req;      // LP Data Req interface
      o_irq_fast_int[`DDR_INT_IRQ_LP_CTRL_REQ         ]  =  i_irq_lp_ctrl_req;      // LP Ctrl Req interface
      o_irq_fast_int[`DDR_INT_IRQ_PLL_IDX             ]  =  i_irq_pll;              // PLL
      o_irq_fast_int[`DDR_INT_IRQ_EXT_0_IDX           ]  =  i_irq_ext[0];           // External IRQ
      o_irq_fast_int[`DDR_INT_IRQ_EXT_1_IDX           ]  =  i_irq_ext[1];           // External IRQ
      o_irq_fast_int[`DDR_INT_IRQ_CTRLUPD_REQ_IDX     ]  =  i_irq_ctrlupd_req;      // Update interface
      o_irq_fast_int[`DDR_INT_IRQ_CTRLUPD_REQ_LOW_IDX ]  =  ~i_irq_ctrlupd_req;     // Update interface
      o_irq_fast_int[`DDR_INT_IRQ_PHYUPD_ACK_IDX      ]  =  i_irq_phyupd_ack;       // Update interface
      o_irq_fast_int[`DDR_INT_IRQ_PHYMSTR_ACK_IDX     ]  =  i_irq_phymstr_ack;      // PHY Master interface
      o_irq_fast_int[`DDR_INT_IRQ_AHB_ADR_DET_0_IDX   ]  =  ahb_pat_0_detect;       // AHB write address detect
      o_irq_fast_int[`DDR_INT_IRQ_AHB_ADR_DET_1_IDX   ]  =  ahb_pat_1_detect;       // AHB write address detect
      o_irq_fast_int[`DDR_INT_IRQ_CH1_0_IDX           ]  =  i_irq_ext[2];           // Secondary channel IRQ
      o_irq_fast_int[`DDR_INT_IRQ_CH1_1_IDX           ]  =  i_irq_ext[3];           // Secondary channel IRQ
   end

   assign irq_ibuf          = i_irq_fast_int[`DDR_INT_IRQ_CH0_IBUF_EMPTY_IDX   ] | i_irq_fast_int[`DDR_INT_IRQ_CH0_IBUF_FULL_IDX    ] | i_irq_fast_int[`DDR_INT_IRQ_CH0_IBUF_OVERFLOW_IDX    ] | i_irq_fast_int[`DDR_INT_IRQ_CH1_IBUF_EMPTY_IDX   ] | i_irq_fast_int[`DDR_INT_IRQ_CH1_IBUF_FULL_IDX    ] | i_irq_fast_int[`DDR_INT_IRQ_CH1_IBUF_OVERFLOW_IDX    ];
   assign irq_ebuf          = i_irq_fast_int[`DDR_INT_IRQ_CH0_EBUF_EMPTY_N_IDX ] | i_irq_fast_int[`DDR_INT_IRQ_CH0_EBUF_FULL_IDX    ] | i_irq_fast_int[`DDR_INT_IRQ_CH0_EBUF_OVERFLOW_IDX    ] | i_irq_fast_int[`DDR_INT_IRQ_CH1_EBUF_EMPTY_N_IDX ] | i_irq_fast_int[`DDR_INT_IRQ_CH1_EBUF_FULL_IDX    ] | i_irq_fast_int[`DDR_INT_IRQ_CH1_EBUF_OVERFLOW_IDX    ];
   assign irq_lp_req        = i_irq_fast_int[`DDR_INT_IRQ_LP_DATA_REQ      ] | i_irq_fast_int[`DDR_INT_IRQ_LP_CTRL_REQ      ];
   assign irq_ahb_det       = i_irq_fast_int[`DDR_INT_IRQ_AHB_ADR_DET_0_IDX] | i_irq_fast_int[`DDR_INT_IRQ_AHB_ADR_DET_1_IDX];
   assign irq_ch1           = i_irq_fast_int[`DDR_INT_IRQ_CH1_0_IDX        ] | i_irq_fast_int[`DDR_INT_IRQ_CH1_1_IDX        ];
   assign irq_ctrlupd_req   = i_irq_fast_int[`DDR_INT_IRQ_CTRLUPD_REQ_IDX  ] | i_irq_fast_int[`DDR_INT_IRQ_CTRLUPD_REQ_LOW_IDX] ;

   always_comb begin
      o_irq_fast = '0;
      o_irq_fast[`DDR_IRQ_HOST2MCU_MSG_REQ_IDX] =  i_irq_fast_int[`DDR_INT_IRQ_HOST2MCU_MSG_REQ_IDX]; // host2mcu MSG Request
      o_irq_fast[`DDR_IRQ_MCU2HOST_MSG_ACK_IDX] =  i_irq_fast_int[`DDR_INT_IRQ_MCU2HOST_MSG_ACK_IDX]; // mcu2host MSG Acknowledge
      o_irq_fast[`DDR_IRQ_IBUF_IDX            ] =  irq_ibuf ;                                         // WRITE BUFFER
      o_irq_fast[`DDR_IRQ_EBUF_IDX            ] =  irq_ebuf ;                                         // READ BUFFER
      o_irq_fast[`DDR_IRQ_INIT_START_IDX      ] =  i_irq_fast_int[`DDR_INT_IRQ_INIT_START_IDX      ]; // Status interface
      o_irq_fast[`DDR_IRQ_INIT_COMPLETE_IDX   ] =  i_irq_fast_int[`DDR_INT_IRQ_INIT_COMPLETE_IDX   ]; // Status interface
      o_irq_fast[`DDR_IRQ_LP_REQ              ] =  irq_lp_req;                                        // LP Req interface
      o_irq_fast[`DDR_IRQ_PLL_IDX             ] =  i_irq_fast_int[`DDR_INT_IRQ_PLL_IDX             ]; // PLL
      o_irq_fast[`DDR_IRQ_EXT_0_IDX           ] =  i_irq_fast_int[`DDR_INT_IRQ_EXT_0_IDX           ]; // External IRQ
      o_irq_fast[`DDR_IRQ_EXT_1_IDX           ] =  i_irq_fast_int[`DDR_INT_IRQ_EXT_1_IDX           ]; // External IRQ
      o_irq_fast[`DDR_IRQ_CTRLUPD_REQ_IDX     ] =  irq_ctrlupd_req;                                   // Update interface
      o_irq_fast[`DDR_IRQ_PHYUPD_ACK_IDX      ] =  i_irq_fast_int[`DDR_INT_IRQ_PHYUPD_ACK_IDX      ]; // Update interface
      o_irq_fast[`DDR_IRQ_PHYMSTR_ACK_IDX     ] =  i_irq_fast_int[`DDR_INT_IRQ_PHYMSTR_ACK_IDX     ]; // PHY Master interface
      o_irq_fast[`DDR_IRQ_AHB_ADR_DET_IDX     ] =  irq_ahb_det;                                       // AHB write address detect
      o_irq_fast[`DDR_IRQ_CH1_IDX             ] =  irq_ch1;                                           // Secondary channel
   end
endmodule

module ddr_clk_ctrl (

   // Scan interface
   input  logic                   i_scan_mode,
   input  logic                   i_scan_en,
   input  logic                   i_scan_clk,
   input  logic                   i_scan_cgc_ctrl,
   input  logic                   i_scan_rst_ctrl,
   input  logic [7:0]             i_scan_freq_en,

   // Clock and reset
   input  logic                   i_refclk,                // Reference clock
   input  logic                   i_refclk_alt,            // Reference clock
   input  logic                   i_pll_clk,               // PLL VCO0 clock
   input  logic                   i_ahb_extclk,            // External AHB clock

   input  logic                   i_phy_rst,               // DDR PHY reset
   input  logic                   i_ahb_extrst,            // External AHB reset
   input  logic                   i_ahb_csr_extrst,        // Exteranl AHB CSR reset

   input  logic                   i_ahb_clk_div_en,        // AHB clock divide enable
   input  logic                   i_pll_clk_en,
   input  logic                   i_mcu_clk_cgc_en,
   input  logic                   i_ref_clk_cgc_en,
   input  logic                   i_ref_clk_sel,
   input  logic                   i_mcu_gfm_sel,           // MCU GFCM select
   output logic                   o_mcuclk_gfm_sel0,
   output logic                   o_mcuclk_gfm_sel1,

   output logic                   o_phy_rst,               // PHY clock reset
   output logic                   o_ref_rst,               // Reference clock reset
   output logic                   o_mcu_rst,               // MCU clock reset
   output logic                   o_ahb_rst,               // AHB clock reset
   output logic                   o_ahb_csr_rst,           // AHB CSR reset

   output logic                   o_ref_clk,               // Reference clock w/ scan
   output logic                   o_mcu_clk,               // MCU clock w/ scan
   output logic                   o_ahb_clk,               // AHB clock w/ scan (divided down MCU clock)
   output logic                   o_ahb_extclk             // AHB external clock w/ scan

);

   // ------------------------------------------------------------------------
   // Resets
   // ------------------------------------------------------------------------

   logic scan_phy_rst;
   ddr_scan_rst u_scan_phy_rst     (.i_scan_rst_ctrl(i_scan_rst_ctrl), .i_rst(i_phy_rst), .o_rst(scan_phy_rst));
   ddr_scan_rst u_scan_ahb_rst     (.i_scan_rst_ctrl(i_scan_rst_ctrl), .i_rst(i_ahb_extrst    ), .o_rst(o_ahb_rst    ));
   ddr_scan_rst u_scan_ahb_csr_rst (.i_scan_rst_ctrl(i_scan_rst_ctrl), .i_rst(i_ahb_csr_extrst), .o_rst(o_ahb_csr_rst));

   assign o_phy_rst = scan_phy_rst;
   assign o_ref_rst = scan_phy_rst;
   assign o_mcu_rst = scan_phy_rst;

   // ------------------------------------------------------------------------
   // Clocks
   // ------------------------------------------------------------------------
   logic pll_clk;
   logic refclk;
   logic scan_refclk;
   logic scan_ahb_extclk;
   logic scan_ahb_clk;
   logic scan_mcu_clk;

   ddr_mux u_ref_clk_mux  (.i_sel(i_ref_clk_sel), .i_a(i_refclk), .i_b(i_refclk_alt), .o_z(refclk));
   ddr_and u_pll_clk_gate ( .i_a(i_pll_clk), .i_b(i_pll_clk_en), .o_z(pll_clk));
   ddr_scan_clk_mux u_scan_ref_clk_mux (.i_scan_mode(i_scan_mode), .i_scan_clk(i_scan_clk), .i_clk(refclk     ),  .o_clk(scan_ref_clk   ));
   ddr_scan_clk_mux u_scan_ahb_clk_mux (.i_scan_mode(i_scan_mode), .i_scan_clk(i_scan_clk), .i_clk(i_ahb_extclk), .o_clk(scan_ahb_extclk));

   // MCU clock Mux
   logic mcu_gfm_sel_sync;
   ddr_demet_r  u_demet_0  (.i_rst(o_mcu_rst), .i_clk(scan_mcu_clk), .i_d(i_mcu_gfm_sel), .o_q(mcu_gfm_sel_sync));

   ddr_clk_mux_gf u_mcu_clk_mux_gf (
      .i_clk_0                    (scan_ref_clk),
      .i_clk_1                    (pll_clk),
      .i_clk_rst_0                (o_ref_rst),
      .i_clk_rst_1                (o_phy_rst),
      .i_sel                      (mcu_gfm_sel_sync),
      .i_test_en                  (i_scan_mode),
      .i_cgc_en                   (i_scan_cgc_ctrl),
      .o_sel_0                    (o_mcuclk_gfm_sel0),
      .o_sel_1                    (o_mcuclk_gfm_sel1),
      .o_clk                      (scan_mcu_clk)
   );

   // AHB clock divider
   logic ahb_clk_div_en_sync;
  `ifdef DDR_ECO_AHB_CDIV_EN_DEMET_TYPE
   ddr_demet_s  u_demet_1  (.i_set(o_mcu_rst), .i_clk(scan_mcu_clk), .i_d(i_ahb_clk_div_en), .o_q(ahb_clk_div_en_sync));
  `else
   ddr_demet_r  u_demet_1  (.i_rst(o_mcu_rst), .i_clk(scan_mcu_clk), .i_d(i_ahb_clk_div_en), .o_q(ahb_clk_div_en_sync));
  `endif

   logic ahb_clk_div_byp;
   assign ahb_clk_div_byp = ~ahb_clk_div_en_sync | i_scan_mode;

   ddr_div2_rst u_ahb_clk_div (.i_rst(o_mcu_rst), .i_clk(scan_mcu_clk), .i_div_en(ahb_clk_div_en_sync), .i_div_byp(ahb_clk_div_byp), .o_div2_clk(scan_ahb_clk));

   // DFT Async clocks
   logic mcu_clk_cgc_en_sync;
   logic ref_clk_cgc_en_sync;

   ddr_demet_r  u_demet_2  (.i_rst(o_mcu_rst), .i_clk(scan_mcu_clk), .i_d(i_mcu_clk_cgc_en), .o_q(mcu_clk_cgc_en_sync));
   ddr_demet_r  u_demet_3  (.i_rst(o_ref_rst), .i_clk(scan_ref_clk), .i_d(i_ref_clk_cgc_en), .o_q(ref_clk_cgc_en_sync));

   ddr_cgc_rl  u_cgc0 (.i_clk(scan_ref_clk),    .i_clk_en(ref_clk_cgc_en_sync), .i_cgc_en(i_scan_freq_en[`DDR_FREQ_EN_REFCLK]),    .o_clk(o_ref_clk));
   ddr_cgc_rl  u_cgc1 (.i_clk(scan_mcu_clk),    .i_clk_en(mcu_clk_cgc_en_sync), .i_cgc_en(i_scan_freq_en[`DDR_FREQ_EN_MCUCLK]),    .o_clk(o_mcu_clk));
   ddr_cgc_rl  u_cgc2 (.i_clk(scan_ahb_extclk), .i_clk_en(1'b1),                .i_cgc_en(i_scan_freq_en[`DDR_FREQ_EN_AHBEXTCLK]), .o_clk(o_ahb_extclk));
   ddr_cgc_rl  u_cgc3 (.i_clk(scan_ahb_clk),    .i_clk_en(1'b1),                .i_cgc_en(i_scan_freq_en[`DDR_FREQ_EN_AHBCLK]),    .o_clk(o_ahb_clk));

endmodule
