
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
`include "ddr_dfich_csr_defs.vh"

import wav_ahb_pkg::*;
import ddr_global_pkg::*;

module ddr_dfi #(
   parameter       NUM_DFI_CH       = 1,                                 // Number of DFI Channel
   parameter       NUM_DFI_DQ       = 4,                                 // Number of DFI DQ
   parameter       NUM_PHY_CH       = 2,                                 // Number of PHY Channel
   parameter       NUM_DQ           = 2,                              // Number of PHY DQ
   parameter       NUM_CA           = 1,                              // Number of PHY CA
   parameter       NUM_WPH          = 8,                        // Number of Phases
   parameter       NUM_RPH          = 8,                        // Number of Phases
   parameter       DQ_WIDTH         = 9,                              // DQ bus width
   parameter       DQ_RWIDTH        = NUM_RPH * DQ_WIDTH,                              // DQ read data width
   parameter       DQ_WWIDTH        = NUM_WPH * DQ_WIDTH,                              // DQ write data width
   parameter       DQS_WIDTH        = 9+0, // DQS bus width
   parameter       DQS_WWIDTH       = NUM_WPH * DQS_WIDTH,                             // DQS write data width
   parameter       CA_WIDTH         = 11,                              // DQ bus width
   parameter       CA_RWIDTH        = NUM_RPH * CA_WIDTH,                              // DQ read data width
   parameter       CA_WWIDTH        = NUM_WPH * CA_WIDTH,                              // DQ write data width
   parameter       CK_WIDTH         = 1+8,   // DQS bus width
   parameter       CK_WWIDTH        = NUM_WPH * CK_WIDTH,                              // DQS write data width
   parameter       AHB_AWIDTH       = 16,                                              // AHB address width
   parameter       AHB_DWIDTH       = 32,                                              // AHB data width
   parameter       IG_DEPTH         = 64,                                              // Ingress FIFO depth
   parameter       IG_AWIDTH        = $clog2(IG_DEPTH),
   parameter       EG_DEPTH         = 64,                                              // Egress FIFO depth
   parameter       TSWIDTH          = 16,                                              // TS Width
   parameter       SWIDTH           = 8,                                               // PHY Slice Width
   parameter       DWIDTH           = SWIDTH * 2,                                      // Data Width R+F
   parameter       BWIDTH           = SWIDTH / 8,                                      // BYTE Width
   parameter       MWIDTH           = BWIDTH,                                          // Data Mask width
   parameter       TWIDTH           = BWIDTH * 2,                                      // WCK Toggle width
   parameter       ERRWIDTH         = BWIDTH * 4,                                      // Error Info Width
   parameter       AWIDTH           = 7,                             // Address bus width
   parameter       CWIDTH           = 11,                              // Cmd/Address bus width
   parameter       SIWIDTH          = 20,                                              // DFI Status, LP, UPD, Master Interfaces counter width
   parameter       DFIRDCLKEN_PEXTWIDTH = 4,                                           // RD CLKEN pulse extension width.
   parameter [0:0] RAM_MODEL        = 1'b0                                             // Enable RAM model

) (

   // Scan
   input  logic                      i_scan_mode,
   input  logic                      i_scan_rst_ctrl,
   input  logic                      i_scan_cgc_ctrl,

   // Clock and reset
   input  logic                      i_rst,
   output logic                      o_dfi_clk,

   input  logic                      i_ch0_phy_clk,
   input  logic                      i_ch0_dfiwr_clk_1,
   input  logic                      i_ch0_dfiwr_clk_2,
   input  logic                      i_ch0_dfird_clk_1,
   input  logic                      i_ch0_dfird_clk_2,
   input  logic                      i_ch1_phy_clk,
   input  logic                      i_ch1_dfiwr_clk_1,
   input  logic                      i_ch1_dfiwr_clk_2,
   input  logic                      i_ch1_dfird_clk_1,
   input  logic                      i_ch1_dfird_clk_2,

   //DFI signals
   output logic                      o_ch0_dfidq_wrtraffic,
   output logic                      o_ch0_dfidqs_wrtraffic,
   output logic                      o_ch0_dfica_traffic,
   output logic                      o_ch0_dfick_traffic,
   output logic [DEC_DFIGBWIDTH-1:0] o_ch0_dfiwrgb_mode,
   output logic [DEC_DFIGBWIDTH-1:0] o_ch0_dfirdgb_mode,
   output logic [3:0]                o_ch0_dfirdclk_en_pulse_ext,
   output logic                      o_ch0_dfirdclk_en_ovr_sel,
   output logic                      o_ch0_dfirdclk_en_ovr,
   output logic                      o_ch1_dfidq_wrtraffic,
   output logic                      o_ch1_dfidqs_wrtraffic,
   output logic                      o_ch1_dfica_traffic,
   output logic                      o_ch1_dfick_traffic,
   output logic [DEC_DFIGBWIDTH-1:0] o_ch1_dfiwrgb_mode,
   output logic [DEC_DFIGBWIDTH-1:0] o_ch1_dfirdgb_mode,
   output logic [3:0]                o_ch1_dfirdclk_en_pulse_ext,
   output logic                      o_ch1_dfirdclk_en_ovr_sel,
   output logic                      o_ch1_dfirdclk_en_ovr,
   output logic                      o_ch1_dfi_ibuf_empty_irq,
   output logic                      o_ch1_dfi_ibuf_full_irq,
   output logic                      o_ch1_dfi_ibuf_overflow_irq,
   output logic                      o_ch1_dfi_ebuf_empty_irq,
   output logic                      o_ch1_dfi_ebuf_full_irq,
   output logic                      o_ch1_dfi_ebuf_overflow_irq,
   output logic                      o_ch0_dfi_ibuf_empty_irq,
   output logic                      o_ch0_dfi_ibuf_full_irq,
   output logic                      o_ch0_dfi_ibuf_overflow_irq,
   output logic                      o_ch0_dfi_ebuf_empty_irq,
   output logic                      o_ch0_dfi_ebuf_full_irq,
   output logic                      o_ch0_dfi_ebuf_overflow_irq,

   input  logic                      i_ahb_clk,
   input  logic                      i_ahb_rst,

   input  logic [AHB_AWIDTH-1:0]     i_ahb_haddr,
   input  logic                      i_ahb_hwrite,
   input  logic                      i_ahb_hsel,
   input  logic [AHB_DWIDTH-1:0]     i_ahb_hwdata,
   input  logic [1:0]                i_ahb_htrans,
   input  logic [2:0]                i_ahb_hsize,
   input  logic [2:0]                i_ahb_hburst,
   input  logic                      i_ahb_hreadyin,
   output logic                      o_ahb_hready,
   output logic [AHB_DWIDTH-1:0]     o_ahb_hrdata,
   output logic [1:0]                o_ahb_hresp,

   input  logic                      i_msr,
   input  logic                      i_init_complete,

   // Update
   output logic                      o_dfi_ctrlupd_ack,
   output logic                      o_dfi_ctrlupd_req,
   input  logic                      i_dfi_ctrlupd_req,
   output logic                      o_dfi_phyupd_ack,
   input  logic                      i_dfi_phyupd_ack,
   output logic                      o_dfi_phyupd_req,
   output logic [1:0]                o_dfi_phyupd_type,

   // Status
   input  logic [1:0]                i_dfi_freq_fsp,
   input  logic [1:0]                i_dfi_freq_ratio,
   input  logic [4:0]                i_dfi_frequency,
   output logic                      o_dfi_init_complete,
   output logic                      o_irq_dfi_init_complete,
   output logic                      o_dfi_init_start,
   input  logic                      i_dfi_init_start,

   // PHY Master
   output logic                      o_dfi_phymstr_ack,
   input  logic                      i_dfi_phymstr_ack,
   output logic [1:0]                o_dfi_phymstr_cs_state,
   output logic                      o_dfi_phymstr_req,
   output logic                      o_dfi_phymstr_state_sel,
   output logic [1:0]                o_dfi_phymstr_type,



   // Low Power Control
   output logic                      o_dfi_lp_ctrl_ack,
   output logic                      o_dfi_lp_ctrl_req,
   input  logic                      i_dfi_lp_ctrl_req,
   input  logic [5:0]                i_dfi_lp_ctrl_wakeup,
   output logic                      o_dfi_lp_data_ack,
   output logic                      o_dfi_lp_data_req,
   input  logic                      i_dfi_lp_data_req,
   input  logic [5:0]                i_dfi_lp_data_wakeup,


   // Command
   input  logic                      i_dfi_reset_n_p0,              // DDR/3/4/5 and LPDDR4/5
   input  logic                      i_dfi_reset_n_p1,              // DDR/3/4/5 and LPDDR4/5
   input  logic                      i_dfi_reset_n_p2,              // DDR/3/4/5 and LPDDR4/5
   input  logic                      i_dfi_reset_n_p3,              // DDR/3/4/5 and LPDDR4/5
   input  logic                      i_dfi_reset_n_p4,              // DDR/3/4/5 and LPDDR4/5
   input  logic                      i_dfi_reset_n_p5,              // DDR/3/4/5 and LPDDR4/5
   input  logic                      i_dfi_reset_n_p6,              // DDR/3/4/5 and LPDDR4/5
   input  logic                      i_dfi_reset_n_p7,              // DDR/3/4/5 and LPDDR4/5

   input  logic [AWIDTH-1:0]         i_dfi_address_p0,              // For DDR4 bits[16:14] are not used
   input  logic [AWIDTH-1:0]         i_dfi_address_p1,              // For DDR4 bits[16:14] are not used
   input  logic [AWIDTH-1:0]         i_dfi_address_p2,              // For DDR4 bits[16:14] are not used
   input  logic [AWIDTH-1:0]         i_dfi_address_p3,              // For DDR4 bits[16:14] are not used
   input  logic [AWIDTH-1:0]         i_dfi_address_p4,              // For DDR4 bits[16:14] are not used
   input  logic [AWIDTH-1:0]         i_dfi_address_p5,              // For DDR4 bits[16:14] are not used
   input  logic [AWIDTH-1:0]         i_dfi_address_p6,              // For DDR4 bits[16:14] are not used
   input  logic [AWIDTH-1:0]         i_dfi_address_p7,              // For DDR4 bits[16:14] are not used
   input  logic [1:0]                i_dfi_cke_p0,                  // DDR1/2/3/4 and LPDDR3/4
   input  logic [1:0]                i_dfi_cke_p1,                  // DDR1/2/3/4 and LPDDR3/4
   input  logic [1:0]                i_dfi_cke_p2,                  // DDR1/2/3/4 and LPDDR3/4
   input  logic [1:0]                i_dfi_cke_p3,                  // DDR1/2/3/4 and LPDDR3/4
   input  logic [1:0]                i_dfi_cke_p4,                  // DDR1/2/3/4 and LPDDR3/4
   input  logic [1:0]                i_dfi_cke_p5,                  // DDR1/2/3/4 and LPDDR3/4
   input  logic [1:0]                i_dfi_cke_p6,                  // DDR1/2/3/4 and LPDDR3/4
   input  logic [1:0]                i_dfi_cke_p7,                  // DDR1/2/3/4 and LPDDR3/4
   input  logic [1:0]                i_dfi_cs_p0,
   input  logic [1:0]                i_dfi_cs_p1,
   input  logic [1:0]                i_dfi_cs_p2,
   input  logic [1:0]                i_dfi_cs_p3,
   input  logic [1:0]                i_dfi_cs_p4,
   input  logic [1:0]                i_dfi_cs_p5,
   input  logic [1:0]                i_dfi_cs_p6,
   input  logic [1:0]                i_dfi_cs_p7,
   input  logic                      i_dfi_dram_clk_disable_p0,
   input  logic                      i_dfi_dram_clk_disable_p1,
   input  logic                      i_dfi_dram_clk_disable_p2,
   input  logic                      i_dfi_dram_clk_disable_p3,
   input  logic                      i_dfi_dram_clk_disable_p4,
   input  logic                      i_dfi_dram_clk_disable_p5,
   input  logic                      i_dfi_dram_clk_disable_p6,
   input  logic                      i_dfi_dram_clk_disable_p7,

   // Write Data
   input  logic                      i_dfi_parity_in_p0,
   input  logic                      i_dfi_parity_in_p1,
   input  logic                      i_dfi_parity_in_p2,
   input  logic                      i_dfi_parity_in_p3,
   input  logic                      i_dfi_parity_in_p4,
   input  logic                      i_dfi_parity_in_p5,
   input  logic                      i_dfi_parity_in_p6,
   input  logic                      i_dfi_parity_in_p7,
   input  logic [1:0]                i_dfi_wrdata_cs_p0,
   input  logic [1:0]                i_dfi_wrdata_cs_p1,
   input  logic [1:0]                i_dfi_wrdata_cs_p2,
   input  logic [1:0]                i_dfi_wrdata_cs_p3,
   input  logic [1:0]                i_dfi_wrdata_cs_p4,
   input  logic [1:0]                i_dfi_wrdata_cs_p5,
   input  logic [1:0]                i_dfi_wrdata_cs_p6,
   input  logic [1:0]                i_dfi_wrdata_cs_p7,
   input  logic                      i_dfi_wrdata_en_p0,
   input  logic                      i_dfi_wrdata_en_p1,
   input  logic                      i_dfi_wrdata_en_p2,
   input  logic                      i_dfi_wrdata_en_p3,
   input  logic                      i_dfi_wrdata_en_p4,
   input  logic                      i_dfi_wrdata_en_p5,
   input  logic                      i_dfi_wrdata_en_p6,
   input  logic                      i_dfi_wrdata_en_p7,
   input  logic [NUM_DFI_DQ*SWIDTH-1:0] i_dfi_wrdata_p0,
   input  logic [NUM_DFI_DQ*SWIDTH-1:0] i_dfi_wrdata_p1,
   input  logic [NUM_DFI_DQ*SWIDTH-1:0] i_dfi_wrdata_p2,
   input  logic [NUM_DFI_DQ*SWIDTH-1:0] i_dfi_wrdata_p3,
   input  logic [NUM_DFI_DQ*SWIDTH-1:0] i_dfi_wrdata_p4,
   input  logic [NUM_DFI_DQ*SWIDTH-1:0] i_dfi_wrdata_p5,
   input  logic [NUM_DFI_DQ*SWIDTH-1:0] i_dfi_wrdata_p6,
   input  logic [NUM_DFI_DQ*SWIDTH-1:0] i_dfi_wrdata_p7,
   input  logic [NUM_DFI_DQ*MWIDTH-1:0] i_dfi_wrdata_mask_p0,
   input  logic [NUM_DFI_DQ*MWIDTH-1:0] i_dfi_wrdata_mask_p1,
   input  logic [NUM_DFI_DQ*MWIDTH-1:0] i_dfi_wrdata_mask_p2,
   input  logic [NUM_DFI_DQ*MWIDTH-1:0] i_dfi_wrdata_mask_p3,
   input  logic [NUM_DFI_DQ*MWIDTH-1:0] i_dfi_wrdata_mask_p4,
   input  logic [NUM_DFI_DQ*MWIDTH-1:0] i_dfi_wrdata_mask_p5,
   input  logic [NUM_DFI_DQ*MWIDTH-1:0] i_dfi_wrdata_mask_p6,
   input  logic [NUM_DFI_DQ*MWIDTH-1:0] i_dfi_wrdata_mask_p7,

   input  logic [1:0]                i_dfi_wck_cs_p0,
   input  logic [1:0]                i_dfi_wck_cs_p1,
   input  logic [1:0]                i_dfi_wck_cs_p2,
   input  logic [1:0]                i_dfi_wck_cs_p3,
   input  logic [1:0]                i_dfi_wck_cs_p4,
   input  logic [1:0]                i_dfi_wck_cs_p5,
   input  logic [1:0]                i_dfi_wck_cs_p6,
   input  logic [1:0]                i_dfi_wck_cs_p7,
   input  logic                      i_dfi_wck_en_p0,
   input  logic                      i_dfi_wck_en_p1,
   input  logic                      i_dfi_wck_en_p2,
   input  logic                      i_dfi_wck_en_p3,
   input  logic                      i_dfi_wck_en_p4,
   input  logic                      i_dfi_wck_en_p5,
   input  logic                      i_dfi_wck_en_p6,
   input  logic                      i_dfi_wck_en_p7,
   input  logic [TWIDTH-1:0]         i_dfi_wck_toggle_p0,
   input  logic [TWIDTH-1:0]         i_dfi_wck_toggle_p1,
   input  logic [TWIDTH-1:0]         i_dfi_wck_toggle_p2,
   input  logic [TWIDTH-1:0]         i_dfi_wck_toggle_p3,
   input  logic [TWIDTH-1:0]         i_dfi_wck_toggle_p4,
   input  logic [TWIDTH-1:0]         i_dfi_wck_toggle_p5,
   input  logic [TWIDTH-1:0]         i_dfi_wck_toggle_p6,
   input  logic [TWIDTH-1:0]         i_dfi_wck_toggle_p7,

   // Read Data
   input  logic [1:0]                i_dfi_rddata_cs_p0,
   input  logic [1:0]                i_dfi_rddata_cs_p1,
   input  logic [1:0]                i_dfi_rddata_cs_p2,
   input  logic [1:0]                i_dfi_rddata_cs_p3,
   input  logic [1:0]                i_dfi_rddata_cs_p4,
   input  logic [1:0]                i_dfi_rddata_cs_p5,
   input  logic [1:0]                i_dfi_rddata_cs_p6,
   input  logic [1:0]                i_dfi_rddata_cs_p7,
   input  logic                      i_dfi_rddata_en_p0,
   input  logic                      i_dfi_rddata_en_p1,
   input  logic                      i_dfi_rddata_en_p2,
   input  logic                      i_dfi_rddata_en_p3,
   input  logic                      i_dfi_rddata_en_p4,
   input  logic                      i_dfi_rddata_en_p5,
   input  logic                      i_dfi_rddata_en_p6,
   input  logic                      i_dfi_rddata_en_p7,

   output logic [NUM_DFI_DQ*SWIDTH-1:0] o_dfi_rddata_w0,
   output logic [NUM_DFI_DQ*SWIDTH-1:0] o_dfi_rddata_w1,
   output logic [NUM_DFI_DQ*SWIDTH-1:0] o_dfi_rddata_w2,
   output logic [NUM_DFI_DQ*SWIDTH-1:0] o_dfi_rddata_w3,
   output logic [NUM_DFI_DQ*SWIDTH-1:0] o_dfi_rddata_w4,
   output logic [NUM_DFI_DQ*SWIDTH-1:0] o_dfi_rddata_w5,
   output logic [NUM_DFI_DQ*SWIDTH-1:0] o_dfi_rddata_w6,
   output logic [NUM_DFI_DQ*SWIDTH-1:0] o_dfi_rddata_w7,
   output logic [NUM_DFI_DQ*MWIDTH-1:0] o_dfi_rddata_dbi_w0,
   output logic [NUM_DFI_DQ*MWIDTH-1:0] o_dfi_rddata_dbi_w1,
   output logic [NUM_DFI_DQ*MWIDTH-1:0] o_dfi_rddata_dbi_w2,
   output logic [NUM_DFI_DQ*MWIDTH-1:0] o_dfi_rddata_dbi_w3,
   output logic [NUM_DFI_DQ*MWIDTH-1:0] o_dfi_rddata_dbi_w4,
   output logic [NUM_DFI_DQ*MWIDTH-1:0] o_dfi_rddata_dbi_w5,
   output logic [NUM_DFI_DQ*MWIDTH-1:0] o_dfi_rddata_dbi_w6,
   output logic [NUM_DFI_DQ*MWIDTH-1:0] o_dfi_rddata_dbi_w7,
   output logic                      o_dfi_rddata_valid_w0,
   output logic                      o_dfi_rddata_valid_w1,
   output logic                      o_dfi_rddata_valid_w2,
   output logic                      o_dfi_rddata_valid_w3,
   output logic                      o_dfi_rddata_valid_w4,
   output logic                      o_dfi_rddata_valid_w5,
   output logic                      o_dfi_rddata_valid_w6,
   output logic                      o_dfi_rddata_valid_w7,

   input  logic                     i_txrx_mode,

   output logic [DQ_WWIDTH-1:0]     o_ch0_dq0_sdr,
   output logic [DQS_WWIDTH-1:0]    o_ch0_dqs0_sdr,
   input  logic [DQ_RWIDTH-1:0]     i_ch0_dq0_sdr,
   input  logic [DQ_WIDTH-1:0]      i_ch0_dq0_sdr_vld,
   output logic [DQ_WWIDTH-1:0]     o_ch0_dq1_sdr,
   output logic [DQS_WWIDTH-1:0]    o_ch0_dqs1_sdr,
   input  logic [DQ_RWIDTH-1:0]     i_ch0_dq1_sdr,
   input  logic [DQ_WIDTH-1:0]      i_ch0_dq1_sdr_vld,
   input  logic [DQ_WWIDTH-1:0]     i_ch0_tx0_sdr,
   input  logic [DQS_WWIDTH-1:0]    i_ch0_tx_ck0_sdr,
   output logic [DQ_RWIDTH-1:0]     o_ch0_rx0_sdr,
   output logic [DQ_WIDTH-1:0]      o_ch0_rx0_sdr_vld,
   input  logic [DQ_WWIDTH-1:0]     i_ch0_tx1_sdr,
   input  logic [DQS_WWIDTH-1:0]    i_ch0_tx_ck1_sdr,
   output logic [DQ_RWIDTH-1:0]     o_ch0_rx1_sdr,
   output logic [DQ_WIDTH-1:0]      o_ch0_rx1_sdr_vld,
   output logic [CA_WWIDTH-1:0]     o_ch0_ca_sdr,
   output logic [CK_WWIDTH-1:0]     o_ch0_ck_sdr,
   input  logic [CA_RWIDTH-1:0]     i_ch0_ca_sdr,
   input  logic [CA_WIDTH-1:0]      i_ch0_ca_sdr_vld,
   output logic [DQ_WWIDTH-1:0]     o_ch1_dq0_sdr,
   output logic [DQS_WWIDTH-1:0]    o_ch1_dqs0_sdr,
   input  logic [DQ_RWIDTH-1:0]     i_ch1_dq0_sdr,
   input  logic [DQ_WIDTH-1:0]      i_ch1_dq0_sdr_vld,
   output logic [DQ_WWIDTH-1:0]     o_ch1_dq1_sdr,
   output logic [DQS_WWIDTH-1:0]    o_ch1_dqs1_sdr,
   input  logic [DQ_RWIDTH-1:0]     i_ch1_dq1_sdr,
   input  logic [DQ_WIDTH-1:0]      i_ch1_dq1_sdr_vld,
   input  logic [DQ_WWIDTH-1:0]     i_ch1_tx0_sdr,
   input  logic [DQS_WWIDTH-1:0]    i_ch1_tx_ck0_sdr,
   output logic [DQ_RWIDTH-1:0]     o_ch1_rx0_sdr,
   output logic [DQ_WIDTH-1:0]      o_ch1_rx0_sdr_vld,
   input  logic [DQ_WWIDTH-1:0]     i_ch1_tx1_sdr,
   input  logic [DQS_WWIDTH-1:0]    i_ch1_tx_ck1_sdr,
   output logic [DQ_RWIDTH-1:0]     o_ch1_rx1_sdr,
   output logic [DQ_WIDTH-1:0]      o_ch1_rx1_sdr_vld,
   output logic [CA_WWIDTH-1:0]     o_ch1_ca_sdr,
   output logic [CK_WWIDTH-1:0]     o_ch1_ck_sdr,
   input  logic [CA_RWIDTH-1:0]     i_ch1_ca_sdr,
   input  logic [CA_WIDTH-1:0]      i_ch1_ca_sdr_vld,

   output logic [31:0]              o_debug
);

    localparam PWIDTH  = 6;
    localparam F0WIDTH = 2;
      localparam F1WIDTH = 3;
        localparam F2WIDTH = 4;
        localparam MAXF2DLY = 10 ;

   logic [AWIDTH-1:0]        y_ch0_dfi_address_p0;
   logic [AWIDTH-1:0]        y_ch0_dfi_address_p1;
   logic [AWIDTH-1:0]        y_ch0_dfi_address_p2;
   logic [AWIDTH-1:0]        y_ch0_dfi_address_p3;
   logic [AWIDTH-1:0]        y_ch0_dfi_address_p4;
   logic [AWIDTH-1:0]        y_ch0_dfi_address_p5;
   logic [AWIDTH-1:0]        y_ch0_dfi_address_p6;
   logic [AWIDTH-1:0]        y_ch0_dfi_address_p7;
   logic [1:0]               y_ch0_dfi_cke_p0;
   logic [1:0]               y_ch0_dfi_cke_p1;
   logic [1:0]               y_ch0_dfi_cke_p2;
   logic [1:0]               y_ch0_dfi_cke_p3;
   logic [1:0]               y_ch0_dfi_cke_p4;
   logic [1:0]               y_ch0_dfi_cke_p5;
   logic [1:0]               y_ch0_dfi_cke_p6;
   logic [1:0]               y_ch0_dfi_cke_p7;
   logic [1:0]               y_ch0_dfi_cs_p0;
   logic [1:0]               y_ch0_dfi_cs_p1;
   logic [1:0]               y_ch0_dfi_cs_p2;
   logic [1:0]               y_ch0_dfi_cs_p3;
   logic [1:0]               y_ch0_dfi_cs_p4;
   logic [1:0]               y_ch0_dfi_cs_p5;
   logic [1:0]               y_ch0_dfi_cs_p6;
   logic [1:0]               y_ch0_dfi_cs_p7;
   logic                     y_ch0_dfi_carddata_en_p0;
   logic                     y_ch0_dfi_carddata_en_p1;
   logic                     y_ch0_dfi_carddata_en_p2;
   logic                     y_ch0_dfi_carddata_en_p3;
   logic                     y_ch0_dfi_carddata_en_p4;
   logic                     y_ch0_dfi_carddata_en_p5;
   logic                     y_ch0_dfi_carddata_en_p6;
   logic                     y_ch0_dfi_carddata_en_p7;
   logic                     y_ch0_dfi_dram_clk_disable_p0;
   logic                     y_ch0_dfi_dram_clk_disable_p1;
   logic                     y_ch0_dfi_dram_clk_disable_p2;
   logic                     y_ch0_dfi_dram_clk_disable_p3;
   logic                     y_ch0_dfi_dram_clk_disable_p4;
   logic                     y_ch0_dfi_dram_clk_disable_p5;
   logic                     y_ch0_dfi_dram_clk_disable_p6;
   logic                     y_ch0_dfi_dram_clk_disable_p7;
   logic                     y_ch0_dfi_dram_clk_enable_p0;
   logic                     y_ch0_dfi_dram_clk_enable_p1;
   logic                     y_ch0_dfi_dram_clk_enable_p2;
   logic                     y_ch0_dfi_dram_clk_enable_p3;
   logic                     y_ch0_dfi_dram_clk_enable_p4;
   logic                     y_ch0_dfi_dram_clk_enable_p5;
   logic                     y_ch0_dfi_dram_clk_enable_p6;
   logic                     y_ch0_dfi_dram_clk_enable_p7;
   logic [SWIDTH-1:0]        y_ch0_dq0_dfi_wrdata_p0;
   logic [SWIDTH-1:0]        y_ch0_dq0_dfi_wrdata_p1;
   logic [SWIDTH-1:0]        y_ch0_dq0_dfi_wrdata_p2;
   logic [SWIDTH-1:0]        y_ch0_dq0_dfi_wrdata_p3;
   logic [SWIDTH-1:0]        y_ch0_dq0_dfi_wrdata_p4;
   logic [SWIDTH-1:0]        y_ch0_dq0_dfi_wrdata_p5;
   logic [SWIDTH-1:0]        y_ch0_dq0_dfi_wrdata_p6;
   logic [SWIDTH-1:0]        y_ch0_dq0_dfi_wrdata_p7;
   logic [MWIDTH-1:0]        y_ch0_dq0_dfi_wrdata_mask_p0;
   logic [MWIDTH-1:0]        y_ch0_dq0_dfi_wrdata_mask_p1;
   logic [MWIDTH-1:0]        y_ch0_dq0_dfi_wrdata_mask_p2;
   logic [MWIDTH-1:0]        y_ch0_dq0_dfi_wrdata_mask_p3;
   logic [MWIDTH-1:0]        y_ch0_dq0_dfi_wrdata_mask_p4;
   logic [MWIDTH-1:0]        y_ch0_dq0_dfi_wrdata_mask_p5;
   logic [MWIDTH-1:0]        y_ch0_dq0_dfi_wrdata_mask_p6;
   logic [MWIDTH-1:0]        y_ch0_dq0_dfi_wrdata_mask_p7;
    logic                    y_ch0_dq0_dfi_parity_in_p0;
    logic                    y_ch0_dq0_dfi_parity_in_p1;
    logic                    y_ch0_dq0_dfi_parity_in_p2;
    logic                    y_ch0_dq0_dfi_parity_in_p3;
    logic                    y_ch0_dq0_dfi_parity_in_p4;
    logic                    y_ch0_dq0_dfi_parity_in_p5;
    logic                    y_ch0_dq0_dfi_parity_in_p6;
    logic                    y_ch0_dq0_dfi_parity_in_p7;
   logic                     y_ch0_dq0_dfi_wrdata_cs_p0;
   logic                     y_ch0_dq0_dfi_wrdata_cs_p1;
   logic                     y_ch0_dq0_dfi_wrdata_cs_p2;
   logic                     y_ch0_dq0_dfi_wrdata_cs_p3;
   logic                     y_ch0_dq0_dfi_wrdata_cs_p4;
   logic                     y_ch0_dq0_dfi_wrdata_cs_p5;
   logic                     y_ch0_dq0_dfi_wrdata_cs_p6;
   logic                     y_ch0_dq0_dfi_wrdata_cs_p7;
   logic                     y_ch0_dq0_dfi_wrdata_en_p0;
   logic                     y_ch0_dq0_dfi_wrdata_en_p1;
   logic                     y_ch0_dq0_dfi_wrdata_en_p2;
   logic                     y_ch0_dq0_dfi_wrdata_en_p3;
   logic                     y_ch0_dq0_dfi_wrdata_en_p4;
   logic                     y_ch0_dq0_dfi_wrdata_en_p5;
   logic                     y_ch0_dq0_dfi_wrdata_en_p6;
   logic                     y_ch0_dq0_dfi_wrdata_en_p7;
   logic                     y_ch0_dq0_dfi_wrdata_oe_p0;
   logic                     y_ch0_dq0_dfi_wrdata_oe_p1;
   logic                     y_ch0_dq0_dfi_wrdata_oe_p2;
   logic                     y_ch0_dq0_dfi_wrdata_oe_p3;
   logic                     y_ch0_dq0_dfi_wrdata_oe_p4;
   logic                     y_ch0_dq0_dfi_wrdata_oe_p5;
   logic                     y_ch0_dq0_dfi_wrdata_oe_p6;
   logic                     y_ch0_dq0_dfi_wrdata_oe_p7;
   logic                     y_ch0_dq0_dfi_wck_en_p0;
   logic                     y_ch0_dq0_dfi_wck_en_p1;
   logic                     y_ch0_dq0_dfi_wck_en_p2;
   logic                     y_ch0_dq0_dfi_wck_en_p3;
   logic                     y_ch0_dq0_dfi_wck_en_p4;
   logic                     y_ch0_dq0_dfi_wck_en_p5;
   logic                     y_ch0_dq0_dfi_wck_en_p6;
   logic                     y_ch0_dq0_dfi_wck_en_p7;
   logic                     y_ch0_dq0_dfi_wck_oe_p0;
   logic                     y_ch0_dq0_dfi_wck_oe_p1;
   logic                     y_ch0_dq0_dfi_wck_oe_p2;
   logic                     y_ch0_dq0_dfi_wck_oe_p3;
   logic                     y_ch0_dq0_dfi_wck_oe_p4;
   logic                     y_ch0_dq0_dfi_wck_oe_p5;
   logic                     y_ch0_dq0_dfi_wck_oe_p6;
   logic                     y_ch0_dq0_dfi_wck_oe_p7;
   logic                     y_ch0_dq0_dfi_wck_cs_p0;
   logic                     y_ch0_dq0_dfi_wck_cs_p1;
   logic                     y_ch0_dq0_dfi_wck_cs_p2;
   logic                     y_ch0_dq0_dfi_wck_cs_p3;
   logic                     y_ch0_dq0_dfi_wck_cs_p4;
   logic                     y_ch0_dq0_dfi_wck_cs_p5;
   logic                     y_ch0_dq0_dfi_wck_cs_p6;
   logic                     y_ch0_dq0_dfi_wck_cs_p7;
   logic                     y_ch0_dq0_dfi_wck_ten_p0;
   logic                     y_ch0_dq0_dfi_wck_ten_p1;
   logic                     y_ch0_dq0_dfi_wck_ten_p2;
   logic                     y_ch0_dq0_dfi_wck_ten_p3;
   logic                     y_ch0_dq0_dfi_wck_ten_p4;
   logic                     y_ch0_dq0_dfi_wck_ten_p5;
   logic                     y_ch0_dq0_dfi_wck_ten_p6;
   logic                     y_ch0_dq0_dfi_wck_ten_p7;
    logic                    y_ch0_dq0_dfi_rddata_cs_p0;
    logic                    y_ch0_dq0_dfi_rddata_cs_p1;
    logic                    y_ch0_dq0_dfi_rddata_cs_p2;
    logic                    y_ch0_dq0_dfi_rddata_cs_p3;
    logic                    y_ch0_dq0_dfi_rddata_cs_p4;
    logic                    y_ch0_dq0_dfi_rddata_cs_p5;
    logic                    y_ch0_dq0_dfi_rddata_cs_p6;
    logic                    y_ch0_dq0_dfi_rddata_cs_p7;
    logic                    y_ch0_dq0_dfi_rddata_en_p0;
    logic                    y_ch0_dq0_dfi_rddata_en_p1;
    logic                    y_ch0_dq0_dfi_rddata_en_p2;
    logic                    y_ch0_dq0_dfi_rddata_en_p3;
    logic                    y_ch0_dq0_dfi_rddata_en_p4;
    logic                    y_ch0_dq0_dfi_rddata_en_p5;
    logic                    y_ch0_dq0_dfi_rddata_en_p6;
    logic                    y_ch0_dq0_dfi_rddata_en_p7;
    logic                    y_ch0_dq0_dfi_rddata_ie_p0;
    logic                    y_ch0_dq0_dfi_rddata_ie_p1;
    logic                    y_ch0_dq0_dfi_rddata_ie_p2;
    logic                    y_ch0_dq0_dfi_rddata_ie_p3;
    logic                    y_ch0_dq0_dfi_rddata_ie_p4;
    logic                    y_ch0_dq0_dfi_rddata_ie_p5;
    logic                    y_ch0_dq0_dfi_rddata_ie_p6;
    logic                    y_ch0_dq0_dfi_rddata_ie_p7;
    logic                    y_ch0_dq0_dfi_rddata_re_p0;
    logic                    y_ch0_dq0_dfi_rddata_re_p1;
    logic                    y_ch0_dq0_dfi_rddata_re_p2;
    logic                    y_ch0_dq0_dfi_rddata_re_p3;
    logic                    y_ch0_dq0_dfi_rddata_re_p4;
    logic                    y_ch0_dq0_dfi_rddata_re_p5;
    logic                    y_ch0_dq0_dfi_rddata_re_p6;
    logic                    y_ch0_dq0_dfi_rddata_re_p7;
   logic [SWIDTH-1:0]        y_ch0_dq1_dfi_wrdata_p0;
   logic [SWIDTH-1:0]        y_ch0_dq1_dfi_wrdata_p1;
   logic [SWIDTH-1:0]        y_ch0_dq1_dfi_wrdata_p2;
   logic [SWIDTH-1:0]        y_ch0_dq1_dfi_wrdata_p3;
   logic [SWIDTH-1:0]        y_ch0_dq1_dfi_wrdata_p4;
   logic [SWIDTH-1:0]        y_ch0_dq1_dfi_wrdata_p5;
   logic [SWIDTH-1:0]        y_ch0_dq1_dfi_wrdata_p6;
   logic [SWIDTH-1:0]        y_ch0_dq1_dfi_wrdata_p7;
   logic [MWIDTH-1:0]        y_ch0_dq1_dfi_wrdata_mask_p0;
   logic [MWIDTH-1:0]        y_ch0_dq1_dfi_wrdata_mask_p1;
   logic [MWIDTH-1:0]        y_ch0_dq1_dfi_wrdata_mask_p2;
   logic [MWIDTH-1:0]        y_ch0_dq1_dfi_wrdata_mask_p3;
   logic [MWIDTH-1:0]        y_ch0_dq1_dfi_wrdata_mask_p4;
   logic [MWIDTH-1:0]        y_ch0_dq1_dfi_wrdata_mask_p5;
   logic [MWIDTH-1:0]        y_ch0_dq1_dfi_wrdata_mask_p6;
   logic [MWIDTH-1:0]        y_ch0_dq1_dfi_wrdata_mask_p7;
    logic                    y_ch0_dq1_dfi_parity_in_p0;
    logic                    y_ch0_dq1_dfi_parity_in_p1;
    logic                    y_ch0_dq1_dfi_parity_in_p2;
    logic                    y_ch0_dq1_dfi_parity_in_p3;
    logic                    y_ch0_dq1_dfi_parity_in_p4;
    logic                    y_ch0_dq1_dfi_parity_in_p5;
    logic                    y_ch0_dq1_dfi_parity_in_p6;
    logic                    y_ch0_dq1_dfi_parity_in_p7;
   logic                     y_ch0_dq1_dfi_wrdata_cs_p0;
   logic                     y_ch0_dq1_dfi_wrdata_cs_p1;
   logic                     y_ch0_dq1_dfi_wrdata_cs_p2;
   logic                     y_ch0_dq1_dfi_wrdata_cs_p3;
   logic                     y_ch0_dq1_dfi_wrdata_cs_p4;
   logic                     y_ch0_dq1_dfi_wrdata_cs_p5;
   logic                     y_ch0_dq1_dfi_wrdata_cs_p6;
   logic                     y_ch0_dq1_dfi_wrdata_cs_p7;
   logic                     y_ch0_dq1_dfi_wrdata_en_p0;
   logic                     y_ch0_dq1_dfi_wrdata_en_p1;
   logic                     y_ch0_dq1_dfi_wrdata_en_p2;
   logic                     y_ch0_dq1_dfi_wrdata_en_p3;
   logic                     y_ch0_dq1_dfi_wrdata_en_p4;
   logic                     y_ch0_dq1_dfi_wrdata_en_p5;
   logic                     y_ch0_dq1_dfi_wrdata_en_p6;
   logic                     y_ch0_dq1_dfi_wrdata_en_p7;
   logic                     y_ch0_dq1_dfi_wrdata_oe_p0;
   logic                     y_ch0_dq1_dfi_wrdata_oe_p1;
   logic                     y_ch0_dq1_dfi_wrdata_oe_p2;
   logic                     y_ch0_dq1_dfi_wrdata_oe_p3;
   logic                     y_ch0_dq1_dfi_wrdata_oe_p4;
   logic                     y_ch0_dq1_dfi_wrdata_oe_p5;
   logic                     y_ch0_dq1_dfi_wrdata_oe_p6;
   logic                     y_ch0_dq1_dfi_wrdata_oe_p7;
   logic                     y_ch0_dq1_dfi_wck_en_p0;
   logic                     y_ch0_dq1_dfi_wck_en_p1;
   logic                     y_ch0_dq1_dfi_wck_en_p2;
   logic                     y_ch0_dq1_dfi_wck_en_p3;
   logic                     y_ch0_dq1_dfi_wck_en_p4;
   logic                     y_ch0_dq1_dfi_wck_en_p5;
   logic                     y_ch0_dq1_dfi_wck_en_p6;
   logic                     y_ch0_dq1_dfi_wck_en_p7;
   logic                     y_ch0_dq1_dfi_wck_oe_p0;
   logic                     y_ch0_dq1_dfi_wck_oe_p1;
   logic                     y_ch0_dq1_dfi_wck_oe_p2;
   logic                     y_ch0_dq1_dfi_wck_oe_p3;
   logic                     y_ch0_dq1_dfi_wck_oe_p4;
   logic                     y_ch0_dq1_dfi_wck_oe_p5;
   logic                     y_ch0_dq1_dfi_wck_oe_p6;
   logic                     y_ch0_dq1_dfi_wck_oe_p7;
   logic                     y_ch0_dq1_dfi_wck_cs_p0;
   logic                     y_ch0_dq1_dfi_wck_cs_p1;
   logic                     y_ch0_dq1_dfi_wck_cs_p2;
   logic                     y_ch0_dq1_dfi_wck_cs_p3;
   logic                     y_ch0_dq1_dfi_wck_cs_p4;
   logic                     y_ch0_dq1_dfi_wck_cs_p5;
   logic                     y_ch0_dq1_dfi_wck_cs_p6;
   logic                     y_ch0_dq1_dfi_wck_cs_p7;
   logic                     y_ch0_dq1_dfi_wck_ten_p0;
   logic                     y_ch0_dq1_dfi_wck_ten_p1;
   logic                     y_ch0_dq1_dfi_wck_ten_p2;
   logic                     y_ch0_dq1_dfi_wck_ten_p3;
   logic                     y_ch0_dq1_dfi_wck_ten_p4;
   logic                     y_ch0_dq1_dfi_wck_ten_p5;
   logic                     y_ch0_dq1_dfi_wck_ten_p6;
   logic                     y_ch0_dq1_dfi_wck_ten_p7;
    logic                    y_ch0_dq1_dfi_rddata_cs_p0;
    logic                    y_ch0_dq1_dfi_rddata_cs_p1;
    logic                    y_ch0_dq1_dfi_rddata_cs_p2;
    logic                    y_ch0_dq1_dfi_rddata_cs_p3;
    logic                    y_ch0_dq1_dfi_rddata_cs_p4;
    logic                    y_ch0_dq1_dfi_rddata_cs_p5;
    logic                    y_ch0_dq1_dfi_rddata_cs_p6;
    logic                    y_ch0_dq1_dfi_rddata_cs_p7;
    logic                    y_ch0_dq1_dfi_rddata_en_p0;
    logic                    y_ch0_dq1_dfi_rddata_en_p1;
    logic                    y_ch0_dq1_dfi_rddata_en_p2;
    logic                    y_ch0_dq1_dfi_rddata_en_p3;
    logic                    y_ch0_dq1_dfi_rddata_en_p4;
    logic                    y_ch0_dq1_dfi_rddata_en_p5;
    logic                    y_ch0_dq1_dfi_rddata_en_p6;
    logic                    y_ch0_dq1_dfi_rddata_en_p7;
    logic                    y_ch0_dq1_dfi_rddata_ie_p0;
    logic                    y_ch0_dq1_dfi_rddata_ie_p1;
    logic                    y_ch0_dq1_dfi_rddata_ie_p2;
    logic                    y_ch0_dq1_dfi_rddata_ie_p3;
    logic                    y_ch0_dq1_dfi_rddata_ie_p4;
    logic                    y_ch0_dq1_dfi_rddata_ie_p5;
    logic                    y_ch0_dq1_dfi_rddata_ie_p6;
    logic                    y_ch0_dq1_dfi_rddata_ie_p7;
    logic                    y_ch0_dq1_dfi_rddata_re_p0;
    logic                    y_ch0_dq1_dfi_rddata_re_p1;
    logic                    y_ch0_dq1_dfi_rddata_re_p2;
    logic                    y_ch0_dq1_dfi_rddata_re_p3;
    logic                    y_ch0_dq1_dfi_rddata_re_p4;
    logic                    y_ch0_dq1_dfi_rddata_re_p5;
    logic                    y_ch0_dq1_dfi_rddata_re_p6;
    logic                    y_ch0_dq1_dfi_rddata_re_p7;

   logic [AWIDTH-1:0]         y_ch0_dfi_address_w0;
   logic [AWIDTH-1:0]         y_ch0_dfi_address_w1;
   logic [AWIDTH-1:0]         y_ch0_dfi_address_w2;
   logic [AWIDTH-1:0]         y_ch0_dfi_address_w3;
   logic [AWIDTH-1:0]         y_ch0_dfi_address_w4;
   logic [AWIDTH-1:0]         y_ch0_dfi_address_w5;
   logic [AWIDTH-1:0]         y_ch0_dfi_address_w6;
   logic [AWIDTH-1:0]         y_ch0_dfi_address_w7;
   logic [1:0]                y_ch0_dfi_cs_w0;
   logic [1:0]                y_ch0_dfi_cs_w1;
   logic [1:0]                y_ch0_dfi_cs_w2;
   logic [1:0]                y_ch0_dfi_cs_w3;
   logic [1:0]                y_ch0_dfi_cs_w4;
   logic [1:0]                y_ch0_dfi_cs_w5;
   logic [1:0]                y_ch0_dfi_cs_w6;
   logic [1:0]                y_ch0_dfi_cs_w7;
   logic [1:0]                y_ch0_dfi_cke_w0;
   logic [1:0]                y_ch0_dfi_cke_w1;
   logic [1:0]                y_ch0_dfi_cke_w2;
   logic [1:0]                y_ch0_dfi_cke_w3;
   logic [1:0]                y_ch0_dfi_cke_w4;
   logic [1:0]                y_ch0_dfi_cke_w5;
   logic [1:0]                y_ch0_dfi_cke_w6;
   logic [1:0]                y_ch0_dfi_cke_w7;
   logic [CA_WIDTH-1:0]       y_ch0_dfi_address_valid;

   logic [SWIDTH-1:0]         y_ch0_dq0_dfi_rddata_w0;
   logic [SWIDTH-1:0]         y_ch0_dq0_dfi_rddata_w1;
   logic [SWIDTH-1:0]         y_ch0_dq0_dfi_rddata_w2;
   logic [SWIDTH-1:0]         y_ch0_dq0_dfi_rddata_w3;
   logic [SWIDTH-1:0]         y_ch0_dq0_dfi_rddata_w4;
   logic [SWIDTH-1:0]         y_ch0_dq0_dfi_rddata_w5;
   logic [SWIDTH-1:0]         y_ch0_dq0_dfi_rddata_w6;
   logic [SWIDTH-1:0]         y_ch0_dq0_dfi_rddata_w7;
   logic [MWIDTH-1:0]         y_ch0_dq0_dfi_rddata_dbi_w0;
   logic [MWIDTH-1:0]         y_ch0_dq0_dfi_rddata_dbi_w1;
   logic [MWIDTH-1:0]         y_ch0_dq0_dfi_rddata_dbi_w2;
   logic [MWIDTH-1:0]         y_ch0_dq0_dfi_rddata_dbi_w3;
   logic [MWIDTH-1:0]         y_ch0_dq0_dfi_rddata_dbi_w4;
   logic [MWIDTH-1:0]         y_ch0_dq0_dfi_rddata_dbi_w5;
   logic [MWIDTH-1:0]         y_ch0_dq0_dfi_rddata_dbi_w6;
   logic [MWIDTH-1:0]         y_ch0_dq0_dfi_rddata_dbi_w7;
   logic [SWIDTH-1:0]         y_ch0_dq0_dfi_rddata_valid;
   logic [SWIDTH-1:0]         y_ch0_dq1_dfi_rddata_w0;
   logic [SWIDTH-1:0]         y_ch0_dq1_dfi_rddata_w1;
   logic [SWIDTH-1:0]         y_ch0_dq1_dfi_rddata_w2;
   logic [SWIDTH-1:0]         y_ch0_dq1_dfi_rddata_w3;
   logic [SWIDTH-1:0]         y_ch0_dq1_dfi_rddata_w4;
   logic [SWIDTH-1:0]         y_ch0_dq1_dfi_rddata_w5;
   logic [SWIDTH-1:0]         y_ch0_dq1_dfi_rddata_w6;
   logic [SWIDTH-1:0]         y_ch0_dq1_dfi_rddata_w7;
   logic [MWIDTH-1:0]         y_ch0_dq1_dfi_rddata_dbi_w0;
   logic [MWIDTH-1:0]         y_ch0_dq1_dfi_rddata_dbi_w1;
   logic [MWIDTH-1:0]         y_ch0_dq1_dfi_rddata_dbi_w2;
   logic [MWIDTH-1:0]         y_ch0_dq1_dfi_rddata_dbi_w3;
   logic [MWIDTH-1:0]         y_ch0_dq1_dfi_rddata_dbi_w4;
   logic [MWIDTH-1:0]         y_ch0_dq1_dfi_rddata_dbi_w5;
   logic [MWIDTH-1:0]         y_ch0_dq1_dfi_rddata_dbi_w6;
   logic [MWIDTH-1:0]         y_ch0_dq1_dfi_rddata_dbi_w7;
   logic [SWIDTH-1:0]         y_ch0_dq1_dfi_rddata_valid;

   logic [AWIDTH-1:0]        y_ch1_dfi_address_p0;
   logic [AWIDTH-1:0]        y_ch1_dfi_address_p1;
   logic [AWIDTH-1:0]        y_ch1_dfi_address_p2;
   logic [AWIDTH-1:0]        y_ch1_dfi_address_p3;
   logic [AWIDTH-1:0]        y_ch1_dfi_address_p4;
   logic [AWIDTH-1:0]        y_ch1_dfi_address_p5;
   logic [AWIDTH-1:0]        y_ch1_dfi_address_p6;
   logic [AWIDTH-1:0]        y_ch1_dfi_address_p7;
   logic [1:0]               y_ch1_dfi_cke_p0;
   logic [1:0]               y_ch1_dfi_cke_p1;
   logic [1:0]               y_ch1_dfi_cke_p2;
   logic [1:0]               y_ch1_dfi_cke_p3;
   logic [1:0]               y_ch1_dfi_cke_p4;
   logic [1:0]               y_ch1_dfi_cke_p5;
   logic [1:0]               y_ch1_dfi_cke_p6;
   logic [1:0]               y_ch1_dfi_cke_p7;
   logic [1:0]               y_ch1_dfi_cs_p0;
   logic [1:0]               y_ch1_dfi_cs_p1;
   logic [1:0]               y_ch1_dfi_cs_p2;
   logic [1:0]               y_ch1_dfi_cs_p3;
   logic [1:0]               y_ch1_dfi_cs_p4;
   logic [1:0]               y_ch1_dfi_cs_p5;
   logic [1:0]               y_ch1_dfi_cs_p6;
   logic [1:0]               y_ch1_dfi_cs_p7;
   logic                     y_ch1_dfi_carddata_en_p0;
   logic                     y_ch1_dfi_carddata_en_p1;
   logic                     y_ch1_dfi_carddata_en_p2;
   logic                     y_ch1_dfi_carddata_en_p3;
   logic                     y_ch1_dfi_carddata_en_p4;
   logic                     y_ch1_dfi_carddata_en_p5;
   logic                     y_ch1_dfi_carddata_en_p6;
   logic                     y_ch1_dfi_carddata_en_p7;
   logic                     y_ch1_dfi_dram_clk_disable_p0;
   logic                     y_ch1_dfi_dram_clk_disable_p1;
   logic                     y_ch1_dfi_dram_clk_disable_p2;
   logic                     y_ch1_dfi_dram_clk_disable_p3;
   logic                     y_ch1_dfi_dram_clk_disable_p4;
   logic                     y_ch1_dfi_dram_clk_disable_p5;
   logic                     y_ch1_dfi_dram_clk_disable_p6;
   logic                     y_ch1_dfi_dram_clk_disable_p7;
   logic                     y_ch1_dfi_dram_clk_enable_p0;
   logic                     y_ch1_dfi_dram_clk_enable_p1;
   logic                     y_ch1_dfi_dram_clk_enable_p2;
   logic                     y_ch1_dfi_dram_clk_enable_p3;
   logic                     y_ch1_dfi_dram_clk_enable_p4;
   logic                     y_ch1_dfi_dram_clk_enable_p5;
   logic                     y_ch1_dfi_dram_clk_enable_p6;
   logic                     y_ch1_dfi_dram_clk_enable_p7;
   logic [SWIDTH-1:0]        y_ch1_dq0_dfi_wrdata_p0;
   logic [SWIDTH-1:0]        y_ch1_dq0_dfi_wrdata_p1;
   logic [SWIDTH-1:0]        y_ch1_dq0_dfi_wrdata_p2;
   logic [SWIDTH-1:0]        y_ch1_dq0_dfi_wrdata_p3;
   logic [SWIDTH-1:0]        y_ch1_dq0_dfi_wrdata_p4;
   logic [SWIDTH-1:0]        y_ch1_dq0_dfi_wrdata_p5;
   logic [SWIDTH-1:0]        y_ch1_dq0_dfi_wrdata_p6;
   logic [SWIDTH-1:0]        y_ch1_dq0_dfi_wrdata_p7;
   logic [MWIDTH-1:0]        y_ch1_dq0_dfi_wrdata_mask_p0;
   logic [MWIDTH-1:0]        y_ch1_dq0_dfi_wrdata_mask_p1;
   logic [MWIDTH-1:0]        y_ch1_dq0_dfi_wrdata_mask_p2;
   logic [MWIDTH-1:0]        y_ch1_dq0_dfi_wrdata_mask_p3;
   logic [MWIDTH-1:0]        y_ch1_dq0_dfi_wrdata_mask_p4;
   logic [MWIDTH-1:0]        y_ch1_dq0_dfi_wrdata_mask_p5;
   logic [MWIDTH-1:0]        y_ch1_dq0_dfi_wrdata_mask_p6;
   logic [MWIDTH-1:0]        y_ch1_dq0_dfi_wrdata_mask_p7;
    logic                    y_ch1_dq0_dfi_parity_in_p0;
    logic                    y_ch1_dq0_dfi_parity_in_p1;
    logic                    y_ch1_dq0_dfi_parity_in_p2;
    logic                    y_ch1_dq0_dfi_parity_in_p3;
    logic                    y_ch1_dq0_dfi_parity_in_p4;
    logic                    y_ch1_dq0_dfi_parity_in_p5;
    logic                    y_ch1_dq0_dfi_parity_in_p6;
    logic                    y_ch1_dq0_dfi_parity_in_p7;
   logic                     y_ch1_dq0_dfi_wrdata_cs_p0;
   logic                     y_ch1_dq0_dfi_wrdata_cs_p1;
   logic                     y_ch1_dq0_dfi_wrdata_cs_p2;
   logic                     y_ch1_dq0_dfi_wrdata_cs_p3;
   logic                     y_ch1_dq0_dfi_wrdata_cs_p4;
   logic                     y_ch1_dq0_dfi_wrdata_cs_p5;
   logic                     y_ch1_dq0_dfi_wrdata_cs_p6;
   logic                     y_ch1_dq0_dfi_wrdata_cs_p7;
   logic                     y_ch1_dq0_dfi_wrdata_en_p0;
   logic                     y_ch1_dq0_dfi_wrdata_en_p1;
   logic                     y_ch1_dq0_dfi_wrdata_en_p2;
   logic                     y_ch1_dq0_dfi_wrdata_en_p3;
   logic                     y_ch1_dq0_dfi_wrdata_en_p4;
   logic                     y_ch1_dq0_dfi_wrdata_en_p5;
   logic                     y_ch1_dq0_dfi_wrdata_en_p6;
   logic                     y_ch1_dq0_dfi_wrdata_en_p7;
   logic                     y_ch1_dq0_dfi_wrdata_oe_p0;
   logic                     y_ch1_dq0_dfi_wrdata_oe_p1;
   logic                     y_ch1_dq0_dfi_wrdata_oe_p2;
   logic                     y_ch1_dq0_dfi_wrdata_oe_p3;
   logic                     y_ch1_dq0_dfi_wrdata_oe_p4;
   logic                     y_ch1_dq0_dfi_wrdata_oe_p5;
   logic                     y_ch1_dq0_dfi_wrdata_oe_p6;
   logic                     y_ch1_dq0_dfi_wrdata_oe_p7;
   logic                     y_ch1_dq0_dfi_wck_en_p0;
   logic                     y_ch1_dq0_dfi_wck_en_p1;
   logic                     y_ch1_dq0_dfi_wck_en_p2;
   logic                     y_ch1_dq0_dfi_wck_en_p3;
   logic                     y_ch1_dq0_dfi_wck_en_p4;
   logic                     y_ch1_dq0_dfi_wck_en_p5;
   logic                     y_ch1_dq0_dfi_wck_en_p6;
   logic                     y_ch1_dq0_dfi_wck_en_p7;
   logic                     y_ch1_dq0_dfi_wck_oe_p0;
   logic                     y_ch1_dq0_dfi_wck_oe_p1;
   logic                     y_ch1_dq0_dfi_wck_oe_p2;
   logic                     y_ch1_dq0_dfi_wck_oe_p3;
   logic                     y_ch1_dq0_dfi_wck_oe_p4;
   logic                     y_ch1_dq0_dfi_wck_oe_p5;
   logic                     y_ch1_dq0_dfi_wck_oe_p6;
   logic                     y_ch1_dq0_dfi_wck_oe_p7;
   logic                     y_ch1_dq0_dfi_wck_cs_p0;
   logic                     y_ch1_dq0_dfi_wck_cs_p1;
   logic                     y_ch1_dq0_dfi_wck_cs_p2;
   logic                     y_ch1_dq0_dfi_wck_cs_p3;
   logic                     y_ch1_dq0_dfi_wck_cs_p4;
   logic                     y_ch1_dq0_dfi_wck_cs_p5;
   logic                     y_ch1_dq0_dfi_wck_cs_p6;
   logic                     y_ch1_dq0_dfi_wck_cs_p7;
   logic                     y_ch1_dq0_dfi_wck_ten_p0;
   logic                     y_ch1_dq0_dfi_wck_ten_p1;
   logic                     y_ch1_dq0_dfi_wck_ten_p2;
   logic                     y_ch1_dq0_dfi_wck_ten_p3;
   logic                     y_ch1_dq0_dfi_wck_ten_p4;
   logic                     y_ch1_dq0_dfi_wck_ten_p5;
   logic                     y_ch1_dq0_dfi_wck_ten_p6;
   logic                     y_ch1_dq0_dfi_wck_ten_p7;
    logic                    y_ch1_dq0_dfi_rddata_cs_p0;
    logic                    y_ch1_dq0_dfi_rddata_cs_p1;
    logic                    y_ch1_dq0_dfi_rddata_cs_p2;
    logic                    y_ch1_dq0_dfi_rddata_cs_p3;
    logic                    y_ch1_dq0_dfi_rddata_cs_p4;
    logic                    y_ch1_dq0_dfi_rddata_cs_p5;
    logic                    y_ch1_dq0_dfi_rddata_cs_p6;
    logic                    y_ch1_dq0_dfi_rddata_cs_p7;
    logic                    y_ch1_dq0_dfi_rddata_en_p0;
    logic                    y_ch1_dq0_dfi_rddata_en_p1;
    logic                    y_ch1_dq0_dfi_rddata_en_p2;
    logic                    y_ch1_dq0_dfi_rddata_en_p3;
    logic                    y_ch1_dq0_dfi_rddata_en_p4;
    logic                    y_ch1_dq0_dfi_rddata_en_p5;
    logic                    y_ch1_dq0_dfi_rddata_en_p6;
    logic                    y_ch1_dq0_dfi_rddata_en_p7;
    logic                    y_ch1_dq0_dfi_rddata_ie_p0;
    logic                    y_ch1_dq0_dfi_rddata_ie_p1;
    logic                    y_ch1_dq0_dfi_rddata_ie_p2;
    logic                    y_ch1_dq0_dfi_rddata_ie_p3;
    logic                    y_ch1_dq0_dfi_rddata_ie_p4;
    logic                    y_ch1_dq0_dfi_rddata_ie_p5;
    logic                    y_ch1_dq0_dfi_rddata_ie_p6;
    logic                    y_ch1_dq0_dfi_rddata_ie_p7;
    logic                    y_ch1_dq0_dfi_rddata_re_p0;
    logic                    y_ch1_dq0_dfi_rddata_re_p1;
    logic                    y_ch1_dq0_dfi_rddata_re_p2;
    logic                    y_ch1_dq0_dfi_rddata_re_p3;
    logic                    y_ch1_dq0_dfi_rddata_re_p4;
    logic                    y_ch1_dq0_dfi_rddata_re_p5;
    logic                    y_ch1_dq0_dfi_rddata_re_p6;
    logic                    y_ch1_dq0_dfi_rddata_re_p7;
   logic [SWIDTH-1:0]        y_ch1_dq1_dfi_wrdata_p0;
   logic [SWIDTH-1:0]        y_ch1_dq1_dfi_wrdata_p1;
   logic [SWIDTH-1:0]        y_ch1_dq1_dfi_wrdata_p2;
   logic [SWIDTH-1:0]        y_ch1_dq1_dfi_wrdata_p3;
   logic [SWIDTH-1:0]        y_ch1_dq1_dfi_wrdata_p4;
   logic [SWIDTH-1:0]        y_ch1_dq1_dfi_wrdata_p5;
   logic [SWIDTH-1:0]        y_ch1_dq1_dfi_wrdata_p6;
   logic [SWIDTH-1:0]        y_ch1_dq1_dfi_wrdata_p7;
   logic [MWIDTH-1:0]        y_ch1_dq1_dfi_wrdata_mask_p0;
   logic [MWIDTH-1:0]        y_ch1_dq1_dfi_wrdata_mask_p1;
   logic [MWIDTH-1:0]        y_ch1_dq1_dfi_wrdata_mask_p2;
   logic [MWIDTH-1:0]        y_ch1_dq1_dfi_wrdata_mask_p3;
   logic [MWIDTH-1:0]        y_ch1_dq1_dfi_wrdata_mask_p4;
   logic [MWIDTH-1:0]        y_ch1_dq1_dfi_wrdata_mask_p5;
   logic [MWIDTH-1:0]        y_ch1_dq1_dfi_wrdata_mask_p6;
   logic [MWIDTH-1:0]        y_ch1_dq1_dfi_wrdata_mask_p7;
    logic                    y_ch1_dq1_dfi_parity_in_p0;
    logic                    y_ch1_dq1_dfi_parity_in_p1;
    logic                    y_ch1_dq1_dfi_parity_in_p2;
    logic                    y_ch1_dq1_dfi_parity_in_p3;
    logic                    y_ch1_dq1_dfi_parity_in_p4;
    logic                    y_ch1_dq1_dfi_parity_in_p5;
    logic                    y_ch1_dq1_dfi_parity_in_p6;
    logic                    y_ch1_dq1_dfi_parity_in_p7;
   logic                     y_ch1_dq1_dfi_wrdata_cs_p0;
   logic                     y_ch1_dq1_dfi_wrdata_cs_p1;
   logic                     y_ch1_dq1_dfi_wrdata_cs_p2;
   logic                     y_ch1_dq1_dfi_wrdata_cs_p3;
   logic                     y_ch1_dq1_dfi_wrdata_cs_p4;
   logic                     y_ch1_dq1_dfi_wrdata_cs_p5;
   logic                     y_ch1_dq1_dfi_wrdata_cs_p6;
   logic                     y_ch1_dq1_dfi_wrdata_cs_p7;
   logic                     y_ch1_dq1_dfi_wrdata_en_p0;
   logic                     y_ch1_dq1_dfi_wrdata_en_p1;
   logic                     y_ch1_dq1_dfi_wrdata_en_p2;
   logic                     y_ch1_dq1_dfi_wrdata_en_p3;
   logic                     y_ch1_dq1_dfi_wrdata_en_p4;
   logic                     y_ch1_dq1_dfi_wrdata_en_p5;
   logic                     y_ch1_dq1_dfi_wrdata_en_p6;
   logic                     y_ch1_dq1_dfi_wrdata_en_p7;
   logic                     y_ch1_dq1_dfi_wrdata_oe_p0;
   logic                     y_ch1_dq1_dfi_wrdata_oe_p1;
   logic                     y_ch1_dq1_dfi_wrdata_oe_p2;
   logic                     y_ch1_dq1_dfi_wrdata_oe_p3;
   logic                     y_ch1_dq1_dfi_wrdata_oe_p4;
   logic                     y_ch1_dq1_dfi_wrdata_oe_p5;
   logic                     y_ch1_dq1_dfi_wrdata_oe_p6;
   logic                     y_ch1_dq1_dfi_wrdata_oe_p7;
   logic                     y_ch1_dq1_dfi_wck_en_p0;
   logic                     y_ch1_dq1_dfi_wck_en_p1;
   logic                     y_ch1_dq1_dfi_wck_en_p2;
   logic                     y_ch1_dq1_dfi_wck_en_p3;
   logic                     y_ch1_dq1_dfi_wck_en_p4;
   logic                     y_ch1_dq1_dfi_wck_en_p5;
   logic                     y_ch1_dq1_dfi_wck_en_p6;
   logic                     y_ch1_dq1_dfi_wck_en_p7;
   logic                     y_ch1_dq1_dfi_wck_oe_p0;
   logic                     y_ch1_dq1_dfi_wck_oe_p1;
   logic                     y_ch1_dq1_dfi_wck_oe_p2;
   logic                     y_ch1_dq1_dfi_wck_oe_p3;
   logic                     y_ch1_dq1_dfi_wck_oe_p4;
   logic                     y_ch1_dq1_dfi_wck_oe_p5;
   logic                     y_ch1_dq1_dfi_wck_oe_p6;
   logic                     y_ch1_dq1_dfi_wck_oe_p7;
   logic                     y_ch1_dq1_dfi_wck_cs_p0;
   logic                     y_ch1_dq1_dfi_wck_cs_p1;
   logic                     y_ch1_dq1_dfi_wck_cs_p2;
   logic                     y_ch1_dq1_dfi_wck_cs_p3;
   logic                     y_ch1_dq1_dfi_wck_cs_p4;
   logic                     y_ch1_dq1_dfi_wck_cs_p5;
   logic                     y_ch1_dq1_dfi_wck_cs_p6;
   logic                     y_ch1_dq1_dfi_wck_cs_p7;
   logic                     y_ch1_dq1_dfi_wck_ten_p0;
   logic                     y_ch1_dq1_dfi_wck_ten_p1;
   logic                     y_ch1_dq1_dfi_wck_ten_p2;
   logic                     y_ch1_dq1_dfi_wck_ten_p3;
   logic                     y_ch1_dq1_dfi_wck_ten_p4;
   logic                     y_ch1_dq1_dfi_wck_ten_p5;
   logic                     y_ch1_dq1_dfi_wck_ten_p6;
   logic                     y_ch1_dq1_dfi_wck_ten_p7;
    logic                    y_ch1_dq1_dfi_rddata_cs_p0;
    logic                    y_ch1_dq1_dfi_rddata_cs_p1;
    logic                    y_ch1_dq1_dfi_rddata_cs_p2;
    logic                    y_ch1_dq1_dfi_rddata_cs_p3;
    logic                    y_ch1_dq1_dfi_rddata_cs_p4;
    logic                    y_ch1_dq1_dfi_rddata_cs_p5;
    logic                    y_ch1_dq1_dfi_rddata_cs_p6;
    logic                    y_ch1_dq1_dfi_rddata_cs_p7;
    logic                    y_ch1_dq1_dfi_rddata_en_p0;
    logic                    y_ch1_dq1_dfi_rddata_en_p1;
    logic                    y_ch1_dq1_dfi_rddata_en_p2;
    logic                    y_ch1_dq1_dfi_rddata_en_p3;
    logic                    y_ch1_dq1_dfi_rddata_en_p4;
    logic                    y_ch1_dq1_dfi_rddata_en_p5;
    logic                    y_ch1_dq1_dfi_rddata_en_p6;
    logic                    y_ch1_dq1_dfi_rddata_en_p7;
    logic                    y_ch1_dq1_dfi_rddata_ie_p0;
    logic                    y_ch1_dq1_dfi_rddata_ie_p1;
    logic                    y_ch1_dq1_dfi_rddata_ie_p2;
    logic                    y_ch1_dq1_dfi_rddata_ie_p3;
    logic                    y_ch1_dq1_dfi_rddata_ie_p4;
    logic                    y_ch1_dq1_dfi_rddata_ie_p5;
    logic                    y_ch1_dq1_dfi_rddata_ie_p6;
    logic                    y_ch1_dq1_dfi_rddata_ie_p7;
    logic                    y_ch1_dq1_dfi_rddata_re_p0;
    logic                    y_ch1_dq1_dfi_rddata_re_p1;
    logic                    y_ch1_dq1_dfi_rddata_re_p2;
    logic                    y_ch1_dq1_dfi_rddata_re_p3;
    logic                    y_ch1_dq1_dfi_rddata_re_p4;
    logic                    y_ch1_dq1_dfi_rddata_re_p5;
    logic                    y_ch1_dq1_dfi_rddata_re_p6;
    logic                    y_ch1_dq1_dfi_rddata_re_p7;

   logic [AWIDTH-1:0]         y_ch1_dfi_address_w0;
   logic [AWIDTH-1:0]         y_ch1_dfi_address_w1;
   logic [AWIDTH-1:0]         y_ch1_dfi_address_w2;
   logic [AWIDTH-1:0]         y_ch1_dfi_address_w3;
   logic [AWIDTH-1:0]         y_ch1_dfi_address_w4;
   logic [AWIDTH-1:0]         y_ch1_dfi_address_w5;
   logic [AWIDTH-1:0]         y_ch1_dfi_address_w6;
   logic [AWIDTH-1:0]         y_ch1_dfi_address_w7;
   logic [1:0]                y_ch1_dfi_cs_w0;
   logic [1:0]                y_ch1_dfi_cs_w1;
   logic [1:0]                y_ch1_dfi_cs_w2;
   logic [1:0]                y_ch1_dfi_cs_w3;
   logic [1:0]                y_ch1_dfi_cs_w4;
   logic [1:0]                y_ch1_dfi_cs_w5;
   logic [1:0]                y_ch1_dfi_cs_w6;
   logic [1:0]                y_ch1_dfi_cs_w7;
   logic [1:0]                y_ch1_dfi_cke_w0;
   logic [1:0]                y_ch1_dfi_cke_w1;
   logic [1:0]                y_ch1_dfi_cke_w2;
   logic [1:0]                y_ch1_dfi_cke_w3;
   logic [1:0]                y_ch1_dfi_cke_w4;
   logic [1:0]                y_ch1_dfi_cke_w5;
   logic [1:0]                y_ch1_dfi_cke_w6;
   logic [1:0]                y_ch1_dfi_cke_w7;
   logic [CA_WIDTH-1:0]       y_ch1_dfi_address_valid;

   logic [SWIDTH-1:0]         y_ch1_dq0_dfi_rddata_w0;
   logic [SWIDTH-1:0]         y_ch1_dq0_dfi_rddata_w1;
   logic [SWIDTH-1:0]         y_ch1_dq0_dfi_rddata_w2;
   logic [SWIDTH-1:0]         y_ch1_dq0_dfi_rddata_w3;
   logic [SWIDTH-1:0]         y_ch1_dq0_dfi_rddata_w4;
   logic [SWIDTH-1:0]         y_ch1_dq0_dfi_rddata_w5;
   logic [SWIDTH-1:0]         y_ch1_dq0_dfi_rddata_w6;
   logic [SWIDTH-1:0]         y_ch1_dq0_dfi_rddata_w7;
   logic [MWIDTH-1:0]         y_ch1_dq0_dfi_rddata_dbi_w0;
   logic [MWIDTH-1:0]         y_ch1_dq0_dfi_rddata_dbi_w1;
   logic [MWIDTH-1:0]         y_ch1_dq0_dfi_rddata_dbi_w2;
   logic [MWIDTH-1:0]         y_ch1_dq0_dfi_rddata_dbi_w3;
   logic [MWIDTH-1:0]         y_ch1_dq0_dfi_rddata_dbi_w4;
   logic [MWIDTH-1:0]         y_ch1_dq0_dfi_rddata_dbi_w5;
   logic [MWIDTH-1:0]         y_ch1_dq0_dfi_rddata_dbi_w6;
   logic [MWIDTH-1:0]         y_ch1_dq0_dfi_rddata_dbi_w7;
   logic [SWIDTH-1:0]         y_ch1_dq0_dfi_rddata_valid;
   logic [SWIDTH-1:0]         y_ch1_dq1_dfi_rddata_w0;
   logic [SWIDTH-1:0]         y_ch1_dq1_dfi_rddata_w1;
   logic [SWIDTH-1:0]         y_ch1_dq1_dfi_rddata_w2;
   logic [SWIDTH-1:0]         y_ch1_dq1_dfi_rddata_w3;
   logic [SWIDTH-1:0]         y_ch1_dq1_dfi_rddata_w4;
   logic [SWIDTH-1:0]         y_ch1_dq1_dfi_rddata_w5;
   logic [SWIDTH-1:0]         y_ch1_dq1_dfi_rddata_w6;
   logic [SWIDTH-1:0]         y_ch1_dq1_dfi_rddata_w7;
   logic [MWIDTH-1:0]         y_ch1_dq1_dfi_rddata_dbi_w0;
   logic [MWIDTH-1:0]         y_ch1_dq1_dfi_rddata_dbi_w1;
   logic [MWIDTH-1:0]         y_ch1_dq1_dfi_rddata_dbi_w2;
   logic [MWIDTH-1:0]         y_ch1_dq1_dfi_rddata_dbi_w3;
   logic [MWIDTH-1:0]         y_ch1_dq1_dfi_rddata_dbi_w4;
   logic [MWIDTH-1:0]         y_ch1_dq1_dfi_rddata_dbi_w5;
   logic [MWIDTH-1:0]         y_ch1_dq1_dfi_rddata_dbi_w6;
   logic [MWIDTH-1:0]         y_ch1_dq1_dfi_rddata_dbi_w7;
   logic [SWIDTH-1:0]         y_ch1_dq1_dfi_rddata_valid;


   logic [31:0] dfich0_dfibuf_debug ;
   logic [31:0] ch0_dpca_debug ;
   logic [31:0] ch0_dpdqwr_debug ;
   logic [31:0] ch0_dpdqrd_debug ;
   logic [31:0] ch1_dpca_debug ;
   logic [31:0] ch1_dpdqwr_debug ;
   logic [31:0] ch1_dpdqrd_debug ;
   logic [31:0] ctrl_debug;
   logic [3:0] debug_bus_sel ;

   assign o_debug = (debug_bus_sel == 4'd0) ? 32'b0 :
                    (debug_bus_sel == 4'd8) ? ctrl_debug :
                    (debug_bus_sel[3] == 1'b0) && (debug_bus_sel[2:0] == 3'd1 ) ? ch0_dpdqwr_debug :
                    (debug_bus_sel[3] == 1'b0) && (debug_bus_sel[2:0] == 3'd2 ) ? ch0_dpdqrd_debug :
                    (debug_bus_sel[3] == 1'b0) && (debug_bus_sel[2:0] == 3'd3 ) ? ch0_dpca_debug   :
                    (debug_bus_sel[3] == 1'b0) && (debug_bus_sel[2:0] == 3'd4 ) ? ch1_dpdqwr_debug :
                    (debug_bus_sel[3] == 1'b0) && (debug_bus_sel[2:0] == 3'd5 ) ? ch1_dpdqrd_debug :
                    (debug_bus_sel[3] == 1'b0) && (debug_bus_sel[2:0] == 3'd6 ) ? ch1_dpca_debug   :
                    (debug_bus_sel[3] == 1'b0) && (debug_bus_sel[2:0] == 3'd7 ) ? dfich0_dfibuf_debug :
                    32'b0 ;

   // ------------------------------------------------------------------------
   // CSR
   // ------------------------------------------------------------------------

   logic [`DDR_DFI_TOP_0_CFG_RANGE]      dfi_top_0_cfg;
   logic [`DDR_DFI_STATUS_IF_CFG_RANGE]  dfi_status_if_cfg;
   logic [`DDR_DFI_STATUS_IF_STA_RANGE]  dfi_status_if_sta;
   logic [`DDR_DFI_STATUS_IF_EVENT_0_CFG_RANGE] dfi_status_if_event_0_cfg;
   logic [`DDR_DFI_STATUS_IF_EVENT_1_CFG_RANGE] dfi_status_if_event_1_cfg;
   logic [`DDR_DFI_CTRLUPD_IF_CFG_RANGE] dfi_ctrlupd_if_cfg;
   logic [`DDR_DFI_CTRLUPD_IF_STA_RANGE] dfi_ctrlupd_if_sta;
   logic [`DDR_DFI_CTRLUPD_IF_EVENT_0_CFG_RANGE] dfi_ctrlupd_if_event_0_cfg;
   logic [`DDR_DFI_CTRLUPD_IF_EVENT_1_CFG_RANGE] dfi_ctrlupd_if_event_1_cfg;
   logic [`DDR_DFI_LP_CTRL_IF_CFG_RANGE] dfi_lp_ctrl_if_cfg;
   logic [`DDR_DFI_LP_CTRL_IF_STA_RANGE] dfi_lp_ctrl_if_sta;
   logic [`DDR_DFI_LP_CTRL_IF_EVENT_0_CFG_RANGE] dfi_lp_ctrl_if_event_0_cfg;
   logic [`DDR_DFI_LP_CTRL_IF_EVENT_1_CFG_RANGE] dfi_lp_ctrl_if_event_1_cfg;
   logic [`DDR_DFI_LP_DATA_IF_CFG_RANGE] dfi_lp_data_if_cfg;
   logic [`DDR_DFI_LP_DATA_IF_STA_RANGE] dfi_lp_data_if_sta;
   logic [`DDR_DFI_LP_DATA_IF_EVENT_0_CFG_RANGE] dfi_lp_data_if_event_0_cfg;
   logic [`DDR_DFI_LP_DATA_IF_EVENT_1_CFG_RANGE] dfi_lp_data_if_event_1_cfg;
   logic [`DDR_DFI_PHYUPD_IF_CFG_RANGE]  dfi_phyupd_if_cfg;
   logic [`DDR_DFI_PHYUPD_IF_STA_RANGE]  dfi_phyupd_if_sta;
   logic [`DDR_DFI_PHYMSTR_IF_CFG_RANGE] dfi_phymstr_if_cfg;
   logic [`DDR_DFI_PHYMSTR_IF_STA_RANGE] dfi_phymstr_if_sta;
   logic [`DDR_DFI_DEBUG_CFG_RANGE]      dfi_debug_cfg;
   logic [`DDR_DFICH_TOP_1_CFG_RANGE]      dfich0_top_1_cfg;
   logic [`DDR_DFICH_TOP_2_CFG_RANGE]      dfich0_top_2_cfg;
   logic [`DDR_DFICH_TOP_3_CFG_RANGE]      dfich0_top_3_cfg;
   logic [`DDR_DFICH_TOP_STA_RANGE]        dfich0_top_sta;
   logic [`DDR_DFICH_IG_DATA_CFG_RANGE]    dfich0_ig_data_cfg;
   logic [`DDR_DFICH_EG_DATA_STA_RANGE]    dfich0_eg_data_sta;
   logic [`DDR_DFICH_WRC_M0_CFG_RANGE]     dfich0_wrc_cfg;
   logic [`DDR_DFICH_WRCCTRL_M0_CFG_RANGE] dfich0_wrcctrl_cfg;
   logic [`DDR_DFICH_CKCTRL_M0_CFG_RANGE]  dfich0_ckctrl_cfg;
   logic [`DDR_DFICH_RDC_M0_CFG_RANGE]     dfich0_rdc_cfg;
   logic [`DDR_DFICH_RCTRL_M0_CFG_RANGE]   dfich0_rctrl_cfg;
   logic [`DDR_DFICH_WCTRL_M0_CFG_RANGE]   dfich0_wctrl_cfg;
   logic [`DDR_DFICH_WENCTRL_M0_CFG_RANGE] dfich0_wenctrl_cfg;
   logic [`DDR_DFICH_WCKCTRL_M0_CFG_RANGE] dfich0_wckctrl_cfg;
   logic [`DDR_DFICH_WRD_M0_CFG_RANGE]     dfich0_wrd_cfg;
   logic [`DDR_DFICH_RDD_M0_CFG_RANGE]     dfich0_rdd_cfg;
   logic [`DDR_DFICH_CTRL0_M0_CFG_RANGE]   dfich0_ctrl0_cfg;
   logic [`DDR_DFICH_CTRL1_M0_CFG_RANGE]   dfich0_ctrl1_cfg;
   logic [`DDR_DFICH_CTRL2_M0_CFG_RANGE]   dfich0_ctrl2_cfg;
   logic [`DDR_DFICH_CTRL3_M0_CFG_RANGE]   dfich0_ctrl3_cfg;
   logic [`DDR_DFICH_CTRL4_M0_CFG_RANGE]   dfich0_ctrl4_cfg;
   logic [`DDR_DFICH_CTRL5_M0_CFG_RANGE]   dfich0_ctrl5_cfg;

   assign debug_bus_sel = dfi_debug_cfg[`DDR_DFI_DEBUG_CFG_DEBUG_BUS_SEL_FIELD] ;

   ddr_dfi_csr_wrapper #(
      .AWIDTH                       (AHB_AWIDTH),
      .DWIDTH                       (AHB_DWIDTH)
   ) u_dfi_csr_wrapper (
      .i_hclk                       (i_ahb_clk),
      .i_hreset                     (i_ahb_rst),
      .i_haddr                      (i_ahb_haddr),
      .i_hwrite                     (i_ahb_hwrite),
      .i_hsel                       (i_ahb_hsel),
      .i_hwdata                     (i_ahb_hwdata),
      .i_htrans                     (i_ahb_htrans),
      .i_hsize                      (i_ahb_hsize),
      .i_hburst                     (i_ahb_hburst),
      .i_hreadyin                   (i_ahb_hreadyin),
      .o_hready                     (o_ahb_hready),
      .o_hrdata                     (o_ahb_hrdata),
      .o_hresp                      (o_ahb_hresp),

      .i_msr                        (i_msr),

      .o_dfi_top_0_cfg              (dfi_top_0_cfg),
      .o_dfich0_top_1_cfg        (dfich0_top_1_cfg),
      .o_dfich0_top_2_cfg        (dfich0_top_2_cfg),
      .o_dfich0_top_3_cfg        (dfich0_top_3_cfg),
      .i_dfich0_top_sta          (dfich0_top_sta),
      .o_dfich0_ig_data_cfg      (dfich0_ig_data_cfg),
      .i_dfich0_eg_data_sta      (dfich0_eg_data_sta),
      .o_dfich0_wrc_cfg          (dfich0_wrc_cfg),
      .o_dfich0_wrcctrl_cfg      (dfich0_wrcctrl_cfg),
      .o_dfich0_ckctrl_cfg       (dfich0_ckctrl_cfg),
      .o_dfich0_rdc_cfg          (dfich0_rdc_cfg),
      .o_dfich0_rctrl_cfg        (dfich0_rctrl_cfg),
      .o_dfich0_wctrl_cfg        (dfich0_wctrl_cfg),
      .o_dfich0_wenctrl_cfg      (dfich0_wenctrl_cfg),
      .o_dfich0_wckctrl_cfg      (dfich0_wckctrl_cfg),
      .o_dfich0_wrd_cfg          (dfich0_wrd_cfg),
      .o_dfich0_rdd_cfg          (dfich0_rdd_cfg),
      .o_dfich0_ctrl4_cfg        (dfich0_ctrl4_cfg),
      .o_dfich0_ctrl5_cfg        (dfich0_ctrl5_cfg),
      .o_dfich0_ctrl0_cfg        (dfich0_ctrl0_cfg),
      .o_dfich0_ctrl1_cfg        (dfich0_ctrl1_cfg),
      .o_dfich0_ctrl2_cfg        (dfich0_ctrl2_cfg),
      .o_dfich0_ctrl3_cfg        (dfich0_ctrl3_cfg),
      .o_dfi_status_if_cfg          (dfi_status_if_cfg),
      .i_dfi_status_if_sta          (dfi_status_if_sta),
      .o_dfi_status_if_event_0_cfg  (dfi_status_if_event_0_cfg),
      .o_dfi_status_if_event_1_cfg  (dfi_status_if_event_1_cfg),
      .o_dfi_ctrlupd_if_cfg         (dfi_ctrlupd_if_cfg),
      .i_dfi_ctrlupd_if_sta         (dfi_ctrlupd_if_sta),
      .o_dfi_ctrlupd_if_event_0_cfg (dfi_ctrlupd_if_event_0_cfg),
      .o_dfi_ctrlupd_if_event_1_cfg (dfi_ctrlupd_if_event_1_cfg),
      .o_dfi_lp_ctrl_if_cfg         (dfi_lp_ctrl_if_cfg),
      .i_dfi_lp_ctrl_if_sta         (dfi_lp_ctrl_if_sta),
      .o_dfi_lp_ctrl_if_event_0_cfg (dfi_lp_ctrl_if_event_0_cfg),
      .o_dfi_lp_ctrl_if_event_1_cfg (dfi_lp_ctrl_if_event_1_cfg),
      .o_dfi_lp_data_if_cfg         (dfi_lp_data_if_cfg),
      .i_dfi_lp_data_if_sta         (dfi_lp_data_if_sta),
      .o_dfi_lp_data_if_event_0_cfg (dfi_lp_data_if_event_0_cfg),
      .o_dfi_lp_data_if_event_1_cfg (dfi_lp_data_if_event_1_cfg),
      .o_dfi_phyupd_if_cfg          (dfi_phyupd_if_cfg),
      .i_dfi_phyupd_if_sta          (dfi_phyupd_if_sta),
      .o_dfi_phymstr_if_cfg         (dfi_phymstr_if_cfg),
      .i_dfi_phymstr_if_sta         (dfi_phymstr_if_sta),
      .o_dfi_debug_cfg              (dfi_debug_cfg)
   );

   // ------------------------------------------------------------------------
   // DFI Control Interface
   // ------------------------------------------------------------------------
   ddr_dfi_ctrl #(
     .SIWIDTH (SIWIDTH)
   ) u_dfi_ctrl (
      .i_clk                        (o_dfi_clk),
      .i_rst                        (i_rst),

      .i_dfi_freq_fsp               (i_dfi_freq_fsp  ),
      .i_dfi_freq_ratio             (i_dfi_freq_ratio),
      .i_dfi_frequency              (i_dfi_frequency ),
      .i_dfi_init_start             (i_dfi_init_start),
      .o_dfi_init_complete          (o_dfi_init_complete),
      .o_irq_dfi_init_complete      (o_irq_dfi_init_complete),
      .o_dfi_init_start             (o_dfi_init_start),
      .i_init_complete              (i_init_complete),
      .i_dfi_status_if_cfg          (dfi_status_if_cfg),
      .o_dfi_status_if_sta          (dfi_status_if_sta),
      .i_dfi_status_if_event_0_cfg  (dfi_status_if_event_0_cfg),
      .i_dfi_status_if_event_1_cfg  (dfi_status_if_event_1_cfg),

      .i_dfi_ctrlupd_req            (i_dfi_ctrlupd_req),
      .o_dfi_ctrlupd_req            (o_dfi_ctrlupd_req),
      .o_dfi_ctrlupd_ack            (o_dfi_ctrlupd_ack),
      .i_dfi_ctrlupd_if_cfg         (dfi_ctrlupd_if_cfg),
      .o_dfi_ctrlupd_if_sta         (dfi_ctrlupd_if_sta),
      .i_dfi_ctrlupd_if_event_0_cfg (dfi_ctrlupd_if_event_0_cfg),
      .i_dfi_ctrlupd_if_event_1_cfg (dfi_ctrlupd_if_event_1_cfg),

      .i_dfi_lp_ctrl_req            (i_dfi_lp_ctrl_req),
      .i_dfi_lp_ctrl_wakeup         (i_dfi_lp_ctrl_wakeup),
      .o_dfi_lp_ctrl_req            (o_dfi_lp_ctrl_req),
      .o_dfi_lp_ctrl_ack            (o_dfi_lp_ctrl_ack),
      .i_dfi_lp_ctrl_if_cfg         (dfi_lp_ctrl_if_cfg),
      .o_dfi_lp_ctrl_if_sta         (dfi_lp_ctrl_if_sta),
      .i_dfi_lp_ctrl_if_event_0_cfg (dfi_lp_ctrl_if_event_0_cfg),
      .i_dfi_lp_ctrl_if_event_1_cfg (dfi_lp_ctrl_if_event_1_cfg),

      .i_dfi_lp_data_req            (i_dfi_lp_data_req),
      .i_dfi_lp_data_wakeup         (i_dfi_lp_data_wakeup),
      .o_dfi_lp_data_req            (o_dfi_lp_data_req),
      .o_dfi_lp_data_ack            (o_dfi_lp_data_ack),
      .i_dfi_lp_data_if_cfg         (dfi_lp_data_if_cfg),
      .o_dfi_lp_data_if_sta         (dfi_lp_data_if_sta),
      .i_dfi_lp_data_if_event_0_cfg (dfi_lp_data_if_event_0_cfg),
      .i_dfi_lp_data_if_event_1_cfg (dfi_lp_data_if_event_1_cfg),

      .o_dfi_phyupd_req             (o_dfi_phyupd_req),
      .i_dfi_phyupd_ack             (i_dfi_phyupd_ack),
      .o_dfi_phyupd_ack             (o_dfi_phyupd_ack),
      .o_dfi_phyupd_type            (o_dfi_phyupd_type),
      .i_dfi_phyupd_if_cfg          (dfi_phyupd_if_cfg),
      .o_dfi_phyupd_if_sta          (dfi_phyupd_if_sta),

      .o_dfi_phymstr_req            (o_dfi_phymstr_req),
      .i_dfi_phymstr_ack            (i_dfi_phymstr_ack),
      .o_dfi_phymstr_ack            (o_dfi_phymstr_ack),
      .o_dfi_phymstr_type           (o_dfi_phymstr_type),
      .o_dfi_phymstr_cs_state       (o_dfi_phymstr_cs_state),
      .o_dfi_phymstr_state_sel      (o_dfi_phymstr_state_sel),
      .i_dfi_phymstr_if_cfg         (dfi_phymstr_if_cfg),
      .o_dfi_phymstr_if_sta         (dfi_phymstr_if_sta),
      .o_debug                      (ctrl_debug)
   );

   // ------------------------------------------------------------------------
   // DFI Clock Control Interface
   // ------------------------------------------------------------------------
   dwgb_t                     dfi_wrgb_mode;
   drgb_t                     dfi_rdgb_mode;
   logic                      dfi_clk;
   logic                      dfidq_wrtraffic;
   logic                      dfidqs_wrtraffic;
   logic                      dfica_traffic;
   logic                      dfick_traffic;
   logic [DEC_DFIGBWIDTH-1:0] dfiwrgb_mode;
   logic [DEC_DFIGBWIDTH-1:0] dfirdgb_mode;
   logic [3:0]                dfirdclk_en_pulse_ext;

   logic cmda_clk_0   , cmdc_clk_0   , wrd_clk_0   , wrc_clk_0   ;
   logic cmda_clk_1   , cmdc_clk_1   , wrd_clk_1   , wrc_clk_1   , rd_clk_1  ;
   logic cmda_clk_2   , cmdc_clk_2   , wrd_clk_2   , wrc_clk_2   , rd_clk_2  ;
   logic dq_wrclk_en  , ca_clk_en ;
   logic dqs_wrclk_en , ck_clk_en ;

   assign dfi_wrgb_mode            = cast_dwgb_t(dfich0_wrd_cfg[`DDR_DFICH_WRD_M0_CFG_GB_MODE_FIELD]);
   assign dfi_rdgb_mode            = cast_drgb_t(dfich0_rdd_cfg[`DDR_DFICH_RDD_M0_CFG_GB_MODE_FIELD]);

   ddr_dfi_clk_ctrl #(
      .WR_PULSE_EXT_WIDTH           (`DDR_DFICH_CTRL2_M0_CFG_DQ_WRCLK_EN_PULSE_EXT_FIELD_WIDTH)
   ) u_dfi_clk_ctrl (
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_rst                        (i_rst),
      .i_phy_clk                    (i_ch0_phy_clk),
      .i_wr_clk_1                   (i_ch0_dfiwr_clk_1),
      .i_wr_clk_2                   (i_ch0_dfiwr_clk_2),

      .i_wrgb_mode                  (dfi_wrgb_mode),
      .i_rdgb_mode                  (dfi_rdgb_mode),
      .i_dq_wrclk_en                (dq_wrclk_en),
      .i_dqs_wrclk_en               (dqs_wrclk_en),
      .i_ca_clk_en                  (ca_clk_en),
      .i_ck_clk_en                  (ck_clk_en),
      .i_dqs_wrclk_en_pulse_ext     (dfich0_ctrl2_cfg[`DDR_DFICH_CTRL2_M0_CFG_DQS_WRCLK_EN_PULSE_EXT_FIELD]),
      .i_dq_wrclk_en_pulse_ext      (dfich0_ctrl2_cfg[`DDR_DFICH_CTRL2_M0_CFG_DQ_WRCLK_EN_PULSE_EXT_FIELD]),
      .i_ca_clk_en_pulse_ext        (dfich0_ctrl2_cfg[`DDR_DFICH_CTRL2_M0_CFG_CA_CLK_EN_PULSE_EXT_FIELD]),
      .i_ck_clk_en_pulse_ext        (dfich0_ctrl2_cfg[`DDR_DFICH_CTRL2_M0_CFG_CK_CLK_EN_PULSE_EXT_FIELD]),

      .i_dqs_wrtraffic_ovr_sel      (dfich0_ctrl1_cfg[`DDR_DFICH_CTRL1_M0_CFG_DQS_WRTRAFFIC_OVR_SEL_FIELD]),
      .i_dqs_wrtraffic_ovr          (dfich0_ctrl1_cfg[`DDR_DFICH_CTRL1_M0_CFG_DQS_WRTRAFFIC_OVR_FIELD]),
      .i_dq_wrtraffic_ovr_sel       (dfich0_ctrl1_cfg[`DDR_DFICH_CTRL1_M0_CFG_DQ_WRTRAFFIC_OVR_SEL_FIELD]),
      .i_dq_wrtraffic_ovr           (dfich0_ctrl1_cfg[`DDR_DFICH_CTRL1_M0_CFG_DQ_WRTRAFFIC_OVR_FIELD]),
      .i_ck_traffic_ovr_sel         (dfich0_ctrl1_cfg[`DDR_DFICH_CTRL1_M0_CFG_CK_TRAFFIC_OVR_SEL_FIELD]),
      .i_ck_traffic_ovr             (dfich0_ctrl1_cfg[`DDR_DFICH_CTRL1_M0_CFG_CK_TRAFFIC_OVR_FIELD]),
      .i_ca_traffic_ovr_sel         (dfich0_ctrl1_cfg[`DDR_DFICH_CTRL1_M0_CFG_CA_TRAFFIC_OVR_SEL_FIELD]),
      .i_ca_traffic_ovr             (dfich0_ctrl1_cfg[`DDR_DFICH_CTRL1_M0_CFG_CA_TRAFFIC_OVR_FIELD]),

      .o_dqs_wrtraffic              (dfidqs_wrtraffic),
      .o_dq_wrtraffic               (dfidq_wrtraffic),
      .o_ck_traffic                 (dfick_traffic),
      .o_ca_traffic                 (dfica_traffic),
      .o_dfiwrgb_mode               (dfiwrgb_mode),
      .o_dfirdgb_mode               (dfirdgb_mode),

      .o_wrd_clk_0                  (wrd_clk_0  ), // DIV1 of SDR clock
      .o_wrd_clk_1                  (wrd_clk_1  ), // DIV2 of SDR clock
      .o_wrd_clk_2                  (wrd_clk_2  ), // DIV4 of SDR clock
      .o_wrc_clk_0                  (wrc_clk_0  ), // DIV1 of SDR clock
      .o_wrc_clk_1                  (wrc_clk_1  ), // DIV2 of SDR clock
      .o_wrc_clk_2                  (wrc_clk_2  ), // DIV4 of SDR clock
      .o_cmda_clk_0                 (cmda_clk_0  ), // DIV1 of SDR clock
      .o_cmda_clk_1                 (cmda_clk_1  ), // DIV2 of SDR clock
      .o_cmda_clk_2                 (cmda_clk_2  ), // DIV4 of SDR clock
      .o_cmdc_clk_0                 (cmdc_clk_0  ), // DIV1 of SDR clock
      .o_cmdc_clk_1                 (cmdc_clk_1  ), // DIV2 of SDR clock
      .o_cmdc_clk_2                 (cmdc_clk_2  ), // DIV4 of SDR clock
      .o_dfi_clk                    (dfi_clk)
   );

      assign rd_clk_1                = i_ch0_dfird_clk_1  ;
      assign rd_clk_2                = i_ch0_dfird_clk_2  ;

      assign o_ch0_dfidq_wrtraffic     = dfidq_wrtraffic;
      assign o_ch0_dfidqs_wrtraffic    = dfidqs_wrtraffic;
      assign o_ch0_dfica_traffic       = dfica_traffic  ;
      assign o_ch0_dfick_traffic       = dfick_traffic  ;
      assign o_ch0_dfiwrgb_mode        = dfiwrgb_mode   ;
      assign o_ch0_dfirdgb_mode        = dfirdgb_mode   ;
      assign o_ch0_dfirdclk_en_pulse_ext = dfich0_ctrl2_cfg[`DDR_DFICH_CTRL2_M0_CFG_RDCLK_EN_PULSE_EXT_FIELD];
      assign o_ch0_dfirdclk_en_ovr_sel   = dfich0_ctrl1_cfg[`DDR_DFICH_CTRL1_M0_CFG_DQ_RDTRAFFIC_OVR_SEL_FIELD];
      assign o_ch0_dfirdclk_en_ovr       = dfich0_ctrl1_cfg[`DDR_DFICH_CTRL1_M0_CFG_DQ_RDTRAFFIC_OVR_FIELD];
      assign o_ch1_dfidq_wrtraffic     = dfidq_wrtraffic;
      assign o_ch1_dfidqs_wrtraffic    = dfidqs_wrtraffic;
      assign o_ch1_dfica_traffic       = dfica_traffic  ;
      assign o_ch1_dfick_traffic       = dfick_traffic  ;
      assign o_ch1_dfiwrgb_mode        = dfiwrgb_mode   ;
      assign o_ch1_dfirdgb_mode        = dfirdgb_mode   ;
      assign o_ch1_dfirdclk_en_pulse_ext = dfich0_ctrl2_cfg[`DDR_DFICH_CTRL2_M0_CFG_RDCLK_EN_PULSE_EXT_FIELD];
      assign o_ch1_dfirdclk_en_ovr_sel   = dfich0_ctrl1_cfg[`DDR_DFICH_CTRL1_M0_CFG_DQ_RDTRAFFIC_OVR_SEL_FIELD];
      assign o_ch1_dfirdclk_en_ovr       = dfich0_ctrl1_cfg[`DDR_DFICH_CTRL1_M0_CFG_DQ_RDTRAFFIC_OVR_FIELD];

      assign o_dfi_clk                      = dfi_clk ;

   // ------------------------------------------------------------------------
   // DFI Transaction Buffer
   // ------------------------------------------------------------------------

   logic                          dfi_rdout_en ;
   logic [NUM_DFI_DQ*SWIDTH-1:0]  dfi_rddata_w0;
   logic [NUM_DFI_DQ*MWIDTH-1:0]  dfi_rddata_dbi_w0;
   logic                          dfi_rddata_valid_w0;
   logic [NUM_DFI_DQ*SWIDTH-1:0]  dfi_rddata_w1;
   logic [NUM_DFI_DQ*MWIDTH-1:0]  dfi_rddata_dbi_w1;
   logic                          dfi_rddata_valid_w1;
   logic [NUM_DFI_DQ*SWIDTH-1:0]  dfi_rddata_w2;
   logic [NUM_DFI_DQ*MWIDTH-1:0]  dfi_rddata_dbi_w2;
   logic                          dfi_rddata_valid_w2;
   logic [NUM_DFI_DQ*SWIDTH-1:0]  dfi_rddata_w3;
   logic [NUM_DFI_DQ*MWIDTH-1:0]  dfi_rddata_dbi_w3;
   logic                          dfi_rddata_valid_w3;
   logic [NUM_DFI_DQ*SWIDTH-1:0]  dfi_rddata_w4;
   logic [NUM_DFI_DQ*MWIDTH-1:0]  dfi_rddata_dbi_w4;
   logic                          dfi_rddata_valid_w4;
   logic [NUM_DFI_DQ*SWIDTH-1:0]  dfi_rddata_w5;
   logic [NUM_DFI_DQ*MWIDTH-1:0]  dfi_rddata_dbi_w5;
   logic                          dfi_rddata_valid_w5;
   logic [NUM_DFI_DQ*SWIDTH-1:0]  dfi_rddata_w6;
   logic [NUM_DFI_DQ*MWIDTH-1:0]  dfi_rddata_dbi_w6;
   logic                          dfi_rddata_valid_w6;
   logic [NUM_DFI_DQ*SWIDTH-1:0]  dfi_rddata_w7;
   logic [NUM_DFI_DQ*MWIDTH-1:0]  dfi_rddata_dbi_w7;
   logic                          dfi_rddata_valid_w7;

   logic [NUM_DQ*SWIDTH-1:0]      ch0_dfi_rddata_w0;
   logic [NUM_DQ*MWIDTH-1:0]      ch0_dfi_rddata_dbi_w0;
   logic                          ch0_dfi_rddata_valid_w0;
   logic [NUM_DQ*SWIDTH-1:0]      ch0_dfi_rddata_w1;
   logic [NUM_DQ*MWIDTH-1:0]      ch0_dfi_rddata_dbi_w1;
   logic                          ch0_dfi_rddata_valid_w1;
   logic [NUM_DQ*SWIDTH-1:0]      ch0_dfi_rddata_w2;
   logic [NUM_DQ*MWIDTH-1:0]      ch0_dfi_rddata_dbi_w2;
   logic                          ch0_dfi_rddata_valid_w2;
   logic [NUM_DQ*SWIDTH-1:0]      ch0_dfi_rddata_w3;
   logic [NUM_DQ*MWIDTH-1:0]      ch0_dfi_rddata_dbi_w3;
   logic                          ch0_dfi_rddata_valid_w3;
   logic [NUM_DQ*SWIDTH-1:0]      ch0_dfi_rddata_w4;
   logic [NUM_DQ*MWIDTH-1:0]      ch0_dfi_rddata_dbi_w4;
   logic                          ch0_dfi_rddata_valid_w4;
   logic [NUM_DQ*SWIDTH-1:0]      ch0_dfi_rddata_w5;
   logic [NUM_DQ*MWIDTH-1:0]      ch0_dfi_rddata_dbi_w5;
   logic                          ch0_dfi_rddata_valid_w5;
   logic [NUM_DQ*SWIDTH-1:0]      ch0_dfi_rddata_w6;
   logic [NUM_DQ*MWIDTH-1:0]      ch0_dfi_rddata_dbi_w6;
   logic                          ch0_dfi_rddata_valid_w6;
   logic [NUM_DQ*SWIDTH-1:0]      ch0_dfi_rddata_w7;
   logic [NUM_DQ*MWIDTH-1:0]      ch0_dfi_rddata_dbi_w7;
   logic                          ch0_dfi_rddata_valid_w7;
   logic [NUM_DQ*SWIDTH-1:0]      ch1_dfi_rddata_w0;
   logic [NUM_DQ*MWIDTH-1:0]      ch1_dfi_rddata_dbi_w0;
   logic                          ch1_dfi_rddata_valid_w0;
   logic [NUM_DQ*SWIDTH-1:0]      ch1_dfi_rddata_w1;
   logic [NUM_DQ*MWIDTH-1:0]      ch1_dfi_rddata_dbi_w1;
   logic                          ch1_dfi_rddata_valid_w1;
   logic [NUM_DQ*SWIDTH-1:0]      ch1_dfi_rddata_w2;
   logic [NUM_DQ*MWIDTH-1:0]      ch1_dfi_rddata_dbi_w2;
   logic                          ch1_dfi_rddata_valid_w2;
   logic [NUM_DQ*SWIDTH-1:0]      ch1_dfi_rddata_w3;
   logic [NUM_DQ*MWIDTH-1:0]      ch1_dfi_rddata_dbi_w3;
   logic                          ch1_dfi_rddata_valid_w3;
   logic [NUM_DQ*SWIDTH-1:0]      ch1_dfi_rddata_w4;
   logic [NUM_DQ*MWIDTH-1:0]      ch1_dfi_rddata_dbi_w4;
   logic                          ch1_dfi_rddata_valid_w4;
   logic [NUM_DQ*SWIDTH-1:0]      ch1_dfi_rddata_w5;
   logic [NUM_DQ*MWIDTH-1:0]      ch1_dfi_rddata_dbi_w5;
   logic                          ch1_dfi_rddata_valid_w5;
   logic [NUM_DQ*SWIDTH-1:0]      ch1_dfi_rddata_w6;
   logic [NUM_DQ*MWIDTH-1:0]      ch1_dfi_rddata_dbi_w6;
   logic                          ch1_dfi_rddata_valid_w6;
   logic [NUM_DQ*SWIDTH-1:0]      ch1_dfi_rddata_w7;
   logic [NUM_DQ*MWIDTH-1:0]      ch1_dfi_rddata_dbi_w7;
   logic                          ch1_dfi_rddata_valid_w7;

   logic [SWIDTH-1:0]             ch0_dq0_dfi_wrdata_p0;
   logic [MWIDTH-1:0]             ch0_dq0_dfi_wrdata_mask_p0;
   logic                          ch0_dq0_dfi_wck_cs_p0;
   logic                          ch0_dq0_dfi_wck_en_p0;
   logic [TWIDTH-1:0]             ch0_dq0_dfi_wck_toggle_p0;
   logic                          ch0_dq0_dfi_wrdata_en_p0;
   logic                          ch0_dq0_dfi_rddata_en_p0;
   logic                          ch0_dq0_dfi_parity_in_p0;
   logic                          ch0_dq0_dfi_wrdata_cs_p0;
   logic                          ch0_dq0_dfi_rddata_cs_p0;
   logic [SWIDTH-1:0]             ch0_dq1_dfi_wrdata_p0;
   logic [MWIDTH-1:0]             ch0_dq1_dfi_wrdata_mask_p0;
   logic                          ch0_dq1_dfi_wck_cs_p0;
   logic                          ch0_dq1_dfi_wck_en_p0;
   logic [TWIDTH-1:0]             ch0_dq1_dfi_wck_toggle_p0;
   logic                          ch0_dq1_dfi_wrdata_en_p0;
   logic                          ch0_dq1_dfi_rddata_en_p0;
   logic                          ch0_dq1_dfi_parity_in_p0;
   logic                          ch0_dq1_dfi_wrdata_cs_p0;
   logic                          ch0_dq1_dfi_rddata_cs_p0;
   logic [SWIDTH-1:0]             ch0_dq0_dfi_wrdata_p1;
   logic [MWIDTH-1:0]             ch0_dq0_dfi_wrdata_mask_p1;
   logic                          ch0_dq0_dfi_wck_cs_p1;
   logic                          ch0_dq0_dfi_wck_en_p1;
   logic [TWIDTH-1:0]             ch0_dq0_dfi_wck_toggle_p1;
   logic                          ch0_dq0_dfi_wrdata_en_p1;
   logic                          ch0_dq0_dfi_rddata_en_p1;
   logic                          ch0_dq0_dfi_parity_in_p1;
   logic                          ch0_dq0_dfi_wrdata_cs_p1;
   logic                          ch0_dq0_dfi_rddata_cs_p1;
   logic [SWIDTH-1:0]             ch0_dq1_dfi_wrdata_p1;
   logic [MWIDTH-1:0]             ch0_dq1_dfi_wrdata_mask_p1;
   logic                          ch0_dq1_dfi_wck_cs_p1;
   logic                          ch0_dq1_dfi_wck_en_p1;
   logic [TWIDTH-1:0]             ch0_dq1_dfi_wck_toggle_p1;
   logic                          ch0_dq1_dfi_wrdata_en_p1;
   logic                          ch0_dq1_dfi_rddata_en_p1;
   logic                          ch0_dq1_dfi_parity_in_p1;
   logic                          ch0_dq1_dfi_wrdata_cs_p1;
   logic                          ch0_dq1_dfi_rddata_cs_p1;
   logic [SWIDTH-1:0]             ch0_dq0_dfi_wrdata_p2;
   logic [MWIDTH-1:0]             ch0_dq0_dfi_wrdata_mask_p2;
   logic                          ch0_dq0_dfi_wck_cs_p2;
   logic                          ch0_dq0_dfi_wck_en_p2;
   logic [TWIDTH-1:0]             ch0_dq0_dfi_wck_toggle_p2;
   logic                          ch0_dq0_dfi_wrdata_en_p2;
   logic                          ch0_dq0_dfi_rddata_en_p2;
   logic                          ch0_dq0_dfi_parity_in_p2;
   logic                          ch0_dq0_dfi_wrdata_cs_p2;
   logic                          ch0_dq0_dfi_rddata_cs_p2;
   logic [SWIDTH-1:0]             ch0_dq1_dfi_wrdata_p2;
   logic [MWIDTH-1:0]             ch0_dq1_dfi_wrdata_mask_p2;
   logic                          ch0_dq1_dfi_wck_cs_p2;
   logic                          ch0_dq1_dfi_wck_en_p2;
   logic [TWIDTH-1:0]             ch0_dq1_dfi_wck_toggle_p2;
   logic                          ch0_dq1_dfi_wrdata_en_p2;
   logic                          ch0_dq1_dfi_rddata_en_p2;
   logic                          ch0_dq1_dfi_parity_in_p2;
   logic                          ch0_dq1_dfi_wrdata_cs_p2;
   logic                          ch0_dq1_dfi_rddata_cs_p2;
   logic [SWIDTH-1:0]             ch0_dq0_dfi_wrdata_p3;
   logic [MWIDTH-1:0]             ch0_dq0_dfi_wrdata_mask_p3;
   logic                          ch0_dq0_dfi_wck_cs_p3;
   logic                          ch0_dq0_dfi_wck_en_p3;
   logic [TWIDTH-1:0]             ch0_dq0_dfi_wck_toggle_p3;
   logic                          ch0_dq0_dfi_wrdata_en_p3;
   logic                          ch0_dq0_dfi_rddata_en_p3;
   logic                          ch0_dq0_dfi_parity_in_p3;
   logic                          ch0_dq0_dfi_wrdata_cs_p3;
   logic                          ch0_dq0_dfi_rddata_cs_p3;
   logic [SWIDTH-1:0]             ch0_dq1_dfi_wrdata_p3;
   logic [MWIDTH-1:0]             ch0_dq1_dfi_wrdata_mask_p3;
   logic                          ch0_dq1_dfi_wck_cs_p3;
   logic                          ch0_dq1_dfi_wck_en_p3;
   logic [TWIDTH-1:0]             ch0_dq1_dfi_wck_toggle_p3;
   logic                          ch0_dq1_dfi_wrdata_en_p3;
   logic                          ch0_dq1_dfi_rddata_en_p3;
   logic                          ch0_dq1_dfi_parity_in_p3;
   logic                          ch0_dq1_dfi_wrdata_cs_p3;
   logic                          ch0_dq1_dfi_rddata_cs_p3;
   logic [SWIDTH-1:0]             ch0_dq0_dfi_wrdata_p4;
   logic [MWIDTH-1:0]             ch0_dq0_dfi_wrdata_mask_p4;
   logic                          ch0_dq0_dfi_wck_cs_p4;
   logic                          ch0_dq0_dfi_wck_en_p4;
   logic [TWIDTH-1:0]             ch0_dq0_dfi_wck_toggle_p4;
   logic                          ch0_dq0_dfi_wrdata_en_p4;
   logic                          ch0_dq0_dfi_rddata_en_p4;
   logic                          ch0_dq0_dfi_parity_in_p4;
   logic                          ch0_dq0_dfi_wrdata_cs_p4;
   logic                          ch0_dq0_dfi_rddata_cs_p4;
   logic [SWIDTH-1:0]             ch0_dq1_dfi_wrdata_p4;
   logic [MWIDTH-1:0]             ch0_dq1_dfi_wrdata_mask_p4;
   logic                          ch0_dq1_dfi_wck_cs_p4;
   logic                          ch0_dq1_dfi_wck_en_p4;
   logic [TWIDTH-1:0]             ch0_dq1_dfi_wck_toggle_p4;
   logic                          ch0_dq1_dfi_wrdata_en_p4;
   logic                          ch0_dq1_dfi_rddata_en_p4;
   logic                          ch0_dq1_dfi_parity_in_p4;
   logic                          ch0_dq1_dfi_wrdata_cs_p4;
   logic                          ch0_dq1_dfi_rddata_cs_p4;
   logic [SWIDTH-1:0]             ch0_dq0_dfi_wrdata_p5;
   logic [MWIDTH-1:0]             ch0_dq0_dfi_wrdata_mask_p5;
   logic                          ch0_dq0_dfi_wck_cs_p5;
   logic                          ch0_dq0_dfi_wck_en_p5;
   logic [TWIDTH-1:0]             ch0_dq0_dfi_wck_toggle_p5;
   logic                          ch0_dq0_dfi_wrdata_en_p5;
   logic                          ch0_dq0_dfi_rddata_en_p5;
   logic                          ch0_dq0_dfi_parity_in_p5;
   logic                          ch0_dq0_dfi_wrdata_cs_p5;
   logic                          ch0_dq0_dfi_rddata_cs_p5;
   logic [SWIDTH-1:0]             ch0_dq1_dfi_wrdata_p5;
   logic [MWIDTH-1:0]             ch0_dq1_dfi_wrdata_mask_p5;
   logic                          ch0_dq1_dfi_wck_cs_p5;
   logic                          ch0_dq1_dfi_wck_en_p5;
   logic [TWIDTH-1:0]             ch0_dq1_dfi_wck_toggle_p5;
   logic                          ch0_dq1_dfi_wrdata_en_p5;
   logic                          ch0_dq1_dfi_rddata_en_p5;
   logic                          ch0_dq1_dfi_parity_in_p5;
   logic                          ch0_dq1_dfi_wrdata_cs_p5;
   logic                          ch0_dq1_dfi_rddata_cs_p5;
   logic [SWIDTH-1:0]             ch0_dq0_dfi_wrdata_p6;
   logic [MWIDTH-1:0]             ch0_dq0_dfi_wrdata_mask_p6;
   logic                          ch0_dq0_dfi_wck_cs_p6;
   logic                          ch0_dq0_dfi_wck_en_p6;
   logic [TWIDTH-1:0]             ch0_dq0_dfi_wck_toggle_p6;
   logic                          ch0_dq0_dfi_wrdata_en_p6;
   logic                          ch0_dq0_dfi_rddata_en_p6;
   logic                          ch0_dq0_dfi_parity_in_p6;
   logic                          ch0_dq0_dfi_wrdata_cs_p6;
   logic                          ch0_dq0_dfi_rddata_cs_p6;
   logic [SWIDTH-1:0]             ch0_dq1_dfi_wrdata_p6;
   logic [MWIDTH-1:0]             ch0_dq1_dfi_wrdata_mask_p6;
   logic                          ch0_dq1_dfi_wck_cs_p6;
   logic                          ch0_dq1_dfi_wck_en_p6;
   logic [TWIDTH-1:0]             ch0_dq1_dfi_wck_toggle_p6;
   logic                          ch0_dq1_dfi_wrdata_en_p6;
   logic                          ch0_dq1_dfi_rddata_en_p6;
   logic                          ch0_dq1_dfi_parity_in_p6;
   logic                          ch0_dq1_dfi_wrdata_cs_p6;
   logic                          ch0_dq1_dfi_rddata_cs_p6;
   logic [SWIDTH-1:0]             ch0_dq0_dfi_wrdata_p7;
   logic [MWIDTH-1:0]             ch0_dq0_dfi_wrdata_mask_p7;
   logic                          ch0_dq0_dfi_wck_cs_p7;
   logic                          ch0_dq0_dfi_wck_en_p7;
   logic [TWIDTH-1:0]             ch0_dq0_dfi_wck_toggle_p7;
   logic                          ch0_dq0_dfi_wrdata_en_p7;
   logic                          ch0_dq0_dfi_rddata_en_p7;
   logic                          ch0_dq0_dfi_parity_in_p7;
   logic                          ch0_dq0_dfi_wrdata_cs_p7;
   logic                          ch0_dq0_dfi_rddata_cs_p7;
   logic [SWIDTH-1:0]             ch0_dq1_dfi_wrdata_p7;
   logic [MWIDTH-1:0]             ch0_dq1_dfi_wrdata_mask_p7;
   logic                          ch0_dq1_dfi_wck_cs_p7;
   logic                          ch0_dq1_dfi_wck_en_p7;
   logic [TWIDTH-1:0]             ch0_dq1_dfi_wck_toggle_p7;
   logic                          ch0_dq1_dfi_wrdata_en_p7;
   logic                          ch0_dq1_dfi_rddata_en_p7;
   logic                          ch0_dq1_dfi_parity_in_p7;
   logic                          ch0_dq1_dfi_wrdata_cs_p7;
   logic                          ch0_dq1_dfi_rddata_cs_p7;
   logic [SWIDTH-1:0]             ch1_dq0_dfi_wrdata_p0;
   logic [MWIDTH-1:0]             ch1_dq0_dfi_wrdata_mask_p0;
   logic                          ch1_dq0_dfi_wck_cs_p0;
   logic                          ch1_dq0_dfi_wck_en_p0;
   logic [TWIDTH-1:0]             ch1_dq0_dfi_wck_toggle_p0;
   logic                          ch1_dq0_dfi_wrdata_en_p0;
   logic                          ch1_dq0_dfi_rddata_en_p0;
   logic                          ch1_dq0_dfi_parity_in_p0;
   logic                          ch1_dq0_dfi_wrdata_cs_p0;
   logic                          ch1_dq0_dfi_rddata_cs_p0;
   logic [SWIDTH-1:0]             ch1_dq1_dfi_wrdata_p0;
   logic [MWIDTH-1:0]             ch1_dq1_dfi_wrdata_mask_p0;
   logic                          ch1_dq1_dfi_wck_cs_p0;
   logic                          ch1_dq1_dfi_wck_en_p0;
   logic [TWIDTH-1:0]             ch1_dq1_dfi_wck_toggle_p0;
   logic                          ch1_dq1_dfi_wrdata_en_p0;
   logic                          ch1_dq1_dfi_rddata_en_p0;
   logic                          ch1_dq1_dfi_parity_in_p0;
   logic                          ch1_dq1_dfi_wrdata_cs_p0;
   logic                          ch1_dq1_dfi_rddata_cs_p0;
   logic [SWIDTH-1:0]             ch1_dq0_dfi_wrdata_p1;
   logic [MWIDTH-1:0]             ch1_dq0_dfi_wrdata_mask_p1;
   logic                          ch1_dq0_dfi_wck_cs_p1;
   logic                          ch1_dq0_dfi_wck_en_p1;
   logic [TWIDTH-1:0]             ch1_dq0_dfi_wck_toggle_p1;
   logic                          ch1_dq0_dfi_wrdata_en_p1;
   logic                          ch1_dq0_dfi_rddata_en_p1;
   logic                          ch1_dq0_dfi_parity_in_p1;
   logic                          ch1_dq0_dfi_wrdata_cs_p1;
   logic                          ch1_dq0_dfi_rddata_cs_p1;
   logic [SWIDTH-1:0]             ch1_dq1_dfi_wrdata_p1;
   logic [MWIDTH-1:0]             ch1_dq1_dfi_wrdata_mask_p1;
   logic                          ch1_dq1_dfi_wck_cs_p1;
   logic                          ch1_dq1_dfi_wck_en_p1;
   logic [TWIDTH-1:0]             ch1_dq1_dfi_wck_toggle_p1;
   logic                          ch1_dq1_dfi_wrdata_en_p1;
   logic                          ch1_dq1_dfi_rddata_en_p1;
   logic                          ch1_dq1_dfi_parity_in_p1;
   logic                          ch1_dq1_dfi_wrdata_cs_p1;
   logic                          ch1_dq1_dfi_rddata_cs_p1;
   logic [SWIDTH-1:0]             ch1_dq0_dfi_wrdata_p2;
   logic [MWIDTH-1:0]             ch1_dq0_dfi_wrdata_mask_p2;
   logic                          ch1_dq0_dfi_wck_cs_p2;
   logic                          ch1_dq0_dfi_wck_en_p2;
   logic [TWIDTH-1:0]             ch1_dq0_dfi_wck_toggle_p2;
   logic                          ch1_dq0_dfi_wrdata_en_p2;
   logic                          ch1_dq0_dfi_rddata_en_p2;
   logic                          ch1_dq0_dfi_parity_in_p2;
   logic                          ch1_dq0_dfi_wrdata_cs_p2;
   logic                          ch1_dq0_dfi_rddata_cs_p2;
   logic [SWIDTH-1:0]             ch1_dq1_dfi_wrdata_p2;
   logic [MWIDTH-1:0]             ch1_dq1_dfi_wrdata_mask_p2;
   logic                          ch1_dq1_dfi_wck_cs_p2;
   logic                          ch1_dq1_dfi_wck_en_p2;
   logic [TWIDTH-1:0]             ch1_dq1_dfi_wck_toggle_p2;
   logic                          ch1_dq1_dfi_wrdata_en_p2;
   logic                          ch1_dq1_dfi_rddata_en_p2;
   logic                          ch1_dq1_dfi_parity_in_p2;
   logic                          ch1_dq1_dfi_wrdata_cs_p2;
   logic                          ch1_dq1_dfi_rddata_cs_p2;
   logic [SWIDTH-1:0]             ch1_dq0_dfi_wrdata_p3;
   logic [MWIDTH-1:0]             ch1_dq0_dfi_wrdata_mask_p3;
   logic                          ch1_dq0_dfi_wck_cs_p3;
   logic                          ch1_dq0_dfi_wck_en_p3;
   logic [TWIDTH-1:0]             ch1_dq0_dfi_wck_toggle_p3;
   logic                          ch1_dq0_dfi_wrdata_en_p3;
   logic                          ch1_dq0_dfi_rddata_en_p3;
   logic                          ch1_dq0_dfi_parity_in_p3;
   logic                          ch1_dq0_dfi_wrdata_cs_p3;
   logic                          ch1_dq0_dfi_rddata_cs_p3;
   logic [SWIDTH-1:0]             ch1_dq1_dfi_wrdata_p3;
   logic [MWIDTH-1:0]             ch1_dq1_dfi_wrdata_mask_p3;
   logic                          ch1_dq1_dfi_wck_cs_p3;
   logic                          ch1_dq1_dfi_wck_en_p3;
   logic [TWIDTH-1:0]             ch1_dq1_dfi_wck_toggle_p3;
   logic                          ch1_dq1_dfi_wrdata_en_p3;
   logic                          ch1_dq1_dfi_rddata_en_p3;
   logic                          ch1_dq1_dfi_parity_in_p3;
   logic                          ch1_dq1_dfi_wrdata_cs_p3;
   logic                          ch1_dq1_dfi_rddata_cs_p3;
   logic [SWIDTH-1:0]             ch1_dq0_dfi_wrdata_p4;
   logic [MWIDTH-1:0]             ch1_dq0_dfi_wrdata_mask_p4;
   logic                          ch1_dq0_dfi_wck_cs_p4;
   logic                          ch1_dq0_dfi_wck_en_p4;
   logic [TWIDTH-1:0]             ch1_dq0_dfi_wck_toggle_p4;
   logic                          ch1_dq0_dfi_wrdata_en_p4;
   logic                          ch1_dq0_dfi_rddata_en_p4;
   logic                          ch1_dq0_dfi_parity_in_p4;
   logic                          ch1_dq0_dfi_wrdata_cs_p4;
   logic                          ch1_dq0_dfi_rddata_cs_p4;
   logic [SWIDTH-1:0]             ch1_dq1_dfi_wrdata_p4;
   logic [MWIDTH-1:0]             ch1_dq1_dfi_wrdata_mask_p4;
   logic                          ch1_dq1_dfi_wck_cs_p4;
   logic                          ch1_dq1_dfi_wck_en_p4;
   logic [TWIDTH-1:0]             ch1_dq1_dfi_wck_toggle_p4;
   logic                          ch1_dq1_dfi_wrdata_en_p4;
   logic                          ch1_dq1_dfi_rddata_en_p4;
   logic                          ch1_dq1_dfi_parity_in_p4;
   logic                          ch1_dq1_dfi_wrdata_cs_p4;
   logic                          ch1_dq1_dfi_rddata_cs_p4;
   logic [SWIDTH-1:0]             ch1_dq0_dfi_wrdata_p5;
   logic [MWIDTH-1:0]             ch1_dq0_dfi_wrdata_mask_p5;
   logic                          ch1_dq0_dfi_wck_cs_p5;
   logic                          ch1_dq0_dfi_wck_en_p5;
   logic [TWIDTH-1:0]             ch1_dq0_dfi_wck_toggle_p5;
   logic                          ch1_dq0_dfi_wrdata_en_p5;
   logic                          ch1_dq0_dfi_rddata_en_p5;
   logic                          ch1_dq0_dfi_parity_in_p5;
   logic                          ch1_dq0_dfi_wrdata_cs_p5;
   logic                          ch1_dq0_dfi_rddata_cs_p5;
   logic [SWIDTH-1:0]             ch1_dq1_dfi_wrdata_p5;
   logic [MWIDTH-1:0]             ch1_dq1_dfi_wrdata_mask_p5;
   logic                          ch1_dq1_dfi_wck_cs_p5;
   logic                          ch1_dq1_dfi_wck_en_p5;
   logic [TWIDTH-1:0]             ch1_dq1_dfi_wck_toggle_p5;
   logic                          ch1_dq1_dfi_wrdata_en_p5;
   logic                          ch1_dq1_dfi_rddata_en_p5;
   logic                          ch1_dq1_dfi_parity_in_p5;
   logic                          ch1_dq1_dfi_wrdata_cs_p5;
   logic                          ch1_dq1_dfi_rddata_cs_p5;
   logic [SWIDTH-1:0]             ch1_dq0_dfi_wrdata_p6;
   logic [MWIDTH-1:0]             ch1_dq0_dfi_wrdata_mask_p6;
   logic                          ch1_dq0_dfi_wck_cs_p6;
   logic                          ch1_dq0_dfi_wck_en_p6;
   logic [TWIDTH-1:0]             ch1_dq0_dfi_wck_toggle_p6;
   logic                          ch1_dq0_dfi_wrdata_en_p6;
   logic                          ch1_dq0_dfi_rddata_en_p6;
   logic                          ch1_dq0_dfi_parity_in_p6;
   logic                          ch1_dq0_dfi_wrdata_cs_p6;
   logic                          ch1_dq0_dfi_rddata_cs_p6;
   logic [SWIDTH-1:0]             ch1_dq1_dfi_wrdata_p6;
   logic [MWIDTH-1:0]             ch1_dq1_dfi_wrdata_mask_p6;
   logic                          ch1_dq1_dfi_wck_cs_p6;
   logic                          ch1_dq1_dfi_wck_en_p6;
   logic [TWIDTH-1:0]             ch1_dq1_dfi_wck_toggle_p6;
   logic                          ch1_dq1_dfi_wrdata_en_p6;
   logic                          ch1_dq1_dfi_rddata_en_p6;
   logic                          ch1_dq1_dfi_parity_in_p6;
   logic                          ch1_dq1_dfi_wrdata_cs_p6;
   logic                          ch1_dq1_dfi_rddata_cs_p6;
   logic [SWIDTH-1:0]             ch1_dq0_dfi_wrdata_p7;
   logic [MWIDTH-1:0]             ch1_dq0_dfi_wrdata_mask_p7;
   logic                          ch1_dq0_dfi_wck_cs_p7;
   logic                          ch1_dq0_dfi_wck_en_p7;
   logic [TWIDTH-1:0]             ch1_dq0_dfi_wck_toggle_p7;
   logic                          ch1_dq0_dfi_wrdata_en_p7;
   logic                          ch1_dq0_dfi_rddata_en_p7;
   logic                          ch1_dq0_dfi_parity_in_p7;
   logic                          ch1_dq0_dfi_wrdata_cs_p7;
   logic                          ch1_dq0_dfi_rddata_cs_p7;
   logic [SWIDTH-1:0]             ch1_dq1_dfi_wrdata_p7;
   logic [MWIDTH-1:0]             ch1_dq1_dfi_wrdata_mask_p7;
   logic                          ch1_dq1_dfi_wck_cs_p7;
   logic                          ch1_dq1_dfi_wck_en_p7;
   logic [TWIDTH-1:0]             ch1_dq1_dfi_wck_toggle_p7;
   logic                          ch1_dq1_dfi_wrdata_en_p7;
   logic                          ch1_dq1_dfi_rddata_en_p7;
   logic                          ch1_dq1_dfi_parity_in_p7;
   logic                          ch1_dq1_dfi_wrdata_cs_p7;
   logic                          ch1_dq1_dfi_rddata_cs_p7;

   logic [AWIDTH-1:0]             dfi_address_w0;
   logic [1:0]                    dfi_cke_w0;
   logic [1:0]                    dfi_cs_w0;
   logic                          dfi_address_valid_w0;
   logic [AWIDTH-1:0]             dfi_address_w1;
   logic [1:0]                    dfi_cke_w1;
   logic [1:0]                    dfi_cs_w1;
   logic                          dfi_address_valid_w1;
   logic [AWIDTH-1:0]             dfi_address_w2;
   logic [1:0]                    dfi_cke_w2;
   logic [1:0]                    dfi_cs_w2;
   logic                          dfi_address_valid_w2;
   logic [AWIDTH-1:0]             dfi_address_w3;
   logic [1:0]                    dfi_cke_w3;
   logic [1:0]                    dfi_cs_w3;
   logic                          dfi_address_valid_w3;
   logic [AWIDTH-1:0]             dfi_address_w4;
   logic [1:0]                    dfi_cke_w4;
   logic [1:0]                    dfi_cs_w4;
   logic                          dfi_address_valid_w4;
   logic [AWIDTH-1:0]             dfi_address_w5;
   logic [1:0]                    dfi_cke_w5;
   logic [1:0]                    dfi_cs_w5;
   logic                          dfi_address_valid_w5;
   logic [AWIDTH-1:0]             dfi_address_w6;
   logic [1:0]                    dfi_cke_w6;
   logic [1:0]                    dfi_cs_w6;
   logic                          dfi_address_valid_w6;
   logic [AWIDTH-1:0]             dfi_address_w7;
   logic [1:0]                    dfi_cke_w7;
   logic [1:0]                    dfi_cs_w7;
   logic                          dfi_address_valid_w7;

   logic [AWIDTH-1:0]             ch0_dfi_address_w0;
   logic [1:0]                    ch0_dfi_cke_w0;
   logic [1:0]                    ch0_dfi_cs_w0;
   logic                          ch0_dfi_address_valid_w0;
   logic [AWIDTH-1:0]             ch0_dfi_address_w1;
   logic [1:0]                    ch0_dfi_cke_w1;
   logic [1:0]                    ch0_dfi_cs_w1;
   logic                          ch0_dfi_address_valid_w1;
   logic [AWIDTH-1:0]             ch0_dfi_address_w2;
   logic [1:0]                    ch0_dfi_cke_w2;
   logic [1:0]                    ch0_dfi_cs_w2;
   logic                          ch0_dfi_address_valid_w2;
   logic [AWIDTH-1:0]             ch0_dfi_address_w3;
   logic [1:0]                    ch0_dfi_cke_w3;
   logic [1:0]                    ch0_dfi_cs_w3;
   logic                          ch0_dfi_address_valid_w3;
   logic [AWIDTH-1:0]             ch0_dfi_address_w4;
   logic [1:0]                    ch0_dfi_cke_w4;
   logic [1:0]                    ch0_dfi_cs_w4;
   logic                          ch0_dfi_address_valid_w4;
   logic [AWIDTH-1:0]             ch0_dfi_address_w5;
   logic [1:0]                    ch0_dfi_cke_w5;
   logic [1:0]                    ch0_dfi_cs_w5;
   logic                          ch0_dfi_address_valid_w5;
   logic [AWIDTH-1:0]             ch0_dfi_address_w6;
   logic [1:0]                    ch0_dfi_cke_w6;
   logic [1:0]                    ch0_dfi_cs_w6;
   logic                          ch0_dfi_address_valid_w6;
   logic [AWIDTH-1:0]             ch0_dfi_address_w7;
   logic [1:0]                    ch0_dfi_cke_w7;
   logic [1:0]                    ch0_dfi_cs_w7;
   logic                          ch0_dfi_address_valid_w7;
   logic [AWIDTH-1:0]             ch1_dfi_address_w0;
   logic [1:0]                    ch1_dfi_cke_w0;
   logic [1:0]                    ch1_dfi_cs_w0;
   logic                          ch1_dfi_address_valid_w0;
   logic [AWIDTH-1:0]             ch1_dfi_address_w1;
   logic [1:0]                    ch1_dfi_cke_w1;
   logic [1:0]                    ch1_dfi_cs_w1;
   logic                          ch1_dfi_address_valid_w1;
   logic [AWIDTH-1:0]             ch1_dfi_address_w2;
   logic [1:0]                    ch1_dfi_cke_w2;
   logic [1:0]                    ch1_dfi_cs_w2;
   logic                          ch1_dfi_address_valid_w2;
   logic [AWIDTH-1:0]             ch1_dfi_address_w3;
   logic [1:0]                    ch1_dfi_cke_w3;
   logic [1:0]                    ch1_dfi_cs_w3;
   logic                          ch1_dfi_address_valid_w3;
   logic [AWIDTH-1:0]             ch1_dfi_address_w4;
   logic [1:0]                    ch1_dfi_cke_w4;
   logic [1:0]                    ch1_dfi_cs_w4;
   logic                          ch1_dfi_address_valid_w4;
   logic [AWIDTH-1:0]             ch1_dfi_address_w5;
   logic [1:0]                    ch1_dfi_cke_w5;
   logic [1:0]                    ch1_dfi_cs_w5;
   logic                          ch1_dfi_address_valid_w5;
   logic [AWIDTH-1:0]             ch1_dfi_address_w6;
   logic [1:0]                    ch1_dfi_cke_w6;
   logic [1:0]                    ch1_dfi_cs_w6;
   logic                          ch1_dfi_address_valid_w6;
   logic [AWIDTH-1:0]             ch1_dfi_address_w7;
   logic [1:0]                    ch1_dfi_cke_w7;
   logic [1:0]                    ch1_dfi_cs_w7;
   logic                          ch1_dfi_address_valid_w7;

   logic [AWIDTH-1:0]             ch0_dfi_address_p0;
   logic [1:0]                    ch0_dfi_cke_p0;
   logic [1:0]                    ch0_dfi_cs_p0;
   logic                          ch0_dfi_dram_clk_disable_p0;
   logic [AWIDTH-1:0]             ch0_dfi_address_p1;
   logic [1:0]                    ch0_dfi_cke_p1;
   logic [1:0]                    ch0_dfi_cs_p1;
   logic                          ch0_dfi_dram_clk_disable_p1;
   logic [AWIDTH-1:0]             ch0_dfi_address_p2;
   logic [1:0]                    ch0_dfi_cke_p2;
   logic [1:0]                    ch0_dfi_cs_p2;
   logic                          ch0_dfi_dram_clk_disable_p2;
   logic [AWIDTH-1:0]             ch0_dfi_address_p3;
   logic [1:0]                    ch0_dfi_cke_p3;
   logic [1:0]                    ch0_dfi_cs_p3;
   logic                          ch0_dfi_dram_clk_disable_p3;
   logic [AWIDTH-1:0]             ch0_dfi_address_p4;
   logic [1:0]                    ch0_dfi_cke_p4;
   logic [1:0]                    ch0_dfi_cs_p4;
   logic                          ch0_dfi_dram_clk_disable_p4;
   logic [AWIDTH-1:0]             ch0_dfi_address_p5;
   logic [1:0]                    ch0_dfi_cke_p5;
   logic [1:0]                    ch0_dfi_cs_p5;
   logic                          ch0_dfi_dram_clk_disable_p5;
   logic [AWIDTH-1:0]             ch0_dfi_address_p6;
   logic [1:0]                    ch0_dfi_cke_p6;
   logic [1:0]                    ch0_dfi_cs_p6;
   logic                          ch0_dfi_dram_clk_disable_p6;
   logic [AWIDTH-1:0]             ch0_dfi_address_p7;
   logic [1:0]                    ch0_dfi_cke_p7;
   logic [1:0]                    ch0_dfi_cs_p7;
   logic                          ch0_dfi_dram_clk_disable_p7;
   logic [AWIDTH-1:0]             ch1_dfi_address_p0;
   logic [1:0]                    ch1_dfi_cke_p0;
   logic [1:0]                    ch1_dfi_cs_p0;
   logic                          ch1_dfi_dram_clk_disable_p0;
   logic [AWIDTH-1:0]             ch1_dfi_address_p1;
   logic [1:0]                    ch1_dfi_cke_p1;
   logic [1:0]                    ch1_dfi_cs_p1;
   logic                          ch1_dfi_dram_clk_disable_p1;
   logic [AWIDTH-1:0]             ch1_dfi_address_p2;
   logic [1:0]                    ch1_dfi_cke_p2;
   logic [1:0]                    ch1_dfi_cs_p2;
   logic                          ch1_dfi_dram_clk_disable_p2;
   logic [AWIDTH-1:0]             ch1_dfi_address_p3;
   logic [1:0]                    ch1_dfi_cke_p3;
   logic [1:0]                    ch1_dfi_cs_p3;
   logic                          ch1_dfi_dram_clk_disable_p3;
   logic [AWIDTH-1:0]             ch1_dfi_address_p4;
   logic [1:0]                    ch1_dfi_cke_p4;
   logic [1:0]                    ch1_dfi_cs_p4;
   logic                          ch1_dfi_dram_clk_disable_p4;
   logic [AWIDTH-1:0]             ch1_dfi_address_p5;
   logic [1:0]                    ch1_dfi_cke_p5;
   logic [1:0]                    ch1_dfi_cs_p5;
   logic                          ch1_dfi_dram_clk_disable_p5;
   logic [AWIDTH-1:0]             ch1_dfi_address_p6;
   logic [1:0]                    ch1_dfi_cke_p6;
   logic [1:0]                    ch1_dfi_cs_p6;
   logic                          ch1_dfi_dram_clk_disable_p6;
   logic [AWIDTH-1:0]             ch1_dfi_address_p7;
   logic [1:0]                    ch1_dfi_cke_p7;
   logic [1:0]                    ch1_dfi_cs_p7;
   logic                          ch1_dfi_dram_clk_disable_p7;

   assign dqs_wrclk_en =  1'b0
                      | (|ch0_dq0_dfi_rddata_en_p0)
                      | (|ch0_dq0_dfi_rddata_en_p1)
                      | (|ch0_dq0_dfi_rddata_en_p2)
                      | (|ch0_dq0_dfi_rddata_en_p3)
                      | (|ch0_dq0_dfi_rddata_en_p4)
                      | (|ch0_dq0_dfi_rddata_en_p5)
                      | (|ch0_dq0_dfi_rddata_en_p6)
                      | (|ch0_dq0_dfi_rddata_en_p7)
                      | (|ch0_dq0_dfi_rddata_cs_p0)
                      | (|ch0_dq0_dfi_rddata_cs_p1)
                      | (|ch0_dq0_dfi_rddata_cs_p2)
                      | (|ch0_dq0_dfi_rddata_cs_p3)
                      | (|ch0_dq0_dfi_rddata_cs_p4)
                      | (|ch0_dq0_dfi_rddata_cs_p5)
                      | (|ch0_dq0_dfi_rddata_cs_p6)
                      | (|ch0_dq0_dfi_rddata_cs_p7)
                      | (|ch0_dq0_dfi_wrdata_cs_p0)
                      | (|ch0_dq0_dfi_wrdata_cs_p1)
                      | (|ch0_dq0_dfi_wrdata_cs_p2)
                      | (|ch0_dq0_dfi_wrdata_cs_p3)
                      | (|ch0_dq0_dfi_wrdata_cs_p4)
                      | (|ch0_dq0_dfi_wrdata_cs_p5)
                      | (|ch0_dq0_dfi_wrdata_cs_p6)
                      | (|ch0_dq0_dfi_wrdata_cs_p7)
                      | (|ch0_dq0_dfi_wrdata_en_p0)
                      | (|ch0_dq0_dfi_wrdata_en_p1)
                      | (|ch0_dq0_dfi_wrdata_en_p2)
                      | (|ch0_dq0_dfi_wrdata_en_p3)
                      | (|ch0_dq0_dfi_wrdata_en_p4)
                      | (|ch0_dq0_dfi_wrdata_en_p5)
                      | (|ch0_dq0_dfi_wrdata_en_p6)
                      | (|ch0_dq0_dfi_wrdata_en_p7)
                      | (|ch0_dq0_dfi_wck_en_p0)
                      | (|ch0_dq0_dfi_wck_en_p1)
                      | (|ch0_dq0_dfi_wck_en_p2)
                      | (|ch0_dq0_dfi_wck_en_p3)
                      | (|ch0_dq0_dfi_wck_en_p4)
                      | (|ch0_dq0_dfi_wck_en_p5)
                      | (|ch0_dq0_dfi_wck_en_p6)
                      | (|ch0_dq0_dfi_wck_en_p7)
                      | (|ch1_dq0_dfi_rddata_en_p0)
                      | (|ch1_dq0_dfi_rddata_en_p1)
                      | (|ch1_dq0_dfi_rddata_en_p2)
                      | (|ch1_dq0_dfi_rddata_en_p3)
                      | (|ch1_dq0_dfi_rddata_en_p4)
                      | (|ch1_dq0_dfi_rddata_en_p5)
                      | (|ch1_dq0_dfi_rddata_en_p6)
                      | (|ch1_dq0_dfi_rddata_en_p7)
                      | (|ch1_dq0_dfi_rddata_cs_p0)
                      | (|ch1_dq0_dfi_rddata_cs_p1)
                      | (|ch1_dq0_dfi_rddata_cs_p2)
                      | (|ch1_dq0_dfi_rddata_cs_p3)
                      | (|ch1_dq0_dfi_rddata_cs_p4)
                      | (|ch1_dq0_dfi_rddata_cs_p5)
                      | (|ch1_dq0_dfi_rddata_cs_p6)
                      | (|ch1_dq0_dfi_rddata_cs_p7)
                      | (|ch1_dq0_dfi_wrdata_cs_p0)
                      | (|ch1_dq0_dfi_wrdata_cs_p1)
                      | (|ch1_dq0_dfi_wrdata_cs_p2)
                      | (|ch1_dq0_dfi_wrdata_cs_p3)
                      | (|ch1_dq0_dfi_wrdata_cs_p4)
                      | (|ch1_dq0_dfi_wrdata_cs_p5)
                      | (|ch1_dq0_dfi_wrdata_cs_p6)
                      | (|ch1_dq0_dfi_wrdata_cs_p7)
                      | (|ch1_dq0_dfi_wrdata_en_p0)
                      | (|ch1_dq0_dfi_wrdata_en_p1)
                      | (|ch1_dq0_dfi_wrdata_en_p2)
                      | (|ch1_dq0_dfi_wrdata_en_p3)
                      | (|ch1_dq0_dfi_wrdata_en_p4)
                      | (|ch1_dq0_dfi_wrdata_en_p5)
                      | (|ch1_dq0_dfi_wrdata_en_p6)
                      | (|ch1_dq0_dfi_wrdata_en_p7)
                      | (|ch1_dq0_dfi_wck_en_p0)
                      | (|ch1_dq0_dfi_wck_en_p1)
                      | (|ch1_dq0_dfi_wck_en_p2)
                      | (|ch1_dq0_dfi_wck_en_p3)
                      | (|ch1_dq0_dfi_wck_en_p4)
                      | (|ch1_dq0_dfi_wck_en_p5)
                      | (|ch1_dq0_dfi_wck_en_p6)
                      | (|ch1_dq0_dfi_wck_en_p7)
                      ;

   assign dq_wrclk_en =  1'b0
                      | (|ch0_dq0_dfi_wrdata_cs_p0)
                      | (|ch0_dq0_dfi_wrdata_cs_p1)
                      | (|ch0_dq0_dfi_wrdata_cs_p2)
                      | (|ch0_dq0_dfi_wrdata_cs_p3)
                      | (|ch0_dq0_dfi_wrdata_cs_p4)
                      | (|ch0_dq0_dfi_wrdata_cs_p5)
                      | (|ch0_dq0_dfi_wrdata_cs_p6)
                      | (|ch0_dq0_dfi_wrdata_cs_p7)
                      | (|ch0_dq0_dfi_wrdata_en_p0)
                      | (|ch0_dq0_dfi_wrdata_en_p1)
                      | (|ch0_dq0_dfi_wrdata_en_p2)
                      | (|ch0_dq0_dfi_wrdata_en_p3)
                      | (|ch0_dq0_dfi_wrdata_en_p4)
                      | (|ch0_dq0_dfi_wrdata_en_p5)
                      | (|ch0_dq0_dfi_wrdata_en_p6)
                      | (|ch0_dq0_dfi_wrdata_en_p7)
                      | (|ch1_dq0_dfi_wrdata_cs_p0)
                      | (|ch1_dq0_dfi_wrdata_cs_p1)
                      | (|ch1_dq0_dfi_wrdata_cs_p2)
                      | (|ch1_dq0_dfi_wrdata_cs_p3)
                      | (|ch1_dq0_dfi_wrdata_cs_p4)
                      | (|ch1_dq0_dfi_wrdata_cs_p5)
                      | (|ch1_dq0_dfi_wrdata_cs_p6)
                      | (|ch1_dq0_dfi_wrdata_cs_p7)
                      | (|ch1_dq0_dfi_wrdata_en_p0)
                      | (|ch1_dq0_dfi_wrdata_en_p1)
                      | (|ch1_dq0_dfi_wrdata_en_p2)
                      | (|ch1_dq0_dfi_wrdata_en_p3)
                      | (|ch1_dq0_dfi_wrdata_en_p4)
                      | (|ch1_dq0_dfi_wrdata_en_p5)
                      | (|ch1_dq0_dfi_wrdata_en_p6)
                      | (|ch1_dq0_dfi_wrdata_en_p7)
                      ;

   assign ck_clk_en =  1'b0
                      | (|(~ch0_dfi_dram_clk_disable_p0))
                      | (|(~ch0_dfi_dram_clk_disable_p1))
                      | (|(~ch0_dfi_dram_clk_disable_p2))
                      | (|(~ch0_dfi_dram_clk_disable_p3))
                      | (|(~ch0_dfi_dram_clk_disable_p4))
                      | (|(~ch0_dfi_dram_clk_disable_p5))
                      | (|(~ch0_dfi_dram_clk_disable_p6))
                      | (|(~ch0_dfi_dram_clk_disable_p7))
                      | (|(~ch1_dfi_dram_clk_disable_p0))
                      | (|(~ch1_dfi_dram_clk_disable_p1))
                      | (|(~ch1_dfi_dram_clk_disable_p2))
                      | (|(~ch1_dfi_dram_clk_disable_p3))
                      | (|(~ch1_dfi_dram_clk_disable_p4))
                      | (|(~ch1_dfi_dram_clk_disable_p5))
                      | (|(~ch1_dfi_dram_clk_disable_p6))
                      | (|(~ch1_dfi_dram_clk_disable_p7))
                      ;

   assign ca_clk_en =  1'b0
                      | (|ch0_dfi_cke_p0)
                      | (|ch0_dfi_cke_p1)
                      | (|ch0_dfi_cke_p2)
                      | (|ch0_dfi_cke_p3)
                      | (|ch0_dfi_cke_p4)
                      | (|ch0_dfi_cke_p5)
                      | (|ch0_dfi_cke_p6)
                      | (|ch0_dfi_cke_p7)
                      | (|ch1_dfi_cke_p0)
                      | (|ch1_dfi_cke_p1)
                      | (|ch1_dfi_cke_p2)
                      | (|ch1_dfi_cke_p3)
                      | (|ch1_dfi_cke_p4)
                      | (|ch1_dfi_cke_p5)
                      | (|ch1_dfi_cke_p6)
                      | (|ch1_dfi_cke_p7)
                      ;
   logic dfi_buf_ig_empty, dfi_buf_ig_full, dfi_buf_ig_overflow, dfi_buf_ig_write_done ;
   logic dfi_buf_eg_empty, dfi_buf_eg_full, dfi_buf_eg_overflow, dfi_buf_eg_read_done ;

   always_comb begin
      dfich0_top_sta                                                     = '0 ;
      dfich0_top_sta[`DDR_DFICH_TOP_STA_IG_STATE_FIELD]     = {dfi_buf_ig_full, dfi_buf_ig_empty};
      dfich0_top_sta[`DDR_DFICH_TOP_STA_IG_STATE_UPD_FIELD] =  dfi_buf_ig_write_done ;
      dfich0_top_sta[`DDR_DFICH_TOP_STA_EG_STATE_FIELD]     = {dfi_buf_eg_full, dfi_buf_eg_empty};
      dfich0_top_sta[`DDR_DFICH_TOP_STA_EG_STATE_UPD_FIELD] =  dfi_buf_eg_read_done ;
   end

   assign dfi_rdout_en   = dfich0_top_1_cfg[`DDR_DFICH_TOP_1_CFG_RDOUT_EN_OVR_SEL_FIELD] ?
                                dfich0_top_1_cfg[`DDR_DFICH_TOP_1_CFG_RDOUT_EN_OVR_FIELD]     :
                                o_dfi_init_complete ;

   ddr_dfi_buf #(
      .NUM_WPH                      (NUM_WPH  ),
      .NUM_RPH                      (NUM_RPH  ),
      .NUM_DQ                       (NUM_DFI_DQ),
      .AHB_DWIDTH                   (AHB_DWIDTH),
      .IG_DEPTH                     (IG_DEPTH),
      .EG_DEPTH                     (EG_DEPTH),
      .TSWIDTH                      (TSWIDTH),
      .SWIDTH                       (SWIDTH),
      .DWIDTH                       (DWIDTH),
      .BWIDTH                       (BWIDTH),
      .MWIDTH                       (MWIDTH),
      .TWIDTH                       (TWIDTH),
      .RAM_MODEL                    (RAM_MODEL)
   ) u_dfi_buf (

      .i_scan_mode                  (i_scan_mode),
      .i_scan_rst_ctrl              (i_scan_rst_ctrl),
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),

      .i_clk                        (o_dfi_clk),
      .i_rst                        (i_rst),

      .i_buf_mode                   (dfich0_top_1_cfg[`DDR_DFICH_TOP_1_CFG_BUF_MODE_FIELD]),
      .i_buf_clk_en                 (dfich0_top_1_cfg[`DDR_DFICH_TOP_1_CFG_BUF_CLK_EN_FIELD]),
      .i_intf_pipe_en               (dfich0_ctrl0_cfg[`DDR_DFICH_CTRL0_M0_CFG_WR_INTF_PIPE_EN_FIELD]),

      .i_ts_enable                  (dfich0_top_1_cfg[`DDR_DFICH_TOP_1_CFG_TS_ENABLE_FIELD]),
      .i_ts_reset                   (dfich0_top_1_cfg[`DDR_DFICH_TOP_1_CFG_TS_RESET_FIELD]),
      .i_ts_brkpt_en                (dfich0_top_3_cfg[`DDR_DFICH_TOP_3_CFG_TS_BRKPT_EN_FIELD]),
      .i_ts_brkpt_val               (dfich0_top_3_cfg[`DDR_DFICH_TOP_3_CFG_TS_BRKPT_VAL_FIELD]),

      .i_ig_loop_mode               (dfich0_top_2_cfg[`DDR_DFICH_TOP_2_CFG_IG_LOOP_MODE_FIELD]),
      .i_ig_num_loops               (dfich0_top_2_cfg[`DDR_DFICH_TOP_2_CFG_IG_NUM_LOOPS_FIELD]),
      .i_ig_load_ptr                (dfich0_top_2_cfg[`DDR_DFICH_TOP_2_CFG_IG_LOAD_PTR_FIELD]),
      .i_ig_stop_ptr                (dfich0_top_2_cfg[`DDR_DFICH_TOP_2_CFG_IG_STOP_PTR_FIELD]),
      .i_ig_start_ptr               (dfich0_top_2_cfg[`DDR_DFICH_TOP_2_CFG_IG_START_PTR_FIELD]),
      .i_ig_wdata_clr               (dfich0_top_1_cfg[`DDR_DFICH_TOP_1_CFG_WDATA_CLR_FIELD]),
      .i_ig_wdata_hold              (dfich0_top_1_cfg[`DDR_DFICH_TOP_1_CFG_WDATA_HOLD_FIELD]),
      .i_ig_wdata_en                (dfich0_top_1_cfg[`DDR_DFICH_TOP_1_CFG_WDATA_ENABLE_FIELD]),
      .i_ig_wdata_upd               (dfich0_top_1_cfg[`DDR_DFICH_TOP_1_CFG_WDATA_UPDATE_FIELD]),
      .i_ig_wdata                   (dfich0_ig_data_cfg[`DDR_DFICH_IG_DATA_CFG_WDATA_FIELD]),
      .o_ig_empty                   (dfi_buf_ig_empty),
      .o_ig_write_done              (dfi_buf_ig_write_done),
      .o_ig_full                    (dfi_buf_ig_full),
      .o_ig_overflow                (dfi_buf_ig_overflow),

      .i_eg_rdata_clr               (dfich0_top_1_cfg[`DDR_DFICH_TOP_1_CFG_RDATA_CLR_FIELD]),
      .i_eg_rdata_en                (dfich0_top_1_cfg[`DDR_DFICH_TOP_1_CFG_RDATA_ENABLE_FIELD]),
      .i_eg_rdata_upd               (dfich0_top_1_cfg[`DDR_DFICH_TOP_1_CFG_RDATA_UPDATE_FIELD]),
      .o_eg_rdata                   (dfich0_eg_data_sta[`DDR_DFICH_EG_DATA_STA_RDATA_FIELD]),
      .o_eg_empty                   (dfi_buf_eg_empty),
      .o_eg_full                    (dfi_buf_eg_full),
      .o_eg_read_done               (dfi_buf_eg_read_done),
      .o_eg_overflow                (dfi_buf_eg_overflow),

   // Write Command Address Data
      .i_dfi_address_p0            (i_dfi_address_p0),
      .i_dfi_address_p1            (i_dfi_address_p1),
      .i_dfi_address_p2            (i_dfi_address_p2),
      .i_dfi_address_p3            (i_dfi_address_p3),
      .i_dfi_address_p4            (i_dfi_address_p4),
      .i_dfi_address_p5            (i_dfi_address_p5),
      .i_dfi_address_p6            (i_dfi_address_p6),
      .i_dfi_address_p7            (i_dfi_address_p7),
      .i_dfi_cke_p0                (i_dfi_cke_p0),
      .i_dfi_cke_p1                (i_dfi_cke_p1),
      .i_dfi_cke_p2                (i_dfi_cke_p2),
      .i_dfi_cke_p3                (i_dfi_cke_p3),
      .i_dfi_cke_p4                (i_dfi_cke_p4),
      .i_dfi_cke_p5                (i_dfi_cke_p5),
      .i_dfi_cke_p6                (i_dfi_cke_p6),
      .i_dfi_cke_p7                (i_dfi_cke_p7),
      .i_dfi_cs_p0                 (i_dfi_cs_p0),
      .i_dfi_cs_p1                 (i_dfi_cs_p1),
      .i_dfi_cs_p2                 (i_dfi_cs_p2),
      .i_dfi_cs_p3                 (i_dfi_cs_p3),
      .i_dfi_cs_p4                 (i_dfi_cs_p4),
      .i_dfi_cs_p5                 (i_dfi_cs_p5),
      .i_dfi_cs_p6                 (i_dfi_cs_p6),
      .i_dfi_cs_p7                 (i_dfi_cs_p7),
      .i_dfi_dcd_p0                (i_dfi_dram_clk_disable_p0),
      .i_dfi_dcd_p1                (i_dfi_dram_clk_disable_p1),
      .i_dfi_dcd_p2                (i_dfi_dram_clk_disable_p2),
      .i_dfi_dcd_p3                (i_dfi_dram_clk_disable_p3),
      .i_dfi_dcd_p4                (i_dfi_dram_clk_disable_p4),
      .i_dfi_dcd_p5                (i_dfi_dram_clk_disable_p5),
      .i_dfi_dcd_p6                (i_dfi_dram_clk_disable_p6),
      .i_dfi_dcd_p7                (i_dfi_dram_clk_disable_p7),

      .o_ch0_dfi_address_p0            (ch0_dfi_address_p0),
      .o_ch0_dfi_address_p1            (ch0_dfi_address_p1),
      .o_ch0_dfi_address_p2            (ch0_dfi_address_p2),
      .o_ch0_dfi_address_p3            (ch0_dfi_address_p3),
      .o_ch0_dfi_address_p4            (ch0_dfi_address_p4),
      .o_ch0_dfi_address_p5            (ch0_dfi_address_p5),
      .o_ch0_dfi_address_p6            (ch0_dfi_address_p6),
      .o_ch0_dfi_address_p7            (ch0_dfi_address_p7),
      .o_ch0_dfi_cke_p0                (ch0_dfi_cke_p0),
      .o_ch0_dfi_cke_p1                (ch0_dfi_cke_p1),
      .o_ch0_dfi_cke_p2                (ch0_dfi_cke_p2),
      .o_ch0_dfi_cke_p3                (ch0_dfi_cke_p3),
      .o_ch0_dfi_cke_p4                (ch0_dfi_cke_p4),
      .o_ch0_dfi_cke_p5                (ch0_dfi_cke_p5),
      .o_ch0_dfi_cke_p6                (ch0_dfi_cke_p6),
      .o_ch0_dfi_cke_p7                (ch0_dfi_cke_p7),
      .o_ch0_dfi_cs_p0                 (ch0_dfi_cs_p0),
      .o_ch0_dfi_cs_p1                 (ch0_dfi_cs_p1),
      .o_ch0_dfi_cs_p2                 (ch0_dfi_cs_p2),
      .o_ch0_dfi_cs_p3                 (ch0_dfi_cs_p3),
      .o_ch0_dfi_cs_p4                 (ch0_dfi_cs_p4),
      .o_ch0_dfi_cs_p5                 (ch0_dfi_cs_p5),
      .o_ch0_dfi_cs_p6                 (ch0_dfi_cs_p6),
      .o_ch0_dfi_cs_p7                 (ch0_dfi_cs_p7),
      .o_ch0_dfi_dcd_p0                (ch0_dfi_dram_clk_disable_p0),
      .o_ch0_dfi_dcd_p1                (ch0_dfi_dram_clk_disable_p1),
      .o_ch0_dfi_dcd_p2                (ch0_dfi_dram_clk_disable_p2),
      .o_ch0_dfi_dcd_p3                (ch0_dfi_dram_clk_disable_p3),
      .o_ch0_dfi_dcd_p4                (ch0_dfi_dram_clk_disable_p4),
      .o_ch0_dfi_dcd_p5                (ch0_dfi_dram_clk_disable_p5),
      .o_ch0_dfi_dcd_p6                (ch0_dfi_dram_clk_disable_p6),
      .o_ch0_dfi_dcd_p7                (ch0_dfi_dram_clk_disable_p7),
      .o_ch1_dfi_address_p0            (ch1_dfi_address_p0),
      .o_ch1_dfi_address_p1            (ch1_dfi_address_p1),
      .o_ch1_dfi_address_p2            (ch1_dfi_address_p2),
      .o_ch1_dfi_address_p3            (ch1_dfi_address_p3),
      .o_ch1_dfi_address_p4            (ch1_dfi_address_p4),
      .o_ch1_dfi_address_p5            (ch1_dfi_address_p5),
      .o_ch1_dfi_address_p6            (ch1_dfi_address_p6),
      .o_ch1_dfi_address_p7            (ch1_dfi_address_p7),
      .o_ch1_dfi_cke_p0                (ch1_dfi_cke_p0),
      .o_ch1_dfi_cke_p1                (ch1_dfi_cke_p1),
      .o_ch1_dfi_cke_p2                (ch1_dfi_cke_p2),
      .o_ch1_dfi_cke_p3                (ch1_dfi_cke_p3),
      .o_ch1_dfi_cke_p4                (ch1_dfi_cke_p4),
      .o_ch1_dfi_cke_p5                (ch1_dfi_cke_p5),
      .o_ch1_dfi_cke_p6                (ch1_dfi_cke_p6),
      .o_ch1_dfi_cke_p7                (ch1_dfi_cke_p7),
      .o_ch1_dfi_cs_p0                 (ch1_dfi_cs_p0),
      .o_ch1_dfi_cs_p1                 (ch1_dfi_cs_p1),
      .o_ch1_dfi_cs_p2                 (ch1_dfi_cs_p2),
      .o_ch1_dfi_cs_p3                 (ch1_dfi_cs_p3),
      .o_ch1_dfi_cs_p4                 (ch1_dfi_cs_p4),
      .o_ch1_dfi_cs_p5                 (ch1_dfi_cs_p5),
      .o_ch1_dfi_cs_p6                 (ch1_dfi_cs_p6),
      .o_ch1_dfi_cs_p7                 (ch1_dfi_cs_p7),
      .o_ch1_dfi_dcd_p0                (ch1_dfi_dram_clk_disable_p0),
      .o_ch1_dfi_dcd_p1                (ch1_dfi_dram_clk_disable_p1),
      .o_ch1_dfi_dcd_p2                (ch1_dfi_dram_clk_disable_p2),
      .o_ch1_dfi_dcd_p3                (ch1_dfi_dram_clk_disable_p3),
      .o_ch1_dfi_dcd_p4                (ch1_dfi_dram_clk_disable_p4),
      .o_ch1_dfi_dcd_p5                (ch1_dfi_dram_clk_disable_p5),
      .o_ch1_dfi_dcd_p6                (ch1_dfi_dram_clk_disable_p6),
      .o_ch1_dfi_dcd_p7                (ch1_dfi_dram_clk_disable_p7),

      // Read Command Address Data
      .i_dfi_address_w0            (dfi_address_w0),
      .i_dfi_address_w1            (dfi_address_w1),
      .i_dfi_address_w2            (dfi_address_w2),
      .i_dfi_address_w3            (dfi_address_w3),
      .i_dfi_address_w4            (dfi_address_w4),
      .i_dfi_address_w5            (dfi_address_w5),
      .i_dfi_address_w6            (dfi_address_w6),
      .i_dfi_address_w7            (dfi_address_w7),

      .i_dfi_cke_w0                (dfi_cke_w0),
      .i_dfi_cke_w1                (dfi_cke_w1),
      .i_dfi_cke_w2                (dfi_cke_w2),
      .i_dfi_cke_w3                (dfi_cke_w3),
      .i_dfi_cke_w4                (dfi_cke_w4),
      .i_dfi_cke_w5                (dfi_cke_w5),
      .i_dfi_cke_w6                (dfi_cke_w6),
      .i_dfi_cke_w7                (dfi_cke_w7),

      .i_dfi_cs_w0                 (dfi_cs_w0),
      .i_dfi_cs_w1                 (dfi_cs_w1),
      .i_dfi_cs_w2                 (dfi_cs_w2),
      .i_dfi_cs_w3                 (dfi_cs_w3),
      .i_dfi_cs_w4                 (dfi_cs_w4),
      .i_dfi_cs_w5                 (dfi_cs_w5),
      .i_dfi_cs_w6                 (dfi_cs_w6),
      .i_dfi_cs_w7                 (dfi_cs_w7),

      .i_dfi_address_valid_w0      (dfi_address_valid_w0),
      .i_dfi_address_valid_w1      (dfi_address_valid_w1),
      .i_dfi_address_valid_w2      (dfi_address_valid_w2),
      .i_dfi_address_valid_w3      (dfi_address_valid_w3),
      .i_dfi_address_valid_w4      (dfi_address_valid_w4),
      .i_dfi_address_valid_w5      (dfi_address_valid_w5),
      .i_dfi_address_valid_w6      (dfi_address_valid_w6),
      .i_dfi_address_valid_w7      (dfi_address_valid_w7),

      // Write Data
      .i_dfi_wrdata_p0              (i_dfi_wrdata_p0),
      .i_dfi_wrdata_p1              (i_dfi_wrdata_p1),
      .i_dfi_wrdata_p2              (i_dfi_wrdata_p2),
      .i_dfi_wrdata_p3              (i_dfi_wrdata_p3),
      .i_dfi_wrdata_p4              (i_dfi_wrdata_p4),
      .i_dfi_wrdata_p5              (i_dfi_wrdata_p5),
      .i_dfi_wrdata_p6              (i_dfi_wrdata_p6),
      .i_dfi_wrdata_p7              (i_dfi_wrdata_p7),
      .i_dfi_wrdata_mask_p0         (i_dfi_wrdata_mask_p0),
      .i_dfi_wrdata_mask_p1         (i_dfi_wrdata_mask_p1),
      .i_dfi_wrdata_mask_p2         (i_dfi_wrdata_mask_p2),
      .i_dfi_wrdata_mask_p3         (i_dfi_wrdata_mask_p3),
      .i_dfi_wrdata_mask_p4         (i_dfi_wrdata_mask_p4),
      .i_dfi_wrdata_mask_p5         (i_dfi_wrdata_mask_p5),
      .i_dfi_wrdata_mask_p6         (i_dfi_wrdata_mask_p6),
      .i_dfi_wrdata_mask_p7         (i_dfi_wrdata_mask_p7),

      .o_ch0_dq0_dfi_wrdata_p0          (ch0_dq0_dfi_wrdata_p0),
      .o_ch0_dq0_dfi_wrdata_p1          (ch0_dq0_dfi_wrdata_p1),
      .o_ch0_dq0_dfi_wrdata_p2          (ch0_dq0_dfi_wrdata_p2),
      .o_ch0_dq0_dfi_wrdata_p3          (ch0_dq0_dfi_wrdata_p3),
      .o_ch0_dq0_dfi_wrdata_p4          (ch0_dq0_dfi_wrdata_p4),
      .o_ch0_dq0_dfi_wrdata_p5          (ch0_dq0_dfi_wrdata_p5),
      .o_ch0_dq0_dfi_wrdata_p6          (ch0_dq0_dfi_wrdata_p6),
      .o_ch0_dq0_dfi_wrdata_p7          (ch0_dq0_dfi_wrdata_p7),
      .o_ch0_dq1_dfi_wrdata_p0          (ch0_dq1_dfi_wrdata_p0),
      .o_ch0_dq1_dfi_wrdata_p1          (ch0_dq1_dfi_wrdata_p1),
      .o_ch0_dq1_dfi_wrdata_p2          (ch0_dq1_dfi_wrdata_p2),
      .o_ch0_dq1_dfi_wrdata_p3          (ch0_dq1_dfi_wrdata_p3),
      .o_ch0_dq1_dfi_wrdata_p4          (ch0_dq1_dfi_wrdata_p4),
      .o_ch0_dq1_dfi_wrdata_p5          (ch0_dq1_dfi_wrdata_p5),
      .o_ch0_dq1_dfi_wrdata_p6          (ch0_dq1_dfi_wrdata_p6),
      .o_ch0_dq1_dfi_wrdata_p7          (ch0_dq1_dfi_wrdata_p7),
      .o_ch0_dq0_dfi_wrdata_mask_p0     (ch0_dq0_dfi_wrdata_mask_p0),
      .o_ch0_dq0_dfi_wrdata_mask_p1     (ch0_dq0_dfi_wrdata_mask_p1),
      .o_ch0_dq0_dfi_wrdata_mask_p2     (ch0_dq0_dfi_wrdata_mask_p2),
      .o_ch0_dq0_dfi_wrdata_mask_p3     (ch0_dq0_dfi_wrdata_mask_p3),
      .o_ch0_dq0_dfi_wrdata_mask_p4     (ch0_dq0_dfi_wrdata_mask_p4),
      .o_ch0_dq0_dfi_wrdata_mask_p5     (ch0_dq0_dfi_wrdata_mask_p5),
      .o_ch0_dq0_dfi_wrdata_mask_p6     (ch0_dq0_dfi_wrdata_mask_p6),
      .o_ch0_dq0_dfi_wrdata_mask_p7     (ch0_dq0_dfi_wrdata_mask_p7),
      .o_ch0_dq1_dfi_wrdata_mask_p0     (ch0_dq1_dfi_wrdata_mask_p0),
      .o_ch0_dq1_dfi_wrdata_mask_p1     (ch0_dq1_dfi_wrdata_mask_p1),
      .o_ch0_dq1_dfi_wrdata_mask_p2     (ch0_dq1_dfi_wrdata_mask_p2),
      .o_ch0_dq1_dfi_wrdata_mask_p3     (ch0_dq1_dfi_wrdata_mask_p3),
      .o_ch0_dq1_dfi_wrdata_mask_p4     (ch0_dq1_dfi_wrdata_mask_p4),
      .o_ch0_dq1_dfi_wrdata_mask_p5     (ch0_dq1_dfi_wrdata_mask_p5),
      .o_ch0_dq1_dfi_wrdata_mask_p6     (ch0_dq1_dfi_wrdata_mask_p6),
      .o_ch0_dq1_dfi_wrdata_mask_p7     (ch0_dq1_dfi_wrdata_mask_p7),
      .o_ch1_dq0_dfi_wrdata_p0          (ch1_dq0_dfi_wrdata_p0),
      .o_ch1_dq0_dfi_wrdata_p1          (ch1_dq0_dfi_wrdata_p1),
      .o_ch1_dq0_dfi_wrdata_p2          (ch1_dq0_dfi_wrdata_p2),
      .o_ch1_dq0_dfi_wrdata_p3          (ch1_dq0_dfi_wrdata_p3),
      .o_ch1_dq0_dfi_wrdata_p4          (ch1_dq0_dfi_wrdata_p4),
      .o_ch1_dq0_dfi_wrdata_p5          (ch1_dq0_dfi_wrdata_p5),
      .o_ch1_dq0_dfi_wrdata_p6          (ch1_dq0_dfi_wrdata_p6),
      .o_ch1_dq0_dfi_wrdata_p7          (ch1_dq0_dfi_wrdata_p7),
      .o_ch1_dq1_dfi_wrdata_p0          (ch1_dq1_dfi_wrdata_p0),
      .o_ch1_dq1_dfi_wrdata_p1          (ch1_dq1_dfi_wrdata_p1),
      .o_ch1_dq1_dfi_wrdata_p2          (ch1_dq1_dfi_wrdata_p2),
      .o_ch1_dq1_dfi_wrdata_p3          (ch1_dq1_dfi_wrdata_p3),
      .o_ch1_dq1_dfi_wrdata_p4          (ch1_dq1_dfi_wrdata_p4),
      .o_ch1_dq1_dfi_wrdata_p5          (ch1_dq1_dfi_wrdata_p5),
      .o_ch1_dq1_dfi_wrdata_p6          (ch1_dq1_dfi_wrdata_p6),
      .o_ch1_dq1_dfi_wrdata_p7          (ch1_dq1_dfi_wrdata_p7),
      .o_ch1_dq0_dfi_wrdata_mask_p0     (ch1_dq0_dfi_wrdata_mask_p0),
      .o_ch1_dq0_dfi_wrdata_mask_p1     (ch1_dq0_dfi_wrdata_mask_p1),
      .o_ch1_dq0_dfi_wrdata_mask_p2     (ch1_dq0_dfi_wrdata_mask_p2),
      .o_ch1_dq0_dfi_wrdata_mask_p3     (ch1_dq0_dfi_wrdata_mask_p3),
      .o_ch1_dq0_dfi_wrdata_mask_p4     (ch1_dq0_dfi_wrdata_mask_p4),
      .o_ch1_dq0_dfi_wrdata_mask_p5     (ch1_dq0_dfi_wrdata_mask_p5),
      .o_ch1_dq0_dfi_wrdata_mask_p6     (ch1_dq0_dfi_wrdata_mask_p6),
      .o_ch1_dq0_dfi_wrdata_mask_p7     (ch1_dq0_dfi_wrdata_mask_p7),
      .o_ch1_dq1_dfi_wrdata_mask_p0     (ch1_dq1_dfi_wrdata_mask_p0),
      .o_ch1_dq1_dfi_wrdata_mask_p1     (ch1_dq1_dfi_wrdata_mask_p1),
      .o_ch1_dq1_dfi_wrdata_mask_p2     (ch1_dq1_dfi_wrdata_mask_p2),
      .o_ch1_dq1_dfi_wrdata_mask_p3     (ch1_dq1_dfi_wrdata_mask_p3),
      .o_ch1_dq1_dfi_wrdata_mask_p4     (ch1_dq1_dfi_wrdata_mask_p4),
      .o_ch1_dq1_dfi_wrdata_mask_p5     (ch1_dq1_dfi_wrdata_mask_p5),
      .o_ch1_dq1_dfi_wrdata_mask_p6     (ch1_dq1_dfi_wrdata_mask_p6),
      .o_ch1_dq1_dfi_wrdata_mask_p7     (ch1_dq1_dfi_wrdata_mask_p7),

      // Write Enable/WCK
      .i_dfi_wrdata_en_p0           (i_dfi_wrdata_en_p0),
      .i_dfi_wrdata_en_p1           (i_dfi_wrdata_en_p1),
      .i_dfi_wrdata_en_p2           (i_dfi_wrdata_en_p2),
      .i_dfi_wrdata_en_p3           (i_dfi_wrdata_en_p3),
      .i_dfi_wrdata_en_p4           (i_dfi_wrdata_en_p4),
      .i_dfi_wrdata_en_p5           (i_dfi_wrdata_en_p5),
      .i_dfi_wrdata_en_p6           (i_dfi_wrdata_en_p6),
      .i_dfi_wrdata_en_p7           (i_dfi_wrdata_en_p7),
      .i_dfi_parity_in_p0           (i_dfi_parity_in_p0),
      .i_dfi_parity_in_p1           (i_dfi_parity_in_p1),
      .i_dfi_parity_in_p2           (i_dfi_parity_in_p2),
      .i_dfi_parity_in_p3           (i_dfi_parity_in_p3),
      .i_dfi_parity_in_p4           (i_dfi_parity_in_p4),
      .i_dfi_parity_in_p5           (i_dfi_parity_in_p5),
      .i_dfi_parity_in_p6           (i_dfi_parity_in_p6),
      .i_dfi_parity_in_p7           (i_dfi_parity_in_p7),
      .i_dfi_wrdata_cs_p0           (i_dfi_wrdata_cs_p0),
      .i_dfi_wrdata_cs_p1           (i_dfi_wrdata_cs_p1),
      .i_dfi_wrdata_cs_p2           (i_dfi_wrdata_cs_p2),
      .i_dfi_wrdata_cs_p3           (i_dfi_wrdata_cs_p3),
      .i_dfi_wrdata_cs_p4           (i_dfi_wrdata_cs_p4),
      .i_dfi_wrdata_cs_p5           (i_dfi_wrdata_cs_p5),
      .i_dfi_wrdata_cs_p6           (i_dfi_wrdata_cs_p6),
      .i_dfi_wrdata_cs_p7           (i_dfi_wrdata_cs_p7),

      .o_ch0_dq0_dfi_wrdata_en_p0           (ch0_dq0_dfi_wrdata_en_p0),
      .o_ch0_dq0_dfi_wrdata_en_p1           (ch0_dq0_dfi_wrdata_en_p1),
      .o_ch0_dq0_dfi_wrdata_en_p2           (ch0_dq0_dfi_wrdata_en_p2),
      .o_ch0_dq0_dfi_wrdata_en_p3           (ch0_dq0_dfi_wrdata_en_p3),
      .o_ch0_dq0_dfi_wrdata_en_p4           (ch0_dq0_dfi_wrdata_en_p4),
      .o_ch0_dq0_dfi_wrdata_en_p5           (ch0_dq0_dfi_wrdata_en_p5),
      .o_ch0_dq0_dfi_wrdata_en_p6           (ch0_dq0_dfi_wrdata_en_p6),
      .o_ch0_dq0_dfi_wrdata_en_p7           (ch0_dq0_dfi_wrdata_en_p7),
      .o_ch0_dq0_dfi_parity_in_p0           (ch0_dq0_dfi_parity_in_p0),
      .o_ch0_dq0_dfi_parity_in_p1           (ch0_dq0_dfi_parity_in_p1),
      .o_ch0_dq0_dfi_parity_in_p2           (ch0_dq0_dfi_parity_in_p2),
      .o_ch0_dq0_dfi_parity_in_p3           (ch0_dq0_dfi_parity_in_p3),
      .o_ch0_dq0_dfi_parity_in_p4           (ch0_dq0_dfi_parity_in_p4),
      .o_ch0_dq0_dfi_parity_in_p5           (ch0_dq0_dfi_parity_in_p5),
      .o_ch0_dq0_dfi_parity_in_p6           (ch0_dq0_dfi_parity_in_p6),
      .o_ch0_dq0_dfi_parity_in_p7           (ch0_dq0_dfi_parity_in_p7),
      .o_ch0_dq0_dfi_wrdata_cs_p0           (ch0_dq0_dfi_wrdata_cs_p0),
      .o_ch0_dq0_dfi_wrdata_cs_p1           (ch0_dq0_dfi_wrdata_cs_p1),
      .o_ch0_dq0_dfi_wrdata_cs_p2           (ch0_dq0_dfi_wrdata_cs_p2),
      .o_ch0_dq0_dfi_wrdata_cs_p3           (ch0_dq0_dfi_wrdata_cs_p3),
      .o_ch0_dq0_dfi_wrdata_cs_p4           (ch0_dq0_dfi_wrdata_cs_p4),
      .o_ch0_dq0_dfi_wrdata_cs_p5           (ch0_dq0_dfi_wrdata_cs_p5),
      .o_ch0_dq0_dfi_wrdata_cs_p6           (ch0_dq0_dfi_wrdata_cs_p6),
      .o_ch0_dq0_dfi_wrdata_cs_p7           (ch0_dq0_dfi_wrdata_cs_p7),
      .o_ch0_dq1_dfi_wrdata_en_p0           (ch0_dq1_dfi_wrdata_en_p0),
      .o_ch0_dq1_dfi_wrdata_en_p1           (ch0_dq1_dfi_wrdata_en_p1),
      .o_ch0_dq1_dfi_wrdata_en_p2           (ch0_dq1_dfi_wrdata_en_p2),
      .o_ch0_dq1_dfi_wrdata_en_p3           (ch0_dq1_dfi_wrdata_en_p3),
      .o_ch0_dq1_dfi_wrdata_en_p4           (ch0_dq1_dfi_wrdata_en_p4),
      .o_ch0_dq1_dfi_wrdata_en_p5           (ch0_dq1_dfi_wrdata_en_p5),
      .o_ch0_dq1_dfi_wrdata_en_p6           (ch0_dq1_dfi_wrdata_en_p6),
      .o_ch0_dq1_dfi_wrdata_en_p7           (ch0_dq1_dfi_wrdata_en_p7),
      .o_ch0_dq1_dfi_parity_in_p0           (ch0_dq1_dfi_parity_in_p0),
      .o_ch0_dq1_dfi_parity_in_p1           (ch0_dq1_dfi_parity_in_p1),
      .o_ch0_dq1_dfi_parity_in_p2           (ch0_dq1_dfi_parity_in_p2),
      .o_ch0_dq1_dfi_parity_in_p3           (ch0_dq1_dfi_parity_in_p3),
      .o_ch0_dq1_dfi_parity_in_p4           (ch0_dq1_dfi_parity_in_p4),
      .o_ch0_dq1_dfi_parity_in_p5           (ch0_dq1_dfi_parity_in_p5),
      .o_ch0_dq1_dfi_parity_in_p6           (ch0_dq1_dfi_parity_in_p6),
      .o_ch0_dq1_dfi_parity_in_p7           (ch0_dq1_dfi_parity_in_p7),
      .o_ch0_dq1_dfi_wrdata_cs_p0           (ch0_dq1_dfi_wrdata_cs_p0),
      .o_ch0_dq1_dfi_wrdata_cs_p1           (ch0_dq1_dfi_wrdata_cs_p1),
      .o_ch0_dq1_dfi_wrdata_cs_p2           (ch0_dq1_dfi_wrdata_cs_p2),
      .o_ch0_dq1_dfi_wrdata_cs_p3           (ch0_dq1_dfi_wrdata_cs_p3),
      .o_ch0_dq1_dfi_wrdata_cs_p4           (ch0_dq1_dfi_wrdata_cs_p4),
      .o_ch0_dq1_dfi_wrdata_cs_p5           (ch0_dq1_dfi_wrdata_cs_p5),
      .o_ch0_dq1_dfi_wrdata_cs_p6           (ch0_dq1_dfi_wrdata_cs_p6),
      .o_ch0_dq1_dfi_wrdata_cs_p7           (ch0_dq1_dfi_wrdata_cs_p7),
      .o_ch1_dq0_dfi_wrdata_en_p0           (ch1_dq0_dfi_wrdata_en_p0),
      .o_ch1_dq0_dfi_wrdata_en_p1           (ch1_dq0_dfi_wrdata_en_p1),
      .o_ch1_dq0_dfi_wrdata_en_p2           (ch1_dq0_dfi_wrdata_en_p2),
      .o_ch1_dq0_dfi_wrdata_en_p3           (ch1_dq0_dfi_wrdata_en_p3),
      .o_ch1_dq0_dfi_wrdata_en_p4           (ch1_dq0_dfi_wrdata_en_p4),
      .o_ch1_dq0_dfi_wrdata_en_p5           (ch1_dq0_dfi_wrdata_en_p5),
      .o_ch1_dq0_dfi_wrdata_en_p6           (ch1_dq0_dfi_wrdata_en_p6),
      .o_ch1_dq0_dfi_wrdata_en_p7           (ch1_dq0_dfi_wrdata_en_p7),
      .o_ch1_dq0_dfi_parity_in_p0           (ch1_dq0_dfi_parity_in_p0),
      .o_ch1_dq0_dfi_parity_in_p1           (ch1_dq0_dfi_parity_in_p1),
      .o_ch1_dq0_dfi_parity_in_p2           (ch1_dq0_dfi_parity_in_p2),
      .o_ch1_dq0_dfi_parity_in_p3           (ch1_dq0_dfi_parity_in_p3),
      .o_ch1_dq0_dfi_parity_in_p4           (ch1_dq0_dfi_parity_in_p4),
      .o_ch1_dq0_dfi_parity_in_p5           (ch1_dq0_dfi_parity_in_p5),
      .o_ch1_dq0_dfi_parity_in_p6           (ch1_dq0_dfi_parity_in_p6),
      .o_ch1_dq0_dfi_parity_in_p7           (ch1_dq0_dfi_parity_in_p7),
      .o_ch1_dq0_dfi_wrdata_cs_p0           (ch1_dq0_dfi_wrdata_cs_p0),
      .o_ch1_dq0_dfi_wrdata_cs_p1           (ch1_dq0_dfi_wrdata_cs_p1),
      .o_ch1_dq0_dfi_wrdata_cs_p2           (ch1_dq0_dfi_wrdata_cs_p2),
      .o_ch1_dq0_dfi_wrdata_cs_p3           (ch1_dq0_dfi_wrdata_cs_p3),
      .o_ch1_dq0_dfi_wrdata_cs_p4           (ch1_dq0_dfi_wrdata_cs_p4),
      .o_ch1_dq0_dfi_wrdata_cs_p5           (ch1_dq0_dfi_wrdata_cs_p5),
      .o_ch1_dq0_dfi_wrdata_cs_p6           (ch1_dq0_dfi_wrdata_cs_p6),
      .o_ch1_dq0_dfi_wrdata_cs_p7           (ch1_dq0_dfi_wrdata_cs_p7),
      .o_ch1_dq1_dfi_wrdata_en_p0           (ch1_dq1_dfi_wrdata_en_p0),
      .o_ch1_dq1_dfi_wrdata_en_p1           (ch1_dq1_dfi_wrdata_en_p1),
      .o_ch1_dq1_dfi_wrdata_en_p2           (ch1_dq1_dfi_wrdata_en_p2),
      .o_ch1_dq1_dfi_wrdata_en_p3           (ch1_dq1_dfi_wrdata_en_p3),
      .o_ch1_dq1_dfi_wrdata_en_p4           (ch1_dq1_dfi_wrdata_en_p4),
      .o_ch1_dq1_dfi_wrdata_en_p5           (ch1_dq1_dfi_wrdata_en_p5),
      .o_ch1_dq1_dfi_wrdata_en_p6           (ch1_dq1_dfi_wrdata_en_p6),
      .o_ch1_dq1_dfi_wrdata_en_p7           (ch1_dq1_dfi_wrdata_en_p7),
      .o_ch1_dq1_dfi_parity_in_p0           (ch1_dq1_dfi_parity_in_p0),
      .o_ch1_dq1_dfi_parity_in_p1           (ch1_dq1_dfi_parity_in_p1),
      .o_ch1_dq1_dfi_parity_in_p2           (ch1_dq1_dfi_parity_in_p2),
      .o_ch1_dq1_dfi_parity_in_p3           (ch1_dq1_dfi_parity_in_p3),
      .o_ch1_dq1_dfi_parity_in_p4           (ch1_dq1_dfi_parity_in_p4),
      .o_ch1_dq1_dfi_parity_in_p5           (ch1_dq1_dfi_parity_in_p5),
      .o_ch1_dq1_dfi_parity_in_p6           (ch1_dq1_dfi_parity_in_p6),
      .o_ch1_dq1_dfi_parity_in_p7           (ch1_dq1_dfi_parity_in_p7),
      .o_ch1_dq1_dfi_wrdata_cs_p0           (ch1_dq1_dfi_wrdata_cs_p0),
      .o_ch1_dq1_dfi_wrdata_cs_p1           (ch1_dq1_dfi_wrdata_cs_p1),
      .o_ch1_dq1_dfi_wrdata_cs_p2           (ch1_dq1_dfi_wrdata_cs_p2),
      .o_ch1_dq1_dfi_wrdata_cs_p3           (ch1_dq1_dfi_wrdata_cs_p3),
      .o_ch1_dq1_dfi_wrdata_cs_p4           (ch1_dq1_dfi_wrdata_cs_p4),
      .o_ch1_dq1_dfi_wrdata_cs_p5           (ch1_dq1_dfi_wrdata_cs_p5),
      .o_ch1_dq1_dfi_wrdata_cs_p6           (ch1_dq1_dfi_wrdata_cs_p6),
      .o_ch1_dq1_dfi_wrdata_cs_p7           (ch1_dq1_dfi_wrdata_cs_p7),

      .i_dfi_wck_cs_p0              (i_dfi_wck_cs_p0),
      .i_dfi_wck_cs_p1              (i_dfi_wck_cs_p1),
      .i_dfi_wck_cs_p2              (i_dfi_wck_cs_p2),
      .i_dfi_wck_cs_p3              (i_dfi_wck_cs_p3),
      .i_dfi_wck_cs_p4              (i_dfi_wck_cs_p4),
      .i_dfi_wck_cs_p5              (i_dfi_wck_cs_p5),
      .i_dfi_wck_cs_p6              (i_dfi_wck_cs_p6),
      .i_dfi_wck_cs_p7              (i_dfi_wck_cs_p7),
      .i_dfi_wck_en_p0              (i_dfi_wck_en_p0),
      .i_dfi_wck_en_p1              (i_dfi_wck_en_p1),
      .i_dfi_wck_en_p2              (i_dfi_wck_en_p2),
      .i_dfi_wck_en_p3              (i_dfi_wck_en_p3),
      .i_dfi_wck_en_p4              (i_dfi_wck_en_p4),
      .i_dfi_wck_en_p5              (i_dfi_wck_en_p5),
      .i_dfi_wck_en_p6              (i_dfi_wck_en_p6),
      .i_dfi_wck_en_p7              (i_dfi_wck_en_p7),
      .i_dfi_wck_toggle_p0          (i_dfi_wck_toggle_p0),
      .i_dfi_wck_toggle_p1          (i_dfi_wck_toggle_p1),
      .i_dfi_wck_toggle_p2          (i_dfi_wck_toggle_p2),
      .i_dfi_wck_toggle_p3          (i_dfi_wck_toggle_p3),
      .i_dfi_wck_toggle_p4          (i_dfi_wck_toggle_p4),
      .i_dfi_wck_toggle_p5          (i_dfi_wck_toggle_p5),
      .i_dfi_wck_toggle_p6          (i_dfi_wck_toggle_p6),
      .i_dfi_wck_toggle_p7          (i_dfi_wck_toggle_p7),

      .o_ch0_dq0_dfi_wck_cs_p0              (ch0_dq0_dfi_wck_cs_p0),
      .o_ch0_dq0_dfi_wck_cs_p1              (ch0_dq0_dfi_wck_cs_p1),
      .o_ch0_dq0_dfi_wck_cs_p2              (ch0_dq0_dfi_wck_cs_p2),
      .o_ch0_dq0_dfi_wck_cs_p3              (ch0_dq0_dfi_wck_cs_p3),
      .o_ch0_dq0_dfi_wck_cs_p4              (ch0_dq0_dfi_wck_cs_p4),
      .o_ch0_dq0_dfi_wck_cs_p5              (ch0_dq0_dfi_wck_cs_p5),
      .o_ch0_dq0_dfi_wck_cs_p6              (ch0_dq0_dfi_wck_cs_p6),
      .o_ch0_dq0_dfi_wck_cs_p7              (ch0_dq0_dfi_wck_cs_p7),
      .o_ch0_dq0_dfi_wck_en_p0              (ch0_dq0_dfi_wck_en_p0),
      .o_ch0_dq0_dfi_wck_en_p1              (ch0_dq0_dfi_wck_en_p1),
      .o_ch0_dq0_dfi_wck_en_p2              (ch0_dq0_dfi_wck_en_p2),
      .o_ch0_dq0_dfi_wck_en_p3              (ch0_dq0_dfi_wck_en_p3),
      .o_ch0_dq0_dfi_wck_en_p4              (ch0_dq0_dfi_wck_en_p4),
      .o_ch0_dq0_dfi_wck_en_p5              (ch0_dq0_dfi_wck_en_p5),
      .o_ch0_dq0_dfi_wck_en_p6              (ch0_dq0_dfi_wck_en_p6),
      .o_ch0_dq0_dfi_wck_en_p7              (ch0_dq0_dfi_wck_en_p7),
      .o_ch0_dq0_dfi_wck_toggle_p0          (ch0_dq0_dfi_wck_toggle_p0),
      .o_ch0_dq0_dfi_wck_toggle_p1          (ch0_dq0_dfi_wck_toggle_p1),
      .o_ch0_dq0_dfi_wck_toggle_p2          (ch0_dq0_dfi_wck_toggle_p2),
      .o_ch0_dq0_dfi_wck_toggle_p3          (ch0_dq0_dfi_wck_toggle_p3),
      .o_ch0_dq0_dfi_wck_toggle_p4          (ch0_dq0_dfi_wck_toggle_p4),
      .o_ch0_dq0_dfi_wck_toggle_p5          (ch0_dq0_dfi_wck_toggle_p5),
      .o_ch0_dq0_dfi_wck_toggle_p6          (ch0_dq0_dfi_wck_toggle_p6),
      .o_ch0_dq0_dfi_wck_toggle_p7          (ch0_dq0_dfi_wck_toggle_p7),
      .o_ch0_dq1_dfi_wck_cs_p0              (ch0_dq1_dfi_wck_cs_p0),
      .o_ch0_dq1_dfi_wck_cs_p1              (ch0_dq1_dfi_wck_cs_p1),
      .o_ch0_dq1_dfi_wck_cs_p2              (ch0_dq1_dfi_wck_cs_p2),
      .o_ch0_dq1_dfi_wck_cs_p3              (ch0_dq1_dfi_wck_cs_p3),
      .o_ch0_dq1_dfi_wck_cs_p4              (ch0_dq1_dfi_wck_cs_p4),
      .o_ch0_dq1_dfi_wck_cs_p5              (ch0_dq1_dfi_wck_cs_p5),
      .o_ch0_dq1_dfi_wck_cs_p6              (ch0_dq1_dfi_wck_cs_p6),
      .o_ch0_dq1_dfi_wck_cs_p7              (ch0_dq1_dfi_wck_cs_p7),
      .o_ch0_dq1_dfi_wck_en_p0              (ch0_dq1_dfi_wck_en_p0),
      .o_ch0_dq1_dfi_wck_en_p1              (ch0_dq1_dfi_wck_en_p1),
      .o_ch0_dq1_dfi_wck_en_p2              (ch0_dq1_dfi_wck_en_p2),
      .o_ch0_dq1_dfi_wck_en_p3              (ch0_dq1_dfi_wck_en_p3),
      .o_ch0_dq1_dfi_wck_en_p4              (ch0_dq1_dfi_wck_en_p4),
      .o_ch0_dq1_dfi_wck_en_p5              (ch0_dq1_dfi_wck_en_p5),
      .o_ch0_dq1_dfi_wck_en_p6              (ch0_dq1_dfi_wck_en_p6),
      .o_ch0_dq1_dfi_wck_en_p7              (ch0_dq1_dfi_wck_en_p7),
      .o_ch0_dq1_dfi_wck_toggle_p0          (ch0_dq1_dfi_wck_toggle_p0),
      .o_ch0_dq1_dfi_wck_toggle_p1          (ch0_dq1_dfi_wck_toggle_p1),
      .o_ch0_dq1_dfi_wck_toggle_p2          (ch0_dq1_dfi_wck_toggle_p2),
      .o_ch0_dq1_dfi_wck_toggle_p3          (ch0_dq1_dfi_wck_toggle_p3),
      .o_ch0_dq1_dfi_wck_toggle_p4          (ch0_dq1_dfi_wck_toggle_p4),
      .o_ch0_dq1_dfi_wck_toggle_p5          (ch0_dq1_dfi_wck_toggle_p5),
      .o_ch0_dq1_dfi_wck_toggle_p6          (ch0_dq1_dfi_wck_toggle_p6),
      .o_ch0_dq1_dfi_wck_toggle_p7          (ch0_dq1_dfi_wck_toggle_p7),
      .o_ch1_dq0_dfi_wck_cs_p0              (ch1_dq0_dfi_wck_cs_p0),
      .o_ch1_dq0_dfi_wck_cs_p1              (ch1_dq0_dfi_wck_cs_p1),
      .o_ch1_dq0_dfi_wck_cs_p2              (ch1_dq0_dfi_wck_cs_p2),
      .o_ch1_dq0_dfi_wck_cs_p3              (ch1_dq0_dfi_wck_cs_p3),
      .o_ch1_dq0_dfi_wck_cs_p4              (ch1_dq0_dfi_wck_cs_p4),
      .o_ch1_dq0_dfi_wck_cs_p5              (ch1_dq0_dfi_wck_cs_p5),
      .o_ch1_dq0_dfi_wck_cs_p6              (ch1_dq0_dfi_wck_cs_p6),
      .o_ch1_dq0_dfi_wck_cs_p7              (ch1_dq0_dfi_wck_cs_p7),
      .o_ch1_dq0_dfi_wck_en_p0              (ch1_dq0_dfi_wck_en_p0),
      .o_ch1_dq0_dfi_wck_en_p1              (ch1_dq0_dfi_wck_en_p1),
      .o_ch1_dq0_dfi_wck_en_p2              (ch1_dq0_dfi_wck_en_p2),
      .o_ch1_dq0_dfi_wck_en_p3              (ch1_dq0_dfi_wck_en_p3),
      .o_ch1_dq0_dfi_wck_en_p4              (ch1_dq0_dfi_wck_en_p4),
      .o_ch1_dq0_dfi_wck_en_p5              (ch1_dq0_dfi_wck_en_p5),
      .o_ch1_dq0_dfi_wck_en_p6              (ch1_dq0_dfi_wck_en_p6),
      .o_ch1_dq0_dfi_wck_en_p7              (ch1_dq0_dfi_wck_en_p7),
      .o_ch1_dq0_dfi_wck_toggle_p0          (ch1_dq0_dfi_wck_toggle_p0),
      .o_ch1_dq0_dfi_wck_toggle_p1          (ch1_dq0_dfi_wck_toggle_p1),
      .o_ch1_dq0_dfi_wck_toggle_p2          (ch1_dq0_dfi_wck_toggle_p2),
      .o_ch1_dq0_dfi_wck_toggle_p3          (ch1_dq0_dfi_wck_toggle_p3),
      .o_ch1_dq0_dfi_wck_toggle_p4          (ch1_dq0_dfi_wck_toggle_p4),
      .o_ch1_dq0_dfi_wck_toggle_p5          (ch1_dq0_dfi_wck_toggle_p5),
      .o_ch1_dq0_dfi_wck_toggle_p6          (ch1_dq0_dfi_wck_toggle_p6),
      .o_ch1_dq0_dfi_wck_toggle_p7          (ch1_dq0_dfi_wck_toggle_p7),
      .o_ch1_dq1_dfi_wck_cs_p0              (ch1_dq1_dfi_wck_cs_p0),
      .o_ch1_dq1_dfi_wck_cs_p1              (ch1_dq1_dfi_wck_cs_p1),
      .o_ch1_dq1_dfi_wck_cs_p2              (ch1_dq1_dfi_wck_cs_p2),
      .o_ch1_dq1_dfi_wck_cs_p3              (ch1_dq1_dfi_wck_cs_p3),
      .o_ch1_dq1_dfi_wck_cs_p4              (ch1_dq1_dfi_wck_cs_p4),
      .o_ch1_dq1_dfi_wck_cs_p5              (ch1_dq1_dfi_wck_cs_p5),
      .o_ch1_dq1_dfi_wck_cs_p6              (ch1_dq1_dfi_wck_cs_p6),
      .o_ch1_dq1_dfi_wck_cs_p7              (ch1_dq1_dfi_wck_cs_p7),
      .o_ch1_dq1_dfi_wck_en_p0              (ch1_dq1_dfi_wck_en_p0),
      .o_ch1_dq1_dfi_wck_en_p1              (ch1_dq1_dfi_wck_en_p1),
      .o_ch1_dq1_dfi_wck_en_p2              (ch1_dq1_dfi_wck_en_p2),
      .o_ch1_dq1_dfi_wck_en_p3              (ch1_dq1_dfi_wck_en_p3),
      .o_ch1_dq1_dfi_wck_en_p4              (ch1_dq1_dfi_wck_en_p4),
      .o_ch1_dq1_dfi_wck_en_p5              (ch1_dq1_dfi_wck_en_p5),
      .o_ch1_dq1_dfi_wck_en_p6              (ch1_dq1_dfi_wck_en_p6),
      .o_ch1_dq1_dfi_wck_en_p7              (ch1_dq1_dfi_wck_en_p7),
      .o_ch1_dq1_dfi_wck_toggle_p0          (ch1_dq1_dfi_wck_toggle_p0),
      .o_ch1_dq1_dfi_wck_toggle_p1          (ch1_dq1_dfi_wck_toggle_p1),
      .o_ch1_dq1_dfi_wck_toggle_p2          (ch1_dq1_dfi_wck_toggle_p2),
      .o_ch1_dq1_dfi_wck_toggle_p3          (ch1_dq1_dfi_wck_toggle_p3),
      .o_ch1_dq1_dfi_wck_toggle_p4          (ch1_dq1_dfi_wck_toggle_p4),
      .o_ch1_dq1_dfi_wck_toggle_p5          (ch1_dq1_dfi_wck_toggle_p5),
      .o_ch1_dq1_dfi_wck_toggle_p6          (ch1_dq1_dfi_wck_toggle_p6),
      .o_ch1_dq1_dfi_wck_toggle_p7          (ch1_dq1_dfi_wck_toggle_p7),

      // Read Data
      .i_dfi_rddata_cs_p0           (i_dfi_rddata_cs_p0),
      .i_dfi_rddata_cs_p1           (i_dfi_rddata_cs_p1),
      .i_dfi_rddata_cs_p2           (i_dfi_rddata_cs_p2),
      .i_dfi_rddata_cs_p3           (i_dfi_rddata_cs_p3),
      .i_dfi_rddata_cs_p4           (i_dfi_rddata_cs_p4),
      .i_dfi_rddata_cs_p5           (i_dfi_rddata_cs_p5),
      .i_dfi_rddata_cs_p6           (i_dfi_rddata_cs_p6),
      .i_dfi_rddata_cs_p7           (i_dfi_rddata_cs_p7),
      .i_dfi_rddata_en_p0           (i_dfi_rddata_en_p0),
      .i_dfi_rddata_en_p1           (i_dfi_rddata_en_p1),
      .i_dfi_rddata_en_p2           (i_dfi_rddata_en_p2),
      .i_dfi_rddata_en_p3           (i_dfi_rddata_en_p3),
      .i_dfi_rddata_en_p4           (i_dfi_rddata_en_p4),
      .i_dfi_rddata_en_p5           (i_dfi_rddata_en_p5),
      .i_dfi_rddata_en_p6           (i_dfi_rddata_en_p6),
      .i_dfi_rddata_en_p7           (i_dfi_rddata_en_p7),

      .o_ch0_dq0_dfi_rddata_cs_p0           (ch0_dq0_dfi_rddata_cs_p0),
      .o_ch0_dq0_dfi_rddata_cs_p1           (ch0_dq0_dfi_rddata_cs_p1),
      .o_ch0_dq0_dfi_rddata_cs_p2           (ch0_dq0_dfi_rddata_cs_p2),
      .o_ch0_dq0_dfi_rddata_cs_p3           (ch0_dq0_dfi_rddata_cs_p3),
      .o_ch0_dq0_dfi_rddata_cs_p4           (ch0_dq0_dfi_rddata_cs_p4),
      .o_ch0_dq0_dfi_rddata_cs_p5           (ch0_dq0_dfi_rddata_cs_p5),
      .o_ch0_dq0_dfi_rddata_cs_p6           (ch0_dq0_dfi_rddata_cs_p6),
      .o_ch0_dq0_dfi_rddata_cs_p7           (ch0_dq0_dfi_rddata_cs_p7),
      .o_ch0_dq0_dfi_rddata_en_p0           (ch0_dq0_dfi_rddata_en_p0),
      .o_ch0_dq0_dfi_rddata_en_p1           (ch0_dq0_dfi_rddata_en_p1),
      .o_ch0_dq0_dfi_rddata_en_p2           (ch0_dq0_dfi_rddata_en_p2),
      .o_ch0_dq0_dfi_rddata_en_p3           (ch0_dq0_dfi_rddata_en_p3),
      .o_ch0_dq0_dfi_rddata_en_p4           (ch0_dq0_dfi_rddata_en_p4),
      .o_ch0_dq0_dfi_rddata_en_p5           (ch0_dq0_dfi_rddata_en_p5),
      .o_ch0_dq0_dfi_rddata_en_p6           (ch0_dq0_dfi_rddata_en_p6),
      .o_ch0_dq0_dfi_rddata_en_p7           (ch0_dq0_dfi_rddata_en_p7),
      .o_ch0_dq1_dfi_rddata_cs_p0           (ch0_dq1_dfi_rddata_cs_p0),
      .o_ch0_dq1_dfi_rddata_cs_p1           (ch0_dq1_dfi_rddata_cs_p1),
      .o_ch0_dq1_dfi_rddata_cs_p2           (ch0_dq1_dfi_rddata_cs_p2),
      .o_ch0_dq1_dfi_rddata_cs_p3           (ch0_dq1_dfi_rddata_cs_p3),
      .o_ch0_dq1_dfi_rddata_cs_p4           (ch0_dq1_dfi_rddata_cs_p4),
      .o_ch0_dq1_dfi_rddata_cs_p5           (ch0_dq1_dfi_rddata_cs_p5),
      .o_ch0_dq1_dfi_rddata_cs_p6           (ch0_dq1_dfi_rddata_cs_p6),
      .o_ch0_dq1_dfi_rddata_cs_p7           (ch0_dq1_dfi_rddata_cs_p7),
      .o_ch0_dq1_dfi_rddata_en_p0           (ch0_dq1_dfi_rddata_en_p0),
      .o_ch0_dq1_dfi_rddata_en_p1           (ch0_dq1_dfi_rddata_en_p1),
      .o_ch0_dq1_dfi_rddata_en_p2           (ch0_dq1_dfi_rddata_en_p2),
      .o_ch0_dq1_dfi_rddata_en_p3           (ch0_dq1_dfi_rddata_en_p3),
      .o_ch0_dq1_dfi_rddata_en_p4           (ch0_dq1_dfi_rddata_en_p4),
      .o_ch0_dq1_dfi_rddata_en_p5           (ch0_dq1_dfi_rddata_en_p5),
      .o_ch0_dq1_dfi_rddata_en_p6           (ch0_dq1_dfi_rddata_en_p6),
      .o_ch0_dq1_dfi_rddata_en_p7           (ch0_dq1_dfi_rddata_en_p7),
      .o_ch1_dq0_dfi_rddata_cs_p0           (ch1_dq0_dfi_rddata_cs_p0),
      .o_ch1_dq0_dfi_rddata_cs_p1           (ch1_dq0_dfi_rddata_cs_p1),
      .o_ch1_dq0_dfi_rddata_cs_p2           (ch1_dq0_dfi_rddata_cs_p2),
      .o_ch1_dq0_dfi_rddata_cs_p3           (ch1_dq0_dfi_rddata_cs_p3),
      .o_ch1_dq0_dfi_rddata_cs_p4           (ch1_dq0_dfi_rddata_cs_p4),
      .o_ch1_dq0_dfi_rddata_cs_p5           (ch1_dq0_dfi_rddata_cs_p5),
      .o_ch1_dq0_dfi_rddata_cs_p6           (ch1_dq0_dfi_rddata_cs_p6),
      .o_ch1_dq0_dfi_rddata_cs_p7           (ch1_dq0_dfi_rddata_cs_p7),
      .o_ch1_dq0_dfi_rddata_en_p0           (ch1_dq0_dfi_rddata_en_p0),
      .o_ch1_dq0_dfi_rddata_en_p1           (ch1_dq0_dfi_rddata_en_p1),
      .o_ch1_dq0_dfi_rddata_en_p2           (ch1_dq0_dfi_rddata_en_p2),
      .o_ch1_dq0_dfi_rddata_en_p3           (ch1_dq0_dfi_rddata_en_p3),
      .o_ch1_dq0_dfi_rddata_en_p4           (ch1_dq0_dfi_rddata_en_p4),
      .o_ch1_dq0_dfi_rddata_en_p5           (ch1_dq0_dfi_rddata_en_p5),
      .o_ch1_dq0_dfi_rddata_en_p6           (ch1_dq0_dfi_rddata_en_p6),
      .o_ch1_dq0_dfi_rddata_en_p7           (ch1_dq0_dfi_rddata_en_p7),
      .o_ch1_dq1_dfi_rddata_cs_p0           (ch1_dq1_dfi_rddata_cs_p0),
      .o_ch1_dq1_dfi_rddata_cs_p1           (ch1_dq1_dfi_rddata_cs_p1),
      .o_ch1_dq1_dfi_rddata_cs_p2           (ch1_dq1_dfi_rddata_cs_p2),
      .o_ch1_dq1_dfi_rddata_cs_p3           (ch1_dq1_dfi_rddata_cs_p3),
      .o_ch1_dq1_dfi_rddata_cs_p4           (ch1_dq1_dfi_rddata_cs_p4),
      .o_ch1_dq1_dfi_rddata_cs_p5           (ch1_dq1_dfi_rddata_cs_p5),
      .o_ch1_dq1_dfi_rddata_cs_p6           (ch1_dq1_dfi_rddata_cs_p6),
      .o_ch1_dq1_dfi_rddata_cs_p7           (ch1_dq1_dfi_rddata_cs_p7),
      .o_ch1_dq1_dfi_rddata_en_p0           (ch1_dq1_dfi_rddata_en_p0),
      .o_ch1_dq1_dfi_rddata_en_p1           (ch1_dq1_dfi_rddata_en_p1),
      .o_ch1_dq1_dfi_rddata_en_p2           (ch1_dq1_dfi_rddata_en_p2),
      .o_ch1_dq1_dfi_rddata_en_p3           (ch1_dq1_dfi_rddata_en_p3),
      .o_ch1_dq1_dfi_rddata_en_p4           (ch1_dq1_dfi_rddata_en_p4),
      .o_ch1_dq1_dfi_rddata_en_p5           (ch1_dq1_dfi_rddata_en_p5),
      .o_ch1_dq1_dfi_rddata_en_p6           (ch1_dq1_dfi_rddata_en_p6),
      .o_ch1_dq1_dfi_rddata_en_p7           (ch1_dq1_dfi_rddata_en_p7),

      .i_dq0_dfi_rddata_valid_w0    (dfi_rddata_valid_w0),
      .i_dq0_dfi_rddata_valid_w1    (dfi_rddata_valid_w1),
      .i_dq0_dfi_rddata_valid_w2    (dfi_rddata_valid_w2),
      .i_dq0_dfi_rddata_valid_w3    (dfi_rddata_valid_w3),
      .i_dq0_dfi_rddata_valid_w4    (dfi_rddata_valid_w4),
      .i_dq0_dfi_rddata_valid_w5    (dfi_rddata_valid_w5),
      .i_dq0_dfi_rddata_valid_w6    (dfi_rddata_valid_w6),
      .i_dq0_dfi_rddata_valid_w7    (dfi_rddata_valid_w7),
      .i_dq0_dfi_rddata_dbi_w0      (dfi_rddata_dbi_w0[(0*MWIDTH)+:MWIDTH]),
      .i_dq0_dfi_rddata_dbi_w1      (dfi_rddata_dbi_w1[(0*MWIDTH)+:MWIDTH]),
      .i_dq0_dfi_rddata_dbi_w2      (dfi_rddata_dbi_w2[(0*MWIDTH)+:MWIDTH]),
      .i_dq0_dfi_rddata_dbi_w3      (dfi_rddata_dbi_w3[(0*MWIDTH)+:MWIDTH]),
      .i_dq0_dfi_rddata_dbi_w4      (dfi_rddata_dbi_w4[(0*MWIDTH)+:MWIDTH]),
      .i_dq0_dfi_rddata_dbi_w5      (dfi_rddata_dbi_w5[(0*MWIDTH)+:MWIDTH]),
      .i_dq0_dfi_rddata_dbi_w6      (dfi_rddata_dbi_w6[(0*MWIDTH)+:MWIDTH]),
      .i_dq0_dfi_rddata_dbi_w7      (dfi_rddata_dbi_w7[(0*MWIDTH)+:MWIDTH]),
      .i_dq0_dfi_rddata_w0          (dfi_rddata_w0[(0*SWIDTH)+:SWIDTH]),
      .i_dq0_dfi_rddata_w1          (dfi_rddata_w1[(0*SWIDTH)+:SWIDTH]),
      .i_dq0_dfi_rddata_w2          (dfi_rddata_w2[(0*SWIDTH)+:SWIDTH]),
      .i_dq0_dfi_rddata_w3          (dfi_rddata_w3[(0*SWIDTH)+:SWIDTH]),
      .i_dq0_dfi_rddata_w4          (dfi_rddata_w4[(0*SWIDTH)+:SWIDTH]),
      .i_dq0_dfi_rddata_w5          (dfi_rddata_w5[(0*SWIDTH)+:SWIDTH]),
      .i_dq0_dfi_rddata_w6          (dfi_rddata_w6[(0*SWIDTH)+:SWIDTH]),
      .i_dq0_dfi_rddata_w7          (dfi_rddata_w7[(0*SWIDTH)+:SWIDTH]),
      .i_dq1_dfi_rddata_valid_w0    (dfi_rddata_valid_w0),
      .i_dq1_dfi_rddata_valid_w1    (dfi_rddata_valid_w1),
      .i_dq1_dfi_rddata_valid_w2    (dfi_rddata_valid_w2),
      .i_dq1_dfi_rddata_valid_w3    (dfi_rddata_valid_w3),
      .i_dq1_dfi_rddata_valid_w4    (dfi_rddata_valid_w4),
      .i_dq1_dfi_rddata_valid_w5    (dfi_rddata_valid_w5),
      .i_dq1_dfi_rddata_valid_w6    (dfi_rddata_valid_w6),
      .i_dq1_dfi_rddata_valid_w7    (dfi_rddata_valid_w7),
      .i_dq1_dfi_rddata_dbi_w0      (dfi_rddata_dbi_w0[(1*MWIDTH)+:MWIDTH]),
      .i_dq1_dfi_rddata_dbi_w1      (dfi_rddata_dbi_w1[(1*MWIDTH)+:MWIDTH]),
      .i_dq1_dfi_rddata_dbi_w2      (dfi_rddata_dbi_w2[(1*MWIDTH)+:MWIDTH]),
      .i_dq1_dfi_rddata_dbi_w3      (dfi_rddata_dbi_w3[(1*MWIDTH)+:MWIDTH]),
      .i_dq1_dfi_rddata_dbi_w4      (dfi_rddata_dbi_w4[(1*MWIDTH)+:MWIDTH]),
      .i_dq1_dfi_rddata_dbi_w5      (dfi_rddata_dbi_w5[(1*MWIDTH)+:MWIDTH]),
      .i_dq1_dfi_rddata_dbi_w6      (dfi_rddata_dbi_w6[(1*MWIDTH)+:MWIDTH]),
      .i_dq1_dfi_rddata_dbi_w7      (dfi_rddata_dbi_w7[(1*MWIDTH)+:MWIDTH]),
      .i_dq1_dfi_rddata_w0          (dfi_rddata_w0[(1*SWIDTH)+:SWIDTH]),
      .i_dq1_dfi_rddata_w1          (dfi_rddata_w1[(1*SWIDTH)+:SWIDTH]),
      .i_dq1_dfi_rddata_w2          (dfi_rddata_w2[(1*SWIDTH)+:SWIDTH]),
      .i_dq1_dfi_rddata_w3          (dfi_rddata_w3[(1*SWIDTH)+:SWIDTH]),
      .i_dq1_dfi_rddata_w4          (dfi_rddata_w4[(1*SWIDTH)+:SWIDTH]),
      .i_dq1_dfi_rddata_w5          (dfi_rddata_w5[(1*SWIDTH)+:SWIDTH]),
      .i_dq1_dfi_rddata_w6          (dfi_rddata_w6[(1*SWIDTH)+:SWIDTH]),
      .i_dq1_dfi_rddata_w7          (dfi_rddata_w7[(1*SWIDTH)+:SWIDTH]),
      .i_dq2_dfi_rddata_valid_w0    (dfi_rddata_valid_w0),
      .i_dq2_dfi_rddata_valid_w1    (dfi_rddata_valid_w1),
      .i_dq2_dfi_rddata_valid_w2    (dfi_rddata_valid_w2),
      .i_dq2_dfi_rddata_valid_w3    (dfi_rddata_valid_w3),
      .i_dq2_dfi_rddata_valid_w4    (dfi_rddata_valid_w4),
      .i_dq2_dfi_rddata_valid_w5    (dfi_rddata_valid_w5),
      .i_dq2_dfi_rddata_valid_w6    (dfi_rddata_valid_w6),
      .i_dq2_dfi_rddata_valid_w7    (dfi_rddata_valid_w7),
      .i_dq2_dfi_rddata_dbi_w0      (dfi_rddata_dbi_w0[(2*MWIDTH)+:MWIDTH]),
      .i_dq2_dfi_rddata_dbi_w1      (dfi_rddata_dbi_w1[(2*MWIDTH)+:MWIDTH]),
      .i_dq2_dfi_rddata_dbi_w2      (dfi_rddata_dbi_w2[(2*MWIDTH)+:MWIDTH]),
      .i_dq2_dfi_rddata_dbi_w3      (dfi_rddata_dbi_w3[(2*MWIDTH)+:MWIDTH]),
      .i_dq2_dfi_rddata_dbi_w4      (dfi_rddata_dbi_w4[(2*MWIDTH)+:MWIDTH]),
      .i_dq2_dfi_rddata_dbi_w5      (dfi_rddata_dbi_w5[(2*MWIDTH)+:MWIDTH]),
      .i_dq2_dfi_rddata_dbi_w6      (dfi_rddata_dbi_w6[(2*MWIDTH)+:MWIDTH]),
      .i_dq2_dfi_rddata_dbi_w7      (dfi_rddata_dbi_w7[(2*MWIDTH)+:MWIDTH]),
      .i_dq2_dfi_rddata_w0          (dfi_rddata_w0[(2*SWIDTH)+:SWIDTH]),
      .i_dq2_dfi_rddata_w1          (dfi_rddata_w1[(2*SWIDTH)+:SWIDTH]),
      .i_dq2_dfi_rddata_w2          (dfi_rddata_w2[(2*SWIDTH)+:SWIDTH]),
      .i_dq2_dfi_rddata_w3          (dfi_rddata_w3[(2*SWIDTH)+:SWIDTH]),
      .i_dq2_dfi_rddata_w4          (dfi_rddata_w4[(2*SWIDTH)+:SWIDTH]),
      .i_dq2_dfi_rddata_w5          (dfi_rddata_w5[(2*SWIDTH)+:SWIDTH]),
      .i_dq2_dfi_rddata_w6          (dfi_rddata_w6[(2*SWIDTH)+:SWIDTH]),
      .i_dq2_dfi_rddata_w7          (dfi_rddata_w7[(2*SWIDTH)+:SWIDTH]),
      .i_dq3_dfi_rddata_valid_w0    (dfi_rddata_valid_w0),
      .i_dq3_dfi_rddata_valid_w1    (dfi_rddata_valid_w1),
      .i_dq3_dfi_rddata_valid_w2    (dfi_rddata_valid_w2),
      .i_dq3_dfi_rddata_valid_w3    (dfi_rddata_valid_w3),
      .i_dq3_dfi_rddata_valid_w4    (dfi_rddata_valid_w4),
      .i_dq3_dfi_rddata_valid_w5    (dfi_rddata_valid_w5),
      .i_dq3_dfi_rddata_valid_w6    (dfi_rddata_valid_w6),
      .i_dq3_dfi_rddata_valid_w7    (dfi_rddata_valid_w7),
      .i_dq3_dfi_rddata_dbi_w0      (dfi_rddata_dbi_w0[(3*MWIDTH)+:MWIDTH]),
      .i_dq3_dfi_rddata_dbi_w1      (dfi_rddata_dbi_w1[(3*MWIDTH)+:MWIDTH]),
      .i_dq3_dfi_rddata_dbi_w2      (dfi_rddata_dbi_w2[(3*MWIDTH)+:MWIDTH]),
      .i_dq3_dfi_rddata_dbi_w3      (dfi_rddata_dbi_w3[(3*MWIDTH)+:MWIDTH]),
      .i_dq3_dfi_rddata_dbi_w4      (dfi_rddata_dbi_w4[(3*MWIDTH)+:MWIDTH]),
      .i_dq3_dfi_rddata_dbi_w5      (dfi_rddata_dbi_w5[(3*MWIDTH)+:MWIDTH]),
      .i_dq3_dfi_rddata_dbi_w6      (dfi_rddata_dbi_w6[(3*MWIDTH)+:MWIDTH]),
      .i_dq3_dfi_rddata_dbi_w7      (dfi_rddata_dbi_w7[(3*MWIDTH)+:MWIDTH]),
      .i_dq3_dfi_rddata_w0          (dfi_rddata_w0[(3*SWIDTH)+:SWIDTH]),
      .i_dq3_dfi_rddata_w1          (dfi_rddata_w1[(3*SWIDTH)+:SWIDTH]),
      .i_dq3_dfi_rddata_w2          (dfi_rddata_w2[(3*SWIDTH)+:SWIDTH]),
      .i_dq3_dfi_rddata_w3          (dfi_rddata_w3[(3*SWIDTH)+:SWIDTH]),
      .i_dq3_dfi_rddata_w4          (dfi_rddata_w4[(3*SWIDTH)+:SWIDTH]),
      .i_dq3_dfi_rddata_w5          (dfi_rddata_w5[(3*SWIDTH)+:SWIDTH]),
      .i_dq3_dfi_rddata_w6          (dfi_rddata_w6[(3*SWIDTH)+:SWIDTH]),
      .i_dq3_dfi_rddata_w7          (dfi_rddata_w7[(3*SWIDTH)+:SWIDTH]),
      .i_dfi_rdout_en                   (dfi_rdout_en),
      .o_dfi_rddata_valid_w0           (o_dfi_rddata_valid_w0),
      .o_dfi_rddata_valid_w1           (o_dfi_rddata_valid_w1),
      .o_dfi_rddata_valid_w2           (o_dfi_rddata_valid_w2),
      .o_dfi_rddata_valid_w3           (o_dfi_rddata_valid_w3),
      .o_dfi_rddata_valid_w4           (o_dfi_rddata_valid_w4),
      .o_dfi_rddata_valid_w5           (o_dfi_rddata_valid_w5),
      .o_dfi_rddata_valid_w6           (o_dfi_rddata_valid_w6),
      .o_dfi_rddata_valid_w7           (o_dfi_rddata_valid_w7),
      .o_dq0_dfi_rddata_dbi_w0      (o_dfi_rddata_dbi_w0[(0*MWIDTH)+:MWIDTH]),
      .o_dq0_dfi_rddata_dbi_w1      (o_dfi_rddata_dbi_w1[(0*MWIDTH)+:MWIDTH]),
      .o_dq0_dfi_rddata_dbi_w2      (o_dfi_rddata_dbi_w2[(0*MWIDTH)+:MWIDTH]),
      .o_dq0_dfi_rddata_dbi_w3      (o_dfi_rddata_dbi_w3[(0*MWIDTH)+:MWIDTH]),
      .o_dq0_dfi_rddata_dbi_w4      (o_dfi_rddata_dbi_w4[(0*MWIDTH)+:MWIDTH]),
      .o_dq0_dfi_rddata_dbi_w5      (o_dfi_rddata_dbi_w5[(0*MWIDTH)+:MWIDTH]),
      .o_dq0_dfi_rddata_dbi_w6      (o_dfi_rddata_dbi_w6[(0*MWIDTH)+:MWIDTH]),
      .o_dq0_dfi_rddata_dbi_w7      (o_dfi_rddata_dbi_w7[(0*MWIDTH)+:MWIDTH]),
      .o_dq0_dfi_rddata_w0          (o_dfi_rddata_w0[(0*SWIDTH)+:SWIDTH]),
      .o_dq0_dfi_rddata_w1          (o_dfi_rddata_w1[(0*SWIDTH)+:SWIDTH]),
      .o_dq0_dfi_rddata_w2          (o_dfi_rddata_w2[(0*SWIDTH)+:SWIDTH]),
      .o_dq0_dfi_rddata_w3          (o_dfi_rddata_w3[(0*SWIDTH)+:SWIDTH]),
      .o_dq0_dfi_rddata_w4          (o_dfi_rddata_w4[(0*SWIDTH)+:SWIDTH]),
      .o_dq0_dfi_rddata_w5          (o_dfi_rddata_w5[(0*SWIDTH)+:SWIDTH]),
      .o_dq0_dfi_rddata_w6          (o_dfi_rddata_w6[(0*SWIDTH)+:SWIDTH]),
      .o_dq0_dfi_rddata_w7          (o_dfi_rddata_w7[(0*SWIDTH)+:SWIDTH]),
      .o_dq1_dfi_rddata_dbi_w0      (o_dfi_rddata_dbi_w0[(1*MWIDTH)+:MWIDTH]),
      .o_dq1_dfi_rddata_dbi_w1      (o_dfi_rddata_dbi_w1[(1*MWIDTH)+:MWIDTH]),
      .o_dq1_dfi_rddata_dbi_w2      (o_dfi_rddata_dbi_w2[(1*MWIDTH)+:MWIDTH]),
      .o_dq1_dfi_rddata_dbi_w3      (o_dfi_rddata_dbi_w3[(1*MWIDTH)+:MWIDTH]),
      .o_dq1_dfi_rddata_dbi_w4      (o_dfi_rddata_dbi_w4[(1*MWIDTH)+:MWIDTH]),
      .o_dq1_dfi_rddata_dbi_w5      (o_dfi_rddata_dbi_w5[(1*MWIDTH)+:MWIDTH]),
      .o_dq1_dfi_rddata_dbi_w6      (o_dfi_rddata_dbi_w6[(1*MWIDTH)+:MWIDTH]),
      .o_dq1_dfi_rddata_dbi_w7      (o_dfi_rddata_dbi_w7[(1*MWIDTH)+:MWIDTH]),
      .o_dq1_dfi_rddata_w0          (o_dfi_rddata_w0[(1*SWIDTH)+:SWIDTH]),
      .o_dq1_dfi_rddata_w1          (o_dfi_rddata_w1[(1*SWIDTH)+:SWIDTH]),
      .o_dq1_dfi_rddata_w2          (o_dfi_rddata_w2[(1*SWIDTH)+:SWIDTH]),
      .o_dq1_dfi_rddata_w3          (o_dfi_rddata_w3[(1*SWIDTH)+:SWIDTH]),
      .o_dq1_dfi_rddata_w4          (o_dfi_rddata_w4[(1*SWIDTH)+:SWIDTH]),
      .o_dq1_dfi_rddata_w5          (o_dfi_rddata_w5[(1*SWIDTH)+:SWIDTH]),
      .o_dq1_dfi_rddata_w6          (o_dfi_rddata_w6[(1*SWIDTH)+:SWIDTH]),
      .o_dq1_dfi_rddata_w7          (o_dfi_rddata_w7[(1*SWIDTH)+:SWIDTH]),
      .o_dq2_dfi_rddata_dbi_w0      (o_dfi_rddata_dbi_w0[(2*MWIDTH)+:MWIDTH]),
      .o_dq2_dfi_rddata_dbi_w1      (o_dfi_rddata_dbi_w1[(2*MWIDTH)+:MWIDTH]),
      .o_dq2_dfi_rddata_dbi_w2      (o_dfi_rddata_dbi_w2[(2*MWIDTH)+:MWIDTH]),
      .o_dq2_dfi_rddata_dbi_w3      (o_dfi_rddata_dbi_w3[(2*MWIDTH)+:MWIDTH]),
      .o_dq2_dfi_rddata_dbi_w4      (o_dfi_rddata_dbi_w4[(2*MWIDTH)+:MWIDTH]),
      .o_dq2_dfi_rddata_dbi_w5      (o_dfi_rddata_dbi_w5[(2*MWIDTH)+:MWIDTH]),
      .o_dq2_dfi_rddata_dbi_w6      (o_dfi_rddata_dbi_w6[(2*MWIDTH)+:MWIDTH]),
      .o_dq2_dfi_rddata_dbi_w7      (o_dfi_rddata_dbi_w7[(2*MWIDTH)+:MWIDTH]),
      .o_dq2_dfi_rddata_w0          (o_dfi_rddata_w0[(2*SWIDTH)+:SWIDTH]),
      .o_dq2_dfi_rddata_w1          (o_dfi_rddata_w1[(2*SWIDTH)+:SWIDTH]),
      .o_dq2_dfi_rddata_w2          (o_dfi_rddata_w2[(2*SWIDTH)+:SWIDTH]),
      .o_dq2_dfi_rddata_w3          (o_dfi_rddata_w3[(2*SWIDTH)+:SWIDTH]),
      .o_dq2_dfi_rddata_w4          (o_dfi_rddata_w4[(2*SWIDTH)+:SWIDTH]),
      .o_dq2_dfi_rddata_w5          (o_dfi_rddata_w5[(2*SWIDTH)+:SWIDTH]),
      .o_dq2_dfi_rddata_w6          (o_dfi_rddata_w6[(2*SWIDTH)+:SWIDTH]),
      .o_dq2_dfi_rddata_w7          (o_dfi_rddata_w7[(2*SWIDTH)+:SWIDTH]),
      .o_dq3_dfi_rddata_dbi_w0      (o_dfi_rddata_dbi_w0[(3*MWIDTH)+:MWIDTH]),
      .o_dq3_dfi_rddata_dbi_w1      (o_dfi_rddata_dbi_w1[(3*MWIDTH)+:MWIDTH]),
      .o_dq3_dfi_rddata_dbi_w2      (o_dfi_rddata_dbi_w2[(3*MWIDTH)+:MWIDTH]),
      .o_dq3_dfi_rddata_dbi_w3      (o_dfi_rddata_dbi_w3[(3*MWIDTH)+:MWIDTH]),
      .o_dq3_dfi_rddata_dbi_w4      (o_dfi_rddata_dbi_w4[(3*MWIDTH)+:MWIDTH]),
      .o_dq3_dfi_rddata_dbi_w5      (o_dfi_rddata_dbi_w5[(3*MWIDTH)+:MWIDTH]),
      .o_dq3_dfi_rddata_dbi_w6      (o_dfi_rddata_dbi_w6[(3*MWIDTH)+:MWIDTH]),
      .o_dq3_dfi_rddata_dbi_w7      (o_dfi_rddata_dbi_w7[(3*MWIDTH)+:MWIDTH]),
      .o_dq3_dfi_rddata_w0          (o_dfi_rddata_w0[(3*SWIDTH)+:SWIDTH]),
      .o_dq3_dfi_rddata_w1          (o_dfi_rddata_w1[(3*SWIDTH)+:SWIDTH]),
      .o_dq3_dfi_rddata_w2          (o_dfi_rddata_w2[(3*SWIDTH)+:SWIDTH]),
      .o_dq3_dfi_rddata_w3          (o_dfi_rddata_w3[(3*SWIDTH)+:SWIDTH]),
      .o_dq3_dfi_rddata_w4          (o_dfi_rddata_w4[(3*SWIDTH)+:SWIDTH]),
      .o_dq3_dfi_rddata_w5          (o_dfi_rddata_w5[(3*SWIDTH)+:SWIDTH]),
      .o_dq3_dfi_rddata_w6          (o_dfi_rddata_w6[(3*SWIDTH)+:SWIDTH]),
      .o_dq3_dfi_rddata_w7          (o_dfi_rddata_w7[(3*SWIDTH)+:SWIDTH]),
      .o_debug                          (dfich0_dfibuf_debug)
   );

   assign o_ch0_dfi_ibuf_empty_irq     = dfi_buf_ig_empty;
   assign o_ch0_dfi_ibuf_full_irq      = dfi_buf_ig_full;
   assign o_ch0_dfi_ibuf_overflow_irq  = dfi_buf_ig_overflow;
   assign o_ch0_dfi_ebuf_empty_irq     = dfi_buf_eg_empty;
   assign o_ch0_dfi_ebuf_full_irq      = dfi_buf_eg_full;
   assign o_ch0_dfi_ebuf_overflow_irq  = dfi_buf_eg_overflow;


   assign o_ch1_dfi_ibuf_empty_irq     = '0;
   assign o_ch1_dfi_ibuf_full_irq      = '0;
   assign o_ch1_dfi_ibuf_overflow_irq  = '0;
   assign o_ch1_dfi_ebuf_empty_irq     = '0;
   assign o_ch1_dfi_ebuf_full_irq      = '0;
   assign o_ch1_dfi_ebuf_overflow_irq  = '0;

   // ------------------------------------------------------------------------
   // DFI DP Channel
   // ------------------------------------------------------------------------
   logic ca_lpbk_sel ;
   logic [NUM_DQ-1:0] ch1_dfi_rdvalid_mask;
   logic [NUM_DQ-1:0] ch0_dfi_rdvalid_mask;
   assign ca_lpbk_sel = dfi_top_0_cfg[`DDR_DFI_TOP_0_CFG_CA_LPBK_SEL_FIELD] ;

   assign dfi_rddata_w0                = { ch1_dfi_rddata_w0      , ch0_dfi_rddata_w0      };
   assign dfi_rddata_dbi_w0            = { ch1_dfi_rddata_dbi_w0  , ch0_dfi_rddata_dbi_w0  };
   assign dfi_rddata_valid_w0          = { ch1_dfi_rddata_valid_w0, ch0_dfi_rddata_valid_w0};
   assign dfi_rddata_w1                = { ch1_dfi_rddata_w1      , ch0_dfi_rddata_w1      };
   assign dfi_rddata_dbi_w1            = { ch1_dfi_rddata_dbi_w1  , ch0_dfi_rddata_dbi_w1  };
   assign dfi_rddata_valid_w1          = { ch1_dfi_rddata_valid_w1, ch0_dfi_rddata_valid_w1};
   assign dfi_rddata_w2                = { ch1_dfi_rddata_w2      , ch0_dfi_rddata_w2      };
   assign dfi_rddata_dbi_w2            = { ch1_dfi_rddata_dbi_w2  , ch0_dfi_rddata_dbi_w2  };
   assign dfi_rddata_valid_w2          = { ch1_dfi_rddata_valid_w2, ch0_dfi_rddata_valid_w2};
   assign dfi_rddata_w3                = { ch1_dfi_rddata_w3      , ch0_dfi_rddata_w3      };
   assign dfi_rddata_dbi_w3            = { ch1_dfi_rddata_dbi_w3  , ch0_dfi_rddata_dbi_w3  };
   assign dfi_rddata_valid_w3          = { ch1_dfi_rddata_valid_w3, ch0_dfi_rddata_valid_w3};
   assign dfi_rddata_w4                = { ch1_dfi_rddata_w4      , ch0_dfi_rddata_w4      };
   assign dfi_rddata_dbi_w4            = { ch1_dfi_rddata_dbi_w4  , ch0_dfi_rddata_dbi_w4  };
   assign dfi_rddata_valid_w4          = { ch1_dfi_rddata_valid_w4, ch0_dfi_rddata_valid_w4};
   assign dfi_rddata_w5                = { ch1_dfi_rddata_w5      , ch0_dfi_rddata_w5      };
   assign dfi_rddata_dbi_w5            = { ch1_dfi_rddata_dbi_w5  , ch0_dfi_rddata_dbi_w5  };
   assign dfi_rddata_valid_w5          = { ch1_dfi_rddata_valid_w5, ch0_dfi_rddata_valid_w5};
   assign dfi_rddata_w6                = { ch1_dfi_rddata_w6      , ch0_dfi_rddata_w6      };
   assign dfi_rddata_dbi_w6            = { ch1_dfi_rddata_dbi_w6  , ch0_dfi_rddata_dbi_w6  };
   assign dfi_rddata_valid_w6          = { ch1_dfi_rddata_valid_w6, ch0_dfi_rddata_valid_w6};
   assign dfi_rddata_w7                = { ch1_dfi_rddata_w7      , ch0_dfi_rddata_w7      };
   assign dfi_rddata_dbi_w7            = { ch1_dfi_rddata_dbi_w7  , ch0_dfi_rddata_dbi_w7  };
   assign dfi_rddata_valid_w7          = { ch1_dfi_rddata_valid_w7, ch0_dfi_rddata_valid_w7};

   assign dfi_address_w0            =  ca_lpbk_sel ? ch1_dfi_address_w0 : ch0_dfi_address_w0;
   assign dfi_address_w1            =  ca_lpbk_sel ? ch1_dfi_address_w1 : ch0_dfi_address_w1;
   assign dfi_address_w2            =  ca_lpbk_sel ? ch1_dfi_address_w2 : ch0_dfi_address_w2;
   assign dfi_address_w3            =  ca_lpbk_sel ? ch1_dfi_address_w3 : ch0_dfi_address_w3;
   assign dfi_address_w4            =  ca_lpbk_sel ? ch1_dfi_address_w4 : ch0_dfi_address_w4;
   assign dfi_address_w5            =  ca_lpbk_sel ? ch1_dfi_address_w5 : ch0_dfi_address_w5;
   assign dfi_address_w6            =  ca_lpbk_sel ? ch1_dfi_address_w6 : ch0_dfi_address_w6;
   assign dfi_address_w7            =  ca_lpbk_sel ? ch1_dfi_address_w7 : ch0_dfi_address_w7;
   assign dfi_cs_w0                 =  ca_lpbk_sel ? ch1_dfi_cs_w0      : ch0_dfi_cs_w0 ;
   assign dfi_cs_w1                 =  ca_lpbk_sel ? ch1_dfi_cs_w1      : ch0_dfi_cs_w1 ;
   assign dfi_cs_w2                 =  ca_lpbk_sel ? ch1_dfi_cs_w2      : ch0_dfi_cs_w2 ;
   assign dfi_cs_w3                 =  ca_lpbk_sel ? ch1_dfi_cs_w3      : ch0_dfi_cs_w3 ;
   assign dfi_cs_w4                 =  ca_lpbk_sel ? ch1_dfi_cs_w4      : ch0_dfi_cs_w4 ;
   assign dfi_cs_w5                 =  ca_lpbk_sel ? ch1_dfi_cs_w5      : ch0_dfi_cs_w5 ;
   assign dfi_cs_w6                 =  ca_lpbk_sel ? ch1_dfi_cs_w6      : ch0_dfi_cs_w6 ;
   assign dfi_cs_w7                 =  ca_lpbk_sel ? ch1_dfi_cs_w7      : ch0_dfi_cs_w7 ;
   assign dfi_cke_w0                =  ca_lpbk_sel ? ch1_dfi_cke_w0     : ch0_dfi_cke_w0 ;
   assign dfi_cke_w1                =  ca_lpbk_sel ? ch1_dfi_cke_w1     : ch0_dfi_cke_w1 ;
   assign dfi_cke_w2                =  ca_lpbk_sel ? ch1_dfi_cke_w2     : ch0_dfi_cke_w2 ;
   assign dfi_cke_w3                =  ca_lpbk_sel ? ch1_dfi_cke_w3     : ch0_dfi_cke_w3 ;
   assign dfi_cke_w4                =  ca_lpbk_sel ? ch1_dfi_cke_w4     : ch0_dfi_cke_w4 ;
   assign dfi_cke_w5                =  ca_lpbk_sel ? ch1_dfi_cke_w5     : ch0_dfi_cke_w5 ;
   assign dfi_cke_w6                =  ca_lpbk_sel ? ch1_dfi_cke_w6     : ch0_dfi_cke_w6 ;
   assign dfi_cke_w7                =  ca_lpbk_sel ? ch1_dfi_cke_w7     : ch0_dfi_cke_w7 ;
   assign dfi_address_valid_w0        =  ca_lpbk_sel ? ch1_dfi_address_valid_w0 : ch0_dfi_address_valid_w0 ;
   assign dfi_address_valid_w1        =  ca_lpbk_sel ? ch1_dfi_address_valid_w1 : ch0_dfi_address_valid_w1 ;
   assign dfi_address_valid_w2        =  ca_lpbk_sel ? ch1_dfi_address_valid_w2 : ch0_dfi_address_valid_w2 ;
   assign dfi_address_valid_w3        =  ca_lpbk_sel ? ch1_dfi_address_valid_w3 : ch0_dfi_address_valid_w3 ;
   assign dfi_address_valid_w4        =  ca_lpbk_sel ? ch1_dfi_address_valid_w4 : ch0_dfi_address_valid_w4 ;
   assign dfi_address_valid_w5        =  ca_lpbk_sel ? ch1_dfi_address_valid_w5 : ch0_dfi_address_valid_w5 ;
   assign dfi_address_valid_w6        =  ca_lpbk_sel ? ch1_dfi_address_valid_w6 : ch0_dfi_address_valid_w6 ;
   assign dfi_address_valid_w7        =  ca_lpbk_sel ? ch1_dfi_address_valid_w7 : ch0_dfi_address_valid_w7 ;


   assign {ch1_dfi_rdvalid_mask,ch0_dfi_rdvalid_mask} = dfich0_top_1_cfg[`DDR_DFICH_TOP_1_CFG_DQBYTE_RDVALID_MASK_FIELD] ;

   assign y_ch0_dfi_carddata_en_p0     =  dfich0_top_1_cfg[`DDR_DFICH_TOP_1_CFG_CA_RDDATA_EN_FIELD];
   assign y_ch0_dfi_carddata_en_p1     =  dfich0_top_1_cfg[`DDR_DFICH_TOP_1_CFG_CA_RDDATA_EN_FIELD];
   assign y_ch0_dfi_carddata_en_p2     =  dfich0_top_1_cfg[`DDR_DFICH_TOP_1_CFG_CA_RDDATA_EN_FIELD];
   assign y_ch0_dfi_carddata_en_p3     =  dfich0_top_1_cfg[`DDR_DFICH_TOP_1_CFG_CA_RDDATA_EN_FIELD];
   assign y_ch0_dfi_carddata_en_p4     =  dfich0_top_1_cfg[`DDR_DFICH_TOP_1_CFG_CA_RDDATA_EN_FIELD];
   assign y_ch0_dfi_carddata_en_p5     =  dfich0_top_1_cfg[`DDR_DFICH_TOP_1_CFG_CA_RDDATA_EN_FIELD];
   assign y_ch0_dfi_carddata_en_p6     =  dfich0_top_1_cfg[`DDR_DFICH_TOP_1_CFG_CA_RDDATA_EN_FIELD];
   assign y_ch0_dfi_carddata_en_p7     =  dfich0_top_1_cfg[`DDR_DFICH_TOP_1_CFG_CA_RDDATA_EN_FIELD];

   ddr_dfi_dp_ca #(
     .AWIDTH                        (AWIDTH),
     .CWIDTH                        (CWIDTH),
     .NUM_WPH                       (NUM_WPH),
     .F0WIDTH                       (F0WIDTH)
   ) u_ch0_dfi_dp_ca (

      //DFT
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_rst                        (i_rst),

      //Clock and Reset
      .i_dfi_clk                    (dfi_clk),

      .i_cmda_clk_0                 (cmda_clk_0  ),
      .i_cmda_clk_1                 (cmda_clk_1  ),
      .i_cmda_clk_2                 (cmda_clk_2  ),
      .i_cmdc_clk_0                 (cmdc_clk_0  ),
      .i_cmdc_clk_1                 (cmdc_clk_1  ),
      .i_cmdc_clk_2                 (cmdc_clk_2  ),

      .i_rd_clk_1                   (rd_clk_1  ),
      .i_rd_clk_2                   (rd_clk_2  ),

      // Data Path Configuration
      .i_dfi_ctrl0_cfg              (dfich0_ctrl0_cfg    ),
      .i_dfi_wrc_cfg                (dfich0_wrc_cfg      ),
      .i_dfi_wrcctrl_cfg            (dfich0_wrcctrl_cfg  ),
      .i_dfi_ckctrl_cfg             (dfich0_ckctrl_cfg   ),
      .i_dfi_rdc_cfg                (dfich0_rdc_cfg      ),

      // Write Command/Address Interface
      .i_dfi_address_p0             (ch0_dfi_address_p0),
      .i_dfi_address_p1             (ch0_dfi_address_p1),
      .i_dfi_address_p2             (ch0_dfi_address_p2),
      .i_dfi_address_p3             (ch0_dfi_address_p3),
      .i_dfi_address_p4             (ch0_dfi_address_p4),
      .i_dfi_address_p5             (ch0_dfi_address_p5),
      .i_dfi_address_p6             (ch0_dfi_address_p6),
      .i_dfi_address_p7             (ch0_dfi_address_p7),
      .i_dfi_cke_p0                 (ch0_dfi_cke_p0),
      .i_dfi_cke_p1                 (ch0_dfi_cke_p1),
      .i_dfi_cke_p2                 (ch0_dfi_cke_p2),
      .i_dfi_cke_p3                 (ch0_dfi_cke_p3),
      .i_dfi_cke_p4                 (ch0_dfi_cke_p4),
      .i_dfi_cke_p5                 (ch0_dfi_cke_p5),
      .i_dfi_cke_p6                 (ch0_dfi_cke_p6),
      .i_dfi_cke_p7                 (ch0_dfi_cke_p7),
      .i_dfi_cs_p0                  (ch0_dfi_cs_p0),
      .i_dfi_cs_p1                  (ch0_dfi_cs_p1),
      .i_dfi_cs_p2                  (ch0_dfi_cs_p2),
      .i_dfi_cs_p3                  (ch0_dfi_cs_p3),
      .i_dfi_cs_p4                  (ch0_dfi_cs_p4),
      .i_dfi_cs_p5                  (ch0_dfi_cs_p5),
      .i_dfi_cs_p6                  (ch0_dfi_cs_p6),
      .i_dfi_cs_p7                  (ch0_dfi_cs_p7),
      .i_dfi_dcd_p0                 (ch0_dfi_dram_clk_disable_p0),
      .i_dfi_dcd_p1                 (ch0_dfi_dram_clk_disable_p1),
      .i_dfi_dcd_p2                 (ch0_dfi_dram_clk_disable_p2),
      .i_dfi_dcd_p3                 (ch0_dfi_dram_clk_disable_p3),
      .i_dfi_dcd_p4                 (ch0_dfi_dram_clk_disable_p4),
      .i_dfi_dcd_p5                 (ch0_dfi_dram_clk_disable_p5),
      .i_dfi_dcd_p6                 (ch0_dfi_dram_clk_disable_p6),
      .i_dfi_dcd_p7                 (ch0_dfi_dram_clk_disable_p7),

      .o_dfi_address_p0             (y_ch0_dfi_address_p0),
      .o_dfi_address_p1             (y_ch0_dfi_address_p1),
      .o_dfi_address_p2             (y_ch0_dfi_address_p2),
      .o_dfi_address_p3             (y_ch0_dfi_address_p3),
      .o_dfi_address_p4             (y_ch0_dfi_address_p4),
      .o_dfi_address_p5             (y_ch0_dfi_address_p5),
      .o_dfi_address_p6             (y_ch0_dfi_address_p6),
      .o_dfi_address_p7             (y_ch0_dfi_address_p7),
      .o_dfi_cke_p0                 (y_ch0_dfi_cke_p0),
      .o_dfi_cke_p1                 (y_ch0_dfi_cke_p1),
      .o_dfi_cke_p2                 (y_ch0_dfi_cke_p2),
      .o_dfi_cke_p3                 (y_ch0_dfi_cke_p3),
      .o_dfi_cke_p4                 (y_ch0_dfi_cke_p4),
      .o_dfi_cke_p5                 (y_ch0_dfi_cke_p5),
      .o_dfi_cke_p6                 (y_ch0_dfi_cke_p6),
      .o_dfi_cke_p7                 (y_ch0_dfi_cke_p7),
      .o_dfi_cs_p0                  (y_ch0_dfi_cs_p0),
      .o_dfi_cs_p1                  (y_ch0_dfi_cs_p1),
      .o_dfi_cs_p2                  (y_ch0_dfi_cs_p2),
      .o_dfi_cs_p3                  (y_ch0_dfi_cs_p3),
      .o_dfi_cs_p4                  (y_ch0_dfi_cs_p4),
      .o_dfi_cs_p5                  (y_ch0_dfi_cs_p5),
      .o_dfi_cs_p6                  (y_ch0_dfi_cs_p6),
      .o_dfi_cs_p7                  (y_ch0_dfi_cs_p7),
      .o_dfi_dcd_p0                 (y_ch0_dfi_dram_clk_disable_p0),
      .o_dfi_dcd_p1                 (y_ch0_dfi_dram_clk_disable_p1),
      .o_dfi_dcd_p2                 (y_ch0_dfi_dram_clk_disable_p2),
      .o_dfi_dcd_p3                 (y_ch0_dfi_dram_clk_disable_p3),
      .o_dfi_dcd_p4                 (y_ch0_dfi_dram_clk_disable_p4),
      .o_dfi_dcd_p5                 (y_ch0_dfi_dram_clk_disable_p5),
      .o_dfi_dcd_p6                 (y_ch0_dfi_dram_clk_disable_p6),
      .o_dfi_dcd_p7                 (y_ch0_dfi_dram_clk_disable_p7),
      .o_dfi_dce_p0                 (y_ch0_dfi_dram_clk_enable_p0),
      .o_dfi_dce_p1                 (y_ch0_dfi_dram_clk_enable_p1),
      .o_dfi_dce_p2                 (y_ch0_dfi_dram_clk_enable_p2),
      .o_dfi_dce_p3                 (y_ch0_dfi_dram_clk_enable_p3),
      .o_dfi_dce_p4                 (y_ch0_dfi_dram_clk_enable_p4),
      .o_dfi_dce_p5                 (y_ch0_dfi_dram_clk_enable_p5),
      .o_dfi_dce_p6                 (y_ch0_dfi_dram_clk_enable_p6),
      .o_dfi_dce_p7                 (y_ch0_dfi_dram_clk_enable_p7),

      // Read Command/Address Interface
      .i_dfi_address_w0             (y_ch0_dfi_address_w0),
      .i_dfi_address_w1             (y_ch0_dfi_address_w1),
      .i_dfi_address_w2             (y_ch0_dfi_address_w2),
      .i_dfi_address_w3             (y_ch0_dfi_address_w3),
      .i_dfi_address_w4             (y_ch0_dfi_address_w4),
      .i_dfi_address_w5             (y_ch0_dfi_address_w5),
      .i_dfi_address_w6             (y_ch0_dfi_address_w6),
      .i_dfi_address_w7             (y_ch0_dfi_address_w7),
      .i_dfi_cs_w0                  (y_ch0_dfi_cs_w0),
      .i_dfi_cs_w1                  (y_ch0_dfi_cs_w1),
      .i_dfi_cs_w2                  (y_ch0_dfi_cs_w2),
      .i_dfi_cs_w3                  (y_ch0_dfi_cs_w3),
      .i_dfi_cs_w4                  (y_ch0_dfi_cs_w4),
      .i_dfi_cs_w5                  (y_ch0_dfi_cs_w5),
      .i_dfi_cs_w6                  (y_ch0_dfi_cs_w6),
      .i_dfi_cs_w7                  (y_ch0_dfi_cs_w7),
      .i_dfi_cke_w0                 (y_ch0_dfi_cke_w0),
      .i_dfi_cke_w1                 (y_ch0_dfi_cke_w1),
      .i_dfi_cke_w2                 (y_ch0_dfi_cke_w2),
      .i_dfi_cke_w3                 (y_ch0_dfi_cke_w3),
      .i_dfi_cke_w4                 (y_ch0_dfi_cke_w4),
      .i_dfi_cke_w5                 (y_ch0_dfi_cke_w5),
      .i_dfi_cke_w6                 (y_ch0_dfi_cke_w6),
      .i_dfi_cke_w7                 (y_ch0_dfi_cke_w7),
      .i_dfi_address_valid           (y_ch0_dfi_address_valid),

      .o_dfi_address_w0             (ch0_dfi_address_w0),
      .o_dfi_address_w1             (ch0_dfi_address_w1),
      .o_dfi_address_w2             (ch0_dfi_address_w2),
      .o_dfi_address_w3             (ch0_dfi_address_w3),
      .o_dfi_address_w4             (ch0_dfi_address_w4),
      .o_dfi_address_w5             (ch0_dfi_address_w5),
      .o_dfi_address_w6             (ch0_dfi_address_w6),
      .o_dfi_address_w7             (ch0_dfi_address_w7),
      .o_dfi_cs_w0                  (ch0_dfi_cs_w0),
      .o_dfi_cs_w1                  (ch0_dfi_cs_w1),
      .o_dfi_cs_w2                  (ch0_dfi_cs_w2),
      .o_dfi_cs_w3                  (ch0_dfi_cs_w3),
      .o_dfi_cs_w4                  (ch0_dfi_cs_w4),
      .o_dfi_cs_w5                  (ch0_dfi_cs_w5),
      .o_dfi_cs_w6                  (ch0_dfi_cs_w6),
      .o_dfi_cs_w7                  (ch0_dfi_cs_w7),
      .o_dfi_cke_w0                 (ch0_dfi_cke_w0),
      .o_dfi_cke_w1                 (ch0_dfi_cke_w1),
      .o_dfi_cke_w2                 (ch0_dfi_cke_w2),
      .o_dfi_cke_w3                 (ch0_dfi_cke_w3),
      .o_dfi_cke_w4                 (ch0_dfi_cke_w4),
      .o_dfi_cke_w5                 (ch0_dfi_cke_w5),
      .o_dfi_cke_w6                 (ch0_dfi_cke_w6),
      .o_dfi_cke_w7                 (ch0_dfi_cke_w7),
      .o_dfi_address_valid_w0       (ch0_dfi_address_valid_w0),
      .o_dfi_address_valid_w1       (ch0_dfi_address_valid_w1),
      .o_dfi_address_valid_w2       (ch0_dfi_address_valid_w2),
      .o_dfi_address_valid_w3       (ch0_dfi_address_valid_w3),
      .o_dfi_address_valid_w4       (ch0_dfi_address_valid_w4),
      .o_dfi_address_valid_w5       (ch0_dfi_address_valid_w5),
      .o_dfi_address_valid_w6       (ch0_dfi_address_valid_w6),
      .o_dfi_address_valid_w7       (ch0_dfi_address_valid_w7),

      .o_debug                       (ch0_dpca_debug)
   );

   ddr_dfi_dp_dq #(
      .NUM_DQ                       (NUM_DQ),
      .SWIDTH                       (SWIDTH),
      .MWIDTH                       (MWIDTH),
      .BWIDTH                       (BWIDTH),
      .TWIDTH                       (TWIDTH),
      .PWIDTH                       (PWIDTH),
      .NUM_WPH                      (NUM_WPH),
      .F0WIDTH                      (F0WIDTH),
      .F1WIDTH                      (F1WIDTH),
      .F2WIDTH                      (F2WIDTH),
      .MAXF2DLY                     (MAXF2DLY)
   ) u_ch0_dfi_dp_dq (

      //DFT
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),

      //Clock and Reset
      .i_rst                        (i_rst),
      .i_dfi_clk                    (dfi_clk),

      .i_rd_clk_1                   (rd_clk_1  ),
      .i_rd_clk_2                   (rd_clk_2  ),

      .i_wrd_clk_0                  (wrd_clk_0  ),
      .i_wrd_clk_1                  (wrd_clk_1  ),
      .i_wrd_clk_2                  (wrd_clk_2  ),
      .i_wrc_clk_0                  (wrc_clk_0  ),
      .i_wrc_clk_1                  (wrc_clk_1  ),
      .i_wrc_clk_2                  (wrc_clk_2  ),

      // Data Path Configuration
      .i_dfi_top_1_cfg              (dfich0_top_1_cfg    ),
      .i_dfi_rctrl_cfg              (dfich0_rctrl_cfg    ),
      .i_dfi_wctrl_cfg              (dfich0_wctrl_cfg    ),
      .i_dfi_wenctrl_cfg            (dfich0_wenctrl_cfg  ),
      .i_dfi_wckctrl_cfg            (dfich0_wckctrl_cfg  ),
      .i_dfi_wrd_cfg                (dfich0_wrd_cfg      ),
      .i_dfi_rdd_cfg                (dfich0_rdd_cfg      ),
      .i_dfi_ctrl0_cfg              (dfich0_ctrl0_cfg    ),
      .i_dfi_ctrl1_cfg              (dfich0_ctrl1_cfg    ),
      .i_dfi_ctrl2_cfg              (dfich0_ctrl2_cfg    ),
      .i_dfi_ctrl3_cfg              (dfich0_ctrl3_cfg    ),
      .i_dfi_ctrl4_cfg              (dfich0_ctrl4_cfg    ),
      .i_dfi_ctrl5_cfg              (dfich0_ctrl5_cfg    ),

      // Write Data Interface
      .i_dq0_dfi_wrdata_p0      (ch0_dq0_dfi_wrdata_p0),
      .i_dq0_dfi_wrdata_p1      (ch0_dq0_dfi_wrdata_p1),
      .i_dq0_dfi_wrdata_p2      (ch0_dq0_dfi_wrdata_p2),
      .i_dq0_dfi_wrdata_p3      (ch0_dq0_dfi_wrdata_p3),
      .i_dq0_dfi_wrdata_p4      (ch0_dq0_dfi_wrdata_p4),
      .i_dq0_dfi_wrdata_p5      (ch0_dq0_dfi_wrdata_p5),
      .i_dq0_dfi_wrdata_p6      (ch0_dq0_dfi_wrdata_p6),
      .i_dq0_dfi_wrdata_p7      (ch0_dq0_dfi_wrdata_p7),
      .i_dq0_dfi_wrdata_mask_p0 (ch0_dq0_dfi_wrdata_mask_p0),
      .i_dq0_dfi_wrdata_mask_p1 (ch0_dq0_dfi_wrdata_mask_p1),
      .i_dq0_dfi_wrdata_mask_p2 (ch0_dq0_dfi_wrdata_mask_p2),
      .i_dq0_dfi_wrdata_mask_p3 (ch0_dq0_dfi_wrdata_mask_p3),
      .i_dq0_dfi_wrdata_mask_p4 (ch0_dq0_dfi_wrdata_mask_p4),
      .i_dq0_dfi_wrdata_mask_p5 (ch0_dq0_dfi_wrdata_mask_p5),
      .i_dq0_dfi_wrdata_mask_p6 (ch0_dq0_dfi_wrdata_mask_p6),
      .i_dq0_dfi_wrdata_mask_p7 (ch0_dq0_dfi_wrdata_mask_p7),
      .o_dq0_dfi_wrdata_p0      (y_ch0_dq0_dfi_wrdata_p0),
      .o_dq0_dfi_wrdata_p1      (y_ch0_dq0_dfi_wrdata_p1),
      .o_dq0_dfi_wrdata_p2      (y_ch0_dq0_dfi_wrdata_p2),
      .o_dq0_dfi_wrdata_p3      (y_ch0_dq0_dfi_wrdata_p3),
      .o_dq0_dfi_wrdata_p4      (y_ch0_dq0_dfi_wrdata_p4),
      .o_dq0_dfi_wrdata_p5      (y_ch0_dq0_dfi_wrdata_p5),
      .o_dq0_dfi_wrdata_p6      (y_ch0_dq0_dfi_wrdata_p6),
      .o_dq0_dfi_wrdata_p7      (y_ch0_dq0_dfi_wrdata_p7),
      .o_dq0_dfi_wrdata_mask_p0 (y_ch0_dq0_dfi_wrdata_mask_p0),
      .o_dq0_dfi_wrdata_mask_p1 (y_ch0_dq0_dfi_wrdata_mask_p1),
      .o_dq0_dfi_wrdata_mask_p2 (y_ch0_dq0_dfi_wrdata_mask_p2),
      .o_dq0_dfi_wrdata_mask_p3 (y_ch0_dq0_dfi_wrdata_mask_p3),
      .o_dq0_dfi_wrdata_mask_p4 (y_ch0_dq0_dfi_wrdata_mask_p4),
      .o_dq0_dfi_wrdata_mask_p5 (y_ch0_dq0_dfi_wrdata_mask_p5),
      .o_dq0_dfi_wrdata_mask_p6 (y_ch0_dq0_dfi_wrdata_mask_p6),
      .o_dq0_dfi_wrdata_mask_p7 (y_ch0_dq0_dfi_wrdata_mask_p7),
      .i_dq0_dfi_wrdata_en_p0           (ch0_dq0_dfi_wrdata_en_p0),
      .i_dq0_dfi_wrdata_en_p1           (ch0_dq0_dfi_wrdata_en_p1),
      .i_dq0_dfi_wrdata_en_p2           (ch0_dq0_dfi_wrdata_en_p2),
      .i_dq0_dfi_wrdata_en_p3           (ch0_dq0_dfi_wrdata_en_p3),
      .i_dq0_dfi_wrdata_en_p4           (ch0_dq0_dfi_wrdata_en_p4),
      .i_dq0_dfi_wrdata_en_p5           (ch0_dq0_dfi_wrdata_en_p5),
      .i_dq0_dfi_wrdata_en_p6           (ch0_dq0_dfi_wrdata_en_p6),
      .i_dq0_dfi_wrdata_en_p7           (ch0_dq0_dfi_wrdata_en_p7),
      .i_dq0_dfi_parity_in_p0           (ch0_dq0_dfi_parity_in_p0),
      .i_dq0_dfi_parity_in_p1           (ch0_dq0_dfi_parity_in_p1),
      .i_dq0_dfi_parity_in_p2           (ch0_dq0_dfi_parity_in_p2),
      .i_dq0_dfi_parity_in_p3           (ch0_dq0_dfi_parity_in_p3),
      .i_dq0_dfi_parity_in_p4           (ch0_dq0_dfi_parity_in_p4),
      .i_dq0_dfi_parity_in_p5           (ch0_dq0_dfi_parity_in_p5),
      .i_dq0_dfi_parity_in_p6           (ch0_dq0_dfi_parity_in_p6),
      .i_dq0_dfi_parity_in_p7           (ch0_dq0_dfi_parity_in_p7),
      .i_dq0_dfi_wrdata_cs_p0           (ch0_dq0_dfi_wrdata_cs_p0),
      .i_dq0_dfi_wrdata_cs_p1           (ch0_dq0_dfi_wrdata_cs_p1),
      .i_dq0_dfi_wrdata_cs_p2           (ch0_dq0_dfi_wrdata_cs_p2),
      .i_dq0_dfi_wrdata_cs_p3           (ch0_dq0_dfi_wrdata_cs_p3),
      .i_dq0_dfi_wrdata_cs_p4           (ch0_dq0_dfi_wrdata_cs_p4),
      .i_dq0_dfi_wrdata_cs_p5           (ch0_dq0_dfi_wrdata_cs_p5),
      .i_dq0_dfi_wrdata_cs_p6           (ch0_dq0_dfi_wrdata_cs_p6),
      .i_dq0_dfi_wrdata_cs_p7           (ch0_dq0_dfi_wrdata_cs_p7),
      .i_dq0_dfi_wck_en_p0              (ch0_dq0_dfi_wck_en_p0),
      .i_dq0_dfi_wck_en_p1              (ch0_dq0_dfi_wck_en_p1),
      .i_dq0_dfi_wck_en_p2              (ch0_dq0_dfi_wck_en_p2),
      .i_dq0_dfi_wck_en_p3              (ch0_dq0_dfi_wck_en_p3),
      .i_dq0_dfi_wck_en_p4              (ch0_dq0_dfi_wck_en_p4),
      .i_dq0_dfi_wck_en_p5              (ch0_dq0_dfi_wck_en_p5),
      .i_dq0_dfi_wck_en_p6              (ch0_dq0_dfi_wck_en_p6),
      .i_dq0_dfi_wck_en_p7              (ch0_dq0_dfi_wck_en_p7),
      .i_dq0_dfi_wck_cs_p0              (ch0_dq0_dfi_wck_cs_p0),
      .i_dq0_dfi_wck_cs_p1              (ch0_dq0_dfi_wck_cs_p1),
      .i_dq0_dfi_wck_cs_p2              (ch0_dq0_dfi_wck_cs_p2),
      .i_dq0_dfi_wck_cs_p3              (ch0_dq0_dfi_wck_cs_p3),
      .i_dq0_dfi_wck_cs_p4              (ch0_dq0_dfi_wck_cs_p4),
      .i_dq0_dfi_wck_cs_p5              (ch0_dq0_dfi_wck_cs_p5),
      .i_dq0_dfi_wck_cs_p6              (ch0_dq0_dfi_wck_cs_p6),
      .i_dq0_dfi_wck_cs_p7              (ch0_dq0_dfi_wck_cs_p7),
      .i_dq0_dfi_wck_toggle_p0          (ch0_dq0_dfi_wck_toggle_p0),
      .i_dq0_dfi_wck_toggle_p1          (ch0_dq0_dfi_wck_toggle_p1),
      .i_dq0_dfi_wck_toggle_p2          (ch0_dq0_dfi_wck_toggle_p2),
      .i_dq0_dfi_wck_toggle_p3          (ch0_dq0_dfi_wck_toggle_p3),
      .i_dq0_dfi_wck_toggle_p4          (ch0_dq0_dfi_wck_toggle_p4),
      .i_dq0_dfi_wck_toggle_p5          (ch0_dq0_dfi_wck_toggle_p5),
      .i_dq0_dfi_wck_toggle_p6          (ch0_dq0_dfi_wck_toggle_p6),
      .i_dq0_dfi_wck_toggle_p7          (ch0_dq0_dfi_wck_toggle_p7),

      .o_dq0_dfi_wrdata_en_p0           (y_ch0_dq0_dfi_wrdata_en_p0),
      .o_dq0_dfi_wrdata_en_p1           (y_ch0_dq0_dfi_wrdata_en_p1),
      .o_dq0_dfi_wrdata_en_p2           (y_ch0_dq0_dfi_wrdata_en_p2),
      .o_dq0_dfi_wrdata_en_p3           (y_ch0_dq0_dfi_wrdata_en_p3),
      .o_dq0_dfi_wrdata_en_p4           (y_ch0_dq0_dfi_wrdata_en_p4),
      .o_dq0_dfi_wrdata_en_p5           (y_ch0_dq0_dfi_wrdata_en_p5),
      .o_dq0_dfi_wrdata_en_p6           (y_ch0_dq0_dfi_wrdata_en_p6),
      .o_dq0_dfi_wrdata_en_p7           (y_ch0_dq0_dfi_wrdata_en_p7),
      .o_dq0_dfi_wrdata_oe_p0           (y_ch0_dq0_dfi_wrdata_oe_p0),
      .o_dq0_dfi_wrdata_oe_p1           (y_ch0_dq0_dfi_wrdata_oe_p1),
      .o_dq0_dfi_wrdata_oe_p2           (y_ch0_dq0_dfi_wrdata_oe_p2),
      .o_dq0_dfi_wrdata_oe_p3           (y_ch0_dq0_dfi_wrdata_oe_p3),
      .o_dq0_dfi_wrdata_oe_p4           (y_ch0_dq0_dfi_wrdata_oe_p4),
      .o_dq0_dfi_wrdata_oe_p5           (y_ch0_dq0_dfi_wrdata_oe_p5),
      .o_dq0_dfi_wrdata_oe_p6           (y_ch0_dq0_dfi_wrdata_oe_p6),
      .o_dq0_dfi_wrdata_oe_p7           (y_ch0_dq0_dfi_wrdata_oe_p7),
      .o_dq0_dfi_parity_in_p0           (y_ch0_dq0_dfi_parity_in_p0),
      .o_dq0_dfi_parity_in_p1           (y_ch0_dq0_dfi_parity_in_p1),
      .o_dq0_dfi_parity_in_p2           (y_ch0_dq0_dfi_parity_in_p2),
      .o_dq0_dfi_parity_in_p3           (y_ch0_dq0_dfi_parity_in_p3),
      .o_dq0_dfi_parity_in_p4           (y_ch0_dq0_dfi_parity_in_p4),
      .o_dq0_dfi_parity_in_p5           (y_ch0_dq0_dfi_parity_in_p5),
      .o_dq0_dfi_parity_in_p6           (y_ch0_dq0_dfi_parity_in_p6),
      .o_dq0_dfi_parity_in_p7           (y_ch0_dq0_dfi_parity_in_p7),
      .o_dq0_dfi_wrdata_cs_p0           (y_ch0_dq0_dfi_wrdata_cs_p0),
      .o_dq0_dfi_wrdata_cs_p1           (y_ch0_dq0_dfi_wrdata_cs_p1),
      .o_dq0_dfi_wrdata_cs_p2           (y_ch0_dq0_dfi_wrdata_cs_p2),
      .o_dq0_dfi_wrdata_cs_p3           (y_ch0_dq0_dfi_wrdata_cs_p3),
      .o_dq0_dfi_wrdata_cs_p4           (y_ch0_dq0_dfi_wrdata_cs_p4),
      .o_dq0_dfi_wrdata_cs_p5           (y_ch0_dq0_dfi_wrdata_cs_p5),
      .o_dq0_dfi_wrdata_cs_p6           (y_ch0_dq0_dfi_wrdata_cs_p6),
      .o_dq0_dfi_wrdata_cs_p7           (y_ch0_dq0_dfi_wrdata_cs_p7),
      .o_dq0_dfi_wck_en_p0              (y_ch0_dq0_dfi_wck_en_p0),
      .o_dq0_dfi_wck_en_p1              (y_ch0_dq0_dfi_wck_en_p1),
      .o_dq0_dfi_wck_en_p2              (y_ch0_dq0_dfi_wck_en_p2),
      .o_dq0_dfi_wck_en_p3              (y_ch0_dq0_dfi_wck_en_p3),
      .o_dq0_dfi_wck_en_p4              (y_ch0_dq0_dfi_wck_en_p4),
      .o_dq0_dfi_wck_en_p5              (y_ch0_dq0_dfi_wck_en_p5),
      .o_dq0_dfi_wck_en_p6              (y_ch0_dq0_dfi_wck_en_p6),
      .o_dq0_dfi_wck_en_p7              (y_ch0_dq0_dfi_wck_en_p7),
      .o_dq0_dfi_wck_oe_p0              (y_ch0_dq0_dfi_wck_oe_p0),
      .o_dq0_dfi_wck_oe_p1              (y_ch0_dq0_dfi_wck_oe_p1),
      .o_dq0_dfi_wck_oe_p2              (y_ch0_dq0_dfi_wck_oe_p2),
      .o_dq0_dfi_wck_oe_p3              (y_ch0_dq0_dfi_wck_oe_p3),
      .o_dq0_dfi_wck_oe_p4              (y_ch0_dq0_dfi_wck_oe_p4),
      .o_dq0_dfi_wck_oe_p5              (y_ch0_dq0_dfi_wck_oe_p5),
      .o_dq0_dfi_wck_oe_p6              (y_ch0_dq0_dfi_wck_oe_p6),
      .o_dq0_dfi_wck_oe_p7              (y_ch0_dq0_dfi_wck_oe_p7),
      .o_dq0_dfi_wck_cs_p0              (y_ch0_dq0_dfi_wck_cs_p0),
      .o_dq0_dfi_wck_cs_p1              (y_ch0_dq0_dfi_wck_cs_p1),
      .o_dq0_dfi_wck_cs_p2              (y_ch0_dq0_dfi_wck_cs_p2),
      .o_dq0_dfi_wck_cs_p3              (y_ch0_dq0_dfi_wck_cs_p3),
      .o_dq0_dfi_wck_cs_p4              (y_ch0_dq0_dfi_wck_cs_p4),
      .o_dq0_dfi_wck_cs_p5              (y_ch0_dq0_dfi_wck_cs_p5),
      .o_dq0_dfi_wck_cs_p6              (y_ch0_dq0_dfi_wck_cs_p6),
      .o_dq0_dfi_wck_cs_p7              (y_ch0_dq0_dfi_wck_cs_p7),
      .o_dq0_dfi_wck_ten_p0             (y_ch0_dq0_dfi_wck_ten_p0),
      .o_dq0_dfi_wck_ten_p1             (y_ch0_dq0_dfi_wck_ten_p1),
      .o_dq0_dfi_wck_ten_p2             (y_ch0_dq0_dfi_wck_ten_p2),
      .o_dq0_dfi_wck_ten_p3             (y_ch0_dq0_dfi_wck_ten_p3),
      .o_dq0_dfi_wck_ten_p4             (y_ch0_dq0_dfi_wck_ten_p4),
      .o_dq0_dfi_wck_ten_p5             (y_ch0_dq0_dfi_wck_ten_p5),
      .o_dq0_dfi_wck_ten_p6             (y_ch0_dq0_dfi_wck_ten_p6),
      .o_dq0_dfi_wck_ten_p7             (y_ch0_dq0_dfi_wck_ten_p7),

   // Read Data En/CS
      .i_dq0_dfi_rddata_en_p0          (ch0_dq0_dfi_rddata_en_p0),
      .i_dq0_dfi_rddata_en_p1          (ch0_dq0_dfi_rddata_en_p1),
      .i_dq0_dfi_rddata_en_p2          (ch0_dq0_dfi_rddata_en_p2),
      .i_dq0_dfi_rddata_en_p3          (ch0_dq0_dfi_rddata_en_p3),
      .i_dq0_dfi_rddata_en_p4          (ch0_dq0_dfi_rddata_en_p4),
      .i_dq0_dfi_rddata_en_p5          (ch0_dq0_dfi_rddata_en_p5),
      .i_dq0_dfi_rddata_en_p6          (ch0_dq0_dfi_rddata_en_p6),
      .i_dq0_dfi_rddata_en_p7          (ch0_dq0_dfi_rddata_en_p7),

      .i_dq0_dfi_rddata_cs_p0          (ch0_dq0_dfi_rddata_cs_p0),
      .i_dq0_dfi_rddata_cs_p1          (ch0_dq0_dfi_rddata_cs_p1),
      .i_dq0_dfi_rddata_cs_p2          (ch0_dq0_dfi_rddata_cs_p2),
      .i_dq0_dfi_rddata_cs_p3          (ch0_dq0_dfi_rddata_cs_p3),
      .i_dq0_dfi_rddata_cs_p4          (ch0_dq0_dfi_rddata_cs_p4),
      .i_dq0_dfi_rddata_cs_p5          (ch0_dq0_dfi_rddata_cs_p5),
      .i_dq0_dfi_rddata_cs_p6          (ch0_dq0_dfi_rddata_cs_p6),
      .i_dq0_dfi_rddata_cs_p7          (ch0_dq0_dfi_rddata_cs_p7),

      .o_dq0_dfi_rddata_en_p0          (y_ch0_dq0_dfi_rddata_en_p0),
      .o_dq0_dfi_rddata_en_p1          (y_ch0_dq0_dfi_rddata_en_p1),
      .o_dq0_dfi_rddata_en_p2          (y_ch0_dq0_dfi_rddata_en_p2),
      .o_dq0_dfi_rddata_en_p3          (y_ch0_dq0_dfi_rddata_en_p3),
      .o_dq0_dfi_rddata_en_p4          (y_ch0_dq0_dfi_rddata_en_p4),
      .o_dq0_dfi_rddata_en_p5          (y_ch0_dq0_dfi_rddata_en_p5),
      .o_dq0_dfi_rddata_en_p6          (y_ch0_dq0_dfi_rddata_en_p6),
      .o_dq0_dfi_rddata_en_p7          (y_ch0_dq0_dfi_rddata_en_p7),
      .o_dq0_dfi_rddata_ie_p0          (y_ch0_dq0_dfi_rddata_ie_p0),
      .o_dq0_dfi_rddata_ie_p1          (y_ch0_dq0_dfi_rddata_ie_p1),
      .o_dq0_dfi_rddata_ie_p2          (y_ch0_dq0_dfi_rddata_ie_p2),
      .o_dq0_dfi_rddata_ie_p3          (y_ch0_dq0_dfi_rddata_ie_p3),
      .o_dq0_dfi_rddata_ie_p4          (y_ch0_dq0_dfi_rddata_ie_p4),
      .o_dq0_dfi_rddata_ie_p5          (y_ch0_dq0_dfi_rddata_ie_p5),
      .o_dq0_dfi_rddata_ie_p6          (y_ch0_dq0_dfi_rddata_ie_p6),
      .o_dq0_dfi_rddata_ie_p7          (y_ch0_dq0_dfi_rddata_ie_p7),
      .o_dq0_dfi_rddata_re_p0          (y_ch0_dq0_dfi_rddata_re_p0),
      .o_dq0_dfi_rddata_re_p1          (y_ch0_dq0_dfi_rddata_re_p1),
      .o_dq0_dfi_rddata_re_p2          (y_ch0_dq0_dfi_rddata_re_p2),
      .o_dq0_dfi_rddata_re_p3          (y_ch0_dq0_dfi_rddata_re_p3),
      .o_dq0_dfi_rddata_re_p4          (y_ch0_dq0_dfi_rddata_re_p4),
      .o_dq0_dfi_rddata_re_p5          (y_ch0_dq0_dfi_rddata_re_p5),
      .o_dq0_dfi_rddata_re_p6          (y_ch0_dq0_dfi_rddata_re_p6),
      .o_dq0_dfi_rddata_re_p7          (y_ch0_dq0_dfi_rddata_re_p7),
      .o_dq0_dfi_rddata_cs_p0          (y_ch0_dq0_dfi_rddata_cs_p0),
      .o_dq0_dfi_rddata_cs_p1          (y_ch0_dq0_dfi_rddata_cs_p1),
      .o_dq0_dfi_rddata_cs_p2          (y_ch0_dq0_dfi_rddata_cs_p2),
      .o_dq0_dfi_rddata_cs_p3          (y_ch0_dq0_dfi_rddata_cs_p3),
      .o_dq0_dfi_rddata_cs_p4          (y_ch0_dq0_dfi_rddata_cs_p4),
      .o_dq0_dfi_rddata_cs_p5          (y_ch0_dq0_dfi_rddata_cs_p5),
      .o_dq0_dfi_rddata_cs_p6          (y_ch0_dq0_dfi_rddata_cs_p6),
      .o_dq0_dfi_rddata_cs_p7          (y_ch0_dq0_dfi_rddata_cs_p7),
      .i_dq1_dfi_wrdata_p0      (ch0_dq1_dfi_wrdata_p0),
      .i_dq1_dfi_wrdata_p1      (ch0_dq1_dfi_wrdata_p1),
      .i_dq1_dfi_wrdata_p2      (ch0_dq1_dfi_wrdata_p2),
      .i_dq1_dfi_wrdata_p3      (ch0_dq1_dfi_wrdata_p3),
      .i_dq1_dfi_wrdata_p4      (ch0_dq1_dfi_wrdata_p4),
      .i_dq1_dfi_wrdata_p5      (ch0_dq1_dfi_wrdata_p5),
      .i_dq1_dfi_wrdata_p6      (ch0_dq1_dfi_wrdata_p6),
      .i_dq1_dfi_wrdata_p7      (ch0_dq1_dfi_wrdata_p7),
      .i_dq1_dfi_wrdata_mask_p0 (ch0_dq1_dfi_wrdata_mask_p0),
      .i_dq1_dfi_wrdata_mask_p1 (ch0_dq1_dfi_wrdata_mask_p1),
      .i_dq1_dfi_wrdata_mask_p2 (ch0_dq1_dfi_wrdata_mask_p2),
      .i_dq1_dfi_wrdata_mask_p3 (ch0_dq1_dfi_wrdata_mask_p3),
      .i_dq1_dfi_wrdata_mask_p4 (ch0_dq1_dfi_wrdata_mask_p4),
      .i_dq1_dfi_wrdata_mask_p5 (ch0_dq1_dfi_wrdata_mask_p5),
      .i_dq1_dfi_wrdata_mask_p6 (ch0_dq1_dfi_wrdata_mask_p6),
      .i_dq1_dfi_wrdata_mask_p7 (ch0_dq1_dfi_wrdata_mask_p7),
      .o_dq1_dfi_wrdata_p0      (y_ch0_dq1_dfi_wrdata_p0),
      .o_dq1_dfi_wrdata_p1      (y_ch0_dq1_dfi_wrdata_p1),
      .o_dq1_dfi_wrdata_p2      (y_ch0_dq1_dfi_wrdata_p2),
      .o_dq1_dfi_wrdata_p3      (y_ch0_dq1_dfi_wrdata_p3),
      .o_dq1_dfi_wrdata_p4      (y_ch0_dq1_dfi_wrdata_p4),
      .o_dq1_dfi_wrdata_p5      (y_ch0_dq1_dfi_wrdata_p5),
      .o_dq1_dfi_wrdata_p6      (y_ch0_dq1_dfi_wrdata_p6),
      .o_dq1_dfi_wrdata_p7      (y_ch0_dq1_dfi_wrdata_p7),
      .o_dq1_dfi_wrdata_mask_p0 (y_ch0_dq1_dfi_wrdata_mask_p0),
      .o_dq1_dfi_wrdata_mask_p1 (y_ch0_dq1_dfi_wrdata_mask_p1),
      .o_dq1_dfi_wrdata_mask_p2 (y_ch0_dq1_dfi_wrdata_mask_p2),
      .o_dq1_dfi_wrdata_mask_p3 (y_ch0_dq1_dfi_wrdata_mask_p3),
      .o_dq1_dfi_wrdata_mask_p4 (y_ch0_dq1_dfi_wrdata_mask_p4),
      .o_dq1_dfi_wrdata_mask_p5 (y_ch0_dq1_dfi_wrdata_mask_p5),
      .o_dq1_dfi_wrdata_mask_p6 (y_ch0_dq1_dfi_wrdata_mask_p6),
      .o_dq1_dfi_wrdata_mask_p7 (y_ch0_dq1_dfi_wrdata_mask_p7),
      .i_dq1_dfi_wrdata_en_p0           (ch0_dq1_dfi_wrdata_en_p0),
      .i_dq1_dfi_wrdata_en_p1           (ch0_dq1_dfi_wrdata_en_p1),
      .i_dq1_dfi_wrdata_en_p2           (ch0_dq1_dfi_wrdata_en_p2),
      .i_dq1_dfi_wrdata_en_p3           (ch0_dq1_dfi_wrdata_en_p3),
      .i_dq1_dfi_wrdata_en_p4           (ch0_dq1_dfi_wrdata_en_p4),
      .i_dq1_dfi_wrdata_en_p5           (ch0_dq1_dfi_wrdata_en_p5),
      .i_dq1_dfi_wrdata_en_p6           (ch0_dq1_dfi_wrdata_en_p6),
      .i_dq1_dfi_wrdata_en_p7           (ch0_dq1_dfi_wrdata_en_p7),
      .i_dq1_dfi_parity_in_p0           (ch0_dq1_dfi_parity_in_p0),
      .i_dq1_dfi_parity_in_p1           (ch0_dq1_dfi_parity_in_p1),
      .i_dq1_dfi_parity_in_p2           (ch0_dq1_dfi_parity_in_p2),
      .i_dq1_dfi_parity_in_p3           (ch0_dq1_dfi_parity_in_p3),
      .i_dq1_dfi_parity_in_p4           (ch0_dq1_dfi_parity_in_p4),
      .i_dq1_dfi_parity_in_p5           (ch0_dq1_dfi_parity_in_p5),
      .i_dq1_dfi_parity_in_p6           (ch0_dq1_dfi_parity_in_p6),
      .i_dq1_dfi_parity_in_p7           (ch0_dq1_dfi_parity_in_p7),
      .i_dq1_dfi_wrdata_cs_p0           (ch0_dq1_dfi_wrdata_cs_p0),
      .i_dq1_dfi_wrdata_cs_p1           (ch0_dq1_dfi_wrdata_cs_p1),
      .i_dq1_dfi_wrdata_cs_p2           (ch0_dq1_dfi_wrdata_cs_p2),
      .i_dq1_dfi_wrdata_cs_p3           (ch0_dq1_dfi_wrdata_cs_p3),
      .i_dq1_dfi_wrdata_cs_p4           (ch0_dq1_dfi_wrdata_cs_p4),
      .i_dq1_dfi_wrdata_cs_p5           (ch0_dq1_dfi_wrdata_cs_p5),
      .i_dq1_dfi_wrdata_cs_p6           (ch0_dq1_dfi_wrdata_cs_p6),
      .i_dq1_dfi_wrdata_cs_p7           (ch0_dq1_dfi_wrdata_cs_p7),
      .i_dq1_dfi_wck_en_p0              (ch0_dq1_dfi_wck_en_p0),
      .i_dq1_dfi_wck_en_p1              (ch0_dq1_dfi_wck_en_p1),
      .i_dq1_dfi_wck_en_p2              (ch0_dq1_dfi_wck_en_p2),
      .i_dq1_dfi_wck_en_p3              (ch0_dq1_dfi_wck_en_p3),
      .i_dq1_dfi_wck_en_p4              (ch0_dq1_dfi_wck_en_p4),
      .i_dq1_dfi_wck_en_p5              (ch0_dq1_dfi_wck_en_p5),
      .i_dq1_dfi_wck_en_p6              (ch0_dq1_dfi_wck_en_p6),
      .i_dq1_dfi_wck_en_p7              (ch0_dq1_dfi_wck_en_p7),
      .i_dq1_dfi_wck_cs_p0              (ch0_dq1_dfi_wck_cs_p0),
      .i_dq1_dfi_wck_cs_p1              (ch0_dq1_dfi_wck_cs_p1),
      .i_dq1_dfi_wck_cs_p2              (ch0_dq1_dfi_wck_cs_p2),
      .i_dq1_dfi_wck_cs_p3              (ch0_dq1_dfi_wck_cs_p3),
      .i_dq1_dfi_wck_cs_p4              (ch0_dq1_dfi_wck_cs_p4),
      .i_dq1_dfi_wck_cs_p5              (ch0_dq1_dfi_wck_cs_p5),
      .i_dq1_dfi_wck_cs_p6              (ch0_dq1_dfi_wck_cs_p6),
      .i_dq1_dfi_wck_cs_p7              (ch0_dq1_dfi_wck_cs_p7),
      .i_dq1_dfi_wck_toggle_p0          (ch0_dq1_dfi_wck_toggle_p0),
      .i_dq1_dfi_wck_toggle_p1          (ch0_dq1_dfi_wck_toggle_p1),
      .i_dq1_dfi_wck_toggle_p2          (ch0_dq1_dfi_wck_toggle_p2),
      .i_dq1_dfi_wck_toggle_p3          (ch0_dq1_dfi_wck_toggle_p3),
      .i_dq1_dfi_wck_toggle_p4          (ch0_dq1_dfi_wck_toggle_p4),
      .i_dq1_dfi_wck_toggle_p5          (ch0_dq1_dfi_wck_toggle_p5),
      .i_dq1_dfi_wck_toggle_p6          (ch0_dq1_dfi_wck_toggle_p6),
      .i_dq1_dfi_wck_toggle_p7          (ch0_dq1_dfi_wck_toggle_p7),

      .o_dq1_dfi_wrdata_en_p0           (y_ch0_dq1_dfi_wrdata_en_p0),
      .o_dq1_dfi_wrdata_en_p1           (y_ch0_dq1_dfi_wrdata_en_p1),
      .o_dq1_dfi_wrdata_en_p2           (y_ch0_dq1_dfi_wrdata_en_p2),
      .o_dq1_dfi_wrdata_en_p3           (y_ch0_dq1_dfi_wrdata_en_p3),
      .o_dq1_dfi_wrdata_en_p4           (y_ch0_dq1_dfi_wrdata_en_p4),
      .o_dq1_dfi_wrdata_en_p5           (y_ch0_dq1_dfi_wrdata_en_p5),
      .o_dq1_dfi_wrdata_en_p6           (y_ch0_dq1_dfi_wrdata_en_p6),
      .o_dq1_dfi_wrdata_en_p7           (y_ch0_dq1_dfi_wrdata_en_p7),
      .o_dq1_dfi_wrdata_oe_p0           (y_ch0_dq1_dfi_wrdata_oe_p0),
      .o_dq1_dfi_wrdata_oe_p1           (y_ch0_dq1_dfi_wrdata_oe_p1),
      .o_dq1_dfi_wrdata_oe_p2           (y_ch0_dq1_dfi_wrdata_oe_p2),
      .o_dq1_dfi_wrdata_oe_p3           (y_ch0_dq1_dfi_wrdata_oe_p3),
      .o_dq1_dfi_wrdata_oe_p4           (y_ch0_dq1_dfi_wrdata_oe_p4),
      .o_dq1_dfi_wrdata_oe_p5           (y_ch0_dq1_dfi_wrdata_oe_p5),
      .o_dq1_dfi_wrdata_oe_p6           (y_ch0_dq1_dfi_wrdata_oe_p6),
      .o_dq1_dfi_wrdata_oe_p7           (y_ch0_dq1_dfi_wrdata_oe_p7),
      .o_dq1_dfi_parity_in_p0           (y_ch0_dq1_dfi_parity_in_p0),
      .o_dq1_dfi_parity_in_p1           (y_ch0_dq1_dfi_parity_in_p1),
      .o_dq1_dfi_parity_in_p2           (y_ch0_dq1_dfi_parity_in_p2),
      .o_dq1_dfi_parity_in_p3           (y_ch0_dq1_dfi_parity_in_p3),
      .o_dq1_dfi_parity_in_p4           (y_ch0_dq1_dfi_parity_in_p4),
      .o_dq1_dfi_parity_in_p5           (y_ch0_dq1_dfi_parity_in_p5),
      .o_dq1_dfi_parity_in_p6           (y_ch0_dq1_dfi_parity_in_p6),
      .o_dq1_dfi_parity_in_p7           (y_ch0_dq1_dfi_parity_in_p7),
      .o_dq1_dfi_wrdata_cs_p0           (y_ch0_dq1_dfi_wrdata_cs_p0),
      .o_dq1_dfi_wrdata_cs_p1           (y_ch0_dq1_dfi_wrdata_cs_p1),
      .o_dq1_dfi_wrdata_cs_p2           (y_ch0_dq1_dfi_wrdata_cs_p2),
      .o_dq1_dfi_wrdata_cs_p3           (y_ch0_dq1_dfi_wrdata_cs_p3),
      .o_dq1_dfi_wrdata_cs_p4           (y_ch0_dq1_dfi_wrdata_cs_p4),
      .o_dq1_dfi_wrdata_cs_p5           (y_ch0_dq1_dfi_wrdata_cs_p5),
      .o_dq1_dfi_wrdata_cs_p6           (y_ch0_dq1_dfi_wrdata_cs_p6),
      .o_dq1_dfi_wrdata_cs_p7           (y_ch0_dq1_dfi_wrdata_cs_p7),
      .o_dq1_dfi_wck_en_p0              (y_ch0_dq1_dfi_wck_en_p0),
      .o_dq1_dfi_wck_en_p1              (y_ch0_dq1_dfi_wck_en_p1),
      .o_dq1_dfi_wck_en_p2              (y_ch0_dq1_dfi_wck_en_p2),
      .o_dq1_dfi_wck_en_p3              (y_ch0_dq1_dfi_wck_en_p3),
      .o_dq1_dfi_wck_en_p4              (y_ch0_dq1_dfi_wck_en_p4),
      .o_dq1_dfi_wck_en_p5              (y_ch0_dq1_dfi_wck_en_p5),
      .o_dq1_dfi_wck_en_p6              (y_ch0_dq1_dfi_wck_en_p6),
      .o_dq1_dfi_wck_en_p7              (y_ch0_dq1_dfi_wck_en_p7),
      .o_dq1_dfi_wck_oe_p0              (y_ch0_dq1_dfi_wck_oe_p0),
      .o_dq1_dfi_wck_oe_p1              (y_ch0_dq1_dfi_wck_oe_p1),
      .o_dq1_dfi_wck_oe_p2              (y_ch0_dq1_dfi_wck_oe_p2),
      .o_dq1_dfi_wck_oe_p3              (y_ch0_dq1_dfi_wck_oe_p3),
      .o_dq1_dfi_wck_oe_p4              (y_ch0_dq1_dfi_wck_oe_p4),
      .o_dq1_dfi_wck_oe_p5              (y_ch0_dq1_dfi_wck_oe_p5),
      .o_dq1_dfi_wck_oe_p6              (y_ch0_dq1_dfi_wck_oe_p6),
      .o_dq1_dfi_wck_oe_p7              (y_ch0_dq1_dfi_wck_oe_p7),
      .o_dq1_dfi_wck_cs_p0              (y_ch0_dq1_dfi_wck_cs_p0),
      .o_dq1_dfi_wck_cs_p1              (y_ch0_dq1_dfi_wck_cs_p1),
      .o_dq1_dfi_wck_cs_p2              (y_ch0_dq1_dfi_wck_cs_p2),
      .o_dq1_dfi_wck_cs_p3              (y_ch0_dq1_dfi_wck_cs_p3),
      .o_dq1_dfi_wck_cs_p4              (y_ch0_dq1_dfi_wck_cs_p4),
      .o_dq1_dfi_wck_cs_p5              (y_ch0_dq1_dfi_wck_cs_p5),
      .o_dq1_dfi_wck_cs_p6              (y_ch0_dq1_dfi_wck_cs_p6),
      .o_dq1_dfi_wck_cs_p7              (y_ch0_dq1_dfi_wck_cs_p7),
      .o_dq1_dfi_wck_ten_p0             (y_ch0_dq1_dfi_wck_ten_p0),
      .o_dq1_dfi_wck_ten_p1             (y_ch0_dq1_dfi_wck_ten_p1),
      .o_dq1_dfi_wck_ten_p2             (y_ch0_dq1_dfi_wck_ten_p2),
      .o_dq1_dfi_wck_ten_p3             (y_ch0_dq1_dfi_wck_ten_p3),
      .o_dq1_dfi_wck_ten_p4             (y_ch0_dq1_dfi_wck_ten_p4),
      .o_dq1_dfi_wck_ten_p5             (y_ch0_dq1_dfi_wck_ten_p5),
      .o_dq1_dfi_wck_ten_p6             (y_ch0_dq1_dfi_wck_ten_p6),
      .o_dq1_dfi_wck_ten_p7             (y_ch0_dq1_dfi_wck_ten_p7),

   // Read Data En/CS
      .i_dq1_dfi_rddata_en_p0          (ch0_dq1_dfi_rddata_en_p0),
      .i_dq1_dfi_rddata_en_p1          (ch0_dq1_dfi_rddata_en_p1),
      .i_dq1_dfi_rddata_en_p2          (ch0_dq1_dfi_rddata_en_p2),
      .i_dq1_dfi_rddata_en_p3          (ch0_dq1_dfi_rddata_en_p3),
      .i_dq1_dfi_rddata_en_p4          (ch0_dq1_dfi_rddata_en_p4),
      .i_dq1_dfi_rddata_en_p5          (ch0_dq1_dfi_rddata_en_p5),
      .i_dq1_dfi_rddata_en_p6          (ch0_dq1_dfi_rddata_en_p6),
      .i_dq1_dfi_rddata_en_p7          (ch0_dq1_dfi_rddata_en_p7),

      .i_dq1_dfi_rddata_cs_p0          (ch0_dq1_dfi_rddata_cs_p0),
      .i_dq1_dfi_rddata_cs_p1          (ch0_dq1_dfi_rddata_cs_p1),
      .i_dq1_dfi_rddata_cs_p2          (ch0_dq1_dfi_rddata_cs_p2),
      .i_dq1_dfi_rddata_cs_p3          (ch0_dq1_dfi_rddata_cs_p3),
      .i_dq1_dfi_rddata_cs_p4          (ch0_dq1_dfi_rddata_cs_p4),
      .i_dq1_dfi_rddata_cs_p5          (ch0_dq1_dfi_rddata_cs_p5),
      .i_dq1_dfi_rddata_cs_p6          (ch0_dq1_dfi_rddata_cs_p6),
      .i_dq1_dfi_rddata_cs_p7          (ch0_dq1_dfi_rddata_cs_p7),

      .o_dq1_dfi_rddata_en_p0          (y_ch0_dq1_dfi_rddata_en_p0),
      .o_dq1_dfi_rddata_en_p1          (y_ch0_dq1_dfi_rddata_en_p1),
      .o_dq1_dfi_rddata_en_p2          (y_ch0_dq1_dfi_rddata_en_p2),
      .o_dq1_dfi_rddata_en_p3          (y_ch0_dq1_dfi_rddata_en_p3),
      .o_dq1_dfi_rddata_en_p4          (y_ch0_dq1_dfi_rddata_en_p4),
      .o_dq1_dfi_rddata_en_p5          (y_ch0_dq1_dfi_rddata_en_p5),
      .o_dq1_dfi_rddata_en_p6          (y_ch0_dq1_dfi_rddata_en_p6),
      .o_dq1_dfi_rddata_en_p7          (y_ch0_dq1_dfi_rddata_en_p7),
      .o_dq1_dfi_rddata_ie_p0          (y_ch0_dq1_dfi_rddata_ie_p0),
      .o_dq1_dfi_rddata_ie_p1          (y_ch0_dq1_dfi_rddata_ie_p1),
      .o_dq1_dfi_rddata_ie_p2          (y_ch0_dq1_dfi_rddata_ie_p2),
      .o_dq1_dfi_rddata_ie_p3          (y_ch0_dq1_dfi_rddata_ie_p3),
      .o_dq1_dfi_rddata_ie_p4          (y_ch0_dq1_dfi_rddata_ie_p4),
      .o_dq1_dfi_rddata_ie_p5          (y_ch0_dq1_dfi_rddata_ie_p5),
      .o_dq1_dfi_rddata_ie_p6          (y_ch0_dq1_dfi_rddata_ie_p6),
      .o_dq1_dfi_rddata_ie_p7          (y_ch0_dq1_dfi_rddata_ie_p7),
      .o_dq1_dfi_rddata_re_p0          (y_ch0_dq1_dfi_rddata_re_p0),
      .o_dq1_dfi_rddata_re_p1          (y_ch0_dq1_dfi_rddata_re_p1),
      .o_dq1_dfi_rddata_re_p2          (y_ch0_dq1_dfi_rddata_re_p2),
      .o_dq1_dfi_rddata_re_p3          (y_ch0_dq1_dfi_rddata_re_p3),
      .o_dq1_dfi_rddata_re_p4          (y_ch0_dq1_dfi_rddata_re_p4),
      .o_dq1_dfi_rddata_re_p5          (y_ch0_dq1_dfi_rddata_re_p5),
      .o_dq1_dfi_rddata_re_p6          (y_ch0_dq1_dfi_rddata_re_p6),
      .o_dq1_dfi_rddata_re_p7          (y_ch0_dq1_dfi_rddata_re_p7),
      .o_dq1_dfi_rddata_cs_p0          (y_ch0_dq1_dfi_rddata_cs_p0),
      .o_dq1_dfi_rddata_cs_p1          (y_ch0_dq1_dfi_rddata_cs_p1),
      .o_dq1_dfi_rddata_cs_p2          (y_ch0_dq1_dfi_rddata_cs_p2),
      .o_dq1_dfi_rddata_cs_p3          (y_ch0_dq1_dfi_rddata_cs_p3),
      .o_dq1_dfi_rddata_cs_p4          (y_ch0_dq1_dfi_rddata_cs_p4),
      .o_dq1_dfi_rddata_cs_p5          (y_ch0_dq1_dfi_rddata_cs_p5),
      .o_dq1_dfi_rddata_cs_p6          (y_ch0_dq1_dfi_rddata_cs_p6),
      .o_dq1_dfi_rddata_cs_p7          (y_ch0_dq1_dfi_rddata_cs_p7),

      // Read Data Interface
      .i_dq0_dfi_rddata_w0          (y_ch0_dq0_dfi_rddata_w0),
      .i_dq0_dfi_rddata_w1          (y_ch0_dq0_dfi_rddata_w1),
      .i_dq0_dfi_rddata_w2          (y_ch0_dq0_dfi_rddata_w2),
      .i_dq0_dfi_rddata_w3          (y_ch0_dq0_dfi_rddata_w3),
      .i_dq0_dfi_rddata_w4          (y_ch0_dq0_dfi_rddata_w4),
      .i_dq0_dfi_rddata_w5          (y_ch0_dq0_dfi_rddata_w5),
      .i_dq0_dfi_rddata_w6          (y_ch0_dq0_dfi_rddata_w6),
      .i_dq0_dfi_rddata_w7          (y_ch0_dq0_dfi_rddata_w7),
      .i_dq0_dfi_rddata_dbi_w0      (y_ch0_dq0_dfi_rddata_dbi_w0),
      .i_dq0_dfi_rddata_dbi_w1      (y_ch0_dq0_dfi_rddata_dbi_w1),
      .i_dq0_dfi_rddata_dbi_w2      (y_ch0_dq0_dfi_rddata_dbi_w2),
      .i_dq0_dfi_rddata_dbi_w3      (y_ch0_dq0_dfi_rddata_dbi_w3),
      .i_dq0_dfi_rddata_dbi_w4      (y_ch0_dq0_dfi_rddata_dbi_w4),
      .i_dq0_dfi_rddata_dbi_w5      (y_ch0_dq0_dfi_rddata_dbi_w5),
      .i_dq0_dfi_rddata_dbi_w6      (y_ch0_dq0_dfi_rddata_dbi_w6),
      .i_dq0_dfi_rddata_dbi_w7      (y_ch0_dq0_dfi_rddata_dbi_w7),
      .i_dq0_dfi_rddata_valid       (y_ch0_dq0_dfi_rddata_valid),
      .i_dq1_dfi_rddata_w0          (y_ch0_dq1_dfi_rddata_w0),
      .i_dq1_dfi_rddata_w1          (y_ch0_dq1_dfi_rddata_w1),
      .i_dq1_dfi_rddata_w2          (y_ch0_dq1_dfi_rddata_w2),
      .i_dq1_dfi_rddata_w3          (y_ch0_dq1_dfi_rddata_w3),
      .i_dq1_dfi_rddata_w4          (y_ch0_dq1_dfi_rddata_w4),
      .i_dq1_dfi_rddata_w5          (y_ch0_dq1_dfi_rddata_w5),
      .i_dq1_dfi_rddata_w6          (y_ch0_dq1_dfi_rddata_w6),
      .i_dq1_dfi_rddata_w7          (y_ch0_dq1_dfi_rddata_w7),
      .i_dq1_dfi_rddata_dbi_w0      (y_ch0_dq1_dfi_rddata_dbi_w0),
      .i_dq1_dfi_rddata_dbi_w1      (y_ch0_dq1_dfi_rddata_dbi_w1),
      .i_dq1_dfi_rddata_dbi_w2      (y_ch0_dq1_dfi_rddata_dbi_w2),
      .i_dq1_dfi_rddata_dbi_w3      (y_ch0_dq1_dfi_rddata_dbi_w3),
      .i_dq1_dfi_rddata_dbi_w4      (y_ch0_dq1_dfi_rddata_dbi_w4),
      .i_dq1_dfi_rddata_dbi_w5      (y_ch0_dq1_dfi_rddata_dbi_w5),
      .i_dq1_dfi_rddata_dbi_w6      (y_ch0_dq1_dfi_rddata_dbi_w6),
      .i_dq1_dfi_rddata_dbi_w7      (y_ch0_dq1_dfi_rddata_dbi_w7),
      .i_dq1_dfi_rddata_valid       (y_ch0_dq1_dfi_rddata_valid),

      .o_dfi_rddata_w0              (ch0_dfi_rddata_w0),
      .o_dfi_rddata_w1              (ch0_dfi_rddata_w1),
      .o_dfi_rddata_w2              (ch0_dfi_rddata_w2),
      .o_dfi_rddata_w3              (ch0_dfi_rddata_w3),
      .o_dfi_rddata_w4              (ch0_dfi_rddata_w4),
      .o_dfi_rddata_w5              (ch0_dfi_rddata_w5),
      .o_dfi_rddata_w6              (ch0_dfi_rddata_w6),
      .o_dfi_rddata_w7              (ch0_dfi_rddata_w7),
      .o_dfi_rddata_dbi_w0          (ch0_dfi_rddata_dbi_w0),
      .o_dfi_rddata_dbi_w1          (ch0_dfi_rddata_dbi_w1),
      .o_dfi_rddata_dbi_w2          (ch0_dfi_rddata_dbi_w2),
      .o_dfi_rddata_dbi_w3          (ch0_dfi_rddata_dbi_w3),
      .o_dfi_rddata_dbi_w4          (ch0_dfi_rddata_dbi_w4),
      .o_dfi_rddata_dbi_w5          (ch0_dfi_rddata_dbi_w5),
      .o_dfi_rddata_dbi_w6          (ch0_dfi_rddata_dbi_w6),
      .o_dfi_rddata_dbi_w7          (ch0_dfi_rddata_dbi_w7),
      .o_dfi_rddata_valid_w0        (ch0_dfi_rddata_valid_w0),
      .o_dfi_rddata_valid_w1        (ch0_dfi_rddata_valid_w1),
      .o_dfi_rddata_valid_w2        (ch0_dfi_rddata_valid_w2),
      .o_dfi_rddata_valid_w3        (ch0_dfi_rddata_valid_w3),
      .o_dfi_rddata_valid_w4        (ch0_dfi_rddata_valid_w4),
      .o_dfi_rddata_valid_w5        (ch0_dfi_rddata_valid_w5),
      .o_dfi_rddata_valid_w6        (ch0_dfi_rddata_valid_w6),
      .o_dfi_rddata_valid_w7        (ch0_dfi_rddata_valid_w7),
      .i_dq_dfi_rddata_valid_mask    (ch0_dfi_rdvalid_mask),

      .o_dqwr_debug                  (ch0_dpdqwr_debug),
      .o_dqrd_debug                  (ch0_dpdqrd_debug)
   );
   assign y_ch1_dfi_carddata_en_p0     =  dfich0_top_1_cfg[`DDR_DFICH_TOP_1_CFG_CA_RDDATA_EN_FIELD];
   assign y_ch1_dfi_carddata_en_p1     =  dfich0_top_1_cfg[`DDR_DFICH_TOP_1_CFG_CA_RDDATA_EN_FIELD];
   assign y_ch1_dfi_carddata_en_p2     =  dfich0_top_1_cfg[`DDR_DFICH_TOP_1_CFG_CA_RDDATA_EN_FIELD];
   assign y_ch1_dfi_carddata_en_p3     =  dfich0_top_1_cfg[`DDR_DFICH_TOP_1_CFG_CA_RDDATA_EN_FIELD];
   assign y_ch1_dfi_carddata_en_p4     =  dfich0_top_1_cfg[`DDR_DFICH_TOP_1_CFG_CA_RDDATA_EN_FIELD];
   assign y_ch1_dfi_carddata_en_p5     =  dfich0_top_1_cfg[`DDR_DFICH_TOP_1_CFG_CA_RDDATA_EN_FIELD];
   assign y_ch1_dfi_carddata_en_p6     =  dfich0_top_1_cfg[`DDR_DFICH_TOP_1_CFG_CA_RDDATA_EN_FIELD];
   assign y_ch1_dfi_carddata_en_p7     =  dfich0_top_1_cfg[`DDR_DFICH_TOP_1_CFG_CA_RDDATA_EN_FIELD];

   ddr_dfi_dp_ca #(
     .AWIDTH                        (AWIDTH),
     .CWIDTH                        (CWIDTH),
     .NUM_WPH                       (NUM_WPH),
     .F0WIDTH                       (F0WIDTH)
   ) u_ch1_dfi_dp_ca (

      //DFT
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_rst                        (i_rst),

      //Clock and Reset
      .i_dfi_clk                    (dfi_clk),

      .i_cmda_clk_0                 (cmda_clk_0  ),
      .i_cmda_clk_1                 (cmda_clk_1  ),
      .i_cmda_clk_2                 (cmda_clk_2  ),
      .i_cmdc_clk_0                 (cmdc_clk_0  ),
      .i_cmdc_clk_1                 (cmdc_clk_1  ),
      .i_cmdc_clk_2                 (cmdc_clk_2  ),

      .i_rd_clk_1                   (rd_clk_1  ),
      .i_rd_clk_2                   (rd_clk_2  ),

      // Data Path Configuration
      .i_dfi_ctrl0_cfg              (dfich0_ctrl0_cfg    ),
      .i_dfi_wrc_cfg                (dfich0_wrc_cfg      ),
      .i_dfi_wrcctrl_cfg            (dfich0_wrcctrl_cfg  ),
      .i_dfi_ckctrl_cfg             (dfich0_ckctrl_cfg   ),
      .i_dfi_rdc_cfg                (dfich0_rdc_cfg      ),

      // Write Command/Address Interface
      .i_dfi_address_p0             (ch1_dfi_address_p0),
      .i_dfi_address_p1             (ch1_dfi_address_p1),
      .i_dfi_address_p2             (ch1_dfi_address_p2),
      .i_dfi_address_p3             (ch1_dfi_address_p3),
      .i_dfi_address_p4             (ch1_dfi_address_p4),
      .i_dfi_address_p5             (ch1_dfi_address_p5),
      .i_dfi_address_p6             (ch1_dfi_address_p6),
      .i_dfi_address_p7             (ch1_dfi_address_p7),
      .i_dfi_cke_p0                 (ch1_dfi_cke_p0),
      .i_dfi_cke_p1                 (ch1_dfi_cke_p1),
      .i_dfi_cke_p2                 (ch1_dfi_cke_p2),
      .i_dfi_cke_p3                 (ch1_dfi_cke_p3),
      .i_dfi_cke_p4                 (ch1_dfi_cke_p4),
      .i_dfi_cke_p5                 (ch1_dfi_cke_p5),
      .i_dfi_cke_p6                 (ch1_dfi_cke_p6),
      .i_dfi_cke_p7                 (ch1_dfi_cke_p7),
      .i_dfi_cs_p0                  (ch1_dfi_cs_p0),
      .i_dfi_cs_p1                  (ch1_dfi_cs_p1),
      .i_dfi_cs_p2                  (ch1_dfi_cs_p2),
      .i_dfi_cs_p3                  (ch1_dfi_cs_p3),
      .i_dfi_cs_p4                  (ch1_dfi_cs_p4),
      .i_dfi_cs_p5                  (ch1_dfi_cs_p5),
      .i_dfi_cs_p6                  (ch1_dfi_cs_p6),
      .i_dfi_cs_p7                  (ch1_dfi_cs_p7),
      .i_dfi_dcd_p0                 (ch1_dfi_dram_clk_disable_p0),
      .i_dfi_dcd_p1                 (ch1_dfi_dram_clk_disable_p1),
      .i_dfi_dcd_p2                 (ch1_dfi_dram_clk_disable_p2),
      .i_dfi_dcd_p3                 (ch1_dfi_dram_clk_disable_p3),
      .i_dfi_dcd_p4                 (ch1_dfi_dram_clk_disable_p4),
      .i_dfi_dcd_p5                 (ch1_dfi_dram_clk_disable_p5),
      .i_dfi_dcd_p6                 (ch1_dfi_dram_clk_disable_p6),
      .i_dfi_dcd_p7                 (ch1_dfi_dram_clk_disable_p7),

      .o_dfi_address_p0             (y_ch1_dfi_address_p0),
      .o_dfi_address_p1             (y_ch1_dfi_address_p1),
      .o_dfi_address_p2             (y_ch1_dfi_address_p2),
      .o_dfi_address_p3             (y_ch1_dfi_address_p3),
      .o_dfi_address_p4             (y_ch1_dfi_address_p4),
      .o_dfi_address_p5             (y_ch1_dfi_address_p5),
      .o_dfi_address_p6             (y_ch1_dfi_address_p6),
      .o_dfi_address_p7             (y_ch1_dfi_address_p7),
      .o_dfi_cke_p0                 (y_ch1_dfi_cke_p0),
      .o_dfi_cke_p1                 (y_ch1_dfi_cke_p1),
      .o_dfi_cke_p2                 (y_ch1_dfi_cke_p2),
      .o_dfi_cke_p3                 (y_ch1_dfi_cke_p3),
      .o_dfi_cke_p4                 (y_ch1_dfi_cke_p4),
      .o_dfi_cke_p5                 (y_ch1_dfi_cke_p5),
      .o_dfi_cke_p6                 (y_ch1_dfi_cke_p6),
      .o_dfi_cke_p7                 (y_ch1_dfi_cke_p7),
      .o_dfi_cs_p0                  (y_ch1_dfi_cs_p0),
      .o_dfi_cs_p1                  (y_ch1_dfi_cs_p1),
      .o_dfi_cs_p2                  (y_ch1_dfi_cs_p2),
      .o_dfi_cs_p3                  (y_ch1_dfi_cs_p3),
      .o_dfi_cs_p4                  (y_ch1_dfi_cs_p4),
      .o_dfi_cs_p5                  (y_ch1_dfi_cs_p5),
      .o_dfi_cs_p6                  (y_ch1_dfi_cs_p6),
      .o_dfi_cs_p7                  (y_ch1_dfi_cs_p7),
      .o_dfi_dcd_p0                 (y_ch1_dfi_dram_clk_disable_p0),
      .o_dfi_dcd_p1                 (y_ch1_dfi_dram_clk_disable_p1),
      .o_dfi_dcd_p2                 (y_ch1_dfi_dram_clk_disable_p2),
      .o_dfi_dcd_p3                 (y_ch1_dfi_dram_clk_disable_p3),
      .o_dfi_dcd_p4                 (y_ch1_dfi_dram_clk_disable_p4),
      .o_dfi_dcd_p5                 (y_ch1_dfi_dram_clk_disable_p5),
      .o_dfi_dcd_p6                 (y_ch1_dfi_dram_clk_disable_p6),
      .o_dfi_dcd_p7                 (y_ch1_dfi_dram_clk_disable_p7),
      .o_dfi_dce_p0                 (y_ch1_dfi_dram_clk_enable_p0),
      .o_dfi_dce_p1                 (y_ch1_dfi_dram_clk_enable_p1),
      .o_dfi_dce_p2                 (y_ch1_dfi_dram_clk_enable_p2),
      .o_dfi_dce_p3                 (y_ch1_dfi_dram_clk_enable_p3),
      .o_dfi_dce_p4                 (y_ch1_dfi_dram_clk_enable_p4),
      .o_dfi_dce_p5                 (y_ch1_dfi_dram_clk_enable_p5),
      .o_dfi_dce_p6                 (y_ch1_dfi_dram_clk_enable_p6),
      .o_dfi_dce_p7                 (y_ch1_dfi_dram_clk_enable_p7),

      // Read Command/Address Interface
      .i_dfi_address_w0             (y_ch1_dfi_address_w0),
      .i_dfi_address_w1             (y_ch1_dfi_address_w1),
      .i_dfi_address_w2             (y_ch1_dfi_address_w2),
      .i_dfi_address_w3             (y_ch1_dfi_address_w3),
      .i_dfi_address_w4             (y_ch1_dfi_address_w4),
      .i_dfi_address_w5             (y_ch1_dfi_address_w5),
      .i_dfi_address_w6             (y_ch1_dfi_address_w6),
      .i_dfi_address_w7             (y_ch1_dfi_address_w7),
      .i_dfi_cs_w0                  (y_ch1_dfi_cs_w0),
      .i_dfi_cs_w1                  (y_ch1_dfi_cs_w1),
      .i_dfi_cs_w2                  (y_ch1_dfi_cs_w2),
      .i_dfi_cs_w3                  (y_ch1_dfi_cs_w3),
      .i_dfi_cs_w4                  (y_ch1_dfi_cs_w4),
      .i_dfi_cs_w5                  (y_ch1_dfi_cs_w5),
      .i_dfi_cs_w6                  (y_ch1_dfi_cs_w6),
      .i_dfi_cs_w7                  (y_ch1_dfi_cs_w7),
      .i_dfi_cke_w0                 (y_ch1_dfi_cke_w0),
      .i_dfi_cke_w1                 (y_ch1_dfi_cke_w1),
      .i_dfi_cke_w2                 (y_ch1_dfi_cke_w2),
      .i_dfi_cke_w3                 (y_ch1_dfi_cke_w3),
      .i_dfi_cke_w4                 (y_ch1_dfi_cke_w4),
      .i_dfi_cke_w5                 (y_ch1_dfi_cke_w5),
      .i_dfi_cke_w6                 (y_ch1_dfi_cke_w6),
      .i_dfi_cke_w7                 (y_ch1_dfi_cke_w7),
      .i_dfi_address_valid           (y_ch1_dfi_address_valid),

      .o_dfi_address_w0             (ch1_dfi_address_w0),
      .o_dfi_address_w1             (ch1_dfi_address_w1),
      .o_dfi_address_w2             (ch1_dfi_address_w2),
      .o_dfi_address_w3             (ch1_dfi_address_w3),
      .o_dfi_address_w4             (ch1_dfi_address_w4),
      .o_dfi_address_w5             (ch1_dfi_address_w5),
      .o_dfi_address_w6             (ch1_dfi_address_w6),
      .o_dfi_address_w7             (ch1_dfi_address_w7),
      .o_dfi_cs_w0                  (ch1_dfi_cs_w0),
      .o_dfi_cs_w1                  (ch1_dfi_cs_w1),
      .o_dfi_cs_w2                  (ch1_dfi_cs_w2),
      .o_dfi_cs_w3                  (ch1_dfi_cs_w3),
      .o_dfi_cs_w4                  (ch1_dfi_cs_w4),
      .o_dfi_cs_w5                  (ch1_dfi_cs_w5),
      .o_dfi_cs_w6                  (ch1_dfi_cs_w6),
      .o_dfi_cs_w7                  (ch1_dfi_cs_w7),
      .o_dfi_cke_w0                 (ch1_dfi_cke_w0),
      .o_dfi_cke_w1                 (ch1_dfi_cke_w1),
      .o_dfi_cke_w2                 (ch1_dfi_cke_w2),
      .o_dfi_cke_w3                 (ch1_dfi_cke_w3),
      .o_dfi_cke_w4                 (ch1_dfi_cke_w4),
      .o_dfi_cke_w5                 (ch1_dfi_cke_w5),
      .o_dfi_cke_w6                 (ch1_dfi_cke_w6),
      .o_dfi_cke_w7                 (ch1_dfi_cke_w7),
      .o_dfi_address_valid_w0       (ch1_dfi_address_valid_w0),
      .o_dfi_address_valid_w1       (ch1_dfi_address_valid_w1),
      .o_dfi_address_valid_w2       (ch1_dfi_address_valid_w2),
      .o_dfi_address_valid_w3       (ch1_dfi_address_valid_w3),
      .o_dfi_address_valid_w4       (ch1_dfi_address_valid_w4),
      .o_dfi_address_valid_w5       (ch1_dfi_address_valid_w5),
      .o_dfi_address_valid_w6       (ch1_dfi_address_valid_w6),
      .o_dfi_address_valid_w7       (ch1_dfi_address_valid_w7),

      .o_debug                       (ch1_dpca_debug)
   );

   ddr_dfi_dp_dq #(
      .NUM_DQ                       (NUM_DQ),
      .SWIDTH                       (SWIDTH),
      .MWIDTH                       (MWIDTH),
      .BWIDTH                       (BWIDTH),
      .TWIDTH                       (TWIDTH),
      .PWIDTH                       (PWIDTH),
      .NUM_WPH                      (NUM_WPH),
      .F0WIDTH                      (F0WIDTH),
      .F1WIDTH                      (F1WIDTH),
      .F2WIDTH                      (F2WIDTH),
      .MAXF2DLY                     (MAXF2DLY)
   ) u_ch1_dfi_dp_dq (

      //DFT
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),

      //Clock and Reset
      .i_rst                        (i_rst),
      .i_dfi_clk                    (dfi_clk),

      .i_rd_clk_1                   (rd_clk_1  ),
      .i_rd_clk_2                   (rd_clk_2  ),

      .i_wrd_clk_0                  (wrd_clk_0  ),
      .i_wrd_clk_1                  (wrd_clk_1  ),
      .i_wrd_clk_2                  (wrd_clk_2  ),
      .i_wrc_clk_0                  (wrc_clk_0  ),
      .i_wrc_clk_1                  (wrc_clk_1  ),
      .i_wrc_clk_2                  (wrc_clk_2  ),

      // Data Path Configuration
      .i_dfi_top_1_cfg              (dfich0_top_1_cfg    ),
      .i_dfi_rctrl_cfg              (dfich0_rctrl_cfg    ),
      .i_dfi_wctrl_cfg              (dfich0_wctrl_cfg    ),
      .i_dfi_wenctrl_cfg            (dfich0_wenctrl_cfg  ),
      .i_dfi_wckctrl_cfg            (dfich0_wckctrl_cfg  ),
      .i_dfi_wrd_cfg                (dfich0_wrd_cfg      ),
      .i_dfi_rdd_cfg                (dfich0_rdd_cfg      ),
      .i_dfi_ctrl0_cfg              (dfich0_ctrl0_cfg    ),
      .i_dfi_ctrl1_cfg              (dfich0_ctrl1_cfg    ),
      .i_dfi_ctrl2_cfg              (dfich0_ctrl2_cfg    ),
      .i_dfi_ctrl3_cfg              (dfich0_ctrl3_cfg    ),
      .i_dfi_ctrl4_cfg              (dfich0_ctrl4_cfg    ),
      .i_dfi_ctrl5_cfg              (dfich0_ctrl5_cfg    ),

      // Write Data Interface
      .i_dq0_dfi_wrdata_p0      (ch1_dq0_dfi_wrdata_p0),
      .i_dq0_dfi_wrdata_p1      (ch1_dq0_dfi_wrdata_p1),
      .i_dq0_dfi_wrdata_p2      (ch1_dq0_dfi_wrdata_p2),
      .i_dq0_dfi_wrdata_p3      (ch1_dq0_dfi_wrdata_p3),
      .i_dq0_dfi_wrdata_p4      (ch1_dq0_dfi_wrdata_p4),
      .i_dq0_dfi_wrdata_p5      (ch1_dq0_dfi_wrdata_p5),
      .i_dq0_dfi_wrdata_p6      (ch1_dq0_dfi_wrdata_p6),
      .i_dq0_dfi_wrdata_p7      (ch1_dq0_dfi_wrdata_p7),
      .i_dq0_dfi_wrdata_mask_p0 (ch1_dq0_dfi_wrdata_mask_p0),
      .i_dq0_dfi_wrdata_mask_p1 (ch1_dq0_dfi_wrdata_mask_p1),
      .i_dq0_dfi_wrdata_mask_p2 (ch1_dq0_dfi_wrdata_mask_p2),
      .i_dq0_dfi_wrdata_mask_p3 (ch1_dq0_dfi_wrdata_mask_p3),
      .i_dq0_dfi_wrdata_mask_p4 (ch1_dq0_dfi_wrdata_mask_p4),
      .i_dq0_dfi_wrdata_mask_p5 (ch1_dq0_dfi_wrdata_mask_p5),
      .i_dq0_dfi_wrdata_mask_p6 (ch1_dq0_dfi_wrdata_mask_p6),
      .i_dq0_dfi_wrdata_mask_p7 (ch1_dq0_dfi_wrdata_mask_p7),
      .o_dq0_dfi_wrdata_p0      (y_ch1_dq0_dfi_wrdata_p0),
      .o_dq0_dfi_wrdata_p1      (y_ch1_dq0_dfi_wrdata_p1),
      .o_dq0_dfi_wrdata_p2      (y_ch1_dq0_dfi_wrdata_p2),
      .o_dq0_dfi_wrdata_p3      (y_ch1_dq0_dfi_wrdata_p3),
      .o_dq0_dfi_wrdata_p4      (y_ch1_dq0_dfi_wrdata_p4),
      .o_dq0_dfi_wrdata_p5      (y_ch1_dq0_dfi_wrdata_p5),
      .o_dq0_dfi_wrdata_p6      (y_ch1_dq0_dfi_wrdata_p6),
      .o_dq0_dfi_wrdata_p7      (y_ch1_dq0_dfi_wrdata_p7),
      .o_dq0_dfi_wrdata_mask_p0 (y_ch1_dq0_dfi_wrdata_mask_p0),
      .o_dq0_dfi_wrdata_mask_p1 (y_ch1_dq0_dfi_wrdata_mask_p1),
      .o_dq0_dfi_wrdata_mask_p2 (y_ch1_dq0_dfi_wrdata_mask_p2),
      .o_dq0_dfi_wrdata_mask_p3 (y_ch1_dq0_dfi_wrdata_mask_p3),
      .o_dq0_dfi_wrdata_mask_p4 (y_ch1_dq0_dfi_wrdata_mask_p4),
      .o_dq0_dfi_wrdata_mask_p5 (y_ch1_dq0_dfi_wrdata_mask_p5),
      .o_dq0_dfi_wrdata_mask_p6 (y_ch1_dq0_dfi_wrdata_mask_p6),
      .o_dq0_dfi_wrdata_mask_p7 (y_ch1_dq0_dfi_wrdata_mask_p7),
      .i_dq0_dfi_wrdata_en_p0           (ch1_dq0_dfi_wrdata_en_p0),
      .i_dq0_dfi_wrdata_en_p1           (ch1_dq0_dfi_wrdata_en_p1),
      .i_dq0_dfi_wrdata_en_p2           (ch1_dq0_dfi_wrdata_en_p2),
      .i_dq0_dfi_wrdata_en_p3           (ch1_dq0_dfi_wrdata_en_p3),
      .i_dq0_dfi_wrdata_en_p4           (ch1_dq0_dfi_wrdata_en_p4),
      .i_dq0_dfi_wrdata_en_p5           (ch1_dq0_dfi_wrdata_en_p5),
      .i_dq0_dfi_wrdata_en_p6           (ch1_dq0_dfi_wrdata_en_p6),
      .i_dq0_dfi_wrdata_en_p7           (ch1_dq0_dfi_wrdata_en_p7),
      .i_dq0_dfi_parity_in_p0           (ch1_dq0_dfi_parity_in_p0),
      .i_dq0_dfi_parity_in_p1           (ch1_dq0_dfi_parity_in_p1),
      .i_dq0_dfi_parity_in_p2           (ch1_dq0_dfi_parity_in_p2),
      .i_dq0_dfi_parity_in_p3           (ch1_dq0_dfi_parity_in_p3),
      .i_dq0_dfi_parity_in_p4           (ch1_dq0_dfi_parity_in_p4),
      .i_dq0_dfi_parity_in_p5           (ch1_dq0_dfi_parity_in_p5),
      .i_dq0_dfi_parity_in_p6           (ch1_dq0_dfi_parity_in_p6),
      .i_dq0_dfi_parity_in_p7           (ch1_dq0_dfi_parity_in_p7),
      .i_dq0_dfi_wrdata_cs_p0           (ch1_dq0_dfi_wrdata_cs_p0),
      .i_dq0_dfi_wrdata_cs_p1           (ch1_dq0_dfi_wrdata_cs_p1),
      .i_dq0_dfi_wrdata_cs_p2           (ch1_dq0_dfi_wrdata_cs_p2),
      .i_dq0_dfi_wrdata_cs_p3           (ch1_dq0_dfi_wrdata_cs_p3),
      .i_dq0_dfi_wrdata_cs_p4           (ch1_dq0_dfi_wrdata_cs_p4),
      .i_dq0_dfi_wrdata_cs_p5           (ch1_dq0_dfi_wrdata_cs_p5),
      .i_dq0_dfi_wrdata_cs_p6           (ch1_dq0_dfi_wrdata_cs_p6),
      .i_dq0_dfi_wrdata_cs_p7           (ch1_dq0_dfi_wrdata_cs_p7),
      .i_dq0_dfi_wck_en_p0              (ch1_dq0_dfi_wck_en_p0),
      .i_dq0_dfi_wck_en_p1              (ch1_dq0_dfi_wck_en_p1),
      .i_dq0_dfi_wck_en_p2              (ch1_dq0_dfi_wck_en_p2),
      .i_dq0_dfi_wck_en_p3              (ch1_dq0_dfi_wck_en_p3),
      .i_dq0_dfi_wck_en_p4              (ch1_dq0_dfi_wck_en_p4),
      .i_dq0_dfi_wck_en_p5              (ch1_dq0_dfi_wck_en_p5),
      .i_dq0_dfi_wck_en_p6              (ch1_dq0_dfi_wck_en_p6),
      .i_dq0_dfi_wck_en_p7              (ch1_dq0_dfi_wck_en_p7),
      .i_dq0_dfi_wck_cs_p0              (ch1_dq0_dfi_wck_cs_p0),
      .i_dq0_dfi_wck_cs_p1              (ch1_dq0_dfi_wck_cs_p1),
      .i_dq0_dfi_wck_cs_p2              (ch1_dq0_dfi_wck_cs_p2),
      .i_dq0_dfi_wck_cs_p3              (ch1_dq0_dfi_wck_cs_p3),
      .i_dq0_dfi_wck_cs_p4              (ch1_dq0_dfi_wck_cs_p4),
      .i_dq0_dfi_wck_cs_p5              (ch1_dq0_dfi_wck_cs_p5),
      .i_dq0_dfi_wck_cs_p6              (ch1_dq0_dfi_wck_cs_p6),
      .i_dq0_dfi_wck_cs_p7              (ch1_dq0_dfi_wck_cs_p7),
      .i_dq0_dfi_wck_toggle_p0          (ch1_dq0_dfi_wck_toggle_p0),
      .i_dq0_dfi_wck_toggle_p1          (ch1_dq0_dfi_wck_toggle_p1),
      .i_dq0_dfi_wck_toggle_p2          (ch1_dq0_dfi_wck_toggle_p2),
      .i_dq0_dfi_wck_toggle_p3          (ch1_dq0_dfi_wck_toggle_p3),
      .i_dq0_dfi_wck_toggle_p4          (ch1_dq0_dfi_wck_toggle_p4),
      .i_dq0_dfi_wck_toggle_p5          (ch1_dq0_dfi_wck_toggle_p5),
      .i_dq0_dfi_wck_toggle_p6          (ch1_dq0_dfi_wck_toggle_p6),
      .i_dq0_dfi_wck_toggle_p7          (ch1_dq0_dfi_wck_toggle_p7),

      .o_dq0_dfi_wrdata_en_p0           (y_ch1_dq0_dfi_wrdata_en_p0),
      .o_dq0_dfi_wrdata_en_p1           (y_ch1_dq0_dfi_wrdata_en_p1),
      .o_dq0_dfi_wrdata_en_p2           (y_ch1_dq0_dfi_wrdata_en_p2),
      .o_dq0_dfi_wrdata_en_p3           (y_ch1_dq0_dfi_wrdata_en_p3),
      .o_dq0_dfi_wrdata_en_p4           (y_ch1_dq0_dfi_wrdata_en_p4),
      .o_dq0_dfi_wrdata_en_p5           (y_ch1_dq0_dfi_wrdata_en_p5),
      .o_dq0_dfi_wrdata_en_p6           (y_ch1_dq0_dfi_wrdata_en_p6),
      .o_dq0_dfi_wrdata_en_p7           (y_ch1_dq0_dfi_wrdata_en_p7),
      .o_dq0_dfi_wrdata_oe_p0           (y_ch1_dq0_dfi_wrdata_oe_p0),
      .o_dq0_dfi_wrdata_oe_p1           (y_ch1_dq0_dfi_wrdata_oe_p1),
      .o_dq0_dfi_wrdata_oe_p2           (y_ch1_dq0_dfi_wrdata_oe_p2),
      .o_dq0_dfi_wrdata_oe_p3           (y_ch1_dq0_dfi_wrdata_oe_p3),
      .o_dq0_dfi_wrdata_oe_p4           (y_ch1_dq0_dfi_wrdata_oe_p4),
      .o_dq0_dfi_wrdata_oe_p5           (y_ch1_dq0_dfi_wrdata_oe_p5),
      .o_dq0_dfi_wrdata_oe_p6           (y_ch1_dq0_dfi_wrdata_oe_p6),
      .o_dq0_dfi_wrdata_oe_p7           (y_ch1_dq0_dfi_wrdata_oe_p7),
      .o_dq0_dfi_parity_in_p0           (y_ch1_dq0_dfi_parity_in_p0),
      .o_dq0_dfi_parity_in_p1           (y_ch1_dq0_dfi_parity_in_p1),
      .o_dq0_dfi_parity_in_p2           (y_ch1_dq0_dfi_parity_in_p2),
      .o_dq0_dfi_parity_in_p3           (y_ch1_dq0_dfi_parity_in_p3),
      .o_dq0_dfi_parity_in_p4           (y_ch1_dq0_dfi_parity_in_p4),
      .o_dq0_dfi_parity_in_p5           (y_ch1_dq0_dfi_parity_in_p5),
      .o_dq0_dfi_parity_in_p6           (y_ch1_dq0_dfi_parity_in_p6),
      .o_dq0_dfi_parity_in_p7           (y_ch1_dq0_dfi_parity_in_p7),
      .o_dq0_dfi_wrdata_cs_p0           (y_ch1_dq0_dfi_wrdata_cs_p0),
      .o_dq0_dfi_wrdata_cs_p1           (y_ch1_dq0_dfi_wrdata_cs_p1),
      .o_dq0_dfi_wrdata_cs_p2           (y_ch1_dq0_dfi_wrdata_cs_p2),
      .o_dq0_dfi_wrdata_cs_p3           (y_ch1_dq0_dfi_wrdata_cs_p3),
      .o_dq0_dfi_wrdata_cs_p4           (y_ch1_dq0_dfi_wrdata_cs_p4),
      .o_dq0_dfi_wrdata_cs_p5           (y_ch1_dq0_dfi_wrdata_cs_p5),
      .o_dq0_dfi_wrdata_cs_p6           (y_ch1_dq0_dfi_wrdata_cs_p6),
      .o_dq0_dfi_wrdata_cs_p7           (y_ch1_dq0_dfi_wrdata_cs_p7),
      .o_dq0_dfi_wck_en_p0              (y_ch1_dq0_dfi_wck_en_p0),
      .o_dq0_dfi_wck_en_p1              (y_ch1_dq0_dfi_wck_en_p1),
      .o_dq0_dfi_wck_en_p2              (y_ch1_dq0_dfi_wck_en_p2),
      .o_dq0_dfi_wck_en_p3              (y_ch1_dq0_dfi_wck_en_p3),
      .o_dq0_dfi_wck_en_p4              (y_ch1_dq0_dfi_wck_en_p4),
      .o_dq0_dfi_wck_en_p5              (y_ch1_dq0_dfi_wck_en_p5),
      .o_dq0_dfi_wck_en_p6              (y_ch1_dq0_dfi_wck_en_p6),
      .o_dq0_dfi_wck_en_p7              (y_ch1_dq0_dfi_wck_en_p7),
      .o_dq0_dfi_wck_oe_p0              (y_ch1_dq0_dfi_wck_oe_p0),
      .o_dq0_dfi_wck_oe_p1              (y_ch1_dq0_dfi_wck_oe_p1),
      .o_dq0_dfi_wck_oe_p2              (y_ch1_dq0_dfi_wck_oe_p2),
      .o_dq0_dfi_wck_oe_p3              (y_ch1_dq0_dfi_wck_oe_p3),
      .o_dq0_dfi_wck_oe_p4              (y_ch1_dq0_dfi_wck_oe_p4),
      .o_dq0_dfi_wck_oe_p5              (y_ch1_dq0_dfi_wck_oe_p5),
      .o_dq0_dfi_wck_oe_p6              (y_ch1_dq0_dfi_wck_oe_p6),
      .o_dq0_dfi_wck_oe_p7              (y_ch1_dq0_dfi_wck_oe_p7),
      .o_dq0_dfi_wck_cs_p0              (y_ch1_dq0_dfi_wck_cs_p0),
      .o_dq0_dfi_wck_cs_p1              (y_ch1_dq0_dfi_wck_cs_p1),
      .o_dq0_dfi_wck_cs_p2              (y_ch1_dq0_dfi_wck_cs_p2),
      .o_dq0_dfi_wck_cs_p3              (y_ch1_dq0_dfi_wck_cs_p3),
      .o_dq0_dfi_wck_cs_p4              (y_ch1_dq0_dfi_wck_cs_p4),
      .o_dq0_dfi_wck_cs_p5              (y_ch1_dq0_dfi_wck_cs_p5),
      .o_dq0_dfi_wck_cs_p6              (y_ch1_dq0_dfi_wck_cs_p6),
      .o_dq0_dfi_wck_cs_p7              (y_ch1_dq0_dfi_wck_cs_p7),
      .o_dq0_dfi_wck_ten_p0             (y_ch1_dq0_dfi_wck_ten_p0),
      .o_dq0_dfi_wck_ten_p1             (y_ch1_dq0_dfi_wck_ten_p1),
      .o_dq0_dfi_wck_ten_p2             (y_ch1_dq0_dfi_wck_ten_p2),
      .o_dq0_dfi_wck_ten_p3             (y_ch1_dq0_dfi_wck_ten_p3),
      .o_dq0_dfi_wck_ten_p4             (y_ch1_dq0_dfi_wck_ten_p4),
      .o_dq0_dfi_wck_ten_p5             (y_ch1_dq0_dfi_wck_ten_p5),
      .o_dq0_dfi_wck_ten_p6             (y_ch1_dq0_dfi_wck_ten_p6),
      .o_dq0_dfi_wck_ten_p7             (y_ch1_dq0_dfi_wck_ten_p7),

   // Read Data En/CS
      .i_dq0_dfi_rddata_en_p0          (ch1_dq0_dfi_rddata_en_p0),
      .i_dq0_dfi_rddata_en_p1          (ch1_dq0_dfi_rddata_en_p1),
      .i_dq0_dfi_rddata_en_p2          (ch1_dq0_dfi_rddata_en_p2),
      .i_dq0_dfi_rddata_en_p3          (ch1_dq0_dfi_rddata_en_p3),
      .i_dq0_dfi_rddata_en_p4          (ch1_dq0_dfi_rddata_en_p4),
      .i_dq0_dfi_rddata_en_p5          (ch1_dq0_dfi_rddata_en_p5),
      .i_dq0_dfi_rddata_en_p6          (ch1_dq0_dfi_rddata_en_p6),
      .i_dq0_dfi_rddata_en_p7          (ch1_dq0_dfi_rddata_en_p7),

      .i_dq0_dfi_rddata_cs_p0          (ch1_dq0_dfi_rddata_cs_p0),
      .i_dq0_dfi_rddata_cs_p1          (ch1_dq0_dfi_rddata_cs_p1),
      .i_dq0_dfi_rddata_cs_p2          (ch1_dq0_dfi_rddata_cs_p2),
      .i_dq0_dfi_rddata_cs_p3          (ch1_dq0_dfi_rddata_cs_p3),
      .i_dq0_dfi_rddata_cs_p4          (ch1_dq0_dfi_rddata_cs_p4),
      .i_dq0_dfi_rddata_cs_p5          (ch1_dq0_dfi_rddata_cs_p5),
      .i_dq0_dfi_rddata_cs_p6          (ch1_dq0_dfi_rddata_cs_p6),
      .i_dq0_dfi_rddata_cs_p7          (ch1_dq0_dfi_rddata_cs_p7),

      .o_dq0_dfi_rddata_en_p0          (y_ch1_dq0_dfi_rddata_en_p0),
      .o_dq0_dfi_rddata_en_p1          (y_ch1_dq0_dfi_rddata_en_p1),
      .o_dq0_dfi_rddata_en_p2          (y_ch1_dq0_dfi_rddata_en_p2),
      .o_dq0_dfi_rddata_en_p3          (y_ch1_dq0_dfi_rddata_en_p3),
      .o_dq0_dfi_rddata_en_p4          (y_ch1_dq0_dfi_rddata_en_p4),
      .o_dq0_dfi_rddata_en_p5          (y_ch1_dq0_dfi_rddata_en_p5),
      .o_dq0_dfi_rddata_en_p6          (y_ch1_dq0_dfi_rddata_en_p6),
      .o_dq0_dfi_rddata_en_p7          (y_ch1_dq0_dfi_rddata_en_p7),
      .o_dq0_dfi_rddata_ie_p0          (y_ch1_dq0_dfi_rddata_ie_p0),
      .o_dq0_dfi_rddata_ie_p1          (y_ch1_dq0_dfi_rddata_ie_p1),
      .o_dq0_dfi_rddata_ie_p2          (y_ch1_dq0_dfi_rddata_ie_p2),
      .o_dq0_dfi_rddata_ie_p3          (y_ch1_dq0_dfi_rddata_ie_p3),
      .o_dq0_dfi_rddata_ie_p4          (y_ch1_dq0_dfi_rddata_ie_p4),
      .o_dq0_dfi_rddata_ie_p5          (y_ch1_dq0_dfi_rddata_ie_p5),
      .o_dq0_dfi_rddata_ie_p6          (y_ch1_dq0_dfi_rddata_ie_p6),
      .o_dq0_dfi_rddata_ie_p7          (y_ch1_dq0_dfi_rddata_ie_p7),
      .o_dq0_dfi_rddata_re_p0          (y_ch1_dq0_dfi_rddata_re_p0),
      .o_dq0_dfi_rddata_re_p1          (y_ch1_dq0_dfi_rddata_re_p1),
      .o_dq0_dfi_rddata_re_p2          (y_ch1_dq0_dfi_rddata_re_p2),
      .o_dq0_dfi_rddata_re_p3          (y_ch1_dq0_dfi_rddata_re_p3),
      .o_dq0_dfi_rddata_re_p4          (y_ch1_dq0_dfi_rddata_re_p4),
      .o_dq0_dfi_rddata_re_p5          (y_ch1_dq0_dfi_rddata_re_p5),
      .o_dq0_dfi_rddata_re_p6          (y_ch1_dq0_dfi_rddata_re_p6),
      .o_dq0_dfi_rddata_re_p7          (y_ch1_dq0_dfi_rddata_re_p7),
      .o_dq0_dfi_rddata_cs_p0          (y_ch1_dq0_dfi_rddata_cs_p0),
      .o_dq0_dfi_rddata_cs_p1          (y_ch1_dq0_dfi_rddata_cs_p1),
      .o_dq0_dfi_rddata_cs_p2          (y_ch1_dq0_dfi_rddata_cs_p2),
      .o_dq0_dfi_rddata_cs_p3          (y_ch1_dq0_dfi_rddata_cs_p3),
      .o_dq0_dfi_rddata_cs_p4          (y_ch1_dq0_dfi_rddata_cs_p4),
      .o_dq0_dfi_rddata_cs_p5          (y_ch1_dq0_dfi_rddata_cs_p5),
      .o_dq0_dfi_rddata_cs_p6          (y_ch1_dq0_dfi_rddata_cs_p6),
      .o_dq0_dfi_rddata_cs_p7          (y_ch1_dq0_dfi_rddata_cs_p7),
      .i_dq1_dfi_wrdata_p0      (ch1_dq1_dfi_wrdata_p0),
      .i_dq1_dfi_wrdata_p1      (ch1_dq1_dfi_wrdata_p1),
      .i_dq1_dfi_wrdata_p2      (ch1_dq1_dfi_wrdata_p2),
      .i_dq1_dfi_wrdata_p3      (ch1_dq1_dfi_wrdata_p3),
      .i_dq1_dfi_wrdata_p4      (ch1_dq1_dfi_wrdata_p4),
      .i_dq1_dfi_wrdata_p5      (ch1_dq1_dfi_wrdata_p5),
      .i_dq1_dfi_wrdata_p6      (ch1_dq1_dfi_wrdata_p6),
      .i_dq1_dfi_wrdata_p7      (ch1_dq1_dfi_wrdata_p7),
      .i_dq1_dfi_wrdata_mask_p0 (ch1_dq1_dfi_wrdata_mask_p0),
      .i_dq1_dfi_wrdata_mask_p1 (ch1_dq1_dfi_wrdata_mask_p1),
      .i_dq1_dfi_wrdata_mask_p2 (ch1_dq1_dfi_wrdata_mask_p2),
      .i_dq1_dfi_wrdata_mask_p3 (ch1_dq1_dfi_wrdata_mask_p3),
      .i_dq1_dfi_wrdata_mask_p4 (ch1_dq1_dfi_wrdata_mask_p4),
      .i_dq1_dfi_wrdata_mask_p5 (ch1_dq1_dfi_wrdata_mask_p5),
      .i_dq1_dfi_wrdata_mask_p6 (ch1_dq1_dfi_wrdata_mask_p6),
      .i_dq1_dfi_wrdata_mask_p7 (ch1_dq1_dfi_wrdata_mask_p7),
      .o_dq1_dfi_wrdata_p0      (y_ch1_dq1_dfi_wrdata_p0),
      .o_dq1_dfi_wrdata_p1      (y_ch1_dq1_dfi_wrdata_p1),
      .o_dq1_dfi_wrdata_p2      (y_ch1_dq1_dfi_wrdata_p2),
      .o_dq1_dfi_wrdata_p3      (y_ch1_dq1_dfi_wrdata_p3),
      .o_dq1_dfi_wrdata_p4      (y_ch1_dq1_dfi_wrdata_p4),
      .o_dq1_dfi_wrdata_p5      (y_ch1_dq1_dfi_wrdata_p5),
      .o_dq1_dfi_wrdata_p6      (y_ch1_dq1_dfi_wrdata_p6),
      .o_dq1_dfi_wrdata_p7      (y_ch1_dq1_dfi_wrdata_p7),
      .o_dq1_dfi_wrdata_mask_p0 (y_ch1_dq1_dfi_wrdata_mask_p0),
      .o_dq1_dfi_wrdata_mask_p1 (y_ch1_dq1_dfi_wrdata_mask_p1),
      .o_dq1_dfi_wrdata_mask_p2 (y_ch1_dq1_dfi_wrdata_mask_p2),
      .o_dq1_dfi_wrdata_mask_p3 (y_ch1_dq1_dfi_wrdata_mask_p3),
      .o_dq1_dfi_wrdata_mask_p4 (y_ch1_dq1_dfi_wrdata_mask_p4),
      .o_dq1_dfi_wrdata_mask_p5 (y_ch1_dq1_dfi_wrdata_mask_p5),
      .o_dq1_dfi_wrdata_mask_p6 (y_ch1_dq1_dfi_wrdata_mask_p6),
      .o_dq1_dfi_wrdata_mask_p7 (y_ch1_dq1_dfi_wrdata_mask_p7),
      .i_dq1_dfi_wrdata_en_p0           (ch1_dq1_dfi_wrdata_en_p0),
      .i_dq1_dfi_wrdata_en_p1           (ch1_dq1_dfi_wrdata_en_p1),
      .i_dq1_dfi_wrdata_en_p2           (ch1_dq1_dfi_wrdata_en_p2),
      .i_dq1_dfi_wrdata_en_p3           (ch1_dq1_dfi_wrdata_en_p3),
      .i_dq1_dfi_wrdata_en_p4           (ch1_dq1_dfi_wrdata_en_p4),
      .i_dq1_dfi_wrdata_en_p5           (ch1_dq1_dfi_wrdata_en_p5),
      .i_dq1_dfi_wrdata_en_p6           (ch1_dq1_dfi_wrdata_en_p6),
      .i_dq1_dfi_wrdata_en_p7           (ch1_dq1_dfi_wrdata_en_p7),
      .i_dq1_dfi_parity_in_p0           (ch1_dq1_dfi_parity_in_p0),
      .i_dq1_dfi_parity_in_p1           (ch1_dq1_dfi_parity_in_p1),
      .i_dq1_dfi_parity_in_p2           (ch1_dq1_dfi_parity_in_p2),
      .i_dq1_dfi_parity_in_p3           (ch1_dq1_dfi_parity_in_p3),
      .i_dq1_dfi_parity_in_p4           (ch1_dq1_dfi_parity_in_p4),
      .i_dq1_dfi_parity_in_p5           (ch1_dq1_dfi_parity_in_p5),
      .i_dq1_dfi_parity_in_p6           (ch1_dq1_dfi_parity_in_p6),
      .i_dq1_dfi_parity_in_p7           (ch1_dq1_dfi_parity_in_p7),
      .i_dq1_dfi_wrdata_cs_p0           (ch1_dq1_dfi_wrdata_cs_p0),
      .i_dq1_dfi_wrdata_cs_p1           (ch1_dq1_dfi_wrdata_cs_p1),
      .i_dq1_dfi_wrdata_cs_p2           (ch1_dq1_dfi_wrdata_cs_p2),
      .i_dq1_dfi_wrdata_cs_p3           (ch1_dq1_dfi_wrdata_cs_p3),
      .i_dq1_dfi_wrdata_cs_p4           (ch1_dq1_dfi_wrdata_cs_p4),
      .i_dq1_dfi_wrdata_cs_p5           (ch1_dq1_dfi_wrdata_cs_p5),
      .i_dq1_dfi_wrdata_cs_p6           (ch1_dq1_dfi_wrdata_cs_p6),
      .i_dq1_dfi_wrdata_cs_p7           (ch1_dq1_dfi_wrdata_cs_p7),
      .i_dq1_dfi_wck_en_p0              (ch1_dq1_dfi_wck_en_p0),
      .i_dq1_dfi_wck_en_p1              (ch1_dq1_dfi_wck_en_p1),
      .i_dq1_dfi_wck_en_p2              (ch1_dq1_dfi_wck_en_p2),
      .i_dq1_dfi_wck_en_p3              (ch1_dq1_dfi_wck_en_p3),
      .i_dq1_dfi_wck_en_p4              (ch1_dq1_dfi_wck_en_p4),
      .i_dq1_dfi_wck_en_p5              (ch1_dq1_dfi_wck_en_p5),
      .i_dq1_dfi_wck_en_p6              (ch1_dq1_dfi_wck_en_p6),
      .i_dq1_dfi_wck_en_p7              (ch1_dq1_dfi_wck_en_p7),
      .i_dq1_dfi_wck_cs_p0              (ch1_dq1_dfi_wck_cs_p0),
      .i_dq1_dfi_wck_cs_p1              (ch1_dq1_dfi_wck_cs_p1),
      .i_dq1_dfi_wck_cs_p2              (ch1_dq1_dfi_wck_cs_p2),
      .i_dq1_dfi_wck_cs_p3              (ch1_dq1_dfi_wck_cs_p3),
      .i_dq1_dfi_wck_cs_p4              (ch1_dq1_dfi_wck_cs_p4),
      .i_dq1_dfi_wck_cs_p5              (ch1_dq1_dfi_wck_cs_p5),
      .i_dq1_dfi_wck_cs_p6              (ch1_dq1_dfi_wck_cs_p6),
      .i_dq1_dfi_wck_cs_p7              (ch1_dq1_dfi_wck_cs_p7),
      .i_dq1_dfi_wck_toggle_p0          (ch1_dq1_dfi_wck_toggle_p0),
      .i_dq1_dfi_wck_toggle_p1          (ch1_dq1_dfi_wck_toggle_p1),
      .i_dq1_dfi_wck_toggle_p2          (ch1_dq1_dfi_wck_toggle_p2),
      .i_dq1_dfi_wck_toggle_p3          (ch1_dq1_dfi_wck_toggle_p3),
      .i_dq1_dfi_wck_toggle_p4          (ch1_dq1_dfi_wck_toggle_p4),
      .i_dq1_dfi_wck_toggle_p5          (ch1_dq1_dfi_wck_toggle_p5),
      .i_dq1_dfi_wck_toggle_p6          (ch1_dq1_dfi_wck_toggle_p6),
      .i_dq1_dfi_wck_toggle_p7          (ch1_dq1_dfi_wck_toggle_p7),

      .o_dq1_dfi_wrdata_en_p0           (y_ch1_dq1_dfi_wrdata_en_p0),
      .o_dq1_dfi_wrdata_en_p1           (y_ch1_dq1_dfi_wrdata_en_p1),
      .o_dq1_dfi_wrdata_en_p2           (y_ch1_dq1_dfi_wrdata_en_p2),
      .o_dq1_dfi_wrdata_en_p3           (y_ch1_dq1_dfi_wrdata_en_p3),
      .o_dq1_dfi_wrdata_en_p4           (y_ch1_dq1_dfi_wrdata_en_p4),
      .o_dq1_dfi_wrdata_en_p5           (y_ch1_dq1_dfi_wrdata_en_p5),
      .o_dq1_dfi_wrdata_en_p6           (y_ch1_dq1_dfi_wrdata_en_p6),
      .o_dq1_dfi_wrdata_en_p7           (y_ch1_dq1_dfi_wrdata_en_p7),
      .o_dq1_dfi_wrdata_oe_p0           (y_ch1_dq1_dfi_wrdata_oe_p0),
      .o_dq1_dfi_wrdata_oe_p1           (y_ch1_dq1_dfi_wrdata_oe_p1),
      .o_dq1_dfi_wrdata_oe_p2           (y_ch1_dq1_dfi_wrdata_oe_p2),
      .o_dq1_dfi_wrdata_oe_p3           (y_ch1_dq1_dfi_wrdata_oe_p3),
      .o_dq1_dfi_wrdata_oe_p4           (y_ch1_dq1_dfi_wrdata_oe_p4),
      .o_dq1_dfi_wrdata_oe_p5           (y_ch1_dq1_dfi_wrdata_oe_p5),
      .o_dq1_dfi_wrdata_oe_p6           (y_ch1_dq1_dfi_wrdata_oe_p6),
      .o_dq1_dfi_wrdata_oe_p7           (y_ch1_dq1_dfi_wrdata_oe_p7),
      .o_dq1_dfi_parity_in_p0           (y_ch1_dq1_dfi_parity_in_p0),
      .o_dq1_dfi_parity_in_p1           (y_ch1_dq1_dfi_parity_in_p1),
      .o_dq1_dfi_parity_in_p2           (y_ch1_dq1_dfi_parity_in_p2),
      .o_dq1_dfi_parity_in_p3           (y_ch1_dq1_dfi_parity_in_p3),
      .o_dq1_dfi_parity_in_p4           (y_ch1_dq1_dfi_parity_in_p4),
      .o_dq1_dfi_parity_in_p5           (y_ch1_dq1_dfi_parity_in_p5),
      .o_dq1_dfi_parity_in_p6           (y_ch1_dq1_dfi_parity_in_p6),
      .o_dq1_dfi_parity_in_p7           (y_ch1_dq1_dfi_parity_in_p7),
      .o_dq1_dfi_wrdata_cs_p0           (y_ch1_dq1_dfi_wrdata_cs_p0),
      .o_dq1_dfi_wrdata_cs_p1           (y_ch1_dq1_dfi_wrdata_cs_p1),
      .o_dq1_dfi_wrdata_cs_p2           (y_ch1_dq1_dfi_wrdata_cs_p2),
      .o_dq1_dfi_wrdata_cs_p3           (y_ch1_dq1_dfi_wrdata_cs_p3),
      .o_dq1_dfi_wrdata_cs_p4           (y_ch1_dq1_dfi_wrdata_cs_p4),
      .o_dq1_dfi_wrdata_cs_p5           (y_ch1_dq1_dfi_wrdata_cs_p5),
      .o_dq1_dfi_wrdata_cs_p6           (y_ch1_dq1_dfi_wrdata_cs_p6),
      .o_dq1_dfi_wrdata_cs_p7           (y_ch1_dq1_dfi_wrdata_cs_p7),
      .o_dq1_dfi_wck_en_p0              (y_ch1_dq1_dfi_wck_en_p0),
      .o_dq1_dfi_wck_en_p1              (y_ch1_dq1_dfi_wck_en_p1),
      .o_dq1_dfi_wck_en_p2              (y_ch1_dq1_dfi_wck_en_p2),
      .o_dq1_dfi_wck_en_p3              (y_ch1_dq1_dfi_wck_en_p3),
      .o_dq1_dfi_wck_en_p4              (y_ch1_dq1_dfi_wck_en_p4),
      .o_dq1_dfi_wck_en_p5              (y_ch1_dq1_dfi_wck_en_p5),
      .o_dq1_dfi_wck_en_p6              (y_ch1_dq1_dfi_wck_en_p6),
      .o_dq1_dfi_wck_en_p7              (y_ch1_dq1_dfi_wck_en_p7),
      .o_dq1_dfi_wck_oe_p0              (y_ch1_dq1_dfi_wck_oe_p0),
      .o_dq1_dfi_wck_oe_p1              (y_ch1_dq1_dfi_wck_oe_p1),
      .o_dq1_dfi_wck_oe_p2              (y_ch1_dq1_dfi_wck_oe_p2),
      .o_dq1_dfi_wck_oe_p3              (y_ch1_dq1_dfi_wck_oe_p3),
      .o_dq1_dfi_wck_oe_p4              (y_ch1_dq1_dfi_wck_oe_p4),
      .o_dq1_dfi_wck_oe_p5              (y_ch1_dq1_dfi_wck_oe_p5),
      .o_dq1_dfi_wck_oe_p6              (y_ch1_dq1_dfi_wck_oe_p6),
      .o_dq1_dfi_wck_oe_p7              (y_ch1_dq1_dfi_wck_oe_p7),
      .o_dq1_dfi_wck_cs_p0              (y_ch1_dq1_dfi_wck_cs_p0),
      .o_dq1_dfi_wck_cs_p1              (y_ch1_dq1_dfi_wck_cs_p1),
      .o_dq1_dfi_wck_cs_p2              (y_ch1_dq1_dfi_wck_cs_p2),
      .o_dq1_dfi_wck_cs_p3              (y_ch1_dq1_dfi_wck_cs_p3),
      .o_dq1_dfi_wck_cs_p4              (y_ch1_dq1_dfi_wck_cs_p4),
      .o_dq1_dfi_wck_cs_p5              (y_ch1_dq1_dfi_wck_cs_p5),
      .o_dq1_dfi_wck_cs_p6              (y_ch1_dq1_dfi_wck_cs_p6),
      .o_dq1_dfi_wck_cs_p7              (y_ch1_dq1_dfi_wck_cs_p7),
      .o_dq1_dfi_wck_ten_p0             (y_ch1_dq1_dfi_wck_ten_p0),
      .o_dq1_dfi_wck_ten_p1             (y_ch1_dq1_dfi_wck_ten_p1),
      .o_dq1_dfi_wck_ten_p2             (y_ch1_dq1_dfi_wck_ten_p2),
      .o_dq1_dfi_wck_ten_p3             (y_ch1_dq1_dfi_wck_ten_p3),
      .o_dq1_dfi_wck_ten_p4             (y_ch1_dq1_dfi_wck_ten_p4),
      .o_dq1_dfi_wck_ten_p5             (y_ch1_dq1_dfi_wck_ten_p5),
      .o_dq1_dfi_wck_ten_p6             (y_ch1_dq1_dfi_wck_ten_p6),
      .o_dq1_dfi_wck_ten_p7             (y_ch1_dq1_dfi_wck_ten_p7),

   // Read Data En/CS
      .i_dq1_dfi_rddata_en_p0          (ch1_dq1_dfi_rddata_en_p0),
      .i_dq1_dfi_rddata_en_p1          (ch1_dq1_dfi_rddata_en_p1),
      .i_dq1_dfi_rddata_en_p2          (ch1_dq1_dfi_rddata_en_p2),
      .i_dq1_dfi_rddata_en_p3          (ch1_dq1_dfi_rddata_en_p3),
      .i_dq1_dfi_rddata_en_p4          (ch1_dq1_dfi_rddata_en_p4),
      .i_dq1_dfi_rddata_en_p5          (ch1_dq1_dfi_rddata_en_p5),
      .i_dq1_dfi_rddata_en_p6          (ch1_dq1_dfi_rddata_en_p6),
      .i_dq1_dfi_rddata_en_p7          (ch1_dq1_dfi_rddata_en_p7),

      .i_dq1_dfi_rddata_cs_p0          (ch1_dq1_dfi_rddata_cs_p0),
      .i_dq1_dfi_rddata_cs_p1          (ch1_dq1_dfi_rddata_cs_p1),
      .i_dq1_dfi_rddata_cs_p2          (ch1_dq1_dfi_rddata_cs_p2),
      .i_dq1_dfi_rddata_cs_p3          (ch1_dq1_dfi_rddata_cs_p3),
      .i_dq1_dfi_rddata_cs_p4          (ch1_dq1_dfi_rddata_cs_p4),
      .i_dq1_dfi_rddata_cs_p5          (ch1_dq1_dfi_rddata_cs_p5),
      .i_dq1_dfi_rddata_cs_p6          (ch1_dq1_dfi_rddata_cs_p6),
      .i_dq1_dfi_rddata_cs_p7          (ch1_dq1_dfi_rddata_cs_p7),

      .o_dq1_dfi_rddata_en_p0          (y_ch1_dq1_dfi_rddata_en_p0),
      .o_dq1_dfi_rddata_en_p1          (y_ch1_dq1_dfi_rddata_en_p1),
      .o_dq1_dfi_rddata_en_p2          (y_ch1_dq1_dfi_rddata_en_p2),
      .o_dq1_dfi_rddata_en_p3          (y_ch1_dq1_dfi_rddata_en_p3),
      .o_dq1_dfi_rddata_en_p4          (y_ch1_dq1_dfi_rddata_en_p4),
      .o_dq1_dfi_rddata_en_p5          (y_ch1_dq1_dfi_rddata_en_p5),
      .o_dq1_dfi_rddata_en_p6          (y_ch1_dq1_dfi_rddata_en_p6),
      .o_dq1_dfi_rddata_en_p7          (y_ch1_dq1_dfi_rddata_en_p7),
      .o_dq1_dfi_rddata_ie_p0          (y_ch1_dq1_dfi_rddata_ie_p0),
      .o_dq1_dfi_rddata_ie_p1          (y_ch1_dq1_dfi_rddata_ie_p1),
      .o_dq1_dfi_rddata_ie_p2          (y_ch1_dq1_dfi_rddata_ie_p2),
      .o_dq1_dfi_rddata_ie_p3          (y_ch1_dq1_dfi_rddata_ie_p3),
      .o_dq1_dfi_rddata_ie_p4          (y_ch1_dq1_dfi_rddata_ie_p4),
      .o_dq1_dfi_rddata_ie_p5          (y_ch1_dq1_dfi_rddata_ie_p5),
      .o_dq1_dfi_rddata_ie_p6          (y_ch1_dq1_dfi_rddata_ie_p6),
      .o_dq1_dfi_rddata_ie_p7          (y_ch1_dq1_dfi_rddata_ie_p7),
      .o_dq1_dfi_rddata_re_p0          (y_ch1_dq1_dfi_rddata_re_p0),
      .o_dq1_dfi_rddata_re_p1          (y_ch1_dq1_dfi_rddata_re_p1),
      .o_dq1_dfi_rddata_re_p2          (y_ch1_dq1_dfi_rddata_re_p2),
      .o_dq1_dfi_rddata_re_p3          (y_ch1_dq1_dfi_rddata_re_p3),
      .o_dq1_dfi_rddata_re_p4          (y_ch1_dq1_dfi_rddata_re_p4),
      .o_dq1_dfi_rddata_re_p5          (y_ch1_dq1_dfi_rddata_re_p5),
      .o_dq1_dfi_rddata_re_p6          (y_ch1_dq1_dfi_rddata_re_p6),
      .o_dq1_dfi_rddata_re_p7          (y_ch1_dq1_dfi_rddata_re_p7),
      .o_dq1_dfi_rddata_cs_p0          (y_ch1_dq1_dfi_rddata_cs_p0),
      .o_dq1_dfi_rddata_cs_p1          (y_ch1_dq1_dfi_rddata_cs_p1),
      .o_dq1_dfi_rddata_cs_p2          (y_ch1_dq1_dfi_rddata_cs_p2),
      .o_dq1_dfi_rddata_cs_p3          (y_ch1_dq1_dfi_rddata_cs_p3),
      .o_dq1_dfi_rddata_cs_p4          (y_ch1_dq1_dfi_rddata_cs_p4),
      .o_dq1_dfi_rddata_cs_p5          (y_ch1_dq1_dfi_rddata_cs_p5),
      .o_dq1_dfi_rddata_cs_p6          (y_ch1_dq1_dfi_rddata_cs_p6),
      .o_dq1_dfi_rddata_cs_p7          (y_ch1_dq1_dfi_rddata_cs_p7),

      // Read Data Interface
      .i_dq0_dfi_rddata_w0          (y_ch1_dq0_dfi_rddata_w0),
      .i_dq0_dfi_rddata_w1          (y_ch1_dq0_dfi_rddata_w1),
      .i_dq0_dfi_rddata_w2          (y_ch1_dq0_dfi_rddata_w2),
      .i_dq0_dfi_rddata_w3          (y_ch1_dq0_dfi_rddata_w3),
      .i_dq0_dfi_rddata_w4          (y_ch1_dq0_dfi_rddata_w4),
      .i_dq0_dfi_rddata_w5          (y_ch1_dq0_dfi_rddata_w5),
      .i_dq0_dfi_rddata_w6          (y_ch1_dq0_dfi_rddata_w6),
      .i_dq0_dfi_rddata_w7          (y_ch1_dq0_dfi_rddata_w7),
      .i_dq0_dfi_rddata_dbi_w0      (y_ch1_dq0_dfi_rddata_dbi_w0),
      .i_dq0_dfi_rddata_dbi_w1      (y_ch1_dq0_dfi_rddata_dbi_w1),
      .i_dq0_dfi_rddata_dbi_w2      (y_ch1_dq0_dfi_rddata_dbi_w2),
      .i_dq0_dfi_rddata_dbi_w3      (y_ch1_dq0_dfi_rddata_dbi_w3),
      .i_dq0_dfi_rddata_dbi_w4      (y_ch1_dq0_dfi_rddata_dbi_w4),
      .i_dq0_dfi_rddata_dbi_w5      (y_ch1_dq0_dfi_rddata_dbi_w5),
      .i_dq0_dfi_rddata_dbi_w6      (y_ch1_dq0_dfi_rddata_dbi_w6),
      .i_dq0_dfi_rddata_dbi_w7      (y_ch1_dq0_dfi_rddata_dbi_w7),
      .i_dq0_dfi_rddata_valid       (y_ch1_dq0_dfi_rddata_valid),
      .i_dq1_dfi_rddata_w0          (y_ch1_dq1_dfi_rddata_w0),
      .i_dq1_dfi_rddata_w1          (y_ch1_dq1_dfi_rddata_w1),
      .i_dq1_dfi_rddata_w2          (y_ch1_dq1_dfi_rddata_w2),
      .i_dq1_dfi_rddata_w3          (y_ch1_dq1_dfi_rddata_w3),
      .i_dq1_dfi_rddata_w4          (y_ch1_dq1_dfi_rddata_w4),
      .i_dq1_dfi_rddata_w5          (y_ch1_dq1_dfi_rddata_w5),
      .i_dq1_dfi_rddata_w6          (y_ch1_dq1_dfi_rddata_w6),
      .i_dq1_dfi_rddata_w7          (y_ch1_dq1_dfi_rddata_w7),
      .i_dq1_dfi_rddata_dbi_w0      (y_ch1_dq1_dfi_rddata_dbi_w0),
      .i_dq1_dfi_rddata_dbi_w1      (y_ch1_dq1_dfi_rddata_dbi_w1),
      .i_dq1_dfi_rddata_dbi_w2      (y_ch1_dq1_dfi_rddata_dbi_w2),
      .i_dq1_dfi_rddata_dbi_w3      (y_ch1_dq1_dfi_rddata_dbi_w3),
      .i_dq1_dfi_rddata_dbi_w4      (y_ch1_dq1_dfi_rddata_dbi_w4),
      .i_dq1_dfi_rddata_dbi_w5      (y_ch1_dq1_dfi_rddata_dbi_w5),
      .i_dq1_dfi_rddata_dbi_w6      (y_ch1_dq1_dfi_rddata_dbi_w6),
      .i_dq1_dfi_rddata_dbi_w7      (y_ch1_dq1_dfi_rddata_dbi_w7),
      .i_dq1_dfi_rddata_valid       (y_ch1_dq1_dfi_rddata_valid),

      .o_dfi_rddata_w0              (ch1_dfi_rddata_w0),
      .o_dfi_rddata_w1              (ch1_dfi_rddata_w1),
      .o_dfi_rddata_w2              (ch1_dfi_rddata_w2),
      .o_dfi_rddata_w3              (ch1_dfi_rddata_w3),
      .o_dfi_rddata_w4              (ch1_dfi_rddata_w4),
      .o_dfi_rddata_w5              (ch1_dfi_rddata_w5),
      .o_dfi_rddata_w6              (ch1_dfi_rddata_w6),
      .o_dfi_rddata_w7              (ch1_dfi_rddata_w7),
      .o_dfi_rddata_dbi_w0          (ch1_dfi_rddata_dbi_w0),
      .o_dfi_rddata_dbi_w1          (ch1_dfi_rddata_dbi_w1),
      .o_dfi_rddata_dbi_w2          (ch1_dfi_rddata_dbi_w2),
      .o_dfi_rddata_dbi_w3          (ch1_dfi_rddata_dbi_w3),
      .o_dfi_rddata_dbi_w4          (ch1_dfi_rddata_dbi_w4),
      .o_dfi_rddata_dbi_w5          (ch1_dfi_rddata_dbi_w5),
      .o_dfi_rddata_dbi_w6          (ch1_dfi_rddata_dbi_w6),
      .o_dfi_rddata_dbi_w7          (ch1_dfi_rddata_dbi_w7),
      .o_dfi_rddata_valid_w0        (ch1_dfi_rddata_valid_w0),
      .o_dfi_rddata_valid_w1        (ch1_dfi_rddata_valid_w1),
      .o_dfi_rddata_valid_w2        (ch1_dfi_rddata_valid_w2),
      .o_dfi_rddata_valid_w3        (ch1_dfi_rddata_valid_w3),
      .o_dfi_rddata_valid_w4        (ch1_dfi_rddata_valid_w4),
      .o_dfi_rddata_valid_w5        (ch1_dfi_rddata_valid_w5),
      .o_dfi_rddata_valid_w6        (ch1_dfi_rddata_valid_w6),
      .o_dfi_rddata_valid_w7        (ch1_dfi_rddata_valid_w7),
      .i_dq_dfi_rddata_valid_mask    (ch1_dfi_rdvalid_mask),

      .o_dqwr_debug                  (ch1_dpdqwr_debug),
      .o_dqrd_debug                  (ch1_dpdqrd_debug)
   );
   // ------------------------------------------------------------------------
   // DFI-to-DP
   // ------------------------------------------------------------------------

   ddr_dfi2dp #(
      .SWIDTH                       (SWIDTH),
      .AWIDTH                       (AWIDTH),
      .NUM_DQ                       (NUM_DQ),
      .NUM_WPH                      (NUM_WPH),
      .NUM_RPH                      (NUM_RPH),
      .DQ_WIDTH                     (DQ_WIDTH),
      .DQ_RWIDTH                    (DQ_RWIDTH),
      .DQ_WWIDTH                    (DQ_WWIDTH),
      .DQS_WIDTH                    (DQS_WIDTH),
      .DQS_WWIDTH                   (DQS_WWIDTH),
      .CA_WIDTH                     (CA_WIDTH),
      .CA_RWIDTH                    (CA_RWIDTH),
      .CA_WWIDTH                    (CA_WWIDTH),
      .CK_WIDTH                     (CK_WIDTH),
      .CK_WWIDTH                    (CK_WWIDTH)
   ) u_ch0_dfi2dp (

      .i_dfi_cke_p0                 (y_ch0_dfi_cke_p0),
      .i_dfi_cke_p1                 (y_ch0_dfi_cke_p1),
      .i_dfi_cke_p2                 (y_ch0_dfi_cke_p2),
      .i_dfi_cke_p3                 (y_ch0_dfi_cke_p3),
      .i_dfi_cke_p4                 (y_ch0_dfi_cke_p4),
      .i_dfi_cke_p5                 (y_ch0_dfi_cke_p5),
      .i_dfi_cke_p6                 (y_ch0_dfi_cke_p6),
      .i_dfi_cke_p7                 (y_ch0_dfi_cke_p7),
      .i_dfi_cs_p0                  (y_ch0_dfi_cs_p0),
      .i_dfi_cs_p1                  (y_ch0_dfi_cs_p1),
      .i_dfi_cs_p2                  (y_ch0_dfi_cs_p2),
      .i_dfi_cs_p3                  (y_ch0_dfi_cs_p3),
      .i_dfi_cs_p4                  (y_ch0_dfi_cs_p4),
      .i_dfi_cs_p5                  (y_ch0_dfi_cs_p5),
      .i_dfi_cs_p6                  (y_ch0_dfi_cs_p6),
      .i_dfi_cs_p7                  (y_ch0_dfi_cs_p7),
      .i_dfi_address_p0             (y_ch0_dfi_address_p0),
      .i_dfi_address_p1             (y_ch0_dfi_address_p1),
      .i_dfi_address_p2             (y_ch0_dfi_address_p2),
      .i_dfi_address_p3             (y_ch0_dfi_address_p3),
      .i_dfi_address_p4             (y_ch0_dfi_address_p4),
      .i_dfi_address_p5             (y_ch0_dfi_address_p5),
      .i_dfi_address_p6             (y_ch0_dfi_address_p6),
      .i_dfi_address_p7             (y_ch0_dfi_address_p7),
      .i_dfi_carddata_en_p0         (y_ch0_dfi_carddata_en_p0),
      .i_dfi_carddata_en_p1         (y_ch0_dfi_carddata_en_p1),
      .i_dfi_carddata_en_p2         (y_ch0_dfi_carddata_en_p2),
      .i_dfi_carddata_en_p3         (y_ch0_dfi_carddata_en_p3),
      .i_dfi_carddata_en_p4         (y_ch0_dfi_carddata_en_p4),
      .i_dfi_carddata_en_p5         (y_ch0_dfi_carddata_en_p5),
      .i_dfi_carddata_en_p6         (y_ch0_dfi_carddata_en_p6),
      .i_dfi_carddata_en_p7         (y_ch0_dfi_carddata_en_p7),
      .i_dfi_dram_clk_enable_p0     (y_ch0_dfi_dram_clk_enable_p0),
      .i_dfi_dram_clk_enable_p1     (y_ch0_dfi_dram_clk_enable_p1),
      .i_dfi_dram_clk_enable_p2     (y_ch0_dfi_dram_clk_enable_p2),
      .i_dfi_dram_clk_enable_p3     (y_ch0_dfi_dram_clk_enable_p3),
      .i_dfi_dram_clk_enable_p4     (y_ch0_dfi_dram_clk_enable_p4),
      .i_dfi_dram_clk_enable_p5     (y_ch0_dfi_dram_clk_enable_p5),
      .i_dfi_dram_clk_enable_p6     (y_ch0_dfi_dram_clk_enable_p6),
      .i_dfi_dram_clk_enable_p7     (y_ch0_dfi_dram_clk_enable_p7),
      .o_dfi_address_w0             (y_ch0_dfi_address_w0),
      .o_dfi_address_w1             (y_ch0_dfi_address_w1),
      .o_dfi_address_w2             (y_ch0_dfi_address_w2),
      .o_dfi_address_w3             (y_ch0_dfi_address_w3),
      .o_dfi_address_w4             (y_ch0_dfi_address_w4),
      .o_dfi_address_w5             (y_ch0_dfi_address_w5),
      .o_dfi_address_w6             (y_ch0_dfi_address_w6),
      .o_dfi_address_w7             (y_ch0_dfi_address_w7),
      .o_dfi_cs_w0                  (y_ch0_dfi_cs_w0),
      .o_dfi_cs_w1                  (y_ch0_dfi_cs_w1),
      .o_dfi_cs_w2                  (y_ch0_dfi_cs_w2),
      .o_dfi_cs_w3                  (y_ch0_dfi_cs_w3),
      .o_dfi_cs_w4                  (y_ch0_dfi_cs_w4),
      .o_dfi_cs_w5                  (y_ch0_dfi_cs_w5),
      .o_dfi_cs_w6                  (y_ch0_dfi_cs_w6),
      .o_dfi_cs_w7                  (y_ch0_dfi_cs_w7),
      .o_dfi_cke_w0                 (y_ch0_dfi_cke_w0),
      .o_dfi_cke_w1                 (y_ch0_dfi_cke_w1),
      .o_dfi_cke_w2                 (y_ch0_dfi_cke_w2),
      .o_dfi_cke_w3                 (y_ch0_dfi_cke_w3),
      .o_dfi_cke_w4                 (y_ch0_dfi_cke_w4),
      .o_dfi_cke_w5                 (y_ch0_dfi_cke_w5),
      .o_dfi_cke_w6                 (y_ch0_dfi_cke_w6),
      .o_dfi_cke_w7                 (y_ch0_dfi_cke_w7),
      .o_dfi_address_valid          (y_ch0_dfi_address_valid),
      .i_dq0_dfi_wrdata_p0          (y_ch0_dq0_dfi_wrdata_p0),
      .i_dq0_dfi_wrdata_p1          (y_ch0_dq0_dfi_wrdata_p1),
      .i_dq0_dfi_wrdata_p2          (y_ch0_dq0_dfi_wrdata_p2),
      .i_dq0_dfi_wrdata_p3          (y_ch0_dq0_dfi_wrdata_p3),
      .i_dq0_dfi_wrdata_p4          (y_ch0_dq0_dfi_wrdata_p4),
      .i_dq0_dfi_wrdata_p5          (y_ch0_dq0_dfi_wrdata_p5),
      .i_dq0_dfi_wrdata_p6          (y_ch0_dq0_dfi_wrdata_p6),
      .i_dq0_dfi_wrdata_p7          (y_ch0_dq0_dfi_wrdata_p7),
      .i_dq0_dfi_wrdata_mask_p0     (y_ch0_dq0_dfi_wrdata_mask_p0),
      .i_dq0_dfi_wrdata_mask_p1     (y_ch0_dq0_dfi_wrdata_mask_p1),
      .i_dq0_dfi_wrdata_mask_p2     (y_ch0_dq0_dfi_wrdata_mask_p2),
      .i_dq0_dfi_wrdata_mask_p3     (y_ch0_dq0_dfi_wrdata_mask_p3),
      .i_dq0_dfi_wrdata_mask_p4     (y_ch0_dq0_dfi_wrdata_mask_p4),
      .i_dq0_dfi_wrdata_mask_p5     (y_ch0_dq0_dfi_wrdata_mask_p5),
      .i_dq0_dfi_wrdata_mask_p6     (y_ch0_dq0_dfi_wrdata_mask_p6),
      .i_dq0_dfi_wrdata_mask_p7     (y_ch0_dq0_dfi_wrdata_mask_p7),
      .i_dq0_dfi_wrdata_cs_p0       (y_ch0_dq0_dfi_wrdata_cs_p0),
      .i_dq0_dfi_wrdata_cs_p1       (y_ch0_dq0_dfi_wrdata_cs_p1),
      .i_dq0_dfi_wrdata_cs_p2       (y_ch0_dq0_dfi_wrdata_cs_p2),
      .i_dq0_dfi_wrdata_cs_p3       (y_ch0_dq0_dfi_wrdata_cs_p3),
      .i_dq0_dfi_wrdata_cs_p4       (y_ch0_dq0_dfi_wrdata_cs_p4),
      .i_dq0_dfi_wrdata_cs_p5       (y_ch0_dq0_dfi_wrdata_cs_p5),
      .i_dq0_dfi_wrdata_cs_p6       (y_ch0_dq0_dfi_wrdata_cs_p6),
      .i_dq0_dfi_wrdata_cs_p7       (y_ch0_dq0_dfi_wrdata_cs_p7),
      .i_dq0_dfi_wck_oe_p0          (y_ch0_dq0_dfi_wck_oe_p0),
      .i_dq0_dfi_wck_oe_p1          (y_ch0_dq0_dfi_wck_oe_p1),
      .i_dq0_dfi_wck_oe_p2          (y_ch0_dq0_dfi_wck_oe_p2),
      .i_dq0_dfi_wck_oe_p3          (y_ch0_dq0_dfi_wck_oe_p3),
      .i_dq0_dfi_wck_oe_p4          (y_ch0_dq0_dfi_wck_oe_p4),
      .i_dq0_dfi_wck_oe_p5          (y_ch0_dq0_dfi_wck_oe_p5),
      .i_dq0_dfi_wck_oe_p6          (y_ch0_dq0_dfi_wck_oe_p6),
      .i_dq0_dfi_wck_oe_p7          (y_ch0_dq0_dfi_wck_oe_p7),
      .i_dq0_dfi_wrdata_oe_p0       (y_ch0_dq0_dfi_wrdata_oe_p0),
      .i_dq0_dfi_wrdata_oe_p1       (y_ch0_dq0_dfi_wrdata_oe_p1),
      .i_dq0_dfi_wrdata_oe_p2       (y_ch0_dq0_dfi_wrdata_oe_p2),
      .i_dq0_dfi_wrdata_oe_p3       (y_ch0_dq0_dfi_wrdata_oe_p3),
      .i_dq0_dfi_wrdata_oe_p4       (y_ch0_dq0_dfi_wrdata_oe_p4),
      .i_dq0_dfi_wrdata_oe_p5       (y_ch0_dq0_dfi_wrdata_oe_p5),
      .i_dq0_dfi_wrdata_oe_p6       (y_ch0_dq0_dfi_wrdata_oe_p6),
      .i_dq0_dfi_wrdata_oe_p7       (y_ch0_dq0_dfi_wrdata_oe_p7),
      .i_dq0_dfi_parity_in_p0       (y_ch0_dq0_dfi_parity_in_p0),
      .i_dq0_dfi_parity_in_p1       (y_ch0_dq0_dfi_parity_in_p1),
      .i_dq0_dfi_parity_in_p2       (y_ch0_dq0_dfi_parity_in_p2),
      .i_dq0_dfi_parity_in_p3       (y_ch0_dq0_dfi_parity_in_p3),
      .i_dq0_dfi_parity_in_p4       (y_ch0_dq0_dfi_parity_in_p4),
      .i_dq0_dfi_parity_in_p5       (y_ch0_dq0_dfi_parity_in_p5),
      .i_dq0_dfi_parity_in_p6       (y_ch0_dq0_dfi_parity_in_p6),
      .i_dq0_dfi_parity_in_p7       (y_ch0_dq0_dfi_parity_in_p7),
      .i_dq0_dfi_wck_ten_p0         (y_ch0_dq0_dfi_wck_ten_p0),
      .i_dq0_dfi_wck_ten_p1         (y_ch0_dq0_dfi_wck_ten_p1),
      .i_dq0_dfi_wck_ten_p2         (y_ch0_dq0_dfi_wck_ten_p2),
      .i_dq0_dfi_wck_ten_p3         (y_ch0_dq0_dfi_wck_ten_p3),
      .i_dq0_dfi_wck_ten_p4         (y_ch0_dq0_dfi_wck_ten_p4),
      .i_dq0_dfi_wck_ten_p5         (y_ch0_dq0_dfi_wck_ten_p5),
      .i_dq0_dfi_wck_ten_p6         (y_ch0_dq0_dfi_wck_ten_p6),
      .i_dq0_dfi_wck_ten_p7         (y_ch0_dq0_dfi_wck_ten_p7),
      .i_dq0_dfi_rddata_cs_p0       (y_ch0_dq0_dfi_rddata_cs_p0),
      .i_dq0_dfi_rddata_cs_p1       (y_ch0_dq0_dfi_rddata_cs_p1),
      .i_dq0_dfi_rddata_cs_p2       (y_ch0_dq0_dfi_rddata_cs_p2),
      .i_dq0_dfi_rddata_cs_p3       (y_ch0_dq0_dfi_rddata_cs_p3),
      .i_dq0_dfi_rddata_cs_p4       (y_ch0_dq0_dfi_rddata_cs_p4),
      .i_dq0_dfi_rddata_cs_p5       (y_ch0_dq0_dfi_rddata_cs_p5),
      .i_dq0_dfi_rddata_cs_p6       (y_ch0_dq0_dfi_rddata_cs_p6),
      .i_dq0_dfi_rddata_cs_p7       (y_ch0_dq0_dfi_rddata_cs_p7),
      .i_dq0_dfi_rddata_ie_p0       (y_ch0_dq0_dfi_rddata_ie_p0),
      .i_dq0_dfi_rddata_ie_p1       (y_ch0_dq0_dfi_rddata_ie_p1),
      .i_dq0_dfi_rddata_ie_p2       (y_ch0_dq0_dfi_rddata_ie_p2),
      .i_dq0_dfi_rddata_ie_p3       (y_ch0_dq0_dfi_rddata_ie_p3),
      .i_dq0_dfi_rddata_ie_p4       (y_ch0_dq0_dfi_rddata_ie_p4),
      .i_dq0_dfi_rddata_ie_p5       (y_ch0_dq0_dfi_rddata_ie_p5),
      .i_dq0_dfi_rddata_ie_p6       (y_ch0_dq0_dfi_rddata_ie_p6),
      .i_dq0_dfi_rddata_ie_p7       (y_ch0_dq0_dfi_rddata_ie_p7),
      .i_dq0_dfi_rddata_re_p0       (y_ch0_dq0_dfi_rddata_re_p0),
      .i_dq0_dfi_rddata_re_p1       (y_ch0_dq0_dfi_rddata_re_p1),
      .i_dq0_dfi_rddata_re_p2       (y_ch0_dq0_dfi_rddata_re_p2),
      .i_dq0_dfi_rddata_re_p3       (y_ch0_dq0_dfi_rddata_re_p3),
      .i_dq0_dfi_rddata_re_p4       (y_ch0_dq0_dfi_rddata_re_p4),
      .i_dq0_dfi_rddata_re_p5       (y_ch0_dq0_dfi_rddata_re_p5),
      .i_dq0_dfi_rddata_re_p6       (y_ch0_dq0_dfi_rddata_re_p6),
      .i_dq0_dfi_rddata_re_p7       (y_ch0_dq0_dfi_rddata_re_p7),
      .i_dq0_dfi_rddata_en_p0       (y_ch0_dq0_dfi_rddata_en_p0),
      .i_dq0_dfi_rddata_en_p1       (y_ch0_dq0_dfi_rddata_en_p1),
      .i_dq0_dfi_rddata_en_p2       (y_ch0_dq0_dfi_rddata_en_p2),
      .i_dq0_dfi_rddata_en_p3       (y_ch0_dq0_dfi_rddata_en_p3),
      .i_dq0_dfi_rddata_en_p4       (y_ch0_dq0_dfi_rddata_en_p4),
      .i_dq0_dfi_rddata_en_p5       (y_ch0_dq0_dfi_rddata_en_p5),
      .i_dq0_dfi_rddata_en_p6       (y_ch0_dq0_dfi_rddata_en_p6),
      .i_dq0_dfi_rddata_en_p7       (y_ch0_dq0_dfi_rddata_en_p7),
      .o_dq0_dfi_rddata_w0          (y_ch0_dq0_dfi_rddata_w0),
      .o_dq0_dfi_rddata_w1          (y_ch0_dq0_dfi_rddata_w1),
      .o_dq0_dfi_rddata_w2          (y_ch0_dq0_dfi_rddata_w2),
      .o_dq0_dfi_rddata_w3          (y_ch0_dq0_dfi_rddata_w3),
      .o_dq0_dfi_rddata_w4          (y_ch0_dq0_dfi_rddata_w4),
      .o_dq0_dfi_rddata_w5          (y_ch0_dq0_dfi_rddata_w5),
      .o_dq0_dfi_rddata_w6          (y_ch0_dq0_dfi_rddata_w6),
      .o_dq0_dfi_rddata_w7          (y_ch0_dq0_dfi_rddata_w7),
      .o_dq0_dfi_rddata_dbi_w0      (y_ch0_dq0_dfi_rddata_dbi_w0),
      .o_dq0_dfi_rddata_dbi_w1      (y_ch0_dq0_dfi_rddata_dbi_w1),
      .o_dq0_dfi_rddata_dbi_w2      (y_ch0_dq0_dfi_rddata_dbi_w2),
      .o_dq0_dfi_rddata_dbi_w3      (y_ch0_dq0_dfi_rddata_dbi_w3),
      .o_dq0_dfi_rddata_dbi_w4      (y_ch0_dq0_dfi_rddata_dbi_w4),
      .o_dq0_dfi_rddata_dbi_w5      (y_ch0_dq0_dfi_rddata_dbi_w5),
      .o_dq0_dfi_rddata_dbi_w6      (y_ch0_dq0_dfi_rddata_dbi_w6),
      .o_dq0_dfi_rddata_dbi_w7      (y_ch0_dq0_dfi_rddata_dbi_w7),
      .o_dq0_dfi_rddata_valid       (y_ch0_dq0_dfi_rddata_valid),
      .i_dq1_dfi_wrdata_p0          (y_ch0_dq1_dfi_wrdata_p0),
      .i_dq1_dfi_wrdata_p1          (y_ch0_dq1_dfi_wrdata_p1),
      .i_dq1_dfi_wrdata_p2          (y_ch0_dq1_dfi_wrdata_p2),
      .i_dq1_dfi_wrdata_p3          (y_ch0_dq1_dfi_wrdata_p3),
      .i_dq1_dfi_wrdata_p4          (y_ch0_dq1_dfi_wrdata_p4),
      .i_dq1_dfi_wrdata_p5          (y_ch0_dq1_dfi_wrdata_p5),
      .i_dq1_dfi_wrdata_p6          (y_ch0_dq1_dfi_wrdata_p6),
      .i_dq1_dfi_wrdata_p7          (y_ch0_dq1_dfi_wrdata_p7),
      .i_dq1_dfi_wrdata_mask_p0     (y_ch0_dq1_dfi_wrdata_mask_p0),
      .i_dq1_dfi_wrdata_mask_p1     (y_ch0_dq1_dfi_wrdata_mask_p1),
      .i_dq1_dfi_wrdata_mask_p2     (y_ch0_dq1_dfi_wrdata_mask_p2),
      .i_dq1_dfi_wrdata_mask_p3     (y_ch0_dq1_dfi_wrdata_mask_p3),
      .i_dq1_dfi_wrdata_mask_p4     (y_ch0_dq1_dfi_wrdata_mask_p4),
      .i_dq1_dfi_wrdata_mask_p5     (y_ch0_dq1_dfi_wrdata_mask_p5),
      .i_dq1_dfi_wrdata_mask_p6     (y_ch0_dq1_dfi_wrdata_mask_p6),
      .i_dq1_dfi_wrdata_mask_p7     (y_ch0_dq1_dfi_wrdata_mask_p7),
      .i_dq1_dfi_wrdata_cs_p0       (y_ch0_dq1_dfi_wrdata_cs_p0),
      .i_dq1_dfi_wrdata_cs_p1       (y_ch0_dq1_dfi_wrdata_cs_p1),
      .i_dq1_dfi_wrdata_cs_p2       (y_ch0_dq1_dfi_wrdata_cs_p2),
      .i_dq1_dfi_wrdata_cs_p3       (y_ch0_dq1_dfi_wrdata_cs_p3),
      .i_dq1_dfi_wrdata_cs_p4       (y_ch0_dq1_dfi_wrdata_cs_p4),
      .i_dq1_dfi_wrdata_cs_p5       (y_ch0_dq1_dfi_wrdata_cs_p5),
      .i_dq1_dfi_wrdata_cs_p6       (y_ch0_dq1_dfi_wrdata_cs_p6),
      .i_dq1_dfi_wrdata_cs_p7       (y_ch0_dq1_dfi_wrdata_cs_p7),
      .i_dq1_dfi_wck_oe_p0          (y_ch0_dq1_dfi_wck_oe_p0),
      .i_dq1_dfi_wck_oe_p1          (y_ch0_dq1_dfi_wck_oe_p1),
      .i_dq1_dfi_wck_oe_p2          (y_ch0_dq1_dfi_wck_oe_p2),
      .i_dq1_dfi_wck_oe_p3          (y_ch0_dq1_dfi_wck_oe_p3),
      .i_dq1_dfi_wck_oe_p4          (y_ch0_dq1_dfi_wck_oe_p4),
      .i_dq1_dfi_wck_oe_p5          (y_ch0_dq1_dfi_wck_oe_p5),
      .i_dq1_dfi_wck_oe_p6          (y_ch0_dq1_dfi_wck_oe_p6),
      .i_dq1_dfi_wck_oe_p7          (y_ch0_dq1_dfi_wck_oe_p7),
      .i_dq1_dfi_wrdata_oe_p0       (y_ch0_dq1_dfi_wrdata_oe_p0),
      .i_dq1_dfi_wrdata_oe_p1       (y_ch0_dq1_dfi_wrdata_oe_p1),
      .i_dq1_dfi_wrdata_oe_p2       (y_ch0_dq1_dfi_wrdata_oe_p2),
      .i_dq1_dfi_wrdata_oe_p3       (y_ch0_dq1_dfi_wrdata_oe_p3),
      .i_dq1_dfi_wrdata_oe_p4       (y_ch0_dq1_dfi_wrdata_oe_p4),
      .i_dq1_dfi_wrdata_oe_p5       (y_ch0_dq1_dfi_wrdata_oe_p5),
      .i_dq1_dfi_wrdata_oe_p6       (y_ch0_dq1_dfi_wrdata_oe_p6),
      .i_dq1_dfi_wrdata_oe_p7       (y_ch0_dq1_dfi_wrdata_oe_p7),
      .i_dq1_dfi_parity_in_p0       (y_ch0_dq1_dfi_parity_in_p0),
      .i_dq1_dfi_parity_in_p1       (y_ch0_dq1_dfi_parity_in_p1),
      .i_dq1_dfi_parity_in_p2       (y_ch0_dq1_dfi_parity_in_p2),
      .i_dq1_dfi_parity_in_p3       (y_ch0_dq1_dfi_parity_in_p3),
      .i_dq1_dfi_parity_in_p4       (y_ch0_dq1_dfi_parity_in_p4),
      .i_dq1_dfi_parity_in_p5       (y_ch0_dq1_dfi_parity_in_p5),
      .i_dq1_dfi_parity_in_p6       (y_ch0_dq1_dfi_parity_in_p6),
      .i_dq1_dfi_parity_in_p7       (y_ch0_dq1_dfi_parity_in_p7),
      .i_dq1_dfi_wck_ten_p0         (y_ch0_dq1_dfi_wck_ten_p0),
      .i_dq1_dfi_wck_ten_p1         (y_ch0_dq1_dfi_wck_ten_p1),
      .i_dq1_dfi_wck_ten_p2         (y_ch0_dq1_dfi_wck_ten_p2),
      .i_dq1_dfi_wck_ten_p3         (y_ch0_dq1_dfi_wck_ten_p3),
      .i_dq1_dfi_wck_ten_p4         (y_ch0_dq1_dfi_wck_ten_p4),
      .i_dq1_dfi_wck_ten_p5         (y_ch0_dq1_dfi_wck_ten_p5),
      .i_dq1_dfi_wck_ten_p6         (y_ch0_dq1_dfi_wck_ten_p6),
      .i_dq1_dfi_wck_ten_p7         (y_ch0_dq1_dfi_wck_ten_p7),
      .i_dq1_dfi_rddata_cs_p0       (y_ch0_dq1_dfi_rddata_cs_p0),
      .i_dq1_dfi_rddata_cs_p1       (y_ch0_dq1_dfi_rddata_cs_p1),
      .i_dq1_dfi_rddata_cs_p2       (y_ch0_dq1_dfi_rddata_cs_p2),
      .i_dq1_dfi_rddata_cs_p3       (y_ch0_dq1_dfi_rddata_cs_p3),
      .i_dq1_dfi_rddata_cs_p4       (y_ch0_dq1_dfi_rddata_cs_p4),
      .i_dq1_dfi_rddata_cs_p5       (y_ch0_dq1_dfi_rddata_cs_p5),
      .i_dq1_dfi_rddata_cs_p6       (y_ch0_dq1_dfi_rddata_cs_p6),
      .i_dq1_dfi_rddata_cs_p7       (y_ch0_dq1_dfi_rddata_cs_p7),
      .i_dq1_dfi_rddata_ie_p0       (y_ch0_dq1_dfi_rddata_ie_p0),
      .i_dq1_dfi_rddata_ie_p1       (y_ch0_dq1_dfi_rddata_ie_p1),
      .i_dq1_dfi_rddata_ie_p2       (y_ch0_dq1_dfi_rddata_ie_p2),
      .i_dq1_dfi_rddata_ie_p3       (y_ch0_dq1_dfi_rddata_ie_p3),
      .i_dq1_dfi_rddata_ie_p4       (y_ch0_dq1_dfi_rddata_ie_p4),
      .i_dq1_dfi_rddata_ie_p5       (y_ch0_dq1_dfi_rddata_ie_p5),
      .i_dq1_dfi_rddata_ie_p6       (y_ch0_dq1_dfi_rddata_ie_p6),
      .i_dq1_dfi_rddata_ie_p7       (y_ch0_dq1_dfi_rddata_ie_p7),
      .i_dq1_dfi_rddata_re_p0       (y_ch0_dq1_dfi_rddata_re_p0),
      .i_dq1_dfi_rddata_re_p1       (y_ch0_dq1_dfi_rddata_re_p1),
      .i_dq1_dfi_rddata_re_p2       (y_ch0_dq1_dfi_rddata_re_p2),
      .i_dq1_dfi_rddata_re_p3       (y_ch0_dq1_dfi_rddata_re_p3),
      .i_dq1_dfi_rddata_re_p4       (y_ch0_dq1_dfi_rddata_re_p4),
      .i_dq1_dfi_rddata_re_p5       (y_ch0_dq1_dfi_rddata_re_p5),
      .i_dq1_dfi_rddata_re_p6       (y_ch0_dq1_dfi_rddata_re_p6),
      .i_dq1_dfi_rddata_re_p7       (y_ch0_dq1_dfi_rddata_re_p7),
      .i_dq1_dfi_rddata_en_p0       (y_ch0_dq1_dfi_rddata_en_p0),
      .i_dq1_dfi_rddata_en_p1       (y_ch0_dq1_dfi_rddata_en_p1),
      .i_dq1_dfi_rddata_en_p2       (y_ch0_dq1_dfi_rddata_en_p2),
      .i_dq1_dfi_rddata_en_p3       (y_ch0_dq1_dfi_rddata_en_p3),
      .i_dq1_dfi_rddata_en_p4       (y_ch0_dq1_dfi_rddata_en_p4),
      .i_dq1_dfi_rddata_en_p5       (y_ch0_dq1_dfi_rddata_en_p5),
      .i_dq1_dfi_rddata_en_p6       (y_ch0_dq1_dfi_rddata_en_p6),
      .i_dq1_dfi_rddata_en_p7       (y_ch0_dq1_dfi_rddata_en_p7),
      .o_dq1_dfi_rddata_w0          (y_ch0_dq1_dfi_rddata_w0),
      .o_dq1_dfi_rddata_w1          (y_ch0_dq1_dfi_rddata_w1),
      .o_dq1_dfi_rddata_w2          (y_ch0_dq1_dfi_rddata_w2),
      .o_dq1_dfi_rddata_w3          (y_ch0_dq1_dfi_rddata_w3),
      .o_dq1_dfi_rddata_w4          (y_ch0_dq1_dfi_rddata_w4),
      .o_dq1_dfi_rddata_w5          (y_ch0_dq1_dfi_rddata_w5),
      .o_dq1_dfi_rddata_w6          (y_ch0_dq1_dfi_rddata_w6),
      .o_dq1_dfi_rddata_w7          (y_ch0_dq1_dfi_rddata_w7),
      .o_dq1_dfi_rddata_dbi_w0      (y_ch0_dq1_dfi_rddata_dbi_w0),
      .o_dq1_dfi_rddata_dbi_w1      (y_ch0_dq1_dfi_rddata_dbi_w1),
      .o_dq1_dfi_rddata_dbi_w2      (y_ch0_dq1_dfi_rddata_dbi_w2),
      .o_dq1_dfi_rddata_dbi_w3      (y_ch0_dq1_dfi_rddata_dbi_w3),
      .o_dq1_dfi_rddata_dbi_w4      (y_ch0_dq1_dfi_rddata_dbi_w4),
      .o_dq1_dfi_rddata_dbi_w5      (y_ch0_dq1_dfi_rddata_dbi_w5),
      .o_dq1_dfi_rddata_dbi_w6      (y_ch0_dq1_dfi_rddata_dbi_w6),
      .o_dq1_dfi_rddata_dbi_w7      (y_ch0_dq1_dfi_rddata_dbi_w7),
      .o_dq1_dfi_rddata_valid       (y_ch0_dq1_dfi_rddata_valid),

      .o_dq0_sdr                    (o_ch0_dq0_sdr),
      .i_dq0_sdr                    (i_ch0_dq0_sdr),
      .i_dq0_sdr_vld                (i_ch0_dq0_sdr_vld),
      .o_dqs0_sdr                   (o_ch0_dqs0_sdr),
      .o_dq1_sdr                    (o_ch0_dq1_sdr),
      .i_dq1_sdr                    (i_ch0_dq1_sdr),
      .i_dq1_sdr_vld                (i_ch0_dq1_sdr_vld),
      .o_dqs1_sdr                   (o_ch0_dqs1_sdr),

      .i_txrx_mode                  (i_txrx_mode),
      .i_tx0_sdr                    (i_ch0_tx0_sdr),
      .i_tx_ck0_sdr                 (i_ch0_tx_ck0_sdr),
      .o_rx0_sdr                    (o_ch0_rx0_sdr),
      .o_rx0_sdr_vld                (o_ch0_rx0_sdr_vld),
      .i_tx1_sdr                    (i_ch0_tx1_sdr),
      .i_tx_ck1_sdr                 (i_ch0_tx_ck1_sdr),
      .o_rx1_sdr                    (o_ch0_rx1_sdr),
      .o_rx1_sdr_vld                (o_ch0_rx1_sdr_vld),

      .o_ca_sdr                     (o_ch0_ca_sdr),
      .i_ca_sdr                     (i_ch0_ca_sdr),
      .i_ca_sdr_vld                 (i_ch0_ca_sdr_vld),
      .o_ck_sdr                     (o_ch0_ck_sdr)

   );
   ddr_dfi2dp #(
      .SWIDTH                       (SWIDTH),
      .AWIDTH                       (AWIDTH),
      .NUM_DQ                       (NUM_DQ),
      .NUM_WPH                      (NUM_WPH),
      .NUM_RPH                      (NUM_RPH),
      .DQ_WIDTH                     (DQ_WIDTH),
      .DQ_RWIDTH                    (DQ_RWIDTH),
      .DQ_WWIDTH                    (DQ_WWIDTH),
      .DQS_WIDTH                    (DQS_WIDTH),
      .DQS_WWIDTH                   (DQS_WWIDTH),
      .CA_WIDTH                     (CA_WIDTH),
      .CA_RWIDTH                    (CA_RWIDTH),
      .CA_WWIDTH                    (CA_WWIDTH),
      .CK_WIDTH                     (CK_WIDTH),
      .CK_WWIDTH                    (CK_WWIDTH)
   ) u_ch1_dfi2dp (

      .i_dfi_cke_p0                 (y_ch1_dfi_cke_p0),
      .i_dfi_cke_p1                 (y_ch1_dfi_cke_p1),
      .i_dfi_cke_p2                 (y_ch1_dfi_cke_p2),
      .i_dfi_cke_p3                 (y_ch1_dfi_cke_p3),
      .i_dfi_cke_p4                 (y_ch1_dfi_cke_p4),
      .i_dfi_cke_p5                 (y_ch1_dfi_cke_p5),
      .i_dfi_cke_p6                 (y_ch1_dfi_cke_p6),
      .i_dfi_cke_p7                 (y_ch1_dfi_cke_p7),
      .i_dfi_cs_p0                  (y_ch1_dfi_cs_p0),
      .i_dfi_cs_p1                  (y_ch1_dfi_cs_p1),
      .i_dfi_cs_p2                  (y_ch1_dfi_cs_p2),
      .i_dfi_cs_p3                  (y_ch1_dfi_cs_p3),
      .i_dfi_cs_p4                  (y_ch1_dfi_cs_p4),
      .i_dfi_cs_p5                  (y_ch1_dfi_cs_p5),
      .i_dfi_cs_p6                  (y_ch1_dfi_cs_p6),
      .i_dfi_cs_p7                  (y_ch1_dfi_cs_p7),
      .i_dfi_address_p0             (y_ch1_dfi_address_p0),
      .i_dfi_address_p1             (y_ch1_dfi_address_p1),
      .i_dfi_address_p2             (y_ch1_dfi_address_p2),
      .i_dfi_address_p3             (y_ch1_dfi_address_p3),
      .i_dfi_address_p4             (y_ch1_dfi_address_p4),
      .i_dfi_address_p5             (y_ch1_dfi_address_p5),
      .i_dfi_address_p6             (y_ch1_dfi_address_p6),
      .i_dfi_address_p7             (y_ch1_dfi_address_p7),
      .i_dfi_carddata_en_p0         (y_ch1_dfi_carddata_en_p0),
      .i_dfi_carddata_en_p1         (y_ch1_dfi_carddata_en_p1),
      .i_dfi_carddata_en_p2         (y_ch1_dfi_carddata_en_p2),
      .i_dfi_carddata_en_p3         (y_ch1_dfi_carddata_en_p3),
      .i_dfi_carddata_en_p4         (y_ch1_dfi_carddata_en_p4),
      .i_dfi_carddata_en_p5         (y_ch1_dfi_carddata_en_p5),
      .i_dfi_carddata_en_p6         (y_ch1_dfi_carddata_en_p6),
      .i_dfi_carddata_en_p7         (y_ch1_dfi_carddata_en_p7),
      .i_dfi_dram_clk_enable_p0     (y_ch1_dfi_dram_clk_enable_p0),
      .i_dfi_dram_clk_enable_p1     (y_ch1_dfi_dram_clk_enable_p1),
      .i_dfi_dram_clk_enable_p2     (y_ch1_dfi_dram_clk_enable_p2),
      .i_dfi_dram_clk_enable_p3     (y_ch1_dfi_dram_clk_enable_p3),
      .i_dfi_dram_clk_enable_p4     (y_ch1_dfi_dram_clk_enable_p4),
      .i_dfi_dram_clk_enable_p5     (y_ch1_dfi_dram_clk_enable_p5),
      .i_dfi_dram_clk_enable_p6     (y_ch1_dfi_dram_clk_enable_p6),
      .i_dfi_dram_clk_enable_p7     (y_ch1_dfi_dram_clk_enable_p7),
      .o_dfi_address_w0             (y_ch1_dfi_address_w0),
      .o_dfi_address_w1             (y_ch1_dfi_address_w1),
      .o_dfi_address_w2             (y_ch1_dfi_address_w2),
      .o_dfi_address_w3             (y_ch1_dfi_address_w3),
      .o_dfi_address_w4             (y_ch1_dfi_address_w4),
      .o_dfi_address_w5             (y_ch1_dfi_address_w5),
      .o_dfi_address_w6             (y_ch1_dfi_address_w6),
      .o_dfi_address_w7             (y_ch1_dfi_address_w7),
      .o_dfi_cs_w0                  (y_ch1_dfi_cs_w0),
      .o_dfi_cs_w1                  (y_ch1_dfi_cs_w1),
      .o_dfi_cs_w2                  (y_ch1_dfi_cs_w2),
      .o_dfi_cs_w3                  (y_ch1_dfi_cs_w3),
      .o_dfi_cs_w4                  (y_ch1_dfi_cs_w4),
      .o_dfi_cs_w5                  (y_ch1_dfi_cs_w5),
      .o_dfi_cs_w6                  (y_ch1_dfi_cs_w6),
      .o_dfi_cs_w7                  (y_ch1_dfi_cs_w7),
      .o_dfi_cke_w0                 (y_ch1_dfi_cke_w0),
      .o_dfi_cke_w1                 (y_ch1_dfi_cke_w1),
      .o_dfi_cke_w2                 (y_ch1_dfi_cke_w2),
      .o_dfi_cke_w3                 (y_ch1_dfi_cke_w3),
      .o_dfi_cke_w4                 (y_ch1_dfi_cke_w4),
      .o_dfi_cke_w5                 (y_ch1_dfi_cke_w5),
      .o_dfi_cke_w6                 (y_ch1_dfi_cke_w6),
      .o_dfi_cke_w7                 (y_ch1_dfi_cke_w7),
      .o_dfi_address_valid          (y_ch1_dfi_address_valid),
      .i_dq0_dfi_wrdata_p0          (y_ch1_dq0_dfi_wrdata_p0),
      .i_dq0_dfi_wrdata_p1          (y_ch1_dq0_dfi_wrdata_p1),
      .i_dq0_dfi_wrdata_p2          (y_ch1_dq0_dfi_wrdata_p2),
      .i_dq0_dfi_wrdata_p3          (y_ch1_dq0_dfi_wrdata_p3),
      .i_dq0_dfi_wrdata_p4          (y_ch1_dq0_dfi_wrdata_p4),
      .i_dq0_dfi_wrdata_p5          (y_ch1_dq0_dfi_wrdata_p5),
      .i_dq0_dfi_wrdata_p6          (y_ch1_dq0_dfi_wrdata_p6),
      .i_dq0_dfi_wrdata_p7          (y_ch1_dq0_dfi_wrdata_p7),
      .i_dq0_dfi_wrdata_mask_p0     (y_ch1_dq0_dfi_wrdata_mask_p0),
      .i_dq0_dfi_wrdata_mask_p1     (y_ch1_dq0_dfi_wrdata_mask_p1),
      .i_dq0_dfi_wrdata_mask_p2     (y_ch1_dq0_dfi_wrdata_mask_p2),
      .i_dq0_dfi_wrdata_mask_p3     (y_ch1_dq0_dfi_wrdata_mask_p3),
      .i_dq0_dfi_wrdata_mask_p4     (y_ch1_dq0_dfi_wrdata_mask_p4),
      .i_dq0_dfi_wrdata_mask_p5     (y_ch1_dq0_dfi_wrdata_mask_p5),
      .i_dq0_dfi_wrdata_mask_p6     (y_ch1_dq0_dfi_wrdata_mask_p6),
      .i_dq0_dfi_wrdata_mask_p7     (y_ch1_dq0_dfi_wrdata_mask_p7),
      .i_dq0_dfi_wrdata_cs_p0       (y_ch1_dq0_dfi_wrdata_cs_p0),
      .i_dq0_dfi_wrdata_cs_p1       (y_ch1_dq0_dfi_wrdata_cs_p1),
      .i_dq0_dfi_wrdata_cs_p2       (y_ch1_dq0_dfi_wrdata_cs_p2),
      .i_dq0_dfi_wrdata_cs_p3       (y_ch1_dq0_dfi_wrdata_cs_p3),
      .i_dq0_dfi_wrdata_cs_p4       (y_ch1_dq0_dfi_wrdata_cs_p4),
      .i_dq0_dfi_wrdata_cs_p5       (y_ch1_dq0_dfi_wrdata_cs_p5),
      .i_dq0_dfi_wrdata_cs_p6       (y_ch1_dq0_dfi_wrdata_cs_p6),
      .i_dq0_dfi_wrdata_cs_p7       (y_ch1_dq0_dfi_wrdata_cs_p7),
      .i_dq0_dfi_wck_oe_p0          (y_ch1_dq0_dfi_wck_oe_p0),
      .i_dq0_dfi_wck_oe_p1          (y_ch1_dq0_dfi_wck_oe_p1),
      .i_dq0_dfi_wck_oe_p2          (y_ch1_dq0_dfi_wck_oe_p2),
      .i_dq0_dfi_wck_oe_p3          (y_ch1_dq0_dfi_wck_oe_p3),
      .i_dq0_dfi_wck_oe_p4          (y_ch1_dq0_dfi_wck_oe_p4),
      .i_dq0_dfi_wck_oe_p5          (y_ch1_dq0_dfi_wck_oe_p5),
      .i_dq0_dfi_wck_oe_p6          (y_ch1_dq0_dfi_wck_oe_p6),
      .i_dq0_dfi_wck_oe_p7          (y_ch1_dq0_dfi_wck_oe_p7),
      .i_dq0_dfi_wrdata_oe_p0       (y_ch1_dq0_dfi_wrdata_oe_p0),
      .i_dq0_dfi_wrdata_oe_p1       (y_ch1_dq0_dfi_wrdata_oe_p1),
      .i_dq0_dfi_wrdata_oe_p2       (y_ch1_dq0_dfi_wrdata_oe_p2),
      .i_dq0_dfi_wrdata_oe_p3       (y_ch1_dq0_dfi_wrdata_oe_p3),
      .i_dq0_dfi_wrdata_oe_p4       (y_ch1_dq0_dfi_wrdata_oe_p4),
      .i_dq0_dfi_wrdata_oe_p5       (y_ch1_dq0_dfi_wrdata_oe_p5),
      .i_dq0_dfi_wrdata_oe_p6       (y_ch1_dq0_dfi_wrdata_oe_p6),
      .i_dq0_dfi_wrdata_oe_p7       (y_ch1_dq0_dfi_wrdata_oe_p7),
      .i_dq0_dfi_parity_in_p0       (y_ch1_dq0_dfi_parity_in_p0),
      .i_dq0_dfi_parity_in_p1       (y_ch1_dq0_dfi_parity_in_p1),
      .i_dq0_dfi_parity_in_p2       (y_ch1_dq0_dfi_parity_in_p2),
      .i_dq0_dfi_parity_in_p3       (y_ch1_dq0_dfi_parity_in_p3),
      .i_dq0_dfi_parity_in_p4       (y_ch1_dq0_dfi_parity_in_p4),
      .i_dq0_dfi_parity_in_p5       (y_ch1_dq0_dfi_parity_in_p5),
      .i_dq0_dfi_parity_in_p6       (y_ch1_dq0_dfi_parity_in_p6),
      .i_dq0_dfi_parity_in_p7       (y_ch1_dq0_dfi_parity_in_p7),
      .i_dq0_dfi_wck_ten_p0         (y_ch1_dq0_dfi_wck_ten_p0),
      .i_dq0_dfi_wck_ten_p1         (y_ch1_dq0_dfi_wck_ten_p1),
      .i_dq0_dfi_wck_ten_p2         (y_ch1_dq0_dfi_wck_ten_p2),
      .i_dq0_dfi_wck_ten_p3         (y_ch1_dq0_dfi_wck_ten_p3),
      .i_dq0_dfi_wck_ten_p4         (y_ch1_dq0_dfi_wck_ten_p4),
      .i_dq0_dfi_wck_ten_p5         (y_ch1_dq0_dfi_wck_ten_p5),
      .i_dq0_dfi_wck_ten_p6         (y_ch1_dq0_dfi_wck_ten_p6),
      .i_dq0_dfi_wck_ten_p7         (y_ch1_dq0_dfi_wck_ten_p7),
      .i_dq0_dfi_rddata_cs_p0       (y_ch1_dq0_dfi_rddata_cs_p0),
      .i_dq0_dfi_rddata_cs_p1       (y_ch1_dq0_dfi_rddata_cs_p1),
      .i_dq0_dfi_rddata_cs_p2       (y_ch1_dq0_dfi_rddata_cs_p2),
      .i_dq0_dfi_rddata_cs_p3       (y_ch1_dq0_dfi_rddata_cs_p3),
      .i_dq0_dfi_rddata_cs_p4       (y_ch1_dq0_dfi_rddata_cs_p4),
      .i_dq0_dfi_rddata_cs_p5       (y_ch1_dq0_dfi_rddata_cs_p5),
      .i_dq0_dfi_rddata_cs_p6       (y_ch1_dq0_dfi_rddata_cs_p6),
      .i_dq0_dfi_rddata_cs_p7       (y_ch1_dq0_dfi_rddata_cs_p7),
      .i_dq0_dfi_rddata_ie_p0       (y_ch1_dq0_dfi_rddata_ie_p0),
      .i_dq0_dfi_rddata_ie_p1       (y_ch1_dq0_dfi_rddata_ie_p1),
      .i_dq0_dfi_rddata_ie_p2       (y_ch1_dq0_dfi_rddata_ie_p2),
      .i_dq0_dfi_rddata_ie_p3       (y_ch1_dq0_dfi_rddata_ie_p3),
      .i_dq0_dfi_rddata_ie_p4       (y_ch1_dq0_dfi_rddata_ie_p4),
      .i_dq0_dfi_rddata_ie_p5       (y_ch1_dq0_dfi_rddata_ie_p5),
      .i_dq0_dfi_rddata_ie_p6       (y_ch1_dq0_dfi_rddata_ie_p6),
      .i_dq0_dfi_rddata_ie_p7       (y_ch1_dq0_dfi_rddata_ie_p7),
      .i_dq0_dfi_rddata_re_p0       (y_ch1_dq0_dfi_rddata_re_p0),
      .i_dq0_dfi_rddata_re_p1       (y_ch1_dq0_dfi_rddata_re_p1),
      .i_dq0_dfi_rddata_re_p2       (y_ch1_dq0_dfi_rddata_re_p2),
      .i_dq0_dfi_rddata_re_p3       (y_ch1_dq0_dfi_rddata_re_p3),
      .i_dq0_dfi_rddata_re_p4       (y_ch1_dq0_dfi_rddata_re_p4),
      .i_dq0_dfi_rddata_re_p5       (y_ch1_dq0_dfi_rddata_re_p5),
      .i_dq0_dfi_rddata_re_p6       (y_ch1_dq0_dfi_rddata_re_p6),
      .i_dq0_dfi_rddata_re_p7       (y_ch1_dq0_dfi_rddata_re_p7),
      .i_dq0_dfi_rddata_en_p0       (y_ch1_dq0_dfi_rddata_en_p0),
      .i_dq0_dfi_rddata_en_p1       (y_ch1_dq0_dfi_rddata_en_p1),
      .i_dq0_dfi_rddata_en_p2       (y_ch1_dq0_dfi_rddata_en_p2),
      .i_dq0_dfi_rddata_en_p3       (y_ch1_dq0_dfi_rddata_en_p3),
      .i_dq0_dfi_rddata_en_p4       (y_ch1_dq0_dfi_rddata_en_p4),
      .i_dq0_dfi_rddata_en_p5       (y_ch1_dq0_dfi_rddata_en_p5),
      .i_dq0_dfi_rddata_en_p6       (y_ch1_dq0_dfi_rddata_en_p6),
      .i_dq0_dfi_rddata_en_p7       (y_ch1_dq0_dfi_rddata_en_p7),
      .o_dq0_dfi_rddata_w0          (y_ch1_dq0_dfi_rddata_w0),
      .o_dq0_dfi_rddata_w1          (y_ch1_dq0_dfi_rddata_w1),
      .o_dq0_dfi_rddata_w2          (y_ch1_dq0_dfi_rddata_w2),
      .o_dq0_dfi_rddata_w3          (y_ch1_dq0_dfi_rddata_w3),
      .o_dq0_dfi_rddata_w4          (y_ch1_dq0_dfi_rddata_w4),
      .o_dq0_dfi_rddata_w5          (y_ch1_dq0_dfi_rddata_w5),
      .o_dq0_dfi_rddata_w6          (y_ch1_dq0_dfi_rddata_w6),
      .o_dq0_dfi_rddata_w7          (y_ch1_dq0_dfi_rddata_w7),
      .o_dq0_dfi_rddata_dbi_w0      (y_ch1_dq0_dfi_rddata_dbi_w0),
      .o_dq0_dfi_rddata_dbi_w1      (y_ch1_dq0_dfi_rddata_dbi_w1),
      .o_dq0_dfi_rddata_dbi_w2      (y_ch1_dq0_dfi_rddata_dbi_w2),
      .o_dq0_dfi_rddata_dbi_w3      (y_ch1_dq0_dfi_rddata_dbi_w3),
      .o_dq0_dfi_rddata_dbi_w4      (y_ch1_dq0_dfi_rddata_dbi_w4),
      .o_dq0_dfi_rddata_dbi_w5      (y_ch1_dq0_dfi_rddata_dbi_w5),
      .o_dq0_dfi_rddata_dbi_w6      (y_ch1_dq0_dfi_rddata_dbi_w6),
      .o_dq0_dfi_rddata_dbi_w7      (y_ch1_dq0_dfi_rddata_dbi_w7),
      .o_dq0_dfi_rddata_valid       (y_ch1_dq0_dfi_rddata_valid),
      .i_dq1_dfi_wrdata_p0          (y_ch1_dq1_dfi_wrdata_p0),
      .i_dq1_dfi_wrdata_p1          (y_ch1_dq1_dfi_wrdata_p1),
      .i_dq1_dfi_wrdata_p2          (y_ch1_dq1_dfi_wrdata_p2),
      .i_dq1_dfi_wrdata_p3          (y_ch1_dq1_dfi_wrdata_p3),
      .i_dq1_dfi_wrdata_p4          (y_ch1_dq1_dfi_wrdata_p4),
      .i_dq1_dfi_wrdata_p5          (y_ch1_dq1_dfi_wrdata_p5),
      .i_dq1_dfi_wrdata_p6          (y_ch1_dq1_dfi_wrdata_p6),
      .i_dq1_dfi_wrdata_p7          (y_ch1_dq1_dfi_wrdata_p7),
      .i_dq1_dfi_wrdata_mask_p0     (y_ch1_dq1_dfi_wrdata_mask_p0),
      .i_dq1_dfi_wrdata_mask_p1     (y_ch1_dq1_dfi_wrdata_mask_p1),
      .i_dq1_dfi_wrdata_mask_p2     (y_ch1_dq1_dfi_wrdata_mask_p2),
      .i_dq1_dfi_wrdata_mask_p3     (y_ch1_dq1_dfi_wrdata_mask_p3),
      .i_dq1_dfi_wrdata_mask_p4     (y_ch1_dq1_dfi_wrdata_mask_p4),
      .i_dq1_dfi_wrdata_mask_p5     (y_ch1_dq1_dfi_wrdata_mask_p5),
      .i_dq1_dfi_wrdata_mask_p6     (y_ch1_dq1_dfi_wrdata_mask_p6),
      .i_dq1_dfi_wrdata_mask_p7     (y_ch1_dq1_dfi_wrdata_mask_p7),
      .i_dq1_dfi_wrdata_cs_p0       (y_ch1_dq1_dfi_wrdata_cs_p0),
      .i_dq1_dfi_wrdata_cs_p1       (y_ch1_dq1_dfi_wrdata_cs_p1),
      .i_dq1_dfi_wrdata_cs_p2       (y_ch1_dq1_dfi_wrdata_cs_p2),
      .i_dq1_dfi_wrdata_cs_p3       (y_ch1_dq1_dfi_wrdata_cs_p3),
      .i_dq1_dfi_wrdata_cs_p4       (y_ch1_dq1_dfi_wrdata_cs_p4),
      .i_dq1_dfi_wrdata_cs_p5       (y_ch1_dq1_dfi_wrdata_cs_p5),
      .i_dq1_dfi_wrdata_cs_p6       (y_ch1_dq1_dfi_wrdata_cs_p6),
      .i_dq1_dfi_wrdata_cs_p7       (y_ch1_dq1_dfi_wrdata_cs_p7),
      .i_dq1_dfi_wck_oe_p0          (y_ch1_dq1_dfi_wck_oe_p0),
      .i_dq1_dfi_wck_oe_p1          (y_ch1_dq1_dfi_wck_oe_p1),
      .i_dq1_dfi_wck_oe_p2          (y_ch1_dq1_dfi_wck_oe_p2),
      .i_dq1_dfi_wck_oe_p3          (y_ch1_dq1_dfi_wck_oe_p3),
      .i_dq1_dfi_wck_oe_p4          (y_ch1_dq1_dfi_wck_oe_p4),
      .i_dq1_dfi_wck_oe_p5          (y_ch1_dq1_dfi_wck_oe_p5),
      .i_dq1_dfi_wck_oe_p6          (y_ch1_dq1_dfi_wck_oe_p6),
      .i_dq1_dfi_wck_oe_p7          (y_ch1_dq1_dfi_wck_oe_p7),
      .i_dq1_dfi_wrdata_oe_p0       (y_ch1_dq1_dfi_wrdata_oe_p0),
      .i_dq1_dfi_wrdata_oe_p1       (y_ch1_dq1_dfi_wrdata_oe_p1),
      .i_dq1_dfi_wrdata_oe_p2       (y_ch1_dq1_dfi_wrdata_oe_p2),
      .i_dq1_dfi_wrdata_oe_p3       (y_ch1_dq1_dfi_wrdata_oe_p3),
      .i_dq1_dfi_wrdata_oe_p4       (y_ch1_dq1_dfi_wrdata_oe_p4),
      .i_dq1_dfi_wrdata_oe_p5       (y_ch1_dq1_dfi_wrdata_oe_p5),
      .i_dq1_dfi_wrdata_oe_p6       (y_ch1_dq1_dfi_wrdata_oe_p6),
      .i_dq1_dfi_wrdata_oe_p7       (y_ch1_dq1_dfi_wrdata_oe_p7),
      .i_dq1_dfi_parity_in_p0       (y_ch1_dq1_dfi_parity_in_p0),
      .i_dq1_dfi_parity_in_p1       (y_ch1_dq1_dfi_parity_in_p1),
      .i_dq1_dfi_parity_in_p2       (y_ch1_dq1_dfi_parity_in_p2),
      .i_dq1_dfi_parity_in_p3       (y_ch1_dq1_dfi_parity_in_p3),
      .i_dq1_dfi_parity_in_p4       (y_ch1_dq1_dfi_parity_in_p4),
      .i_dq1_dfi_parity_in_p5       (y_ch1_dq1_dfi_parity_in_p5),
      .i_dq1_dfi_parity_in_p6       (y_ch1_dq1_dfi_parity_in_p6),
      .i_dq1_dfi_parity_in_p7       (y_ch1_dq1_dfi_parity_in_p7),
      .i_dq1_dfi_wck_ten_p0         (y_ch1_dq1_dfi_wck_ten_p0),
      .i_dq1_dfi_wck_ten_p1         (y_ch1_dq1_dfi_wck_ten_p1),
      .i_dq1_dfi_wck_ten_p2         (y_ch1_dq1_dfi_wck_ten_p2),
      .i_dq1_dfi_wck_ten_p3         (y_ch1_dq1_dfi_wck_ten_p3),
      .i_dq1_dfi_wck_ten_p4         (y_ch1_dq1_dfi_wck_ten_p4),
      .i_dq1_dfi_wck_ten_p5         (y_ch1_dq1_dfi_wck_ten_p5),
      .i_dq1_dfi_wck_ten_p6         (y_ch1_dq1_dfi_wck_ten_p6),
      .i_dq1_dfi_wck_ten_p7         (y_ch1_dq1_dfi_wck_ten_p7),
      .i_dq1_dfi_rddata_cs_p0       (y_ch1_dq1_dfi_rddata_cs_p0),
      .i_dq1_dfi_rddata_cs_p1       (y_ch1_dq1_dfi_rddata_cs_p1),
      .i_dq1_dfi_rddata_cs_p2       (y_ch1_dq1_dfi_rddata_cs_p2),
      .i_dq1_dfi_rddata_cs_p3       (y_ch1_dq1_dfi_rddata_cs_p3),
      .i_dq1_dfi_rddata_cs_p4       (y_ch1_dq1_dfi_rddata_cs_p4),
      .i_dq1_dfi_rddata_cs_p5       (y_ch1_dq1_dfi_rddata_cs_p5),
      .i_dq1_dfi_rddata_cs_p6       (y_ch1_dq1_dfi_rddata_cs_p6),
      .i_dq1_dfi_rddata_cs_p7       (y_ch1_dq1_dfi_rddata_cs_p7),
      .i_dq1_dfi_rddata_ie_p0       (y_ch1_dq1_dfi_rddata_ie_p0),
      .i_dq1_dfi_rddata_ie_p1       (y_ch1_dq1_dfi_rddata_ie_p1),
      .i_dq1_dfi_rddata_ie_p2       (y_ch1_dq1_dfi_rddata_ie_p2),
      .i_dq1_dfi_rddata_ie_p3       (y_ch1_dq1_dfi_rddata_ie_p3),
      .i_dq1_dfi_rddata_ie_p4       (y_ch1_dq1_dfi_rddata_ie_p4),
      .i_dq1_dfi_rddata_ie_p5       (y_ch1_dq1_dfi_rddata_ie_p5),
      .i_dq1_dfi_rddata_ie_p6       (y_ch1_dq1_dfi_rddata_ie_p6),
      .i_dq1_dfi_rddata_ie_p7       (y_ch1_dq1_dfi_rddata_ie_p7),
      .i_dq1_dfi_rddata_re_p0       (y_ch1_dq1_dfi_rddata_re_p0),
      .i_dq1_dfi_rddata_re_p1       (y_ch1_dq1_dfi_rddata_re_p1),
      .i_dq1_dfi_rddata_re_p2       (y_ch1_dq1_dfi_rddata_re_p2),
      .i_dq1_dfi_rddata_re_p3       (y_ch1_dq1_dfi_rddata_re_p3),
      .i_dq1_dfi_rddata_re_p4       (y_ch1_dq1_dfi_rddata_re_p4),
      .i_dq1_dfi_rddata_re_p5       (y_ch1_dq1_dfi_rddata_re_p5),
      .i_dq1_dfi_rddata_re_p6       (y_ch1_dq1_dfi_rddata_re_p6),
      .i_dq1_dfi_rddata_re_p7       (y_ch1_dq1_dfi_rddata_re_p7),
      .i_dq1_dfi_rddata_en_p0       (y_ch1_dq1_dfi_rddata_en_p0),
      .i_dq1_dfi_rddata_en_p1       (y_ch1_dq1_dfi_rddata_en_p1),
      .i_dq1_dfi_rddata_en_p2       (y_ch1_dq1_dfi_rddata_en_p2),
      .i_dq1_dfi_rddata_en_p3       (y_ch1_dq1_dfi_rddata_en_p3),
      .i_dq1_dfi_rddata_en_p4       (y_ch1_dq1_dfi_rddata_en_p4),
      .i_dq1_dfi_rddata_en_p5       (y_ch1_dq1_dfi_rddata_en_p5),
      .i_dq1_dfi_rddata_en_p6       (y_ch1_dq1_dfi_rddata_en_p6),
      .i_dq1_dfi_rddata_en_p7       (y_ch1_dq1_dfi_rddata_en_p7),
      .o_dq1_dfi_rddata_w0          (y_ch1_dq1_dfi_rddata_w0),
      .o_dq1_dfi_rddata_w1          (y_ch1_dq1_dfi_rddata_w1),
      .o_dq1_dfi_rddata_w2          (y_ch1_dq1_dfi_rddata_w2),
      .o_dq1_dfi_rddata_w3          (y_ch1_dq1_dfi_rddata_w3),
      .o_dq1_dfi_rddata_w4          (y_ch1_dq1_dfi_rddata_w4),
      .o_dq1_dfi_rddata_w5          (y_ch1_dq1_dfi_rddata_w5),
      .o_dq1_dfi_rddata_w6          (y_ch1_dq1_dfi_rddata_w6),
      .o_dq1_dfi_rddata_w7          (y_ch1_dq1_dfi_rddata_w7),
      .o_dq1_dfi_rddata_dbi_w0      (y_ch1_dq1_dfi_rddata_dbi_w0),
      .o_dq1_dfi_rddata_dbi_w1      (y_ch1_dq1_dfi_rddata_dbi_w1),
      .o_dq1_dfi_rddata_dbi_w2      (y_ch1_dq1_dfi_rddata_dbi_w2),
      .o_dq1_dfi_rddata_dbi_w3      (y_ch1_dq1_dfi_rddata_dbi_w3),
      .o_dq1_dfi_rddata_dbi_w4      (y_ch1_dq1_dfi_rddata_dbi_w4),
      .o_dq1_dfi_rddata_dbi_w5      (y_ch1_dq1_dfi_rddata_dbi_w5),
      .o_dq1_dfi_rddata_dbi_w6      (y_ch1_dq1_dfi_rddata_dbi_w6),
      .o_dq1_dfi_rddata_dbi_w7      (y_ch1_dq1_dfi_rddata_dbi_w7),
      .o_dq1_dfi_rddata_valid       (y_ch1_dq1_dfi_rddata_valid),

      .o_dq0_sdr                    (o_ch1_dq0_sdr),
      .i_dq0_sdr                    (i_ch1_dq0_sdr),
      .i_dq0_sdr_vld                (i_ch1_dq0_sdr_vld),
      .o_dqs0_sdr                   (o_ch1_dqs0_sdr),
      .o_dq1_sdr                    (o_ch1_dq1_sdr),
      .i_dq1_sdr                    (i_ch1_dq1_sdr),
      .i_dq1_sdr_vld                (i_ch1_dq1_sdr_vld),
      .o_dqs1_sdr                   (o_ch1_dqs1_sdr),

      .i_txrx_mode                  (i_txrx_mode),
      .i_tx0_sdr                    (i_ch1_tx0_sdr),
      .i_tx_ck0_sdr                 (i_ch1_tx_ck0_sdr),
      .o_rx0_sdr                    (o_ch1_rx0_sdr),
      .o_rx0_sdr_vld                (o_ch1_rx0_sdr_vld),
      .i_tx1_sdr                    (i_ch1_tx1_sdr),
      .i_tx_ck1_sdr                 (i_ch1_tx_ck1_sdr),
      .o_rx1_sdr                    (o_ch1_rx1_sdr),
      .o_rx1_sdr_vld                (o_ch1_rx1_sdr_vld),

      .o_ca_sdr                     (o_ch1_ca_sdr),
      .i_ca_sdr                     (i_ch1_ca_sdr),
      .i_ca_sdr_vld                 (i_ch1_ca_sdr_vld),
      .o_ck_sdr                     (o_ch1_ck_sdr)

   );

endmodule

module ddr_dfi_dp_ca  #(
    parameter AWIDTH                =  7,
    parameter CWIDTH                =  11,
    parameter NUM_WPH               = 8,
    parameter F0WIDTH               = 2

) (
   input  logic                                                  i_scan_cgc_ctrl,
   input  logic                                                  i_rst,

   // Clock
   input  logic                                                  i_cmdc_clk_0,
   input  logic                                                  i_cmdc_clk_1,
   input  logic                                                  i_cmdc_clk_2,
   input  logic                                                  i_cmda_clk_0,
   input  logic                                                  i_cmda_clk_1,
   input  logic                                                  i_cmda_clk_2,

   input  logic                                                  i_dfi_clk    ,
   input  logic                                                  i_rd_clk_1   ,
   input  logic                                                  i_rd_clk_2   ,

   // Data Path Configuration
   input  logic [`DDR_DFICH_CTRL0_M0_CFG_RANGE]    i_dfi_ctrl0_cfg,
   input  logic [`DDR_DFICH_WRC_M0_CFG_RANGE]      i_dfi_wrc_cfg,
   input  logic [`DDR_DFICH_WRCCTRL_M0_CFG_RANGE]  i_dfi_wrcctrl_cfg,
   input  logic [`DDR_DFICH_CKCTRL_M0_CFG_RANGE]   i_dfi_ckctrl_cfg,
   input  logic [`DDR_DFICH_RDC_M0_CFG_RANGE]      i_dfi_rdc_cfg,

   // Write Command/Address
   input  logic [AWIDTH-1:0]        i_dfi_address_p0,
   input  logic [AWIDTH-1:0]        i_dfi_address_p1,
   input  logic [AWIDTH-1:0]        i_dfi_address_p2,
   input  logic [AWIDTH-1:0]        i_dfi_address_p3,
   input  logic [AWIDTH-1:0]        i_dfi_address_p4,
   input  logic [AWIDTH-1:0]        i_dfi_address_p5,
   input  logic [AWIDTH-1:0]        i_dfi_address_p6,
   input  logic [AWIDTH-1:0]        i_dfi_address_p7,
   input  logic [1:0]               i_dfi_cke_p0,
   input  logic [1:0]               i_dfi_cke_p1,
   input  logic [1:0]               i_dfi_cke_p2,
   input  logic [1:0]               i_dfi_cke_p3,
   input  logic [1:0]               i_dfi_cke_p4,
   input  logic [1:0]               i_dfi_cke_p5,
   input  logic [1:0]               i_dfi_cke_p6,
   input  logic [1:0]               i_dfi_cke_p7,
   input  logic [1:0]               i_dfi_cs_p0,
   input  logic [1:0]               i_dfi_cs_p1,
   input  logic [1:0]               i_dfi_cs_p2,
   input  logic [1:0]               i_dfi_cs_p3,
   input  logic [1:0]               i_dfi_cs_p4,
   input  logic [1:0]               i_dfi_cs_p5,
   input  logic [1:0]               i_dfi_cs_p6,
   input  logic [1:0]               i_dfi_cs_p7,
   input  logic                     i_dfi_dcd_p0,
   input  logic                     i_dfi_dcd_p1,
   input  logic                     i_dfi_dcd_p2,
   input  logic                     i_dfi_dcd_p3,
   input  logic                     i_dfi_dcd_p4,
   input  logic                     i_dfi_dcd_p5,
   input  logic                     i_dfi_dcd_p6,
   input  logic                     i_dfi_dcd_p7,

   output logic [AWIDTH-1:0]        o_dfi_address_p0,
   output logic [AWIDTH-1:0]        o_dfi_address_p1,
   output logic [AWIDTH-1:0]        o_dfi_address_p2,
   output logic [AWIDTH-1:0]        o_dfi_address_p3,
   output logic [AWIDTH-1:0]        o_dfi_address_p4,
   output logic [AWIDTH-1:0]        o_dfi_address_p5,
   output logic [AWIDTH-1:0]        o_dfi_address_p6,
   output logic [AWIDTH-1:0]        o_dfi_address_p7,
   output logic [1:0]               o_dfi_cke_p0,
   output logic [1:0]               o_dfi_cke_p1,
   output logic [1:0]               o_dfi_cke_p2,
   output logic [1:0]               o_dfi_cke_p3,
   output logic [1:0]               o_dfi_cke_p4,
   output logic [1:0]               o_dfi_cke_p5,
   output logic [1:0]               o_dfi_cke_p6,
   output logic [1:0]               o_dfi_cke_p7,
   output logic [1:0]               o_dfi_cs_p0,
   output logic [1:0]               o_dfi_cs_p1,
   output logic [1:0]               o_dfi_cs_p2,
   output logic [1:0]               o_dfi_cs_p3,
   output logic [1:0]               o_dfi_cs_p4,
   output logic [1:0]               o_dfi_cs_p5,
   output logic [1:0]               o_dfi_cs_p6,
   output logic [1:0]               o_dfi_cs_p7,
   output logic                     o_dfi_dcd_p0,
   output logic                     o_dfi_dcd_p1,
   output logic                     o_dfi_dcd_p2,
   output logic                     o_dfi_dcd_p3,
   output logic                     o_dfi_dcd_p4,
   output logic                     o_dfi_dcd_p5,
   output logic                     o_dfi_dcd_p6,
   output logic                     o_dfi_dcd_p7,
   output logic                     o_dfi_dce_p0,
   output logic                     o_dfi_dce_p1,
   output logic                     o_dfi_dce_p2,
   output logic                     o_dfi_dce_p3,
   output logic                     o_dfi_dce_p4,
   output logic                     o_dfi_dce_p5,
   output logic                     o_dfi_dce_p6,
   output logic                     o_dfi_dce_p7,

   // Read Command/Address Interface
   input  logic [AWIDTH-1:0]        i_dfi_address_w0,
   input  logic [AWIDTH-1:0]        i_dfi_address_w1,
   input  logic [AWIDTH-1:0]        i_dfi_address_w2,
   input  logic [AWIDTH-1:0]        i_dfi_address_w3,
   input  logic [AWIDTH-1:0]        i_dfi_address_w4,
   input  logic [AWIDTH-1:0]        i_dfi_address_w5,
   input  logic [AWIDTH-1:0]        i_dfi_address_w6,
   input  logic [AWIDTH-1:0]        i_dfi_address_w7,
   input  logic [1:0]               i_dfi_cke_w0,
   input  logic [1:0]               i_dfi_cke_w1,
   input  logic [1:0]               i_dfi_cke_w2,
   input  logic [1:0]               i_dfi_cke_w3,
   input  logic [1:0]               i_dfi_cke_w4,
   input  logic [1:0]               i_dfi_cke_w5,
   input  logic [1:0]               i_dfi_cke_w6,
   input  logic [1:0]               i_dfi_cke_w7,
   input  logic [1:0]               i_dfi_cs_w0,
   input  logic [1:0]               i_dfi_cs_w1,
   input  logic [1:0]               i_dfi_cs_w2,
   input  logic [1:0]               i_dfi_cs_w3,
   input  logic [1:0]               i_dfi_cs_w4,
   input  logic [1:0]               i_dfi_cs_w5,
   input  logic [1:0]               i_dfi_cs_w6,
   input  logic [1:0]               i_dfi_cs_w7,
   input  logic [CWIDTH-1:0]        i_dfi_address_valid,

   output logic [AWIDTH-1:0]        o_dfi_address_w0,
   output logic [AWIDTH-1:0]        o_dfi_address_w1,
   output logic [AWIDTH-1:0]        o_dfi_address_w2,
   output logic [AWIDTH-1:0]        o_dfi_address_w3,
   output logic [AWIDTH-1:0]        o_dfi_address_w4,
   output logic [AWIDTH-1:0]        o_dfi_address_w5,
   output logic [AWIDTH-1:0]        o_dfi_address_w6,
   output logic [AWIDTH-1:0]        o_dfi_address_w7,
   output logic [1:0]               o_dfi_cke_w0,
   output logic [1:0]               o_dfi_cke_w1,
   output logic [1:0]               o_dfi_cke_w2,
   output logic [1:0]               o_dfi_cke_w3,
   output logic [1:0]               o_dfi_cke_w4,
   output logic [1:0]               o_dfi_cke_w5,
   output logic [1:0]               o_dfi_cke_w6,
   output logic [1:0]               o_dfi_cke_w7,
   output logic [1:0]               o_dfi_cs_w0,
   output logic [1:0]               o_dfi_cs_w1,
   output logic [1:0]               o_dfi_cs_w2,
   output logic [1:0]               o_dfi_cs_w3,
   output logic [1:0]               o_dfi_cs_w4,
   output logic [1:0]               o_dfi_cs_w5,
   output logic [1:0]               o_dfi_cs_w6,
   output logic [1:0]               o_dfi_cs_w7,
   output logic                     o_dfi_address_valid_w0,
   output logic                     o_dfi_address_valid_w1,
   output logic                     o_dfi_address_valid_w2,
   output logic                     o_dfi_address_valid_w3,
   output logic                     o_dfi_address_valid_w4,
   output logic                     o_dfi_address_valid_w5,
   output logic                     o_dfi_address_valid_w6,
   output logic                     o_dfi_address_valid_w7,

   output logic [31:0]              o_debug

);

    assign o_debug = {  {(32-(2* 8 )){1'b0}} ,
                        o_dfi_cke_p7,
                        o_dfi_cke_p6,
                        o_dfi_cke_p5,
                        o_dfi_cke_p4,
                        o_dfi_cke_p3,
                        o_dfi_cke_p2,
                        o_dfi_cke_p1,
                        o_dfi_cke_p0,
                        o_dfi_dce_p7,
                        o_dfi_dce_p6,
                        o_dfi_dce_p5,
                        o_dfi_dce_p4,
                        o_dfi_dce_p3,
                        o_dfi_dce_p2,
                        o_dfi_dce_p1,
                        o_dfi_dce_p0
                     } ;
   // ------------------------------------------------------------------------
   // DFI Write Command/Address Interface
   // ------------------------------------------------------------------------

   ddr_dfi_write_cmd #(
      .SWIDTH                       (AWIDTH),
      .NUM_WPH                      (NUM_WPH),
      .FWIDTH                       (F0WIDTH)
   ) u_dq_dfi_write_cmd (
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_cmdc_clk_0                 (i_cmdc_clk_0),
      .i_cmdc_clk_1                 (i_cmdc_clk_1),
      .i_cmdc_clk_2                 (i_cmdc_clk_2),

      .i_cmda_clk_0                 (i_cmda_clk_0),
      .i_cmda_clk_1                 (i_cmda_clk_1),
      .i_cmda_clk_2                 (i_cmda_clk_2),

      .i_wrc_pipe_en                (i_dfi_wrc_cfg[`DDR_DFICH_WRC_M0_CFG_PIPE_EN_FIELD]),
      .i_wrc_gb_mode                (cast_dwgb_t(i_dfi_wrc_cfg[`DDR_DFICH_WRC_M0_CFG_GB_MODE_FIELD])),
      .i_wrc_post_gb_dly            (i_dfi_wrc_cfg[`DDR_DFICH_WRC_M0_CFG_POST_GB_FC_DLY_FIELD]),

      .i_wrcctrl_pipe_en            (i_dfi_wrcctrl_cfg[`DDR_DFICH_WRCCTRL_M0_CFG_PIPE_EN_FIELD]),
      .i_wrcctrl_gb_mode            (cast_dwgb_t(i_dfi_wrcctrl_cfg[`DDR_DFICH_WRCCTRL_M0_CFG_GB_MODE_FIELD])),
      .i_wrcctrl_post_gb_dly        (i_dfi_wrcctrl_cfg[`DDR_DFICH_WRCCTRL_M0_CFG_POST_GB_FC_DLY_FIELD]),

      .i_ckctrl_pipe_en             (i_dfi_ckctrl_cfg[`DDR_DFICH_CKCTRL_M0_CFG_PIPE_EN_FIELD]),
      .i_ckctrl_gb_mode             (cast_dwgb_t(i_dfi_ckctrl_cfg[`DDR_DFICH_CKCTRL_M0_CFG_GB_MODE_FIELD])),
      .i_ckctrl_post_gb_dly         (i_dfi_ckctrl_cfg[`DDR_DFICH_CKCTRL_M0_CFG_POST_GB_FC_DLY_FIELD]),

      .i_dfi_address_p0             (i_dfi_address_p0),
      .i_dfi_address_p1             (i_dfi_address_p1),
      .i_dfi_address_p2             (i_dfi_address_p2),
      .i_dfi_address_p3             (i_dfi_address_p3),
      .i_dfi_address_p4             (i_dfi_address_p4),
      .i_dfi_address_p5             (i_dfi_address_p5),
      .i_dfi_address_p6             (i_dfi_address_p6),
      .i_dfi_address_p7             (i_dfi_address_p7),
      .i_dfi_cke_p0                 (i_dfi_cke_p0),
      .i_dfi_cke_p1                 (i_dfi_cke_p1),
      .i_dfi_cke_p2                 (i_dfi_cke_p2),
      .i_dfi_cke_p3                 (i_dfi_cke_p3),
      .i_dfi_cke_p4                 (i_dfi_cke_p4),
      .i_dfi_cke_p5                 (i_dfi_cke_p5),
      .i_dfi_cke_p6                 (i_dfi_cke_p6),
      .i_dfi_cke_p7                 (i_dfi_cke_p7),
      .i_dfi_cs_p0                  (i_dfi_cs_p0),
      .i_dfi_cs_p1                  (i_dfi_cs_p1),
      .i_dfi_cs_p2                  (i_dfi_cs_p2),
      .i_dfi_cs_p3                  (i_dfi_cs_p3),
      .i_dfi_cs_p4                  (i_dfi_cs_p4),
      .i_dfi_cs_p5                  (i_dfi_cs_p5),
      .i_dfi_cs_p6                  (i_dfi_cs_p6),
      .i_dfi_cs_p7                  (i_dfi_cs_p7),
      .i_dfi_dcd_p0                 (i_dfi_dcd_p0),
      .i_dfi_dcd_p1                 (i_dfi_dcd_p1),
      .i_dfi_dcd_p2                 (i_dfi_dcd_p2),
      .i_dfi_dcd_p3                 (i_dfi_dcd_p3),
      .i_dfi_dcd_p4                 (i_dfi_dcd_p4),
      .i_dfi_dcd_p5                 (i_dfi_dcd_p5),
      .i_dfi_dcd_p6                 (i_dfi_dcd_p6),
      .i_dfi_dcd_p7                 (i_dfi_dcd_p7),

      .o_dfi_address_p0             (o_dfi_address_p0),
      .o_dfi_address_p1             (o_dfi_address_p1),
      .o_dfi_address_p2             (o_dfi_address_p2),
      .o_dfi_address_p3             (o_dfi_address_p3),
      .o_dfi_address_p4             (o_dfi_address_p4),
      .o_dfi_address_p5             (o_dfi_address_p5),
      .o_dfi_address_p6             (o_dfi_address_p6),
      .o_dfi_address_p7             (o_dfi_address_p7),
      .o_dfi_cke_p0                 (o_dfi_cke_p0),
      .o_dfi_cke_p1                 (o_dfi_cke_p1),
      .o_dfi_cke_p2                 (o_dfi_cke_p2),
      .o_dfi_cke_p3                 (o_dfi_cke_p3),
      .o_dfi_cke_p4                 (o_dfi_cke_p4),
      .o_dfi_cke_p5                 (o_dfi_cke_p5),
      .o_dfi_cke_p6                 (o_dfi_cke_p6),
      .o_dfi_cke_p7                 (o_dfi_cke_p7),
      .o_dfi_cs_p0                  (o_dfi_cs_p0),
      .o_dfi_cs_p1                  (o_dfi_cs_p1),
      .o_dfi_cs_p2                  (o_dfi_cs_p2),
      .o_dfi_cs_p3                  (o_dfi_cs_p3),
      .o_dfi_cs_p4                  (o_dfi_cs_p4),
      .o_dfi_cs_p5                  (o_dfi_cs_p5),
      .o_dfi_cs_p6                  (o_dfi_cs_p6),
      .o_dfi_cs_p7                  (o_dfi_cs_p7),
      .o_dfi_dcd_p0                 (o_dfi_dcd_p0),
      .o_dfi_dcd_p1                 (o_dfi_dcd_p1),
      .o_dfi_dcd_p2                 (o_dfi_dcd_p2),
      .o_dfi_dcd_p3                 (o_dfi_dcd_p3),
      .o_dfi_dcd_p4                 (o_dfi_dcd_p4),
      .o_dfi_dcd_p5                 (o_dfi_dcd_p5),
      .o_dfi_dcd_p6                 (o_dfi_dcd_p6),
      .o_dfi_dcd_p7                 (o_dfi_dcd_p7),

      .o_debug                      ()
   );

   assign o_dfi_dce_p0 = ~o_dfi_dcd_p0;
   assign o_dfi_dce_p1 = ~o_dfi_dcd_p1;
   assign o_dfi_dce_p2 = ~o_dfi_dcd_p2;
   assign o_dfi_dce_p3 = ~o_dfi_dcd_p3;
   assign o_dfi_dce_p4 = ~o_dfi_dcd_p4;
   assign o_dfi_dce_p5 = ~o_dfi_dcd_p5;
   assign o_dfi_dce_p6 = ~o_dfi_dcd_p6;
   assign o_dfi_dce_p7 = ~o_dfi_dcd_p7;

   // ------------------------------------------------------------------------
   // DFI Read Command Interface
   // ------------------------------------------------------------------------

   ddr_dfi_read_cmd #(
     .CWIDTH                        (CWIDTH),
     .AWIDTH                        (AWIDTH)
   ) u_dfi_read_cmd (
      .i_clk_1                      (i_rd_clk_1  ),  // DIV2
      .i_clk_2                      (i_rd_clk_2  ),  // DIV4
      .i_dfi_clk                    (i_dfi_clk ),  // DFI clock
      .i_rgb_mode                   (cast_drgb_t(i_dfi_rdc_cfg[`DDR_DFICH_RDC_M0_CFG_GB_MODE_FIELD])),
      .i_intf_pipe_en               (i_dfi_ctrl0_cfg[`DDR_DFICH_CTRL0_M0_CFG_RD_INTF_PIPE_EN_FIELD]),
      .i_dfi_address_w0             (i_dfi_address_w0),
      .i_dfi_address_w1             (i_dfi_address_w1),
      .i_dfi_address_w2             (i_dfi_address_w2),
      .i_dfi_address_w3             (i_dfi_address_w3),
      .i_dfi_address_w4             (i_dfi_address_w4),
      .i_dfi_address_w5             (i_dfi_address_w5),
      .i_dfi_address_w6             (i_dfi_address_w6),
      .i_dfi_address_w7             (i_dfi_address_w7),
      .i_dfi_cs_w0                  (i_dfi_cs_w0),
      .i_dfi_cs_w1                  (i_dfi_cs_w1),
      .i_dfi_cs_w2                  (i_dfi_cs_w2),
      .i_dfi_cs_w3                  (i_dfi_cs_w3),
      .i_dfi_cs_w4                  (i_dfi_cs_w4),
      .i_dfi_cs_w5                  (i_dfi_cs_w5),
      .i_dfi_cs_w6                  (i_dfi_cs_w6),
      .i_dfi_cs_w7                  (i_dfi_cs_w7),
      .i_dfi_cke_w0                 (i_dfi_cke_w0),
      .i_dfi_cke_w1                 (i_dfi_cke_w1),
      .i_dfi_cke_w2                 (i_dfi_cke_w2),
      .i_dfi_cke_w3                 (i_dfi_cke_w3),
      .i_dfi_cke_w4                 (i_dfi_cke_w4),
      .i_dfi_cke_w5                 (i_dfi_cke_w5),
      .i_dfi_cke_w6                 (i_dfi_cke_w6),
      .i_dfi_cke_w7                 (i_dfi_cke_w7),
      .i_dfi_address_valid          (i_dfi_address_valid),

      .o_dfi_address_w0             (o_dfi_address_w0),
      .o_dfi_address_w1             (o_dfi_address_w1),
      .o_dfi_address_w2             (o_dfi_address_w2),
      .o_dfi_address_w3             (o_dfi_address_w3),
      .o_dfi_address_w4             (o_dfi_address_w4),
      .o_dfi_address_w5             (o_dfi_address_w5),
      .o_dfi_address_w6             (o_dfi_address_w6),
      .o_dfi_address_w7             (o_dfi_address_w7),
      .o_dfi_cs_w0                  (o_dfi_cs_w0),
      .o_dfi_cs_w1                  (o_dfi_cs_w1),
      .o_dfi_cs_w2                  (o_dfi_cs_w2),
      .o_dfi_cs_w3                  (o_dfi_cs_w3),
      .o_dfi_cs_w4                  (o_dfi_cs_w4),
      .o_dfi_cs_w5                  (o_dfi_cs_w5),
      .o_dfi_cs_w6                  (o_dfi_cs_w6),
      .o_dfi_cs_w7                  (o_dfi_cs_w7),
      .o_dfi_cke_w0                 (o_dfi_cke_w0),
      .o_dfi_cke_w1                 (o_dfi_cke_w1),
      .o_dfi_cke_w2                 (o_dfi_cke_w2),
      .o_dfi_cke_w3                 (o_dfi_cke_w3),
      .o_dfi_cke_w4                 (o_dfi_cke_w4),
      .o_dfi_cke_w5                 (o_dfi_cke_w5),
      .o_dfi_cke_w6                 (o_dfi_cke_w6),
      .o_dfi_cke_w7                 (o_dfi_cke_w7),
      .o_dfi_address_valid_w0      (o_dfi_address_valid_w0),
      .o_dfi_address_valid_w1      (o_dfi_address_valid_w1),
      .o_dfi_address_valid_w2      (o_dfi_address_valid_w2),
      .o_dfi_address_valid_w3      (o_dfi_address_valid_w3),
      .o_dfi_address_valid_w4      (o_dfi_address_valid_w4),
      .o_dfi_address_valid_w5      (o_dfi_address_valid_w5),
      .o_dfi_address_valid_w6      (o_dfi_address_valid_w6),
      .o_dfi_address_valid_w7      (o_dfi_address_valid_w7),
      .o_debug                      ()
   );

endmodule

module ddr_dfi_dp_dq  #(
    parameter NUM_DQ           = 2,
    parameter SWIDTH           = 8,            // PHY Slice Width
    parameter BWIDTH           = SWIDTH / 8,   // BYTE Width
    parameter MWIDTH           = BWIDTH,        // Mask width
    parameter TWIDTH           = BWIDTH * 2,   // Toggle width
    parameter PWIDTH           = 4,            // Pulse Extension width
    parameter F0WIDTH          = 2,
    parameter F1WIDTH          = 2,
    parameter F2WIDTH          = 2,
    parameter MAXF2DLY         = (1 << F2WIDTH) -1 ,
    parameter NUM_WPH          = 8

) (
   input  logic                                                  i_scan_cgc_ctrl,
   input  logic                                                  i_rst,

   // Clock
   input  logic                                                  i_wrd_clk_0  ,
   input  logic                                                  i_wrd_clk_1  ,
   input  logic                                                  i_wrd_clk_2  ,
   input  logic                                                  i_wrc_clk_0  ,
   input  logic                                                  i_wrc_clk_1  ,
   input  logic                                                  i_wrc_clk_2  ,

   input  logic                                                  i_dfi_clk    ,
   input  logic                                                  i_rd_clk_1   ,
   input  logic                                                  i_rd_clk_2   ,
  // Data Path Configuration
   input  logic [`DDR_DFICH_TOP_1_CFG_RANGE]       i_dfi_top_1_cfg,
   input  logic [`DDR_DFICH_RCTRL_M0_CFG_RANGE]    i_dfi_rctrl_cfg,
   input  logic [`DDR_DFICH_WCTRL_M0_CFG_RANGE]    i_dfi_wctrl_cfg,
   input  logic [`DDR_DFICH_WENCTRL_M0_CFG_RANGE]  i_dfi_wenctrl_cfg,
   input  logic [`DDR_DFICH_WCKCTRL_M0_CFG_RANGE]  i_dfi_wckctrl_cfg,
   input  logic [`DDR_DFICH_WRD_M0_CFG_RANGE]      i_dfi_wrd_cfg,
   input  logic [`DDR_DFICH_RDD_M0_CFG_RANGE]      i_dfi_rdd_cfg,
   input  logic [`DDR_DFICH_CTRL0_M0_CFG_RANGE]    i_dfi_ctrl0_cfg,
   input  logic [`DDR_DFICH_CTRL1_M0_CFG_RANGE]    i_dfi_ctrl1_cfg,
   input  logic [`DDR_DFICH_CTRL2_M0_CFG_RANGE]    i_dfi_ctrl2_cfg,
   input  logic [`DDR_DFICH_CTRL3_M0_CFG_RANGE]    i_dfi_ctrl3_cfg,
   input  logic [`DDR_DFICH_CTRL4_M0_CFG_RANGE]    i_dfi_ctrl4_cfg,
   input  logic [`DDR_DFICH_CTRL5_M0_CFG_RANGE]    i_dfi_ctrl5_cfg,

   // Write data Interface
   input  logic [SWIDTH-1:0]        i_dq0_dfi_wrdata_p0,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_wrdata_p1,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_wrdata_p2,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_wrdata_p3,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_wrdata_p4,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_wrdata_p5,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_wrdata_p6,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_wrdata_p7,

   input  logic [MWIDTH-1:0]        i_dq0_dfi_wrdata_mask_p0,
   input  logic [MWIDTH-1:0]        i_dq0_dfi_wrdata_mask_p1,
   input  logic [MWIDTH-1:0]        i_dq0_dfi_wrdata_mask_p2,
   input  logic [MWIDTH-1:0]        i_dq0_dfi_wrdata_mask_p3,
   input  logic [MWIDTH-1:0]        i_dq0_dfi_wrdata_mask_p4,
   input  logic [MWIDTH-1:0]        i_dq0_dfi_wrdata_mask_p5,
   input  logic [MWIDTH-1:0]        i_dq0_dfi_wrdata_mask_p6,
   input  logic [MWIDTH-1:0]        i_dq0_dfi_wrdata_mask_p7,

   output logic [SWIDTH-1:0]        o_dq0_dfi_wrdata_p0,
   output logic [SWIDTH-1:0]        o_dq0_dfi_wrdata_p1,
   output logic [SWIDTH-1:0]        o_dq0_dfi_wrdata_p2,
   output logic [SWIDTH-1:0]        o_dq0_dfi_wrdata_p3,
   output logic [SWIDTH-1:0]        o_dq0_dfi_wrdata_p4,
   output logic [SWIDTH-1:0]        o_dq0_dfi_wrdata_p5,
   output logic [SWIDTH-1:0]        o_dq0_dfi_wrdata_p6,
   output logic [SWIDTH-1:0]        o_dq0_dfi_wrdata_p7,
   output logic [MWIDTH-1:0]        o_dq0_dfi_wrdata_mask_p0,
   output logic [MWIDTH-1:0]        o_dq0_dfi_wrdata_mask_p1,
   output logic [MWIDTH-1:0]        o_dq0_dfi_wrdata_mask_p2,
   output logic [MWIDTH-1:0]        o_dq0_dfi_wrdata_mask_p3,
   output logic [MWIDTH-1:0]        o_dq0_dfi_wrdata_mask_p4,
   output logic [MWIDTH-1:0]        o_dq0_dfi_wrdata_mask_p5,
   output logic [MWIDTH-1:0]        o_dq0_dfi_wrdata_mask_p6,
   output logic [MWIDTH-1:0]        o_dq0_dfi_wrdata_mask_p7,

   // Wck/Write Enable Interafce
   input  logic                     i_dq0_dfi_wrdata_en_p0,
   input  logic                     i_dq0_dfi_wrdata_en_p1,
   input  logic                     i_dq0_dfi_wrdata_en_p2,
   input  logic                     i_dq0_dfi_wrdata_en_p3,
   input  logic                     i_dq0_dfi_wrdata_en_p4,
   input  logic                     i_dq0_dfi_wrdata_en_p5,
   input  logic                     i_dq0_dfi_wrdata_en_p6,
   input  logic                     i_dq0_dfi_wrdata_en_p7,
   input  logic                     i_dq0_dfi_parity_in_p0,
   input  logic                     i_dq0_dfi_parity_in_p1,
   input  logic                     i_dq0_dfi_parity_in_p2,
   input  logic                     i_dq0_dfi_parity_in_p3,
   input  logic                     i_dq0_dfi_parity_in_p4,
   input  logic                     i_dq0_dfi_parity_in_p5,
   input  logic                     i_dq0_dfi_parity_in_p6,
   input  logic                     i_dq0_dfi_parity_in_p7,
   input  logic                     i_dq0_dfi_wrdata_cs_p0,
   input  logic                     i_dq0_dfi_wrdata_cs_p1,
   input  logic                     i_dq0_dfi_wrdata_cs_p2,
   input  logic                     i_dq0_dfi_wrdata_cs_p3,
   input  logic                     i_dq0_dfi_wrdata_cs_p4,
   input  logic                     i_dq0_dfi_wrdata_cs_p5,
   input  logic                     i_dq0_dfi_wrdata_cs_p6,
   input  logic                     i_dq0_dfi_wrdata_cs_p7,

   input  logic                     i_dq0_dfi_wck_cs_p0,
   input  logic                     i_dq0_dfi_wck_cs_p1,
   input  logic                     i_dq0_dfi_wck_cs_p2,
   input  logic                     i_dq0_dfi_wck_cs_p3,
   input  logic                     i_dq0_dfi_wck_cs_p4,
   input  logic                     i_dq0_dfi_wck_cs_p5,
   input  logic                     i_dq0_dfi_wck_cs_p6,
   input  logic                     i_dq0_dfi_wck_cs_p7,
   input  logic                     i_dq0_dfi_wck_en_p0,
   input  logic                     i_dq0_dfi_wck_en_p1,
   input  logic                     i_dq0_dfi_wck_en_p2,
   input  logic                     i_dq0_dfi_wck_en_p3,
   input  logic                     i_dq0_dfi_wck_en_p4,
   input  logic                     i_dq0_dfi_wck_en_p5,
   input  logic                     i_dq0_dfi_wck_en_p6,
   input  logic                     i_dq0_dfi_wck_en_p7,
   input  logic [TWIDTH-1:0]        i_dq0_dfi_wck_toggle_p0,
   input  logic [TWIDTH-1:0]        i_dq0_dfi_wck_toggle_p1,
   input  logic [TWIDTH-1:0]        i_dq0_dfi_wck_toggle_p2,
   input  logic [TWIDTH-1:0]        i_dq0_dfi_wck_toggle_p3,
   input  logic [TWIDTH-1:0]        i_dq0_dfi_wck_toggle_p4,
   input  logic [TWIDTH-1:0]        i_dq0_dfi_wck_toggle_p5,
   input  logic [TWIDTH-1:0]        i_dq0_dfi_wck_toggle_p6,
   input  logic [TWIDTH-1:0]        i_dq0_dfi_wck_toggle_p7,
   output logic                     o_dq0_dfi_wrdata_en_p0,
   output logic                     o_dq0_dfi_wrdata_en_p1,
   output logic                     o_dq0_dfi_wrdata_en_p2,
   output logic                     o_dq0_dfi_wrdata_en_p3,
   output logic                     o_dq0_dfi_wrdata_en_p4,
   output logic                     o_dq0_dfi_wrdata_en_p5,
   output logic                     o_dq0_dfi_wrdata_en_p6,
   output logic                     o_dq0_dfi_wrdata_en_p7,
   output logic                     o_dq0_dfi_wrdata_oe_p0,
   output logic                     o_dq0_dfi_wrdata_oe_p1,
   output logic                     o_dq0_dfi_wrdata_oe_p2,
   output logic                     o_dq0_dfi_wrdata_oe_p3,
   output logic                     o_dq0_dfi_wrdata_oe_p4,
   output logic                     o_dq0_dfi_wrdata_oe_p5,
   output logic                     o_dq0_dfi_wrdata_oe_p6,
   output logic                     o_dq0_dfi_wrdata_oe_p7,
   output logic                     o_dq0_dfi_parity_in_p0,
   output logic                     o_dq0_dfi_parity_in_p1,
   output logic                     o_dq0_dfi_parity_in_p2,
   output logic                     o_dq0_dfi_parity_in_p3,
   output logic                     o_dq0_dfi_parity_in_p4,
   output logic                     o_dq0_dfi_parity_in_p5,
   output logic                     o_dq0_dfi_parity_in_p6,
   output logic                     o_dq0_dfi_parity_in_p7,
   output logic                     o_dq0_dfi_wrdata_cs_p0,
   output logic                     o_dq0_dfi_wrdata_cs_p1,
   output logic                     o_dq0_dfi_wrdata_cs_p2,
   output logic                     o_dq0_dfi_wrdata_cs_p3,
   output logic                     o_dq0_dfi_wrdata_cs_p4,
   output logic                     o_dq0_dfi_wrdata_cs_p5,
   output logic                     o_dq0_dfi_wrdata_cs_p6,
   output logic                     o_dq0_dfi_wrdata_cs_p7,
   output logic                     o_dq0_dfi_wck_en_p0,
   output logic                     o_dq0_dfi_wck_en_p1,
   output logic                     o_dq0_dfi_wck_en_p2,
   output logic                     o_dq0_dfi_wck_en_p3,
   output logic                     o_dq0_dfi_wck_en_p4,
   output logic                     o_dq0_dfi_wck_en_p5,
   output logic                     o_dq0_dfi_wck_en_p6,
   output logic                     o_dq0_dfi_wck_en_p7,
   output logic                     o_dq0_dfi_wck_oe_p0,
   output logic                     o_dq0_dfi_wck_oe_p1,
   output logic                     o_dq0_dfi_wck_oe_p2,
   output logic                     o_dq0_dfi_wck_oe_p3,
   output logic                     o_dq0_dfi_wck_oe_p4,
   output logic                     o_dq0_dfi_wck_oe_p5,
   output logic                     o_dq0_dfi_wck_oe_p6,
   output logic                     o_dq0_dfi_wck_oe_p7,
   output logic                     o_dq0_dfi_wck_ten_p0,
   output logic                     o_dq0_dfi_wck_ten_p1,
   output logic                     o_dq0_dfi_wck_ten_p2,
   output logic                     o_dq0_dfi_wck_ten_p3,
   output logic                     o_dq0_dfi_wck_ten_p4,
   output logic                     o_dq0_dfi_wck_ten_p5,
   output logic                     o_dq0_dfi_wck_ten_p6,
   output logic                     o_dq0_dfi_wck_ten_p7,
   output logic                     o_dq0_dfi_wck_cs_p0,
   output logic                     o_dq0_dfi_wck_cs_p1,
   output logic                     o_dq0_dfi_wck_cs_p2,
   output logic                     o_dq0_dfi_wck_cs_p3,
   output logic                     o_dq0_dfi_wck_cs_p4,
   output logic                     o_dq0_dfi_wck_cs_p5,
   output logic                     o_dq0_dfi_wck_cs_p6,
   output logic                     o_dq0_dfi_wck_cs_p7,

   input  logic                     i_dq0_dfi_rddata_en_p0,
   input  logic                     i_dq0_dfi_rddata_en_p1,
   input  logic                     i_dq0_dfi_rddata_en_p2,
   input  logic                     i_dq0_dfi_rddata_en_p3,
   input  logic                     i_dq0_dfi_rddata_en_p4,
   input  logic                     i_dq0_dfi_rddata_en_p5,
   input  logic                     i_dq0_dfi_rddata_en_p6,
   input  logic                     i_dq0_dfi_rddata_en_p7,

   input  logic                     i_dq0_dfi_rddata_cs_p0,
   input  logic                     i_dq0_dfi_rddata_cs_p1,
   input  logic                     i_dq0_dfi_rddata_cs_p2,
   input  logic                     i_dq0_dfi_rddata_cs_p3,
   input  logic                     i_dq0_dfi_rddata_cs_p4,
   input  logic                     i_dq0_dfi_rddata_cs_p5,
   input  logic                     i_dq0_dfi_rddata_cs_p6,
   input  logic                     i_dq0_dfi_rddata_cs_p7,

   output logic                     o_dq0_dfi_rddata_en_p0,
   output logic                     o_dq0_dfi_rddata_en_p1,
   output logic                     o_dq0_dfi_rddata_en_p2,
   output logic                     o_dq0_dfi_rddata_en_p3,
   output logic                     o_dq0_dfi_rddata_en_p4,
   output logic                     o_dq0_dfi_rddata_en_p5,
   output logic                     o_dq0_dfi_rddata_en_p6,
   output logic                     o_dq0_dfi_rddata_en_p7,
   output logic                     o_dq0_dfi_rddata_ie_p0,
   output logic                     o_dq0_dfi_rddata_ie_p1,
   output logic                     o_dq0_dfi_rddata_ie_p2,
   output logic                     o_dq0_dfi_rddata_ie_p3,
   output logic                     o_dq0_dfi_rddata_ie_p4,
   output logic                     o_dq0_dfi_rddata_ie_p5,
   output logic                     o_dq0_dfi_rddata_ie_p6,
   output logic                     o_dq0_dfi_rddata_ie_p7,
   output logic                     o_dq0_dfi_rddata_re_p0,
   output logic                     o_dq0_dfi_rddata_re_p1,
   output logic                     o_dq0_dfi_rddata_re_p2,
   output logic                     o_dq0_dfi_rddata_re_p3,
   output logic                     o_dq0_dfi_rddata_re_p4,
   output logic                     o_dq0_dfi_rddata_re_p5,
   output logic                     o_dq0_dfi_rddata_re_p6,
   output logic                     o_dq0_dfi_rddata_re_p7,

   output logic                     o_dq0_dfi_rddata_cs_p0,
   output logic                     o_dq0_dfi_rddata_cs_p1,
   output logic                     o_dq0_dfi_rddata_cs_p2,
   output logic                     o_dq0_dfi_rddata_cs_p3,
   output logic                     o_dq0_dfi_rddata_cs_p4,
   output logic                     o_dq0_dfi_rddata_cs_p5,
   output logic                     o_dq0_dfi_rddata_cs_p6,
   output logic                     o_dq0_dfi_rddata_cs_p7,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_wrdata_p0,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_wrdata_p1,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_wrdata_p2,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_wrdata_p3,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_wrdata_p4,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_wrdata_p5,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_wrdata_p6,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_wrdata_p7,

   input  logic [MWIDTH-1:0]        i_dq1_dfi_wrdata_mask_p0,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_wrdata_mask_p1,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_wrdata_mask_p2,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_wrdata_mask_p3,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_wrdata_mask_p4,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_wrdata_mask_p5,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_wrdata_mask_p6,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_wrdata_mask_p7,

   output logic [SWIDTH-1:0]        o_dq1_dfi_wrdata_p0,
   output logic [SWIDTH-1:0]        o_dq1_dfi_wrdata_p1,
   output logic [SWIDTH-1:0]        o_dq1_dfi_wrdata_p2,
   output logic [SWIDTH-1:0]        o_dq1_dfi_wrdata_p3,
   output logic [SWIDTH-1:0]        o_dq1_dfi_wrdata_p4,
   output logic [SWIDTH-1:0]        o_dq1_dfi_wrdata_p5,
   output logic [SWIDTH-1:0]        o_dq1_dfi_wrdata_p6,
   output logic [SWIDTH-1:0]        o_dq1_dfi_wrdata_p7,
   output logic [MWIDTH-1:0]        o_dq1_dfi_wrdata_mask_p0,
   output logic [MWIDTH-1:0]        o_dq1_dfi_wrdata_mask_p1,
   output logic [MWIDTH-1:0]        o_dq1_dfi_wrdata_mask_p2,
   output logic [MWIDTH-1:0]        o_dq1_dfi_wrdata_mask_p3,
   output logic [MWIDTH-1:0]        o_dq1_dfi_wrdata_mask_p4,
   output logic [MWIDTH-1:0]        o_dq1_dfi_wrdata_mask_p5,
   output logic [MWIDTH-1:0]        o_dq1_dfi_wrdata_mask_p6,
   output logic [MWIDTH-1:0]        o_dq1_dfi_wrdata_mask_p7,

   // Wck/Write Enable Interafce
   input  logic                     i_dq1_dfi_wrdata_en_p0,
   input  logic                     i_dq1_dfi_wrdata_en_p1,
   input  logic                     i_dq1_dfi_wrdata_en_p2,
   input  logic                     i_dq1_dfi_wrdata_en_p3,
   input  logic                     i_dq1_dfi_wrdata_en_p4,
   input  logic                     i_dq1_dfi_wrdata_en_p5,
   input  logic                     i_dq1_dfi_wrdata_en_p6,
   input  logic                     i_dq1_dfi_wrdata_en_p7,
   input  logic                     i_dq1_dfi_parity_in_p0,
   input  logic                     i_dq1_dfi_parity_in_p1,
   input  logic                     i_dq1_dfi_parity_in_p2,
   input  logic                     i_dq1_dfi_parity_in_p3,
   input  logic                     i_dq1_dfi_parity_in_p4,
   input  logic                     i_dq1_dfi_parity_in_p5,
   input  logic                     i_dq1_dfi_parity_in_p6,
   input  logic                     i_dq1_dfi_parity_in_p7,
   input  logic                     i_dq1_dfi_wrdata_cs_p0,
   input  logic                     i_dq1_dfi_wrdata_cs_p1,
   input  logic                     i_dq1_dfi_wrdata_cs_p2,
   input  logic                     i_dq1_dfi_wrdata_cs_p3,
   input  logic                     i_dq1_dfi_wrdata_cs_p4,
   input  logic                     i_dq1_dfi_wrdata_cs_p5,
   input  logic                     i_dq1_dfi_wrdata_cs_p6,
   input  logic                     i_dq1_dfi_wrdata_cs_p7,

   input  logic                     i_dq1_dfi_wck_cs_p0,
   input  logic                     i_dq1_dfi_wck_cs_p1,
   input  logic                     i_dq1_dfi_wck_cs_p2,
   input  logic                     i_dq1_dfi_wck_cs_p3,
   input  logic                     i_dq1_dfi_wck_cs_p4,
   input  logic                     i_dq1_dfi_wck_cs_p5,
   input  logic                     i_dq1_dfi_wck_cs_p6,
   input  logic                     i_dq1_dfi_wck_cs_p7,
   input  logic                     i_dq1_dfi_wck_en_p0,
   input  logic                     i_dq1_dfi_wck_en_p1,
   input  logic                     i_dq1_dfi_wck_en_p2,
   input  logic                     i_dq1_dfi_wck_en_p3,
   input  logic                     i_dq1_dfi_wck_en_p4,
   input  logic                     i_dq1_dfi_wck_en_p5,
   input  logic                     i_dq1_dfi_wck_en_p6,
   input  logic                     i_dq1_dfi_wck_en_p7,
   input  logic [TWIDTH-1:0]        i_dq1_dfi_wck_toggle_p0,
   input  logic [TWIDTH-1:0]        i_dq1_dfi_wck_toggle_p1,
   input  logic [TWIDTH-1:0]        i_dq1_dfi_wck_toggle_p2,
   input  logic [TWIDTH-1:0]        i_dq1_dfi_wck_toggle_p3,
   input  logic [TWIDTH-1:0]        i_dq1_dfi_wck_toggle_p4,
   input  logic [TWIDTH-1:0]        i_dq1_dfi_wck_toggle_p5,
   input  logic [TWIDTH-1:0]        i_dq1_dfi_wck_toggle_p6,
   input  logic [TWIDTH-1:0]        i_dq1_dfi_wck_toggle_p7,
   output logic                     o_dq1_dfi_wrdata_en_p0,
   output logic                     o_dq1_dfi_wrdata_en_p1,
   output logic                     o_dq1_dfi_wrdata_en_p2,
   output logic                     o_dq1_dfi_wrdata_en_p3,
   output logic                     o_dq1_dfi_wrdata_en_p4,
   output logic                     o_dq1_dfi_wrdata_en_p5,
   output logic                     o_dq1_dfi_wrdata_en_p6,
   output logic                     o_dq1_dfi_wrdata_en_p7,
   output logic                     o_dq1_dfi_wrdata_oe_p0,
   output logic                     o_dq1_dfi_wrdata_oe_p1,
   output logic                     o_dq1_dfi_wrdata_oe_p2,
   output logic                     o_dq1_dfi_wrdata_oe_p3,
   output logic                     o_dq1_dfi_wrdata_oe_p4,
   output logic                     o_dq1_dfi_wrdata_oe_p5,
   output logic                     o_dq1_dfi_wrdata_oe_p6,
   output logic                     o_dq1_dfi_wrdata_oe_p7,
   output logic                     o_dq1_dfi_parity_in_p0,
   output logic                     o_dq1_dfi_parity_in_p1,
   output logic                     o_dq1_dfi_parity_in_p2,
   output logic                     o_dq1_dfi_parity_in_p3,
   output logic                     o_dq1_dfi_parity_in_p4,
   output logic                     o_dq1_dfi_parity_in_p5,
   output logic                     o_dq1_dfi_parity_in_p6,
   output logic                     o_dq1_dfi_parity_in_p7,
   output logic                     o_dq1_dfi_wrdata_cs_p0,
   output logic                     o_dq1_dfi_wrdata_cs_p1,
   output logic                     o_dq1_dfi_wrdata_cs_p2,
   output logic                     o_dq1_dfi_wrdata_cs_p3,
   output logic                     o_dq1_dfi_wrdata_cs_p4,
   output logic                     o_dq1_dfi_wrdata_cs_p5,
   output logic                     o_dq1_dfi_wrdata_cs_p6,
   output logic                     o_dq1_dfi_wrdata_cs_p7,
   output logic                     o_dq1_dfi_wck_en_p0,
   output logic                     o_dq1_dfi_wck_en_p1,
   output logic                     o_dq1_dfi_wck_en_p2,
   output logic                     o_dq1_dfi_wck_en_p3,
   output logic                     o_dq1_dfi_wck_en_p4,
   output logic                     o_dq1_dfi_wck_en_p5,
   output logic                     o_dq1_dfi_wck_en_p6,
   output logic                     o_dq1_dfi_wck_en_p7,
   output logic                     o_dq1_dfi_wck_oe_p0,
   output logic                     o_dq1_dfi_wck_oe_p1,
   output logic                     o_dq1_dfi_wck_oe_p2,
   output logic                     o_dq1_dfi_wck_oe_p3,
   output logic                     o_dq1_dfi_wck_oe_p4,
   output logic                     o_dq1_dfi_wck_oe_p5,
   output logic                     o_dq1_dfi_wck_oe_p6,
   output logic                     o_dq1_dfi_wck_oe_p7,
   output logic                     o_dq1_dfi_wck_ten_p0,
   output logic                     o_dq1_dfi_wck_ten_p1,
   output logic                     o_dq1_dfi_wck_ten_p2,
   output logic                     o_dq1_dfi_wck_ten_p3,
   output logic                     o_dq1_dfi_wck_ten_p4,
   output logic                     o_dq1_dfi_wck_ten_p5,
   output logic                     o_dq1_dfi_wck_ten_p6,
   output logic                     o_dq1_dfi_wck_ten_p7,
   output logic                     o_dq1_dfi_wck_cs_p0,
   output logic                     o_dq1_dfi_wck_cs_p1,
   output logic                     o_dq1_dfi_wck_cs_p2,
   output logic                     o_dq1_dfi_wck_cs_p3,
   output logic                     o_dq1_dfi_wck_cs_p4,
   output logic                     o_dq1_dfi_wck_cs_p5,
   output logic                     o_dq1_dfi_wck_cs_p6,
   output logic                     o_dq1_dfi_wck_cs_p7,

   input  logic                     i_dq1_dfi_rddata_en_p0,
   input  logic                     i_dq1_dfi_rddata_en_p1,
   input  logic                     i_dq1_dfi_rddata_en_p2,
   input  logic                     i_dq1_dfi_rddata_en_p3,
   input  logic                     i_dq1_dfi_rddata_en_p4,
   input  logic                     i_dq1_dfi_rddata_en_p5,
   input  logic                     i_dq1_dfi_rddata_en_p6,
   input  logic                     i_dq1_dfi_rddata_en_p7,

   input  logic                     i_dq1_dfi_rddata_cs_p0,
   input  logic                     i_dq1_dfi_rddata_cs_p1,
   input  logic                     i_dq1_dfi_rddata_cs_p2,
   input  logic                     i_dq1_dfi_rddata_cs_p3,
   input  logic                     i_dq1_dfi_rddata_cs_p4,
   input  logic                     i_dq1_dfi_rddata_cs_p5,
   input  logic                     i_dq1_dfi_rddata_cs_p6,
   input  logic                     i_dq1_dfi_rddata_cs_p7,

   output logic                     o_dq1_dfi_rddata_en_p0,
   output logic                     o_dq1_dfi_rddata_en_p1,
   output logic                     o_dq1_dfi_rddata_en_p2,
   output logic                     o_dq1_dfi_rddata_en_p3,
   output logic                     o_dq1_dfi_rddata_en_p4,
   output logic                     o_dq1_dfi_rddata_en_p5,
   output logic                     o_dq1_dfi_rddata_en_p6,
   output logic                     o_dq1_dfi_rddata_en_p7,
   output logic                     o_dq1_dfi_rddata_ie_p0,
   output logic                     o_dq1_dfi_rddata_ie_p1,
   output logic                     o_dq1_dfi_rddata_ie_p2,
   output logic                     o_dq1_dfi_rddata_ie_p3,
   output logic                     o_dq1_dfi_rddata_ie_p4,
   output logic                     o_dq1_dfi_rddata_ie_p5,
   output logic                     o_dq1_dfi_rddata_ie_p6,
   output logic                     o_dq1_dfi_rddata_ie_p7,
   output logic                     o_dq1_dfi_rddata_re_p0,
   output logic                     o_dq1_dfi_rddata_re_p1,
   output logic                     o_dq1_dfi_rddata_re_p2,
   output logic                     o_dq1_dfi_rddata_re_p3,
   output logic                     o_dq1_dfi_rddata_re_p4,
   output logic                     o_dq1_dfi_rddata_re_p5,
   output logic                     o_dq1_dfi_rddata_re_p6,
   output logic                     o_dq1_dfi_rddata_re_p7,

   output logic                     o_dq1_dfi_rddata_cs_p0,
   output logic                     o_dq1_dfi_rddata_cs_p1,
   output logic                     o_dq1_dfi_rddata_cs_p2,
   output logic                     o_dq1_dfi_rddata_cs_p3,
   output logic                     o_dq1_dfi_rddata_cs_p4,
   output logic                     o_dq1_dfi_rddata_cs_p5,
   output logic                     o_dq1_dfi_rddata_cs_p6,
   output logic                     o_dq1_dfi_rddata_cs_p7,

   // Read Data Interface
   input  logic [SWIDTH-1:0]        i_dq0_dfi_rddata_w0,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_rddata_w1,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_rddata_w2,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_rddata_w3,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_rddata_w4,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_rddata_w5,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_rddata_w6,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_rddata_w7,
   input  logic [MWIDTH-1:0]        i_dq0_dfi_rddata_dbi_w0,
   input  logic [MWIDTH-1:0]        i_dq0_dfi_rddata_dbi_w1,
   input  logic [MWIDTH-1:0]        i_dq0_dfi_rddata_dbi_w2,
   input  logic [MWIDTH-1:0]        i_dq0_dfi_rddata_dbi_w3,
   input  logic [MWIDTH-1:0]        i_dq0_dfi_rddata_dbi_w4,
   input  logic [MWIDTH-1:0]        i_dq0_dfi_rddata_dbi_w5,
   input  logic [MWIDTH-1:0]        i_dq0_dfi_rddata_dbi_w6,
   input  logic [MWIDTH-1:0]        i_dq0_dfi_rddata_dbi_w7,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_rddata_valid,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_rddata_w0,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_rddata_w1,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_rddata_w2,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_rddata_w3,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_rddata_w4,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_rddata_w5,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_rddata_w6,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_rddata_w7,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_rddata_dbi_w0,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_rddata_dbi_w1,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_rddata_dbi_w2,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_rddata_dbi_w3,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_rddata_dbi_w4,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_rddata_dbi_w5,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_rddata_dbi_w6,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_rddata_dbi_w7,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_rddata_valid,
   input  logic [NUM_DQ-1:0]        i_dq_dfi_rddata_valid_mask ,

   output logic [NUM_DQ*SWIDTH-1:0] o_dfi_rddata_w0,
   output logic [NUM_DQ*SWIDTH-1:0] o_dfi_rddata_w1,
   output logic [NUM_DQ*SWIDTH-1:0] o_dfi_rddata_w2,
   output logic [NUM_DQ*SWIDTH-1:0] o_dfi_rddata_w3,
   output logic [NUM_DQ*SWIDTH-1:0] o_dfi_rddata_w4,
   output logic [NUM_DQ*SWIDTH-1:0] o_dfi_rddata_w5,
   output logic [NUM_DQ*SWIDTH-1:0] o_dfi_rddata_w6,
   output logic [NUM_DQ*SWIDTH-1:0] o_dfi_rddata_w7,
   output logic [NUM_DQ*MWIDTH-1:0] o_dfi_rddata_dbi_w0,
   output logic [NUM_DQ*MWIDTH-1:0] o_dfi_rddata_dbi_w1,
   output logic [NUM_DQ*MWIDTH-1:0] o_dfi_rddata_dbi_w2,
   output logic [NUM_DQ*MWIDTH-1:0] o_dfi_rddata_dbi_w3,
   output logic [NUM_DQ*MWIDTH-1:0] o_dfi_rddata_dbi_w4,
   output logic [NUM_DQ*MWIDTH-1:0] o_dfi_rddata_dbi_w5,
   output logic [NUM_DQ*MWIDTH-1:0] o_dfi_rddata_dbi_w6,
   output logic [NUM_DQ*MWIDTH-1:0] o_dfi_rddata_dbi_w7,
   output logic                     o_dfi_rddata_valid_w0,
   output logic                     o_dfi_rddata_valid_w1,
   output logic                     o_dfi_rddata_valid_w2,
   output logic                     o_dfi_rddata_valid_w3,
   output logic                     o_dfi_rddata_valid_w4,
   output logic                     o_dfi_rddata_valid_w5,
   output logic                     o_dfi_rddata_valid_w6,
   output logic                     o_dfi_rddata_valid_w7,
   output logic [31:0]              o_dqwr_debug,
   output logic [31:0]              o_dqrd_debug

);

    assign o_dqwr_debug = {  //{(32-(4*`DDR_NUM_PHY_DATA_PHASES)){1'b0}},
                               o_dq0_dfi_wck_oe_p7   ,
                               o_dq0_dfi_wck_oe_p6   ,
                               o_dq0_dfi_wck_oe_p5   ,
                               o_dq0_dfi_wck_oe_p4   ,
                               o_dq0_dfi_wck_oe_p3   ,
                               o_dq0_dfi_wck_oe_p2   ,
                               o_dq0_dfi_wck_oe_p1   ,
                               o_dq0_dfi_wck_oe_p0   ,
                               o_dq0_dfi_wck_ten_p7  ,
                               o_dq0_dfi_wck_ten_p6  ,
                               o_dq0_dfi_wck_ten_p5  ,
                               o_dq0_dfi_wck_ten_p4  ,
                               o_dq0_dfi_wck_ten_p3  ,
                               o_dq0_dfi_wck_ten_p2  ,
                               o_dq0_dfi_wck_ten_p1  ,
                               o_dq0_dfi_wck_ten_p0  ,
                               o_dq0_dfi_wrdata_en_p7,
                               o_dq0_dfi_wrdata_en_p6,
                               o_dq0_dfi_wrdata_en_p5,
                               o_dq0_dfi_wrdata_en_p4,
                               o_dq0_dfi_wrdata_en_p3,
                               o_dq0_dfi_wrdata_en_p2,
                               o_dq0_dfi_wrdata_en_p1,
                               o_dq0_dfi_wrdata_en_p0,
                               o_dq0_dfi_wrdata_oe_p7,
                               o_dq0_dfi_wrdata_oe_p6,
                               o_dq0_dfi_wrdata_oe_p5,
                               o_dq0_dfi_wrdata_oe_p4,
                               o_dq0_dfi_wrdata_oe_p3,
                               o_dq0_dfi_wrdata_oe_p2,
                               o_dq0_dfi_wrdata_oe_p1,
                               o_dq0_dfi_wrdata_oe_p0
                          } ;
    assign o_dqrd_debug = {  {(32-(3*8)-2){1'b0}},
                               o_dq0_dfi_rddata_en_p7,
                               o_dq0_dfi_rddata_en_p6,
                               o_dq0_dfi_rddata_en_p5,
                               o_dq0_dfi_rddata_en_p4,
                               o_dq0_dfi_rddata_en_p3,
                               o_dq0_dfi_rddata_en_p2,
                               o_dq0_dfi_rddata_en_p1,
                               o_dq0_dfi_rddata_en_p0,
                               o_dq0_dfi_rddata_ie_p7,
                               o_dq0_dfi_rddata_ie_p6,
                               o_dq0_dfi_rddata_ie_p5,
                               o_dq0_dfi_rddata_ie_p4,
                               o_dq0_dfi_rddata_ie_p3,
                               o_dq0_dfi_rddata_ie_p2,
                               o_dq0_dfi_rddata_ie_p1,
                               o_dq0_dfi_rddata_ie_p0,
                               o_dq0_dfi_rddata_re_p7,
                               o_dq0_dfi_rddata_re_p6,
                               o_dq0_dfi_rddata_re_p5,
                               o_dq0_dfi_rddata_re_p4,
                               o_dq0_dfi_rddata_re_p3,
                               o_dq0_dfi_rddata_re_p2,
                               o_dq0_dfi_rddata_re_p1,
                               o_dq0_dfi_rddata_re_p0,
                               i_dq1_dfi_rddata_valid,
                               i_dq0_dfi_rddata_valid
                           };

   // ------------------------------------------------------------------------
   // DFI Write Interface
   // ------------------------------------------------------------------------

   ddr_dfi_write #(
      .FWIDTH                       (F0WIDTH),
      .SWIDTH                       (SWIDTH),
      .BWIDTH                       (BWIDTH),
      .MWIDTH                       (MWIDTH),
      .PWIDTH                       (PWIDTH),
      .NUM_WPH                      (NUM_WPH)
   ) u_dq0_dfi_write (
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_rst                        (i_rst),
      .i_clk_0                      (i_wrd_clk_0),
      .i_clk_1                      (i_wrd_clk_1),
      .i_clk_2                      (i_wrd_clk_2),

      .i_wrd_pipe_en                (i_dfi_wrd_cfg[`DDR_DFICH_WRD_M0_CFG_PIPE_EN_FIELD]),
      .i_wrd_gb_mode                (cast_dwgb_t(i_dfi_wrd_cfg[`DDR_DFICH_WRD_M0_CFG_GB_MODE_FIELD])),
      .i_wrd_post_gb_dly            (i_dfi_wrd_cfg[`DDR_DFICH_WRD_M0_CFG_POST_GB_FC_DLY_FIELD]),

      .i_dfi_wrdata_p0              (i_dq0_dfi_wrdata_p0),
      .i_dfi_wrdata_p1              (i_dq0_dfi_wrdata_p1),
      .i_dfi_wrdata_p2              (i_dq0_dfi_wrdata_p2),
      .i_dfi_wrdata_p3              (i_dq0_dfi_wrdata_p3),
      .i_dfi_wrdata_p4              (i_dq0_dfi_wrdata_p4),
      .i_dfi_wrdata_p5              (i_dq0_dfi_wrdata_p5),
      .i_dfi_wrdata_p6              (i_dq0_dfi_wrdata_p6),
      .i_dfi_wrdata_p7              (i_dq0_dfi_wrdata_p7),

      .i_dfi_wrdata_mask_p0         (i_dq0_dfi_wrdata_mask_p0),
      .i_dfi_wrdata_mask_p1         (i_dq0_dfi_wrdata_mask_p1),
      .i_dfi_wrdata_mask_p2         (i_dq0_dfi_wrdata_mask_p2),
      .i_dfi_wrdata_mask_p3         (i_dq0_dfi_wrdata_mask_p3),
      .i_dfi_wrdata_mask_p4         (i_dq0_dfi_wrdata_mask_p4),
      .i_dfi_wrdata_mask_p5         (i_dq0_dfi_wrdata_mask_p5),
      .i_dfi_wrdata_mask_p6         (i_dq0_dfi_wrdata_mask_p6),
      .i_dfi_wrdata_mask_p7         (i_dq0_dfi_wrdata_mask_p7),

      .o_dfi_wrdata_p0               (o_dq0_dfi_wrdata_p0),
      .o_dfi_wrdata_p1               (o_dq0_dfi_wrdata_p1),
      .o_dfi_wrdata_p2               (o_dq0_dfi_wrdata_p2),
      .o_dfi_wrdata_p3               (o_dq0_dfi_wrdata_p3),
      .o_dfi_wrdata_p4               (o_dq0_dfi_wrdata_p4),
      .o_dfi_wrdata_p5               (o_dq0_dfi_wrdata_p5),
      .o_dfi_wrdata_p6               (o_dq0_dfi_wrdata_p6),
      .o_dfi_wrdata_p7               (o_dq0_dfi_wrdata_p7),
      .o_dfi_wrdata_mask_p0          (o_dq0_dfi_wrdata_mask_p0),
      .o_dfi_wrdata_mask_p1          (o_dq0_dfi_wrdata_mask_p1),
      .o_dfi_wrdata_mask_p2          (o_dq0_dfi_wrdata_mask_p2),
      .o_dfi_wrdata_mask_p3          (o_dq0_dfi_wrdata_mask_p3),
      .o_dfi_wrdata_mask_p4          (o_dq0_dfi_wrdata_mask_p4),
      .o_dfi_wrdata_mask_p5          (o_dq0_dfi_wrdata_mask_p5),
      .o_dfi_wrdata_mask_p6          (o_dq0_dfi_wrdata_mask_p6),
      .o_dfi_wrdata_mask_p7          (o_dq0_dfi_wrdata_mask_p7),

      .o_debug                        (/*OPEN*/)
   );
   ddr_dfi_write #(
      .FWIDTH                       (F0WIDTH),
      .SWIDTH                       (SWIDTH),
      .BWIDTH                       (BWIDTH),
      .MWIDTH                       (MWIDTH),
      .PWIDTH                       (PWIDTH),
      .NUM_WPH                      (NUM_WPH)
   ) u_dq1_dfi_write (
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_rst                        (i_rst),
      .i_clk_0                      (i_wrd_clk_0),
      .i_clk_1                      (i_wrd_clk_1),
      .i_clk_2                      (i_wrd_clk_2),

      .i_wrd_pipe_en                (i_dfi_wrd_cfg[`DDR_DFICH_WRD_M0_CFG_PIPE_EN_FIELD]),
      .i_wrd_gb_mode                (cast_dwgb_t(i_dfi_wrd_cfg[`DDR_DFICH_WRD_M0_CFG_GB_MODE_FIELD])),
      .i_wrd_post_gb_dly            (i_dfi_wrd_cfg[`DDR_DFICH_WRD_M0_CFG_POST_GB_FC_DLY_FIELD]),

      .i_dfi_wrdata_p0              (i_dq1_dfi_wrdata_p0),
      .i_dfi_wrdata_p1              (i_dq1_dfi_wrdata_p1),
      .i_dfi_wrdata_p2              (i_dq1_dfi_wrdata_p2),
      .i_dfi_wrdata_p3              (i_dq1_dfi_wrdata_p3),
      .i_dfi_wrdata_p4              (i_dq1_dfi_wrdata_p4),
      .i_dfi_wrdata_p5              (i_dq1_dfi_wrdata_p5),
      .i_dfi_wrdata_p6              (i_dq1_dfi_wrdata_p6),
      .i_dfi_wrdata_p7              (i_dq1_dfi_wrdata_p7),

      .i_dfi_wrdata_mask_p0         (i_dq1_dfi_wrdata_mask_p0),
      .i_dfi_wrdata_mask_p1         (i_dq1_dfi_wrdata_mask_p1),
      .i_dfi_wrdata_mask_p2         (i_dq1_dfi_wrdata_mask_p2),
      .i_dfi_wrdata_mask_p3         (i_dq1_dfi_wrdata_mask_p3),
      .i_dfi_wrdata_mask_p4         (i_dq1_dfi_wrdata_mask_p4),
      .i_dfi_wrdata_mask_p5         (i_dq1_dfi_wrdata_mask_p5),
      .i_dfi_wrdata_mask_p6         (i_dq1_dfi_wrdata_mask_p6),
      .i_dfi_wrdata_mask_p7         (i_dq1_dfi_wrdata_mask_p7),

      .o_dfi_wrdata_p0               (o_dq1_dfi_wrdata_p0),
      .o_dfi_wrdata_p1               (o_dq1_dfi_wrdata_p1),
      .o_dfi_wrdata_p2               (o_dq1_dfi_wrdata_p2),
      .o_dfi_wrdata_p3               (o_dq1_dfi_wrdata_p3),
      .o_dfi_wrdata_p4               (o_dq1_dfi_wrdata_p4),
      .o_dfi_wrdata_p5               (o_dq1_dfi_wrdata_p5),
      .o_dfi_wrdata_p6               (o_dq1_dfi_wrdata_p6),
      .o_dfi_wrdata_p7               (o_dq1_dfi_wrdata_p7),
      .o_dfi_wrdata_mask_p0          (o_dq1_dfi_wrdata_mask_p0),
      .o_dfi_wrdata_mask_p1          (o_dq1_dfi_wrdata_mask_p1),
      .o_dfi_wrdata_mask_p2          (o_dq1_dfi_wrdata_mask_p2),
      .o_dfi_wrdata_mask_p3          (o_dq1_dfi_wrdata_mask_p3),
      .o_dfi_wrdata_mask_p4          (o_dq1_dfi_wrdata_mask_p4),
      .o_dfi_wrdata_mask_p5          (o_dq1_dfi_wrdata_mask_p5),
      .o_dfi_wrdata_mask_p6          (o_dq1_dfi_wrdata_mask_p6),
      .o_dfi_wrdata_mask_p7          (o_dq1_dfi_wrdata_mask_p7),

      .o_debug                        (/*OPEN*/)
   );

   // ------------------------------------------------------------------------
   // DFI Write Enable/(WCK) Interface
   // ------------------------------------------------------------------------

   ddr_dfi_write_en #(
      .SWIDTH                       (SWIDTH),
      .BWIDTH                       (BWIDTH),
      .TWIDTH                       (TWIDTH),
      .PWIDTH                       (PWIDTH),
      .NUM_WPH                      (NUM_WPH  ),
      .F0WIDTH                      (F0WIDTH),
      .F1WIDTH                      (F1WIDTH),
      .F2WIDTH                      (F2WIDTH),
      .MAXF2DLY                     (MAXF2DLY)
   ) u_dq0_dfi_write_en (
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_rst                        (i_rst),

      .i_clk_0                      (i_wrc_clk_0),
      .i_clk_1                      (i_wrc_clk_1),
      .i_clk_2                      (i_wrc_clk_2),

      .i_wck_mode                   (i_dfi_top_1_cfg[`DDR_DFICH_TOP_1_CFG_WCK_MODE_FIELD]),
      .i_wctrl_pipe_en              (i_dfi_wctrl_cfg[`DDR_DFICH_WCTRL_M0_CFG_PIPE_EN_FIELD]),
      .i_wctrl_gb_mode              (cast_dwgb_t(i_dfi_wctrl_cfg[`DDR_DFICH_WCTRL_M0_CFG_GB_MODE_FIELD])),
      .i_wctrl_post_gb_dly          (i_dfi_wctrl_cfg[`DDR_DFICH_WCTRL_M0_CFG_POST_GB_FC_DLY_FIELD]),
      .i_wenctrl_pipe_en            (i_dfi_wenctrl_cfg[`DDR_DFICH_WENCTRL_M0_CFG_PIPE_EN_FIELD]),
      .i_wenctrl_gb_mode            (cast_dwgb_t(i_dfi_wenctrl_cfg[`DDR_DFICH_WENCTRL_M0_CFG_GB_MODE_FIELD])),
      .i_wenctrl_post_gb_dly        (i_dfi_wenctrl_cfg[`DDR_DFICH_WENCTRL_M0_CFG_POST_GB_FC_DLY_FIELD]),
      .i_wckctrl_pipe_en            (i_dfi_wckctrl_cfg[`DDR_DFICH_WCKCTRL_M0_CFG_PIPE_EN_FIELD]),
      .i_wckctrl_gb_mode            (cast_dwgb_t(i_dfi_wckctrl_cfg[`DDR_DFICH_WCKCTRL_M0_CFG_GB_MODE_FIELD])),
      .i_wckctrl_post_gb_dly        (i_dfi_wckctrl_cfg[`DDR_DFICH_WCKCTRL_M0_CFG_POST_GB_FC_DLY_FIELD]),
      .i_wrd_pipe_en                (i_dfi_wrd_cfg[`DDR_DFICH_WRD_M0_CFG_PIPE_EN_FIELD]),
      .i_wrd_gb_mode                (cast_dwgb_t(i_dfi_wrd_cfg[`DDR_DFICH_WRD_M0_CFG_GB_MODE_FIELD])),
      .i_wrd_post_gb_dly            (i_dfi_wrd_cfg[`DDR_DFICH_WRD_M0_CFG_POST_GB_FC_DLY_FIELD]),

      .i_wrden_phase_ext            (i_dfi_ctrl3_cfg[`DDR_DFICH_CTRL3_M0_CFG_WRD_EN_PHASE_EXT_FIELD]),
      .i_wrdoe_phase_ext            (i_dfi_ctrl3_cfg[`DDR_DFICH_CTRL3_M0_CFG_WRD_OE_PHASE_EXT_FIELD]),
      .i_wrdcs_phase_ext            (i_dfi_ctrl3_cfg[`DDR_DFICH_CTRL3_M0_CFG_WRD_CS_PHASE_EXT_FIELD]),
      .i_wckoe_phase_ext            (i_dfi_ctrl4_cfg[`DDR_DFICH_CTRL4_M0_CFG_WCK_OE_PHASE_EXT_FIELD]),
      .i_wckcs_phase_ext            (i_dfi_ctrl4_cfg[`DDR_DFICH_CTRL4_M0_CFG_WCK_CS_PHASE_EXT_FIELD]),

      .i_dfi_wrdata_en_p0           (i_dq0_dfi_wrdata_en_p0),
      .i_dfi_wrdata_en_p1           (i_dq0_dfi_wrdata_en_p1),
      .i_dfi_wrdata_en_p2           (i_dq0_dfi_wrdata_en_p2),
      .i_dfi_wrdata_en_p3           (i_dq0_dfi_wrdata_en_p3),
      .i_dfi_wrdata_en_p4           (i_dq0_dfi_wrdata_en_p4),
      .i_dfi_wrdata_en_p5           (i_dq0_dfi_wrdata_en_p5),
      .i_dfi_wrdata_en_p6           (i_dq0_dfi_wrdata_en_p6),
      .i_dfi_wrdata_en_p7           (i_dq0_dfi_wrdata_en_p7),
      .i_dfi_parity_in_p0           (i_dq0_dfi_parity_in_p0),
      .i_dfi_parity_in_p1           (i_dq0_dfi_parity_in_p1),
      .i_dfi_parity_in_p2           (i_dq0_dfi_parity_in_p2),
      .i_dfi_parity_in_p3           (i_dq0_dfi_parity_in_p3),
      .i_dfi_parity_in_p4           (i_dq0_dfi_parity_in_p4),
      .i_dfi_parity_in_p5           (i_dq0_dfi_parity_in_p5),
      .i_dfi_parity_in_p6           (i_dq0_dfi_parity_in_p6),
      .i_dfi_parity_in_p7           (i_dq0_dfi_parity_in_p7),
      .i_dfi_wrdata_cs_p0           (i_dq0_dfi_wrdata_cs_p0),
      .i_dfi_wrdata_cs_p1           (i_dq0_dfi_wrdata_cs_p1),
      .i_dfi_wrdata_cs_p2           (i_dq0_dfi_wrdata_cs_p2),
      .i_dfi_wrdata_cs_p3           (i_dq0_dfi_wrdata_cs_p3),
      .i_dfi_wrdata_cs_p4           (i_dq0_dfi_wrdata_cs_p4),
      .i_dfi_wrdata_cs_p5           (i_dq0_dfi_wrdata_cs_p5),
      .i_dfi_wrdata_cs_p6           (i_dq0_dfi_wrdata_cs_p6),
      .i_dfi_wrdata_cs_p7           (i_dq0_dfi_wrdata_cs_p7),
      .i_dfi_wck_en_p0              (i_dq0_dfi_wck_en_p0),
      .i_dfi_wck_en_p1              (i_dq0_dfi_wck_en_p1),
      .i_dfi_wck_en_p2              (i_dq0_dfi_wck_en_p2),
      .i_dfi_wck_en_p3              (i_dq0_dfi_wck_en_p3),
      .i_dfi_wck_en_p4              (i_dq0_dfi_wck_en_p4),
      .i_dfi_wck_en_p5              (i_dq0_dfi_wck_en_p5),
      .i_dfi_wck_en_p6              (i_dq0_dfi_wck_en_p6),
      .i_dfi_wck_en_p7              (i_dq0_dfi_wck_en_p7),
      .i_dfi_wck_cs_p0              (i_dq0_dfi_wck_cs_p0),
      .i_dfi_wck_cs_p1              (i_dq0_dfi_wck_cs_p1),
      .i_dfi_wck_cs_p2              (i_dq0_dfi_wck_cs_p2),
      .i_dfi_wck_cs_p3              (i_dq0_dfi_wck_cs_p3),
      .i_dfi_wck_cs_p4              (i_dq0_dfi_wck_cs_p4),
      .i_dfi_wck_cs_p5              (i_dq0_dfi_wck_cs_p5),
      .i_dfi_wck_cs_p6              (i_dq0_dfi_wck_cs_p6),
      .i_dfi_wck_cs_p7              (i_dq0_dfi_wck_cs_p7),
      .i_dfi_wck_toggle_p0          (i_dq0_dfi_wck_toggle_p0),
      .i_dfi_wck_toggle_p1          (i_dq0_dfi_wck_toggle_p1),
      .i_dfi_wck_toggle_p2          (i_dq0_dfi_wck_toggle_p2),
      .i_dfi_wck_toggle_p3          (i_dq0_dfi_wck_toggle_p3),
      .i_dfi_wck_toggle_p4          (i_dq0_dfi_wck_toggle_p4),
      .i_dfi_wck_toggle_p5          (i_dq0_dfi_wck_toggle_p5),
      .i_dfi_wck_toggle_p6          (i_dq0_dfi_wck_toggle_p6),
      .i_dfi_wck_toggle_p7          (i_dq0_dfi_wck_toggle_p7),

      .o_dfi_wrdata_en_p0           (o_dq0_dfi_wrdata_en_p0),
      .o_dfi_wrdata_en_p1           (o_dq0_dfi_wrdata_en_p1),
      .o_dfi_wrdata_en_p2           (o_dq0_dfi_wrdata_en_p2),
      .o_dfi_wrdata_en_p3           (o_dq0_dfi_wrdata_en_p3),
      .o_dfi_wrdata_en_p4           (o_dq0_dfi_wrdata_en_p4),
      .o_dfi_wrdata_en_p5           (o_dq0_dfi_wrdata_en_p5),
      .o_dfi_wrdata_en_p6           (o_dq0_dfi_wrdata_en_p6),
      .o_dfi_wrdata_en_p7           (o_dq0_dfi_wrdata_en_p7),
      .o_dfi_wrdata_oe_p0           (o_dq0_dfi_wrdata_oe_p0),
      .o_dfi_wrdata_oe_p1           (o_dq0_dfi_wrdata_oe_p1),
      .o_dfi_wrdata_oe_p2           (o_dq0_dfi_wrdata_oe_p2),
      .o_dfi_wrdata_oe_p3           (o_dq0_dfi_wrdata_oe_p3),
      .o_dfi_wrdata_oe_p4           (o_dq0_dfi_wrdata_oe_p4),
      .o_dfi_wrdata_oe_p5           (o_dq0_dfi_wrdata_oe_p5),
      .o_dfi_wrdata_oe_p6           (o_dq0_dfi_wrdata_oe_p6),
      .o_dfi_wrdata_oe_p7           (o_dq0_dfi_wrdata_oe_p7),
      .o_dfi_parity_in_p0           (o_dq0_dfi_parity_in_p0),
      .o_dfi_parity_in_p1           (o_dq0_dfi_parity_in_p1),
      .o_dfi_parity_in_p2           (o_dq0_dfi_parity_in_p2),
      .o_dfi_parity_in_p3           (o_dq0_dfi_parity_in_p3),
      .o_dfi_parity_in_p4           (o_dq0_dfi_parity_in_p4),
      .o_dfi_parity_in_p5           (o_dq0_dfi_parity_in_p5),
      .o_dfi_parity_in_p6           (o_dq0_dfi_parity_in_p6),
      .o_dfi_parity_in_p7           (o_dq0_dfi_parity_in_p7),
      .o_dfi_wrdata_cs_p0           (o_dq0_dfi_wrdata_cs_p0),
      .o_dfi_wrdata_cs_p1           (o_dq0_dfi_wrdata_cs_p1),
      .o_dfi_wrdata_cs_p2           (o_dq0_dfi_wrdata_cs_p2),
      .o_dfi_wrdata_cs_p3           (o_dq0_dfi_wrdata_cs_p3),
      .o_dfi_wrdata_cs_p4           (o_dq0_dfi_wrdata_cs_p4),
      .o_dfi_wrdata_cs_p5           (o_dq0_dfi_wrdata_cs_p5),
      .o_dfi_wrdata_cs_p6           (o_dq0_dfi_wrdata_cs_p6),
      .o_dfi_wrdata_cs_p7           (o_dq0_dfi_wrdata_cs_p7),
      .o_dfi_wck_en_p0              (o_dq0_dfi_wck_en_p0),
      .o_dfi_wck_en_p1              (o_dq0_dfi_wck_en_p1),
      .o_dfi_wck_en_p2              (o_dq0_dfi_wck_en_p2),
      .o_dfi_wck_en_p3              (o_dq0_dfi_wck_en_p3),
      .o_dfi_wck_en_p4              (o_dq0_dfi_wck_en_p4),
      .o_dfi_wck_en_p5              (o_dq0_dfi_wck_en_p5),
      .o_dfi_wck_en_p6              (o_dq0_dfi_wck_en_p6),
      .o_dfi_wck_en_p7              (o_dq0_dfi_wck_en_p7),
      .o_dfi_wck_oe_p0              (o_dq0_dfi_wck_oe_p0),
      .o_dfi_wck_oe_p1              (o_dq0_dfi_wck_oe_p1),
      .o_dfi_wck_oe_p2              (o_dq0_dfi_wck_oe_p2),
      .o_dfi_wck_oe_p3              (o_dq0_dfi_wck_oe_p3),
      .o_dfi_wck_oe_p4              (o_dq0_dfi_wck_oe_p4),
      .o_dfi_wck_oe_p5              (o_dq0_dfi_wck_oe_p5),
      .o_dfi_wck_oe_p6              (o_dq0_dfi_wck_oe_p6),
      .o_dfi_wck_oe_p7              (o_dq0_dfi_wck_oe_p7),
      .o_dfi_wck_cs_p0              (o_dq0_dfi_wck_cs_p0),
      .o_dfi_wck_cs_p1              (o_dq0_dfi_wck_cs_p1),
      .o_dfi_wck_cs_p2              (o_dq0_dfi_wck_cs_p2),
      .o_dfi_wck_cs_p3              (o_dq0_dfi_wck_cs_p3),
      .o_dfi_wck_cs_p4              (o_dq0_dfi_wck_cs_p4),
      .o_dfi_wck_cs_p5              (o_dq0_dfi_wck_cs_p5),
      .o_dfi_wck_cs_p6              (o_dq0_dfi_wck_cs_p6),
      .o_dfi_wck_cs_p7              (o_dq0_dfi_wck_cs_p7),
      .o_dfi_wck_ten_p0             (o_dq0_dfi_wck_ten_p0),
      .o_dfi_wck_ten_p1             (o_dq0_dfi_wck_ten_p1),
      .o_dfi_wck_ten_p2             (o_dq0_dfi_wck_ten_p2),
      .o_dfi_wck_ten_p3             (o_dq0_dfi_wck_ten_p3),
      .o_dfi_wck_ten_p4             (o_dq0_dfi_wck_ten_p4),
      .o_dfi_wck_ten_p5             (o_dq0_dfi_wck_ten_p5),
      .o_dfi_wck_ten_p6             (o_dq0_dfi_wck_ten_p6),
      .o_dfi_wck_ten_p7             (o_dq0_dfi_wck_ten_p7),
      .o_debug                      (/*OPEN*/)
   );
   ddr_dfi_write_en #(
      .SWIDTH                       (SWIDTH),
      .BWIDTH                       (BWIDTH),
      .TWIDTH                       (TWIDTH),
      .PWIDTH                       (PWIDTH),
      .NUM_WPH                      (NUM_WPH  ),
      .F0WIDTH                      (F0WIDTH),
      .F1WIDTH                      (F1WIDTH),
      .F2WIDTH                      (F2WIDTH),
      .MAXF2DLY                     (MAXF2DLY)
   ) u_dq1_dfi_write_en (
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_rst                        (i_rst),

      .i_clk_0                      (i_wrc_clk_0),
      .i_clk_1                      (i_wrc_clk_1),
      .i_clk_2                      (i_wrc_clk_2),

      .i_wck_mode                   (i_dfi_top_1_cfg[`DDR_DFICH_TOP_1_CFG_WCK_MODE_FIELD]),
      .i_wctrl_pipe_en              (i_dfi_wctrl_cfg[`DDR_DFICH_WCTRL_M0_CFG_PIPE_EN_FIELD]),
      .i_wctrl_gb_mode              (cast_dwgb_t(i_dfi_wctrl_cfg[`DDR_DFICH_WCTRL_M0_CFG_GB_MODE_FIELD])),
      .i_wctrl_post_gb_dly          (i_dfi_wctrl_cfg[`DDR_DFICH_WCTRL_M0_CFG_POST_GB_FC_DLY_FIELD]),
      .i_wenctrl_pipe_en            (i_dfi_wenctrl_cfg[`DDR_DFICH_WENCTRL_M0_CFG_PIPE_EN_FIELD]),
      .i_wenctrl_gb_mode            (cast_dwgb_t(i_dfi_wenctrl_cfg[`DDR_DFICH_WENCTRL_M0_CFG_GB_MODE_FIELD])),
      .i_wenctrl_post_gb_dly        (i_dfi_wenctrl_cfg[`DDR_DFICH_WENCTRL_M0_CFG_POST_GB_FC_DLY_FIELD]),
      .i_wckctrl_pipe_en            (i_dfi_wckctrl_cfg[`DDR_DFICH_WCKCTRL_M0_CFG_PIPE_EN_FIELD]),
      .i_wckctrl_gb_mode            (cast_dwgb_t(i_dfi_wckctrl_cfg[`DDR_DFICH_WCKCTRL_M0_CFG_GB_MODE_FIELD])),
      .i_wckctrl_post_gb_dly        (i_dfi_wckctrl_cfg[`DDR_DFICH_WCKCTRL_M0_CFG_POST_GB_FC_DLY_FIELD]),
      .i_wrd_pipe_en                (i_dfi_wrd_cfg[`DDR_DFICH_WRD_M0_CFG_PIPE_EN_FIELD]),
      .i_wrd_gb_mode                (cast_dwgb_t(i_dfi_wrd_cfg[`DDR_DFICH_WRD_M0_CFG_GB_MODE_FIELD])),
      .i_wrd_post_gb_dly            (i_dfi_wrd_cfg[`DDR_DFICH_WRD_M0_CFG_POST_GB_FC_DLY_FIELD]),

      .i_wrden_phase_ext            (i_dfi_ctrl3_cfg[`DDR_DFICH_CTRL3_M0_CFG_WRD_EN_PHASE_EXT_FIELD]),
      .i_wrdoe_phase_ext            (i_dfi_ctrl3_cfg[`DDR_DFICH_CTRL3_M0_CFG_WRD_OE_PHASE_EXT_FIELD]),
      .i_wrdcs_phase_ext            (i_dfi_ctrl3_cfg[`DDR_DFICH_CTRL3_M0_CFG_WRD_CS_PHASE_EXT_FIELD]),
      .i_wckoe_phase_ext            (i_dfi_ctrl4_cfg[`DDR_DFICH_CTRL4_M0_CFG_WCK_OE_PHASE_EXT_FIELD]),
      .i_wckcs_phase_ext            (i_dfi_ctrl4_cfg[`DDR_DFICH_CTRL4_M0_CFG_WCK_CS_PHASE_EXT_FIELD]),

      .i_dfi_wrdata_en_p0           (i_dq1_dfi_wrdata_en_p0),
      .i_dfi_wrdata_en_p1           (i_dq1_dfi_wrdata_en_p1),
      .i_dfi_wrdata_en_p2           (i_dq1_dfi_wrdata_en_p2),
      .i_dfi_wrdata_en_p3           (i_dq1_dfi_wrdata_en_p3),
      .i_dfi_wrdata_en_p4           (i_dq1_dfi_wrdata_en_p4),
      .i_dfi_wrdata_en_p5           (i_dq1_dfi_wrdata_en_p5),
      .i_dfi_wrdata_en_p6           (i_dq1_dfi_wrdata_en_p6),
      .i_dfi_wrdata_en_p7           (i_dq1_dfi_wrdata_en_p7),
      .i_dfi_parity_in_p0           (i_dq1_dfi_parity_in_p0),
      .i_dfi_parity_in_p1           (i_dq1_dfi_parity_in_p1),
      .i_dfi_parity_in_p2           (i_dq1_dfi_parity_in_p2),
      .i_dfi_parity_in_p3           (i_dq1_dfi_parity_in_p3),
      .i_dfi_parity_in_p4           (i_dq1_dfi_parity_in_p4),
      .i_dfi_parity_in_p5           (i_dq1_dfi_parity_in_p5),
      .i_dfi_parity_in_p6           (i_dq1_dfi_parity_in_p6),
      .i_dfi_parity_in_p7           (i_dq1_dfi_parity_in_p7),
      .i_dfi_wrdata_cs_p0           (i_dq1_dfi_wrdata_cs_p0),
      .i_dfi_wrdata_cs_p1           (i_dq1_dfi_wrdata_cs_p1),
      .i_dfi_wrdata_cs_p2           (i_dq1_dfi_wrdata_cs_p2),
      .i_dfi_wrdata_cs_p3           (i_dq1_dfi_wrdata_cs_p3),
      .i_dfi_wrdata_cs_p4           (i_dq1_dfi_wrdata_cs_p4),
      .i_dfi_wrdata_cs_p5           (i_dq1_dfi_wrdata_cs_p5),
      .i_dfi_wrdata_cs_p6           (i_dq1_dfi_wrdata_cs_p6),
      .i_dfi_wrdata_cs_p7           (i_dq1_dfi_wrdata_cs_p7),
      .i_dfi_wck_en_p0              (i_dq1_dfi_wck_en_p0),
      .i_dfi_wck_en_p1              (i_dq1_dfi_wck_en_p1),
      .i_dfi_wck_en_p2              (i_dq1_dfi_wck_en_p2),
      .i_dfi_wck_en_p3              (i_dq1_dfi_wck_en_p3),
      .i_dfi_wck_en_p4              (i_dq1_dfi_wck_en_p4),
      .i_dfi_wck_en_p5              (i_dq1_dfi_wck_en_p5),
      .i_dfi_wck_en_p6              (i_dq1_dfi_wck_en_p6),
      .i_dfi_wck_en_p7              (i_dq1_dfi_wck_en_p7),
      .i_dfi_wck_cs_p0              (i_dq1_dfi_wck_cs_p0),
      .i_dfi_wck_cs_p1              (i_dq1_dfi_wck_cs_p1),
      .i_dfi_wck_cs_p2              (i_dq1_dfi_wck_cs_p2),
      .i_dfi_wck_cs_p3              (i_dq1_dfi_wck_cs_p3),
      .i_dfi_wck_cs_p4              (i_dq1_dfi_wck_cs_p4),
      .i_dfi_wck_cs_p5              (i_dq1_dfi_wck_cs_p5),
      .i_dfi_wck_cs_p6              (i_dq1_dfi_wck_cs_p6),
      .i_dfi_wck_cs_p7              (i_dq1_dfi_wck_cs_p7),
      .i_dfi_wck_toggle_p0          (i_dq1_dfi_wck_toggle_p0),
      .i_dfi_wck_toggle_p1          (i_dq1_dfi_wck_toggle_p1),
      .i_dfi_wck_toggle_p2          (i_dq1_dfi_wck_toggle_p2),
      .i_dfi_wck_toggle_p3          (i_dq1_dfi_wck_toggle_p3),
      .i_dfi_wck_toggle_p4          (i_dq1_dfi_wck_toggle_p4),
      .i_dfi_wck_toggle_p5          (i_dq1_dfi_wck_toggle_p5),
      .i_dfi_wck_toggle_p6          (i_dq1_dfi_wck_toggle_p6),
      .i_dfi_wck_toggle_p7          (i_dq1_dfi_wck_toggle_p7),

      .o_dfi_wrdata_en_p0           (o_dq1_dfi_wrdata_en_p0),
      .o_dfi_wrdata_en_p1           (o_dq1_dfi_wrdata_en_p1),
      .o_dfi_wrdata_en_p2           (o_dq1_dfi_wrdata_en_p2),
      .o_dfi_wrdata_en_p3           (o_dq1_dfi_wrdata_en_p3),
      .o_dfi_wrdata_en_p4           (o_dq1_dfi_wrdata_en_p4),
      .o_dfi_wrdata_en_p5           (o_dq1_dfi_wrdata_en_p5),
      .o_dfi_wrdata_en_p6           (o_dq1_dfi_wrdata_en_p6),
      .o_dfi_wrdata_en_p7           (o_dq1_dfi_wrdata_en_p7),
      .o_dfi_wrdata_oe_p0           (o_dq1_dfi_wrdata_oe_p0),
      .o_dfi_wrdata_oe_p1           (o_dq1_dfi_wrdata_oe_p1),
      .o_dfi_wrdata_oe_p2           (o_dq1_dfi_wrdata_oe_p2),
      .o_dfi_wrdata_oe_p3           (o_dq1_dfi_wrdata_oe_p3),
      .o_dfi_wrdata_oe_p4           (o_dq1_dfi_wrdata_oe_p4),
      .o_dfi_wrdata_oe_p5           (o_dq1_dfi_wrdata_oe_p5),
      .o_dfi_wrdata_oe_p6           (o_dq1_dfi_wrdata_oe_p6),
      .o_dfi_wrdata_oe_p7           (o_dq1_dfi_wrdata_oe_p7),
      .o_dfi_parity_in_p0           (o_dq1_dfi_parity_in_p0),
      .o_dfi_parity_in_p1           (o_dq1_dfi_parity_in_p1),
      .o_dfi_parity_in_p2           (o_dq1_dfi_parity_in_p2),
      .o_dfi_parity_in_p3           (o_dq1_dfi_parity_in_p3),
      .o_dfi_parity_in_p4           (o_dq1_dfi_parity_in_p4),
      .o_dfi_parity_in_p5           (o_dq1_dfi_parity_in_p5),
      .o_dfi_parity_in_p6           (o_dq1_dfi_parity_in_p6),
      .o_dfi_parity_in_p7           (o_dq1_dfi_parity_in_p7),
      .o_dfi_wrdata_cs_p0           (o_dq1_dfi_wrdata_cs_p0),
      .o_dfi_wrdata_cs_p1           (o_dq1_dfi_wrdata_cs_p1),
      .o_dfi_wrdata_cs_p2           (o_dq1_dfi_wrdata_cs_p2),
      .o_dfi_wrdata_cs_p3           (o_dq1_dfi_wrdata_cs_p3),
      .o_dfi_wrdata_cs_p4           (o_dq1_dfi_wrdata_cs_p4),
      .o_dfi_wrdata_cs_p5           (o_dq1_dfi_wrdata_cs_p5),
      .o_dfi_wrdata_cs_p6           (o_dq1_dfi_wrdata_cs_p6),
      .o_dfi_wrdata_cs_p7           (o_dq1_dfi_wrdata_cs_p7),
      .o_dfi_wck_en_p0              (o_dq1_dfi_wck_en_p0),
      .o_dfi_wck_en_p1              (o_dq1_dfi_wck_en_p1),
      .o_dfi_wck_en_p2              (o_dq1_dfi_wck_en_p2),
      .o_dfi_wck_en_p3              (o_dq1_dfi_wck_en_p3),
      .o_dfi_wck_en_p4              (o_dq1_dfi_wck_en_p4),
      .o_dfi_wck_en_p5              (o_dq1_dfi_wck_en_p5),
      .o_dfi_wck_en_p6              (o_dq1_dfi_wck_en_p6),
      .o_dfi_wck_en_p7              (o_dq1_dfi_wck_en_p7),
      .o_dfi_wck_oe_p0              (o_dq1_dfi_wck_oe_p0),
      .o_dfi_wck_oe_p1              (o_dq1_dfi_wck_oe_p1),
      .o_dfi_wck_oe_p2              (o_dq1_dfi_wck_oe_p2),
      .o_dfi_wck_oe_p3              (o_dq1_dfi_wck_oe_p3),
      .o_dfi_wck_oe_p4              (o_dq1_dfi_wck_oe_p4),
      .o_dfi_wck_oe_p5              (o_dq1_dfi_wck_oe_p5),
      .o_dfi_wck_oe_p6              (o_dq1_dfi_wck_oe_p6),
      .o_dfi_wck_oe_p7              (o_dq1_dfi_wck_oe_p7),
      .o_dfi_wck_cs_p0              (o_dq1_dfi_wck_cs_p0),
      .o_dfi_wck_cs_p1              (o_dq1_dfi_wck_cs_p1),
      .o_dfi_wck_cs_p2              (o_dq1_dfi_wck_cs_p2),
      .o_dfi_wck_cs_p3              (o_dq1_dfi_wck_cs_p3),
      .o_dfi_wck_cs_p4              (o_dq1_dfi_wck_cs_p4),
      .o_dfi_wck_cs_p5              (o_dq1_dfi_wck_cs_p5),
      .o_dfi_wck_cs_p6              (o_dq1_dfi_wck_cs_p6),
      .o_dfi_wck_cs_p7              (o_dq1_dfi_wck_cs_p7),
      .o_dfi_wck_ten_p0             (o_dq1_dfi_wck_ten_p0),
      .o_dfi_wck_ten_p1             (o_dq1_dfi_wck_ten_p1),
      .o_dfi_wck_ten_p2             (o_dq1_dfi_wck_ten_p2),
      .o_dfi_wck_ten_p3             (o_dq1_dfi_wck_ten_p3),
      .o_dfi_wck_ten_p4             (o_dq1_dfi_wck_ten_p4),
      .o_dfi_wck_ten_p5             (o_dq1_dfi_wck_ten_p5),
      .o_dfi_wck_ten_p6             (o_dq1_dfi_wck_ten_p6),
      .o_dfi_wck_ten_p7             (o_dq1_dfi_wck_ten_p7),
      .o_debug                      (/*OPEN*/)
   );

   // ------------------------------------------------------------------------
   // DFI Read Enable Interface
   // ------------------------------------------------------------------------

   ddr_dfi_read_en #(
      .PWIDTH                       (PWIDTH),
      .NUM_WPH                      (NUM_WPH),
      .FWIDTH                       (F1WIDTH)
   ) u_dq0_dfi_read_en (
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_rst                        (i_rst),

      .i_clk_0                      (i_wrc_clk_0),
      .i_clk_1                      (i_wrc_clk_1),
      .i_clk_2                      (i_wrc_clk_2),

      .i_rctrl_pipe_en              (i_dfi_rctrl_cfg[`DDR_DFICH_RCTRL_M0_CFG_PIPE_EN_FIELD]),
      .i_rctrl_gb_mode              (cast_dwgb_t(i_dfi_rctrl_cfg[`DDR_DFICH_RCTRL_M0_CFG_GB_MODE_FIELD])),
      .i_rctrl_post_gb_dly          (i_dfi_rctrl_cfg[`DDR_DFICH_RCTRL_M0_CFG_POST_GB_FC_DLY_FIELD]),

      .i_rcs_phase_ext              (i_dfi_ctrl5_cfg[`DDR_DFICH_CTRL5_M0_CFG_RCS_PHASE_EXT_FIELD]),
      .i_ren_phase_ext              (i_dfi_ctrl5_cfg[`DDR_DFICH_CTRL5_M0_CFG_REN_PHASE_EXT_FIELD]),
      .i_ie_phase_ext               (i_dfi_ctrl5_cfg[`DDR_DFICH_CTRL5_M0_CFG_IE_PHASE_EXT_FIELD]),
      .i_re_phase_ext               (i_dfi_ctrl5_cfg[`DDR_DFICH_CTRL5_M0_CFG_RE_PHASE_EXT_FIELD]),

      .i_dfi_rddata_en_p0          (i_dq0_dfi_rddata_en_p0),
      .i_dfi_rddata_en_p1          (i_dq0_dfi_rddata_en_p1),
      .i_dfi_rddata_en_p2          (i_dq0_dfi_rddata_en_p2),
      .i_dfi_rddata_en_p3          (i_dq0_dfi_rddata_en_p3),
      .i_dfi_rddata_en_p4          (i_dq0_dfi_rddata_en_p4),
      .i_dfi_rddata_en_p5          (i_dq0_dfi_rddata_en_p5),
      .i_dfi_rddata_en_p6          (i_dq0_dfi_rddata_en_p6),
      .i_dfi_rddata_en_p7          (i_dq0_dfi_rddata_en_p7),

      .i_dfi_rddata_cs_p0          (i_dq0_dfi_rddata_cs_p0),
      .i_dfi_rddata_cs_p1          (i_dq0_dfi_rddata_cs_p1),
      .i_dfi_rddata_cs_p2          (i_dq0_dfi_rddata_cs_p2),
      .i_dfi_rddata_cs_p3          (i_dq0_dfi_rddata_cs_p3),
      .i_dfi_rddata_cs_p4          (i_dq0_dfi_rddata_cs_p4),
      .i_dfi_rddata_cs_p5          (i_dq0_dfi_rddata_cs_p5),
      .i_dfi_rddata_cs_p6          (i_dq0_dfi_rddata_cs_p6),
      .i_dfi_rddata_cs_p7          (i_dq0_dfi_rddata_cs_p7),

      .o_dfi_rddata_en_p0          (o_dq0_dfi_rddata_en_p0),
      .o_dfi_rddata_en_p1          (o_dq0_dfi_rddata_en_p1),
      .o_dfi_rddata_en_p2          (o_dq0_dfi_rddata_en_p2),
      .o_dfi_rddata_en_p3          (o_dq0_dfi_rddata_en_p3),
      .o_dfi_rddata_en_p4          (o_dq0_dfi_rddata_en_p4),
      .o_dfi_rddata_en_p5          (o_dq0_dfi_rddata_en_p5),
      .o_dfi_rddata_en_p6          (o_dq0_dfi_rddata_en_p6),
      .o_dfi_rddata_en_p7          (o_dq0_dfi_rddata_en_p7),
      .o_dfi_rddata_ie_p0          (o_dq0_dfi_rddata_ie_p0),
      .o_dfi_rddata_ie_p1          (o_dq0_dfi_rddata_ie_p1),
      .o_dfi_rddata_ie_p2          (o_dq0_dfi_rddata_ie_p2),
      .o_dfi_rddata_ie_p3          (o_dq0_dfi_rddata_ie_p3),
      .o_dfi_rddata_ie_p4          (o_dq0_dfi_rddata_ie_p4),
      .o_dfi_rddata_ie_p5          (o_dq0_dfi_rddata_ie_p5),
      .o_dfi_rddata_ie_p6          (o_dq0_dfi_rddata_ie_p6),
      .o_dfi_rddata_ie_p7          (o_dq0_dfi_rddata_ie_p7),
      .o_dfi_rddata_re_p0          (o_dq0_dfi_rddata_re_p0),
      .o_dfi_rddata_re_p1          (o_dq0_dfi_rddata_re_p1),
      .o_dfi_rddata_re_p2          (o_dq0_dfi_rddata_re_p2),
      .o_dfi_rddata_re_p3          (o_dq0_dfi_rddata_re_p3),
      .o_dfi_rddata_re_p4          (o_dq0_dfi_rddata_re_p4),
      .o_dfi_rddata_re_p5          (o_dq0_dfi_rddata_re_p5),
      .o_dfi_rddata_re_p6          (o_dq0_dfi_rddata_re_p6),
      .o_dfi_rddata_re_p7          (o_dq0_dfi_rddata_re_p7),
      .o_dfi_rddata_cs_p0          (o_dq0_dfi_rddata_cs_p0),
      .o_dfi_rddata_cs_p1          (o_dq0_dfi_rddata_cs_p1),
      .o_dfi_rddata_cs_p2          (o_dq0_dfi_rddata_cs_p2),
      .o_dfi_rddata_cs_p3          (o_dq0_dfi_rddata_cs_p3),
      .o_dfi_rddata_cs_p4          (o_dq0_dfi_rddata_cs_p4),
      .o_dfi_rddata_cs_p5          (o_dq0_dfi_rddata_cs_p5),
      .o_dfi_rddata_cs_p6          (o_dq0_dfi_rddata_cs_p6),
      .o_dfi_rddata_cs_p7          (o_dq0_dfi_rddata_cs_p7),

      .o_debug                      (/*OPEN*/)
   );
   ddr_dfi_read_en #(
      .PWIDTH                       (PWIDTH),
      .NUM_WPH                      (NUM_WPH),
      .FWIDTH                       (F1WIDTH)
   ) u_dq1_dfi_read_en (
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_rst                        (i_rst),

      .i_clk_0                      (i_wrc_clk_0),
      .i_clk_1                      (i_wrc_clk_1),
      .i_clk_2                      (i_wrc_clk_2),

      .i_rctrl_pipe_en              (i_dfi_rctrl_cfg[`DDR_DFICH_RCTRL_M0_CFG_PIPE_EN_FIELD]),
      .i_rctrl_gb_mode              (cast_dwgb_t(i_dfi_rctrl_cfg[`DDR_DFICH_RCTRL_M0_CFG_GB_MODE_FIELD])),
      .i_rctrl_post_gb_dly          (i_dfi_rctrl_cfg[`DDR_DFICH_RCTRL_M0_CFG_POST_GB_FC_DLY_FIELD]),

      .i_rcs_phase_ext              (i_dfi_ctrl5_cfg[`DDR_DFICH_CTRL5_M0_CFG_RCS_PHASE_EXT_FIELD]),
      .i_ren_phase_ext              (i_dfi_ctrl5_cfg[`DDR_DFICH_CTRL5_M0_CFG_REN_PHASE_EXT_FIELD]),
      .i_ie_phase_ext               (i_dfi_ctrl5_cfg[`DDR_DFICH_CTRL5_M0_CFG_IE_PHASE_EXT_FIELD]),
      .i_re_phase_ext               (i_dfi_ctrl5_cfg[`DDR_DFICH_CTRL5_M0_CFG_RE_PHASE_EXT_FIELD]),

      .i_dfi_rddata_en_p0          (i_dq1_dfi_rddata_en_p0),
      .i_dfi_rddata_en_p1          (i_dq1_dfi_rddata_en_p1),
      .i_dfi_rddata_en_p2          (i_dq1_dfi_rddata_en_p2),
      .i_dfi_rddata_en_p3          (i_dq1_dfi_rddata_en_p3),
      .i_dfi_rddata_en_p4          (i_dq1_dfi_rddata_en_p4),
      .i_dfi_rddata_en_p5          (i_dq1_dfi_rddata_en_p5),
      .i_dfi_rddata_en_p6          (i_dq1_dfi_rddata_en_p6),
      .i_dfi_rddata_en_p7          (i_dq1_dfi_rddata_en_p7),

      .i_dfi_rddata_cs_p0          (i_dq1_dfi_rddata_cs_p0),
      .i_dfi_rddata_cs_p1          (i_dq1_dfi_rddata_cs_p1),
      .i_dfi_rddata_cs_p2          (i_dq1_dfi_rddata_cs_p2),
      .i_dfi_rddata_cs_p3          (i_dq1_dfi_rddata_cs_p3),
      .i_dfi_rddata_cs_p4          (i_dq1_dfi_rddata_cs_p4),
      .i_dfi_rddata_cs_p5          (i_dq1_dfi_rddata_cs_p5),
      .i_dfi_rddata_cs_p6          (i_dq1_dfi_rddata_cs_p6),
      .i_dfi_rddata_cs_p7          (i_dq1_dfi_rddata_cs_p7),

      .o_dfi_rddata_en_p0          (o_dq1_dfi_rddata_en_p0),
      .o_dfi_rddata_en_p1          (o_dq1_dfi_rddata_en_p1),
      .o_dfi_rddata_en_p2          (o_dq1_dfi_rddata_en_p2),
      .o_dfi_rddata_en_p3          (o_dq1_dfi_rddata_en_p3),
      .o_dfi_rddata_en_p4          (o_dq1_dfi_rddata_en_p4),
      .o_dfi_rddata_en_p5          (o_dq1_dfi_rddata_en_p5),
      .o_dfi_rddata_en_p6          (o_dq1_dfi_rddata_en_p6),
      .o_dfi_rddata_en_p7          (o_dq1_dfi_rddata_en_p7),
      .o_dfi_rddata_ie_p0          (o_dq1_dfi_rddata_ie_p0),
      .o_dfi_rddata_ie_p1          (o_dq1_dfi_rddata_ie_p1),
      .o_dfi_rddata_ie_p2          (o_dq1_dfi_rddata_ie_p2),
      .o_dfi_rddata_ie_p3          (o_dq1_dfi_rddata_ie_p3),
      .o_dfi_rddata_ie_p4          (o_dq1_dfi_rddata_ie_p4),
      .o_dfi_rddata_ie_p5          (o_dq1_dfi_rddata_ie_p5),
      .o_dfi_rddata_ie_p6          (o_dq1_dfi_rddata_ie_p6),
      .o_dfi_rddata_ie_p7          (o_dq1_dfi_rddata_ie_p7),
      .o_dfi_rddata_re_p0          (o_dq1_dfi_rddata_re_p0),
      .o_dfi_rddata_re_p1          (o_dq1_dfi_rddata_re_p1),
      .o_dfi_rddata_re_p2          (o_dq1_dfi_rddata_re_p2),
      .o_dfi_rddata_re_p3          (o_dq1_dfi_rddata_re_p3),
      .o_dfi_rddata_re_p4          (o_dq1_dfi_rddata_re_p4),
      .o_dfi_rddata_re_p5          (o_dq1_dfi_rddata_re_p5),
      .o_dfi_rddata_re_p6          (o_dq1_dfi_rddata_re_p6),
      .o_dfi_rddata_re_p7          (o_dq1_dfi_rddata_re_p7),
      .o_dfi_rddata_cs_p0          (o_dq1_dfi_rddata_cs_p0),
      .o_dfi_rddata_cs_p1          (o_dq1_dfi_rddata_cs_p1),
      .o_dfi_rddata_cs_p2          (o_dq1_dfi_rddata_cs_p2),
      .o_dfi_rddata_cs_p3          (o_dq1_dfi_rddata_cs_p3),
      .o_dfi_rddata_cs_p4          (o_dq1_dfi_rddata_cs_p4),
      .o_dfi_rddata_cs_p5          (o_dq1_dfi_rddata_cs_p5),
      .o_dfi_rddata_cs_p6          (o_dq1_dfi_rddata_cs_p6),
      .o_dfi_rddata_cs_p7          (o_dq1_dfi_rddata_cs_p7),

      .o_debug                      (/*OPEN*/)
   );

   // ------------------------------------------------------------------------
   // DFI Read Interface
   // DFI Read Data/DBI/Valid Path
   // ------------------------------------------------------------------------

   ddr_dfi_read #(
     .NUM_DQ                        (NUM_DQ),
     .SWIDTH                        (SWIDTH)
   ) u_dfi_read (
      .i_clk_1                      (i_rd_clk_1  ),  // DIV2
      .i_clk_2                      (i_rd_clk_2  ),  // DIV4
      .i_dfi_clk                    (i_dfi_clk ),  // DFI clock
      .i_rgb_mode                   (cast_drgb_t(i_dfi_rdd_cfg[`DDR_DFICH_RDD_M0_CFG_GB_MODE_FIELD])),
      .i_intf_pipe_en               (i_dfi_ctrl0_cfg[`DDR_DFICH_CTRL0_M0_CFG_RD_INTF_PIPE_EN_FIELD]),

      .i_dq0_dfi_rddata_w0          (i_dq0_dfi_rddata_w0),
      .i_dq0_dfi_rddata_w1          (i_dq0_dfi_rddata_w1),
      .i_dq0_dfi_rddata_w2          (i_dq0_dfi_rddata_w2),
      .i_dq0_dfi_rddata_w3          (i_dq0_dfi_rddata_w3),
      .i_dq0_dfi_rddata_w4          (i_dq0_dfi_rddata_w4),
      .i_dq0_dfi_rddata_w5          (i_dq0_dfi_rddata_w5),
      .i_dq0_dfi_rddata_w6          (i_dq0_dfi_rddata_w6),
      .i_dq0_dfi_rddata_w7          (i_dq0_dfi_rddata_w7),
      .i_dq0_dfi_rddata_dbi_w0      (i_dq0_dfi_rddata_dbi_w0),
      .i_dq0_dfi_rddata_dbi_w1      (i_dq0_dfi_rddata_dbi_w1),
      .i_dq0_dfi_rddata_dbi_w2      (i_dq0_dfi_rddata_dbi_w2),
      .i_dq0_dfi_rddata_dbi_w3      (i_dq0_dfi_rddata_dbi_w3),
      .i_dq0_dfi_rddata_dbi_w4      (i_dq0_dfi_rddata_dbi_w4),
      .i_dq0_dfi_rddata_dbi_w5      (i_dq0_dfi_rddata_dbi_w5),
      .i_dq0_dfi_rddata_dbi_w6      (i_dq0_dfi_rddata_dbi_w6),
      .i_dq0_dfi_rddata_dbi_w7      (i_dq0_dfi_rddata_dbi_w7),
      .i_dq0_dfi_rddata_valid       (i_dq0_dfi_rddata_valid),
      .i_dq1_dfi_rddata_w0          (i_dq1_dfi_rddata_w0),
      .i_dq1_dfi_rddata_w1          (i_dq1_dfi_rddata_w1),
      .i_dq1_dfi_rddata_w2          (i_dq1_dfi_rddata_w2),
      .i_dq1_dfi_rddata_w3          (i_dq1_dfi_rddata_w3),
      .i_dq1_dfi_rddata_w4          (i_dq1_dfi_rddata_w4),
      .i_dq1_dfi_rddata_w5          (i_dq1_dfi_rddata_w5),
      .i_dq1_dfi_rddata_w6          (i_dq1_dfi_rddata_w6),
      .i_dq1_dfi_rddata_w7          (i_dq1_dfi_rddata_w7),
      .i_dq1_dfi_rddata_dbi_w0      (i_dq1_dfi_rddata_dbi_w0),
      .i_dq1_dfi_rddata_dbi_w1      (i_dq1_dfi_rddata_dbi_w1),
      .i_dq1_dfi_rddata_dbi_w2      (i_dq1_dfi_rddata_dbi_w2),
      .i_dq1_dfi_rddata_dbi_w3      (i_dq1_dfi_rddata_dbi_w3),
      .i_dq1_dfi_rddata_dbi_w4      (i_dq1_dfi_rddata_dbi_w4),
      .i_dq1_dfi_rddata_dbi_w5      (i_dq1_dfi_rddata_dbi_w5),
      .i_dq1_dfi_rddata_dbi_w6      (i_dq1_dfi_rddata_dbi_w6),
      .i_dq1_dfi_rddata_dbi_w7      (i_dq1_dfi_rddata_dbi_w7),
      .i_dq1_dfi_rddata_valid       (i_dq1_dfi_rddata_valid),
      .i_dq_dfi_rddata_valid_mask      (i_dq_dfi_rddata_valid_mask),

      .o_dfi_rddata_w0              (o_dfi_rddata_w0),
      .o_dfi_rddata_w1              (o_dfi_rddata_w1),
      .o_dfi_rddata_w2              (o_dfi_rddata_w2),
      .o_dfi_rddata_w3              (o_dfi_rddata_w3),
      .o_dfi_rddata_w4              (o_dfi_rddata_w4),
      .o_dfi_rddata_w5              (o_dfi_rddata_w5),
      .o_dfi_rddata_w6              (o_dfi_rddata_w6),
      .o_dfi_rddata_w7              (o_dfi_rddata_w7),
      .o_dfi_rddata_dbi_w0          (o_dfi_rddata_dbi_w0),
      .o_dfi_rddata_dbi_w1          (o_dfi_rddata_dbi_w1),
      .o_dfi_rddata_dbi_w2          (o_dfi_rddata_dbi_w2),
      .o_dfi_rddata_dbi_w3          (o_dfi_rddata_dbi_w3),
      .o_dfi_rddata_dbi_w4          (o_dfi_rddata_dbi_w4),
      .o_dfi_rddata_dbi_w5          (o_dfi_rddata_dbi_w5),
      .o_dfi_rddata_dbi_w6          (o_dfi_rddata_dbi_w6),
      .o_dfi_rddata_dbi_w7          (o_dfi_rddata_dbi_w7),
      .o_dfi_rddata_valid_w0        (o_dfi_rddata_valid_w0),
      .o_dfi_rddata_valid_w1        (o_dfi_rddata_valid_w1),
      .o_dfi_rddata_valid_w2        (o_dfi_rddata_valid_w2),
      .o_dfi_rddata_valid_w3        (o_dfi_rddata_valid_w3),
      .o_dfi_rddata_valid_w4        (o_dfi_rddata_valid_w4),
      .o_dfi_rddata_valid_w5        (o_dfi_rddata_valid_w5),
      .o_dfi_rddata_valid_w6        (o_dfi_rddata_valid_w6),
      .o_dfi_rddata_valid_w7        (o_dfi_rddata_valid_w7),
      .o_debug                      ()
   );

endmodule

module ddr_dfi_ctrl #(
   parameter       SIWIDTH          = 20                                // DFI Interface counter width
) (
      input  logic                                          i_clk,
      input  logic                                          i_rst,

      input  logic [1:0]                                    i_dfi_freq_fsp,
      input  logic [1:0]                                    i_dfi_freq_ratio,
      input  logic [4:0]                                    i_dfi_frequency,
      input  logic                                          i_dfi_init_start,
      output logic                                          o_dfi_init_complete,
      output logic                                          o_irq_dfi_init_complete,
      output logic                                          o_dfi_init_start,
      input  logic                                          i_init_complete,
      input  logic [`DDR_DFI_STATUS_IF_CFG_RANGE]           i_dfi_status_if_cfg,
      output logic [`DDR_DFI_STATUS_IF_STA_RANGE]           o_dfi_status_if_sta,
      input  logic [`DDR_DFI_STATUS_IF_EVENT_0_CFG_RANGE]   i_dfi_status_if_event_0_cfg,
      input  logic [`DDR_DFI_STATUS_IF_EVENT_1_CFG_RANGE]   i_dfi_status_if_event_1_cfg,

      input  logic                                          i_dfi_ctrlupd_req,
      output logic                                          o_dfi_ctrlupd_req,
      output logic                                          o_dfi_ctrlupd_ack,
      input  logic [`DDR_DFI_CTRLUPD_IF_CFG_RANGE]          i_dfi_ctrlupd_if_cfg,
      output logic [`DDR_DFI_CTRLUPD_IF_STA_RANGE]          o_dfi_ctrlupd_if_sta,
      input  logic [`DDR_DFI_CTRLUPD_IF_EVENT_0_CFG_RANGE]  i_dfi_ctrlupd_if_event_0_cfg,
      input  logic [`DDR_DFI_CTRLUPD_IF_EVENT_1_CFG_RANGE]  i_dfi_ctrlupd_if_event_1_cfg,

      input  logic                                          i_dfi_lp_ctrl_req,
      input  logic [5:0]                                    i_dfi_lp_ctrl_wakeup,
      output logic                                          o_dfi_lp_ctrl_req,
      output logic                                          o_dfi_lp_ctrl_ack,
      input  logic [`DDR_DFI_LP_CTRL_IF_CFG_RANGE]          i_dfi_lp_ctrl_if_cfg,
      output logic [`DDR_DFI_LP_CTRL_IF_STA_RANGE]          o_dfi_lp_ctrl_if_sta,
      input  logic [`DDR_DFI_LP_CTRL_IF_EVENT_0_CFG_RANGE]  i_dfi_lp_ctrl_if_event_0_cfg,
      input  logic [`DDR_DFI_LP_CTRL_IF_EVENT_1_CFG_RANGE]  i_dfi_lp_ctrl_if_event_1_cfg,

      input  logic                                          i_dfi_lp_data_req,
      input  logic [5:0]                                    i_dfi_lp_data_wakeup,
      output logic                                          o_dfi_lp_data_req,
      output logic                                          o_dfi_lp_data_ack,
      input  logic [`DDR_DFI_LP_DATA_IF_CFG_RANGE]          i_dfi_lp_data_if_cfg,
      output logic [`DDR_DFI_LP_DATA_IF_STA_RANGE]          o_dfi_lp_data_if_sta,
      input  logic [`DDR_DFI_LP_DATA_IF_EVENT_0_CFG_RANGE]  i_dfi_lp_data_if_event_0_cfg,
      input  logic [`DDR_DFI_LP_DATA_IF_EVENT_1_CFG_RANGE]  i_dfi_lp_data_if_event_1_cfg,

      output logic                                          o_dfi_phyupd_req,
      input  logic                                          i_dfi_phyupd_ack,
      output logic                                          o_dfi_phyupd_ack,
      output logic [1:0]                                    o_dfi_phyupd_type,
      input  logic [`DDR_DFI_PHYUPD_IF_CFG_RANGE]           i_dfi_phyupd_if_cfg,
      output logic [`DDR_DFI_PHYUPD_IF_STA_RANGE]           o_dfi_phyupd_if_sta,

      output logic                                          o_dfi_phymstr_req,
      input  logic                                          i_dfi_phymstr_ack,
      output logic                                          o_dfi_phymstr_ack,
      output logic [1:0]                                    o_dfi_phymstr_type,
      output logic [1:0]                                    o_dfi_phymstr_cs_state,
      output logic                                          o_dfi_phymstr_state_sel,
      input  logic [`DDR_DFI_PHYMSTR_IF_CFG_RANGE]          i_dfi_phymstr_if_cfg,
      output logic [`DDR_DFI_PHYMSTR_IF_STA_RANGE]          o_dfi_phymstr_if_sta,
      output logic [31:0]                                   o_debug
);

   // ------------------------------------------------------------------------
   // DFI Status Interface
   // ------------------------------------------------------------------------

   logic dfi_status_req, dfi_status_ack;
   logic dfi_status_ack_irq ;

   ddr_dfi_ig_req_intf #(
      .POR_SW_ACK_HI                (1),
      .POR_SW_REQ_HI                (0),
      .POR_SW_REQ_LO                (1),
      .RH_EDGE_TRIG                 (1'b1),
      .CWIDTH                       (SIWIDTH)
   ) u_status_intf (
      .i_clk                        (i_clk),
      .i_rst                        (i_rst),

      .i_req                        (i_dfi_init_start),
      .o_req                        (dfi_status_req),
      .o_ack                        (dfi_status_ack),
      .o_irq_ack                    (dfi_status_ack_irq),

      .i_event_0_en                 ('0),  // Unused
      .i_event_0                    ('0),  // Unused
      .i_event_1_en                 ('1),
      .i_event_1                    (i_init_complete),

      .i_sw_event_0_cnt             (i_dfi_status_if_event_0_cfg[`DDR_DFI_STATUS_IF_EVENT_0_CFG_SW_EVENT_CNT_FIELD]),
      .i_sw_event_1_cnt             (i_dfi_status_if_event_1_cfg[`DDR_DFI_STATUS_IF_EVENT_1_CFG_SW_EVENT_CNT_FIELD]),
      .i_sw_event_0_cnt_sel         (i_dfi_status_if_event_0_cfg[`DDR_DFI_STATUS_IF_EVENT_0_CFG_SW_EVENT_CNT_SEL_FIELD]),
      .i_sw_event_1_cnt_sel         (i_dfi_status_if_event_1_cfg[`DDR_DFI_STATUS_IF_EVENT_1_CFG_SW_EVENT_CNT_SEL_FIELD]),
      .i_hw_event_0_cnt             ('0),
      .i_hw_event_1_cnt             ('0),

      .i_sw_req_ovr                 (i_dfi_status_if_cfg[`DDR_DFI_STATUS_IF_CFG_SW_REQ_OVR_FIELD]),
      .i_sw_req_val                 (i_dfi_status_if_cfg[`DDR_DFI_STATUS_IF_CFG_SW_REQ_VAL_FIELD]),
      .i_sw_ack_ovr                 (i_dfi_status_if_cfg[`DDR_DFI_STATUS_IF_CFG_SW_ACK_OVR_FIELD]),
      .i_sw_ack_val                 (i_dfi_status_if_cfg[`DDR_DFI_STATUS_IF_CFG_SW_ACK_VAL_FIELD]),
      .i_sw_event_0_ovr             (i_dfi_status_if_cfg[`DDR_DFI_STATUS_IF_CFG_SW_EVENT_0_OVR_FIELD]),
      .i_sw_event_0_val             (i_dfi_status_if_cfg[`DDR_DFI_STATUS_IF_CFG_SW_EVENT_0_VAL_FIELD]),
      .i_sw_event_1_ovr             (i_dfi_status_if_cfg[`DDR_DFI_STATUS_IF_CFG_SW_EVENT_1_OVR_FIELD]),
      .i_sw_event_1_val             (i_dfi_status_if_cfg[`DDR_DFI_STATUS_IF_CFG_SW_EVENT_1_VAL_FIELD])
   );

   // Status Init Start
   assign o_dfi_init_start = dfi_status_req;

   // Status Init Complete
   assign o_dfi_init_complete = ~dfi_status_ack ;
   assign o_irq_dfi_init_complete = ~dfi_status_ack_irq ;

   always_comb begin
      o_dfi_status_if_sta                                                       = '0;
      o_dfi_status_if_sta[`DDR_DFI_STATUS_IF_STA_REQ_FIELD]        = dfi_status_req;
      o_dfi_status_if_sta[`DDR_DFI_STATUS_IF_STA_ACK_FIELD]        = dfi_status_ack;
      o_dfi_status_if_sta[`DDR_DFI_STATUS_IF_STA_FREQ_FSP_FIELD]   =
                     i_dfi_status_if_cfg[`DDR_DFI_STATUS_IF_CFG_SW_FREQ_OVR_FIELD] ?
                     i_dfi_status_if_cfg[`DDR_DFI_STATUS_IF_CFG_SW_FREQ_FSP_VAL_FIELD] :
                     i_dfi_freq_fsp;
      o_dfi_status_if_sta[`DDR_DFI_STATUS_IF_STA_FREQ_RATIO_FIELD] =
                     i_dfi_status_if_cfg[`DDR_DFI_STATUS_IF_CFG_SW_FREQ_OVR_FIELD] ?
                     i_dfi_status_if_cfg[`DDR_DFI_STATUS_IF_CFG_SW_FREQ_RATIO_VAL_FIELD] :
                     i_dfi_freq_ratio;
      o_dfi_status_if_sta[`DDR_DFI_STATUS_IF_STA_FREQUENCY_FIELD]  =
                     i_dfi_status_if_cfg[`DDR_DFI_STATUS_IF_CFG_SW_FREQ_OVR_FIELD] ?
                     i_dfi_status_if_cfg[`DDR_DFI_STATUS_IF_CFG_SW_FREQUENCY_VAL_FIELD] :
                     i_dfi_frequency;
   end

   // ------------------------------------------------------------------------
   // DFI Update (CTRL) Interface
   // ------------------------------------------------------------------------

   ddr_dfi_ig_req_intf #(
      .CWIDTH                       (SIWIDTH)
   ) u_ctrlupd_intf (
      .i_clk                        (i_clk),
      .i_rst                        (i_rst),

      .i_req                        (i_dfi_ctrlupd_req),
      .o_req                        (o_dfi_ctrlupd_req),
      .o_ack                        (o_dfi_ctrlupd_ack),
      .o_irq_ack                    (/*OPEN*/),

      .i_event_0_en                 ('0),
      .i_event_0                    ('0),
      .i_event_1_en                 ('0),
      .i_event_1                    ('0),

      .i_sw_event_0_cnt             (i_dfi_ctrlupd_if_event_0_cfg[`DDR_DFI_CTRLUPD_IF_EVENT_0_CFG_SW_EVENT_CNT_FIELD]),
      .i_sw_event_1_cnt             (i_dfi_ctrlupd_if_event_1_cfg[`DDR_DFI_CTRLUPD_IF_EVENT_1_CFG_SW_EVENT_CNT_FIELD]),
      .i_sw_event_0_cnt_sel         (i_dfi_ctrlupd_if_event_0_cfg[`DDR_DFI_CTRLUPD_IF_EVENT_0_CFG_SW_EVENT_CNT_SEL_FIELD]),
      .i_sw_event_1_cnt_sel         (i_dfi_ctrlupd_if_event_1_cfg[`DDR_DFI_CTRLUPD_IF_EVENT_1_CFG_SW_EVENT_CNT_SEL_FIELD]),
      .i_hw_event_0_cnt             ('0),
      .i_hw_event_1_cnt             ('0),

      .i_sw_req_ovr                 (i_dfi_ctrlupd_if_cfg[`DDR_DFI_CTRLUPD_IF_CFG_SW_REQ_OVR_FIELD]),
      .i_sw_req_val                 (i_dfi_ctrlupd_if_cfg[`DDR_DFI_CTRLUPD_IF_CFG_SW_REQ_VAL_FIELD]),
      .i_sw_ack_ovr                 (i_dfi_ctrlupd_if_cfg[`DDR_DFI_CTRLUPD_IF_CFG_SW_ACK_OVR_FIELD]),
      .i_sw_ack_val                 (i_dfi_ctrlupd_if_cfg[`DDR_DFI_CTRLUPD_IF_CFG_SW_ACK_VAL_FIELD]),
      .i_sw_event_0_ovr             (i_dfi_ctrlupd_if_cfg[`DDR_DFI_CTRLUPD_IF_CFG_SW_EVENT_0_OVR_FIELD]),
      .i_sw_event_0_val             (i_dfi_ctrlupd_if_cfg[`DDR_DFI_CTRLUPD_IF_CFG_SW_EVENT_0_VAL_FIELD]),
      .i_sw_event_1_ovr             (i_dfi_ctrlupd_if_cfg[`DDR_DFI_CTRLUPD_IF_CFG_SW_EVENT_1_OVR_FIELD]),
      .i_sw_event_1_val             (i_dfi_ctrlupd_if_cfg[`DDR_DFI_CTRLUPD_IF_CFG_SW_EVENT_1_VAL_FIELD])
   );

   always_comb begin
      o_dfi_ctrlupd_if_sta = '0;
      o_dfi_ctrlupd_if_sta[`DDR_DFI_CTRLUPD_IF_STA_REQ_FIELD] = o_dfi_ctrlupd_req;
      o_dfi_ctrlupd_if_sta[`DDR_DFI_CTRLUPD_IF_STA_ACK_FIELD] = o_dfi_ctrlupd_ack;
   end

   // ------------------------------------------------------------------------
   // DFI Low Power (CTRL) Interface
   // ------------------------------------------------------------------------
   logic [SIWIDTH-1:0] lp_ctrl_hw_event_1_cnt;
   assign lp_ctrl_hw_event_1_cnt = 1'b1 << i_dfi_lp_ctrl_wakeup ;

   ddr_dfi_ig_req_intf #(
      .CWIDTH                       (SIWIDTH)
   ) u_lp_ctrl_intf (
      .i_clk                        (i_clk),
      .i_rst                        (i_rst),

      .i_req                        (i_dfi_lp_ctrl_req),
      .o_req                        (o_dfi_lp_ctrl_req),
      .o_ack                        (o_dfi_lp_ctrl_ack),
      .o_irq_ack                    (/*OPEN*/),

      .i_event_0_en                 ('0),
      .i_event_0                    ('0),
      .i_event_1_en                 ('0),
      .i_event_1                    ('0),

      .i_sw_event_0_cnt             (i_dfi_lp_ctrl_if_event_0_cfg[`DDR_DFI_LP_CTRL_IF_EVENT_0_CFG_SW_EVENT_CNT_FIELD]),
      .i_sw_event_1_cnt             (i_dfi_lp_ctrl_if_event_1_cfg[`DDR_DFI_LP_CTRL_IF_EVENT_1_CFG_SW_EVENT_CNT_FIELD]),
      .i_sw_event_0_cnt_sel         (i_dfi_lp_ctrl_if_event_0_cfg[`DDR_DFI_LP_CTRL_IF_EVENT_0_CFG_SW_EVENT_CNT_SEL_FIELD]),
      .i_sw_event_1_cnt_sel         (i_dfi_lp_ctrl_if_event_1_cfg[`DDR_DFI_LP_CTRL_IF_EVENT_1_CFG_SW_EVENT_CNT_SEL_FIELD]),
      .i_hw_event_0_cnt             ('0),
      .i_hw_event_1_cnt             (lp_ctrl_hw_event_1_cnt),

      .i_sw_req_ovr                 (i_dfi_lp_ctrl_if_cfg[`DDR_DFI_LP_CTRL_IF_CFG_SW_REQ_OVR_FIELD]),
      .i_sw_req_val                 (i_dfi_lp_ctrl_if_cfg[`DDR_DFI_LP_CTRL_IF_CFG_SW_REQ_VAL_FIELD]),
      .i_sw_ack_ovr                 (i_dfi_lp_ctrl_if_cfg[`DDR_DFI_LP_CTRL_IF_CFG_SW_ACK_OVR_FIELD]),
      .i_sw_ack_val                 (i_dfi_lp_ctrl_if_cfg[`DDR_DFI_LP_CTRL_IF_CFG_SW_ACK_VAL_FIELD]),
      .i_sw_event_0_ovr             (i_dfi_lp_ctrl_if_cfg[`DDR_DFI_LP_CTRL_IF_CFG_SW_EVENT_0_OVR_FIELD]),
      .i_sw_event_0_val             (i_dfi_lp_ctrl_if_cfg[`DDR_DFI_LP_CTRL_IF_CFG_SW_EVENT_0_VAL_FIELD]),
      .i_sw_event_1_ovr             (i_dfi_lp_ctrl_if_cfg[`DDR_DFI_LP_CTRL_IF_CFG_SW_EVENT_1_OVR_FIELD]),
      .i_sw_event_1_val             (i_dfi_lp_ctrl_if_cfg[`DDR_DFI_LP_CTRL_IF_CFG_SW_EVENT_1_VAL_FIELD])
   );

   always_comb begin
      o_dfi_lp_ctrl_if_sta = '0;
      o_dfi_lp_ctrl_if_sta[`DDR_DFI_LP_CTRL_IF_STA_REQ_FIELD]    = o_dfi_lp_ctrl_req;
      o_dfi_lp_ctrl_if_sta[`DDR_DFI_LP_CTRL_IF_STA_ACK_FIELD]    = o_dfi_lp_ctrl_ack;
      o_dfi_lp_ctrl_if_sta[`DDR_DFI_LP_CTRL_IF_STA_WAKEUP_FIELD] = i_dfi_lp_ctrl_wakeup;
   end

   // ------------------------------------------------------------------------
   // DFI Low Power (DATA) Interface
   // ------------------------------------------------------------------------
   logic [SIWIDTH-1:0] lp_data_hw_event_1_cnt;
   assign lp_data_hw_event_1_cnt = 1'b1 << i_dfi_lp_data_wakeup ;

   ddr_dfi_ig_req_intf #(
      .CWIDTH                       (SIWIDTH)
   ) u_lp_data_intf (
      .i_clk                        (i_clk),
      .i_rst                        (i_rst),

      .i_req                        (i_dfi_lp_data_req),
      .o_req                        (o_dfi_lp_data_req),
      .o_ack                        (o_dfi_lp_data_ack),
      .o_irq_ack                    (/*OPEN*/),

      .i_event_0_en                 ('0),
      .i_event_0                    ('0),
      .i_event_1_en                 ('0),
      .i_event_1                    ('0),

      .i_sw_event_0_cnt             (i_dfi_lp_data_if_event_0_cfg[`DDR_DFI_LP_DATA_IF_EVENT_0_CFG_SW_EVENT_CNT_FIELD]),
      .i_sw_event_1_cnt             (i_dfi_lp_data_if_event_1_cfg[`DDR_DFI_LP_DATA_IF_EVENT_1_CFG_SW_EVENT_CNT_FIELD]),
      .i_sw_event_0_cnt_sel         (i_dfi_lp_data_if_event_0_cfg[`DDR_DFI_LP_DATA_IF_EVENT_0_CFG_SW_EVENT_CNT_SEL_FIELD]),
      .i_sw_event_1_cnt_sel         (i_dfi_lp_data_if_event_1_cfg[`DDR_DFI_LP_DATA_IF_EVENT_1_CFG_SW_EVENT_CNT_SEL_FIELD]),
      .i_hw_event_0_cnt             ('0),
      .i_hw_event_1_cnt             (lp_data_hw_event_1_cnt),

      .i_sw_req_ovr                 (i_dfi_lp_data_if_cfg[`DDR_DFI_LP_DATA_IF_CFG_SW_REQ_OVR_FIELD]),
      .i_sw_req_val                 (i_dfi_lp_data_if_cfg[`DDR_DFI_LP_DATA_IF_CFG_SW_REQ_VAL_FIELD]),
      .i_sw_ack_ovr                 (i_dfi_lp_data_if_cfg[`DDR_DFI_LP_DATA_IF_CFG_SW_ACK_OVR_FIELD]),
      .i_sw_ack_val                 (i_dfi_lp_data_if_cfg[`DDR_DFI_LP_DATA_IF_CFG_SW_ACK_VAL_FIELD]),
      .i_sw_event_0_ovr             (i_dfi_lp_data_if_cfg[`DDR_DFI_LP_DATA_IF_CFG_SW_EVENT_0_OVR_FIELD]),
      .i_sw_event_0_val             (i_dfi_lp_data_if_cfg[`DDR_DFI_LP_DATA_IF_CFG_SW_EVENT_0_VAL_FIELD]),
      .i_sw_event_1_ovr             (i_dfi_lp_data_if_cfg[`DDR_DFI_LP_DATA_IF_CFG_SW_EVENT_1_OVR_FIELD]),
      .i_sw_event_1_val             (i_dfi_lp_data_if_cfg[`DDR_DFI_LP_DATA_IF_CFG_SW_EVENT_1_VAL_FIELD])
   );

   always_comb begin
      o_dfi_lp_data_if_sta = '0;
      o_dfi_lp_data_if_sta[`DDR_DFI_LP_DATA_IF_STA_REQ_FIELD]    = o_dfi_lp_data_req;
      o_dfi_lp_data_if_sta[`DDR_DFI_LP_DATA_IF_STA_ACK_FIELD]    = o_dfi_lp_data_ack;
      o_dfi_lp_data_if_sta[`DDR_DFI_LP_DATA_IF_STA_WAKEUP_FIELD] = i_dfi_lp_data_wakeup;
   end

   // ------------------------------------------------------------------------
   // DFI Update (PHY) Interface
   // ------------------------------------------------------------------------

   ddr_dfi_eg_req_intf u_phyupd_intf (
      .i_clk                        (i_clk),
      .i_rst                        (i_rst),

      .i_event                      ('0),  //  Connect to any logic (done) that may need to update based on ACK
      .i_req                        ('0),  //  Connect to any logic that might request an update (other than SW)
      .o_req                        (o_dfi_phyupd_req),
      .o_ack                        (o_dfi_phyupd_ack),
      .i_ack                        (i_dfi_phyupd_ack),

      .i_sw_req_ovr                 (i_dfi_phyupd_if_cfg[`DDR_DFI_PHYUPD_IF_CFG_SW_REQ_OVR_FIELD]),
      .i_sw_req_val                 (i_dfi_phyupd_if_cfg[`DDR_DFI_PHYUPD_IF_CFG_SW_REQ_VAL_FIELD]),
      .i_sw_ack_ovr                 (i_dfi_phyupd_if_cfg[`DDR_DFI_PHYUPD_IF_CFG_SW_ACK_OVR_FIELD]),
      .i_sw_ack_val                 (i_dfi_phyupd_if_cfg[`DDR_DFI_PHYUPD_IF_CFG_SW_ACK_VAL_FIELD]),
      .i_sw_event_ovr               (i_dfi_phyupd_if_cfg[`DDR_DFI_PHYUPD_IF_CFG_SW_EVENT_OVR_FIELD]),
      .i_sw_event_val               (i_dfi_phyupd_if_cfg[`DDR_DFI_PHYUPD_IF_CFG_SW_EVENT_VAL_FIELD])
   );

   always_comb begin
      o_dfi_phyupd_if_sta = '0;
      o_dfi_phyupd_if_sta[`DDR_DFI_PHYUPD_IF_STA_REQ_FIELD]   = o_dfi_phyupd_req;
      o_dfi_phyupd_if_sta[`DDR_DFI_PHYUPD_IF_STA_ACK_FIELD]   = i_dfi_phyupd_ack;
      o_dfi_phyupd_if_sta[`DDR_DFI_PHYUPD_IF_STA_EVENT_FIELD] = '0; // FIXME - Connect to event
   end

   assign o_dfi_phyupd_type = i_dfi_phyupd_if_cfg[`DDR_DFI_PHYUPD_IF_CFG_SW_TYPE_FIELD];

   // ------------------------------------------------------------------------
   // DFI PHY Master Interface
   // ------------------------------------------------------------------------

   ddr_dfi_eg_req_intf u_phymstr_intf (
      .i_clk                        (i_clk),
      .i_rst                        (i_rst),

      .i_event                      ('0),  // Connect to any logic (done) that may need to update based on ACK
      .i_req                        ('0),  // Connect to any logic that might request an update (other than SW)
      .o_req                        (o_dfi_phymstr_req),
      .o_ack                        (o_dfi_phymstr_ack),
      .i_ack                        (i_dfi_phymstr_ack),

      .i_sw_req_ovr                 (i_dfi_phymstr_if_cfg[`DDR_DFI_PHYMSTR_IF_CFG_SW_REQ_OVR_FIELD]),
      .i_sw_req_val                 (i_dfi_phymstr_if_cfg[`DDR_DFI_PHYMSTR_IF_CFG_SW_REQ_VAL_FIELD]),
      .i_sw_ack_ovr                 (i_dfi_phymstr_if_cfg[`DDR_DFI_PHYMSTR_IF_CFG_SW_ACK_OVR_FIELD]),
      .i_sw_ack_val                 (i_dfi_phymstr_if_cfg[`DDR_DFI_PHYMSTR_IF_CFG_SW_ACK_VAL_FIELD]),
      .i_sw_event_ovr               (i_dfi_phymstr_if_cfg[`DDR_DFI_PHYMSTR_IF_CFG_SW_EVENT_OVR_FIELD]),
      .i_sw_event_val               (i_dfi_phymstr_if_cfg[`DDR_DFI_PHYMSTR_IF_CFG_SW_EVENT_VAL_FIELD])
   );

   always_comb begin
      o_dfi_phymstr_if_sta = '0;
      o_dfi_phymstr_if_sta[`DDR_DFI_PHYMSTR_IF_STA_REQ_FIELD]   = o_dfi_phymstr_req;
      o_dfi_phymstr_if_sta[`DDR_DFI_PHYMSTR_IF_STA_ACK_FIELD]   = i_dfi_phymstr_ack;
      o_dfi_phymstr_if_sta[`DDR_DFI_PHYMSTR_IF_STA_EVENT_FIELD] = '0; // FIXME - Connect to event
   end

   assign o_dfi_phymstr_type      = i_dfi_phymstr_if_cfg[`DDR_DFI_PHYMSTR_IF_CFG_SW_TYPE_FIELD];
   assign o_dfi_phymstr_cs_state  = i_dfi_phymstr_if_cfg[`DDR_DFI_PHYMSTR_IF_CFG_SW_CS_STATE_FIELD];
   assign o_dfi_phymstr_state_sel = i_dfi_phymstr_if_cfg[`DDR_DFI_PHYMSTR_IF_CFG_SW_STATE_SEL_FIELD];

   //---------------------------------------------------------------------------
   // Debug Bus
   //---------------------------------------------------------------------------
   assign o_debug = {
                      // PHY Master Intf - 4 bits
                      o_dfi_phymstr_type,
                      i_dfi_phymstr_ack,
                      o_dfi_phymstr_req,
                      // PHY Upd Intf - 4 bits
                      o_dfi_phyupd_type,
                      i_dfi_phyupd_ack,
                      o_dfi_phyupd_req,
                      // LP Data Intf - 8 bits
                      i_dfi_lp_data_wakeup,
                      1'b0,
                      o_dfi_lp_data_req,
                      o_dfi_lp_data_ack,
                      i_dfi_lp_data_req,
                      // LP Control Intf - 8 bits
                      i_dfi_lp_ctrl_wakeup,
                      1'b0,
                      o_dfi_lp_ctrl_req,
                      o_dfi_lp_ctrl_ack,
                      i_dfi_lp_ctrl_req,
                      // Control Update - 4 bits
                      1'b0,
                      o_dfi_ctrlupd_req,
                      o_dfi_ctrlupd_ack,
                      i_dfi_ctrlupd_req,
                      // Status interface - 4 bits
                      i_init_complete ,
                      dfi_status_req  ,
                      dfi_status_ack  ,
                      i_dfi_init_start
                    };
endmodule

module ddr_dfi2dp #(
   parameter       SWIDTH           = 8,                                               // PHY Slice Width
   parameter       BWIDTH           = SWIDTH / 8,                                      // BYTE Width
   parameter       MWIDTH           = BWIDTH,                                          // Mask width for single phase.
   parameter       AWIDTH           = 7,                             // Address bus width
   parameter       NUM_DQ           = 2,                              // Number of DQs
   parameter       NUM_WPH          = 8,                        // Number of Phases
   parameter       NUM_RPH          = 8,                        // Number of Phases
   parameter       DQ_WIDTH         =  9,                             // DQ bus width
   parameter       DQ_RWIDTH        = NUM_RPH * DQ_WIDTH,                              // DQ read data width
   parameter       DQ_WWIDTH        = NUM_WPH * DQ_WIDTH,                              // DQ write data width
   parameter       DQS_WIDTH        =  9+0,// DQS bus width
   parameter       DQS_WWIDTH       = NUM_WPH * DQS_WIDTH,                             // DQS write data width
   parameter       CA_WIDTH         =  11,                             // DQ bus width
   parameter       CA_RWIDTH        = NUM_RPH * CA_WIDTH,                              // DQ read data width
   parameter       CA_WWIDTH        = NUM_WPH * CA_WIDTH,                              // DQ write data width
   parameter       CK_WIDTH         =  1+8,  // DQS bus width
   parameter       CK_WWIDTH        = NUM_WPH * CK_WIDTH                               // DQS write data width
) (
   input  logic [1:0]                i_dfi_cke_p0,
   input  logic [1:0]                i_dfi_cke_p1,
   input  logic [1:0]                i_dfi_cke_p2,
   input  logic [1:0]                i_dfi_cke_p3,
   input  logic [1:0]                i_dfi_cke_p4,
   input  logic [1:0]                i_dfi_cke_p5,
   input  logic [1:0]                i_dfi_cke_p6,
   input  logic [1:0]                i_dfi_cke_p7,
   input  logic [1:0]                i_dfi_cs_p0,
   input  logic [1:0]                i_dfi_cs_p1,
   input  logic [1:0]                i_dfi_cs_p2,
   input  logic [1:0]                i_dfi_cs_p3,
   input  logic [1:0]                i_dfi_cs_p4,
   input  logic [1:0]                i_dfi_cs_p5,
   input  logic [1:0]                i_dfi_cs_p6,
   input  logic [1:0]                i_dfi_cs_p7,
   input  logic [AWIDTH-1:0]         i_dfi_address_p0,
   input  logic [AWIDTH-1:0]         i_dfi_address_p1,
   input  logic [AWIDTH-1:0]         i_dfi_address_p2,
   input  logic [AWIDTH-1:0]         i_dfi_address_p3,
   input  logic [AWIDTH-1:0]         i_dfi_address_p4,
   input  logic [AWIDTH-1:0]         i_dfi_address_p5,
   input  logic [AWIDTH-1:0]         i_dfi_address_p6,
   input  logic [AWIDTH-1:0]         i_dfi_address_p7,
   input  logic                      i_dfi_carddata_en_p0,
   input  logic                      i_dfi_carddata_en_p1,
   input  logic                      i_dfi_carddata_en_p2,
   input  logic                      i_dfi_carddata_en_p3,
   input  logic                      i_dfi_carddata_en_p4,
   input  logic                      i_dfi_carddata_en_p5,
   input  logic                      i_dfi_carddata_en_p6,
   input  logic                      i_dfi_carddata_en_p7,
   input  logic                      i_dfi_dram_clk_enable_p0,
   input  logic                      i_dfi_dram_clk_enable_p1,
   input  logic                      i_dfi_dram_clk_enable_p2,
   input  logic                      i_dfi_dram_clk_enable_p3,
   input  logic                      i_dfi_dram_clk_enable_p4,
   input  logic                      i_dfi_dram_clk_enable_p5,
   input  logic                      i_dfi_dram_clk_enable_p6,
   input  logic                      i_dfi_dram_clk_enable_p7,
   output logic [AWIDTH-1:0]         o_dfi_address_w0,
   output logic [AWIDTH-1:0]         o_dfi_address_w1,
   output logic [AWIDTH-1:0]         o_dfi_address_w2,
   output logic [AWIDTH-1:0]         o_dfi_address_w3,
   output logic [AWIDTH-1:0]         o_dfi_address_w4,
   output logic [AWIDTH-1:0]         o_dfi_address_w5,
   output logic [AWIDTH-1:0]         o_dfi_address_w6,
   output logic [AWIDTH-1:0]         o_dfi_address_w7,
   output logic [1:0]                o_dfi_cs_w0,
   output logic [1:0]                o_dfi_cs_w1,
   output logic [1:0]                o_dfi_cs_w2,
   output logic [1:0]                o_dfi_cs_w3,
   output logic [1:0]                o_dfi_cs_w4,
   output logic [1:0]                o_dfi_cs_w5,
   output logic [1:0]                o_dfi_cs_w6,
   output logic [1:0]                o_dfi_cs_w7,
   output logic [1:0]                o_dfi_cke_w0,
   output logic [1:0]                o_dfi_cke_w1,
   output logic [1:0]                o_dfi_cke_w2,
   output logic [1:0]                o_dfi_cke_w3,
   output logic [1:0]                o_dfi_cke_w4,
   output logic [1:0]                o_dfi_cke_w5,
   output logic [1:0]                o_dfi_cke_w6,
   output logic [1:0]                o_dfi_cke_w7,
   output logic [CA_WIDTH-1:0]       o_dfi_address_valid,
   input  logic [SWIDTH-1:0]         i_dq0_dfi_wrdata_p0,
   input  logic [SWIDTH-1:0]         i_dq0_dfi_wrdata_p1,
   input  logic [SWIDTH-1:0]         i_dq0_dfi_wrdata_p2,
   input  logic [SWIDTH-1:0]         i_dq0_dfi_wrdata_p3,
   input  logic [SWIDTH-1:0]         i_dq0_dfi_wrdata_p4,
   input  logic [SWIDTH-1:0]         i_dq0_dfi_wrdata_p5,
   input  logic [SWIDTH-1:0]         i_dq0_dfi_wrdata_p6,
   input  logic [SWIDTH-1:0]         i_dq0_dfi_wrdata_p7,
   input  logic [MWIDTH-1:0]         i_dq0_dfi_wrdata_mask_p0,
   input  logic [MWIDTH-1:0]         i_dq0_dfi_wrdata_mask_p1,
   input  logic [MWIDTH-1:0]         i_dq0_dfi_wrdata_mask_p2,
   input  logic [MWIDTH-1:0]         i_dq0_dfi_wrdata_mask_p3,
   input  logic [MWIDTH-1:0]         i_dq0_dfi_wrdata_mask_p4,
   input  logic [MWIDTH-1:0]         i_dq0_dfi_wrdata_mask_p5,
   input  logic [MWIDTH-1:0]         i_dq0_dfi_wrdata_mask_p6,
   input  logic [MWIDTH-1:0]         i_dq0_dfi_wrdata_mask_p7,
   input  logic                      i_dq0_dfi_wrdata_cs_p0,
   input  logic                      i_dq0_dfi_wrdata_cs_p1,
   input  logic                      i_dq0_dfi_wrdata_cs_p2,
   input  logic                      i_dq0_dfi_wrdata_cs_p3,
   input  logic                      i_dq0_dfi_wrdata_cs_p4,
   input  logic                      i_dq0_dfi_wrdata_cs_p5,
   input  logic                      i_dq0_dfi_wrdata_cs_p6,
   input  logic                      i_dq0_dfi_wrdata_cs_p7,
   input  logic                      i_dq0_dfi_wck_oe_p0,
   input  logic                      i_dq0_dfi_wck_oe_p1,
   input  logic                      i_dq0_dfi_wck_oe_p2,
   input  logic                      i_dq0_dfi_wck_oe_p3,
   input  logic                      i_dq0_dfi_wck_oe_p4,
   input  logic                      i_dq0_dfi_wck_oe_p5,
   input  logic                      i_dq0_dfi_wck_oe_p6,
   input  logic                      i_dq0_dfi_wck_oe_p7,
   input  logic                      i_dq0_dfi_wrdata_oe_p0,
   input  logic                      i_dq0_dfi_wrdata_oe_p1,
   input  logic                      i_dq0_dfi_wrdata_oe_p2,
   input  logic                      i_dq0_dfi_wrdata_oe_p3,
   input  logic                      i_dq0_dfi_wrdata_oe_p4,
   input  logic                      i_dq0_dfi_wrdata_oe_p5,
   input  logic                      i_dq0_dfi_wrdata_oe_p6,
   input  logic                      i_dq0_dfi_wrdata_oe_p7,
   input  logic                      i_dq0_dfi_parity_in_p0,
   input  logic                      i_dq0_dfi_parity_in_p1,
   input  logic                      i_dq0_dfi_parity_in_p2,
   input  logic                      i_dq0_dfi_parity_in_p3,
   input  logic                      i_dq0_dfi_parity_in_p4,
   input  logic                      i_dq0_dfi_parity_in_p5,
   input  logic                      i_dq0_dfi_parity_in_p6,
   input  logic                      i_dq0_dfi_parity_in_p7,
   input  logic                      i_dq0_dfi_wck_ten_p0,
   input  logic                      i_dq0_dfi_wck_ten_p1,
   input  logic                      i_dq0_dfi_wck_ten_p2,
   input  logic                      i_dq0_dfi_wck_ten_p3,
   input  logic                      i_dq0_dfi_wck_ten_p4,
   input  logic                      i_dq0_dfi_wck_ten_p5,
   input  logic                      i_dq0_dfi_wck_ten_p6,
   input  logic                      i_dq0_dfi_wck_ten_p7,
   input  logic                      i_dq0_dfi_rddata_cs_p0,
   input  logic                      i_dq0_dfi_rddata_cs_p1,
   input  logic                      i_dq0_dfi_rddata_cs_p2,
   input  logic                      i_dq0_dfi_rddata_cs_p3,
   input  logic                      i_dq0_dfi_rddata_cs_p4,
   input  logic                      i_dq0_dfi_rddata_cs_p5,
   input  logic                      i_dq0_dfi_rddata_cs_p6,
   input  logic                      i_dq0_dfi_rddata_cs_p7,
   input  logic                      i_dq0_dfi_rddata_ie_p0,
   input  logic                      i_dq0_dfi_rddata_ie_p1,
   input  logic                      i_dq0_dfi_rddata_ie_p2,
   input  logic                      i_dq0_dfi_rddata_ie_p3,
   input  logic                      i_dq0_dfi_rddata_ie_p4,
   input  logic                      i_dq0_dfi_rddata_ie_p5,
   input  logic                      i_dq0_dfi_rddata_ie_p6,
   input  logic                      i_dq0_dfi_rddata_ie_p7,
   input  logic                      i_dq0_dfi_rddata_re_p0,
   input  logic                      i_dq0_dfi_rddata_re_p1,
   input  logic                      i_dq0_dfi_rddata_re_p2,
   input  logic                      i_dq0_dfi_rddata_re_p3,
   input  logic                      i_dq0_dfi_rddata_re_p4,
   input  logic                      i_dq0_dfi_rddata_re_p5,
   input  logic                      i_dq0_dfi_rddata_re_p6,
   input  logic                      i_dq0_dfi_rddata_re_p7,
   input  logic                      i_dq0_dfi_rddata_en_p0,
   input  logic                      i_dq0_dfi_rddata_en_p1,
   input  logic                      i_dq0_dfi_rddata_en_p2,
   input  logic                      i_dq0_dfi_rddata_en_p3,
   input  logic                      i_dq0_dfi_rddata_en_p4,
   input  logic                      i_dq0_dfi_rddata_en_p5,
   input  logic                      i_dq0_dfi_rddata_en_p6,
   input  logic                      i_dq0_dfi_rddata_en_p7,
   output logic [SWIDTH-1:0]         o_dq0_dfi_rddata_w0,
   output logic [SWIDTH-1:0]         o_dq0_dfi_rddata_w1,
   output logic [SWIDTH-1:0]         o_dq0_dfi_rddata_w2,
   output logic [SWIDTH-1:0]         o_dq0_dfi_rddata_w3,
   output logic [SWIDTH-1:0]         o_dq0_dfi_rddata_w4,
   output logic [SWIDTH-1:0]         o_dq0_dfi_rddata_w5,
   output logic [SWIDTH-1:0]         o_dq0_dfi_rddata_w6,
   output logic [SWIDTH-1:0]         o_dq0_dfi_rddata_w7,
   output logic [MWIDTH-1:0]         o_dq0_dfi_rddata_dbi_w0,
   output logic [MWIDTH-1:0]         o_dq0_dfi_rddata_dbi_w1,
   output logic [MWIDTH-1:0]         o_dq0_dfi_rddata_dbi_w2,
   output logic [MWIDTH-1:0]         o_dq0_dfi_rddata_dbi_w3,
   output logic [MWIDTH-1:0]         o_dq0_dfi_rddata_dbi_w4,
   output logic [MWIDTH-1:0]         o_dq0_dfi_rddata_dbi_w5,
   output logic [MWIDTH-1:0]         o_dq0_dfi_rddata_dbi_w6,
   output logic [MWIDTH-1:0]         o_dq0_dfi_rddata_dbi_w7,
   output logic [SWIDTH-1:0]         o_dq0_dfi_rddata_valid,
   input  logic [SWIDTH-1:0]         i_dq1_dfi_wrdata_p0,
   input  logic [SWIDTH-1:0]         i_dq1_dfi_wrdata_p1,
   input  logic [SWIDTH-1:0]         i_dq1_dfi_wrdata_p2,
   input  logic [SWIDTH-1:0]         i_dq1_dfi_wrdata_p3,
   input  logic [SWIDTH-1:0]         i_dq1_dfi_wrdata_p4,
   input  logic [SWIDTH-1:0]         i_dq1_dfi_wrdata_p5,
   input  logic [SWIDTH-1:0]         i_dq1_dfi_wrdata_p6,
   input  logic [SWIDTH-1:0]         i_dq1_dfi_wrdata_p7,
   input  logic [MWIDTH-1:0]         i_dq1_dfi_wrdata_mask_p0,
   input  logic [MWIDTH-1:0]         i_dq1_dfi_wrdata_mask_p1,
   input  logic [MWIDTH-1:0]         i_dq1_dfi_wrdata_mask_p2,
   input  logic [MWIDTH-1:0]         i_dq1_dfi_wrdata_mask_p3,
   input  logic [MWIDTH-1:0]         i_dq1_dfi_wrdata_mask_p4,
   input  logic [MWIDTH-1:0]         i_dq1_dfi_wrdata_mask_p5,
   input  logic [MWIDTH-1:0]         i_dq1_dfi_wrdata_mask_p6,
   input  logic [MWIDTH-1:0]         i_dq1_dfi_wrdata_mask_p7,
   input  logic                      i_dq1_dfi_wrdata_cs_p0,
   input  logic                      i_dq1_dfi_wrdata_cs_p1,
   input  logic                      i_dq1_dfi_wrdata_cs_p2,
   input  logic                      i_dq1_dfi_wrdata_cs_p3,
   input  logic                      i_dq1_dfi_wrdata_cs_p4,
   input  logic                      i_dq1_dfi_wrdata_cs_p5,
   input  logic                      i_dq1_dfi_wrdata_cs_p6,
   input  logic                      i_dq1_dfi_wrdata_cs_p7,
   input  logic                      i_dq1_dfi_wck_oe_p0,
   input  logic                      i_dq1_dfi_wck_oe_p1,
   input  logic                      i_dq1_dfi_wck_oe_p2,
   input  logic                      i_dq1_dfi_wck_oe_p3,
   input  logic                      i_dq1_dfi_wck_oe_p4,
   input  logic                      i_dq1_dfi_wck_oe_p5,
   input  logic                      i_dq1_dfi_wck_oe_p6,
   input  logic                      i_dq1_dfi_wck_oe_p7,
   input  logic                      i_dq1_dfi_wrdata_oe_p0,
   input  logic                      i_dq1_dfi_wrdata_oe_p1,
   input  logic                      i_dq1_dfi_wrdata_oe_p2,
   input  logic                      i_dq1_dfi_wrdata_oe_p3,
   input  logic                      i_dq1_dfi_wrdata_oe_p4,
   input  logic                      i_dq1_dfi_wrdata_oe_p5,
   input  logic                      i_dq1_dfi_wrdata_oe_p6,
   input  logic                      i_dq1_dfi_wrdata_oe_p7,
   input  logic                      i_dq1_dfi_parity_in_p0,
   input  logic                      i_dq1_dfi_parity_in_p1,
   input  logic                      i_dq1_dfi_parity_in_p2,
   input  logic                      i_dq1_dfi_parity_in_p3,
   input  logic                      i_dq1_dfi_parity_in_p4,
   input  logic                      i_dq1_dfi_parity_in_p5,
   input  logic                      i_dq1_dfi_parity_in_p6,
   input  logic                      i_dq1_dfi_parity_in_p7,
   input  logic                      i_dq1_dfi_wck_ten_p0,
   input  logic                      i_dq1_dfi_wck_ten_p1,
   input  logic                      i_dq1_dfi_wck_ten_p2,
   input  logic                      i_dq1_dfi_wck_ten_p3,
   input  logic                      i_dq1_dfi_wck_ten_p4,
   input  logic                      i_dq1_dfi_wck_ten_p5,
   input  logic                      i_dq1_dfi_wck_ten_p6,
   input  logic                      i_dq1_dfi_wck_ten_p7,
   input  logic                      i_dq1_dfi_rddata_cs_p0,
   input  logic                      i_dq1_dfi_rddata_cs_p1,
   input  logic                      i_dq1_dfi_rddata_cs_p2,
   input  logic                      i_dq1_dfi_rddata_cs_p3,
   input  logic                      i_dq1_dfi_rddata_cs_p4,
   input  logic                      i_dq1_dfi_rddata_cs_p5,
   input  logic                      i_dq1_dfi_rddata_cs_p6,
   input  logic                      i_dq1_dfi_rddata_cs_p7,
   input  logic                      i_dq1_dfi_rddata_ie_p0,
   input  logic                      i_dq1_dfi_rddata_ie_p1,
   input  logic                      i_dq1_dfi_rddata_ie_p2,
   input  logic                      i_dq1_dfi_rddata_ie_p3,
   input  logic                      i_dq1_dfi_rddata_ie_p4,
   input  logic                      i_dq1_dfi_rddata_ie_p5,
   input  logic                      i_dq1_dfi_rddata_ie_p6,
   input  logic                      i_dq1_dfi_rddata_ie_p7,
   input  logic                      i_dq1_dfi_rddata_re_p0,
   input  logic                      i_dq1_dfi_rddata_re_p1,
   input  logic                      i_dq1_dfi_rddata_re_p2,
   input  logic                      i_dq1_dfi_rddata_re_p3,
   input  logic                      i_dq1_dfi_rddata_re_p4,
   input  logic                      i_dq1_dfi_rddata_re_p5,
   input  logic                      i_dq1_dfi_rddata_re_p6,
   input  logic                      i_dq1_dfi_rddata_re_p7,
   input  logic                      i_dq1_dfi_rddata_en_p0,
   input  logic                      i_dq1_dfi_rddata_en_p1,
   input  logic                      i_dq1_dfi_rddata_en_p2,
   input  logic                      i_dq1_dfi_rddata_en_p3,
   input  logic                      i_dq1_dfi_rddata_en_p4,
   input  logic                      i_dq1_dfi_rddata_en_p5,
   input  logic                      i_dq1_dfi_rddata_en_p6,
   input  logic                      i_dq1_dfi_rddata_en_p7,
   output logic [SWIDTH-1:0]         o_dq1_dfi_rddata_w0,
   output logic [SWIDTH-1:0]         o_dq1_dfi_rddata_w1,
   output logic [SWIDTH-1:0]         o_dq1_dfi_rddata_w2,
   output logic [SWIDTH-1:0]         o_dq1_dfi_rddata_w3,
   output logic [SWIDTH-1:0]         o_dq1_dfi_rddata_w4,
   output logic [SWIDTH-1:0]         o_dq1_dfi_rddata_w5,
   output logic [SWIDTH-1:0]         o_dq1_dfi_rddata_w6,
   output logic [SWIDTH-1:0]         o_dq1_dfi_rddata_w7,
   output logic [MWIDTH-1:0]         o_dq1_dfi_rddata_dbi_w0,
   output logic [MWIDTH-1:0]         o_dq1_dfi_rddata_dbi_w1,
   output logic [MWIDTH-1:0]         o_dq1_dfi_rddata_dbi_w2,
   output logic [MWIDTH-1:0]         o_dq1_dfi_rddata_dbi_w3,
   output logic [MWIDTH-1:0]         o_dq1_dfi_rddata_dbi_w4,
   output logic [MWIDTH-1:0]         o_dq1_dfi_rddata_dbi_w5,
   output logic [MWIDTH-1:0]         o_dq1_dfi_rddata_dbi_w6,
   output logic [MWIDTH-1:0]         o_dq1_dfi_rddata_dbi_w7,
   output logic [SWIDTH-1:0]         o_dq1_dfi_rddata_valid,

   // Internal (PHY) interface
   output logic [DQ_WWIDTH-1:0]     o_dq0_sdr,
   input  logic [DQ_RWIDTH-1:0]     i_dq0_sdr,
   input  logic [DQ_WIDTH-1:0]      i_dq0_sdr_vld,
   output logic [DQS_WWIDTH-1:0]    o_dqs0_sdr,
   output logic [DQ_WWIDTH-1:0]     o_dq1_sdr,
   input  logic [DQ_RWIDTH-1:0]     i_dq1_sdr,
   input  logic [DQ_WIDTH-1:0]      i_dq1_sdr_vld,
   output logic [DQS_WWIDTH-1:0]    o_dqs1_sdr,

   // External interface
   input  logic                     i_txrx_mode,
   input  logic [DQ_WWIDTH-1:0]     i_tx0_sdr,
   input  logic [DQS_WWIDTH-1:0]    i_tx_ck0_sdr,
   output logic [DQ_RWIDTH-1:0]     o_rx0_sdr,
   output logic [DQ_WIDTH-1:0]      o_rx0_sdr_vld,
   input  logic [DQ_WWIDTH-1:0]     i_tx1_sdr,
   input  logic [DQS_WWIDTH-1:0]    i_tx_ck1_sdr,
   output logic [DQ_RWIDTH-1:0]     o_rx1_sdr,
   output logic [DQ_WIDTH-1:0]      o_rx1_sdr_vld,

   output logic [CA_WWIDTH-1:0]     o_ca_sdr,
   input  logic [CA_RWIDTH-1:0]     i_ca_sdr,
   input  logic [CA_WIDTH-1:0]      i_ca_sdr_vld,
   output logic [CK_WWIDTH-1:0]     o_ck_sdr

);

   // ------------------------------------------------------------------------
   // Datapath Bus Assignment
   // ------------------------------------------------------------------------

   logic [DQ_WWIDTH-1:0]  tx_dq0_sdr;
   logic [DQ_WWIDTH-1:0]  int_tx_dq0_sdr;
   logic [DQS_WWIDTH-1:0] int_tx_dqs0_sdr;

   // DQ Transmitter
   assign tx_dq0_sdr = {
                    {i_dq0_dfi_wrdata_mask_p7,i_dq0_dfi_wrdata_p7},
                    {i_dq0_dfi_wrdata_mask_p6,i_dq0_dfi_wrdata_p6},
                    {i_dq0_dfi_wrdata_mask_p5,i_dq0_dfi_wrdata_p5},
                    {i_dq0_dfi_wrdata_mask_p4,i_dq0_dfi_wrdata_p4},
                    {i_dq0_dfi_wrdata_mask_p3,i_dq0_dfi_wrdata_p3},
                    {i_dq0_dfi_wrdata_mask_p2,i_dq0_dfi_wrdata_p2},
                    {i_dq0_dfi_wrdata_mask_p1,i_dq0_dfi_wrdata_p1},
                    {i_dq0_dfi_wrdata_mask_p0,i_dq0_dfi_wrdata_p0}
                   };

   // Convert to Words-Of-Phases (WOP) format
   //    Pn[Wn...W0]...P0[Wn...W0] -> Wn[Pn...P0]...W0[Pn...P0]
   ddr_dp_pow2wop #(.WIDTH(DQ_WIDTH), .NUM_PH(NUM_WPH)) u_dq0_tx_pow2wop (.i_d(tx_dq0_sdr),.o_d(int_tx_dq0_sdr));

   // External vs DFI mode select
   assign o_dq0_sdr = i_txrx_mode ? i_tx0_sdr : int_tx_dq0_sdr;

   logic [DQ_RWIDTH-1:0] rx_dq0_sdr;

   // Convert to Phases-Of-Words (POW) format
   //    Wn[Pn...P0]...W0[Pn...P0] -> Pn[Wn...W0]...P0[Wn...W0]
   ddr_dp_wop2pow #(.WIDTH(DQ_WIDTH), .NUM_PH(NUM_RPH)) u_dq0_rx_wop2pow (.i_d(i_dq0_sdr),.o_d(rx_dq0_sdr));

   // Pass External data - no format change required
   assign o_rx0_sdr = i_dq0_sdr;

   // DQ Receiver
   assign {
           {o_dq0_dfi_rddata_dbi_w7,o_dq0_dfi_rddata_w7},
           {o_dq0_dfi_rddata_dbi_w6,o_dq0_dfi_rddata_w6},
           {o_dq0_dfi_rddata_dbi_w5,o_dq0_dfi_rddata_w5},
           {o_dq0_dfi_rddata_dbi_w4,o_dq0_dfi_rddata_w4},
           {o_dq0_dfi_rddata_dbi_w3,o_dq0_dfi_rddata_w3},
           {o_dq0_dfi_rddata_dbi_w2,o_dq0_dfi_rddata_w2},
           {o_dq0_dfi_rddata_dbi_w1,o_dq0_dfi_rddata_w1},
           {o_dq0_dfi_rddata_dbi_w0,o_dq0_dfi_rddata_w0}
          } = rx_dq0_sdr;

   assign o_dq0_dfi_rddata_valid = i_dq0_sdr_vld;

   // Pass Exteranl data - no format change required
   assign o_rx0_sdr_vld = i_dq0_sdr_vld;

   logic [DQS_WIDTH-1:0] dq0_dqs_sdr_p0;
   logic [DQS_WIDTH-1:0] dq0_dqs_sdr_p1;
   logic [DQS_WIDTH-1:0] dq0_dqs_sdr_p2;
   logic [DQS_WIDTH-1:0] dq0_dqs_sdr_p3;
   logic [DQS_WIDTH-1:0] dq0_dqs_sdr_p4;
   logic [DQS_WIDTH-1:0] dq0_dqs_sdr_p5;
   logic [DQS_WIDTH-1:0] dq0_dqs_sdr_p6;
   logic [DQS_WIDTH-1:0] dq0_dqs_sdr_p7;

   // Map DQ control bits into the DQS bus
   assign dq0_dqs_sdr_p0[`DDR_DQS_RCS_IDX   ] = i_dq0_dfi_rddata_cs_p0;
   assign dq0_dqs_sdr_p0[`DDR_DQS_WCS_IDX   ] = i_dq0_dfi_wrdata_cs_p0;
   assign dq0_dqs_sdr_p0[`DDR_DQS_WCK_OE_IDX] = i_dq0_dfi_wck_oe_p0;
   assign dq0_dqs_sdr_p0[`DDR_DQS_RE_IDX    ] = i_dq0_dfi_rddata_re_p0;
   assign dq0_dqs_sdr_p0[`DDR_DQS_IE_IDX    ] = i_dq0_dfi_rddata_ie_p0;
   assign dq0_dqs_sdr_p0[`DDR_DQS_OE_IDX    ] = i_dq0_dfi_wrdata_oe_p0;
   assign dq0_dqs_sdr_p0[`DDR_DQS_REN_IDX   ] = i_dq0_dfi_rddata_en_p0;
   assign dq0_dqs_sdr_p0[`DDR_DQS_DQS_IDX   ] = i_dq0_dfi_parity_in_p0;       // Use as a clock in LP4x mode and a write parity in LP5 mode.
   assign dq0_dqs_sdr_p0[`DDR_DQS_WCK_IDX   ] = i_dq0_dfi_wck_ten_p0;         // Not used in LP4x mode and used as WCK in LP5 mode
   assign dq0_dqs_sdr_p1[`DDR_DQS_RCS_IDX   ] = i_dq0_dfi_rddata_cs_p1;
   assign dq0_dqs_sdr_p1[`DDR_DQS_WCS_IDX   ] = i_dq0_dfi_wrdata_cs_p1;
   assign dq0_dqs_sdr_p1[`DDR_DQS_WCK_OE_IDX] = i_dq0_dfi_wck_oe_p1;
   assign dq0_dqs_sdr_p1[`DDR_DQS_RE_IDX    ] = i_dq0_dfi_rddata_re_p1;
   assign dq0_dqs_sdr_p1[`DDR_DQS_IE_IDX    ] = i_dq0_dfi_rddata_ie_p1;
   assign dq0_dqs_sdr_p1[`DDR_DQS_OE_IDX    ] = i_dq0_dfi_wrdata_oe_p1;
   assign dq0_dqs_sdr_p1[`DDR_DQS_REN_IDX   ] = i_dq0_dfi_rddata_en_p1;
   assign dq0_dqs_sdr_p1[`DDR_DQS_DQS_IDX   ] = i_dq0_dfi_parity_in_p1;       // Use as a clock in LP4x mode and a write parity in LP5 mode.
   assign dq0_dqs_sdr_p1[`DDR_DQS_WCK_IDX   ] = i_dq0_dfi_wck_ten_p1;         // Not used in LP4x mode and used as WCK in LP5 mode
   assign dq0_dqs_sdr_p2[`DDR_DQS_RCS_IDX   ] = i_dq0_dfi_rddata_cs_p2;
   assign dq0_dqs_sdr_p2[`DDR_DQS_WCS_IDX   ] = i_dq0_dfi_wrdata_cs_p2;
   assign dq0_dqs_sdr_p2[`DDR_DQS_WCK_OE_IDX] = i_dq0_dfi_wck_oe_p2;
   assign dq0_dqs_sdr_p2[`DDR_DQS_RE_IDX    ] = i_dq0_dfi_rddata_re_p2;
   assign dq0_dqs_sdr_p2[`DDR_DQS_IE_IDX    ] = i_dq0_dfi_rddata_ie_p2;
   assign dq0_dqs_sdr_p2[`DDR_DQS_OE_IDX    ] = i_dq0_dfi_wrdata_oe_p2;
   assign dq0_dqs_sdr_p2[`DDR_DQS_REN_IDX   ] = i_dq0_dfi_rddata_en_p2;
   assign dq0_dqs_sdr_p2[`DDR_DQS_DQS_IDX   ] = i_dq0_dfi_parity_in_p2;       // Use as a clock in LP4x mode and a write parity in LP5 mode.
   assign dq0_dqs_sdr_p2[`DDR_DQS_WCK_IDX   ] = i_dq0_dfi_wck_ten_p2;         // Not used in LP4x mode and used as WCK in LP5 mode
   assign dq0_dqs_sdr_p3[`DDR_DQS_RCS_IDX   ] = i_dq0_dfi_rddata_cs_p3;
   assign dq0_dqs_sdr_p3[`DDR_DQS_WCS_IDX   ] = i_dq0_dfi_wrdata_cs_p3;
   assign dq0_dqs_sdr_p3[`DDR_DQS_WCK_OE_IDX] = i_dq0_dfi_wck_oe_p3;
   assign dq0_dqs_sdr_p3[`DDR_DQS_RE_IDX    ] = i_dq0_dfi_rddata_re_p3;
   assign dq0_dqs_sdr_p3[`DDR_DQS_IE_IDX    ] = i_dq0_dfi_rddata_ie_p3;
   assign dq0_dqs_sdr_p3[`DDR_DQS_OE_IDX    ] = i_dq0_dfi_wrdata_oe_p3;
   assign dq0_dqs_sdr_p3[`DDR_DQS_REN_IDX   ] = i_dq0_dfi_rddata_en_p3;
   assign dq0_dqs_sdr_p3[`DDR_DQS_DQS_IDX   ] = i_dq0_dfi_parity_in_p3;       // Use as a clock in LP4x mode and a write parity in LP5 mode.
   assign dq0_dqs_sdr_p3[`DDR_DQS_WCK_IDX   ] = i_dq0_dfi_wck_ten_p3;         // Not used in LP4x mode and used as WCK in LP5 mode
   assign dq0_dqs_sdr_p4[`DDR_DQS_RCS_IDX   ] = i_dq0_dfi_rddata_cs_p4;
   assign dq0_dqs_sdr_p4[`DDR_DQS_WCS_IDX   ] = i_dq0_dfi_wrdata_cs_p4;
   assign dq0_dqs_sdr_p4[`DDR_DQS_WCK_OE_IDX] = i_dq0_dfi_wck_oe_p4;
   assign dq0_dqs_sdr_p4[`DDR_DQS_RE_IDX    ] = i_dq0_dfi_rddata_re_p4;
   assign dq0_dqs_sdr_p4[`DDR_DQS_IE_IDX    ] = i_dq0_dfi_rddata_ie_p4;
   assign dq0_dqs_sdr_p4[`DDR_DQS_OE_IDX    ] = i_dq0_dfi_wrdata_oe_p4;
   assign dq0_dqs_sdr_p4[`DDR_DQS_REN_IDX   ] = i_dq0_dfi_rddata_en_p4;
   assign dq0_dqs_sdr_p4[`DDR_DQS_DQS_IDX   ] = i_dq0_dfi_parity_in_p4;       // Use as a clock in LP4x mode and a write parity in LP5 mode.
   assign dq0_dqs_sdr_p4[`DDR_DQS_WCK_IDX   ] = i_dq0_dfi_wck_ten_p4;         // Not used in LP4x mode and used as WCK in LP5 mode
   assign dq0_dqs_sdr_p5[`DDR_DQS_RCS_IDX   ] = i_dq0_dfi_rddata_cs_p5;
   assign dq0_dqs_sdr_p5[`DDR_DQS_WCS_IDX   ] = i_dq0_dfi_wrdata_cs_p5;
   assign dq0_dqs_sdr_p5[`DDR_DQS_WCK_OE_IDX] = i_dq0_dfi_wck_oe_p5;
   assign dq0_dqs_sdr_p5[`DDR_DQS_RE_IDX    ] = i_dq0_dfi_rddata_re_p5;
   assign dq0_dqs_sdr_p5[`DDR_DQS_IE_IDX    ] = i_dq0_dfi_rddata_ie_p5;
   assign dq0_dqs_sdr_p5[`DDR_DQS_OE_IDX    ] = i_dq0_dfi_wrdata_oe_p5;
   assign dq0_dqs_sdr_p5[`DDR_DQS_REN_IDX   ] = i_dq0_dfi_rddata_en_p5;
   assign dq0_dqs_sdr_p5[`DDR_DQS_DQS_IDX   ] = i_dq0_dfi_parity_in_p5;       // Use as a clock in LP4x mode and a write parity in LP5 mode.
   assign dq0_dqs_sdr_p5[`DDR_DQS_WCK_IDX   ] = i_dq0_dfi_wck_ten_p5;         // Not used in LP4x mode and used as WCK in LP5 mode
   assign dq0_dqs_sdr_p6[`DDR_DQS_RCS_IDX   ] = i_dq0_dfi_rddata_cs_p6;
   assign dq0_dqs_sdr_p6[`DDR_DQS_WCS_IDX   ] = i_dq0_dfi_wrdata_cs_p6;
   assign dq0_dqs_sdr_p6[`DDR_DQS_WCK_OE_IDX] = i_dq0_dfi_wck_oe_p6;
   assign dq0_dqs_sdr_p6[`DDR_DQS_RE_IDX    ] = i_dq0_dfi_rddata_re_p6;
   assign dq0_dqs_sdr_p6[`DDR_DQS_IE_IDX    ] = i_dq0_dfi_rddata_ie_p6;
   assign dq0_dqs_sdr_p6[`DDR_DQS_OE_IDX    ] = i_dq0_dfi_wrdata_oe_p6;
   assign dq0_dqs_sdr_p6[`DDR_DQS_REN_IDX   ] = i_dq0_dfi_rddata_en_p6;
   assign dq0_dqs_sdr_p6[`DDR_DQS_DQS_IDX   ] = i_dq0_dfi_parity_in_p6;       // Use as a clock in LP4x mode and a write parity in LP5 mode.
   assign dq0_dqs_sdr_p6[`DDR_DQS_WCK_IDX   ] = i_dq0_dfi_wck_ten_p6;         // Not used in LP4x mode and used as WCK in LP5 mode
   assign dq0_dqs_sdr_p7[`DDR_DQS_RCS_IDX   ] = i_dq0_dfi_rddata_cs_p7;
   assign dq0_dqs_sdr_p7[`DDR_DQS_WCS_IDX   ] = i_dq0_dfi_wrdata_cs_p7;
   assign dq0_dqs_sdr_p7[`DDR_DQS_WCK_OE_IDX] = i_dq0_dfi_wck_oe_p7;
   assign dq0_dqs_sdr_p7[`DDR_DQS_RE_IDX    ] = i_dq0_dfi_rddata_re_p7;
   assign dq0_dqs_sdr_p7[`DDR_DQS_IE_IDX    ] = i_dq0_dfi_rddata_ie_p7;
   assign dq0_dqs_sdr_p7[`DDR_DQS_OE_IDX    ] = i_dq0_dfi_wrdata_oe_p7;
   assign dq0_dqs_sdr_p7[`DDR_DQS_REN_IDX   ] = i_dq0_dfi_rddata_en_p7;
   assign dq0_dqs_sdr_p7[`DDR_DQS_DQS_IDX   ] = i_dq0_dfi_parity_in_p7;       // Use as a clock in LP4x mode and a write parity in LP5 mode.
   assign dq0_dqs_sdr_p7[`DDR_DQS_WCK_IDX   ] = i_dq0_dfi_wck_ten_p7;         // Not used in LP4x mode and used as WCK in LP5 mode

   logic [DQS_WWIDTH-1:0] tx_dqs0_sdr;

   // DQS Transmitter
   assign tx_dqs0_sdr = {
                        dq0_dqs_sdr_p7,
                        dq0_dqs_sdr_p6,
                        dq0_dqs_sdr_p5,
                        dq0_dqs_sdr_p4,
                        dq0_dqs_sdr_p3,
                        dq0_dqs_sdr_p2,
                        dq0_dqs_sdr_p1,
                        dq0_dqs_sdr_p0
                       };

   // Convert to Words-Of-Phases (WOP) format
   //    Pn[Wn...W0]...P0[Wn...W0] -> Wn[Pn...P0]...W0[Pn...P0]
   ddr_dp_pow2wop #(.WIDTH(DQS_WIDTH), .NUM_PH(NUM_WPH)) u_dqs0_tx_pow2wop (.i_d(tx_dqs0_sdr),.o_d(int_tx_dqs0_sdr));

   // External vs DFI mode select
   assign o_dqs0_sdr = i_txrx_mode ? i_tx_ck0_sdr : int_tx_dqs0_sdr;
   logic [DQ_WWIDTH-1:0]  tx_dq1_sdr;
   logic [DQ_WWIDTH-1:0]  int_tx_dq1_sdr;
   logic [DQS_WWIDTH-1:0] int_tx_dqs1_sdr;

   // DQ Transmitter
   assign tx_dq1_sdr = {
                    {i_dq1_dfi_wrdata_mask_p7,i_dq1_dfi_wrdata_p7},
                    {i_dq1_dfi_wrdata_mask_p6,i_dq1_dfi_wrdata_p6},
                    {i_dq1_dfi_wrdata_mask_p5,i_dq1_dfi_wrdata_p5},
                    {i_dq1_dfi_wrdata_mask_p4,i_dq1_dfi_wrdata_p4},
                    {i_dq1_dfi_wrdata_mask_p3,i_dq1_dfi_wrdata_p3},
                    {i_dq1_dfi_wrdata_mask_p2,i_dq1_dfi_wrdata_p2},
                    {i_dq1_dfi_wrdata_mask_p1,i_dq1_dfi_wrdata_p1},
                    {i_dq1_dfi_wrdata_mask_p0,i_dq1_dfi_wrdata_p0}
                   };

   // Convert to Words-Of-Phases (WOP) format
   //    Pn[Wn...W0]...P0[Wn...W0] -> Wn[Pn...P0]...W0[Pn...P0]
   ddr_dp_pow2wop #(.WIDTH(DQ_WIDTH), .NUM_PH(NUM_WPH)) u_dq1_tx_pow2wop (.i_d(tx_dq1_sdr),.o_d(int_tx_dq1_sdr));

   // External vs DFI mode select
   assign o_dq1_sdr = i_txrx_mode ? i_tx1_sdr : int_tx_dq1_sdr;

   logic [DQ_RWIDTH-1:0] rx_dq1_sdr;

   // Convert to Phases-Of-Words (POW) format
   //    Wn[Pn...P0]...W0[Pn...P0] -> Pn[Wn...W0]...P0[Wn...W0]
   ddr_dp_wop2pow #(.WIDTH(DQ_WIDTH), .NUM_PH(NUM_RPH)) u_dq1_rx_wop2pow (.i_d(i_dq1_sdr),.o_d(rx_dq1_sdr));

   // Pass External data - no format change required
   assign o_rx1_sdr = i_dq1_sdr;

   // DQ Receiver
   assign {
           {o_dq1_dfi_rddata_dbi_w7,o_dq1_dfi_rddata_w7},
           {o_dq1_dfi_rddata_dbi_w6,o_dq1_dfi_rddata_w6},
           {o_dq1_dfi_rddata_dbi_w5,o_dq1_dfi_rddata_w5},
           {o_dq1_dfi_rddata_dbi_w4,o_dq1_dfi_rddata_w4},
           {o_dq1_dfi_rddata_dbi_w3,o_dq1_dfi_rddata_w3},
           {o_dq1_dfi_rddata_dbi_w2,o_dq1_dfi_rddata_w2},
           {o_dq1_dfi_rddata_dbi_w1,o_dq1_dfi_rddata_w1},
           {o_dq1_dfi_rddata_dbi_w0,o_dq1_dfi_rddata_w0}
          } = rx_dq1_sdr;

   assign o_dq1_dfi_rddata_valid = i_dq1_sdr_vld;

   // Pass Exteranl data - no format change required
   assign o_rx1_sdr_vld = i_dq1_sdr_vld;

   logic [DQS_WIDTH-1:0] dq1_dqs_sdr_p0;
   logic [DQS_WIDTH-1:0] dq1_dqs_sdr_p1;
   logic [DQS_WIDTH-1:0] dq1_dqs_sdr_p2;
   logic [DQS_WIDTH-1:0] dq1_dqs_sdr_p3;
   logic [DQS_WIDTH-1:0] dq1_dqs_sdr_p4;
   logic [DQS_WIDTH-1:0] dq1_dqs_sdr_p5;
   logic [DQS_WIDTH-1:0] dq1_dqs_sdr_p6;
   logic [DQS_WIDTH-1:0] dq1_dqs_sdr_p7;

   // Map DQ control bits into the DQS bus
   assign dq1_dqs_sdr_p0[`DDR_DQS_RCS_IDX   ] = i_dq1_dfi_rddata_cs_p0;
   assign dq1_dqs_sdr_p0[`DDR_DQS_WCS_IDX   ] = i_dq1_dfi_wrdata_cs_p0;
   assign dq1_dqs_sdr_p0[`DDR_DQS_WCK_OE_IDX] = i_dq1_dfi_wck_oe_p0;
   assign dq1_dqs_sdr_p0[`DDR_DQS_RE_IDX    ] = i_dq1_dfi_rddata_re_p0;
   assign dq1_dqs_sdr_p0[`DDR_DQS_IE_IDX    ] = i_dq1_dfi_rddata_ie_p0;
   assign dq1_dqs_sdr_p0[`DDR_DQS_OE_IDX    ] = i_dq1_dfi_wrdata_oe_p0;
   assign dq1_dqs_sdr_p0[`DDR_DQS_REN_IDX   ] = i_dq1_dfi_rddata_en_p0;
   assign dq1_dqs_sdr_p0[`DDR_DQS_DQS_IDX   ] = i_dq1_dfi_parity_in_p0;       // Use as a clock in LP4x mode and a write parity in LP5 mode.
   assign dq1_dqs_sdr_p0[`DDR_DQS_WCK_IDX   ] = i_dq1_dfi_wck_ten_p0;         // Not used in LP4x mode and used as WCK in LP5 mode
   assign dq1_dqs_sdr_p1[`DDR_DQS_RCS_IDX   ] = i_dq1_dfi_rddata_cs_p1;
   assign dq1_dqs_sdr_p1[`DDR_DQS_WCS_IDX   ] = i_dq1_dfi_wrdata_cs_p1;
   assign dq1_dqs_sdr_p1[`DDR_DQS_WCK_OE_IDX] = i_dq1_dfi_wck_oe_p1;
   assign dq1_dqs_sdr_p1[`DDR_DQS_RE_IDX    ] = i_dq1_dfi_rddata_re_p1;
   assign dq1_dqs_sdr_p1[`DDR_DQS_IE_IDX    ] = i_dq1_dfi_rddata_ie_p1;
   assign dq1_dqs_sdr_p1[`DDR_DQS_OE_IDX    ] = i_dq1_dfi_wrdata_oe_p1;
   assign dq1_dqs_sdr_p1[`DDR_DQS_REN_IDX   ] = i_dq1_dfi_rddata_en_p1;
   assign dq1_dqs_sdr_p1[`DDR_DQS_DQS_IDX   ] = i_dq1_dfi_parity_in_p1;       // Use as a clock in LP4x mode and a write parity in LP5 mode.
   assign dq1_dqs_sdr_p1[`DDR_DQS_WCK_IDX   ] = i_dq1_dfi_wck_ten_p1;         // Not used in LP4x mode and used as WCK in LP5 mode
   assign dq1_dqs_sdr_p2[`DDR_DQS_RCS_IDX   ] = i_dq1_dfi_rddata_cs_p2;
   assign dq1_dqs_sdr_p2[`DDR_DQS_WCS_IDX   ] = i_dq1_dfi_wrdata_cs_p2;
   assign dq1_dqs_sdr_p2[`DDR_DQS_WCK_OE_IDX] = i_dq1_dfi_wck_oe_p2;
   assign dq1_dqs_sdr_p2[`DDR_DQS_RE_IDX    ] = i_dq1_dfi_rddata_re_p2;
   assign dq1_dqs_sdr_p2[`DDR_DQS_IE_IDX    ] = i_dq1_dfi_rddata_ie_p2;
   assign dq1_dqs_sdr_p2[`DDR_DQS_OE_IDX    ] = i_dq1_dfi_wrdata_oe_p2;
   assign dq1_dqs_sdr_p2[`DDR_DQS_REN_IDX   ] = i_dq1_dfi_rddata_en_p2;
   assign dq1_dqs_sdr_p2[`DDR_DQS_DQS_IDX   ] = i_dq1_dfi_parity_in_p2;       // Use as a clock in LP4x mode and a write parity in LP5 mode.
   assign dq1_dqs_sdr_p2[`DDR_DQS_WCK_IDX   ] = i_dq1_dfi_wck_ten_p2;         // Not used in LP4x mode and used as WCK in LP5 mode
   assign dq1_dqs_sdr_p3[`DDR_DQS_RCS_IDX   ] = i_dq1_dfi_rddata_cs_p3;
   assign dq1_dqs_sdr_p3[`DDR_DQS_WCS_IDX   ] = i_dq1_dfi_wrdata_cs_p3;
   assign dq1_dqs_sdr_p3[`DDR_DQS_WCK_OE_IDX] = i_dq1_dfi_wck_oe_p3;
   assign dq1_dqs_sdr_p3[`DDR_DQS_RE_IDX    ] = i_dq1_dfi_rddata_re_p3;
   assign dq1_dqs_sdr_p3[`DDR_DQS_IE_IDX    ] = i_dq1_dfi_rddata_ie_p3;
   assign dq1_dqs_sdr_p3[`DDR_DQS_OE_IDX    ] = i_dq1_dfi_wrdata_oe_p3;
   assign dq1_dqs_sdr_p3[`DDR_DQS_REN_IDX   ] = i_dq1_dfi_rddata_en_p3;
   assign dq1_dqs_sdr_p3[`DDR_DQS_DQS_IDX   ] = i_dq1_dfi_parity_in_p3;       // Use as a clock in LP4x mode and a write parity in LP5 mode.
   assign dq1_dqs_sdr_p3[`DDR_DQS_WCK_IDX   ] = i_dq1_dfi_wck_ten_p3;         // Not used in LP4x mode and used as WCK in LP5 mode
   assign dq1_dqs_sdr_p4[`DDR_DQS_RCS_IDX   ] = i_dq1_dfi_rddata_cs_p4;
   assign dq1_dqs_sdr_p4[`DDR_DQS_WCS_IDX   ] = i_dq1_dfi_wrdata_cs_p4;
   assign dq1_dqs_sdr_p4[`DDR_DQS_WCK_OE_IDX] = i_dq1_dfi_wck_oe_p4;
   assign dq1_dqs_sdr_p4[`DDR_DQS_RE_IDX    ] = i_dq1_dfi_rddata_re_p4;
   assign dq1_dqs_sdr_p4[`DDR_DQS_IE_IDX    ] = i_dq1_dfi_rddata_ie_p4;
   assign dq1_dqs_sdr_p4[`DDR_DQS_OE_IDX    ] = i_dq1_dfi_wrdata_oe_p4;
   assign dq1_dqs_sdr_p4[`DDR_DQS_REN_IDX   ] = i_dq1_dfi_rddata_en_p4;
   assign dq1_dqs_sdr_p4[`DDR_DQS_DQS_IDX   ] = i_dq1_dfi_parity_in_p4;       // Use as a clock in LP4x mode and a write parity in LP5 mode.
   assign dq1_dqs_sdr_p4[`DDR_DQS_WCK_IDX   ] = i_dq1_dfi_wck_ten_p4;         // Not used in LP4x mode and used as WCK in LP5 mode
   assign dq1_dqs_sdr_p5[`DDR_DQS_RCS_IDX   ] = i_dq1_dfi_rddata_cs_p5;
   assign dq1_dqs_sdr_p5[`DDR_DQS_WCS_IDX   ] = i_dq1_dfi_wrdata_cs_p5;
   assign dq1_dqs_sdr_p5[`DDR_DQS_WCK_OE_IDX] = i_dq1_dfi_wck_oe_p5;
   assign dq1_dqs_sdr_p5[`DDR_DQS_RE_IDX    ] = i_dq1_dfi_rddata_re_p5;
   assign dq1_dqs_sdr_p5[`DDR_DQS_IE_IDX    ] = i_dq1_dfi_rddata_ie_p5;
   assign dq1_dqs_sdr_p5[`DDR_DQS_OE_IDX    ] = i_dq1_dfi_wrdata_oe_p5;
   assign dq1_dqs_sdr_p5[`DDR_DQS_REN_IDX   ] = i_dq1_dfi_rddata_en_p5;
   assign dq1_dqs_sdr_p5[`DDR_DQS_DQS_IDX   ] = i_dq1_dfi_parity_in_p5;       // Use as a clock in LP4x mode and a write parity in LP5 mode.
   assign dq1_dqs_sdr_p5[`DDR_DQS_WCK_IDX   ] = i_dq1_dfi_wck_ten_p5;         // Not used in LP4x mode and used as WCK in LP5 mode
   assign dq1_dqs_sdr_p6[`DDR_DQS_RCS_IDX   ] = i_dq1_dfi_rddata_cs_p6;
   assign dq1_dqs_sdr_p6[`DDR_DQS_WCS_IDX   ] = i_dq1_dfi_wrdata_cs_p6;
   assign dq1_dqs_sdr_p6[`DDR_DQS_WCK_OE_IDX] = i_dq1_dfi_wck_oe_p6;
   assign dq1_dqs_sdr_p6[`DDR_DQS_RE_IDX    ] = i_dq1_dfi_rddata_re_p6;
   assign dq1_dqs_sdr_p6[`DDR_DQS_IE_IDX    ] = i_dq1_dfi_rddata_ie_p6;
   assign dq1_dqs_sdr_p6[`DDR_DQS_OE_IDX    ] = i_dq1_dfi_wrdata_oe_p6;
   assign dq1_dqs_sdr_p6[`DDR_DQS_REN_IDX   ] = i_dq1_dfi_rddata_en_p6;
   assign dq1_dqs_sdr_p6[`DDR_DQS_DQS_IDX   ] = i_dq1_dfi_parity_in_p6;       // Use as a clock in LP4x mode and a write parity in LP5 mode.
   assign dq1_dqs_sdr_p6[`DDR_DQS_WCK_IDX   ] = i_dq1_dfi_wck_ten_p6;         // Not used in LP4x mode and used as WCK in LP5 mode
   assign dq1_dqs_sdr_p7[`DDR_DQS_RCS_IDX   ] = i_dq1_dfi_rddata_cs_p7;
   assign dq1_dqs_sdr_p7[`DDR_DQS_WCS_IDX   ] = i_dq1_dfi_wrdata_cs_p7;
   assign dq1_dqs_sdr_p7[`DDR_DQS_WCK_OE_IDX] = i_dq1_dfi_wck_oe_p7;
   assign dq1_dqs_sdr_p7[`DDR_DQS_RE_IDX    ] = i_dq1_dfi_rddata_re_p7;
   assign dq1_dqs_sdr_p7[`DDR_DQS_IE_IDX    ] = i_dq1_dfi_rddata_ie_p7;
   assign dq1_dqs_sdr_p7[`DDR_DQS_OE_IDX    ] = i_dq1_dfi_wrdata_oe_p7;
   assign dq1_dqs_sdr_p7[`DDR_DQS_REN_IDX   ] = i_dq1_dfi_rddata_en_p7;
   assign dq1_dqs_sdr_p7[`DDR_DQS_DQS_IDX   ] = i_dq1_dfi_parity_in_p7;       // Use as a clock in LP4x mode and a write parity in LP5 mode.
   assign dq1_dqs_sdr_p7[`DDR_DQS_WCK_IDX   ] = i_dq1_dfi_wck_ten_p7;         // Not used in LP4x mode and used as WCK in LP5 mode

   logic [DQS_WWIDTH-1:0] tx_dqs1_sdr;

   // DQS Transmitter
   assign tx_dqs1_sdr = {
                        dq1_dqs_sdr_p7,
                        dq1_dqs_sdr_p6,
                        dq1_dqs_sdr_p5,
                        dq1_dqs_sdr_p4,
                        dq1_dqs_sdr_p3,
                        dq1_dqs_sdr_p2,
                        dq1_dqs_sdr_p1,
                        dq1_dqs_sdr_p0
                       };

   // Convert to Words-Of-Phases (WOP) format
   //    Pn[Wn...W0]...P0[Wn...W0] -> Wn[Pn...P0]...W0[Pn...P0]
   ddr_dp_pow2wop #(.WIDTH(DQS_WIDTH), .NUM_PH(NUM_WPH)) u_dqs1_tx_pow2wop (.i_d(tx_dqs1_sdr),.o_d(int_tx_dqs1_sdr));

   // External vs DFI mode select
   assign o_dqs1_sdr = i_txrx_mode ? i_tx_ck1_sdr : int_tx_dqs1_sdr;

   logic [CA_WWIDTH-1:0] tx_ca_sdr;

   // CA Transmitter
   assign tx_ca_sdr = {
                       {i_dfi_cke_p7, i_dfi_cs_p7, i_dfi_address_p7},
                       {i_dfi_cke_p6, i_dfi_cs_p6, i_dfi_address_p6},
                       {i_dfi_cke_p5, i_dfi_cs_p5, i_dfi_address_p5},
                       {i_dfi_cke_p4, i_dfi_cs_p4, i_dfi_address_p4},
                       {i_dfi_cke_p3, i_dfi_cs_p3, i_dfi_address_p3},
                       {i_dfi_cke_p2, i_dfi_cs_p2, i_dfi_address_p2},
                       {i_dfi_cke_p1, i_dfi_cs_p1, i_dfi_address_p1},
                       {i_dfi_cke_p0, i_dfi_cs_p0, i_dfi_address_p0}
                      };

   // Convert to Words-Of-Phases (WOP) format
   //    Pn[Wn...W0]...P0[Wn...W0] -> Wn[Pn...P0]...W0[Pn...P0]
   ddr_dp_pow2wop #(.WIDTH(CA_WIDTH), .NUM_PH(NUM_WPH)) u_ca_tx_pow2wop (.i_d(tx_ca_sdr),.o_d(o_ca_sdr));

   logic [CA_RWIDTH-1:0] rx_ca_sdr;

   // Convert to Phases-Of-Words (POW) format
   //    Wn[Pn...P0]...W0[Pn...P0] -> Pn[Wn...W0]...P0[Wn...W0]
   ddr_dp_wop2pow #(.WIDTH(CA_WIDTH), .NUM_PH(NUM_RPH)) u_ca_rx_wop2pow (.i_d(i_ca_sdr),.o_d(rx_ca_sdr));

   // CA Receiver
   assign {
           {o_dfi_cke_w7, o_dfi_cs_w7, o_dfi_address_w7},
           {o_dfi_cke_w6, o_dfi_cs_w6, o_dfi_address_w6},
           {o_dfi_cke_w5, o_dfi_cs_w5, o_dfi_address_w5},
           {o_dfi_cke_w4, o_dfi_cs_w4, o_dfi_address_w4},
           {o_dfi_cke_w3, o_dfi_cs_w3, o_dfi_address_w3},
           {o_dfi_cke_w2, o_dfi_cs_w2, o_dfi_address_w2},
           {o_dfi_cke_w1, o_dfi_cs_w1, o_dfi_address_w1},
           {o_dfi_cke_w0, o_dfi_cs_w0, o_dfi_address_w0}
          } = rx_ca_sdr;

   assign o_dfi_address_valid = i_ca_sdr_vld;

   logic [CK_WIDTH-1:0] ca_ck_sdr_p0;
   logic [CK_WIDTH-1:0] ca_ck_sdr_p1;
   logic [CK_WIDTH-1:0] ca_ck_sdr_p2;
   logic [CK_WIDTH-1:0] ca_ck_sdr_p3;
   logic [CK_WIDTH-1:0] ca_ck_sdr_p4;
   logic [CK_WIDTH-1:0] ca_ck_sdr_p5;
   logic [CK_WIDTH-1:0] ca_ck_sdr_p6;
   logic [CK_WIDTH-1:0] ca_ck_sdr_p7;

   // Map CK control bits into the DQS bus
   assign ca_ck_sdr_p0[`DDR_DQS_RCS_IDX   ] = 'b0;
   assign ca_ck_sdr_p0[`DDR_DQS_WCS_IDX   ] = 'b0;
   assign ca_ck_sdr_p0[`DDR_DQS_WCK_OE_IDX] = 'b1;
   assign ca_ck_sdr_p0[`DDR_DQS_IE_IDX    ] = 'b1;
   assign ca_ck_sdr_p0[`DDR_DQS_OE_IDX    ] = 'b1;
   assign ca_ck_sdr_p0[`DDR_DQS_RE_IDX    ] = 'b1;
   assign ca_ck_sdr_p0[`DDR_DQS_REN_IDX   ] = i_dfi_carddata_en_p0 ;
   assign ca_ck_sdr_p0[`DDR_DQS_DQS_IDX   ] = 'b0;
   assign ca_ck_sdr_p0[`DDR_DQS_WCK_IDX   ] = i_dfi_dram_clk_enable_p0;
   assign ca_ck_sdr_p1[`DDR_DQS_RCS_IDX   ] = 'b0;
   assign ca_ck_sdr_p1[`DDR_DQS_WCS_IDX   ] = 'b0;
   assign ca_ck_sdr_p1[`DDR_DQS_WCK_OE_IDX] = 'b1;
   assign ca_ck_sdr_p1[`DDR_DQS_IE_IDX    ] = 'b1;
   assign ca_ck_sdr_p1[`DDR_DQS_OE_IDX    ] = 'b1;
   assign ca_ck_sdr_p1[`DDR_DQS_RE_IDX    ] = 'b1;
   assign ca_ck_sdr_p1[`DDR_DQS_REN_IDX   ] = i_dfi_carddata_en_p1 ;
   assign ca_ck_sdr_p1[`DDR_DQS_DQS_IDX   ] = 'b0;
   assign ca_ck_sdr_p1[`DDR_DQS_WCK_IDX   ] = i_dfi_dram_clk_enable_p1;
   assign ca_ck_sdr_p2[`DDR_DQS_RCS_IDX   ] = 'b0;
   assign ca_ck_sdr_p2[`DDR_DQS_WCS_IDX   ] = 'b0;
   assign ca_ck_sdr_p2[`DDR_DQS_WCK_OE_IDX] = 'b1;
   assign ca_ck_sdr_p2[`DDR_DQS_IE_IDX    ] = 'b1;
   assign ca_ck_sdr_p2[`DDR_DQS_OE_IDX    ] = 'b1;
   assign ca_ck_sdr_p2[`DDR_DQS_RE_IDX    ] = 'b1;
   assign ca_ck_sdr_p2[`DDR_DQS_REN_IDX   ] = i_dfi_carddata_en_p2 ;
   assign ca_ck_sdr_p2[`DDR_DQS_DQS_IDX   ] = 'b0;
   assign ca_ck_sdr_p2[`DDR_DQS_WCK_IDX   ] = i_dfi_dram_clk_enable_p2;
   assign ca_ck_sdr_p3[`DDR_DQS_RCS_IDX   ] = 'b0;
   assign ca_ck_sdr_p3[`DDR_DQS_WCS_IDX   ] = 'b0;
   assign ca_ck_sdr_p3[`DDR_DQS_WCK_OE_IDX] = 'b1;
   assign ca_ck_sdr_p3[`DDR_DQS_IE_IDX    ] = 'b1;
   assign ca_ck_sdr_p3[`DDR_DQS_OE_IDX    ] = 'b1;
   assign ca_ck_sdr_p3[`DDR_DQS_RE_IDX    ] = 'b1;
   assign ca_ck_sdr_p3[`DDR_DQS_REN_IDX   ] = i_dfi_carddata_en_p3 ;
   assign ca_ck_sdr_p3[`DDR_DQS_DQS_IDX   ] = 'b0;
   assign ca_ck_sdr_p3[`DDR_DQS_WCK_IDX   ] = i_dfi_dram_clk_enable_p3;
   assign ca_ck_sdr_p4[`DDR_DQS_RCS_IDX   ] = 'b0;
   assign ca_ck_sdr_p4[`DDR_DQS_WCS_IDX   ] = 'b0;
   assign ca_ck_sdr_p4[`DDR_DQS_WCK_OE_IDX] = 'b1;
   assign ca_ck_sdr_p4[`DDR_DQS_IE_IDX    ] = 'b1;
   assign ca_ck_sdr_p4[`DDR_DQS_OE_IDX    ] = 'b1;
   assign ca_ck_sdr_p4[`DDR_DQS_RE_IDX    ] = 'b1;
   assign ca_ck_sdr_p4[`DDR_DQS_REN_IDX   ] = i_dfi_carddata_en_p4 ;
   assign ca_ck_sdr_p4[`DDR_DQS_DQS_IDX   ] = 'b0;
   assign ca_ck_sdr_p4[`DDR_DQS_WCK_IDX   ] = i_dfi_dram_clk_enable_p4;
   assign ca_ck_sdr_p5[`DDR_DQS_RCS_IDX   ] = 'b0;
   assign ca_ck_sdr_p5[`DDR_DQS_WCS_IDX   ] = 'b0;
   assign ca_ck_sdr_p5[`DDR_DQS_WCK_OE_IDX] = 'b1;
   assign ca_ck_sdr_p5[`DDR_DQS_IE_IDX    ] = 'b1;
   assign ca_ck_sdr_p5[`DDR_DQS_OE_IDX    ] = 'b1;
   assign ca_ck_sdr_p5[`DDR_DQS_RE_IDX    ] = 'b1;
   assign ca_ck_sdr_p5[`DDR_DQS_REN_IDX   ] = i_dfi_carddata_en_p5 ;
   assign ca_ck_sdr_p5[`DDR_DQS_DQS_IDX   ] = 'b0;
   assign ca_ck_sdr_p5[`DDR_DQS_WCK_IDX   ] = i_dfi_dram_clk_enable_p5;
   assign ca_ck_sdr_p6[`DDR_DQS_RCS_IDX   ] = 'b0;
   assign ca_ck_sdr_p6[`DDR_DQS_WCS_IDX   ] = 'b0;
   assign ca_ck_sdr_p6[`DDR_DQS_WCK_OE_IDX] = 'b1;
   assign ca_ck_sdr_p6[`DDR_DQS_IE_IDX    ] = 'b1;
   assign ca_ck_sdr_p6[`DDR_DQS_OE_IDX    ] = 'b1;
   assign ca_ck_sdr_p6[`DDR_DQS_RE_IDX    ] = 'b1;
   assign ca_ck_sdr_p6[`DDR_DQS_REN_IDX   ] = i_dfi_carddata_en_p6 ;
   assign ca_ck_sdr_p6[`DDR_DQS_DQS_IDX   ] = 'b0;
   assign ca_ck_sdr_p6[`DDR_DQS_WCK_IDX   ] = i_dfi_dram_clk_enable_p6;
   assign ca_ck_sdr_p7[`DDR_DQS_RCS_IDX   ] = 'b0;
   assign ca_ck_sdr_p7[`DDR_DQS_WCS_IDX   ] = 'b0;
   assign ca_ck_sdr_p7[`DDR_DQS_WCK_OE_IDX] = 'b1;
   assign ca_ck_sdr_p7[`DDR_DQS_IE_IDX    ] = 'b1;
   assign ca_ck_sdr_p7[`DDR_DQS_OE_IDX    ] = 'b1;
   assign ca_ck_sdr_p7[`DDR_DQS_RE_IDX    ] = 'b1;
   assign ca_ck_sdr_p7[`DDR_DQS_REN_IDX   ] = i_dfi_carddata_en_p7 ;
   assign ca_ck_sdr_p7[`DDR_DQS_DQS_IDX   ] = 'b0;
   assign ca_ck_sdr_p7[`DDR_DQS_WCK_IDX   ] = i_dfi_dram_clk_enable_p7;

   logic [CK_WWIDTH-1:0] tx_ck_sdr;

   // CK Transmitter
   assign tx_ck_sdr = {
                       ca_ck_sdr_p7,
                       ca_ck_sdr_p6,
                       ca_ck_sdr_p5,
                       ca_ck_sdr_p4,
                       ca_ck_sdr_p3,
                       ca_ck_sdr_p2,
                       ca_ck_sdr_p1,
                       ca_ck_sdr_p0
                      };

   // Convert to Words-Of-Phases (WOP) format
   //    Pn[Wn...W0]...P0[Wn...W0] -> Wn[Pn...P0]...W0[Pn...P0]
   ddr_dp_pow2wop #(.WIDTH(CK_WIDTH), .NUM_PH(NUM_WPH)) u_ck_tx_pow2wop (.i_d(tx_ck_sdr),.o_d(o_ck_sdr));

endmodule

module ddr_dfi_csr_wrapper #(
   parameter AWIDTH = 32,
   parameter DWIDTH = 32
) (

   input   logic                                 i_hclk,
   input   logic                                 i_hreset,
   input   logic [AWIDTH-1:0]                    i_haddr,
   input   logic                                 i_hwrite,
   input   logic                                 i_hsel,
   input   logic [DWIDTH-1:0]                    i_hwdata,
   input   logic [1:0]                           i_htrans,
   input   logic [2:0]                           i_hsize,
   input   logic [2:0]                           i_hburst,
   input   logic                                 i_hreadyin,
   output  logic                                 o_hready,
   output  logic [DWIDTH-1:0]                    o_hrdata,
   output  logic [1:0]                           o_hresp,

   input   logic                                 i_msr,

   output  logic [`DDR_DFI_TOP_0_CFG_RANGE]            o_dfi_top_0_cfg,
   output  logic [`DDR_DFICH_TOP_1_CFG_RANGE]       o_dfich0_top_1_cfg,
   output  logic [`DDR_DFICH_TOP_2_CFG_RANGE]       o_dfich0_top_2_cfg,
   output  logic [`DDR_DFICH_TOP_3_CFG_RANGE]       o_dfich0_top_3_cfg,
   input   logic [`DDR_DFICH_TOP_STA_RANGE]         i_dfich0_top_sta,
   output  logic [`DDR_DFICH_IG_DATA_CFG_RANGE]     o_dfich0_ig_data_cfg,
   input   logic [`DDR_DFICH_EG_DATA_STA_RANGE]     i_dfich0_eg_data_sta,
   output  logic [`DDR_DFICH_WRC_M0_CFG_RANGE]      o_dfich0_wrc_cfg,
   output  logic [`DDR_DFICH_WRCCTRL_M0_CFG_RANGE]  o_dfich0_wrcctrl_cfg,
   output  logic [`DDR_DFICH_CKCTRL_M0_CFG_RANGE]   o_dfich0_ckctrl_cfg,
   output  logic [`DDR_DFICH_RDC_M0_CFG_RANGE]      o_dfich0_rdc_cfg,
   output  logic [`DDR_DFICH_RCTRL_M0_CFG_RANGE]    o_dfich0_rctrl_cfg,
   output  logic [`DDR_DFICH_WCTRL_M0_CFG_RANGE]    o_dfich0_wctrl_cfg,
   output  logic [`DDR_DFICH_WENCTRL_M0_CFG_RANGE]  o_dfich0_wenctrl_cfg,
   output  logic [`DDR_DFICH_WCKCTRL_M0_CFG_RANGE]  o_dfich0_wckctrl_cfg,
   output  logic [`DDR_DFICH_WRD_M0_CFG_RANGE]      o_dfich0_wrd_cfg,
   output  logic [`DDR_DFICH_RDD_M0_CFG_RANGE]      o_dfich0_rdd_cfg,
   output  logic [`DDR_DFICH_CTRL0_M0_CFG_RANGE]    o_dfich0_ctrl0_cfg,
   output  logic [`DDR_DFICH_CTRL1_M0_CFG_RANGE]    o_dfich0_ctrl1_cfg,
   output  logic [`DDR_DFICH_CTRL2_M0_CFG_RANGE]    o_dfich0_ctrl2_cfg,
   output  logic [`DDR_DFICH_CTRL3_M0_CFG_RANGE]    o_dfich0_ctrl3_cfg,
   output  logic [`DDR_DFICH_CTRL4_M0_CFG_RANGE]    o_dfich0_ctrl4_cfg,
   output  logic [`DDR_DFICH_CTRL5_M0_CFG_RANGE]    o_dfich0_ctrl5_cfg,
   output  logic [`DDR_DFI_STATUS_IF_CFG_RANGE]   o_dfi_status_if_cfg,
   input   logic [`DDR_DFI_STATUS_IF_STA_RANGE]   i_dfi_status_if_sta,
   output  logic [`DDR_DFI_STATUS_IF_EVENT_0_CFG_RANGE] o_dfi_status_if_event_0_cfg,
   output  logic [`DDR_DFI_STATUS_IF_EVENT_1_CFG_RANGE] o_dfi_status_if_event_1_cfg,
   output  logic [`DDR_DFI_CTRLUPD_IF_CFG_RANGE]  o_dfi_ctrlupd_if_cfg,
   input   logic [`DDR_DFI_CTRLUPD_IF_STA_RANGE]  i_dfi_ctrlupd_if_sta,
   output  logic [`DDR_DFI_CTRLUPD_IF_EVENT_0_CFG_RANGE] o_dfi_ctrlupd_if_event_0_cfg,
   output  logic [`DDR_DFI_CTRLUPD_IF_EVENT_1_CFG_RANGE] o_dfi_ctrlupd_if_event_1_cfg,
   output  logic [`DDR_DFI_LP_CTRL_IF_CFG_RANGE]  o_dfi_lp_ctrl_if_cfg,
   input   logic [`DDR_DFI_LP_CTRL_IF_STA_RANGE]  i_dfi_lp_ctrl_if_sta,
   output  logic [`DDR_DFI_LP_CTRL_IF_EVENT_0_CFG_RANGE] o_dfi_lp_ctrl_if_event_0_cfg,
   output  logic [`DDR_DFI_LP_CTRL_IF_EVENT_1_CFG_RANGE] o_dfi_lp_ctrl_if_event_1_cfg,
   output  logic [`DDR_DFI_LP_DATA_IF_CFG_RANGE]  o_dfi_lp_data_if_cfg,
   input   logic [`DDR_DFI_LP_DATA_IF_STA_RANGE]  i_dfi_lp_data_if_sta,
   output  logic [`DDR_DFI_LP_DATA_IF_EVENT_0_CFG_RANGE] o_dfi_lp_data_if_event_0_cfg,
   output  logic [`DDR_DFI_LP_DATA_IF_EVENT_1_CFG_RANGE] o_dfi_lp_data_if_event_1_cfg,
   output  logic [`DDR_DFI_PHYUPD_IF_CFG_RANGE]   o_dfi_phyupd_if_cfg,
   input   logic [`DDR_DFI_PHYUPD_IF_STA_RANGE]   i_dfi_phyupd_if_sta,
   output  logic [`DDR_DFI_PHYMSTR_IF_CFG_RANGE]  o_dfi_phymstr_if_cfg,
   input   logic [`DDR_DFI_PHYMSTR_IF_STA_RANGE]  i_dfi_phymstr_if_sta,
   output  logic [`DDR_DFI_DEBUG_CFG_RANGE]       o_dfi_debug_cfg
);

  //----------------------------------------------------------------------------
  //AHB Slave Mux
  //----------------------------------------------------------------------------
   logic [AWIDTH-1:0]                    dfi_haddr ;
   logic                                 dfi_hwrite;
   logic                                 dfi_hsel  ;
   logic [DWIDTH-1:0]                    dfi_hwdata;
   logic [1:0]                           dfi_htrans;
   logic [2:0]                           dfi_hsize ;
   logic [2:0]                           dfi_hburst;
   logic                                 dfi_hreadyin;
   logic                                 dfi_hready;
   logic [DWIDTH-1:0]                    dfi_hrdata;
   logic [1:0]                           dfi_hresp ;

   logic [AWIDTH-1:0]                    dfich0_haddr ;
   logic                                 dfich0_hwrite;
   logic                                 dfich0_hsel  ;
   logic [DWIDTH-1:0]                    dfich0_hwdata;
   logic [1:0]                           dfich0_htrans;
   logic [2:0]                           dfich0_hsize ;
   logic [2:0]                           dfich0_hburst;
   logic                                 dfich0_hready;
   logic                                 dfich0_hreadyin;
   logic [DWIDTH-1:0]                    dfich0_hrdata;
   logic [1:0]                           dfich0_hresp ;
   logic [AWIDTH-1:0]                    dfich1_haddr ;
   logic                                 dfich1_hwrite;
   logic                                 dfich1_hsel  ;
   logic [DWIDTH-1:0]                    dfich1_hwdata;
   logic [1:0]                           dfich1_htrans;
   logic [2:0]                           dfich1_hsize ;
   logic [2:0]                           dfich1_hburst;
   logic                                 dfich1_hready;
   logic                                 dfich1_hreadyin;
   logic [DWIDTH-1:0]                    dfich1_hrdata;
   logic [1:0]                           dfich1_hresp ;

   localparam NUM_SLVS    = 3;
   localparam SWIDTH      = $clog2(NUM_SLVS)+'b1;

   localparam DFI_SLV_IDX    = 0  ;
   localparam DFICH0_SLV_IDX = 1  ;
   localparam DFICH1_SLV_IDX = 2  ;

   logic [AWIDTH-1:0]                 haddr_offset;
   logic [AWIDTH-1:0]                 haddr_local;

   logic [AWIDTH*NUM_SLVS-1:0]        slv_mux_haddr ;
   logic [NUM_SLVS-1:0]               slv_mux_hwrite;
   logic [NUM_SLVS-1:0]               slv_mux_hsel  ;
   logic [DWIDTH*NUM_SLVS-1:0]        slv_mux_hwdata;
   logic [2*NUM_SLVS-1:0]             slv_mux_htrans;
   logic [3*NUM_SLVS-1:0]             slv_mux_hsize ;
   logic [3*NUM_SLVS-1:0]             slv_mux_hburst;
   logic [NUM_SLVS-1:0]               slv_mux_hready;
   logic [NUM_SLVS-1:0]               slv_mux_hreadyin;
   logic [DWIDTH*NUM_SLVS-1:0]        slv_mux_hrdata;
   logic [2*NUM_SLVS-1:0]             slv_mux_hresp ;
   logic [SWIDTH-1:0]                 slv_sel ;

   assign dfi_haddr    =  slv_mux_haddr   [DFI_SLV_IDX*AWIDTH+:AWIDTH];
   assign dfi_hwrite   =  slv_mux_hwrite  [DFI_SLV_IDX];
   assign dfi_hsel     =  slv_mux_hsel    [DFI_SLV_IDX];
   assign dfi_hreadyin =  slv_mux_hreadyin[DFI_SLV_IDX];
   assign dfi_hwdata   =  slv_mux_hwdata  [DFI_SLV_IDX*DWIDTH+:DWIDTH];
   assign dfi_htrans   =  slv_mux_htrans  [DFI_SLV_IDX*2+:2];
   assign dfi_hsize    =  slv_mux_hsize   [DFI_SLV_IDX*3+:3];
   assign dfi_hburst   =  slv_mux_hburst  [DFI_SLV_IDX*3+:3];

   assign dfich0_haddr    =  slv_mux_haddr   [DFICH0_SLV_IDX*AWIDTH+:AWIDTH];
   assign dfich0_hwrite   =  slv_mux_hwrite  [DFICH0_SLV_IDX];
   assign dfich0_hsel     =  slv_mux_hsel    [DFICH0_SLV_IDX];
   assign dfich0_hreadyin =  slv_mux_hreadyin[DFICH0_SLV_IDX];
   assign dfich0_hwdata   =  slv_mux_hwdata  [DFICH0_SLV_IDX*DWIDTH+:DWIDTH];
   assign dfich0_htrans   =  slv_mux_htrans  [DFICH0_SLV_IDX*2+:2];
   assign dfich0_hsize    =  slv_mux_hsize   [DFICH0_SLV_IDX*3+:3];
   assign dfich0_hburst   =  slv_mux_hburst  [DFICH0_SLV_IDX*3+:3];

   assign dfich1_haddr    =  slv_mux_haddr   [DFICH1_SLV_IDX*AWIDTH+:AWIDTH];
   assign dfich1_hwrite   =  slv_mux_hwrite  [DFICH1_SLV_IDX];
   assign dfich1_hsel     =  slv_mux_hsel    [DFICH1_SLV_IDX];
   assign dfich1_hreadyin =  slv_mux_hreadyin[DFICH1_SLV_IDX];
   assign dfich1_hwdata   =  slv_mux_hwdata  [DFICH1_SLV_IDX*DWIDTH+:DWIDTH];
   assign dfich1_htrans   =  slv_mux_htrans  [DFICH1_SLV_IDX*2+:2];
   assign dfich1_hsize    =  slv_mux_hsize   [DFICH1_SLV_IDX*3+:3];
   assign dfich1_hburst   =  slv_mux_hburst  [DFICH1_SLV_IDX*3+:3];

   assign slv_mux_hready[DFI_SLV_IDX]                   = dfi_hready;
   assign slv_mux_hrdata[DFI_SLV_IDX*DWIDTH+:DWIDTH]    = dfi_hrdata;
   assign slv_mux_hresp [DFI_SLV_IDX*2+:2]              = dfi_hresp ;

   assign slv_mux_hready[DFICH0_SLV_IDX]                = dfich0_hready;
   assign slv_mux_hrdata[DFICH0_SLV_IDX*DWIDTH+:DWIDTH] = dfich0_hrdata;
   assign slv_mux_hresp [DFICH0_SLV_IDX*2+:2]           = dfich0_hresp ;

   assign slv_mux_hready[DFICH1_SLV_IDX]                = dfich1_hready;
   assign slv_mux_hrdata[DFICH1_SLV_IDX*DWIDTH+:DWIDTH] = dfich1_hrdata;
   assign slv_mux_hresp [DFICH1_SLV_IDX*2+:2]           = dfich1_hresp ;
   assign dfich1_hready = '1 ;
   assign dfich1_hrdata = '0 ;
   assign dfich1_hresp  = AHB_RESP_ERROR ;

   //Slave sel and slave decode
   assign slv_sel     = (i_haddr < (DDR_DFICH0_OFFSET - DDR_DFI_OFFSET)) ? ('b1+DFI_SLV_IDX ) :
                        ((i_haddr >= (DDR_DFICH0_OFFSET - DDR_DFI_OFFSET)) & (i_haddr < (DDR_DFICH1_OFFSET - DDR_DFI_OFFSET))) ? ('b1+DFICH0_SLV_IDX ) :
                        ((i_haddr >= (DDR_DFICH1_OFFSET - DDR_DFI_OFFSET)) & (i_haddr < (DDR_CH0_DQ0_OFFSET- DDR_DFI_OFFSET))) ? ('b1+DFICH1_SLV_IDX ) :
                        '0;

   assign haddr_offset = (slv_sel == ('b1+DFICH0_SLV_IDX  )) ? DDR_DFICH0_OFFSET - DDR_DFI_OFFSET  :
                         (slv_sel == ('b1+DFICH1_SLV_IDX  )) ? DDR_DFICH1_OFFSET - DDR_DFI_OFFSET  :
                         '0;

   assign haddr_local  = i_haddr - haddr_offset;

   wav_ahb_slave_mux #(
      .DWIDTH           (32),
      .AWIDTH           (32),
      .NUM_SLV          (NUM_SLVS)
   ) u_slv_mux (

      .i_hclk           (i_hclk),
      .i_hreset         (i_hreset),

      .i_slv_sel        (slv_sel),
      .i_hbusreq        (i_hsel),
      .i_haddr          (haddr_local),
      .i_hwrite         (i_hwrite),
      .i_hwdata         (i_hwdata),
      .i_htrans         (i_htrans),
      .i_hsize          (i_hsize ),
      .i_hburst         (i_hburst),
      .i_hreadyin       (i_hreadyin),
      .o_hready         (o_hready),
      .o_hrdata         (o_hrdata),
      .o_hresp          (o_hresp ),

      .o_haddr          (slv_mux_haddr ),
      .o_hwrite         (slv_mux_hwrite),
      .o_hsel           (slv_mux_hsel  ),
      .o_hwdata         (slv_mux_hwdata),
      .o_htrans         (slv_mux_htrans),
      .o_hsize          (slv_mux_hsize ),
      .o_hburst         (slv_mux_hburst),
      .o_hreadyin       (slv_mux_hreadyin),
      .i_hready         (slv_mux_hready),
      .i_hrdata         (slv_mux_hrdata),
      .i_hresp          (slv_mux_hresp )
   );

  //----------------------------------------------------------------------------
  //CSR Instances
  //----------------------------------------------------------------------------
   logic [`DDR_DFICH_WRC_M0_CFG_RANGE]     dfich0_wrc_m0_cfg;
   logic [`DDR_DFICH_WRC_M1_CFG_RANGE]     dfich0_wrc_m1_cfg;
   logic [`DDR_DFICH_WRCCTRL_M0_CFG_RANGE] dfich0_wrcctrl_m0_cfg;
   logic [`DDR_DFICH_WRCCTRL_M1_CFG_RANGE] dfich0_wrcctrl_m1_cfg;
   logic [`DDR_DFICH_CKCTRL_M0_CFG_RANGE]  dfich0_ckctrl_m0_cfg;
   logic [`DDR_DFICH_CKCTRL_M1_CFG_RANGE]  dfich0_ckctrl_m1_cfg;
   logic [`DDR_DFICH_RDC_M0_CFG_RANGE]     dfich0_rdc_m0_cfg;
   logic [`DDR_DFICH_RDC_M1_CFG_RANGE]     dfich0_rdc_m1_cfg;
   logic [`DDR_DFICH_RCTRL_M0_CFG_RANGE]   dfich0_rctrl_m0_cfg;
   logic [`DDR_DFICH_RCTRL_M1_CFG_RANGE]   dfich0_rctrl_m1_cfg;
   logic [`DDR_DFICH_WCTRL_M0_CFG_RANGE]   dfich0_wctrl_m0_cfg;
   logic [`DDR_DFICH_WCTRL_M1_CFG_RANGE]   dfich0_wctrl_m1_cfg;
   logic [`DDR_DFICH_WENCTRL_M0_CFG_RANGE] dfich0_wenctrl_m0_cfg;
   logic [`DDR_DFICH_WENCTRL_M1_CFG_RANGE] dfich0_wenctrl_m1_cfg;
   logic [`DDR_DFICH_WCKCTRL_M0_CFG_RANGE] dfich0_wckctrl_m0_cfg;
   logic [`DDR_DFICH_WCKCTRL_M1_CFG_RANGE] dfich0_wckctrl_m1_cfg;
   logic [`DDR_DFICH_WRD_M0_CFG_RANGE]     dfich0_wrd_m0_cfg;
   logic [`DDR_DFICH_WRD_M1_CFG_RANGE]     dfich0_wrd_m1_cfg;
   logic [`DDR_DFICH_RDD_M0_CFG_RANGE]     dfich0_rdd_m0_cfg;
   logic [`DDR_DFICH_RDD_M1_CFG_RANGE]     dfich0_rdd_m1_cfg;
   logic [`DDR_DFICH_CTRL0_M0_CFG_RANGE]   dfich0_ctrl0_m0_cfg;
   logic [`DDR_DFICH_CTRL0_M1_CFG_RANGE]   dfich0_ctrl0_m1_cfg;
   logic [`DDR_DFICH_CTRL1_M0_CFG_RANGE]   dfich0_ctrl1_m0_cfg;
   logic [`DDR_DFICH_CTRL1_M1_CFG_RANGE]   dfich0_ctrl1_m1_cfg;
   logic [`DDR_DFICH_CTRL2_M0_CFG_RANGE]   dfich0_ctrl2_m0_cfg;
   logic [`DDR_DFICH_CTRL2_M1_CFG_RANGE]   dfich0_ctrl2_m1_cfg;
   logic [`DDR_DFICH_CTRL3_M0_CFG_RANGE]   dfich0_ctrl3_m0_cfg;
   logic [`DDR_DFICH_CTRL3_M1_CFG_RANGE]   dfich0_ctrl3_m1_cfg;
   logic [`DDR_DFICH_CTRL4_M0_CFG_RANGE]   dfich0_ctrl4_m0_cfg;
   logic [`DDR_DFICH_CTRL4_M1_CFG_RANGE]   dfich0_ctrl4_m1_cfg;
   logic [`DDR_DFICH_CTRL5_M0_CFG_RANGE]   dfich0_ctrl5_m0_cfg;
   logic [`DDR_DFICH_CTRL5_M1_CFG_RANGE]   dfich0_ctrl5_m1_cfg;

   ddr_dfi_ahb_csr #(
      .AWIDTH                          (AWIDTH),
      .DWIDTH                          (DWIDTH)
   ) u_dfi_csr (
      .i_hclk                          (i_hclk),
      .i_hreset                        (i_hreset),
      .i_haddr                         (dfi_haddr),
      .i_hwrite                        (dfi_hwrite),
      .i_hsel                          (dfi_hsel),
      .i_hwdata                        (dfi_hwdata),
      .i_htrans                        (dfi_htrans),
      .i_hsize                         (dfi_hsize),
      .i_hburst                        (dfi_hburst),
      .i_hreadyin                      (dfi_hreadyin),
      .o_hready                        (dfi_hready),
      .o_hrdata                        (dfi_hrdata),
      .o_hresp                         (dfi_hresp),
      .o_dfi_top_0_cfg                 (o_dfi_top_0_cfg),
      .o_dfi_status_if_cfg             (o_dfi_status_if_cfg),
      .i_dfi_status_if_sta             (i_dfi_status_if_sta),
      .o_dfi_status_if_event_0_cfg     (o_dfi_status_if_event_0_cfg),
      .o_dfi_status_if_event_1_cfg     (o_dfi_status_if_event_1_cfg),
      .o_dfi_ctrlupd_if_cfg            (o_dfi_ctrlupd_if_cfg),
      .i_dfi_ctrlupd_if_sta            (i_dfi_ctrlupd_if_sta),
      .o_dfi_ctrlupd_if_event_0_cfg    (o_dfi_ctrlupd_if_event_0_cfg),
      .o_dfi_ctrlupd_if_event_1_cfg    (o_dfi_ctrlupd_if_event_1_cfg),
      .o_dfi_lp_ctrl_if_cfg            (o_dfi_lp_ctrl_if_cfg),
      .i_dfi_lp_ctrl_if_sta            (i_dfi_lp_ctrl_if_sta),
      .o_dfi_lp_ctrl_if_event_0_cfg    (o_dfi_lp_ctrl_if_event_0_cfg),
      .o_dfi_lp_ctrl_if_event_1_cfg    (o_dfi_lp_ctrl_if_event_1_cfg),
      .o_dfi_lp_data_if_cfg            (o_dfi_lp_data_if_cfg),
      .i_dfi_lp_data_if_sta            (i_dfi_lp_data_if_sta),
      .o_dfi_lp_data_if_event_0_cfg    (o_dfi_lp_data_if_event_0_cfg),
      .o_dfi_lp_data_if_event_1_cfg    (o_dfi_lp_data_if_event_1_cfg),
      .o_dfi_phyupd_if_cfg             (o_dfi_phyupd_if_cfg),
      .i_dfi_phyupd_if_sta             (i_dfi_phyupd_if_sta),
      .o_dfi_phymstr_if_cfg            (o_dfi_phymstr_if_cfg),
      .i_dfi_phymstr_if_sta            (i_dfi_phymstr_if_sta),
      .o_dfi_debug_cfg                 (o_dfi_debug_cfg),
      .o_dfi_data_bit_enable_cfg       (/*OPEN*/),                        // FIXME - May need to connect to some slice mask logic
      .o_dfi_phyfreq_range_cfg         (/*OPEN*/)                         // Only used to communicate freq support to host
   );

   ddr_dfich_ahb_csr #(
      .AWIDTH                          (AWIDTH),
      .DWIDTH                          (DWIDTH)
   ) u_dfich0_csr (
      .i_hclk                          (i_hclk),
      .i_hreset                        (i_hreset),
      .i_haddr                         (dfich0_haddr),
      .i_hwrite                        (dfich0_hwrite),
      .i_hsel                          (dfich0_hsel),
      .i_hwdata                        (dfich0_hwdata),
      .i_htrans                        (dfich0_htrans),
      .i_hsize                         (dfich0_hsize),
      .i_hburst                        (dfich0_hburst),
      .i_hreadyin                      (dfich0_hreadyin),
      .o_hready                        (dfich0_hready),
      .o_hrdata                        (dfich0_hrdata),
      .o_hresp                         (dfich0_hresp),
      .o_dfich_top_1_cfg               (o_dfich0_top_1_cfg),
      .o_dfich_top_2_cfg               (o_dfich0_top_2_cfg),
      .o_dfich_top_3_cfg               (o_dfich0_top_3_cfg),
      .i_dfich_top_sta                 (i_dfich0_top_sta),
      .o_dfich_ig_data_cfg             (o_dfich0_ig_data_cfg),
      .i_dfich_eg_data_sta             (i_dfich0_eg_data_sta),
      .o_dfich_wrc_m0_cfg              (dfich0_wrc_m0_cfg),
      .o_dfich_wrc_m1_cfg              (dfich0_wrc_m1_cfg),
      .o_dfich_wrcctrl_m0_cfg          (dfich0_wrcctrl_m0_cfg),
      .o_dfich_wrcctrl_m1_cfg          (dfich0_wrcctrl_m1_cfg),
      .o_dfich_ckctrl_m0_cfg           (dfich0_ckctrl_m0_cfg),
      .o_dfich_ckctrl_m1_cfg           (dfich0_ckctrl_m1_cfg),
      .o_dfich_rdc_m0_cfg              (dfich0_rdc_m0_cfg),
      .o_dfich_rdc_m1_cfg              (dfich0_rdc_m1_cfg),
      .o_dfich_rctrl_m0_cfg            (dfich0_rctrl_m0_cfg),
      .o_dfich_rctrl_m1_cfg            (dfich0_rctrl_m1_cfg),
      .o_dfich_wctrl_m0_cfg            (dfich0_wctrl_m0_cfg),
      .o_dfich_wctrl_m1_cfg            (dfich0_wctrl_m1_cfg),
      .o_dfich_wenctrl_m0_cfg          (dfich0_wenctrl_m0_cfg),
      .o_dfich_wenctrl_m1_cfg          (dfich0_wenctrl_m1_cfg),
      .o_dfich_wckctrl_m0_cfg          (dfich0_wckctrl_m0_cfg),
      .o_dfich_wckctrl_m1_cfg          (dfich0_wckctrl_m1_cfg),
      .o_dfich_wrd_m0_cfg              (dfich0_wrd_m0_cfg),
      .o_dfich_wrd_m1_cfg              (dfich0_wrd_m1_cfg),
      .o_dfich_rdd_m0_cfg              (dfich0_rdd_m0_cfg),
      .o_dfich_rdd_m1_cfg              (dfich0_rdd_m1_cfg),
      .o_dfich_ctrl0_m0_cfg            (dfich0_ctrl0_m0_cfg),
      .o_dfich_ctrl0_m1_cfg            (dfich0_ctrl0_m1_cfg),
      .o_dfich_ctrl1_m0_cfg            (dfich0_ctrl1_m0_cfg),
      .o_dfich_ctrl1_m1_cfg            (dfich0_ctrl1_m1_cfg),
      .o_dfich_ctrl2_m0_cfg            (dfich0_ctrl2_m0_cfg),
      .o_dfich_ctrl2_m1_cfg            (dfich0_ctrl2_m1_cfg),
      .o_dfich_ctrl3_m0_cfg            (dfich0_ctrl3_m0_cfg),
      .o_dfich_ctrl3_m1_cfg            (dfich0_ctrl3_m1_cfg),
      .o_dfich_ctrl4_m0_cfg            (dfich0_ctrl4_m0_cfg),
      .o_dfich_ctrl4_m1_cfg            (dfich0_ctrl4_m1_cfg),
      .o_dfich_ctrl5_m0_cfg            (dfich0_ctrl5_m0_cfg),
      .o_dfich_ctrl5_m1_cfg            (dfich0_ctrl5_m1_cfg)
   );

   assign o_dfich0_wrc_cfg     = i_msr ? dfich0_wrc_m1_cfg     : dfich0_wrc_m0_cfg;
   assign o_dfich0_wrcctrl_cfg = i_msr ? dfich0_wrcctrl_m1_cfg : dfich0_wrcctrl_m0_cfg;
   assign o_dfich0_ckctrl_cfg  = i_msr ? dfich0_ckctrl_m1_cfg  : dfich0_ckctrl_m0_cfg;
   assign o_dfich0_rdc_cfg     = i_msr ? dfich0_rdc_m1_cfg     : dfich0_rdc_m0_cfg;
   assign o_dfich0_rctrl_cfg   = i_msr ? dfich0_rctrl_m1_cfg   : dfich0_rctrl_m0_cfg;
   assign o_dfich0_wctrl_cfg   = i_msr ? dfich0_wctrl_m1_cfg   : dfich0_wctrl_m0_cfg;
   assign o_dfich0_wenctrl_cfg = i_msr ? dfich0_wenctrl_m1_cfg : dfich0_wenctrl_m0_cfg;
   assign o_dfich0_wckctrl_cfg = i_msr ? dfich0_wckctrl_m1_cfg : dfich0_wckctrl_m0_cfg;
   assign o_dfich0_wrd_cfg     = i_msr ? dfich0_wrd_m1_cfg     : dfich0_wrd_m0_cfg;
   assign o_dfich0_rdd_cfg     = i_msr ? dfich0_rdd_m1_cfg     : dfich0_rdd_m0_cfg;
   assign o_dfich0_ctrl0_cfg   = i_msr ? dfich0_ctrl0_m1_cfg   : dfich0_ctrl0_m0_cfg;
   assign o_dfich0_ctrl1_cfg   = i_msr ? dfich0_ctrl1_m1_cfg   : dfich0_ctrl1_m0_cfg;
   assign o_dfich0_ctrl2_cfg   = i_msr ? dfich0_ctrl2_m1_cfg   : dfich0_ctrl2_m0_cfg;
   assign o_dfich0_ctrl3_cfg   = i_msr ? dfich0_ctrl3_m1_cfg   : dfich0_ctrl3_m0_cfg;
   assign o_dfich0_ctrl4_cfg   = i_msr ? dfich0_ctrl4_m1_cfg   : dfich0_ctrl4_m0_cfg;
   assign o_dfich0_ctrl5_cfg   = i_msr ? dfich0_ctrl5_m1_cfg   : dfich0_ctrl5_m0_cfg;

endmodule

module ddr_dfi_write_cmd #(
   parameter FWIDTH                 = 2,
   parameter SWIDTH                 = 12,                 // Address Slice Width
   parameter DWIDTH                 = SWIDTH * 2,         // Data Width R+F
   parameter NUM_WPH                = 8  // Number of Phases
) (

   input  logic                     i_scan_cgc_ctrl,

   // Clock
   input  logic                     i_cmdc_clk_0,
   input  logic                     i_cmdc_clk_1,
   input  logic                     i_cmdc_clk_2,

   input  logic                     i_cmda_clk_0,
   input  logic                     i_cmda_clk_1,
   input  logic                     i_cmda_clk_2,

   // Write Datapath Control
   input  logic                     i_wrc_pipe_en,
   input  dwgb_t                    i_wrc_gb_mode,
   input  logic [FWIDTH-1:0]        i_wrc_post_gb_dly,

   input  logic                     i_wrcctrl_pipe_en,
   input  dwgb_t                    i_wrcctrl_gb_mode,
   input  logic [FWIDTH-1:0]        i_wrcctrl_post_gb_dly,

   input  logic                     i_ckctrl_pipe_en,
   input  dwgb_t                    i_ckctrl_gb_mode,
   input  logic [FWIDTH-1:0]        i_ckctrl_post_gb_dly,

   // Write Data
   input  logic [SWIDTH-1:0]        i_dfi_address_p0,
   input  logic [SWIDTH-1:0]        i_dfi_address_p1,
   input  logic [SWIDTH-1:0]        i_dfi_address_p2,
   input  logic [SWIDTH-1:0]        i_dfi_address_p3,
   input  logic [SWIDTH-1:0]        i_dfi_address_p4,
   input  logic [SWIDTH-1:0]        i_dfi_address_p5,
   input  logic [SWIDTH-1:0]        i_dfi_address_p6,
   input  logic [SWIDTH-1:0]        i_dfi_address_p7,
   input  logic [1:0]               i_dfi_cke_p0,
   input  logic [1:0]               i_dfi_cke_p1,
   input  logic [1:0]               i_dfi_cke_p2,
   input  logic [1:0]               i_dfi_cke_p3,
   input  logic [1:0]               i_dfi_cke_p4,
   input  logic [1:0]               i_dfi_cke_p5,
   input  logic [1:0]               i_dfi_cke_p6,
   input  logic [1:0]               i_dfi_cke_p7,
   input  logic [1:0]               i_dfi_cs_p0,
   input  logic [1:0]               i_dfi_cs_p1,
   input  logic [1:0]               i_dfi_cs_p2,
   input  logic [1:0]               i_dfi_cs_p3,
   input  logic [1:0]               i_dfi_cs_p4,
   input  logic [1:0]               i_dfi_cs_p5,
   input  logic [1:0]               i_dfi_cs_p6,
   input  logic [1:0]               i_dfi_cs_p7,
   input  logic                     i_dfi_dcd_p0,
   input  logic                     i_dfi_dcd_p1,
   input  logic                     i_dfi_dcd_p2,
   input  logic                     i_dfi_dcd_p3,
   input  logic                     i_dfi_dcd_p4,
   input  logic                     i_dfi_dcd_p5,
   input  logic                     i_dfi_dcd_p6,
   input  logic                     i_dfi_dcd_p7,

   output logic [SWIDTH-1:0]        o_dfi_address_p0,
   output logic [SWIDTH-1:0]        o_dfi_address_p1,
   output logic [SWIDTH-1:0]        o_dfi_address_p2,
   output logic [SWIDTH-1:0]        o_dfi_address_p3,
   output logic [SWIDTH-1:0]        o_dfi_address_p4,
   output logic [SWIDTH-1:0]        o_dfi_address_p5,
   output logic [SWIDTH-1:0]        o_dfi_address_p6,
   output logic [SWIDTH-1:0]        o_dfi_address_p7,
   output logic [1:0]               o_dfi_cke_p0,
   output logic [1:0]               o_dfi_cke_p1,
   output logic [1:0]               o_dfi_cke_p2,
   output logic [1:0]               o_dfi_cke_p3,
   output logic [1:0]               o_dfi_cke_p4,
   output logic [1:0]               o_dfi_cke_p5,
   output logic [1:0]               o_dfi_cke_p6,
   output logic [1:0]               o_dfi_cke_p7,
   output logic [1:0]               o_dfi_cs_p0,
   output logic [1:0]               o_dfi_cs_p1,
   output logic [1:0]               o_dfi_cs_p2,
   output logic [1:0]               o_dfi_cs_p3,
   output logic [1:0]               o_dfi_cs_p4,
   output logic [1:0]               o_dfi_cs_p5,
   output logic [1:0]               o_dfi_cs_p6,
   output logic [1:0]               o_dfi_cs_p7,
   output logic                     o_dfi_dcd_p0,
   output logic                     o_dfi_dcd_p1,
   output logic                     o_dfi_dcd_p2,
   output logic                     o_dfi_dcd_p3,
   output logic                     o_dfi_dcd_p4,
   output logic                     o_dfi_dcd_p5,
   output logic                     o_dfi_dcd_p6,
   output logic                     o_dfi_dcd_p7,

   output logic [31:0]              o_debug
);

    assign o_debug = '0 ; //FXIME
   // ------------------------------------------------------------------------
   // DFI Address Datapath
   // ------------------------------------------------------------------------

   ddr_dfi_wdp #(
      .SWIDTH                       (SWIDTH),
      .SDR_MODE                     (1'b0),
      .FWIDTH                       (FWIDTH)
   ) u_wdp_adr (
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_rst                        ('0),
      .i_clk_0                      (i_cmda_clk_0),
      .i_clk_1                      (i_cmda_clk_1),
      .i_clk_2                      (i_cmda_clk_2),
      .i_pipe_en                    (i_wrc_pipe_en),
      .i_wgb_mode                   (i_wrc_gb_mode),
      .i_post_gb_dly                (i_wrc_post_gb_dly),
      .i_phase_ext                  ('0),
      .i_dfi_data_p0                (i_dfi_address_p0),
      .i_dfi_data_p1                (i_dfi_address_p1),
      .i_dfi_data_p2                (i_dfi_address_p2),
      .i_dfi_data_p3                (i_dfi_address_p3),
      .i_dfi_data_p4                (i_dfi_address_p4),
      .i_dfi_data_p5                (i_dfi_address_p5),
      .i_dfi_data_p6                (i_dfi_address_p6),
      .i_dfi_data_p7                (i_dfi_address_p7),

      .o_dfi_data_p0                (o_dfi_address_p0),
      .o_dfi_data_p1                (o_dfi_address_p1),
      .o_dfi_data_p2                (o_dfi_address_p2),
      .o_dfi_data_p3                (o_dfi_address_p3),
      .o_dfi_data_p4                (o_dfi_address_p4),
      .o_dfi_data_p5                (o_dfi_address_p5),
      .o_dfi_data_p6                (o_dfi_address_p6),
      .o_dfi_data_p7                (o_dfi_address_p7),

      .o_debug                      (/*OPEN*/)
   );

   // ------------------------------------------------------------------------
   // DFI CKE
   // ------------------------------------------------------------------------

   ddr_dfi_wdp #(
      .SWIDTH                       (2),
      .SDR_MODE                     (1'b0),
      .FWIDTH                       (FWIDTH)
   ) u_wdp_cke (
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_rst                        ('0),
      .i_clk_0                      (i_cmda_clk_0),
      .i_clk_1                      (i_cmda_clk_1),
      .i_clk_2                      (i_cmda_clk_2),
      .i_pipe_en                    (i_wrc_pipe_en),
      .i_wgb_mode                   (i_wrc_gb_mode),
      .i_post_gb_dly                (i_wrc_post_gb_dly),
      .i_phase_ext                  ('0),

      .i_dfi_data_p0                (i_dfi_cke_p0),
      .i_dfi_data_p1                (i_dfi_cke_p1),
      .i_dfi_data_p2                (i_dfi_cke_p2),
      .i_dfi_data_p3                (i_dfi_cke_p3),
      .i_dfi_data_p4                (i_dfi_cke_p4),
      .i_dfi_data_p5                (i_dfi_cke_p5),
      .i_dfi_data_p6                (i_dfi_cke_p6),
      .i_dfi_data_p7                (i_dfi_cke_p7),

      .o_dfi_data_p0                (o_dfi_cke_p0),
      .o_dfi_data_p1                (o_dfi_cke_p1),
      .o_dfi_data_p2                (o_dfi_cke_p2),
      .o_dfi_data_p3                (o_dfi_cke_p3),
      .o_dfi_data_p4                (o_dfi_cke_p4),
      .o_dfi_data_p5                (o_dfi_cke_p5),
      .o_dfi_data_p6                (o_dfi_cke_p6),
      .o_dfi_data_p7                (o_dfi_cke_p7),

      .o_debug                      (/*OPEN*/)
   );

   // ------------------------------------------------------------------------
   // DFI CS
   // ------------------------------------------------------------------------

   ddr_dfi_wdp #(
      .SWIDTH                       (2),
      .SDR_MODE                     (1'b0),
      .FWIDTH                       (FWIDTH)
   ) u_wdp_cs (
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_rst                        ('0),
      .i_clk_0                      (i_cmda_clk_0),
      .i_clk_1                      (i_cmda_clk_1),
      .i_clk_2                      (i_cmda_clk_2),
      .i_pipe_en                    (i_wrcctrl_pipe_en),
      .i_wgb_mode                   (i_wrcctrl_gb_mode),
      .i_post_gb_dly                (i_wrcctrl_post_gb_dly),
      .i_phase_ext                  ('0),

      .i_dfi_data_p0                (i_dfi_cs_p0),
      .i_dfi_data_p1                (i_dfi_cs_p1),
      .i_dfi_data_p2                (i_dfi_cs_p2),
      .i_dfi_data_p3                (i_dfi_cs_p3),
      .i_dfi_data_p4                (i_dfi_cs_p4),
      .i_dfi_data_p5                (i_dfi_cs_p5),
      .i_dfi_data_p6                (i_dfi_cs_p6),
      .i_dfi_data_p7                (i_dfi_cs_p7),

      .o_dfi_data_p0                (o_dfi_cs_p0),
      .o_dfi_data_p1                (o_dfi_cs_p1),
      .o_dfi_data_p2                (o_dfi_cs_p2),
      .o_dfi_data_p3                (o_dfi_cs_p3),
      .o_dfi_data_p4                (o_dfi_cs_p4),
      .o_dfi_data_p5                (o_dfi_cs_p5),
      .o_dfi_data_p6                (o_dfi_cs_p6),
      .o_dfi_data_p7                (o_dfi_cs_p7),

      .o_debug                      (/*OPEN*/)
   );

   // ------------------------------------------------------------------------
   // DFI DRAM Clock Disable
   // ------------------------------------------------------------------------
   logic                            dfi_dcd_p0;
   logic                            dfi_dcd_p1;
   logic                            dfi_dcd_p2;
   logic                            dfi_dcd_p3;
   logic                            dfi_dcd_p4;
   logic                            dfi_dcd_p5;
   logic                            dfi_dcd_p6;
   logic                            dfi_dcd_p7;

   ddr_dfi_wdp #(
      .SWIDTH                       (1),
      .SDR_MODE                     (1'b0),
      .FWIDTH                       (FWIDTH)
   ) u_wdp_dcd (
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_rst                        ('0),
      .i_clk_0                      (i_cmdc_clk_0),
      .i_clk_1                      (i_cmdc_clk_1),
      .i_clk_2                      (i_cmdc_clk_2),
      .i_pipe_en                    (i_ckctrl_pipe_en),
      .i_wgb_mode                   (i_ckctrl_gb_mode),
      .i_post_gb_dly                (i_ckctrl_post_gb_dly),
      .i_phase_ext                  ('0),

      .i_dfi_data_p0                (i_dfi_dcd_p0),
      .i_dfi_data_p1                (i_dfi_dcd_p1),
      .i_dfi_data_p2                (i_dfi_dcd_p2),
      .i_dfi_data_p3                (i_dfi_dcd_p3),
      .i_dfi_data_p4                (i_dfi_dcd_p4),
      .i_dfi_data_p5                (i_dfi_dcd_p5),
      .i_dfi_data_p6                (i_dfi_dcd_p6),
      .i_dfi_data_p7                (i_dfi_dcd_p7),

      .o_dfi_data_p0                (dfi_dcd_p0),
      .o_dfi_data_p1                (dfi_dcd_p1),
      .o_dfi_data_p2                (dfi_dcd_p2),
      .o_dfi_data_p3                (dfi_dcd_p3),
      .o_dfi_data_p4                (dfi_dcd_p4),
      .o_dfi_data_p5                (dfi_dcd_p5),
      .o_dfi_data_p6                (dfi_dcd_p6),
      .o_dfi_data_p7                (dfi_dcd_p7),

      .o_debug                      (/*OPEN*/)
   );

   assign o_dfi_dcd_p0 = dfi_dcd_p0 ;
   assign o_dfi_dcd_p1 = 1'b1;

   assign o_dfi_dcd_p2 = dfi_dcd_p2 ;
   assign o_dfi_dcd_p3 = 1'b1;

   assign o_dfi_dcd_p4 = dfi_dcd_p4 ;
   assign o_dfi_dcd_p5 = 1'b1;

   assign o_dfi_dcd_p6 = dfi_dcd_p6 ;
   assign o_dfi_dcd_p7 = 1'b1;


endmodule

module ddr_dfi_write #(
   parameter FWIDTH                 = 2,
   parameter SWIDTH                 = 16,                 // PHY Slice Width
   parameter BWIDTH                 = SWIDTH / 8,         // Byte width
   parameter MWIDTH                 = BWIDTH * 2,         // Mask width R+F
   parameter PWIDTH                 = 4,                  // Phase Extension Width
   parameter NUM_WPH                = 8                    // Number of Phases
) (

   input  logic                     i_scan_cgc_ctrl,
   input  logic                     i_rst,

   // Clock
   input  logic                     i_clk_0,
   input  logic                     i_clk_1,
   input  logic                     i_clk_2,

   // Write Datapath Control
   input  logic                     i_wrd_pipe_en,
   input  dwgb_t                    i_wrd_gb_mode,
   input  logic [FWIDTH-1:0]        i_wrd_post_gb_dly,

   // Write Data
   input  logic [SWIDTH-1:0]        i_dfi_wrdata_p0,
   input  logic [SWIDTH-1:0]        i_dfi_wrdata_p1,
   input  logic [SWIDTH-1:0]        i_dfi_wrdata_p2,
   input  logic [SWIDTH-1:0]        i_dfi_wrdata_p3,
   input  logic [SWIDTH-1:0]        i_dfi_wrdata_p4,
   input  logic [SWIDTH-1:0]        i_dfi_wrdata_p5,
   input  logic [SWIDTH-1:0]        i_dfi_wrdata_p6,
   input  logic [SWIDTH-1:0]        i_dfi_wrdata_p7,

   input  logic [MWIDTH-1:0]        i_dfi_wrdata_mask_p0,
   input  logic [MWIDTH-1:0]        i_dfi_wrdata_mask_p1,
   input  logic [MWIDTH-1:0]        i_dfi_wrdata_mask_p2,
   input  logic [MWIDTH-1:0]        i_dfi_wrdata_mask_p3,
   input  logic [MWIDTH-1:0]        i_dfi_wrdata_mask_p4,
   input  logic [MWIDTH-1:0]        i_dfi_wrdata_mask_p5,
   input  logic [MWIDTH-1:0]        i_dfi_wrdata_mask_p6,
   input  logic [MWIDTH-1:0]        i_dfi_wrdata_mask_p7,

   output logic [SWIDTH-1:0]        o_dfi_wrdata_p0,
   output logic [SWIDTH-1:0]        o_dfi_wrdata_p1,
   output logic [SWIDTH-1:0]        o_dfi_wrdata_p2,
   output logic [SWIDTH-1:0]        o_dfi_wrdata_p3,
   output logic [SWIDTH-1:0]        o_dfi_wrdata_p4,
   output logic [SWIDTH-1:0]        o_dfi_wrdata_p5,
   output logic [SWIDTH-1:0]        o_dfi_wrdata_p6,
   output logic [SWIDTH-1:0]        o_dfi_wrdata_p7,
   output logic [MWIDTH-1:0]        o_dfi_wrdata_mask_p0,
   output logic [MWIDTH-1:0]        o_dfi_wrdata_mask_p1,
   output logic [MWIDTH-1:0]        o_dfi_wrdata_mask_p2,
   output logic [MWIDTH-1:0]        o_dfi_wrdata_mask_p3,
   output logic [MWIDTH-1:0]        o_dfi_wrdata_mask_p4,
   output logic [MWIDTH-1:0]        o_dfi_wrdata_mask_p5,
   output logic [MWIDTH-1:0]        o_dfi_wrdata_mask_p6,
   output logic [MWIDTH-1:0]        o_dfi_wrdata_mask_p7,

   output logic [31:0]              o_debug
);

    assign o_debug = '0 ; //FXIME
   // ------------------------------------------------------------------------
   // DFI Write Bus Datapath
   // ------------------------------------------------------------------------

   ddr_dfi_wdp #(
      .SWIDTH                       (SWIDTH),
      .SDR_MODE                     (1'b0),
      .FWIDTH                       (FWIDTH)
   ) u_wdp_wrd (
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_rst                        (i_rst),
      .i_clk_0                      (i_clk_0),
      .i_clk_1                      (i_clk_1),
      .i_clk_2                      (i_clk_2),
      .i_pipe_en                    (i_wrd_pipe_en),
      .i_wgb_mode                   (i_wrd_gb_mode),
      .i_post_gb_dly                (i_wrd_post_gb_dly),
      .i_phase_ext                  ('0),

      .i_dfi_data_p0                (i_dfi_wrdata_p0),
      .i_dfi_data_p1                (i_dfi_wrdata_p1),
      .i_dfi_data_p2                (i_dfi_wrdata_p2),
      .i_dfi_data_p3                (i_dfi_wrdata_p3),
      .i_dfi_data_p4                (i_dfi_wrdata_p4),
      .i_dfi_data_p5                (i_dfi_wrdata_p5),
      .i_dfi_data_p6                (i_dfi_wrdata_p6),
      .i_dfi_data_p7                (i_dfi_wrdata_p7),

      .o_dfi_data_p0                (o_dfi_wrdata_p0),
      .o_dfi_data_p1                (o_dfi_wrdata_p1),
      .o_dfi_data_p2                (o_dfi_wrdata_p2),
      .o_dfi_data_p3                (o_dfi_wrdata_p3),
      .o_dfi_data_p4                (o_dfi_wrdata_p4),
      .o_dfi_data_p5                (o_dfi_wrdata_p5),
      .o_dfi_data_p6                (o_dfi_wrdata_p6),
      .o_dfi_data_p7                (o_dfi_wrdata_p7),

      .o_debug                      (/*OPEN*/)
   );

   // ------------------------------------------------------------------------
   // DFI Write Bus Mask Datapath
   // ------------------------------------------------------------------------

   ddr_dfi_wdp #(
      .SWIDTH                       (MWIDTH),
      .SDR_MODE                     (1'b0),
      .FWIDTH                       (FWIDTH)
   ) u_wdp_wrm (
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_rst                        (i_rst),
      .i_clk_0                      (i_clk_0),
      .i_clk_1                      (i_clk_1),
      .i_clk_2                      (i_clk_2),
      .i_pipe_en                    (i_wrd_pipe_en),
      .i_wgb_mode                   (i_wrd_gb_mode),
      .i_post_gb_dly                (i_wrd_post_gb_dly),
      .i_phase_ext                  ('0),

      .i_dfi_data_p0                (i_dfi_wrdata_mask_p0),
      .i_dfi_data_p1                (i_dfi_wrdata_mask_p1),
      .i_dfi_data_p2                (i_dfi_wrdata_mask_p2),
      .i_dfi_data_p3                (i_dfi_wrdata_mask_p3),
      .i_dfi_data_p4                (i_dfi_wrdata_mask_p4),
      .i_dfi_data_p5                (i_dfi_wrdata_mask_p5),
      .i_dfi_data_p6                (i_dfi_wrdata_mask_p6),
      .i_dfi_data_p7                (i_dfi_wrdata_mask_p7),

      .o_dfi_data_p0                (o_dfi_wrdata_mask_p0),
      .o_dfi_data_p1                (o_dfi_wrdata_mask_p1),
      .o_dfi_data_p2                (o_dfi_wrdata_mask_p2),
      .o_dfi_data_p3                (o_dfi_wrdata_mask_p3),
      .o_dfi_data_p4                (o_dfi_wrdata_mask_p4),
      .o_dfi_data_p5                (o_dfi_wrdata_mask_p5),
      .o_dfi_data_p6                (o_dfi_wrdata_mask_p6),
      .o_dfi_data_p7                (o_dfi_wrdata_mask_p7),

      .o_debug                      (/*OPEN*/)
   );

endmodule

module ddr_dfi_write_en #(
   parameter F0WIDTH                = 2,
   parameter F1WIDTH                = 2,
   parameter F2WIDTH                = 2,
   parameter MAXF2DLY               = (1 << F2WIDTH) -1 ,
   parameter SWIDTH                 = 16,                     // PHY Slice Width
   parameter BWIDTH                 = SWIDTH / 8,             // Byte width
   parameter TWIDTH                 = BWIDTH * 2,             // Toggle width
   parameter PWIDTH                 = 4,                      // Pulse Extension width
   parameter NUM_WPH                = 8                    // Number of Phases
) (

   input  logic                     i_scan_cgc_ctrl,
   input  logic                     i_rst,

   // Clock
   input  logic                     i_clk_0,                  // Div1 clock
   input  logic                     i_clk_1,                  // Div2 clock
   input  logic                     i_clk_2,                  // Div4 clock

   // Datapath Control
   input  logic                     i_wck_mode,               // 0: LP4/DDR/HBM mode, 1: LP5/GDDR mode
   input  logic                     i_wctrl_pipe_en,
   input  dwgb_t                    i_wctrl_gb_mode,
   input  logic [F1WIDTH-1:0]       i_wctrl_post_gb_dly,
   input  logic                     i_wenctrl_pipe_en,
   input  dwgb_t                    i_wenctrl_gb_mode,
   input  logic [F2WIDTH-1:0]       i_wenctrl_post_gb_dly,
   input  logic                     i_wckctrl_pipe_en,
   input  dwgb_t                    i_wckctrl_gb_mode,
   input  logic [F1WIDTH-1:0]       i_wckctrl_post_gb_dly,
   input  logic                     i_wrd_pipe_en,
   input  dwgb_t                    i_wrd_gb_mode,
   input  logic [F0WIDTH-1:0]       i_wrd_post_gb_dly,

   input  logic [PWIDTH-1:0]        i_wrden_phase_ext,           // Pulse extension cycles @ phy clock rate.
   input  logic [PWIDTH-1:0]        i_wrdoe_phase_ext,           // Pulse extension cycles @ phy clock rate.
   input  logic [PWIDTH-1:0]        i_wrdcs_phase_ext,           // Pulse extension cycles @ phy clock rate.
   input  logic [PWIDTH-1:0]        i_wckoe_phase_ext,           // Pulse extension cycles @ phy clock rate.
   input  logic [PWIDTH-1:0]        i_wckcs_phase_ext,           // Pulse extension cycles @ phy clock rate.

   // Write Enable
   input  logic                     i_dfi_wrdata_en_p0,
   input  logic                     i_dfi_wrdata_en_p1,
   input  logic                     i_dfi_wrdata_en_p2,
   input  logic                     i_dfi_wrdata_en_p3,
   input  logic                     i_dfi_wrdata_en_p4,
   input  logic                     i_dfi_wrdata_en_p5,
   input  logic                     i_dfi_wrdata_en_p6,
   input  logic                     i_dfi_wrdata_en_p7,
   input  logic                     i_dfi_parity_in_p0,
   input  logic                     i_dfi_parity_in_p1,
   input  logic                     i_dfi_parity_in_p2,
   input  logic                     i_dfi_parity_in_p3,
   input  logic                     i_dfi_parity_in_p4,
   input  logic                     i_dfi_parity_in_p5,
   input  logic                     i_dfi_parity_in_p6,
   input  logic                     i_dfi_parity_in_p7,
   input  logic                     i_dfi_wrdata_cs_p0,
   input  logic                     i_dfi_wrdata_cs_p1,
   input  logic                     i_dfi_wrdata_cs_p2,
   input  logic                     i_dfi_wrdata_cs_p3,
   input  logic                     i_dfi_wrdata_cs_p4,
   input  logic                     i_dfi_wrdata_cs_p5,
   input  logic                     i_dfi_wrdata_cs_p6,
   input  logic                     i_dfi_wrdata_cs_p7,

   // WCK Control
   input  logic                     i_dfi_wck_cs_p0,
   input  logic                     i_dfi_wck_cs_p1,
   input  logic                     i_dfi_wck_cs_p2,
   input  logic                     i_dfi_wck_cs_p3,
   input  logic                     i_dfi_wck_cs_p4,
   input  logic                     i_dfi_wck_cs_p5,
   input  logic                     i_dfi_wck_cs_p6,
   input  logic                     i_dfi_wck_cs_p7,
   input  logic                     i_dfi_wck_en_p0,
   input  logic                     i_dfi_wck_en_p1,
   input  logic                     i_dfi_wck_en_p2,
   input  logic                     i_dfi_wck_en_p3,
   input  logic                     i_dfi_wck_en_p4,
   input  logic                     i_dfi_wck_en_p5,
   input  logic                     i_dfi_wck_en_p6,
   input  logic                     i_dfi_wck_en_p7,
   input  logic [TWIDTH-1:0]        i_dfi_wck_toggle_p0,
   input  logic [TWIDTH-1:0]        i_dfi_wck_toggle_p1,
   input  logic [TWIDTH-1:0]        i_dfi_wck_toggle_p2,
   input  logic [TWIDTH-1:0]        i_dfi_wck_toggle_p3,
   input  logic [TWIDTH-1:0]        i_dfi_wck_toggle_p4,
   input  logic [TWIDTH-1:0]        i_dfi_wck_toggle_p5,
   input  logic [TWIDTH-1:0]        i_dfi_wck_toggle_p6,
   input  logic [TWIDTH-1:0]        i_dfi_wck_toggle_p7,
   output logic                     o_dfi_wrdata_en_p0,
   output logic                     o_dfi_wrdata_en_p1,
   output logic                     o_dfi_wrdata_en_p2,
   output logic                     o_dfi_wrdata_en_p3,
   output logic                     o_dfi_wrdata_en_p4,
   output logic                     o_dfi_wrdata_en_p5,
   output logic                     o_dfi_wrdata_en_p6,
   output logic                     o_dfi_wrdata_en_p7,
   output logic                     o_dfi_wrdata_oe_p0,
   output logic                     o_dfi_wrdata_oe_p1,
   output logic                     o_dfi_wrdata_oe_p2,
   output logic                     o_dfi_wrdata_oe_p3,
   output logic                     o_dfi_wrdata_oe_p4,
   output logic                     o_dfi_wrdata_oe_p5,
   output logic                     o_dfi_wrdata_oe_p6,
   output logic                     o_dfi_wrdata_oe_p7,
   output logic                     o_dfi_parity_in_p0,
   output logic                     o_dfi_parity_in_p1,
   output logic                     o_dfi_parity_in_p2,
   output logic                     o_dfi_parity_in_p3,
   output logic                     o_dfi_parity_in_p4,
   output logic                     o_dfi_parity_in_p5,
   output logic                     o_dfi_parity_in_p6,
   output logic                     o_dfi_parity_in_p7,
   output logic                     o_dfi_wrdata_cs_p0,
   output logic                     o_dfi_wrdata_cs_p1,
   output logic                     o_dfi_wrdata_cs_p2,
   output logic                     o_dfi_wrdata_cs_p3,
   output logic                     o_dfi_wrdata_cs_p4,
   output logic                     o_dfi_wrdata_cs_p5,
   output logic                     o_dfi_wrdata_cs_p6,
   output logic                     o_dfi_wrdata_cs_p7,
   output logic                     o_dfi_wck_en_p0,
   output logic                     o_dfi_wck_en_p1,
   output logic                     o_dfi_wck_en_p2,
   output logic                     o_dfi_wck_en_p3,
   output logic                     o_dfi_wck_en_p4,
   output logic                     o_dfi_wck_en_p5,
   output logic                     o_dfi_wck_en_p6,
   output logic                     o_dfi_wck_en_p7,
   output logic                     o_dfi_wck_oe_p0,
   output logic                     o_dfi_wck_oe_p1,
   output logic                     o_dfi_wck_oe_p2,
   output logic                     o_dfi_wck_oe_p3,
   output logic                     o_dfi_wck_oe_p4,
   output logic                     o_dfi_wck_oe_p5,
   output logic                     o_dfi_wck_oe_p6,
   output logic                     o_dfi_wck_oe_p7,
   output logic                     o_dfi_wck_ten_p0,
   output logic                     o_dfi_wck_ten_p1,
   output logic                     o_dfi_wck_ten_p2,
   output logic                     o_dfi_wck_ten_p3,
   output logic                     o_dfi_wck_ten_p4,
   output logic                     o_dfi_wck_ten_p5,
   output logic                     o_dfi_wck_ten_p6,
   output logic                     o_dfi_wck_ten_p7,
   output logic                     o_dfi_wck_cs_p0,
   output logic                     o_dfi_wck_cs_p1,
   output logic                     o_dfi_wck_cs_p2,
   output logic                     o_dfi_wck_cs_p3,
   output logic                     o_dfi_wck_cs_p4,
   output logic                     o_dfi_wck_cs_p5,
   output logic                     o_dfi_wck_cs_p6,
   output logic                     o_dfi_wck_cs_p7,

   output logic [31:0]              o_debug
);

    assign o_debug = '0 ; //FXIME
   // ------------------------------------------------------------------------
   // DFI Write Bus Enable Datapath
   // ------------------------------------------------------------------------

   ddr_dfi_wdp #(
      .FWIDTH                       (F2WIDTH),
      .MAXDLY                       (MAXF2DLY),
      .SWIDTH                       (1),
      .DWIDTH                       (1),
      .PWIDTH                       (PWIDTH),
      .PHASE_EXT_EN                 (1),
      .SDR_MODE                     (1'b1)
   ) u_wdp_wen (
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_rst                        (i_rst),
      .i_clk_0                      (i_clk_0),
      .i_clk_1                      (i_clk_1),
      .i_clk_2                      (i_clk_2),
      .i_pipe_en                    (i_wenctrl_pipe_en),
      .i_wgb_mode                   (i_wenctrl_gb_mode),
      .i_post_gb_dly                (i_wenctrl_post_gb_dly),
      .i_phase_ext                  (i_wrden_phase_ext),

      // Configure for SDR mode
      .i_dfi_data_p0                (i_dfi_wrdata_en_p0),
      .i_dfi_data_p1                (i_dfi_wrdata_en_p1),
      .i_dfi_data_p2                (i_dfi_wrdata_en_p2),
      .i_dfi_data_p3                (i_dfi_wrdata_en_p3),
      .i_dfi_data_p4                (i_dfi_wrdata_en_p4),
      .i_dfi_data_p5                (i_dfi_wrdata_en_p5),
      .i_dfi_data_p6                (i_dfi_wrdata_en_p6),
      .i_dfi_data_p7                (i_dfi_wrdata_en_p7),

      .o_dfi_data_p0                (o_dfi_wrdata_en_p0),
      .o_dfi_data_p1                (o_dfi_wrdata_en_p1),
      .o_dfi_data_p2                (o_dfi_wrdata_en_p2),
      .o_dfi_data_p3                (o_dfi_wrdata_en_p3),
      .o_dfi_data_p4                (o_dfi_wrdata_en_p4),
      .o_dfi_data_p5                (o_dfi_wrdata_en_p5),
      .o_dfi_data_p6                (o_dfi_wrdata_en_p6),
      .o_dfi_data_p7                (o_dfi_wrdata_en_p7),
      .o_debug                      (/*OPEN*/)
   );

   ddr_dfi_wdp #(
      .FWIDTH                       (F1WIDTH),
      .SWIDTH                       (1),
      .DWIDTH                       (1),
      .PWIDTH                       (PWIDTH),
      .PHASE_EXT_EN                 (1),
      .SDR_MODE                     (1'b1)
   ) u_wdp_woe (
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_rst                        (i_rst),
      .i_clk_0                      (i_clk_0),
      .i_clk_1                      (i_clk_1),
      .i_clk_2                      (i_clk_2),
      .i_pipe_en                    (i_wctrl_pipe_en),
      .i_wgb_mode                   (i_wctrl_gb_mode),
      .i_post_gb_dly                (i_wctrl_post_gb_dly),
      .i_phase_ext                  (i_wrdoe_phase_ext),

      // Configure for SDR mode
      .i_dfi_data_p0                (i_dfi_wrdata_en_p0),
      .i_dfi_data_p1                (i_dfi_wrdata_en_p1),
      .i_dfi_data_p2                (i_dfi_wrdata_en_p2),
      .i_dfi_data_p3                (i_dfi_wrdata_en_p3),
      .i_dfi_data_p4                (i_dfi_wrdata_en_p4),
      .i_dfi_data_p5                (i_dfi_wrdata_en_p5),
      .i_dfi_data_p6                (i_dfi_wrdata_en_p6),
      .i_dfi_data_p7                (i_dfi_wrdata_en_p7),

      .o_dfi_data_p0                (o_dfi_wrdata_oe_p0),
      .o_dfi_data_p1                (o_dfi_wrdata_oe_p1),
      .o_dfi_data_p2                (o_dfi_wrdata_oe_p2),
      .o_dfi_data_p3                (o_dfi_wrdata_oe_p3),
      .o_dfi_data_p4                (o_dfi_wrdata_oe_p4),
      .o_dfi_data_p5                (o_dfi_wrdata_oe_p5),
      .o_dfi_data_p6                (o_dfi_wrdata_oe_p6),
      .o_dfi_data_p7                (o_dfi_wrdata_oe_p7),

      .o_debug                      (/*OPEN*/)
   );

   // ------------------------------------------------------------------------
   // DFI Write Bus CS Datapath
   // ------------------------------------------------------------------------

   ddr_dfi_wdp #(
      .FWIDTH                       (F1WIDTH),
      .SWIDTH                       (1),
      .DWIDTH                       (1),
      .PWIDTH                       (PWIDTH),
      .PHASE_EXT_EN                 (1),
      .SDR_MODE                     (1'b1)
   ) u_wdp_wcs (
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_rst                        (i_rst),
      .i_clk_0                      (i_clk_0),
      .i_clk_1                      (i_clk_1),
      .i_clk_2                      (i_clk_2),
      .i_pipe_en                    (i_wctrl_pipe_en),
      .i_wgb_mode                   (i_wctrl_gb_mode),
      .i_post_gb_dly                (i_wctrl_post_gb_dly),
      .i_phase_ext                  (i_wrdcs_phase_ext),

      // Configure for SDR mode
      .i_dfi_data_p0                (i_dfi_wrdata_cs_p0),
      .i_dfi_data_p1                (i_dfi_wrdata_cs_p1),
      .i_dfi_data_p2                (i_dfi_wrdata_cs_p2),
      .i_dfi_data_p3                (i_dfi_wrdata_cs_p3),
      .i_dfi_data_p4                (i_dfi_wrdata_cs_p4),
      .i_dfi_data_p5                (i_dfi_wrdata_cs_p5),
      .i_dfi_data_p6                (i_dfi_wrdata_cs_p6),
      .i_dfi_data_p7                (i_dfi_wrdata_cs_p7),

      .o_dfi_data_p0                (o_dfi_wrdata_cs_p0),
      .o_dfi_data_p1                (o_dfi_wrdata_cs_p1),
      .o_dfi_data_p2                (o_dfi_wrdata_cs_p2),
      .o_dfi_data_p3                (o_dfi_wrdata_cs_p3),
      .o_dfi_data_p4                (o_dfi_wrdata_cs_p4),
      .o_dfi_data_p5                (o_dfi_wrdata_cs_p5),
      .o_dfi_data_p6                (o_dfi_wrdata_cs_p6),
      .o_dfi_data_p7                (o_dfi_wrdata_cs_p7),

      .o_debug                      (/*OPEN*/)
   );

   // ------------------------------------------------------------------------
   // DFI WCK Enable Datapath
   // ------------------------------------------------------------------------

   ddr_dfi_wdp #(
      .FWIDTH                       (F1WIDTH),
      .SWIDTH                       (1),
      .DWIDTH                       (1),
      .PWIDTH                       (PWIDTH),
      .PHASE_EXT_EN                 (0),
      .SDR_MODE                     (1'b1)
   ) u_wdp_wcken (
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_rst                        (i_rst),
      .i_clk_0                      (i_clk_0),
      .i_clk_1                      (i_clk_1),
      .i_clk_2                      (i_clk_2),
      .i_pipe_en                    (i_wckctrl_pipe_en),
      .i_wgb_mode                   (i_wckctrl_gb_mode),
      .i_post_gb_dly                (i_wckctrl_post_gb_dly),
      .i_phase_ext                  ('0),

      // Configure for SDR mode
      .i_dfi_data_p0                (i_dfi_wck_en_p0),
      .i_dfi_data_p1                (i_dfi_wck_en_p1),
      .i_dfi_data_p2                (i_dfi_wck_en_p2),
      .i_dfi_data_p3                (i_dfi_wck_en_p3),
      .i_dfi_data_p4                (i_dfi_wck_en_p4),
      .i_dfi_data_p5                (i_dfi_wck_en_p5),
      .i_dfi_data_p6                (i_dfi_wck_en_p6),
      .i_dfi_data_p7                (i_dfi_wck_en_p7),

      .o_dfi_data_p0                (o_dfi_wck_en_p0),
      .o_dfi_data_p1                (o_dfi_wck_en_p1),
      .o_dfi_data_p2                (o_dfi_wck_en_p2),
      .o_dfi_data_p3                (o_dfi_wck_en_p3),
      .o_dfi_data_p4                (o_dfi_wck_en_p4),
      .o_dfi_data_p5                (o_dfi_wck_en_p5),
      .o_dfi_data_p6                (o_dfi_wck_en_p6),
      .o_dfi_data_p7                (o_dfi_wck_en_p7),

      .o_debug                      (/*OPEN*/)
   );

   logic  dfi_wck_enable_p0;
   logic  dfi_wck_enable_p1;
   logic  dfi_wck_enable_p2;
   logic  dfi_wck_enable_p3;
   logic  dfi_wck_enable_p4;
   logic  dfi_wck_enable_p5;
   logic  dfi_wck_enable_p6;
   logic  dfi_wck_enable_p7;
   assign dfi_wck_enable_p0 = i_wck_mode ? i_dfi_wck_en_p0 : '0;
   assign dfi_wck_enable_p1 = i_wck_mode ? i_dfi_wck_en_p1 : '0;
   assign dfi_wck_enable_p2 = i_wck_mode ? i_dfi_wck_en_p2 : '0;
   assign dfi_wck_enable_p3 = i_wck_mode ? i_dfi_wck_en_p3 : '0;
   assign dfi_wck_enable_p4 = i_wck_mode ? i_dfi_wck_en_p4 : '0;
   assign dfi_wck_enable_p5 = i_wck_mode ? i_dfi_wck_en_p5 : '0;
   assign dfi_wck_enable_p6 = i_wck_mode ? i_dfi_wck_en_p6 : '0;
   assign dfi_wck_enable_p7 = i_wck_mode ? i_dfi_wck_en_p7 : '0;

   ddr_dfi_wdp #(
      .FWIDTH                       (F1WIDTH),
      .SWIDTH                       (1),
      .DWIDTH                       (1),
      .PWIDTH                       (PWIDTH),
      .PHASE_EXT_EN                 (1),
      .SDR_MODE                     (1'b1)
   ) u_wdp_wckoe (
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_rst                        (i_rst),
      .i_clk_0                      (i_clk_0),
      .i_clk_1                      (i_clk_1),
      .i_clk_2                      (i_clk_2),
      .i_pipe_en                    (i_wckctrl_pipe_en),
      .i_wgb_mode                   (i_wckctrl_gb_mode),
      .i_post_gb_dly                (i_wckctrl_post_gb_dly),
      .i_phase_ext                  (i_wckoe_phase_ext),

      // Configure for SDR mode
      .i_dfi_data_p0                (dfi_wck_enable_p0),
      .i_dfi_data_p1                (dfi_wck_enable_p1),
      .i_dfi_data_p2                (dfi_wck_enable_p2),
      .i_dfi_data_p3                (dfi_wck_enable_p3),
      .i_dfi_data_p4                (dfi_wck_enable_p4),
      .i_dfi_data_p5                (dfi_wck_enable_p5),
      .i_dfi_data_p6                (dfi_wck_enable_p6),
      .i_dfi_data_p7                (dfi_wck_enable_p7),

      .o_dfi_data_p0                (o_dfi_wck_oe_p0),
      .o_dfi_data_p1                (o_dfi_wck_oe_p1),
      .o_dfi_data_p2                (o_dfi_wck_oe_p2),
      .o_dfi_data_p3                (o_dfi_wck_oe_p3),
      .o_dfi_data_p4                (o_dfi_wck_oe_p4),
      .o_dfi_data_p5                (o_dfi_wck_oe_p5),
      .o_dfi_data_p6                (o_dfi_wck_oe_p6),
      .o_dfi_data_p7                (o_dfi_wck_oe_p7),

      .o_debug                      (/*OPEN*/)
   );

   // ------------------------------------------------------------------------
   // DFI WCK CS Datapath
   // ------------------------------------------------------------------------

  ddr_dfi_wdp #(
      .FWIDTH                       (F1WIDTH),
      .SWIDTH                       (1),
      .DWIDTH                       (1),
      .PWIDTH                       (PWIDTH),
      .PHASE_EXT_EN                 (1),
      .SDR_MODE                     (1'b1)
   ) u_wdp_wckcs (
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_rst                        (i_rst),
      .i_clk_0                      (i_clk_0),
      .i_clk_1                      (i_clk_1),
      .i_clk_2                      (i_clk_2),
      .i_pipe_en                    (i_wckctrl_pipe_en),
      .i_wgb_mode                   (i_wckctrl_gb_mode),
      .i_post_gb_dly                (i_wckctrl_post_gb_dly),
      .i_phase_ext                  (i_wckcs_phase_ext),

      // Configure for SDR mode
      .i_dfi_data_p0                (i_dfi_wck_cs_p0),
      .i_dfi_data_p1                (i_dfi_wck_cs_p1),
      .i_dfi_data_p2                (i_dfi_wck_cs_p2),
      .i_dfi_data_p3                (i_dfi_wck_cs_p3),
      .i_dfi_data_p4                (i_dfi_wck_cs_p4),
      .i_dfi_data_p5                (i_dfi_wck_cs_p5),
      .i_dfi_data_p6                (i_dfi_wck_cs_p6),
      .i_dfi_data_p7                (i_dfi_wck_cs_p7),

      .o_dfi_data_p0                (o_dfi_wck_cs_p0),
      .o_dfi_data_p1                (o_dfi_wck_cs_p1),
      .o_dfi_data_p2                (o_dfi_wck_cs_p2),
      .o_dfi_data_p3                (o_dfi_wck_cs_p3),
      .o_dfi_data_p4                (o_dfi_wck_cs_p4),
      .o_dfi_data_p5                (o_dfi_wck_cs_p5),
      .o_dfi_data_p6                (o_dfi_wck_cs_p6),
      .o_dfi_data_p7                (o_dfi_wck_cs_p7),

      .o_debug                      (/*OPEN*/)
   );

   // ------------------------------------------------------------------------
   // DFI WCK Toggle Datapath
   // ------------------------------------------------------------------------
   logic  dfi_wck_ten_p0;
   logic  dfi_wck_ten_p1;
   logic  dfi_wck_ten_p2;
   logic  dfi_wck_ten_p3;
   logic  dfi_wck_ten_p4;
   logic  dfi_wck_ten_p5;
   logic  dfi_wck_ten_p6;
   logic  dfi_wck_ten_p7;

   logic [TWIDTH-1:0] dfi_wck_toggle_p0;
   logic [TWIDTH-1:0] dfi_wck_toggle_p1;
   logic [TWIDTH-1:0] dfi_wck_toggle_p2;
   logic [TWIDTH-1:0] dfi_wck_toggle_p3;
   logic [TWIDTH-1:0] dfi_wck_toggle_p4;
   logic [TWIDTH-1:0] dfi_wck_toggle_p5;
   logic [TWIDTH-1:0] dfi_wck_toggle_p6;
   logic [TWIDTH-1:0] dfi_wck_toggle_p7;

   ddr_dfi_wdp #(
      .FWIDTH                       (F1WIDTH),
      .SWIDTH                       (TWIDTH),
      .DWIDTH                       (TWIDTH),
      .SDR_MODE                     (1'b1)
   ) u_wdp_wckten (
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_rst                        (i_rst),
      .i_clk_0                      (i_clk_0),
      .i_clk_1                      (i_clk_1),
      .i_clk_2                      (i_clk_2),
      .i_pipe_en                    (i_wckctrl_pipe_en),
      .i_wgb_mode                   (i_wckctrl_gb_mode),
      .i_post_gb_dly                (i_wckctrl_post_gb_dly),
      .i_phase_ext                  ('0),

      // Configure for SDR mode
      .i_dfi_data_p0                (i_dfi_wck_toggle_p0),
      .i_dfi_data_p1                (i_dfi_wck_toggle_p1),
      .i_dfi_data_p2                (i_dfi_wck_toggle_p2),
      .i_dfi_data_p3                (i_dfi_wck_toggle_p3),
      .i_dfi_data_p4                (i_dfi_wck_toggle_p4),
      .i_dfi_data_p5                (i_dfi_wck_toggle_p5),
      .i_dfi_data_p6                (i_dfi_wck_toggle_p6),
      .i_dfi_data_p7                (i_dfi_wck_toggle_p7),

      .o_dfi_data_p0                (dfi_wck_toggle_p0),
      .o_dfi_data_p1                (dfi_wck_toggle_p1),
      .o_dfi_data_p2                (dfi_wck_toggle_p2),
      .o_dfi_data_p3                (dfi_wck_toggle_p3),
      .o_dfi_data_p4                (dfi_wck_toggle_p4),
      .o_dfi_data_p5                (dfi_wck_toggle_p5),
      .o_dfi_data_p6                (dfi_wck_toggle_p6),
      .o_dfi_data_p7                (dfi_wck_toggle_p7),

      .o_debug                      (/*OPEN*/)
   );

   // FIXME : FIX WCK Toggler for PHY phases -> 8 and 16
   // Set the appropriate phase for the slow WCK toggle
   logic wck_toggle;
   always_ff @ (posedge i_clk_0) begin
      if (
          (dfi_wck_toggle_p2 != WCK_TOGGLE) &&
          (dfi_wck_toggle_p0 != WCK_TOGGLE))
            wck_toggle <= 1'b0;
      else if (
          (dfi_wck_toggle_p2 == WCK_TOGGLE) &&
          (dfi_wck_toggle_p0 != WCK_TOGGLE))
            wck_toggle <= 1'b1;
   end

   always_comb begin
      case ({dfi_wck_toggle_p2, dfi_wck_toggle_p0})
         {WCK_STATIC_LOW , WCK_STATIC_LOW } : {
                                               dfi_wck_ten_p3,
                                               dfi_wck_ten_p2,
                                               dfi_wck_ten_p1,
                                               dfi_wck_ten_p0
                                              } = 'b0;
         {WCK_STATIC_LOW , WCK_STATIC_HIGH} : {
                                               dfi_wck_ten_p3,
                                               dfi_wck_ten_p2,
                                               dfi_wck_ten_p1,
                                               dfi_wck_ten_p0
                                              } = 4'b0011;
         {WCK_STATIC_LOW , WCK_TOGGLE     } : {
                                               dfi_wck_ten_p3,
                                               dfi_wck_ten_p2,
                                               dfi_wck_ten_p1,
                                               dfi_wck_ten_p0
                                              } = wck_toggle ? 4'b0010 : 4'b0000;
         {WCK_STATIC_LOW , WCK_FAST_TOGGLE} : {
                                               dfi_wck_ten_p3,
                                               dfi_wck_ten_p2,
                                               dfi_wck_ten_p1,
                                               dfi_wck_ten_p0
                                              } = 4'b0010;
         {WCK_STATIC_HIGH, WCK_STATIC_LOW } : {
                                               dfi_wck_ten_p3,
                                               dfi_wck_ten_p2,
                                               dfi_wck_ten_p1,
                                               dfi_wck_ten_p0
                                              } = 4'b1100;
         {WCK_STATIC_HIGH, WCK_STATIC_HIGH} : {
                                               dfi_wck_ten_p3,
                                               dfi_wck_ten_p2,
                                               dfi_wck_ten_p1,
                                               dfi_wck_ten_p0
                                              } = 4'b1111;
         {WCK_STATIC_HIGH, WCK_TOGGLE     } : {
                                               dfi_wck_ten_p3,
                                               dfi_wck_ten_p2,
                                               dfi_wck_ten_p1,
                                               dfi_wck_ten_p0
                                              } = wck_toggle ? 4'b1110 : 4'b1100;
         {WCK_STATIC_HIGH, WCK_FAST_TOGGLE} : {
                                               dfi_wck_ten_p3,
                                               dfi_wck_ten_p2,
                                               dfi_wck_ten_p1,
                                               dfi_wck_ten_p0
                                              } = 4'b1110;
         {WCK_TOGGLE     , WCK_STATIC_LOW } : {
                                               dfi_wck_ten_p3,
                                               dfi_wck_ten_p2,
                                               dfi_wck_ten_p1,
                                               dfi_wck_ten_p0
                                              } = 4'b1000;
         {WCK_TOGGLE     , WCK_STATIC_HIGH} : {
                                               dfi_wck_ten_p3,
                                               dfi_wck_ten_p2,
                                               dfi_wck_ten_p1,
                                               dfi_wck_ten_p0
                                              } = 4'b1011;
         {WCK_TOGGLE     , WCK_TOGGLE     } : {
                                               dfi_wck_ten_p3,
                                               dfi_wck_ten_p2,
                                               dfi_wck_ten_p1,
                                               dfi_wck_ten_p0
                                              } = wck_toggle ? 4'b0010 : 4'b1000;
         {WCK_TOGGLE     , WCK_FAST_TOGGLE} : {
                                               dfi_wck_ten_p3,
                                               dfi_wck_ten_p2,
                                               dfi_wck_ten_p1,
                                               dfi_wck_ten_p0
                                              } = 4'b0010;
         {WCK_FAST_TOGGLE, WCK_STATIC_LOW } : {
                                               dfi_wck_ten_p3,
                                               dfi_wck_ten_p2,
                                               dfi_wck_ten_p1,
                                               dfi_wck_ten_p0
                                              } = 4'b1000;
         {WCK_FAST_TOGGLE, WCK_STATIC_HIGH} : {
                                               dfi_wck_ten_p3,
                                               dfi_wck_ten_p2,
                                               dfi_wck_ten_p1,
                                               dfi_wck_ten_p0} = 4'b1011;
         {WCK_FAST_TOGGLE, WCK_TOGGLE     } : {
                                               dfi_wck_ten_p3,
                                               dfi_wck_ten_p2,
                                               dfi_wck_ten_p1,
                                               dfi_wck_ten_p0
                                              } = wck_toggle ? 4'b1010 : 4'b1000;
         {WCK_FAST_TOGGLE, WCK_FAST_TOGGLE} : {
                                               dfi_wck_ten_p7,
                                               dfi_wck_ten_p6,
                                               dfi_wck_ten_p5,
                                               dfi_wck_ten_p4,
                                               dfi_wck_ten_p3,
                                               dfi_wck_ten_p2,
                                               dfi_wck_ten_p1,
                                               dfi_wck_ten_p0
                                              } = 8'b10101010;
      endcase
   end

   assign o_dfi_wck_ten_p0 = i_wck_mode ? dfi_wck_ten_p0 & o_dfi_wck_en_p0 : '0; // Not used in LP4x mode and used as WCK in LP5 mode, see parity below
   assign o_dfi_wck_ten_p1 = i_wck_mode ? dfi_wck_ten_p1 & o_dfi_wck_en_p1 : '0; // Not used in LP4x mode and used as WCK in LP5 mode, see parity below
   assign o_dfi_wck_ten_p2 = i_wck_mode ? dfi_wck_ten_p2 & o_dfi_wck_en_p2 : '0; // Not used in LP4x mode and used as WCK in LP5 mode, see parity below
   assign o_dfi_wck_ten_p3 = i_wck_mode ? dfi_wck_ten_p3 & o_dfi_wck_en_p3 : '0; // Not used in LP4x mode and used as WCK in LP5 mode, see parity below
   assign o_dfi_wck_ten_p4 = i_wck_mode ? dfi_wck_ten_p4 & o_dfi_wck_en_p4 : '0; // Not used in LP4x mode and used as WCK in LP5 mode, see parity below
   assign o_dfi_wck_ten_p5 = i_wck_mode ? dfi_wck_ten_p5 & o_dfi_wck_en_p5 : '0; // Not used in LP4x mode and used as WCK in LP5 mode, see parity below
   assign o_dfi_wck_ten_p6 = i_wck_mode ? dfi_wck_ten_p6 & o_dfi_wck_en_p6 : '0; // Not used in LP4x mode and used as WCK in LP5 mode, see parity below
   assign o_dfi_wck_ten_p7 = i_wck_mode ? dfi_wck_ten_p7 & o_dfi_wck_en_p7 : '0; // Not used in LP4x mode and used as WCK in LP5 mode, see parity below

   // ------------------------------------------------------------------------
   // DFI Write Bus Parity Datapath
   // ------------------------------------------------------------------------

   logic dfi_parity_in_p0;
   logic int_dfi_wrdata_en_p0;
   logic dfi_parity_in_p1;
   logic int_dfi_wrdata_en_p1;
   logic dfi_parity_in_p2;
   logic int_dfi_wrdata_en_p2;
   logic dfi_parity_in_p3;
   logic int_dfi_wrdata_en_p3;
   logic dfi_parity_in_p4;
   logic int_dfi_wrdata_en_p4;
   logic dfi_parity_in_p5;
   logic int_dfi_wrdata_en_p5;
   logic dfi_parity_in_p6;
   logic int_dfi_wrdata_en_p6;
   logic dfi_parity_in_p7;
   logic int_dfi_wrdata_en_p7;

   ddr_dfi_wdp #(
      .FWIDTH                       (F0WIDTH),
      .SWIDTH                       (1),
      .DWIDTH                       (1),
      .SDR_MODE                     (1'b1)
   ) u_wdp_parity (
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_rst                        (i_rst),
      .i_clk_0                      (i_clk_0),
      .i_clk_1                      (i_clk_1),
      .i_clk_2                      (i_clk_2),
      .i_pipe_en                    (i_wrd_pipe_en),
      .i_wgb_mode                   (i_wrd_gb_mode),
      .i_post_gb_dly                (i_wrd_post_gb_dly),
      .i_phase_ext                  ('0),

      // Configure for SDR mode
      .i_dfi_data_p0                (i_dfi_parity_in_p0),
      .i_dfi_data_p1                (i_dfi_parity_in_p1),
      .i_dfi_data_p2                (i_dfi_parity_in_p2),
      .i_dfi_data_p3                (i_dfi_parity_in_p3),
      .i_dfi_data_p4                (i_dfi_parity_in_p4),
      .i_dfi_data_p5                (i_dfi_parity_in_p5),
      .i_dfi_data_p6                (i_dfi_parity_in_p6),
      .i_dfi_data_p7                (i_dfi_parity_in_p7),

      .o_dfi_data_p0                (dfi_parity_in_p0),
      .o_dfi_data_p1                (dfi_parity_in_p1),
      .o_dfi_data_p2                (dfi_parity_in_p2),
      .o_dfi_data_p3                (dfi_parity_in_p3),
      .o_dfi_data_p4                (dfi_parity_in_p4),
      .o_dfi_data_p5                (dfi_parity_in_p5),
      .o_dfi_data_p6                (dfi_parity_in_p6),
      .o_dfi_data_p7                (dfi_parity_in_p7),

      .o_debug                      (/*OPEN*/)
   );

   assign int_dfi_wrdata_en_p0   = o_dfi_wrdata_en_p0 ;
   assign int_dfi_wrdata_en_p1   = '0 ;
   assign int_dfi_wrdata_en_p2   = o_dfi_wrdata_en_p2 ;
   assign int_dfi_wrdata_en_p3   = '0 ;
   assign int_dfi_wrdata_en_p4   = o_dfi_wrdata_en_p4 ;
   assign int_dfi_wrdata_en_p5   = '0 ;
   assign int_dfi_wrdata_en_p6   = o_dfi_wrdata_en_p6 ;
   assign int_dfi_wrdata_en_p7   = '0 ;
   // Support parity in LP5 mode and DQS in LP4 mode
   assign o_dfi_parity_in_p0 = i_wck_mode ? dfi_parity_in_p0 : int_dfi_wrdata_en_p0;
   assign o_dfi_parity_in_p1 = i_wck_mode ? dfi_parity_in_p1 : int_dfi_wrdata_en_p1;
   assign o_dfi_parity_in_p2 = i_wck_mode ? dfi_parity_in_p2 : int_dfi_wrdata_en_p2;
   assign o_dfi_parity_in_p3 = i_wck_mode ? dfi_parity_in_p3 : int_dfi_wrdata_en_p3;
   assign o_dfi_parity_in_p4 = i_wck_mode ? dfi_parity_in_p4 : int_dfi_wrdata_en_p4;
   assign o_dfi_parity_in_p5 = i_wck_mode ? dfi_parity_in_p5 : int_dfi_wrdata_en_p5;
   assign o_dfi_parity_in_p6 = i_wck_mode ? dfi_parity_in_p6 : int_dfi_wrdata_en_p6;
   assign o_dfi_parity_in_p7 = i_wck_mode ? dfi_parity_in_p7 : int_dfi_wrdata_en_p7;

endmodule

module ddr_dfi_read_en #(
   parameter FWIDTH                 = 2,
   parameter PWIDTH                 = 4,                      // Pulse Extension width
   parameter NUM_WPH                = 8                    // Number of Phases
) (

   input  logic                     i_scan_cgc_ctrl,
   input  logic                     i_rst,

   // Clock
   input  logic                     i_clk_0,                  // Div1 clock
   input  logic                     i_clk_1,                  // Div2 clock
   input  logic                     i_clk_2,                  // Div4 clock

   // Datapath Control
   input  logic                     i_rctrl_pipe_en,
   input  dwgb_t                    i_rctrl_gb_mode,
   input  logic  [FWIDTH-1:0]       i_rctrl_post_gb_dly,

   input  logic [PWIDTH-1:0]        i_rcs_phase_ext,          // Phase extension cycles @ phy clock rate.
   input  logic [PWIDTH-1:0]        i_ren_phase_ext,          // Phase extension cycles @ phy clock rate.
   input  logic [PWIDTH-1:0]        i_ie_phase_ext,           // Phase extension cycles @ phy clock rate.
   input  logic [PWIDTH-1:0]        i_re_phase_ext,           // Phase extension cycles @ phy clock rate.

   input  logic                     i_dfi_rddata_en_p0,
   input  logic                     i_dfi_rddata_en_p1,
   input  logic                     i_dfi_rddata_en_p2,
   input  logic                     i_dfi_rddata_en_p3,
   input  logic                     i_dfi_rddata_en_p4,
   input  logic                     i_dfi_rddata_en_p5,
   input  logic                     i_dfi_rddata_en_p6,
   input  logic                     i_dfi_rddata_en_p7,

   input  logic                     i_dfi_rddata_cs_p0,
   input  logic                     i_dfi_rddata_cs_p1,
   input  logic                     i_dfi_rddata_cs_p2,
   input  logic                     i_dfi_rddata_cs_p3,
   input  logic                     i_dfi_rddata_cs_p4,
   input  logic                     i_dfi_rddata_cs_p5,
   input  logic                     i_dfi_rddata_cs_p6,
   input  logic                     i_dfi_rddata_cs_p7,

   output logic                     o_dfi_rddata_en_p0,
   output logic                     o_dfi_rddata_en_p1,
   output logic                     o_dfi_rddata_en_p2,
   output logic                     o_dfi_rddata_en_p3,
   output logic                     o_dfi_rddata_en_p4,
   output logic                     o_dfi_rddata_en_p5,
   output logic                     o_dfi_rddata_en_p6,
   output logic                     o_dfi_rddata_en_p7,
   output logic                     o_dfi_rddata_ie_p0,
   output logic                     o_dfi_rddata_ie_p1,
   output logic                     o_dfi_rddata_ie_p2,
   output logic                     o_dfi_rddata_ie_p3,
   output logic                     o_dfi_rddata_ie_p4,
   output logic                     o_dfi_rddata_ie_p5,
   output logic                     o_dfi_rddata_ie_p6,
   output logic                     o_dfi_rddata_ie_p7,
   output logic                     o_dfi_rddata_re_p0,
   output logic                     o_dfi_rddata_re_p1,
   output logic                     o_dfi_rddata_re_p2,
   output logic                     o_dfi_rddata_re_p3,
   output logic                     o_dfi_rddata_re_p4,
   output logic                     o_dfi_rddata_re_p5,
   output logic                     o_dfi_rddata_re_p6,
   output logic                     o_dfi_rddata_re_p7,

   output logic                     o_dfi_rddata_cs_p0,
   output logic                     o_dfi_rddata_cs_p1,
   output logic                     o_dfi_rddata_cs_p2,
   output logic                     o_dfi_rddata_cs_p3,
   output logic                     o_dfi_rddata_cs_p4,
   output logic                     o_dfi_rddata_cs_p5,
   output logic                     o_dfi_rddata_cs_p6,
   output logic                     o_dfi_rddata_cs_p7,

   output logic [31:0]              o_debug
);

    assign o_debug = '0 ; //FXIME
   // ------------------------------------------------------------------------
   // DFI Read Bus Enable Datapath
   // ------------------------------------------------------------------------

   ddr_dfi_wdp #(
      .FWIDTH                       (FWIDTH),
      .SWIDTH                       (1),
      .DWIDTH                       (1),
      .PWIDTH                       (PWIDTH),
      .PHASE_EXT_EN                 (1),
      .SDR_MODE                     (1'b1)
   ) u_wdp_ren (
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_rst                        (i_rst),
      .i_clk_0                      (i_clk_0),
      .i_clk_1                      (i_clk_1),
      .i_clk_2                      (i_clk_2),
      .i_pipe_en                    (i_rctrl_pipe_en),
      .i_wgb_mode                   (i_rctrl_gb_mode),
      .i_post_gb_dly                (i_rctrl_post_gb_dly),
      .i_phase_ext                  (i_ren_phase_ext),

      // Configure for SDR mode
      .i_dfi_data_p0                (i_dfi_rddata_en_p0),
      .i_dfi_data_p1                (i_dfi_rddata_en_p1),
      .i_dfi_data_p2                (i_dfi_rddata_en_p2),
      .i_dfi_data_p3                (i_dfi_rddata_en_p3),
      .i_dfi_data_p4                (i_dfi_rddata_en_p4),
      .i_dfi_data_p5                (i_dfi_rddata_en_p5),
      .i_dfi_data_p6                (i_dfi_rddata_en_p6),
      .i_dfi_data_p7                (i_dfi_rddata_en_p7),

      .o_dfi_data_p0                (o_dfi_rddata_en_p0),
      .o_dfi_data_p1                (o_dfi_rddata_en_p1),
      .o_dfi_data_p2                (o_dfi_rddata_en_p2),
      .o_dfi_data_p3                (o_dfi_rddata_en_p3),
      .o_dfi_data_p4                (o_dfi_rddata_en_p4),
      .o_dfi_data_p5                (o_dfi_rddata_en_p5),
      .o_dfi_data_p6                (o_dfi_rddata_en_p6),
      .o_dfi_data_p7                (o_dfi_rddata_en_p7),

      .o_debug                      (/*OPEN*/)
   );

   ddr_dfi_wdp #(
      .FWIDTH                       (FWIDTH),
      .SWIDTH                       (1),
      .DWIDTH                       (1),
      .PWIDTH                       (PWIDTH),
      .PHASE_EXT_EN                 (1),
      .SDR_MODE                     (1'b1)
   ) u_wdp_ie (
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_rst                        (i_rst),
      .i_clk_0                      (i_clk_0),
      .i_clk_1                      (i_clk_1),
      .i_clk_2                      (i_clk_2),
      .i_pipe_en                    (i_rctrl_pipe_en),
      .i_wgb_mode                   (i_rctrl_gb_mode),
      .i_post_gb_dly                (i_rctrl_post_gb_dly),
      .i_phase_ext                  (i_ie_phase_ext),

      // Configure for SDR mode
      .i_dfi_data_p0                (i_dfi_rddata_en_p0),
      .i_dfi_data_p1                (i_dfi_rddata_en_p1),
      .i_dfi_data_p2                (i_dfi_rddata_en_p2),
      .i_dfi_data_p3                (i_dfi_rddata_en_p3),
      .i_dfi_data_p4                (i_dfi_rddata_en_p4),
      .i_dfi_data_p5                (i_dfi_rddata_en_p5),
      .i_dfi_data_p6                (i_dfi_rddata_en_p6),
      .i_dfi_data_p7                (i_dfi_rddata_en_p7),

      .o_dfi_data_p0                (o_dfi_rddata_ie_p0),
      .o_dfi_data_p1                (o_dfi_rddata_ie_p1),
      .o_dfi_data_p2                (o_dfi_rddata_ie_p2),
      .o_dfi_data_p3                (o_dfi_rddata_ie_p3),
      .o_dfi_data_p4                (o_dfi_rddata_ie_p4),
      .o_dfi_data_p5                (o_dfi_rddata_ie_p5),
      .o_dfi_data_p6                (o_dfi_rddata_ie_p6),
      .o_dfi_data_p7                (o_dfi_rddata_ie_p7),

      .o_debug                      (/*OPEN*/)
   );

   ddr_dfi_wdp #(
      .FWIDTH                       (FWIDTH),
      .SWIDTH                       (1),
      .DWIDTH                       (1),
      .PWIDTH                       (PWIDTH),
      .PHASE_EXT_EN                 (1),
      .SDR_MODE                     (1'b1)
   ) u_wdp_re (
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_rst                        (i_rst),
      .i_clk_0                      (i_clk_0),
      .i_clk_1                      (i_clk_1),
      .i_clk_2                      (i_clk_2),
      .i_pipe_en                    (i_rctrl_pipe_en),
      .i_wgb_mode                   (i_rctrl_gb_mode),
      .i_post_gb_dly                (i_rctrl_post_gb_dly),
      .i_phase_ext                  (i_re_phase_ext),

      // Configure for SDR mode
      .i_dfi_data_p0                (i_dfi_rddata_en_p0),
      .i_dfi_data_p1                (i_dfi_rddata_en_p1),
      .i_dfi_data_p2                (i_dfi_rddata_en_p2),
      .i_dfi_data_p3                (i_dfi_rddata_en_p3),
      .i_dfi_data_p4                (i_dfi_rddata_en_p4),
      .i_dfi_data_p5                (i_dfi_rddata_en_p5),
      .i_dfi_data_p6                (i_dfi_rddata_en_p6),
      .i_dfi_data_p7                (i_dfi_rddata_en_p7),

      .o_dfi_data_p0                (o_dfi_rddata_re_p0),
      .o_dfi_data_p1                (o_dfi_rddata_re_p1),
      .o_dfi_data_p2                (o_dfi_rddata_re_p2),
      .o_dfi_data_p3                (o_dfi_rddata_re_p3),
      .o_dfi_data_p4                (o_dfi_rddata_re_p4),
      .o_dfi_data_p5                (o_dfi_rddata_re_p5),
      .o_dfi_data_p6                (o_dfi_rddata_re_p6),
      .o_dfi_data_p7                (o_dfi_rddata_re_p7),

      .o_debug                      (/*OPEN*/)
   );

   // ------------------------------------------------------------------------
   // DFI Read Bus CS Datapath
   // ------------------------------------------------------------------------
   ddr_dfi_wdp #(
      .FWIDTH                       (FWIDTH),
      .SWIDTH                       (1),
      .DWIDTH                       (1),
      .PWIDTH                       (PWIDTH),
      .PHASE_EXT_EN                 (1),
      .SDR_MODE                     (1'b1)
   ) u_wdp_rcs (
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_rst                        (i_rst),
      .i_clk_0                      (i_clk_0),
      .i_clk_1                      (i_clk_1),
      .i_clk_2                      (i_clk_2),
      .i_pipe_en                    (i_rctrl_pipe_en),
      .i_wgb_mode                   (i_rctrl_gb_mode),
      .i_post_gb_dly                (i_rctrl_post_gb_dly),
      .i_phase_ext                  (i_rcs_phase_ext),

      // Configure for SDR mode
      .i_dfi_data_p0               (i_dfi_rddata_cs_p0),
      .i_dfi_data_p1               (i_dfi_rddata_cs_p1),
      .i_dfi_data_p2               (i_dfi_rddata_cs_p2),
      .i_dfi_data_p3               (i_dfi_rddata_cs_p3),
      .i_dfi_data_p4               (i_dfi_rddata_cs_p4),
      .i_dfi_data_p5               (i_dfi_rddata_cs_p5),
      .i_dfi_data_p6               (i_dfi_rddata_cs_p6),
      .i_dfi_data_p7               (i_dfi_rddata_cs_p7),

      .o_dfi_data_p0               (o_dfi_rddata_cs_p0),
      .o_dfi_data_p1               (o_dfi_rddata_cs_p1),
      .o_dfi_data_p2               (o_dfi_rddata_cs_p2),
      .o_dfi_data_p3               (o_dfi_rddata_cs_p3),
      .o_dfi_data_p4               (o_dfi_rddata_cs_p4),
      .o_dfi_data_p5               (o_dfi_rddata_cs_p5),
      .o_dfi_data_p6               (o_dfi_rddata_cs_p6),
      .o_dfi_data_p7               (o_dfi_rddata_cs_p7),

      .o_debug                      (/*OPEN*/)
   );

endmodule

module ddr_dfi_wdp #(
   parameter       FWIDTH           = 2,
   parameter       MAXDLY           = (1 << FWIDTH) - 1,
   parameter       SWIDTH           = 16,           // PHY Slice Width
   parameter       DWIDTH           = SWIDTH * 2,   // Data Width R+F
   parameter       PWIDTH           = 4,            // Phase Extension width
   parameter [0:0] SDR_MODE         = '0,           // 1: SDR mode, 0: DDR mode
   parameter       PHASE_EXT_EN     = 0,            // 1: Enable Phase extention support , 0: Disable Phase Extenstion support.
   parameter       NUM_WPH          = 8                    // Number of Phases
) (

   input  logic                     i_scan_cgc_ctrl,

   input  logic                     i_clk_0,        // Div2 clock
   input  logic                     i_clk_1,        // Div2 clock
   input  logic                     i_clk_2,        // Div4 clock
   input  logic                     i_rst,

   input  logic                     i_pipe_en,
   input  dwgb_t                    i_wgb_mode,
   input  logic [FWIDTH-1:0]        i_post_gb_dly,
   input  logic [PWIDTH-1:0]        i_phase_ext,           // Pulse extension cycles @ phy clock rate.

   input  logic [SWIDTH-1:0]        i_dfi_data_p0,
   input  logic [SWIDTH-1:0]        i_dfi_data_p1,
   input  logic [SWIDTH-1:0]        i_dfi_data_p2,
   input  logic [SWIDTH-1:0]        i_dfi_data_p3,
   input  logic [SWIDTH-1:0]        i_dfi_data_p4,
   input  logic [SWIDTH-1:0]        i_dfi_data_p5,
   input  logic [SWIDTH-1:0]        i_dfi_data_p6,
   input  logic [SWIDTH-1:0]        i_dfi_data_p7,

   output logic [SWIDTH-1:0]        o_dfi_data_p0,
   output logic [SWIDTH-1:0]        o_dfi_data_p1,
   output logic [SWIDTH-1:0]        o_dfi_data_p2,
   output logic [SWIDTH-1:0]        o_dfi_data_p3,
   output logic [SWIDTH-1:0]        o_dfi_data_p4,
   output logic [SWIDTH-1:0]        o_dfi_data_p5,
   output logic [SWIDTH-1:0]        o_dfi_data_p6,
   output logic [SWIDTH-1:0]        o_dfi_data_p7,

   output logic [31:0]              o_debug
);

   assign o_debug = '0 ; //FXIME

   localparam NDWIDTH   = NUM_WPH*SWIDTH;
   localparam GBNDWIDTH = 8*SWIDTH;

   integer i, idx;
   logic [NDWIDTH-1:0]   dfi_data, dfi_data_q, dfi_data_q_int;
   logic [GBNDWIDTH-1:0] dfi_data_gb, dfi_data_pext ;
   logic [SWIDTH-1:0]    gb_en ;

   // Lower half of the bus is rising edge of DQS and upper half is falling edge of DQS.
   // Concatenate and interleave DFI WDATA bus

   always_comb begin
      for(i=0; i<SWIDTH; i=i+1) begin
         idx = i*8;
         dfi_data[idx + 0] = i_dfi_data_p0 [i];
         dfi_data[idx + 1] = SDR_MODE ? i_dfi_data_p0[i] : i_dfi_data_p1[i];
         dfi_data[idx + 2] = i_dfi_data_p2 [i];
         dfi_data[idx + 3] = SDR_MODE ? i_dfi_data_p2[i] : i_dfi_data_p3[i];
         dfi_data[idx + 4] = i_dfi_data_p4 [i];
         dfi_data[idx + 5] = SDR_MODE ? i_dfi_data_p4[i] : i_dfi_data_p5[i];
         dfi_data[idx + 6] = i_dfi_data_p6 [i];
         dfi_data[idx + 7] = SDR_MODE ? i_dfi_data_p6[i] : i_dfi_data_p7[i];
      end
   end

   ddr_pipeline #(
      .DWIDTH                       (NDWIDTH)
   ) u_pipeline (
      .i_clk                        (i_clk_2),
      .i_pipe_en                    ({NDWIDTH{i_pipe_en}}),
      .i_d                          (dfi_data),
      .o_q                          (dfi_data_q)
   );

   genvar j;
   generate
      for (j=0; j<SWIDTH; j=j+1) begin : GEARBOX
         ddr_gearbox_down # (
           .NUM_IN_PHASES  (NUM_WPH  ),
           .NUM_OUT_PHASES (8)
         ) u_gearbox (
            .i_scan_cgc_ctrl        (i_scan_cgc_ctrl),
            .i_clk_1                (i_clk_1),
            .i_clk_2                (i_clk_2),
            .i_mode                 (i_wgb_mode),
            .o_gb_en                (gb_en[j]),
            .o_d                    ( {
                                        dfi_data_gb[(SWIDTH*7)+j],
                                        dfi_data_gb[(SWIDTH*6)+j],
                                        dfi_data_gb[(SWIDTH*5)+j],
                                        dfi_data_gb[(SWIDTH*4)+j],
                                        dfi_data_gb[(SWIDTH*3)+j],
                                        dfi_data_gb[(SWIDTH*2)+j],
                                        dfi_data_gb[(SWIDTH*1)+j],
                                        dfi_data_gb[(SWIDTH*0)+j]
                                     } ),
            .i_d                    (dfi_data_q[NUM_WPH*j+:NUM_WPH])
         );

         if(PHASE_EXT_EN == 1) begin : PEXT
         ddr_dfi_phase_extender #(
            .PWIDTH                       (PWIDTH),
            .NPH                          (8)
         ) u_phase_ext (
            .i_clk                        (i_clk_0),
            .i_rst                        (i_rst),
            .i_gb_mode                    (i_wgb_mode),
            .i_d                          ({
                                           dfi_data_gb[(SWIDTH*7)+j],
                                           dfi_data_gb[(SWIDTH*6)+j],
                                           dfi_data_gb[(SWIDTH*5)+j],
                                           dfi_data_gb[(SWIDTH*4)+j],
                                           dfi_data_gb[(SWIDTH*3)+j],
                                           dfi_data_gb[(SWIDTH*2)+j],
                                           dfi_data_gb[(SWIDTH*1)+j],
                                           dfi_data_gb[(SWIDTH*0)+j]
                                          }),
            .i_num_pulses                 (i_phase_ext),
            .o_d                          ({
                                           dfi_data_pext[(SWIDTH*7)+j],
                                           dfi_data_pext[(SWIDTH*6)+j],
                                           dfi_data_pext[(SWIDTH*5)+j],
                                           dfi_data_pext[(SWIDTH*4)+j],
                                           dfi_data_pext[(SWIDTH*3)+j],
                                           dfi_data_pext[(SWIDTH*2)+j],
                                           dfi_data_pext[(SWIDTH*1)+j],
                                           dfi_data_pext[(SWIDTH*0)+j]
                                          })
         );
         end else begin: NO_PEXT
            assign dfi_data_pext[(SWIDTH*7)+j] = dfi_data_gb[(SWIDTH*7)+j] ;
            assign dfi_data_pext[(SWIDTH*6)+j] = dfi_data_gb[(SWIDTH*6)+j] ;
            assign dfi_data_pext[(SWIDTH*5)+j] = dfi_data_gb[(SWIDTH*5)+j] ;
            assign dfi_data_pext[(SWIDTH*4)+j] = dfi_data_gb[(SWIDTH*4)+j] ;
            assign dfi_data_pext[(SWIDTH*3)+j] = dfi_data_gb[(SWIDTH*3)+j] ;
            assign dfi_data_pext[(SWIDTH*2)+j] = dfi_data_gb[(SWIDTH*2)+j] ;
            assign dfi_data_pext[(SWIDTH*1)+j] = dfi_data_gb[(SWIDTH*1)+j] ;
            assign dfi_data_pext[(SWIDTH*0)+j] = dfi_data_gb[(SWIDTH*0)+j] ;
         end

         ddr_fc_dly #(
            .DWIDTH (8),
            .MAXDLY (MAXDLY),
            .FWIDTH (FWIDTH)
         ) u_sdr_fc_dly (
            .i_clk   (i_clk_0),
            .i_delay (i_post_gb_dly),
            .i_d     ({
                      dfi_data_pext[(SWIDTH*7)+j],
                      dfi_data_pext[(SWIDTH*6)+j],
                      dfi_data_pext[(SWIDTH*5)+j],
                      dfi_data_pext[(SWIDTH*4)+j],
                      dfi_data_pext[(SWIDTH*3)+j],
                      dfi_data_pext[(SWIDTH*2)+j],
                      dfi_data_pext[(SWIDTH*1)+j],
                      dfi_data_pext[(SWIDTH*0)+j]
                     }),
            .o_q     ({
                       o_dfi_data_p7 [j],
                       o_dfi_data_p6 [j],
                       o_dfi_data_p5 [j],
                       o_dfi_data_p4 [j],
                       o_dfi_data_p3 [j],
                       o_dfi_data_p2 [j],
                       o_dfi_data_p1 [j],
                       o_dfi_data_p0 [j]
                     })
         );

      end
   endgenerate

endmodule

module ddr_dfi_buf #(
   parameter       NUM_WPH          = 8, // Number of Phases
   parameter       NUM_RPH          = 8, // Number of Phases
   parameter       NUM_APH          = 8, // Number of Phases
   parameter       NUM_DQ           = 4,          // Number of DQs
   parameter       AHB_DWIDTH       = 32,                       // AHB data width
   parameter       IG_DEPTH         = 64,                       // Ingress FIFO depth
   parameter       EG_DEPTH         = 64,                       // Egress FIFO depth
   parameter       IG_AWIDTH        = $clog2(IG_DEPTH),
   parameter       TSWIDTH          = 16,                       // TS Width
   parameter       SWIDTH           = 8,                        // DQ Slice Width
   parameter       AWIDTH           = 7,                        // CA Slice Width
   parameter       DWIDTH           = SWIDTH * 2,               // Data Width R+F
   parameter       BWIDTH           = SWIDTH / 8,               // BYTE Width
   parameter       MWIDTH           = BWIDTH * 2,               // Mask width
   parameter       TWIDTH           = BWIDTH * 2,               // WCK Toggle width
   parameter [0:0] RAM_MODEL        = 1'b0                      // Enable RAM model
) (

   input  logic                     i_scan_mode,
   input  logic                     i_scan_rst_ctrl,
   input  logic                     i_scan_cgc_ctrl,

   input  logic                     i_clk,
   input  logic                     i_rst,

   input  logic                     i_buf_mode,
   input  logic                     i_buf_clk_en,
   input  logic                     i_intf_pipe_en,
   input  logic                     i_ts_enable,
   input  logic                     i_ts_reset,
   input  logic                     i_ts_brkpt_en,
   input  logic [TSWIDTH-1:0]       i_ts_brkpt_val,

   input  logic                     i_ig_loop_mode,
   input  logic [3:0]               i_ig_num_loops,
   input  logic                     i_ig_load_ptr,
   input  logic [IG_AWIDTH-1:0]     i_ig_stop_ptr,
   input  logic [IG_AWIDTH-1:0]     i_ig_start_ptr,
   input  logic                     i_ig_wdata_clr,
   input  logic                     i_ig_wdata_hold,
   input  logic                     i_ig_wdata_en,
   input  logic                     i_ig_wdata_upd,
   input  logic [AHB_DWIDTH-1:0]    i_ig_wdata,
   output logic                     o_ig_empty,
   output logic                     o_ig_write_done,
   output logic                     o_ig_full,
   output logic                     o_ig_overflow,

   input  logic                     i_eg_rdata_clr,
   input  logic                     i_eg_rdata_en,
   input  logic                     i_eg_rdata_upd,
   output logic [AHB_DWIDTH-1:0]    o_eg_rdata,
   output logic                     o_eg_empty,
   output logic                     o_eg_read_done,
   output logic                     o_eg_full,
   output logic                     o_eg_overflow,

   // Write Command Address Data
   input  logic [AWIDTH-1:0]        i_dfi_address_p0,
   input  logic [AWIDTH-1:0]        i_dfi_address_p1,
   input  logic [AWIDTH-1:0]        i_dfi_address_p2,
   input  logic [AWIDTH-1:0]        i_dfi_address_p3,
   input  logic [AWIDTH-1:0]        i_dfi_address_p4,
   input  logic [AWIDTH-1:0]        i_dfi_address_p5,
   input  logic [AWIDTH-1:0]        i_dfi_address_p6,
   input  logic [AWIDTH-1:0]        i_dfi_address_p7,
   input  logic [1:0]               i_dfi_cke_p0,
   input  logic [1:0]               i_dfi_cke_p1,
   input  logic [1:0]               i_dfi_cke_p2,
   input  logic [1:0]               i_dfi_cke_p3,
   input  logic [1:0]               i_dfi_cke_p4,
   input  logic [1:0]               i_dfi_cke_p5,
   input  logic [1:0]               i_dfi_cke_p6,
   input  logic [1:0]               i_dfi_cke_p7,
   input  logic [1:0]               i_dfi_cs_p0,
   input  logic [1:0]               i_dfi_cs_p1,
   input  logic [1:0]               i_dfi_cs_p2,
   input  logic [1:0]               i_dfi_cs_p3,
   input  logic [1:0]               i_dfi_cs_p4,
   input  logic [1:0]               i_dfi_cs_p5,
   input  logic [1:0]               i_dfi_cs_p6,
   input  logic [1:0]               i_dfi_cs_p7,
   input  logic                     i_dfi_dcd_p0,
   input  logic                     i_dfi_dcd_p1,
   input  logic                     i_dfi_dcd_p2,
   input  logic                     i_dfi_dcd_p3,
   input  logic                     i_dfi_dcd_p4,
   input  logic                     i_dfi_dcd_p5,
   input  logic                     i_dfi_dcd_p6,
   input  logic                     i_dfi_dcd_p7,

   output logic [AWIDTH-1:0]        o_ch0_dfi_address_p0,
   output logic [AWIDTH-1:0]        o_ch0_dfi_address_p1,
   output logic [AWIDTH-1:0]        o_ch0_dfi_address_p2,
   output logic [AWIDTH-1:0]        o_ch0_dfi_address_p3,
   output logic [AWIDTH-1:0]        o_ch0_dfi_address_p4,
   output logic [AWIDTH-1:0]        o_ch0_dfi_address_p5,
   output logic [AWIDTH-1:0]        o_ch0_dfi_address_p6,
   output logic [AWIDTH-1:0]        o_ch0_dfi_address_p7,
   output logic [1:0]               o_ch0_dfi_cke_p0,
   output logic [1:0]               o_ch0_dfi_cke_p1,
   output logic [1:0]               o_ch0_dfi_cke_p2,
   output logic [1:0]               o_ch0_dfi_cke_p3,
   output logic [1:0]               o_ch0_dfi_cke_p4,
   output logic [1:0]               o_ch0_dfi_cke_p5,
   output logic [1:0]               o_ch0_dfi_cke_p6,
   output logic [1:0]               o_ch0_dfi_cke_p7,
   output logic [1:0]               o_ch0_dfi_cs_p0,
   output logic [1:0]               o_ch0_dfi_cs_p1,
   output logic [1:0]               o_ch0_dfi_cs_p2,
   output logic [1:0]               o_ch0_dfi_cs_p3,
   output logic [1:0]               o_ch0_dfi_cs_p4,
   output logic [1:0]               o_ch0_dfi_cs_p5,
   output logic [1:0]               o_ch0_dfi_cs_p6,
   output logic [1:0]               o_ch0_dfi_cs_p7,
   output logic                     o_ch0_dfi_dcd_p0,
   output logic                     o_ch0_dfi_dcd_p1,
   output logic                     o_ch0_dfi_dcd_p2,
   output logic                     o_ch0_dfi_dcd_p3,
   output logic                     o_ch0_dfi_dcd_p4,
   output logic                     o_ch0_dfi_dcd_p5,
   output logic                     o_ch0_dfi_dcd_p6,
   output logic                     o_ch0_dfi_dcd_p7,
   output logic [AWIDTH-1:0]        o_ch1_dfi_address_p0,
   output logic [AWIDTH-1:0]        o_ch1_dfi_address_p1,
   output logic [AWIDTH-1:0]        o_ch1_dfi_address_p2,
   output logic [AWIDTH-1:0]        o_ch1_dfi_address_p3,
   output logic [AWIDTH-1:0]        o_ch1_dfi_address_p4,
   output logic [AWIDTH-1:0]        o_ch1_dfi_address_p5,
   output logic [AWIDTH-1:0]        o_ch1_dfi_address_p6,
   output logic [AWIDTH-1:0]        o_ch1_dfi_address_p7,
   output logic [1:0]               o_ch1_dfi_cke_p0,
   output logic [1:0]               o_ch1_dfi_cke_p1,
   output logic [1:0]               o_ch1_dfi_cke_p2,
   output logic [1:0]               o_ch1_dfi_cke_p3,
   output logic [1:0]               o_ch1_dfi_cke_p4,
   output logic [1:0]               o_ch1_dfi_cke_p5,
   output logic [1:0]               o_ch1_dfi_cke_p6,
   output logic [1:0]               o_ch1_dfi_cke_p7,
   output logic [1:0]               o_ch1_dfi_cs_p0,
   output logic [1:0]               o_ch1_dfi_cs_p1,
   output logic [1:0]               o_ch1_dfi_cs_p2,
   output logic [1:0]               o_ch1_dfi_cs_p3,
   output logic [1:0]               o_ch1_dfi_cs_p4,
   output logic [1:0]               o_ch1_dfi_cs_p5,
   output logic [1:0]               o_ch1_dfi_cs_p6,
   output logic [1:0]               o_ch1_dfi_cs_p7,
   output logic                     o_ch1_dfi_dcd_p0,
   output logic                     o_ch1_dfi_dcd_p1,
   output logic                     o_ch1_dfi_dcd_p2,
   output logic                     o_ch1_dfi_dcd_p3,
   output logic                     o_ch1_dfi_dcd_p4,
   output logic                     o_ch1_dfi_dcd_p5,
   output logic                     o_ch1_dfi_dcd_p6,
   output logic                     o_ch1_dfi_dcd_p7,

   // Read Command Address Data
   input  logic [AWIDTH-1:0]        i_dfi_address_w0,
   input  logic [AWIDTH-1:0]        i_dfi_address_w1,
   input  logic [AWIDTH-1:0]        i_dfi_address_w2,
   input  logic [AWIDTH-1:0]        i_dfi_address_w3,
   input  logic [AWIDTH-1:0]        i_dfi_address_w4,
   input  logic [AWIDTH-1:0]        i_dfi_address_w5,
   input  logic [AWIDTH-1:0]        i_dfi_address_w6,
   input  logic [AWIDTH-1:0]        i_dfi_address_w7,

   input  logic [1:0]               i_dfi_cke_w0,
   input  logic [1:0]               i_dfi_cke_w1,
   input  logic [1:0]               i_dfi_cke_w2,
   input  logic [1:0]               i_dfi_cke_w3,
   input  logic [1:0]               i_dfi_cke_w4,
   input  logic [1:0]               i_dfi_cke_w5,
   input  logic [1:0]               i_dfi_cke_w6,
   input  logic [1:0]               i_dfi_cke_w7,

   input  logic [1:0]               i_dfi_cs_w0,
   input  logic [1:0]               i_dfi_cs_w1,
   input  logic [1:0]               i_dfi_cs_w2,
   input  logic [1:0]               i_dfi_cs_w3,
   input  logic [1:0]               i_dfi_cs_w4,
   input  logic [1:0]               i_dfi_cs_w5,
   input  logic [1:0]               i_dfi_cs_w6,
   input  logic [1:0]               i_dfi_cs_w7,

   input  logic                     i_dfi_address_valid_w0,
   input  logic                     i_dfi_address_valid_w1,
   input  logic                     i_dfi_address_valid_w2,
   input  logic                     i_dfi_address_valid_w3,
   input  logic                     i_dfi_address_valid_w4,
   input  logic                     i_dfi_address_valid_w5,
   input  logic                     i_dfi_address_valid_w6,
   input  logic                     i_dfi_address_valid_w7,

   // Write Data
   input  logic [NUM_DQ*SWIDTH-1:0] i_dfi_wrdata_p0,
   input  logic [NUM_DQ*SWIDTH-1:0] i_dfi_wrdata_p1,
   input  logic [NUM_DQ*SWIDTH-1:0] i_dfi_wrdata_p2,
   input  logic [NUM_DQ*SWIDTH-1:0] i_dfi_wrdata_p3,
   input  logic [NUM_DQ*SWIDTH-1:0] i_dfi_wrdata_p4,
   input  logic [NUM_DQ*SWIDTH-1:0] i_dfi_wrdata_p5,
   input  logic [NUM_DQ*SWIDTH-1:0] i_dfi_wrdata_p6,
   input  logic [NUM_DQ*SWIDTH-1:0] i_dfi_wrdata_p7,
   input  logic                     i_dfi_parity_in_p0,
   input  logic                     i_dfi_parity_in_p1,
   input  logic                     i_dfi_parity_in_p2,
   input  logic                     i_dfi_parity_in_p3,
   input  logic                     i_dfi_parity_in_p4,
   input  logic                     i_dfi_parity_in_p5,
   input  logic                     i_dfi_parity_in_p6,
   input  logic                     i_dfi_parity_in_p7,
   input  logic [1:0]               i_dfi_wrdata_cs_p0,
   input  logic [1:0]               i_dfi_wrdata_cs_p1,
   input  logic [1:0]               i_dfi_wrdata_cs_p2,
   input  logic [1:0]               i_dfi_wrdata_cs_p3,
   input  logic [1:0]               i_dfi_wrdata_cs_p4,
   input  logic [1:0]               i_dfi_wrdata_cs_p5,
   input  logic [1:0]               i_dfi_wrdata_cs_p6,
   input  logic [1:0]               i_dfi_wrdata_cs_p7,
   input  logic [NUM_DQ*BWIDTH-1:0] i_dfi_wrdata_mask_p0,
   input  logic [NUM_DQ*BWIDTH-1:0] i_dfi_wrdata_mask_p1,
   input  logic [NUM_DQ*BWIDTH-1:0] i_dfi_wrdata_mask_p2,
   input  logic [NUM_DQ*BWIDTH-1:0] i_dfi_wrdata_mask_p3,
   input  logic [NUM_DQ*BWIDTH-1:0] i_dfi_wrdata_mask_p4,
   input  logic [NUM_DQ*BWIDTH-1:0] i_dfi_wrdata_mask_p5,
   input  logic [NUM_DQ*BWIDTH-1:0] i_dfi_wrdata_mask_p6,
   input  logic [NUM_DQ*BWIDTH-1:0] i_dfi_wrdata_mask_p7,

   output logic [SWIDTH-1:0]        o_ch0_dq0_dfi_wrdata_p0,
   output logic [SWIDTH-1:0]        o_ch0_dq0_dfi_wrdata_p1,
   output logic [SWIDTH-1:0]        o_ch0_dq0_dfi_wrdata_p2,
   output logic [SWIDTH-1:0]        o_ch0_dq0_dfi_wrdata_p3,
   output logic [SWIDTH-1:0]        o_ch0_dq0_dfi_wrdata_p4,
   output logic [SWIDTH-1:0]        o_ch0_dq0_dfi_wrdata_p5,
   output logic [SWIDTH-1:0]        o_ch0_dq0_dfi_wrdata_p6,
   output logic [SWIDTH-1:0]        o_ch0_dq0_dfi_wrdata_p7,
   output logic                     o_ch0_dq0_dfi_parity_in_p0,
   output logic                     o_ch0_dq0_dfi_parity_in_p1,
   output logic                     o_ch0_dq0_dfi_parity_in_p2,
   output logic                     o_ch0_dq0_dfi_parity_in_p3,
   output logic                     o_ch0_dq0_dfi_parity_in_p4,
   output logic                     o_ch0_dq0_dfi_parity_in_p5,
   output logic                     o_ch0_dq0_dfi_parity_in_p6,
   output logic                     o_ch0_dq0_dfi_parity_in_p7,
   output logic                     o_ch0_dq0_dfi_wrdata_cs_p0,
   output logic                     o_ch0_dq0_dfi_wrdata_cs_p1,
   output logic                     o_ch0_dq0_dfi_wrdata_cs_p2,
   output logic                     o_ch0_dq0_dfi_wrdata_cs_p3,
   output logic                     o_ch0_dq0_dfi_wrdata_cs_p4,
   output logic                     o_ch0_dq0_dfi_wrdata_cs_p5,
   output logic                     o_ch0_dq0_dfi_wrdata_cs_p6,
   output logic                     o_ch0_dq0_dfi_wrdata_cs_p7,
   output logic [BWIDTH-1:0]        o_ch0_dq0_dfi_wrdata_mask_p0,
   output logic [BWIDTH-1:0]        o_ch0_dq0_dfi_wrdata_mask_p1,
   output logic [BWIDTH-1:0]        o_ch0_dq0_dfi_wrdata_mask_p2,
   output logic [BWIDTH-1:0]        o_ch0_dq0_dfi_wrdata_mask_p3,
   output logic [BWIDTH-1:0]        o_ch0_dq0_dfi_wrdata_mask_p4,
   output logic [BWIDTH-1:0]        o_ch0_dq0_dfi_wrdata_mask_p5,
   output logic [BWIDTH-1:0]        o_ch0_dq0_dfi_wrdata_mask_p6,
   output logic [BWIDTH-1:0]        o_ch0_dq0_dfi_wrdata_mask_p7,
   output logic [SWIDTH-1:0]        o_ch0_dq1_dfi_wrdata_p0,
   output logic [SWIDTH-1:0]        o_ch0_dq1_dfi_wrdata_p1,
   output logic [SWIDTH-1:0]        o_ch0_dq1_dfi_wrdata_p2,
   output logic [SWIDTH-1:0]        o_ch0_dq1_dfi_wrdata_p3,
   output logic [SWIDTH-1:0]        o_ch0_dq1_dfi_wrdata_p4,
   output logic [SWIDTH-1:0]        o_ch0_dq1_dfi_wrdata_p5,
   output logic [SWIDTH-1:0]        o_ch0_dq1_dfi_wrdata_p6,
   output logic [SWIDTH-1:0]        o_ch0_dq1_dfi_wrdata_p7,
   output logic                     o_ch0_dq1_dfi_parity_in_p0,
   output logic                     o_ch0_dq1_dfi_parity_in_p1,
   output logic                     o_ch0_dq1_dfi_parity_in_p2,
   output logic                     o_ch0_dq1_dfi_parity_in_p3,
   output logic                     o_ch0_dq1_dfi_parity_in_p4,
   output logic                     o_ch0_dq1_dfi_parity_in_p5,
   output logic                     o_ch0_dq1_dfi_parity_in_p6,
   output logic                     o_ch0_dq1_dfi_parity_in_p7,
   output logic                     o_ch0_dq1_dfi_wrdata_cs_p0,
   output logic                     o_ch0_dq1_dfi_wrdata_cs_p1,
   output logic                     o_ch0_dq1_dfi_wrdata_cs_p2,
   output logic                     o_ch0_dq1_dfi_wrdata_cs_p3,
   output logic                     o_ch0_dq1_dfi_wrdata_cs_p4,
   output logic                     o_ch0_dq1_dfi_wrdata_cs_p5,
   output logic                     o_ch0_dq1_dfi_wrdata_cs_p6,
   output logic                     o_ch0_dq1_dfi_wrdata_cs_p7,
   output logic [BWIDTH-1:0]        o_ch0_dq1_dfi_wrdata_mask_p0,
   output logic [BWIDTH-1:0]        o_ch0_dq1_dfi_wrdata_mask_p1,
   output logic [BWIDTH-1:0]        o_ch0_dq1_dfi_wrdata_mask_p2,
   output logic [BWIDTH-1:0]        o_ch0_dq1_dfi_wrdata_mask_p3,
   output logic [BWIDTH-1:0]        o_ch0_dq1_dfi_wrdata_mask_p4,
   output logic [BWIDTH-1:0]        o_ch0_dq1_dfi_wrdata_mask_p5,
   output logic [BWIDTH-1:0]        o_ch0_dq1_dfi_wrdata_mask_p6,
   output logic [BWIDTH-1:0]        o_ch0_dq1_dfi_wrdata_mask_p7,
   output logic [SWIDTH-1:0]        o_ch1_dq0_dfi_wrdata_p0,
   output logic [SWIDTH-1:0]        o_ch1_dq0_dfi_wrdata_p1,
   output logic [SWIDTH-1:0]        o_ch1_dq0_dfi_wrdata_p2,
   output logic [SWIDTH-1:0]        o_ch1_dq0_dfi_wrdata_p3,
   output logic [SWIDTH-1:0]        o_ch1_dq0_dfi_wrdata_p4,
   output logic [SWIDTH-1:0]        o_ch1_dq0_dfi_wrdata_p5,
   output logic [SWIDTH-1:0]        o_ch1_dq0_dfi_wrdata_p6,
   output logic [SWIDTH-1:0]        o_ch1_dq0_dfi_wrdata_p7,
   output logic                     o_ch1_dq0_dfi_parity_in_p0,
   output logic                     o_ch1_dq0_dfi_parity_in_p1,
   output logic                     o_ch1_dq0_dfi_parity_in_p2,
   output logic                     o_ch1_dq0_dfi_parity_in_p3,
   output logic                     o_ch1_dq0_dfi_parity_in_p4,
   output logic                     o_ch1_dq0_dfi_parity_in_p5,
   output logic                     o_ch1_dq0_dfi_parity_in_p6,
   output logic                     o_ch1_dq0_dfi_parity_in_p7,
   output logic                     o_ch1_dq0_dfi_wrdata_cs_p0,
   output logic                     o_ch1_dq0_dfi_wrdata_cs_p1,
   output logic                     o_ch1_dq0_dfi_wrdata_cs_p2,
   output logic                     o_ch1_dq0_dfi_wrdata_cs_p3,
   output logic                     o_ch1_dq0_dfi_wrdata_cs_p4,
   output logic                     o_ch1_dq0_dfi_wrdata_cs_p5,
   output logic                     o_ch1_dq0_dfi_wrdata_cs_p6,
   output logic                     o_ch1_dq0_dfi_wrdata_cs_p7,
   output logic [BWIDTH-1:0]        o_ch1_dq0_dfi_wrdata_mask_p0,
   output logic [BWIDTH-1:0]        o_ch1_dq0_dfi_wrdata_mask_p1,
   output logic [BWIDTH-1:0]        o_ch1_dq0_dfi_wrdata_mask_p2,
   output logic [BWIDTH-1:0]        o_ch1_dq0_dfi_wrdata_mask_p3,
   output logic [BWIDTH-1:0]        o_ch1_dq0_dfi_wrdata_mask_p4,
   output logic [BWIDTH-1:0]        o_ch1_dq0_dfi_wrdata_mask_p5,
   output logic [BWIDTH-1:0]        o_ch1_dq0_dfi_wrdata_mask_p6,
   output logic [BWIDTH-1:0]        o_ch1_dq0_dfi_wrdata_mask_p7,
   output logic [SWIDTH-1:0]        o_ch1_dq1_dfi_wrdata_p0,
   output logic [SWIDTH-1:0]        o_ch1_dq1_dfi_wrdata_p1,
   output logic [SWIDTH-1:0]        o_ch1_dq1_dfi_wrdata_p2,
   output logic [SWIDTH-1:0]        o_ch1_dq1_dfi_wrdata_p3,
   output logic [SWIDTH-1:0]        o_ch1_dq1_dfi_wrdata_p4,
   output logic [SWIDTH-1:0]        o_ch1_dq1_dfi_wrdata_p5,
   output logic [SWIDTH-1:0]        o_ch1_dq1_dfi_wrdata_p6,
   output logic [SWIDTH-1:0]        o_ch1_dq1_dfi_wrdata_p7,
   output logic                     o_ch1_dq1_dfi_parity_in_p0,
   output logic                     o_ch1_dq1_dfi_parity_in_p1,
   output logic                     o_ch1_dq1_dfi_parity_in_p2,
   output logic                     o_ch1_dq1_dfi_parity_in_p3,
   output logic                     o_ch1_dq1_dfi_parity_in_p4,
   output logic                     o_ch1_dq1_dfi_parity_in_p5,
   output logic                     o_ch1_dq1_dfi_parity_in_p6,
   output logic                     o_ch1_dq1_dfi_parity_in_p7,
   output logic                     o_ch1_dq1_dfi_wrdata_cs_p0,
   output logic                     o_ch1_dq1_dfi_wrdata_cs_p1,
   output logic                     o_ch1_dq1_dfi_wrdata_cs_p2,
   output logic                     o_ch1_dq1_dfi_wrdata_cs_p3,
   output logic                     o_ch1_dq1_dfi_wrdata_cs_p4,
   output logic                     o_ch1_dq1_dfi_wrdata_cs_p5,
   output logic                     o_ch1_dq1_dfi_wrdata_cs_p6,
   output logic                     o_ch1_dq1_dfi_wrdata_cs_p7,
   output logic [BWIDTH-1:0]        o_ch1_dq1_dfi_wrdata_mask_p0,
   output logic [BWIDTH-1:0]        o_ch1_dq1_dfi_wrdata_mask_p1,
   output logic [BWIDTH-1:0]        o_ch1_dq1_dfi_wrdata_mask_p2,
   output logic [BWIDTH-1:0]        o_ch1_dq1_dfi_wrdata_mask_p3,
   output logic [BWIDTH-1:0]        o_ch1_dq1_dfi_wrdata_mask_p4,
   output logic [BWIDTH-1:0]        o_ch1_dq1_dfi_wrdata_mask_p5,
   output logic [BWIDTH-1:0]        o_ch1_dq1_dfi_wrdata_mask_p6,
   output logic [BWIDTH-1:0]        o_ch1_dq1_dfi_wrdata_mask_p7,

   // Write Enable/WCK
   input  logic                     i_dfi_wrdata_en_p0,
   input  logic                     i_dfi_wrdata_en_p1,
   input  logic                     i_dfi_wrdata_en_p2,
   input  logic                     i_dfi_wrdata_en_p3,
   input  logic                     i_dfi_wrdata_en_p4,
   input  logic                     i_dfi_wrdata_en_p5,
   input  logic                     i_dfi_wrdata_en_p6,
   input  logic                     i_dfi_wrdata_en_p7,
   input  logic [1:0]               i_dfi_wck_cs_p0,
   input  logic [1:0]               i_dfi_wck_cs_p1,
   input  logic [1:0]               i_dfi_wck_cs_p2,
   input  logic [1:0]               i_dfi_wck_cs_p3,
   input  logic [1:0]               i_dfi_wck_cs_p4,
   input  logic [1:0]               i_dfi_wck_cs_p5,
   input  logic [1:0]               i_dfi_wck_cs_p6,
   input  logic [1:0]               i_dfi_wck_cs_p7,
   input  logic                     i_dfi_wck_en_p0,
   input  logic                     i_dfi_wck_en_p1,
   input  logic                     i_dfi_wck_en_p2,
   input  logic                     i_dfi_wck_en_p3,
   input  logic                     i_dfi_wck_en_p4,
   input  logic                     i_dfi_wck_en_p5,
   input  logic                     i_dfi_wck_en_p6,
   input  logic                     i_dfi_wck_en_p7,
   input  logic [TWIDTH-1:0]        i_dfi_wck_toggle_p0,
   input  logic [TWIDTH-1:0]        i_dfi_wck_toggle_p1,
   input  logic [TWIDTH-1:0]        i_dfi_wck_toggle_p2,
   input  logic [TWIDTH-1:0]        i_dfi_wck_toggle_p3,
   input  logic [TWIDTH-1:0]        i_dfi_wck_toggle_p4,
   input  logic [TWIDTH-1:0]        i_dfi_wck_toggle_p5,
   input  logic [TWIDTH-1:0]        i_dfi_wck_toggle_p6,
   input  logic [TWIDTH-1:0]        i_dfi_wck_toggle_p7,
   output logic                     o_ch0_dq0_dfi_wrdata_en_p0,
   output logic                     o_ch0_dq0_dfi_wrdata_en_p1,
   output logic                     o_ch0_dq0_dfi_wrdata_en_p2,
   output logic                     o_ch0_dq0_dfi_wrdata_en_p3,
   output logic                     o_ch0_dq0_dfi_wrdata_en_p4,
   output logic                     o_ch0_dq0_dfi_wrdata_en_p5,
   output logic                     o_ch0_dq0_dfi_wrdata_en_p6,
   output logic                     o_ch0_dq0_dfi_wrdata_en_p7,
   output  logic                    o_ch0_dq0_dfi_wck_cs_p0,
   output  logic                    o_ch0_dq0_dfi_wck_cs_p1,
   output  logic                    o_ch0_dq0_dfi_wck_cs_p2,
   output  logic                    o_ch0_dq0_dfi_wck_cs_p3,
   output  logic                    o_ch0_dq0_dfi_wck_cs_p4,
   output  logic                    o_ch0_dq0_dfi_wck_cs_p5,
   output  logic                    o_ch0_dq0_dfi_wck_cs_p6,
   output  logic                    o_ch0_dq0_dfi_wck_cs_p7,
   output logic                     o_ch0_dq0_dfi_wck_en_p0,
   output logic                     o_ch0_dq0_dfi_wck_en_p1,
   output logic                     o_ch0_dq0_dfi_wck_en_p2,
   output logic                     o_ch0_dq0_dfi_wck_en_p3,
   output logic                     o_ch0_dq0_dfi_wck_en_p4,
   output logic                     o_ch0_dq0_dfi_wck_en_p5,
   output logic                     o_ch0_dq0_dfi_wck_en_p6,
   output logic                     o_ch0_dq0_dfi_wck_en_p7,
   output logic [TWIDTH-1:0]        o_ch0_dq0_dfi_wck_toggle_p0,
   output logic [TWIDTH-1:0]        o_ch0_dq0_dfi_wck_toggle_p1,
   output logic [TWIDTH-1:0]        o_ch0_dq0_dfi_wck_toggle_p2,
   output logic [TWIDTH-1:0]        o_ch0_dq0_dfi_wck_toggle_p3,
   output logic [TWIDTH-1:0]        o_ch0_dq0_dfi_wck_toggle_p4,
   output logic [TWIDTH-1:0]        o_ch0_dq0_dfi_wck_toggle_p5,
   output logic [TWIDTH-1:0]        o_ch0_dq0_dfi_wck_toggle_p6,
   output logic [TWIDTH-1:0]        o_ch0_dq0_dfi_wck_toggle_p7,
   output logic                     o_ch0_dq1_dfi_wrdata_en_p0,
   output logic                     o_ch0_dq1_dfi_wrdata_en_p1,
   output logic                     o_ch0_dq1_dfi_wrdata_en_p2,
   output logic                     o_ch0_dq1_dfi_wrdata_en_p3,
   output logic                     o_ch0_dq1_dfi_wrdata_en_p4,
   output logic                     o_ch0_dq1_dfi_wrdata_en_p5,
   output logic                     o_ch0_dq1_dfi_wrdata_en_p6,
   output logic                     o_ch0_dq1_dfi_wrdata_en_p7,
   output  logic                    o_ch0_dq1_dfi_wck_cs_p0,
   output  logic                    o_ch0_dq1_dfi_wck_cs_p1,
   output  logic                    o_ch0_dq1_dfi_wck_cs_p2,
   output  logic                    o_ch0_dq1_dfi_wck_cs_p3,
   output  logic                    o_ch0_dq1_dfi_wck_cs_p4,
   output  logic                    o_ch0_dq1_dfi_wck_cs_p5,
   output  logic                    o_ch0_dq1_dfi_wck_cs_p6,
   output  logic                    o_ch0_dq1_dfi_wck_cs_p7,
   output logic                     o_ch0_dq1_dfi_wck_en_p0,
   output logic                     o_ch0_dq1_dfi_wck_en_p1,
   output logic                     o_ch0_dq1_dfi_wck_en_p2,
   output logic                     o_ch0_dq1_dfi_wck_en_p3,
   output logic                     o_ch0_dq1_dfi_wck_en_p4,
   output logic                     o_ch0_dq1_dfi_wck_en_p5,
   output logic                     o_ch0_dq1_dfi_wck_en_p6,
   output logic                     o_ch0_dq1_dfi_wck_en_p7,
   output logic [TWIDTH-1:0]        o_ch0_dq1_dfi_wck_toggle_p0,
   output logic [TWIDTH-1:0]        o_ch0_dq1_dfi_wck_toggle_p1,
   output logic [TWIDTH-1:0]        o_ch0_dq1_dfi_wck_toggle_p2,
   output logic [TWIDTH-1:0]        o_ch0_dq1_dfi_wck_toggle_p3,
   output logic [TWIDTH-1:0]        o_ch0_dq1_dfi_wck_toggle_p4,
   output logic [TWIDTH-1:0]        o_ch0_dq1_dfi_wck_toggle_p5,
   output logic [TWIDTH-1:0]        o_ch0_dq1_dfi_wck_toggle_p6,
   output logic [TWIDTH-1:0]        o_ch0_dq1_dfi_wck_toggle_p7,
   output logic                     o_ch1_dq0_dfi_wrdata_en_p0,
   output logic                     o_ch1_dq0_dfi_wrdata_en_p1,
   output logic                     o_ch1_dq0_dfi_wrdata_en_p2,
   output logic                     o_ch1_dq0_dfi_wrdata_en_p3,
   output logic                     o_ch1_dq0_dfi_wrdata_en_p4,
   output logic                     o_ch1_dq0_dfi_wrdata_en_p5,
   output logic                     o_ch1_dq0_dfi_wrdata_en_p6,
   output logic                     o_ch1_dq0_dfi_wrdata_en_p7,
   output  logic                    o_ch1_dq0_dfi_wck_cs_p0,
   output  logic                    o_ch1_dq0_dfi_wck_cs_p1,
   output  logic                    o_ch1_dq0_dfi_wck_cs_p2,
   output  logic                    o_ch1_dq0_dfi_wck_cs_p3,
   output  logic                    o_ch1_dq0_dfi_wck_cs_p4,
   output  logic                    o_ch1_dq0_dfi_wck_cs_p5,
   output  logic                    o_ch1_dq0_dfi_wck_cs_p6,
   output  logic                    o_ch1_dq0_dfi_wck_cs_p7,
   output logic                     o_ch1_dq0_dfi_wck_en_p0,
   output logic                     o_ch1_dq0_dfi_wck_en_p1,
   output logic                     o_ch1_dq0_dfi_wck_en_p2,
   output logic                     o_ch1_dq0_dfi_wck_en_p3,
   output logic                     o_ch1_dq0_dfi_wck_en_p4,
   output logic                     o_ch1_dq0_dfi_wck_en_p5,
   output logic                     o_ch1_dq0_dfi_wck_en_p6,
   output logic                     o_ch1_dq0_dfi_wck_en_p7,
   output logic [TWIDTH-1:0]        o_ch1_dq0_dfi_wck_toggle_p0,
   output logic [TWIDTH-1:0]        o_ch1_dq0_dfi_wck_toggle_p1,
   output logic [TWIDTH-1:0]        o_ch1_dq0_dfi_wck_toggle_p2,
   output logic [TWIDTH-1:0]        o_ch1_dq0_dfi_wck_toggle_p3,
   output logic [TWIDTH-1:0]        o_ch1_dq0_dfi_wck_toggle_p4,
   output logic [TWIDTH-1:0]        o_ch1_dq0_dfi_wck_toggle_p5,
   output logic [TWIDTH-1:0]        o_ch1_dq0_dfi_wck_toggle_p6,
   output logic [TWIDTH-1:0]        o_ch1_dq0_dfi_wck_toggle_p7,
   output logic                     o_ch1_dq1_dfi_wrdata_en_p0,
   output logic                     o_ch1_dq1_dfi_wrdata_en_p1,
   output logic                     o_ch1_dq1_dfi_wrdata_en_p2,
   output logic                     o_ch1_dq1_dfi_wrdata_en_p3,
   output logic                     o_ch1_dq1_dfi_wrdata_en_p4,
   output logic                     o_ch1_dq1_dfi_wrdata_en_p5,
   output logic                     o_ch1_dq1_dfi_wrdata_en_p6,
   output logic                     o_ch1_dq1_dfi_wrdata_en_p7,
   output  logic                    o_ch1_dq1_dfi_wck_cs_p0,
   output  logic                    o_ch1_dq1_dfi_wck_cs_p1,
   output  logic                    o_ch1_dq1_dfi_wck_cs_p2,
   output  logic                    o_ch1_dq1_dfi_wck_cs_p3,
   output  logic                    o_ch1_dq1_dfi_wck_cs_p4,
   output  logic                    o_ch1_dq1_dfi_wck_cs_p5,
   output  logic                    o_ch1_dq1_dfi_wck_cs_p6,
   output  logic                    o_ch1_dq1_dfi_wck_cs_p7,
   output logic                     o_ch1_dq1_dfi_wck_en_p0,
   output logic                     o_ch1_dq1_dfi_wck_en_p1,
   output logic                     o_ch1_dq1_dfi_wck_en_p2,
   output logic                     o_ch1_dq1_dfi_wck_en_p3,
   output logic                     o_ch1_dq1_dfi_wck_en_p4,
   output logic                     o_ch1_dq1_dfi_wck_en_p5,
   output logic                     o_ch1_dq1_dfi_wck_en_p6,
   output logic                     o_ch1_dq1_dfi_wck_en_p7,
   output logic [TWIDTH-1:0]        o_ch1_dq1_dfi_wck_toggle_p0,
   output logic [TWIDTH-1:0]        o_ch1_dq1_dfi_wck_toggle_p1,
   output logic [TWIDTH-1:0]        o_ch1_dq1_dfi_wck_toggle_p2,
   output logic [TWIDTH-1:0]        o_ch1_dq1_dfi_wck_toggle_p3,
   output logic [TWIDTH-1:0]        o_ch1_dq1_dfi_wck_toggle_p4,
   output logic [TWIDTH-1:0]        o_ch1_dq1_dfi_wck_toggle_p5,
   output logic [TWIDTH-1:0]        o_ch1_dq1_dfi_wck_toggle_p6,
   output logic [TWIDTH-1:0]        o_ch1_dq1_dfi_wck_toggle_p7,

   // Read Data
   input  logic [1:0]               i_dfi_rddata_cs_p0,
   input  logic [1:0]               i_dfi_rddata_cs_p1,
   input  logic [1:0]               i_dfi_rddata_cs_p2,
   input  logic [1:0]               i_dfi_rddata_cs_p3,
   input  logic [1:0]               i_dfi_rddata_cs_p4,
   input  logic [1:0]               i_dfi_rddata_cs_p5,
   input  logic [1:0]               i_dfi_rddata_cs_p6,
   input  logic [1:0]               i_dfi_rddata_cs_p7,
   input  logic                     i_dfi_rddata_en_p0,
   input  logic                     i_dfi_rddata_en_p1,
   input  logic                     i_dfi_rddata_en_p2,
   input  logic                     i_dfi_rddata_en_p3,
   input  logic                     i_dfi_rddata_en_p4,
   input  logic                     i_dfi_rddata_en_p5,
   input  logic                     i_dfi_rddata_en_p6,
   input  logic                     i_dfi_rddata_en_p7,
   output logic                     o_ch0_dq0_dfi_rddata_cs_p0,
   output logic                     o_ch0_dq0_dfi_rddata_cs_p1,
   output logic                     o_ch0_dq0_dfi_rddata_cs_p2,
   output logic                     o_ch0_dq0_dfi_rddata_cs_p3,
   output logic                     o_ch0_dq0_dfi_rddata_cs_p4,
   output logic                     o_ch0_dq0_dfi_rddata_cs_p5,
   output logic                     o_ch0_dq0_dfi_rddata_cs_p6,
   output logic                     o_ch0_dq0_dfi_rddata_cs_p7,
   output logic                     o_ch0_dq0_dfi_rddata_en_p0,
   output logic                     o_ch0_dq0_dfi_rddata_en_p1,
   output logic                     o_ch0_dq0_dfi_rddata_en_p2,
   output logic                     o_ch0_dq0_dfi_rddata_en_p3,
   output logic                     o_ch0_dq0_dfi_rddata_en_p4,
   output logic                     o_ch0_dq0_dfi_rddata_en_p5,
   output logic                     o_ch0_dq0_dfi_rddata_en_p6,
   output logic                     o_ch0_dq0_dfi_rddata_en_p7,
   output logic                     o_ch0_dq1_dfi_rddata_cs_p0,
   output logic                     o_ch0_dq1_dfi_rddata_cs_p1,
   output logic                     o_ch0_dq1_dfi_rddata_cs_p2,
   output logic                     o_ch0_dq1_dfi_rddata_cs_p3,
   output logic                     o_ch0_dq1_dfi_rddata_cs_p4,
   output logic                     o_ch0_dq1_dfi_rddata_cs_p5,
   output logic                     o_ch0_dq1_dfi_rddata_cs_p6,
   output logic                     o_ch0_dq1_dfi_rddata_cs_p7,
   output logic                     o_ch0_dq1_dfi_rddata_en_p0,
   output logic                     o_ch0_dq1_dfi_rddata_en_p1,
   output logic                     o_ch0_dq1_dfi_rddata_en_p2,
   output logic                     o_ch0_dq1_dfi_rddata_en_p3,
   output logic                     o_ch0_dq1_dfi_rddata_en_p4,
   output logic                     o_ch0_dq1_dfi_rddata_en_p5,
   output logic                     o_ch0_dq1_dfi_rddata_en_p6,
   output logic                     o_ch0_dq1_dfi_rddata_en_p7,
   output logic                     o_ch1_dq0_dfi_rddata_cs_p0,
   output logic                     o_ch1_dq0_dfi_rddata_cs_p1,
   output logic                     o_ch1_dq0_dfi_rddata_cs_p2,
   output logic                     o_ch1_dq0_dfi_rddata_cs_p3,
   output logic                     o_ch1_dq0_dfi_rddata_cs_p4,
   output logic                     o_ch1_dq0_dfi_rddata_cs_p5,
   output logic                     o_ch1_dq0_dfi_rddata_cs_p6,
   output logic                     o_ch1_dq0_dfi_rddata_cs_p7,
   output logic                     o_ch1_dq0_dfi_rddata_en_p0,
   output logic                     o_ch1_dq0_dfi_rddata_en_p1,
   output logic                     o_ch1_dq0_dfi_rddata_en_p2,
   output logic                     o_ch1_dq0_dfi_rddata_en_p3,
   output logic                     o_ch1_dq0_dfi_rddata_en_p4,
   output logic                     o_ch1_dq0_dfi_rddata_en_p5,
   output logic                     o_ch1_dq0_dfi_rddata_en_p6,
   output logic                     o_ch1_dq0_dfi_rddata_en_p7,
   output logic                     o_ch1_dq1_dfi_rddata_cs_p0,
   output logic                     o_ch1_dq1_dfi_rddata_cs_p1,
   output logic                     o_ch1_dq1_dfi_rddata_cs_p2,
   output logic                     o_ch1_dq1_dfi_rddata_cs_p3,
   output logic                     o_ch1_dq1_dfi_rddata_cs_p4,
   output logic                     o_ch1_dq1_dfi_rddata_cs_p5,
   output logic                     o_ch1_dq1_dfi_rddata_cs_p6,
   output logic                     o_ch1_dq1_dfi_rddata_cs_p7,
   output logic                     o_ch1_dq1_dfi_rddata_en_p0,
   output logic                     o_ch1_dq1_dfi_rddata_en_p1,
   output logic                     o_ch1_dq1_dfi_rddata_en_p2,
   output logic                     o_ch1_dq1_dfi_rddata_en_p3,
   output logic                     o_ch1_dq1_dfi_rddata_en_p4,
   output logic                     o_ch1_dq1_dfi_rddata_en_p5,
   output logic                     o_ch1_dq1_dfi_rddata_en_p6,
   output logic                     o_ch1_dq1_dfi_rddata_en_p7,

   input  logic [SWIDTH-1:0]        i_dq0_dfi_rddata_w0,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_rddata_w1,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_rddata_w2,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_rddata_w3,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_rddata_w4,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_rddata_w5,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_rddata_w6,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_rddata_w7,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_rddata_w0,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_rddata_w1,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_rddata_w2,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_rddata_w3,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_rddata_w4,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_rddata_w5,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_rddata_w6,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_rddata_w7,
   input  logic [SWIDTH-1:0]        i_dq2_dfi_rddata_w0,
   input  logic [SWIDTH-1:0]        i_dq2_dfi_rddata_w1,
   input  logic [SWIDTH-1:0]        i_dq2_dfi_rddata_w2,
   input  logic [SWIDTH-1:0]        i_dq2_dfi_rddata_w3,
   input  logic [SWIDTH-1:0]        i_dq2_dfi_rddata_w4,
   input  logic [SWIDTH-1:0]        i_dq2_dfi_rddata_w5,
   input  logic [SWIDTH-1:0]        i_dq2_dfi_rddata_w6,
   input  logic [SWIDTH-1:0]        i_dq2_dfi_rddata_w7,
   input  logic [SWIDTH-1:0]        i_dq3_dfi_rddata_w0,
   input  logic [SWIDTH-1:0]        i_dq3_dfi_rddata_w1,
   input  logic [SWIDTH-1:0]        i_dq3_dfi_rddata_w2,
   input  logic [SWIDTH-1:0]        i_dq3_dfi_rddata_w3,
   input  logic [SWIDTH-1:0]        i_dq3_dfi_rddata_w4,
   input  logic [SWIDTH-1:0]        i_dq3_dfi_rddata_w5,
   input  logic [SWIDTH-1:0]        i_dq3_dfi_rddata_w6,
   input  logic [SWIDTH-1:0]        i_dq3_dfi_rddata_w7,

   input  logic [MWIDTH-1:0]        i_dq0_dfi_rddata_dbi_w0,
   input  logic [MWIDTH-1:0]        i_dq0_dfi_rddata_dbi_w1,
   input  logic [MWIDTH-1:0]        i_dq0_dfi_rddata_dbi_w2,
   input  logic [MWIDTH-1:0]        i_dq0_dfi_rddata_dbi_w3,
   input  logic [MWIDTH-1:0]        i_dq0_dfi_rddata_dbi_w4,
   input  logic [MWIDTH-1:0]        i_dq0_dfi_rddata_dbi_w5,
   input  logic [MWIDTH-1:0]        i_dq0_dfi_rddata_dbi_w6,
   input  logic [MWIDTH-1:0]        i_dq0_dfi_rddata_dbi_w7,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_rddata_dbi_w0,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_rddata_dbi_w1,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_rddata_dbi_w2,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_rddata_dbi_w3,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_rddata_dbi_w4,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_rddata_dbi_w5,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_rddata_dbi_w6,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_rddata_dbi_w7,
   input  logic [MWIDTH-1:0]        i_dq2_dfi_rddata_dbi_w0,
   input  logic [MWIDTH-1:0]        i_dq2_dfi_rddata_dbi_w1,
   input  logic [MWIDTH-1:0]        i_dq2_dfi_rddata_dbi_w2,
   input  logic [MWIDTH-1:0]        i_dq2_dfi_rddata_dbi_w3,
   input  logic [MWIDTH-1:0]        i_dq2_dfi_rddata_dbi_w4,
   input  logic [MWIDTH-1:0]        i_dq2_dfi_rddata_dbi_w5,
   input  logic [MWIDTH-1:0]        i_dq2_dfi_rddata_dbi_w6,
   input  logic [MWIDTH-1:0]        i_dq2_dfi_rddata_dbi_w7,
   input  logic [MWIDTH-1:0]        i_dq3_dfi_rddata_dbi_w0,
   input  logic [MWIDTH-1:0]        i_dq3_dfi_rddata_dbi_w1,
   input  logic [MWIDTH-1:0]        i_dq3_dfi_rddata_dbi_w2,
   input  logic [MWIDTH-1:0]        i_dq3_dfi_rddata_dbi_w3,
   input  logic [MWIDTH-1:0]        i_dq3_dfi_rddata_dbi_w4,
   input  logic [MWIDTH-1:0]        i_dq3_dfi_rddata_dbi_w5,
   input  logic [MWIDTH-1:0]        i_dq3_dfi_rddata_dbi_w6,
   input  logic [MWIDTH-1:0]        i_dq3_dfi_rddata_dbi_w7,

   input  logic                     i_dq0_dfi_rddata_valid_w0,
   input  logic                     i_dq0_dfi_rddata_valid_w1,
   input  logic                     i_dq0_dfi_rddata_valid_w2,
   input  logic                     i_dq0_dfi_rddata_valid_w3,
   input  logic                     i_dq0_dfi_rddata_valid_w4,
   input  logic                     i_dq0_dfi_rddata_valid_w5,
   input  logic                     i_dq0_dfi_rddata_valid_w6,
   input  logic                     i_dq0_dfi_rddata_valid_w7,
   input  logic                     i_dq1_dfi_rddata_valid_w0,
   input  logic                     i_dq1_dfi_rddata_valid_w1,
   input  logic                     i_dq1_dfi_rddata_valid_w2,
   input  logic                     i_dq1_dfi_rddata_valid_w3,
   input  logic                     i_dq1_dfi_rddata_valid_w4,
   input  logic                     i_dq1_dfi_rddata_valid_w5,
   input  logic                     i_dq1_dfi_rddata_valid_w6,
   input  logic                     i_dq1_dfi_rddata_valid_w7,
   input  logic                     i_dq2_dfi_rddata_valid_w0,
   input  logic                     i_dq2_dfi_rddata_valid_w1,
   input  logic                     i_dq2_dfi_rddata_valid_w2,
   input  logic                     i_dq2_dfi_rddata_valid_w3,
   input  logic                     i_dq2_dfi_rddata_valid_w4,
   input  logic                     i_dq2_dfi_rddata_valid_w5,
   input  logic                     i_dq2_dfi_rddata_valid_w6,
   input  logic                     i_dq2_dfi_rddata_valid_w7,
   input  logic                     i_dq3_dfi_rddata_valid_w0,
   input  logic                     i_dq3_dfi_rddata_valid_w1,
   input  logic                     i_dq3_dfi_rddata_valid_w2,
   input  logic                     i_dq3_dfi_rddata_valid_w3,
   input  logic                     i_dq3_dfi_rddata_valid_w4,
   input  logic                     i_dq3_dfi_rddata_valid_w5,
   input  logic                     i_dq3_dfi_rddata_valid_w6,
   input  logic                     i_dq3_dfi_rddata_valid_w7,

   input  logic                     i_dfi_rdout_en,

   output logic [SWIDTH-1:0]       o_dq0_dfi_rddata_w0,
   output logic [SWIDTH-1:0]       o_dq0_dfi_rddata_w1,
   output logic [SWIDTH-1:0]       o_dq0_dfi_rddata_w2,
   output logic [SWIDTH-1:0]       o_dq0_dfi_rddata_w3,
   output logic [SWIDTH-1:0]       o_dq0_dfi_rddata_w4,
   output logic [SWIDTH-1:0]       o_dq0_dfi_rddata_w5,
   output logic [SWIDTH-1:0]       o_dq0_dfi_rddata_w6,
   output logic [SWIDTH-1:0]       o_dq0_dfi_rddata_w7,
   output logic [SWIDTH-1:0]       o_dq1_dfi_rddata_w0,
   output logic [SWIDTH-1:0]       o_dq1_dfi_rddata_w1,
   output logic [SWIDTH-1:0]       o_dq1_dfi_rddata_w2,
   output logic [SWIDTH-1:0]       o_dq1_dfi_rddata_w3,
   output logic [SWIDTH-1:0]       o_dq1_dfi_rddata_w4,
   output logic [SWIDTH-1:0]       o_dq1_dfi_rddata_w5,
   output logic [SWIDTH-1:0]       o_dq1_dfi_rddata_w6,
   output logic [SWIDTH-1:0]       o_dq1_dfi_rddata_w7,
   output logic [SWIDTH-1:0]       o_dq2_dfi_rddata_w0,
   output logic [SWIDTH-1:0]       o_dq2_dfi_rddata_w1,
   output logic [SWIDTH-1:0]       o_dq2_dfi_rddata_w2,
   output logic [SWIDTH-1:0]       o_dq2_dfi_rddata_w3,
   output logic [SWIDTH-1:0]       o_dq2_dfi_rddata_w4,
   output logic [SWIDTH-1:0]       o_dq2_dfi_rddata_w5,
   output logic [SWIDTH-1:0]       o_dq2_dfi_rddata_w6,
   output logic [SWIDTH-1:0]       o_dq2_dfi_rddata_w7,
   output logic [SWIDTH-1:0]       o_dq3_dfi_rddata_w0,
   output logic [SWIDTH-1:0]       o_dq3_dfi_rddata_w1,
   output logic [SWIDTH-1:0]       o_dq3_dfi_rddata_w2,
   output logic [SWIDTH-1:0]       o_dq3_dfi_rddata_w3,
   output logic [SWIDTH-1:0]       o_dq3_dfi_rddata_w4,
   output logic [SWIDTH-1:0]       o_dq3_dfi_rddata_w5,
   output logic [SWIDTH-1:0]       o_dq3_dfi_rddata_w6,
   output logic [SWIDTH-1:0]       o_dq3_dfi_rddata_w7,
   output logic [MWIDTH-1:0]       o_dq0_dfi_rddata_dbi_w0,
   output logic [MWIDTH-1:0]       o_dq0_dfi_rddata_dbi_w1,
   output logic [MWIDTH-1:0]       o_dq0_dfi_rddata_dbi_w2,
   output logic [MWIDTH-1:0]       o_dq0_dfi_rddata_dbi_w3,
   output logic [MWIDTH-1:0]       o_dq0_dfi_rddata_dbi_w4,
   output logic [MWIDTH-1:0]       o_dq0_dfi_rddata_dbi_w5,
   output logic [MWIDTH-1:0]       o_dq0_dfi_rddata_dbi_w6,
   output logic [MWIDTH-1:0]       o_dq0_dfi_rddata_dbi_w7,
   output logic [MWIDTH-1:0]       o_dq1_dfi_rddata_dbi_w0,
   output logic [MWIDTH-1:0]       o_dq1_dfi_rddata_dbi_w1,
   output logic [MWIDTH-1:0]       o_dq1_dfi_rddata_dbi_w2,
   output logic [MWIDTH-1:0]       o_dq1_dfi_rddata_dbi_w3,
   output logic [MWIDTH-1:0]       o_dq1_dfi_rddata_dbi_w4,
   output logic [MWIDTH-1:0]       o_dq1_dfi_rddata_dbi_w5,
   output logic [MWIDTH-1:0]       o_dq1_dfi_rddata_dbi_w6,
   output logic [MWIDTH-1:0]       o_dq1_dfi_rddata_dbi_w7,
   output logic [MWIDTH-1:0]       o_dq2_dfi_rddata_dbi_w0,
   output logic [MWIDTH-1:0]       o_dq2_dfi_rddata_dbi_w1,
   output logic [MWIDTH-1:0]       o_dq2_dfi_rddata_dbi_w2,
   output logic [MWIDTH-1:0]       o_dq2_dfi_rddata_dbi_w3,
   output logic [MWIDTH-1:0]       o_dq2_dfi_rddata_dbi_w4,
   output logic [MWIDTH-1:0]       o_dq2_dfi_rddata_dbi_w5,
   output logic [MWIDTH-1:0]       o_dq2_dfi_rddata_dbi_w6,
   output logic [MWIDTH-1:0]       o_dq2_dfi_rddata_dbi_w7,
   output logic [MWIDTH-1:0]       o_dq3_dfi_rddata_dbi_w0,
   output logic [MWIDTH-1:0]       o_dq3_dfi_rddata_dbi_w1,
   output logic [MWIDTH-1:0]       o_dq3_dfi_rddata_dbi_w2,
   output logic [MWIDTH-1:0]       o_dq3_dfi_rddata_dbi_w3,
   output logic [MWIDTH-1:0]       o_dq3_dfi_rddata_dbi_w4,
   output logic [MWIDTH-1:0]       o_dq3_dfi_rddata_dbi_w5,
   output logic [MWIDTH-1:0]       o_dq3_dfi_rddata_dbi_w6,
   output logic [MWIDTH-1:0]       o_dq3_dfi_rddata_dbi_w7,
   output logic                    o_dfi_rddata_valid_w0,
   output logic                    o_dfi_rddata_valid_w1,
   output logic                    o_dfi_rddata_valid_w2,
   output logic                    o_dfi_rddata_valid_w3,
   output logic                    o_dfi_rddata_valid_w4,
   output logic                    o_dfi_rddata_valid_w5,
   output logic                    o_dfi_rddata_valid_w6,
   output logic                    o_dfi_rddata_valid_w7,
   output logic [31:0]              o_debug
);

   // ------------------------------------------------------------------------
   // Local Clock Gating
   // ------------------------------------------------------------------------
   logic clk_g, buf_mode_sync, buf_clk_en_sync, cgc_en;

   ddr_demet_r u_demet_6     (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_buf_mode), .o_q(buf_mode_sync));
   ddr_demet_r u_demet_9     (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_buf_clk_en), .o_q(buf_clk_en_sync));

   assign cgc_en = buf_mode_sync | buf_clk_en_sync ;

   ddr_cgc_rl u_cgc_dfi_clk  (.i_clk(i_clk), .i_clk_en(cgc_en), .i_cgc_en(i_scan_cgc_ctrl), .o_clk(clk_g));

   // ------------------------------------------------------------------------
   // Timestamp Counter
   // ------------------------------------------------------------------------

   logic [TSWIDTH-1:0] timestamp_q;
   logic ts_enable_sync;
   logic ts_reset_sync;
   logic ts_brkpt_en_sync;
   logic ts_brkpt ;

   // Synchronize CSR controls
   ddr_demet_r u_demet_0 (.i_clk(clk_g), .i_rst(i_rst), .i_d(i_ts_enable),        .o_q(ts_enable_sync));
   ddr_demet_r u_demet_1 (.i_clk(clk_g), .i_rst(i_rst), .i_d(i_ts_reset ),        .o_q(ts_reset_sync ));
   ddr_demet_r u_demet_7 (.i_clk(clk_g), .i_rst(i_rst), .i_d(i_ts_brkpt_en),      .o_q(ts_brkpt_en_sync ));

   assign ts_brkpt = ts_brkpt_en_sync && (timestamp_q == i_ts_brkpt_val) ;

   // Timestamp counter
   always_ff @ (posedge clk_g, posedge i_rst) begin
      if (i_rst)
         timestamp_q <= '0;
      else if (ts_reset_sync)
         timestamp_q <= '0;
      else if (ts_enable_sync)
         timestamp_q <=  ts_brkpt ? timestamp_q : timestamp_q + 'b1;
   end

   // ------------------------------------------------------------------------
   // Buffer Ingress - To DDR Datapath
   // ------------------------------------------------------------------------

   localparam IG_WIDTH = TSWIDTH
                         + (NUM_WPH*(10+TWIDTH+((MWIDTH+SWIDTH)*NUM_DQ)))
                         + (NUM_APH*(2+2+1+AWIDTH));

   logic [TSWIDTH-1:0] ig_timestamp, timestamp_early;
   logic ig_read, ig_write, ig_empty_n, ig_empty_n_q, ig_write_toggle_q ;
   logic [IG_WIDTH-1:0] ig_wdata, ig_rdata, ig_rdata_q, ig_mask_n, ig_mask_n_q;
   logic ig_wdata_en_sync, ig_wdata_en_q;
   logic ig_wdata_upd_sync, ig_wdata_upd_q;
   logic ig_load_ptr_sync ;
   logic wdata_loader_en, wdata_loader_upd;
   logic [IG_WIDTH-1:0] wdata_loader_q;
   logic [3:0] ig_loop_cnt_q ;
   logic [3:0] ig_loop_cnt_d ;

   logic [SWIDTH-1:0] dq0_dfi_wrdata_p0;
   logic [BWIDTH-1:0] dq0_dfi_wrdata_mask_p0;
   logic [SWIDTH-1:0] dq1_dfi_wrdata_p0;
   logic [BWIDTH-1:0] dq1_dfi_wrdata_mask_p0;
   logic [SWIDTH-1:0] dq2_dfi_wrdata_p0;
   logic [BWIDTH-1:0] dq2_dfi_wrdata_mask_p0;
   logic [SWIDTH-1:0] dq3_dfi_wrdata_p0;
   logic [BWIDTH-1:0] dq3_dfi_wrdata_mask_p0;
   logic              dfi_parity_in_p0;
   logic [1:0]        dfi_wrdata_cs_p0;
   logic              dfi_wrdata_en_p0;
   logic [1:0]        dfi_wck_cs_p0;
   logic              dfi_wck_en_p0;
   logic [TWIDTH-1:0] dfi_wck_toggle_p0;
   logic [1:0]        dfi_rddata_cs_p0;
   logic              dfi_rddata_en_p0;
   logic [SWIDTH-1:0] dq0_dfi_wrdata_p1;
   logic [BWIDTH-1:0] dq0_dfi_wrdata_mask_p1;
   logic [SWIDTH-1:0] dq1_dfi_wrdata_p1;
   logic [BWIDTH-1:0] dq1_dfi_wrdata_mask_p1;
   logic [SWIDTH-1:0] dq2_dfi_wrdata_p1;
   logic [BWIDTH-1:0] dq2_dfi_wrdata_mask_p1;
   logic [SWIDTH-1:0] dq3_dfi_wrdata_p1;
   logic [BWIDTH-1:0] dq3_dfi_wrdata_mask_p1;
   logic              dfi_parity_in_p1;
   logic [1:0]        dfi_wrdata_cs_p1;
   logic              dfi_wrdata_en_p1;
   logic [1:0]        dfi_wck_cs_p1;
   logic              dfi_wck_en_p1;
   logic [TWIDTH-1:0] dfi_wck_toggle_p1;
   logic [1:0]        dfi_rddata_cs_p1;
   logic              dfi_rddata_en_p1;
   logic [SWIDTH-1:0] dq0_dfi_wrdata_p2;
   logic [BWIDTH-1:0] dq0_dfi_wrdata_mask_p2;
   logic [SWIDTH-1:0] dq1_dfi_wrdata_p2;
   logic [BWIDTH-1:0] dq1_dfi_wrdata_mask_p2;
   logic [SWIDTH-1:0] dq2_dfi_wrdata_p2;
   logic [BWIDTH-1:0] dq2_dfi_wrdata_mask_p2;
   logic [SWIDTH-1:0] dq3_dfi_wrdata_p2;
   logic [BWIDTH-1:0] dq3_dfi_wrdata_mask_p2;
   logic              dfi_parity_in_p2;
   logic [1:0]        dfi_wrdata_cs_p2;
   logic              dfi_wrdata_en_p2;
   logic [1:0]        dfi_wck_cs_p2;
   logic              dfi_wck_en_p2;
   logic [TWIDTH-1:0] dfi_wck_toggle_p2;
   logic [1:0]        dfi_rddata_cs_p2;
   logic              dfi_rddata_en_p2;
   logic [SWIDTH-1:0] dq0_dfi_wrdata_p3;
   logic [BWIDTH-1:0] dq0_dfi_wrdata_mask_p3;
   logic [SWIDTH-1:0] dq1_dfi_wrdata_p3;
   logic [BWIDTH-1:0] dq1_dfi_wrdata_mask_p3;
   logic [SWIDTH-1:0] dq2_dfi_wrdata_p3;
   logic [BWIDTH-1:0] dq2_dfi_wrdata_mask_p3;
   logic [SWIDTH-1:0] dq3_dfi_wrdata_p3;
   logic [BWIDTH-1:0] dq3_dfi_wrdata_mask_p3;
   logic              dfi_parity_in_p3;
   logic [1:0]        dfi_wrdata_cs_p3;
   logic              dfi_wrdata_en_p3;
   logic [1:0]        dfi_wck_cs_p3;
   logic              dfi_wck_en_p3;
   logic [TWIDTH-1:0] dfi_wck_toggle_p3;
   logic [1:0]        dfi_rddata_cs_p3;
   logic              dfi_rddata_en_p3;
   logic [SWIDTH-1:0] dq0_dfi_wrdata_p4;
   logic [BWIDTH-1:0] dq0_dfi_wrdata_mask_p4;
   logic [SWIDTH-1:0] dq1_dfi_wrdata_p4;
   logic [BWIDTH-1:0] dq1_dfi_wrdata_mask_p4;
   logic [SWIDTH-1:0] dq2_dfi_wrdata_p4;
   logic [BWIDTH-1:0] dq2_dfi_wrdata_mask_p4;
   logic [SWIDTH-1:0] dq3_dfi_wrdata_p4;
   logic [BWIDTH-1:0] dq3_dfi_wrdata_mask_p4;
   logic              dfi_parity_in_p4;
   logic [1:0]        dfi_wrdata_cs_p4;
   logic              dfi_wrdata_en_p4;
   logic [1:0]        dfi_wck_cs_p4;
   logic              dfi_wck_en_p4;
   logic [TWIDTH-1:0] dfi_wck_toggle_p4;
   logic [1:0]        dfi_rddata_cs_p4;
   logic              dfi_rddata_en_p4;
   logic [SWIDTH-1:0] dq0_dfi_wrdata_p5;
   logic [BWIDTH-1:0] dq0_dfi_wrdata_mask_p5;
   logic [SWIDTH-1:0] dq1_dfi_wrdata_p5;
   logic [BWIDTH-1:0] dq1_dfi_wrdata_mask_p5;
   logic [SWIDTH-1:0] dq2_dfi_wrdata_p5;
   logic [BWIDTH-1:0] dq2_dfi_wrdata_mask_p5;
   logic [SWIDTH-1:0] dq3_dfi_wrdata_p5;
   logic [BWIDTH-1:0] dq3_dfi_wrdata_mask_p5;
   logic              dfi_parity_in_p5;
   logic [1:0]        dfi_wrdata_cs_p5;
   logic              dfi_wrdata_en_p5;
   logic [1:0]        dfi_wck_cs_p5;
   logic              dfi_wck_en_p5;
   logic [TWIDTH-1:0] dfi_wck_toggle_p5;
   logic [1:0]        dfi_rddata_cs_p5;
   logic              dfi_rddata_en_p5;
   logic [SWIDTH-1:0] dq0_dfi_wrdata_p6;
   logic [BWIDTH-1:0] dq0_dfi_wrdata_mask_p6;
   logic [SWIDTH-1:0] dq1_dfi_wrdata_p6;
   logic [BWIDTH-1:0] dq1_dfi_wrdata_mask_p6;
   logic [SWIDTH-1:0] dq2_dfi_wrdata_p6;
   logic [BWIDTH-1:0] dq2_dfi_wrdata_mask_p6;
   logic [SWIDTH-1:0] dq3_dfi_wrdata_p6;
   logic [BWIDTH-1:0] dq3_dfi_wrdata_mask_p6;
   logic              dfi_parity_in_p6;
   logic [1:0]        dfi_wrdata_cs_p6;
   logic              dfi_wrdata_en_p6;
   logic [1:0]        dfi_wck_cs_p6;
   logic              dfi_wck_en_p6;
   logic [TWIDTH-1:0] dfi_wck_toggle_p6;
   logic [1:0]        dfi_rddata_cs_p6;
   logic              dfi_rddata_en_p6;
   logic [SWIDTH-1:0] dq0_dfi_wrdata_p7;
   logic [BWIDTH-1:0] dq0_dfi_wrdata_mask_p7;
   logic [SWIDTH-1:0] dq1_dfi_wrdata_p7;
   logic [BWIDTH-1:0] dq1_dfi_wrdata_mask_p7;
   logic [SWIDTH-1:0] dq2_dfi_wrdata_p7;
   logic [BWIDTH-1:0] dq2_dfi_wrdata_mask_p7;
   logic [SWIDTH-1:0] dq3_dfi_wrdata_p7;
   logic [BWIDTH-1:0] dq3_dfi_wrdata_mask_p7;
   logic              dfi_parity_in_p7;
   logic [1:0]        dfi_wrdata_cs_p7;
   logic              dfi_wrdata_en_p7;
   logic [1:0]        dfi_wck_cs_p7;
   logic              dfi_wck_en_p7;
   logic [TWIDTH-1:0] dfi_wck_toggle_p7;
   logic [1:0]        dfi_rddata_cs_p7;
   logic              dfi_rddata_en_p7;
   logic [AWIDTH-1:0] dfi_address_p0;
   logic [1:0]        dfi_cke_p0;
   logic [1:0]        dfi_cs_p0;
   logic              dfi_dcd_p0;
   logic              dfi_dce_p0;
   logic [AWIDTH-1:0] dfi_address_p1;
   logic [1:0]        dfi_cke_p1;
   logic [1:0]        dfi_cs_p1;
   logic              dfi_dcd_p1;
   logic              dfi_dce_p1;
   logic [AWIDTH-1:0] dfi_address_p2;
   logic [1:0]        dfi_cke_p2;
   logic [1:0]        dfi_cs_p2;
   logic              dfi_dcd_p2;
   logic              dfi_dce_p2;
   logic [AWIDTH-1:0] dfi_address_p3;
   logic [1:0]        dfi_cke_p3;
   logic [1:0]        dfi_cs_p3;
   logic              dfi_dcd_p3;
   logic              dfi_dce_p3;
   logic [AWIDTH-1:0] dfi_address_p4;
   logic [1:0]        dfi_cke_p4;
   logic [1:0]        dfi_cs_p4;
   logic              dfi_dcd_p4;
   logic              dfi_dce_p4;
   logic [AWIDTH-1:0] dfi_address_p5;
   logic [1:0]        dfi_cke_p5;
   logic [1:0]        dfi_cs_p5;
   logic              dfi_dcd_p5;
   logic              dfi_dce_p5;
   logic [AWIDTH-1:0] dfi_address_p6;
   logic [1:0]        dfi_cke_p6;
   logic [1:0]        dfi_cs_p6;
   logic              dfi_dcd_p6;
   logic              dfi_dce_p6;
   logic [AWIDTH-1:0] dfi_address_p7;
   logic [1:0]        dfi_cke_p7;
   logic [1:0]        dfi_cs_p7;
   logic              dfi_dcd_p7;
   logic              dfi_dce_p7;

   // Current timestamp at the head of the FIFO
   assign timestamp_early = ig_rdata[IG_WIDTH-1:IG_WIDTH-TSWIDTH];

   // If the FIFO "head" timestamp matches the current runnign timestamp, then pop data
   assign ig_read = (timestamp_early == timestamp_q) & ig_empty_n & ( (ig_loop_cnt_q != 0) || (i_ig_loop_mode == 1'b0) );

   // Remove the timestamp from the read mask. Output data masked when TS does not match
   assign ig_mask_n = {{TSWIDTH{1'b1}},{IG_WIDTH-TSWIDTH{ig_read}}};

   assign dfi_dcd_p0 = ~dfi_dce_p0;
   assign dfi_dcd_p1 = ~dfi_dce_p1;
   assign dfi_dcd_p2 = ~dfi_dce_p2;
   assign dfi_dcd_p3 = ~dfi_dce_p3;
   assign dfi_dcd_p4 = ~dfi_dce_p4;
   assign dfi_dcd_p5 = ~dfi_dce_p5;
   assign dfi_dcd_p6 = ~dfi_dce_p6;
   assign dfi_dcd_p7 = ~dfi_dce_p7;

   // Ingress Read Data
   assign {
       ig_timestamp
      ,dfi_dce_p0
      ,dfi_cs_p0
      ,dfi_cke_p0
      ,dfi_address_p0
      ,dfi_dce_p1
      ,dfi_cs_p1
      ,dfi_cke_p1
      ,dfi_address_p1
      ,dfi_dce_p2
      ,dfi_cs_p2
      ,dfi_cke_p2
      ,dfi_address_p2
      ,dfi_dce_p3
      ,dfi_cs_p3
      ,dfi_cke_p3
      ,dfi_address_p3
      ,dfi_dce_p4
      ,dfi_cs_p4
      ,dfi_cke_p4
      ,dfi_address_p4
      ,dfi_dce_p5
      ,dfi_cs_p5
      ,dfi_cke_p5
      ,dfi_address_p5
      ,dfi_dce_p6
      ,dfi_cs_p6
      ,dfi_cke_p6
      ,dfi_address_p6
      ,dfi_dce_p7
      ,dfi_cs_p7
      ,dfi_cke_p7
      ,dfi_address_p7
      ,dfi_rddata_en_p0
      ,dfi_rddata_cs_p0
      ,dfi_wck_toggle_p0
      ,dfi_wck_en_p0
      ,dfi_wck_cs_p0
      ,dfi_wrdata_en_p0
      ,dfi_parity_in_p0
      ,dfi_wrdata_cs_p0
      ,dq0_dfi_wrdata_mask_p0
      ,dq0_dfi_wrdata_p0
      ,dq1_dfi_wrdata_mask_p0
      ,dq1_dfi_wrdata_p0
      ,dq2_dfi_wrdata_mask_p0
      ,dq2_dfi_wrdata_p0
      ,dq3_dfi_wrdata_mask_p0
      ,dq3_dfi_wrdata_p0
      ,dfi_rddata_en_p1
      ,dfi_rddata_cs_p1
      ,dfi_wck_toggle_p1
      ,dfi_wck_en_p1
      ,dfi_wck_cs_p1
      ,dfi_wrdata_en_p1
      ,dfi_parity_in_p1
      ,dfi_wrdata_cs_p1
      ,dq0_dfi_wrdata_mask_p1
      ,dq0_dfi_wrdata_p1
      ,dq1_dfi_wrdata_mask_p1
      ,dq1_dfi_wrdata_p1
      ,dq2_dfi_wrdata_mask_p1
      ,dq2_dfi_wrdata_p1
      ,dq3_dfi_wrdata_mask_p1
      ,dq3_dfi_wrdata_p1
      ,dfi_rddata_en_p2
      ,dfi_rddata_cs_p2
      ,dfi_wck_toggle_p2
      ,dfi_wck_en_p2
      ,dfi_wck_cs_p2
      ,dfi_wrdata_en_p2
      ,dfi_parity_in_p2
      ,dfi_wrdata_cs_p2
      ,dq0_dfi_wrdata_mask_p2
      ,dq0_dfi_wrdata_p2
      ,dq1_dfi_wrdata_mask_p2
      ,dq1_dfi_wrdata_p2
      ,dq2_dfi_wrdata_mask_p2
      ,dq2_dfi_wrdata_p2
      ,dq3_dfi_wrdata_mask_p2
      ,dq3_dfi_wrdata_p2
      ,dfi_rddata_en_p3
      ,dfi_rddata_cs_p3
      ,dfi_wck_toggle_p3
      ,dfi_wck_en_p3
      ,dfi_wck_cs_p3
      ,dfi_wrdata_en_p3
      ,dfi_parity_in_p3
      ,dfi_wrdata_cs_p3
      ,dq0_dfi_wrdata_mask_p3
      ,dq0_dfi_wrdata_p3
      ,dq1_dfi_wrdata_mask_p3
      ,dq1_dfi_wrdata_p3
      ,dq2_dfi_wrdata_mask_p3
      ,dq2_dfi_wrdata_p3
      ,dq3_dfi_wrdata_mask_p3
      ,dq3_dfi_wrdata_p3
      ,dfi_rddata_en_p4
      ,dfi_rddata_cs_p4
      ,dfi_wck_toggle_p4
      ,dfi_wck_en_p4
      ,dfi_wck_cs_p4
      ,dfi_wrdata_en_p4
      ,dfi_parity_in_p4
      ,dfi_wrdata_cs_p4
      ,dq0_dfi_wrdata_mask_p4
      ,dq0_dfi_wrdata_p4
      ,dq1_dfi_wrdata_mask_p4
      ,dq1_dfi_wrdata_p4
      ,dq2_dfi_wrdata_mask_p4
      ,dq2_dfi_wrdata_p4
      ,dq3_dfi_wrdata_mask_p4
      ,dq3_dfi_wrdata_p4
      ,dfi_rddata_en_p5
      ,dfi_rddata_cs_p5
      ,dfi_wck_toggle_p5
      ,dfi_wck_en_p5
      ,dfi_wck_cs_p5
      ,dfi_wrdata_en_p5
      ,dfi_parity_in_p5
      ,dfi_wrdata_cs_p5
      ,dq0_dfi_wrdata_mask_p5
      ,dq0_dfi_wrdata_p5
      ,dq1_dfi_wrdata_mask_p5
      ,dq1_dfi_wrdata_p5
      ,dq2_dfi_wrdata_mask_p5
      ,dq2_dfi_wrdata_p5
      ,dq3_dfi_wrdata_mask_p5
      ,dq3_dfi_wrdata_p5
      ,dfi_rddata_en_p6
      ,dfi_rddata_cs_p6
      ,dfi_wck_toggle_p6
      ,dfi_wck_en_p6
      ,dfi_wck_cs_p6
      ,dfi_wrdata_en_p6
      ,dfi_parity_in_p6
      ,dfi_wrdata_cs_p6
      ,dq0_dfi_wrdata_mask_p6
      ,dq0_dfi_wrdata_p6
      ,dq1_dfi_wrdata_mask_p6
      ,dq1_dfi_wrdata_p6
      ,dq2_dfi_wrdata_mask_p6
      ,dq2_dfi_wrdata_p6
      ,dq3_dfi_wrdata_mask_p6
      ,dq3_dfi_wrdata_p6
      ,dfi_rddata_en_p7
      ,dfi_rddata_cs_p7
      ,dfi_wck_toggle_p7
      ,dfi_wck_en_p7
      ,dfi_wck_cs_p7
      ,dfi_wrdata_en_p7
      ,dfi_parity_in_p7
      ,dfi_wrdata_cs_p7
      ,dq0_dfi_wrdata_mask_p7
      ,dq0_dfi_wrdata_p7
      ,dq1_dfi_wrdata_mask_p7
      ,dq1_dfi_wrdata_p7
      ,dq2_dfi_wrdata_mask_p7
      ,dq2_dfi_wrdata_p7
      ,dq3_dfi_wrdata_mask_p7
      ,dq3_dfi_wrdata_p7
   } = ig_rdata_q & ig_mask_n_q;

   // Synchronize CSR controls
   ddr_demet_r u_demet_2 (.i_clk(clk_g), .i_rst(i_rst), .i_d(i_ig_wdata_en ), .o_q(ig_wdata_en_sync ));
   ddr_demet_r u_demet_3 (.i_clk(clk_g), .i_rst(i_rst), .i_d(i_ig_wdata_upd), .o_q(ig_wdata_upd_sync));
   ddr_demet_r u_demet_8 (.i_clk(clk_g), .i_rst(i_rst), .i_d(i_ig_load_ptr),  .o_q(ig_load_ptr_sync));

   always_ff @ (posedge clk_g, posedge i_rst) begin
      if (i_rst) begin
         ig_wdata_en_q     <= '0;
         ig_wdata_upd_q    <= '0;
         ig_write_toggle_q <= '0;
      end else begin
         ig_wdata_en_q     <= ig_wdata_en_sync;
         ig_wdata_upd_q    <= ig_wdata_upd_sync;
         ig_write_toggle_q <= ig_write_toggle_q ^ ig_write ;
      end
   end

   // Update the data loader on a CSR toggle
   assign wdata_loader_upd =  ig_wdata_upd_q ^ ig_wdata_upd_sync;

   // Enable the data loader on a CSR toggle
   assign wdata_loader_en = ig_wdata_en_q ^ ig_wdata_en_sync;

   // Ingress Write Data Loader
   always_ff @ (posedge clk_g, posedge i_rst) begin
      if (i_rst)
         wdata_loader_q <= '0;
      else if (wdata_loader_en)
         wdata_loader_q <= {wdata_loader_q[IG_WIDTH-AHB_DWIDTH-1:0], i_ig_wdata};
   end

   assign ig_wdata        = wdata_loader_q;
   assign ig_write        = wdata_loader_upd;
   assign o_ig_empty      = ~ig_empty_n_q;
   assign o_ig_overflow   = o_ig_full & ig_write;
   assign o_ig_write_done = ig_write_toggle_q ;

   ddr_fifo #(
      .WWIDTH                       (IG_WIDTH),
      .RWIDTH                       (IG_WIDTH),
      .DEPTH                        (IG_DEPTH),
      .SYNC                         (1'b1),
      .RAM_MODEL                    (RAM_MODEL)
   ) u_ig_fifo (
      .i_scan_mode                  (i_scan_mode),
      .i_scan_rst_ctrl              (i_scan_rst_ctrl),
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_clr                        (i_ig_wdata_clr),
      .i_loop_mode                  (i_ig_loop_mode),
      .i_load_ptr                   (ig_load_ptr_sync),
      .i_stop_ptr                   (i_ig_stop_ptr ),
      .i_start_ptr                  (i_ig_start_ptr),
      .i_wclk                       (clk_g),
      .i_wrst                       (i_rst),
      .i_write                      (ig_write),
      .i_wdata                      (ig_wdata),
      .o_full                       (o_ig_full),
      .o_early_full                 (/*OPEN*/),
      .i_rclk                       (clk_g),
      .i_rrst                       (i_rst),
      .i_read                       (ig_read),
      .o_rdata                      (ig_rdata),
      .o_early_empty_n              (/*OPEN*/),
      .o_empty_n                    (ig_empty_n)
   );

   assign ig_loop_cnt_d = ig_load_ptr_sync             ? i_ig_num_loops :
                          (ig_empty_n_q & ~ig_empty_n) ? ig_loop_cnt_q - 1'b1 :
                          ig_loop_cnt_q ;

   // Hold data so values persist on bus
   always_ff @ (posedge clk_g, posedge i_rst) begin
      if (i_rst) begin
         ig_rdata_q    <= '0;
         ig_mask_n_q   <= '0;
         ig_empty_n_q  <= '0;
         ig_loop_cnt_q <= 4'h1;
      end else begin
         if (ig_read || !i_ig_wdata_hold) begin
            ig_rdata_q  <= ig_rdata;
            ig_mask_n_q <= ig_mask_n;
         end
         ig_empty_n_q  <= ig_empty_n;
         if (i_ig_loop_mode)
            ig_loop_cnt_q <= ig_loop_cnt_d;
      end
   end

   // ------------------------------------------------------------------------
   // Buffer Egress - From Datapath
   // ------------------------------------------------------------------------

   localparam EG_WIDTH = TSWIDTH
                         + (NUM_RPH*(BWIDTH+MWIDTH+SWIDTH) * NUM_DQ)
                         + (NUM_APH*(2+2+AWIDTH));

   logic [EG_WIDTH-1:0] eg_wdata, eg_rdata;
   logic eg_write, eg_read, eg_empty_n, eg_read_toggle_q ;
   logic eg_rdata_en_sync, eg_rdata_en_q;
   logic eg_rdata_upd_sync, eg_rdata_upd_q;
   logic rdata_loader_en, rdata_loader_upd;
   logic [EG_WIDTH-1:0] rdata_loader_q;

   // Read Data
   assign eg_wdata = {
       timestamp_q
       ,i_dfi_cs_w0
       ,i_dfi_cke_w0
       ,i_dfi_address_w0
       ,i_dfi_cs_w1
       ,i_dfi_cke_w1
       ,i_dfi_address_w1
       ,i_dfi_cs_w2
       ,i_dfi_cke_w2
       ,i_dfi_address_w2
       ,i_dfi_cs_w3
       ,i_dfi_cke_w3
       ,i_dfi_address_w3
       ,i_dfi_cs_w4
       ,i_dfi_cke_w4
       ,i_dfi_address_w4
       ,i_dfi_cs_w5
       ,i_dfi_cke_w5
       ,i_dfi_address_w5
       ,i_dfi_cs_w6
       ,i_dfi_cke_w6
       ,i_dfi_address_w6
       ,i_dfi_cs_w7
       ,i_dfi_cke_w7
       ,i_dfi_address_w7
       ,i_dq0_dfi_rddata_valid_w0
       ,i_dq0_dfi_rddata_dbi_w0
       ,i_dq0_dfi_rddata_w0
       ,i_dq0_dfi_rddata_valid_w1
       ,i_dq0_dfi_rddata_dbi_w1
       ,i_dq0_dfi_rddata_w1
       ,i_dq0_dfi_rddata_valid_w2
       ,i_dq0_dfi_rddata_dbi_w2
       ,i_dq0_dfi_rddata_w2
       ,i_dq0_dfi_rddata_valid_w3
       ,i_dq0_dfi_rddata_dbi_w3
       ,i_dq0_dfi_rddata_w3
       ,i_dq0_dfi_rddata_valid_w4
       ,i_dq0_dfi_rddata_dbi_w4
       ,i_dq0_dfi_rddata_w4
       ,i_dq0_dfi_rddata_valid_w5
       ,i_dq0_dfi_rddata_dbi_w5
       ,i_dq0_dfi_rddata_w5
       ,i_dq0_dfi_rddata_valid_w6
       ,i_dq0_dfi_rddata_dbi_w6
       ,i_dq0_dfi_rddata_w6
       ,i_dq0_dfi_rddata_valid_w7
       ,i_dq0_dfi_rddata_dbi_w7
       ,i_dq0_dfi_rddata_w7
       ,i_dq1_dfi_rddata_valid_w0
       ,i_dq1_dfi_rddata_dbi_w0
       ,i_dq1_dfi_rddata_w0
       ,i_dq1_dfi_rddata_valid_w1
       ,i_dq1_dfi_rddata_dbi_w1
       ,i_dq1_dfi_rddata_w1
       ,i_dq1_dfi_rddata_valid_w2
       ,i_dq1_dfi_rddata_dbi_w2
       ,i_dq1_dfi_rddata_w2
       ,i_dq1_dfi_rddata_valid_w3
       ,i_dq1_dfi_rddata_dbi_w3
       ,i_dq1_dfi_rddata_w3
       ,i_dq1_dfi_rddata_valid_w4
       ,i_dq1_dfi_rddata_dbi_w4
       ,i_dq1_dfi_rddata_w4
       ,i_dq1_dfi_rddata_valid_w5
       ,i_dq1_dfi_rddata_dbi_w5
       ,i_dq1_dfi_rddata_w5
       ,i_dq1_dfi_rddata_valid_w6
       ,i_dq1_dfi_rddata_dbi_w6
       ,i_dq1_dfi_rddata_w6
       ,i_dq1_dfi_rddata_valid_w7
       ,i_dq1_dfi_rddata_dbi_w7
       ,i_dq1_dfi_rddata_w7
       ,i_dq2_dfi_rddata_valid_w0
       ,i_dq2_dfi_rddata_dbi_w0
       ,i_dq2_dfi_rddata_w0
       ,i_dq2_dfi_rddata_valid_w1
       ,i_dq2_dfi_rddata_dbi_w1
       ,i_dq2_dfi_rddata_w1
       ,i_dq2_dfi_rddata_valid_w2
       ,i_dq2_dfi_rddata_dbi_w2
       ,i_dq2_dfi_rddata_w2
       ,i_dq2_dfi_rddata_valid_w3
       ,i_dq2_dfi_rddata_dbi_w3
       ,i_dq2_dfi_rddata_w3
       ,i_dq2_dfi_rddata_valid_w4
       ,i_dq2_dfi_rddata_dbi_w4
       ,i_dq2_dfi_rddata_w4
       ,i_dq2_dfi_rddata_valid_w5
       ,i_dq2_dfi_rddata_dbi_w5
       ,i_dq2_dfi_rddata_w5
       ,i_dq2_dfi_rddata_valid_w6
       ,i_dq2_dfi_rddata_dbi_w6
       ,i_dq2_dfi_rddata_w6
       ,i_dq2_dfi_rddata_valid_w7
       ,i_dq2_dfi_rddata_dbi_w7
       ,i_dq2_dfi_rddata_w7
       ,i_dq3_dfi_rddata_valid_w0
       ,i_dq3_dfi_rddata_dbi_w0
       ,i_dq3_dfi_rddata_w0
       ,i_dq3_dfi_rddata_valid_w1
       ,i_dq3_dfi_rddata_dbi_w1
       ,i_dq3_dfi_rddata_w1
       ,i_dq3_dfi_rddata_valid_w2
       ,i_dq3_dfi_rddata_dbi_w2
       ,i_dq3_dfi_rddata_w2
       ,i_dq3_dfi_rddata_valid_w3
       ,i_dq3_dfi_rddata_dbi_w3
       ,i_dq3_dfi_rddata_w3
       ,i_dq3_dfi_rddata_valid_w4
       ,i_dq3_dfi_rddata_dbi_w4
       ,i_dq3_dfi_rddata_w4
       ,i_dq3_dfi_rddata_valid_w5
       ,i_dq3_dfi_rddata_dbi_w5
       ,i_dq3_dfi_rddata_w5
       ,i_dq3_dfi_rddata_valid_w6
       ,i_dq3_dfi_rddata_dbi_w6
       ,i_dq3_dfi_rddata_w6
       ,i_dq3_dfi_rddata_valid_w7
       ,i_dq3_dfi_rddata_dbi_w7
       ,i_dq3_dfi_rddata_w7
   };

   assign eg_write   = (
    (|i_dq0_dfi_rddata_valid_w0) |
    (|i_dq0_dfi_rddata_valid_w1) |
    (|i_dq0_dfi_rddata_valid_w2) |
    (|i_dq0_dfi_rddata_valid_w3) |
    (|i_dq0_dfi_rddata_valid_w4) |
    (|i_dq0_dfi_rddata_valid_w5) |
    (|i_dq0_dfi_rddata_valid_w6) |
    (|i_dq0_dfi_rddata_valid_w7) |
    (|i_dfi_address_valid_w0)    |
    (|i_dfi_address_valid_w1)    |
    (|i_dfi_address_valid_w2)    |
    (|i_dfi_address_valid_w3)    |
    (|i_dfi_address_valid_w4)    |
    (|i_dfi_address_valid_w5)    |
    (|i_dfi_address_valid_w6)    |
    (|i_dfi_address_valid_w7)    |
    (|i_dq1_dfi_rddata_valid_w0) |
    (|i_dq1_dfi_rddata_valid_w1) |
    (|i_dq1_dfi_rddata_valid_w2) |
    (|i_dq1_dfi_rddata_valid_w3) |
    (|i_dq1_dfi_rddata_valid_w4) |
    (|i_dq1_dfi_rddata_valid_w5) |
    (|i_dq1_dfi_rddata_valid_w6) |
    (|i_dq1_dfi_rddata_valid_w7) |
    (|i_dfi_address_valid_w0)    |
    (|i_dfi_address_valid_w1)    |
    (|i_dfi_address_valid_w2)    |
    (|i_dfi_address_valid_w3)    |
    (|i_dfi_address_valid_w4)    |
    (|i_dfi_address_valid_w5)    |
    (|i_dfi_address_valid_w6)    |
    (|i_dfi_address_valid_w7)    |
    (|i_dq2_dfi_rddata_valid_w0) |
    (|i_dq2_dfi_rddata_valid_w1) |
    (|i_dq2_dfi_rddata_valid_w2) |
    (|i_dq2_dfi_rddata_valid_w3) |
    (|i_dq2_dfi_rddata_valid_w4) |
    (|i_dq2_dfi_rddata_valid_w5) |
    (|i_dq2_dfi_rddata_valid_w6) |
    (|i_dq2_dfi_rddata_valid_w7) |
    (|i_dfi_address_valid_w0)    |
    (|i_dfi_address_valid_w1)    |
    (|i_dfi_address_valid_w2)    |
    (|i_dfi_address_valid_w3)    |
    (|i_dfi_address_valid_w4)    |
    (|i_dfi_address_valid_w5)    |
    (|i_dfi_address_valid_w6)    |
    (|i_dfi_address_valid_w7)    |
    (|i_dq3_dfi_rddata_valid_w0) |
    (|i_dq3_dfi_rddata_valid_w1) |
    (|i_dq3_dfi_rddata_valid_w2) |
    (|i_dq3_dfi_rddata_valid_w3) |
    (|i_dq3_dfi_rddata_valid_w4) |
    (|i_dq3_dfi_rddata_valid_w5) |
    (|i_dq3_dfi_rddata_valid_w6) |
    (|i_dq3_dfi_rddata_valid_w7) |
    (|i_dfi_address_valid_w0)    |
    (|i_dfi_address_valid_w1)    |
    (|i_dfi_address_valid_w2)    |
    (|i_dfi_address_valid_w3)    |
    (|i_dfi_address_valid_w4)    |
    (|i_dfi_address_valid_w5)    |
    (|i_dfi_address_valid_w6)    |
    (|i_dfi_address_valid_w7)    |
      1'b0
   );

   assign o_eg_empty     =  ~eg_empty_n ;
   assign o_eg_overflow  = o_eg_full & eg_write;
   assign o_eg_read_done = eg_read_toggle_q ;

   ddr_fifo #(
      .WWIDTH                       (EG_WIDTH),
      .RWIDTH                       (EG_WIDTH),
      .DEPTH                        (EG_DEPTH),
      .SYNC                         (1'b1),
      .RAM_MODEL                    (RAM_MODEL)
   ) u_eg_fifo (
      .i_scan_mode                  (i_scan_mode),
      .i_scan_rst_ctrl              (i_scan_rst_ctrl),
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_clr                        (i_eg_rdata_clr),
      .i_loop_mode                  ('0),
      .i_load_ptr                   ('0),
      .i_stop_ptr                   ('0),
      .i_start_ptr                  ('0),
      .i_wclk                       (clk_g),
      .i_wrst                       (i_rst),
      .i_write                      (eg_write),
      .i_wdata                      (eg_wdata),
      .o_full                       (o_eg_full),
      .o_early_full                 (/*OPEN*/),
      .i_rclk                       (clk_g),
      .i_rrst                       (i_rst),
      .i_read                       (eg_read),
      .o_rdata                      (eg_rdata),
      .o_early_empty_n              (/*OPEN*/),
      .o_empty_n                    (eg_empty_n)
   );

   // Synchronize CSR controls
   ddr_demet_r u_demet_4 (.i_clk(clk_g), .i_rst(i_rst), .i_d(i_eg_rdata_en ), .o_q(eg_rdata_en_sync ));
   ddr_demet_r u_demet_5 (.i_clk(clk_g), .i_rst(i_rst), .i_d(i_eg_rdata_upd), .o_q(eg_rdata_upd_sync));

   always_ff @ (posedge clk_g, posedge i_rst) begin
      if (i_rst) begin
         eg_rdata_en_q     <= '0;
         eg_rdata_upd_q    <= '0;
         eg_read_toggle_q  <= '0;
      end else begin
         eg_rdata_en_q     <= eg_rdata_en_sync;
         eg_rdata_upd_q    <= eg_rdata_upd_sync;
         eg_read_toggle_q  <= eg_read_toggle_q ^ eg_read ;
      end
   end

   // Update the data loader on a CSR toggle
   assign rdata_loader_upd =  eg_rdata_upd_q ^ eg_rdata_upd_sync;

   // Enable the data loader on a CSR toggle
   assign rdata_loader_en = eg_rdata_en_q ^ eg_rdata_en_sync;

   // Egress Write Data Loader
   always_ff @ (posedge clk_g, posedge i_rst) begin
      if (i_rst)
         rdata_loader_q <= '0;
      else if (rdata_loader_upd)
         rdata_loader_q <= eg_rdata;
      else if (rdata_loader_en)
         rdata_loader_q <= {{AHB_DWIDTH{1'b0}},rdata_loader_q[EG_WIDTH-1:AHB_DWIDTH]};
   end

   // Pop read data from Egress FIFO
   assign eg_read = rdata_loader_upd;

   // Read data to CSR
   assign o_eg_rdata = rdata_loader_q[AHB_DWIDTH-1:0];

   // ------------------------------------------------------------------------
   // Mode Mux
   // ------------------------------------------------------------------------
   // Write Command Address Data
   logic [AWIDTH-1:0]        int_dfi_address_p0;
   logic [AWIDTH-1:0]        int_dfi_address_p1;
   logic [AWIDTH-1:0]        int_dfi_address_p2;
   logic [AWIDTH-1:0]        int_dfi_address_p3;
   logic [AWIDTH-1:0]        int_dfi_address_p4;
   logic [AWIDTH-1:0]        int_dfi_address_p5;
   logic [AWIDTH-1:0]        int_dfi_address_p6;
   logic [AWIDTH-1:0]        int_dfi_address_p7;

   logic [1:0]               int_dfi_cke_p0;
   logic [1:0]               int_dfi_cke_p1;
   logic [1:0]               int_dfi_cke_p2;
   logic [1:0]               int_dfi_cke_p3;
   logic [1:0]               int_dfi_cke_p4;
   logic [1:0]               int_dfi_cke_p5;
   logic [1:0]               int_dfi_cke_p6;
   logic [1:0]               int_dfi_cke_p7;

   logic [1:0]               int_dfi_cs_p0;
   logic [1:0]               int_dfi_cs_p1;
   logic [1:0]               int_dfi_cs_p2;
   logic [1:0]               int_dfi_cs_p3;
   logic [1:0]               int_dfi_cs_p4;
   logic [1:0]               int_dfi_cs_p5;
   logic [1:0]               int_dfi_cs_p6;
   logic [1:0]               int_dfi_cs_p7;

   logic                     int_dfi_dcd_p0;
   logic                     int_dfi_dcd_p1;
   logic                     int_dfi_dcd_p2;
   logic                     int_dfi_dcd_p3;
   logic                     int_dfi_dcd_p4;
   logic                     int_dfi_dcd_p5;
   logic                     int_dfi_dcd_p6;
   logic                     int_dfi_dcd_p7;

   logic [SWIDTH-1:0]        int_dq0_dfi_wrdata_p0;
   logic [SWIDTH-1:0]        int_dq0_dfi_wrdata_p1;
   logic [SWIDTH-1:0]        int_dq0_dfi_wrdata_p2;
   logic [SWIDTH-1:0]        int_dq0_dfi_wrdata_p3;
   logic [SWIDTH-1:0]        int_dq0_dfi_wrdata_p4;
   logic [SWIDTH-1:0]        int_dq0_dfi_wrdata_p5;
   logic [SWIDTH-1:0]        int_dq0_dfi_wrdata_p6;
   logic [SWIDTH-1:0]        int_dq0_dfi_wrdata_p7;
   logic [SWIDTH-1:0]        int_dq1_dfi_wrdata_p0;
   logic [SWIDTH-1:0]        int_dq1_dfi_wrdata_p1;
   logic [SWIDTH-1:0]        int_dq1_dfi_wrdata_p2;
   logic [SWIDTH-1:0]        int_dq1_dfi_wrdata_p3;
   logic [SWIDTH-1:0]        int_dq1_dfi_wrdata_p4;
   logic [SWIDTH-1:0]        int_dq1_dfi_wrdata_p5;
   logic [SWIDTH-1:0]        int_dq1_dfi_wrdata_p6;
   logic [SWIDTH-1:0]        int_dq1_dfi_wrdata_p7;
   logic [SWIDTH-1:0]        int_dq2_dfi_wrdata_p0;
   logic [SWIDTH-1:0]        int_dq2_dfi_wrdata_p1;
   logic [SWIDTH-1:0]        int_dq2_dfi_wrdata_p2;
   logic [SWIDTH-1:0]        int_dq2_dfi_wrdata_p3;
   logic [SWIDTH-1:0]        int_dq2_dfi_wrdata_p4;
   logic [SWIDTH-1:0]        int_dq2_dfi_wrdata_p5;
   logic [SWIDTH-1:0]        int_dq2_dfi_wrdata_p6;
   logic [SWIDTH-1:0]        int_dq2_dfi_wrdata_p7;
   logic [SWIDTH-1:0]        int_dq3_dfi_wrdata_p0;
   logic [SWIDTH-1:0]        int_dq3_dfi_wrdata_p1;
   logic [SWIDTH-1:0]        int_dq3_dfi_wrdata_p2;
   logic [SWIDTH-1:0]        int_dq3_dfi_wrdata_p3;
   logic [SWIDTH-1:0]        int_dq3_dfi_wrdata_p4;
   logic [SWIDTH-1:0]        int_dq3_dfi_wrdata_p5;
   logic [SWIDTH-1:0]        int_dq3_dfi_wrdata_p6;
   logic [SWIDTH-1:0]        int_dq3_dfi_wrdata_p7;
   logic                     int_dfi_parity_in_p0;
   logic                     int_dfi_parity_in_p1;
   logic                     int_dfi_parity_in_p2;
   logic                     int_dfi_parity_in_p3;
   logic                     int_dfi_parity_in_p4;
   logic                     int_dfi_parity_in_p5;
   logic                     int_dfi_parity_in_p6;
   logic                     int_dfi_parity_in_p7;
   logic                     int_dfi_wrdata_cs_p0;
   logic                     int_dfi_wrdata_cs_p1;
   logic                     int_dfi_wrdata_cs_p2;
   logic                     int_dfi_wrdata_cs_p3;
   logic                     int_dfi_wrdata_cs_p4;
   logic                     int_dfi_wrdata_cs_p5;
   logic                     int_dfi_wrdata_cs_p6;
   logic                     int_dfi_wrdata_cs_p7;
   logic [BWIDTH-1:0]        int_dq0_dfi_wrdata_mask_p0;
   logic [BWIDTH-1:0]        int_dq0_dfi_wrdata_mask_p1;
   logic [BWIDTH-1:0]        int_dq0_dfi_wrdata_mask_p2;
   logic [BWIDTH-1:0]        int_dq0_dfi_wrdata_mask_p3;
   logic [BWIDTH-1:0]        int_dq0_dfi_wrdata_mask_p4;
   logic [BWIDTH-1:0]        int_dq0_dfi_wrdata_mask_p5;
   logic [BWIDTH-1:0]        int_dq0_dfi_wrdata_mask_p6;
   logic [BWIDTH-1:0]        int_dq0_dfi_wrdata_mask_p7;
   logic [BWIDTH-1:0]        int_dq1_dfi_wrdata_mask_p0;
   logic [BWIDTH-1:0]        int_dq1_dfi_wrdata_mask_p1;
   logic [BWIDTH-1:0]        int_dq1_dfi_wrdata_mask_p2;
   logic [BWIDTH-1:0]        int_dq1_dfi_wrdata_mask_p3;
   logic [BWIDTH-1:0]        int_dq1_dfi_wrdata_mask_p4;
   logic [BWIDTH-1:0]        int_dq1_dfi_wrdata_mask_p5;
   logic [BWIDTH-1:0]        int_dq1_dfi_wrdata_mask_p6;
   logic [BWIDTH-1:0]        int_dq1_dfi_wrdata_mask_p7;
   logic [BWIDTH-1:0]        int_dq2_dfi_wrdata_mask_p0;
   logic [BWIDTH-1:0]        int_dq2_dfi_wrdata_mask_p1;
   logic [BWIDTH-1:0]        int_dq2_dfi_wrdata_mask_p2;
   logic [BWIDTH-1:0]        int_dq2_dfi_wrdata_mask_p3;
   logic [BWIDTH-1:0]        int_dq2_dfi_wrdata_mask_p4;
   logic [BWIDTH-1:0]        int_dq2_dfi_wrdata_mask_p5;
   logic [BWIDTH-1:0]        int_dq2_dfi_wrdata_mask_p6;
   logic [BWIDTH-1:0]        int_dq2_dfi_wrdata_mask_p7;
   logic [BWIDTH-1:0]        int_dq3_dfi_wrdata_mask_p0;
   logic [BWIDTH-1:0]        int_dq3_dfi_wrdata_mask_p1;
   logic [BWIDTH-1:0]        int_dq3_dfi_wrdata_mask_p2;
   logic [BWIDTH-1:0]        int_dq3_dfi_wrdata_mask_p3;
   logic [BWIDTH-1:0]        int_dq3_dfi_wrdata_mask_p4;
   logic [BWIDTH-1:0]        int_dq3_dfi_wrdata_mask_p5;
   logic [BWIDTH-1:0]        int_dq3_dfi_wrdata_mask_p6;
   logic [BWIDTH-1:0]        int_dq3_dfi_wrdata_mask_p7;
   logic                     int_dfi_wrdata_en_p0;
   logic                     int_dfi_wrdata_en_p1;
   logic                     int_dfi_wrdata_en_p2;
   logic                     int_dfi_wrdata_en_p3;
   logic                     int_dfi_wrdata_en_p4;
   logic                     int_dfi_wrdata_en_p5;
   logic                     int_dfi_wrdata_en_p6;
   logic                     int_dfi_wrdata_en_p7;
    logic                    int_dfi_wck_cs_p0;
    logic                    int_dfi_wck_cs_p1;
    logic                    int_dfi_wck_cs_p2;
    logic                    int_dfi_wck_cs_p3;
    logic                    int_dfi_wck_cs_p4;
    logic                    int_dfi_wck_cs_p5;
    logic                    int_dfi_wck_cs_p6;
    logic                    int_dfi_wck_cs_p7;
   logic                     int_dfi_wck_en_p0;
   logic                     int_dfi_wck_en_p1;
   logic                     int_dfi_wck_en_p2;
   logic                     int_dfi_wck_en_p3;
   logic                     int_dfi_wck_en_p4;
   logic                     int_dfi_wck_en_p5;
   logic                     int_dfi_wck_en_p6;
   logic                     int_dfi_wck_en_p7;
   logic [TWIDTH-1:0]        int_dfi_wck_toggle_p0;
   logic [TWIDTH-1:0]        int_dfi_wck_toggle_p1;
   logic [TWIDTH-1:0]        int_dfi_wck_toggle_p2;
   logic [TWIDTH-1:0]        int_dfi_wck_toggle_p3;
   logic [TWIDTH-1:0]        int_dfi_wck_toggle_p4;
   logic [TWIDTH-1:0]        int_dfi_wck_toggle_p5;
   logic [TWIDTH-1:0]        int_dfi_wck_toggle_p6;
   logic [TWIDTH-1:0]        int_dfi_wck_toggle_p7;
   logic                     int_dfi_rddata_cs_p0;
   logic                     int_dfi_rddata_cs_p1;
   logic                     int_dfi_rddata_cs_p2;
   logic                     int_dfi_rddata_cs_p3;
   logic                     int_dfi_rddata_cs_p4;
   logic                     int_dfi_rddata_cs_p5;
   logic                     int_dfi_rddata_cs_p6;
   logic                     int_dfi_rddata_cs_p7;
   logic                     int_dfi_rddata_en_p0;
   logic                     int_dfi_rddata_en_p1;
   logic                     int_dfi_rddata_en_p2;
   logic                     int_dfi_rddata_en_p3;
   logic                     int_dfi_rddata_en_p4;
   logic                     int_dfi_rddata_en_p5;
   logic                     int_dfi_rddata_en_p6;
   logic                     int_dfi_rddata_en_p7;

   ddr_mux #(.DWIDTH(1)) u_dq0_mux_p0_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p0[0*SWIDTH+:SWIDTH]),       .i_b(dq0_dfi_wrdata_p0     ),    .o_z(int_dq0_dfi_wrdata_p0      ));
   ddr_mux #(.DWIDTH(1)) u_dq0_mux_p0_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p0[0*MWIDTH+:MWIDTH]),  .i_b(dq0_dfi_wrdata_mask_p0),    .o_z(int_dq0_dfi_wrdata_mask_p0 ));
   ddr_mux #(.DWIDTH(1)) u_dq1_mux_p0_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p0[1*SWIDTH+:SWIDTH]),       .i_b(dq1_dfi_wrdata_p0     ),    .o_z(int_dq1_dfi_wrdata_p0      ));
   ddr_mux #(.DWIDTH(1)) u_dq1_mux_p0_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p0[1*MWIDTH+:MWIDTH]),  .i_b(dq1_dfi_wrdata_mask_p0),    .o_z(int_dq1_dfi_wrdata_mask_p0 ));
   ddr_mux #(.DWIDTH(1)) u_dq2_mux_p0_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p0[2*SWIDTH+:SWIDTH]),       .i_b(dq2_dfi_wrdata_p0     ),    .o_z(int_dq2_dfi_wrdata_p0      ));
   ddr_mux #(.DWIDTH(1)) u_dq2_mux_p0_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p0[2*MWIDTH+:MWIDTH]),  .i_b(dq2_dfi_wrdata_mask_p0),    .o_z(int_dq2_dfi_wrdata_mask_p0 ));
   ddr_mux #(.DWIDTH(1)) u_dq3_mux_p0_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p0[3*SWIDTH+:SWIDTH]),       .i_b(dq3_dfi_wrdata_p0     ),    .o_z(int_dq3_dfi_wrdata_p0      ));
   ddr_mux #(.DWIDTH(1)) u_dq3_mux_p0_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p0[3*MWIDTH+:MWIDTH]),  .i_b(dq3_dfi_wrdata_mask_p0),    .o_z(int_dq3_dfi_wrdata_mask_p0 ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p0_0              (.i_sel(buf_mode_sync), .i_a(i_dfi_parity_in_p0 ),                      .i_b(dfi_parity_in_p0  ),        .o_z(int_dfi_parity_in_p0  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p0_1              (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_cs_p0[1]),                  .i_b(dfi_wrdata_cs_p0[1]),        .o_z(int_dfi_wrdata_cs_p0 ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p0_2              (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_en_p0 ),                      .i_b(dfi_wrdata_en_p0  ),        .o_z(int_dfi_wrdata_en_p0  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p0_3              (.i_sel(buf_mode_sync), .i_a(i_dfi_wck_cs_p0[1]    ),                 .i_b(dfi_wck_cs_p0[1] ),        .o_z(int_dfi_wck_cs_p0  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p0_4              (.i_sel(buf_mode_sync), .i_a(i_dfi_wck_en_p0    ),                      .i_b(dfi_wck_en_p0     ),        .o_z(int_dfi_wck_en_p0     ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p0_5 [TWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wck_toggle_p0),                      .i_b(dfi_wck_toggle_p0 ),        .o_z(int_dfi_wck_toggle_p0 ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p0_6              (.i_sel(buf_mode_sync), .i_a(i_dfi_rddata_cs_p0[1] ),                      .i_b(dfi_rddata_cs_p0[1]  ),        .o_z(int_dfi_rddata_cs_p0  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p0_7              (.i_sel(buf_mode_sync), .i_a(i_dfi_rddata_en_p0 ),                      .i_b(dfi_rddata_en_p0  ),        .o_z(int_dfi_rddata_en_p0  ));
   ddr_mux #(.DWIDTH(1)) u_dq0_mux_p1_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p1[0*SWIDTH+:SWIDTH]),       .i_b(dq0_dfi_wrdata_p1     ),    .o_z(int_dq0_dfi_wrdata_p1      ));
   ddr_mux #(.DWIDTH(1)) u_dq0_mux_p1_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p1[0*MWIDTH+:MWIDTH]),  .i_b(dq0_dfi_wrdata_mask_p1),    .o_z(int_dq0_dfi_wrdata_mask_p1 ));
   ddr_mux #(.DWIDTH(1)) u_dq1_mux_p1_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p1[1*SWIDTH+:SWIDTH]),       .i_b(dq1_dfi_wrdata_p1     ),    .o_z(int_dq1_dfi_wrdata_p1      ));
   ddr_mux #(.DWIDTH(1)) u_dq1_mux_p1_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p1[1*MWIDTH+:MWIDTH]),  .i_b(dq1_dfi_wrdata_mask_p1),    .o_z(int_dq1_dfi_wrdata_mask_p1 ));
   ddr_mux #(.DWIDTH(1)) u_dq2_mux_p1_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p1[2*SWIDTH+:SWIDTH]),       .i_b(dq2_dfi_wrdata_p1     ),    .o_z(int_dq2_dfi_wrdata_p1      ));
   ddr_mux #(.DWIDTH(1)) u_dq2_mux_p1_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p1[2*MWIDTH+:MWIDTH]),  .i_b(dq2_dfi_wrdata_mask_p1),    .o_z(int_dq2_dfi_wrdata_mask_p1 ));
   ddr_mux #(.DWIDTH(1)) u_dq3_mux_p1_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p1[3*SWIDTH+:SWIDTH]),       .i_b(dq3_dfi_wrdata_p1     ),    .o_z(int_dq3_dfi_wrdata_p1      ));
   ddr_mux #(.DWIDTH(1)) u_dq3_mux_p1_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p1[3*MWIDTH+:MWIDTH]),  .i_b(dq3_dfi_wrdata_mask_p1),    .o_z(int_dq3_dfi_wrdata_mask_p1 ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p1_0              (.i_sel(buf_mode_sync), .i_a(i_dfi_parity_in_p1 ),                      .i_b(dfi_parity_in_p1  ),        .o_z(int_dfi_parity_in_p1  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p1_1              (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_cs_p1[1]),                  .i_b(dfi_wrdata_cs_p1[1]),        .o_z(int_dfi_wrdata_cs_p1 ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p1_2              (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_en_p1 ),                      .i_b(dfi_wrdata_en_p1  ),        .o_z(int_dfi_wrdata_en_p1  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p1_3              (.i_sel(buf_mode_sync), .i_a(i_dfi_wck_cs_p1[1]    ),                 .i_b(dfi_wck_cs_p1[1] ),        .o_z(int_dfi_wck_cs_p1  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p1_4              (.i_sel(buf_mode_sync), .i_a(i_dfi_wck_en_p1    ),                      .i_b(dfi_wck_en_p1     ),        .o_z(int_dfi_wck_en_p1     ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p1_5 [TWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wck_toggle_p1),                      .i_b(dfi_wck_toggle_p1 ),        .o_z(int_dfi_wck_toggle_p1 ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p1_6              (.i_sel(buf_mode_sync), .i_a(i_dfi_rddata_cs_p1[1] ),                      .i_b(dfi_rddata_cs_p1[1]  ),        .o_z(int_dfi_rddata_cs_p1  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p1_7              (.i_sel(buf_mode_sync), .i_a(i_dfi_rddata_en_p1 ),                      .i_b(dfi_rddata_en_p1  ),        .o_z(int_dfi_rddata_en_p1  ));
   ddr_mux #(.DWIDTH(1)) u_dq0_mux_p2_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p2[0*SWIDTH+:SWIDTH]),       .i_b(dq0_dfi_wrdata_p2     ),    .o_z(int_dq0_dfi_wrdata_p2      ));
   ddr_mux #(.DWIDTH(1)) u_dq0_mux_p2_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p2[0*MWIDTH+:MWIDTH]),  .i_b(dq0_dfi_wrdata_mask_p2),    .o_z(int_dq0_dfi_wrdata_mask_p2 ));
   ddr_mux #(.DWIDTH(1)) u_dq1_mux_p2_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p2[1*SWIDTH+:SWIDTH]),       .i_b(dq1_dfi_wrdata_p2     ),    .o_z(int_dq1_dfi_wrdata_p2      ));
   ddr_mux #(.DWIDTH(1)) u_dq1_mux_p2_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p2[1*MWIDTH+:MWIDTH]),  .i_b(dq1_dfi_wrdata_mask_p2),    .o_z(int_dq1_dfi_wrdata_mask_p2 ));
   ddr_mux #(.DWIDTH(1)) u_dq2_mux_p2_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p2[2*SWIDTH+:SWIDTH]),       .i_b(dq2_dfi_wrdata_p2     ),    .o_z(int_dq2_dfi_wrdata_p2      ));
   ddr_mux #(.DWIDTH(1)) u_dq2_mux_p2_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p2[2*MWIDTH+:MWIDTH]),  .i_b(dq2_dfi_wrdata_mask_p2),    .o_z(int_dq2_dfi_wrdata_mask_p2 ));
   ddr_mux #(.DWIDTH(1)) u_dq3_mux_p2_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p2[3*SWIDTH+:SWIDTH]),       .i_b(dq3_dfi_wrdata_p2     ),    .o_z(int_dq3_dfi_wrdata_p2      ));
   ddr_mux #(.DWIDTH(1)) u_dq3_mux_p2_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p2[3*MWIDTH+:MWIDTH]),  .i_b(dq3_dfi_wrdata_mask_p2),    .o_z(int_dq3_dfi_wrdata_mask_p2 ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p2_0              (.i_sel(buf_mode_sync), .i_a(i_dfi_parity_in_p2 ),                      .i_b(dfi_parity_in_p2  ),        .o_z(int_dfi_parity_in_p2  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p2_1              (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_cs_p2[1]),                  .i_b(dfi_wrdata_cs_p2[1]),        .o_z(int_dfi_wrdata_cs_p2 ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p2_2              (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_en_p2 ),                      .i_b(dfi_wrdata_en_p2  ),        .o_z(int_dfi_wrdata_en_p2  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p2_3              (.i_sel(buf_mode_sync), .i_a(i_dfi_wck_cs_p2[1]    ),                 .i_b(dfi_wck_cs_p2[1] ),        .o_z(int_dfi_wck_cs_p2  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p2_4              (.i_sel(buf_mode_sync), .i_a(i_dfi_wck_en_p2    ),                      .i_b(dfi_wck_en_p2     ),        .o_z(int_dfi_wck_en_p2     ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p2_5 [TWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wck_toggle_p2),                      .i_b(dfi_wck_toggle_p2 ),        .o_z(int_dfi_wck_toggle_p2 ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p2_6              (.i_sel(buf_mode_sync), .i_a(i_dfi_rddata_cs_p2[1] ),                      .i_b(dfi_rddata_cs_p2[1]  ),        .o_z(int_dfi_rddata_cs_p2  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p2_7              (.i_sel(buf_mode_sync), .i_a(i_dfi_rddata_en_p2 ),                      .i_b(dfi_rddata_en_p2  ),        .o_z(int_dfi_rddata_en_p2  ));
   ddr_mux #(.DWIDTH(1)) u_dq0_mux_p3_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p3[0*SWIDTH+:SWIDTH]),       .i_b(dq0_dfi_wrdata_p3     ),    .o_z(int_dq0_dfi_wrdata_p3      ));
   ddr_mux #(.DWIDTH(1)) u_dq0_mux_p3_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p3[0*MWIDTH+:MWIDTH]),  .i_b(dq0_dfi_wrdata_mask_p3),    .o_z(int_dq0_dfi_wrdata_mask_p3 ));
   ddr_mux #(.DWIDTH(1)) u_dq1_mux_p3_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p3[1*SWIDTH+:SWIDTH]),       .i_b(dq1_dfi_wrdata_p3     ),    .o_z(int_dq1_dfi_wrdata_p3      ));
   ddr_mux #(.DWIDTH(1)) u_dq1_mux_p3_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p3[1*MWIDTH+:MWIDTH]),  .i_b(dq1_dfi_wrdata_mask_p3),    .o_z(int_dq1_dfi_wrdata_mask_p3 ));
   ddr_mux #(.DWIDTH(1)) u_dq2_mux_p3_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p3[2*SWIDTH+:SWIDTH]),       .i_b(dq2_dfi_wrdata_p3     ),    .o_z(int_dq2_dfi_wrdata_p3      ));
   ddr_mux #(.DWIDTH(1)) u_dq2_mux_p3_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p3[2*MWIDTH+:MWIDTH]),  .i_b(dq2_dfi_wrdata_mask_p3),    .o_z(int_dq2_dfi_wrdata_mask_p3 ));
   ddr_mux #(.DWIDTH(1)) u_dq3_mux_p3_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p3[3*SWIDTH+:SWIDTH]),       .i_b(dq3_dfi_wrdata_p3     ),    .o_z(int_dq3_dfi_wrdata_p3      ));
   ddr_mux #(.DWIDTH(1)) u_dq3_mux_p3_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p3[3*MWIDTH+:MWIDTH]),  .i_b(dq3_dfi_wrdata_mask_p3),    .o_z(int_dq3_dfi_wrdata_mask_p3 ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p3_0              (.i_sel(buf_mode_sync), .i_a(i_dfi_parity_in_p3 ),                      .i_b(dfi_parity_in_p3  ),        .o_z(int_dfi_parity_in_p3  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p3_1              (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_cs_p3[1]),                  .i_b(dfi_wrdata_cs_p3[1]),        .o_z(int_dfi_wrdata_cs_p3 ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p3_2              (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_en_p3 ),                      .i_b(dfi_wrdata_en_p3  ),        .o_z(int_dfi_wrdata_en_p3  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p3_3              (.i_sel(buf_mode_sync), .i_a(i_dfi_wck_cs_p3[1]    ),                 .i_b(dfi_wck_cs_p3[1] ),        .o_z(int_dfi_wck_cs_p3  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p3_4              (.i_sel(buf_mode_sync), .i_a(i_dfi_wck_en_p3    ),                      .i_b(dfi_wck_en_p3     ),        .o_z(int_dfi_wck_en_p3     ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p3_5 [TWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wck_toggle_p3),                      .i_b(dfi_wck_toggle_p3 ),        .o_z(int_dfi_wck_toggle_p3 ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p3_6              (.i_sel(buf_mode_sync), .i_a(i_dfi_rddata_cs_p3[1] ),                      .i_b(dfi_rddata_cs_p3[1]  ),        .o_z(int_dfi_rddata_cs_p3  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p3_7              (.i_sel(buf_mode_sync), .i_a(i_dfi_rddata_en_p3 ),                      .i_b(dfi_rddata_en_p3  ),        .o_z(int_dfi_rddata_en_p3  ));
   ddr_mux #(.DWIDTH(1)) u_dq0_mux_p4_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p4[0*SWIDTH+:SWIDTH]),       .i_b(dq0_dfi_wrdata_p4     ),    .o_z(int_dq0_dfi_wrdata_p4      ));
   ddr_mux #(.DWIDTH(1)) u_dq0_mux_p4_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p4[0*MWIDTH+:MWIDTH]),  .i_b(dq0_dfi_wrdata_mask_p4),    .o_z(int_dq0_dfi_wrdata_mask_p4 ));
   ddr_mux #(.DWIDTH(1)) u_dq1_mux_p4_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p4[1*SWIDTH+:SWIDTH]),       .i_b(dq1_dfi_wrdata_p4     ),    .o_z(int_dq1_dfi_wrdata_p4      ));
   ddr_mux #(.DWIDTH(1)) u_dq1_mux_p4_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p4[1*MWIDTH+:MWIDTH]),  .i_b(dq1_dfi_wrdata_mask_p4),    .o_z(int_dq1_dfi_wrdata_mask_p4 ));
   ddr_mux #(.DWIDTH(1)) u_dq2_mux_p4_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p4[2*SWIDTH+:SWIDTH]),       .i_b(dq2_dfi_wrdata_p4     ),    .o_z(int_dq2_dfi_wrdata_p4      ));
   ddr_mux #(.DWIDTH(1)) u_dq2_mux_p4_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p4[2*MWIDTH+:MWIDTH]),  .i_b(dq2_dfi_wrdata_mask_p4),    .o_z(int_dq2_dfi_wrdata_mask_p4 ));
   ddr_mux #(.DWIDTH(1)) u_dq3_mux_p4_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p4[3*SWIDTH+:SWIDTH]),       .i_b(dq3_dfi_wrdata_p4     ),    .o_z(int_dq3_dfi_wrdata_p4      ));
   ddr_mux #(.DWIDTH(1)) u_dq3_mux_p4_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p4[3*MWIDTH+:MWIDTH]),  .i_b(dq3_dfi_wrdata_mask_p4),    .o_z(int_dq3_dfi_wrdata_mask_p4 ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p4_0              (.i_sel(buf_mode_sync), .i_a(i_dfi_parity_in_p4 ),                      .i_b(dfi_parity_in_p4  ),        .o_z(int_dfi_parity_in_p4  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p4_1              (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_cs_p4[1]),                  .i_b(dfi_wrdata_cs_p4[1]),        .o_z(int_dfi_wrdata_cs_p4 ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p4_2              (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_en_p4 ),                      .i_b(dfi_wrdata_en_p4  ),        .o_z(int_dfi_wrdata_en_p4  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p4_3              (.i_sel(buf_mode_sync), .i_a(i_dfi_wck_cs_p4[1]    ),                 .i_b(dfi_wck_cs_p4[1] ),        .o_z(int_dfi_wck_cs_p4  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p4_4              (.i_sel(buf_mode_sync), .i_a(i_dfi_wck_en_p4    ),                      .i_b(dfi_wck_en_p4     ),        .o_z(int_dfi_wck_en_p4     ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p4_5 [TWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wck_toggle_p4),                      .i_b(dfi_wck_toggle_p4 ),        .o_z(int_dfi_wck_toggle_p4 ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p4_6              (.i_sel(buf_mode_sync), .i_a(i_dfi_rddata_cs_p4[1] ),                      .i_b(dfi_rddata_cs_p4[1]  ),        .o_z(int_dfi_rddata_cs_p4  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p4_7              (.i_sel(buf_mode_sync), .i_a(i_dfi_rddata_en_p4 ),                      .i_b(dfi_rddata_en_p4  ),        .o_z(int_dfi_rddata_en_p4  ));
   ddr_mux #(.DWIDTH(1)) u_dq0_mux_p5_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p5[0*SWIDTH+:SWIDTH]),       .i_b(dq0_dfi_wrdata_p5     ),    .o_z(int_dq0_dfi_wrdata_p5      ));
   ddr_mux #(.DWIDTH(1)) u_dq0_mux_p5_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p5[0*MWIDTH+:MWIDTH]),  .i_b(dq0_dfi_wrdata_mask_p5),    .o_z(int_dq0_dfi_wrdata_mask_p5 ));
   ddr_mux #(.DWIDTH(1)) u_dq1_mux_p5_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p5[1*SWIDTH+:SWIDTH]),       .i_b(dq1_dfi_wrdata_p5     ),    .o_z(int_dq1_dfi_wrdata_p5      ));
   ddr_mux #(.DWIDTH(1)) u_dq1_mux_p5_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p5[1*MWIDTH+:MWIDTH]),  .i_b(dq1_dfi_wrdata_mask_p5),    .o_z(int_dq1_dfi_wrdata_mask_p5 ));
   ddr_mux #(.DWIDTH(1)) u_dq2_mux_p5_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p5[2*SWIDTH+:SWIDTH]),       .i_b(dq2_dfi_wrdata_p5     ),    .o_z(int_dq2_dfi_wrdata_p5      ));
   ddr_mux #(.DWIDTH(1)) u_dq2_mux_p5_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p5[2*MWIDTH+:MWIDTH]),  .i_b(dq2_dfi_wrdata_mask_p5),    .o_z(int_dq2_dfi_wrdata_mask_p5 ));
   ddr_mux #(.DWIDTH(1)) u_dq3_mux_p5_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p5[3*SWIDTH+:SWIDTH]),       .i_b(dq3_dfi_wrdata_p5     ),    .o_z(int_dq3_dfi_wrdata_p5      ));
   ddr_mux #(.DWIDTH(1)) u_dq3_mux_p5_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p5[3*MWIDTH+:MWIDTH]),  .i_b(dq3_dfi_wrdata_mask_p5),    .o_z(int_dq3_dfi_wrdata_mask_p5 ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p5_0              (.i_sel(buf_mode_sync), .i_a(i_dfi_parity_in_p5 ),                      .i_b(dfi_parity_in_p5  ),        .o_z(int_dfi_parity_in_p5  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p5_1              (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_cs_p5[1]),                  .i_b(dfi_wrdata_cs_p5[1]),        .o_z(int_dfi_wrdata_cs_p5 ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p5_2              (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_en_p5 ),                      .i_b(dfi_wrdata_en_p5  ),        .o_z(int_dfi_wrdata_en_p5  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p5_3              (.i_sel(buf_mode_sync), .i_a(i_dfi_wck_cs_p5[1]    ),                 .i_b(dfi_wck_cs_p5[1] ),        .o_z(int_dfi_wck_cs_p5  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p5_4              (.i_sel(buf_mode_sync), .i_a(i_dfi_wck_en_p5    ),                      .i_b(dfi_wck_en_p5     ),        .o_z(int_dfi_wck_en_p5     ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p5_5 [TWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wck_toggle_p5),                      .i_b(dfi_wck_toggle_p5 ),        .o_z(int_dfi_wck_toggle_p5 ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p5_6              (.i_sel(buf_mode_sync), .i_a(i_dfi_rddata_cs_p5[1] ),                      .i_b(dfi_rddata_cs_p5[1]  ),        .o_z(int_dfi_rddata_cs_p5  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p5_7              (.i_sel(buf_mode_sync), .i_a(i_dfi_rddata_en_p5 ),                      .i_b(dfi_rddata_en_p5  ),        .o_z(int_dfi_rddata_en_p5  ));
   ddr_mux #(.DWIDTH(1)) u_dq0_mux_p6_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p6[0*SWIDTH+:SWIDTH]),       .i_b(dq0_dfi_wrdata_p6     ),    .o_z(int_dq0_dfi_wrdata_p6      ));
   ddr_mux #(.DWIDTH(1)) u_dq0_mux_p6_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p6[0*MWIDTH+:MWIDTH]),  .i_b(dq0_dfi_wrdata_mask_p6),    .o_z(int_dq0_dfi_wrdata_mask_p6 ));
   ddr_mux #(.DWIDTH(1)) u_dq1_mux_p6_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p6[1*SWIDTH+:SWIDTH]),       .i_b(dq1_dfi_wrdata_p6     ),    .o_z(int_dq1_dfi_wrdata_p6      ));
   ddr_mux #(.DWIDTH(1)) u_dq1_mux_p6_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p6[1*MWIDTH+:MWIDTH]),  .i_b(dq1_dfi_wrdata_mask_p6),    .o_z(int_dq1_dfi_wrdata_mask_p6 ));
   ddr_mux #(.DWIDTH(1)) u_dq2_mux_p6_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p6[2*SWIDTH+:SWIDTH]),       .i_b(dq2_dfi_wrdata_p6     ),    .o_z(int_dq2_dfi_wrdata_p6      ));
   ddr_mux #(.DWIDTH(1)) u_dq2_mux_p6_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p6[2*MWIDTH+:MWIDTH]),  .i_b(dq2_dfi_wrdata_mask_p6),    .o_z(int_dq2_dfi_wrdata_mask_p6 ));
   ddr_mux #(.DWIDTH(1)) u_dq3_mux_p6_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p6[3*SWIDTH+:SWIDTH]),       .i_b(dq3_dfi_wrdata_p6     ),    .o_z(int_dq3_dfi_wrdata_p6      ));
   ddr_mux #(.DWIDTH(1)) u_dq3_mux_p6_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p6[3*MWIDTH+:MWIDTH]),  .i_b(dq3_dfi_wrdata_mask_p6),    .o_z(int_dq3_dfi_wrdata_mask_p6 ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p6_0              (.i_sel(buf_mode_sync), .i_a(i_dfi_parity_in_p6 ),                      .i_b(dfi_parity_in_p6  ),        .o_z(int_dfi_parity_in_p6  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p6_1              (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_cs_p6[1]),                  .i_b(dfi_wrdata_cs_p6[1]),        .o_z(int_dfi_wrdata_cs_p6 ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p6_2              (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_en_p6 ),                      .i_b(dfi_wrdata_en_p6  ),        .o_z(int_dfi_wrdata_en_p6  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p6_3              (.i_sel(buf_mode_sync), .i_a(i_dfi_wck_cs_p6[1]    ),                 .i_b(dfi_wck_cs_p6[1] ),        .o_z(int_dfi_wck_cs_p6  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p6_4              (.i_sel(buf_mode_sync), .i_a(i_dfi_wck_en_p6    ),                      .i_b(dfi_wck_en_p6     ),        .o_z(int_dfi_wck_en_p6     ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p6_5 [TWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wck_toggle_p6),                      .i_b(dfi_wck_toggle_p6 ),        .o_z(int_dfi_wck_toggle_p6 ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p6_6              (.i_sel(buf_mode_sync), .i_a(i_dfi_rddata_cs_p6[1] ),                      .i_b(dfi_rddata_cs_p6[1]  ),        .o_z(int_dfi_rddata_cs_p6  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p6_7              (.i_sel(buf_mode_sync), .i_a(i_dfi_rddata_en_p6 ),                      .i_b(dfi_rddata_en_p6  ),        .o_z(int_dfi_rddata_en_p6  ));
   ddr_mux #(.DWIDTH(1)) u_dq0_mux_p7_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p7[0*SWIDTH+:SWIDTH]),       .i_b(dq0_dfi_wrdata_p7     ),    .o_z(int_dq0_dfi_wrdata_p7      ));
   ddr_mux #(.DWIDTH(1)) u_dq0_mux_p7_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p7[0*MWIDTH+:MWIDTH]),  .i_b(dq0_dfi_wrdata_mask_p7),    .o_z(int_dq0_dfi_wrdata_mask_p7 ));
   ddr_mux #(.DWIDTH(1)) u_dq1_mux_p7_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p7[1*SWIDTH+:SWIDTH]),       .i_b(dq1_dfi_wrdata_p7     ),    .o_z(int_dq1_dfi_wrdata_p7      ));
   ddr_mux #(.DWIDTH(1)) u_dq1_mux_p7_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p7[1*MWIDTH+:MWIDTH]),  .i_b(dq1_dfi_wrdata_mask_p7),    .o_z(int_dq1_dfi_wrdata_mask_p7 ));
   ddr_mux #(.DWIDTH(1)) u_dq2_mux_p7_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p7[2*SWIDTH+:SWIDTH]),       .i_b(dq2_dfi_wrdata_p7     ),    .o_z(int_dq2_dfi_wrdata_p7      ));
   ddr_mux #(.DWIDTH(1)) u_dq2_mux_p7_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p7[2*MWIDTH+:MWIDTH]),  .i_b(dq2_dfi_wrdata_mask_p7),    .o_z(int_dq2_dfi_wrdata_mask_p7 ));
   ddr_mux #(.DWIDTH(1)) u_dq3_mux_p7_0 [SWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_p7[3*SWIDTH+:SWIDTH]),       .i_b(dq3_dfi_wrdata_p7     ),    .o_z(int_dq3_dfi_wrdata_p7      ));
   ddr_mux #(.DWIDTH(1)) u_dq3_mux_p7_1 [MWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_mask_p7[3*MWIDTH+:MWIDTH]),  .i_b(dq3_dfi_wrdata_mask_p7),    .o_z(int_dq3_dfi_wrdata_mask_p7 ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p7_0              (.i_sel(buf_mode_sync), .i_a(i_dfi_parity_in_p7 ),                      .i_b(dfi_parity_in_p7  ),        .o_z(int_dfi_parity_in_p7  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p7_1              (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_cs_p7[1]),                  .i_b(dfi_wrdata_cs_p7[1]),        .o_z(int_dfi_wrdata_cs_p7 ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p7_2              (.i_sel(buf_mode_sync), .i_a(i_dfi_wrdata_en_p7 ),                      .i_b(dfi_wrdata_en_p7  ),        .o_z(int_dfi_wrdata_en_p7  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p7_3              (.i_sel(buf_mode_sync), .i_a(i_dfi_wck_cs_p7[1]    ),                 .i_b(dfi_wck_cs_p7[1] ),        .o_z(int_dfi_wck_cs_p7  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p7_4              (.i_sel(buf_mode_sync), .i_a(i_dfi_wck_en_p7    ),                      .i_b(dfi_wck_en_p7     ),        .o_z(int_dfi_wck_en_p7     ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p7_5 [TWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_wck_toggle_p7),                      .i_b(dfi_wck_toggle_p7 ),        .o_z(int_dfi_wck_toggle_p7 ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p7_6              (.i_sel(buf_mode_sync), .i_a(i_dfi_rddata_cs_p7[1] ),                      .i_b(dfi_rddata_cs_p7[1]  ),        .o_z(int_dfi_rddata_cs_p7  ));
   ddr_mux #(.DWIDTH(1))  u_dq_mux_p7_7              (.i_sel(buf_mode_sync), .i_a(i_dfi_rddata_en_p7 ),                      .i_b(dfi_rddata_en_p7  ),        .o_z(int_dfi_rddata_en_p7  ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p0_0 [AWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_address_p0   ),                      .i_b(dfi_address_p0    ),        .o_z(int_dfi_address_p0    ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p0_1        [1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_cs_p0        ),                      .i_b(dfi_cs_p0         ),        .o_z(int_dfi_cs_p0         ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p0_2        [1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_cke_p0       ),                      .i_b(dfi_cke_p0        ),        .o_z(int_dfi_cke_p0        ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p0_3              (.i_sel(buf_mode_sync), .i_a(i_dfi_dcd_p0       ),                      .i_b(dfi_dcd_p0        ),        .o_z(int_dfi_dcd_p0        ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p1_0 [AWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_address_p1   ),                      .i_b(dfi_address_p1    ),        .o_z(int_dfi_address_p1    ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p1_1        [1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_cs_p1        ),                      .i_b(dfi_cs_p1         ),        .o_z(int_dfi_cs_p1         ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p1_2        [1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_cke_p1       ),                      .i_b(dfi_cke_p1        ),        .o_z(int_dfi_cke_p1        ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p1_3              (.i_sel(buf_mode_sync), .i_a(i_dfi_dcd_p1       ),                      .i_b(dfi_dcd_p1        ),        .o_z(int_dfi_dcd_p1        ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p2_0 [AWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_address_p2   ),                      .i_b(dfi_address_p2    ),        .o_z(int_dfi_address_p2    ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p2_1        [1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_cs_p2        ),                      .i_b(dfi_cs_p2         ),        .o_z(int_dfi_cs_p2         ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p2_2        [1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_cke_p2       ),                      .i_b(dfi_cke_p2        ),        .o_z(int_dfi_cke_p2        ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p2_3              (.i_sel(buf_mode_sync), .i_a(i_dfi_dcd_p2       ),                      .i_b(dfi_dcd_p2        ),        .o_z(int_dfi_dcd_p2        ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p3_0 [AWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_address_p3   ),                      .i_b(dfi_address_p3    ),        .o_z(int_dfi_address_p3    ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p3_1        [1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_cs_p3        ),                      .i_b(dfi_cs_p3         ),        .o_z(int_dfi_cs_p3         ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p3_2        [1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_cke_p3       ),                      .i_b(dfi_cke_p3        ),        .o_z(int_dfi_cke_p3        ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p3_3              (.i_sel(buf_mode_sync), .i_a(i_dfi_dcd_p3       ),                      .i_b(dfi_dcd_p3        ),        .o_z(int_dfi_dcd_p3        ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p4_0 [AWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_address_p4   ),                      .i_b(dfi_address_p4    ),        .o_z(int_dfi_address_p4    ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p4_1        [1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_cs_p4        ),                      .i_b(dfi_cs_p4         ),        .o_z(int_dfi_cs_p4         ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p4_2        [1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_cke_p4       ),                      .i_b(dfi_cke_p4        ),        .o_z(int_dfi_cke_p4        ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p4_3              (.i_sel(buf_mode_sync), .i_a(i_dfi_dcd_p4       ),                      .i_b(dfi_dcd_p4        ),        .o_z(int_dfi_dcd_p4        ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p5_0 [AWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_address_p5   ),                      .i_b(dfi_address_p5    ),        .o_z(int_dfi_address_p5    ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p5_1        [1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_cs_p5        ),                      .i_b(dfi_cs_p5         ),        .o_z(int_dfi_cs_p5         ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p5_2        [1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_cke_p5       ),                      .i_b(dfi_cke_p5        ),        .o_z(int_dfi_cke_p5        ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p5_3              (.i_sel(buf_mode_sync), .i_a(i_dfi_dcd_p5       ),                      .i_b(dfi_dcd_p5        ),        .o_z(int_dfi_dcd_p5        ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p6_0 [AWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_address_p6   ),                      .i_b(dfi_address_p6    ),        .o_z(int_dfi_address_p6    ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p6_1        [1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_cs_p6        ),                      .i_b(dfi_cs_p6         ),        .o_z(int_dfi_cs_p6         ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p6_2        [1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_cke_p6       ),                      .i_b(dfi_cke_p6        ),        .o_z(int_dfi_cke_p6        ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p6_3              (.i_sel(buf_mode_sync), .i_a(i_dfi_dcd_p6       ),                      .i_b(dfi_dcd_p6        ),        .o_z(int_dfi_dcd_p6        ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p7_0 [AWIDTH-1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_address_p7   ),                      .i_b(dfi_address_p7    ),        .o_z(int_dfi_address_p7    ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p7_1        [1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_cs_p7        ),                      .i_b(dfi_cs_p7         ),        .o_z(int_dfi_cs_p7         ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p7_2        [1:0] (.i_sel(buf_mode_sync), .i_a(i_dfi_cke_p7       ),                      .i_b(dfi_cke_p7        ),        .o_z(int_dfi_cke_p7        ));
   ddr_mux #(.DWIDTH(1))  u_ca_mux_p7_3              (.i_sel(buf_mode_sync), .i_a(i_dfi_dcd_p7       ),                      .i_b(dfi_dcd_p7        ),        .o_z(int_dfi_dcd_p7        ));

   // ------------------------------------------------------------------------
   // Read Mux
   // ------------------------------------------------------------------------

   ddr_mux #(.DWIDTH(1)) u_dq0_rd_mux_p0_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq0_dfi_rddata_w0     ),   .o_z(o_dq0_dfi_rddata_w0    ));
   ddr_mux #(.DWIDTH(1)) u_dq0_rd_mux_p0_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq0_dfi_rddata_dbi_w0 ),   .o_z(o_dq0_dfi_rddata_dbi_w0));
   ddr_mux #(.DWIDTH(1)) u_dq1_rd_mux_p0_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq1_dfi_rddata_w0     ),   .o_z(o_dq1_dfi_rddata_w0    ));
   ddr_mux #(.DWIDTH(1)) u_dq1_rd_mux_p0_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq1_dfi_rddata_dbi_w0 ),   .o_z(o_dq1_dfi_rddata_dbi_w0));
   ddr_mux #(.DWIDTH(1)) u_dq2_rd_mux_p0_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq2_dfi_rddata_w0     ),   .o_z(o_dq2_dfi_rddata_w0    ));
   ddr_mux #(.DWIDTH(1)) u_dq2_rd_mux_p0_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq2_dfi_rddata_dbi_w0 ),   .o_z(o_dq2_dfi_rddata_dbi_w0));
   ddr_mux #(.DWIDTH(1)) u_dq3_rd_mux_p0_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq3_dfi_rddata_w0     ),   .o_z(o_dq3_dfi_rddata_w0    ));
   ddr_mux #(.DWIDTH(1)) u_dq3_rd_mux_p0_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq3_dfi_rddata_dbi_w0 ),   .o_z(o_dq3_dfi_rddata_dbi_w0));
   ddr_mux #(.DWIDTH(1)) u_rdvld_mux_w0                   (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq0_dfi_rddata_valid_w0),    .o_z(o_dfi_rddata_valid_w0     ));
   ddr_mux #(.DWIDTH(1)) u_dq0_rd_mux_p1_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq0_dfi_rddata_w1     ),   .o_z(o_dq0_dfi_rddata_w1    ));
   ddr_mux #(.DWIDTH(1)) u_dq0_rd_mux_p1_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq0_dfi_rddata_dbi_w1 ),   .o_z(o_dq0_dfi_rddata_dbi_w1));
   ddr_mux #(.DWIDTH(1)) u_dq1_rd_mux_p1_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq1_dfi_rddata_w1     ),   .o_z(o_dq1_dfi_rddata_w1    ));
   ddr_mux #(.DWIDTH(1)) u_dq1_rd_mux_p1_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq1_dfi_rddata_dbi_w1 ),   .o_z(o_dq1_dfi_rddata_dbi_w1));
   ddr_mux #(.DWIDTH(1)) u_dq2_rd_mux_p1_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq2_dfi_rddata_w1     ),   .o_z(o_dq2_dfi_rddata_w1    ));
   ddr_mux #(.DWIDTH(1)) u_dq2_rd_mux_p1_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq2_dfi_rddata_dbi_w1 ),   .o_z(o_dq2_dfi_rddata_dbi_w1));
   ddr_mux #(.DWIDTH(1)) u_dq3_rd_mux_p1_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq3_dfi_rddata_w1     ),   .o_z(o_dq3_dfi_rddata_w1    ));
   ddr_mux #(.DWIDTH(1)) u_dq3_rd_mux_p1_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq3_dfi_rddata_dbi_w1 ),   .o_z(o_dq3_dfi_rddata_dbi_w1));
   ddr_mux #(.DWIDTH(1)) u_rdvld_mux_w1                   (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq0_dfi_rddata_valid_w1),    .o_z(o_dfi_rddata_valid_w1     ));
   ddr_mux #(.DWIDTH(1)) u_dq0_rd_mux_p2_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq0_dfi_rddata_w2     ),   .o_z(o_dq0_dfi_rddata_w2    ));
   ddr_mux #(.DWIDTH(1)) u_dq0_rd_mux_p2_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq0_dfi_rddata_dbi_w2 ),   .o_z(o_dq0_dfi_rddata_dbi_w2));
   ddr_mux #(.DWIDTH(1)) u_dq1_rd_mux_p2_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq1_dfi_rddata_w2     ),   .o_z(o_dq1_dfi_rddata_w2    ));
   ddr_mux #(.DWIDTH(1)) u_dq1_rd_mux_p2_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq1_dfi_rddata_dbi_w2 ),   .o_z(o_dq1_dfi_rddata_dbi_w2));
   ddr_mux #(.DWIDTH(1)) u_dq2_rd_mux_p2_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq2_dfi_rddata_w2     ),   .o_z(o_dq2_dfi_rddata_w2    ));
   ddr_mux #(.DWIDTH(1)) u_dq2_rd_mux_p2_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq2_dfi_rddata_dbi_w2 ),   .o_z(o_dq2_dfi_rddata_dbi_w2));
   ddr_mux #(.DWIDTH(1)) u_dq3_rd_mux_p2_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq3_dfi_rddata_w2     ),   .o_z(o_dq3_dfi_rddata_w2    ));
   ddr_mux #(.DWIDTH(1)) u_dq3_rd_mux_p2_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq3_dfi_rddata_dbi_w2 ),   .o_z(o_dq3_dfi_rddata_dbi_w2));
   ddr_mux #(.DWIDTH(1)) u_rdvld_mux_w2                   (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq0_dfi_rddata_valid_w2),    .o_z(o_dfi_rddata_valid_w2     ));
   ddr_mux #(.DWIDTH(1)) u_dq0_rd_mux_p3_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq0_dfi_rddata_w3     ),   .o_z(o_dq0_dfi_rddata_w3    ));
   ddr_mux #(.DWIDTH(1)) u_dq0_rd_mux_p3_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq0_dfi_rddata_dbi_w3 ),   .o_z(o_dq0_dfi_rddata_dbi_w3));
   ddr_mux #(.DWIDTH(1)) u_dq1_rd_mux_p3_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq1_dfi_rddata_w3     ),   .o_z(o_dq1_dfi_rddata_w3    ));
   ddr_mux #(.DWIDTH(1)) u_dq1_rd_mux_p3_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq1_dfi_rddata_dbi_w3 ),   .o_z(o_dq1_dfi_rddata_dbi_w3));
   ddr_mux #(.DWIDTH(1)) u_dq2_rd_mux_p3_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq2_dfi_rddata_w3     ),   .o_z(o_dq2_dfi_rddata_w3    ));
   ddr_mux #(.DWIDTH(1)) u_dq2_rd_mux_p3_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq2_dfi_rddata_dbi_w3 ),   .o_z(o_dq2_dfi_rddata_dbi_w3));
   ddr_mux #(.DWIDTH(1)) u_dq3_rd_mux_p3_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq3_dfi_rddata_w3     ),   .o_z(o_dq3_dfi_rddata_w3    ));
   ddr_mux #(.DWIDTH(1)) u_dq3_rd_mux_p3_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq3_dfi_rddata_dbi_w3 ),   .o_z(o_dq3_dfi_rddata_dbi_w3));
   ddr_mux #(.DWIDTH(1)) u_rdvld_mux_w3                   (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq0_dfi_rddata_valid_w3),    .o_z(o_dfi_rddata_valid_w3     ));
   ddr_mux #(.DWIDTH(1)) u_dq0_rd_mux_p4_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq0_dfi_rddata_w4     ),   .o_z(o_dq0_dfi_rddata_w4    ));
   ddr_mux #(.DWIDTH(1)) u_dq0_rd_mux_p4_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq0_dfi_rddata_dbi_w4 ),   .o_z(o_dq0_dfi_rddata_dbi_w4));
   ddr_mux #(.DWIDTH(1)) u_dq1_rd_mux_p4_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq1_dfi_rddata_w4     ),   .o_z(o_dq1_dfi_rddata_w4    ));
   ddr_mux #(.DWIDTH(1)) u_dq1_rd_mux_p4_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq1_dfi_rddata_dbi_w4 ),   .o_z(o_dq1_dfi_rddata_dbi_w4));
   ddr_mux #(.DWIDTH(1)) u_dq2_rd_mux_p4_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq2_dfi_rddata_w4     ),   .o_z(o_dq2_dfi_rddata_w4    ));
   ddr_mux #(.DWIDTH(1)) u_dq2_rd_mux_p4_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq2_dfi_rddata_dbi_w4 ),   .o_z(o_dq2_dfi_rddata_dbi_w4));
   ddr_mux #(.DWIDTH(1)) u_dq3_rd_mux_p4_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq3_dfi_rddata_w4     ),   .o_z(o_dq3_dfi_rddata_w4    ));
   ddr_mux #(.DWIDTH(1)) u_dq3_rd_mux_p4_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq3_dfi_rddata_dbi_w4 ),   .o_z(o_dq3_dfi_rddata_dbi_w4));
   ddr_mux #(.DWIDTH(1)) u_rdvld_mux_w4                   (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq0_dfi_rddata_valid_w4),    .o_z(o_dfi_rddata_valid_w4     ));
   ddr_mux #(.DWIDTH(1)) u_dq0_rd_mux_p5_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq0_dfi_rddata_w5     ),   .o_z(o_dq0_dfi_rddata_w5    ));
   ddr_mux #(.DWIDTH(1)) u_dq0_rd_mux_p5_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq0_dfi_rddata_dbi_w5 ),   .o_z(o_dq0_dfi_rddata_dbi_w5));
   ddr_mux #(.DWIDTH(1)) u_dq1_rd_mux_p5_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq1_dfi_rddata_w5     ),   .o_z(o_dq1_dfi_rddata_w5    ));
   ddr_mux #(.DWIDTH(1)) u_dq1_rd_mux_p5_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq1_dfi_rddata_dbi_w5 ),   .o_z(o_dq1_dfi_rddata_dbi_w5));
   ddr_mux #(.DWIDTH(1)) u_dq2_rd_mux_p5_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq2_dfi_rddata_w5     ),   .o_z(o_dq2_dfi_rddata_w5    ));
   ddr_mux #(.DWIDTH(1)) u_dq2_rd_mux_p5_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq2_dfi_rddata_dbi_w5 ),   .o_z(o_dq2_dfi_rddata_dbi_w5));
   ddr_mux #(.DWIDTH(1)) u_dq3_rd_mux_p5_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq3_dfi_rddata_w5     ),   .o_z(o_dq3_dfi_rddata_w5    ));
   ddr_mux #(.DWIDTH(1)) u_dq3_rd_mux_p5_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq3_dfi_rddata_dbi_w5 ),   .o_z(o_dq3_dfi_rddata_dbi_w5));
   ddr_mux #(.DWIDTH(1)) u_rdvld_mux_w5                   (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq0_dfi_rddata_valid_w5),    .o_z(o_dfi_rddata_valid_w5     ));
   ddr_mux #(.DWIDTH(1)) u_dq0_rd_mux_p6_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq0_dfi_rddata_w6     ),   .o_z(o_dq0_dfi_rddata_w6    ));
   ddr_mux #(.DWIDTH(1)) u_dq0_rd_mux_p6_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq0_dfi_rddata_dbi_w6 ),   .o_z(o_dq0_dfi_rddata_dbi_w6));
   ddr_mux #(.DWIDTH(1)) u_dq1_rd_mux_p6_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq1_dfi_rddata_w6     ),   .o_z(o_dq1_dfi_rddata_w6    ));
   ddr_mux #(.DWIDTH(1)) u_dq1_rd_mux_p6_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq1_dfi_rddata_dbi_w6 ),   .o_z(o_dq1_dfi_rddata_dbi_w6));
   ddr_mux #(.DWIDTH(1)) u_dq2_rd_mux_p6_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq2_dfi_rddata_w6     ),   .o_z(o_dq2_dfi_rddata_w6    ));
   ddr_mux #(.DWIDTH(1)) u_dq2_rd_mux_p6_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq2_dfi_rddata_dbi_w6 ),   .o_z(o_dq2_dfi_rddata_dbi_w6));
   ddr_mux #(.DWIDTH(1)) u_dq3_rd_mux_p6_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq3_dfi_rddata_w6     ),   .o_z(o_dq3_dfi_rddata_w6    ));
   ddr_mux #(.DWIDTH(1)) u_dq3_rd_mux_p6_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq3_dfi_rddata_dbi_w6 ),   .o_z(o_dq3_dfi_rddata_dbi_w6));
   ddr_mux #(.DWIDTH(1)) u_rdvld_mux_w6                   (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq0_dfi_rddata_valid_w6),    .o_z(o_dfi_rddata_valid_w6     ));
   ddr_mux #(.DWIDTH(1)) u_dq0_rd_mux_p7_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq0_dfi_rddata_w7     ),   .o_z(o_dq0_dfi_rddata_w7    ));
   ddr_mux #(.DWIDTH(1)) u_dq0_rd_mux_p7_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq0_dfi_rddata_dbi_w7 ),   .o_z(o_dq0_dfi_rddata_dbi_w7));
   ddr_mux #(.DWIDTH(1)) u_dq1_rd_mux_p7_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq1_dfi_rddata_w7     ),   .o_z(o_dq1_dfi_rddata_w7    ));
   ddr_mux #(.DWIDTH(1)) u_dq1_rd_mux_p7_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq1_dfi_rddata_dbi_w7 ),   .o_z(o_dq1_dfi_rddata_dbi_w7));
   ddr_mux #(.DWIDTH(1)) u_dq2_rd_mux_p7_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq2_dfi_rddata_w7     ),   .o_z(o_dq2_dfi_rddata_w7    ));
   ddr_mux #(.DWIDTH(1)) u_dq2_rd_mux_p7_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq2_dfi_rddata_dbi_w7 ),   .o_z(o_dq2_dfi_rddata_dbi_w7));
   ddr_mux #(.DWIDTH(1)) u_dq3_rd_mux_p7_0 [SWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq3_dfi_rddata_w7     ),   .o_z(o_dq3_dfi_rddata_w7    ));
   ddr_mux #(.DWIDTH(1)) u_dq3_rd_mux_p7_1 [MWIDTH-1:0] (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq3_dfi_rddata_dbi_w7 ),   .o_z(o_dq3_dfi_rddata_dbi_w7));
   ddr_mux #(.DWIDTH(1)) u_rdvld_mux_w7                   (.i_sel(i_dfi_rdout_en), .i_a('0),   .i_b(i_dq0_dfi_rddata_valid_w7),    .o_z(o_dfi_rddata_valid_w7     ));

   // ------------------------------------------------------------------------
   // Pipeline to Isolate from Interface
   // ------------------------------------------------------------------------
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p0_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq0_dfi_wrdata_p0      ), .o_q(o_ch0_dq0_dfi_wrdata_p0      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p0_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq0_dfi_wrdata_mask_p0 ), .o_q(o_ch0_dq0_dfi_wrdata_mask_p0 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p0_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p0       ), .o_q(o_ch0_dq0_dfi_parity_in_p0       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p0_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p0       ), .o_q(o_ch0_dq0_dfi_wrdata_cs_p0       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p0_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p0       ), .o_q(o_ch0_dq0_dfi_wrdata_en_p0       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p0_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p0          ), .o_q(o_ch0_dq0_dfi_wck_cs_p0          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p0_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p0          ), .o_q(o_ch0_dq0_dfi_wck_en_p0          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p0_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p0      ), .o_q(o_ch0_dq0_dfi_wck_toggle_p0      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p0_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p0       ), .o_q(o_ch0_dq0_dfi_rddata_cs_p0       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p0_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p0       ), .o_q(o_ch0_dq0_dfi_rddata_en_p0       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p0_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq1_dfi_wrdata_p0      ), .o_q(o_ch0_dq1_dfi_wrdata_p0      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p0_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq1_dfi_wrdata_mask_p0 ), .o_q(o_ch0_dq1_dfi_wrdata_mask_p0 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p0_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p0       ), .o_q(o_ch0_dq1_dfi_parity_in_p0       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p0_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p0       ), .o_q(o_ch0_dq1_dfi_wrdata_cs_p0       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p0_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p0       ), .o_q(o_ch0_dq1_dfi_wrdata_en_p0       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p0_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p0          ), .o_q(o_ch0_dq1_dfi_wck_cs_p0          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p0_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p0          ), .o_q(o_ch0_dq1_dfi_wck_en_p0          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p0_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p0      ), .o_q(o_ch0_dq1_dfi_wck_toggle_p0      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p0_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p0       ), .o_q(o_ch0_dq1_dfi_rddata_cs_p0       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p0_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p0       ), .o_q(o_ch0_dq1_dfi_rddata_en_p0       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p1_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq0_dfi_wrdata_p1      ), .o_q(o_ch0_dq0_dfi_wrdata_p1      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p1_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq0_dfi_wrdata_mask_p1 ), .o_q(o_ch0_dq0_dfi_wrdata_mask_p1 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p1_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p1       ), .o_q(o_ch0_dq0_dfi_parity_in_p1       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p1_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p1       ), .o_q(o_ch0_dq0_dfi_wrdata_cs_p1       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p1_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p1       ), .o_q(o_ch0_dq0_dfi_wrdata_en_p1       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p1_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p1          ), .o_q(o_ch0_dq0_dfi_wck_cs_p1          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p1_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p1          ), .o_q(o_ch0_dq0_dfi_wck_en_p1          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p1_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p1      ), .o_q(o_ch0_dq0_dfi_wck_toggle_p1      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p1_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p1       ), .o_q(o_ch0_dq0_dfi_rddata_cs_p1       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p1_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p1       ), .o_q(o_ch0_dq0_dfi_rddata_en_p1       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p1_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq1_dfi_wrdata_p1      ), .o_q(o_ch0_dq1_dfi_wrdata_p1      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p1_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq1_dfi_wrdata_mask_p1 ), .o_q(o_ch0_dq1_dfi_wrdata_mask_p1 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p1_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p1       ), .o_q(o_ch0_dq1_dfi_parity_in_p1       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p1_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p1       ), .o_q(o_ch0_dq1_dfi_wrdata_cs_p1       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p1_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p1       ), .o_q(o_ch0_dq1_dfi_wrdata_en_p1       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p1_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p1          ), .o_q(o_ch0_dq1_dfi_wck_cs_p1          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p1_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p1          ), .o_q(o_ch0_dq1_dfi_wck_en_p1          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p1_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p1      ), .o_q(o_ch0_dq1_dfi_wck_toggle_p1      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p1_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p1       ), .o_q(o_ch0_dq1_dfi_rddata_cs_p1       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p1_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p1       ), .o_q(o_ch0_dq1_dfi_rddata_en_p1       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p2_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq0_dfi_wrdata_p2      ), .o_q(o_ch0_dq0_dfi_wrdata_p2      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p2_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq0_dfi_wrdata_mask_p2 ), .o_q(o_ch0_dq0_dfi_wrdata_mask_p2 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p2_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p2       ), .o_q(o_ch0_dq0_dfi_parity_in_p2       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p2_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p2       ), .o_q(o_ch0_dq0_dfi_wrdata_cs_p2       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p2_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p2       ), .o_q(o_ch0_dq0_dfi_wrdata_en_p2       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p2_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p2          ), .o_q(o_ch0_dq0_dfi_wck_cs_p2          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p2_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p2          ), .o_q(o_ch0_dq0_dfi_wck_en_p2          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p2_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p2      ), .o_q(o_ch0_dq0_dfi_wck_toggle_p2      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p2_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p2       ), .o_q(o_ch0_dq0_dfi_rddata_cs_p2       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p2_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p2       ), .o_q(o_ch0_dq0_dfi_rddata_en_p2       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p2_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq1_dfi_wrdata_p2      ), .o_q(o_ch0_dq1_dfi_wrdata_p2      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p2_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq1_dfi_wrdata_mask_p2 ), .o_q(o_ch0_dq1_dfi_wrdata_mask_p2 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p2_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p2       ), .o_q(o_ch0_dq1_dfi_parity_in_p2       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p2_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p2       ), .o_q(o_ch0_dq1_dfi_wrdata_cs_p2       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p2_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p2       ), .o_q(o_ch0_dq1_dfi_wrdata_en_p2       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p2_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p2          ), .o_q(o_ch0_dq1_dfi_wck_cs_p2          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p2_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p2          ), .o_q(o_ch0_dq1_dfi_wck_en_p2          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p2_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p2      ), .o_q(o_ch0_dq1_dfi_wck_toggle_p2      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p2_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p2       ), .o_q(o_ch0_dq1_dfi_rddata_cs_p2       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p2_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p2       ), .o_q(o_ch0_dq1_dfi_rddata_en_p2       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p3_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq0_dfi_wrdata_p3      ), .o_q(o_ch0_dq0_dfi_wrdata_p3      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p3_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq0_dfi_wrdata_mask_p3 ), .o_q(o_ch0_dq0_dfi_wrdata_mask_p3 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p3_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p3       ), .o_q(o_ch0_dq0_dfi_parity_in_p3       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p3_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p3       ), .o_q(o_ch0_dq0_dfi_wrdata_cs_p3       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p3_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p3       ), .o_q(o_ch0_dq0_dfi_wrdata_en_p3       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p3_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p3          ), .o_q(o_ch0_dq0_dfi_wck_cs_p3          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p3_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p3          ), .o_q(o_ch0_dq0_dfi_wck_en_p3          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p3_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p3      ), .o_q(o_ch0_dq0_dfi_wck_toggle_p3      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p3_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p3       ), .o_q(o_ch0_dq0_dfi_rddata_cs_p3       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p3_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p3       ), .o_q(o_ch0_dq0_dfi_rddata_en_p3       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p3_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq1_dfi_wrdata_p3      ), .o_q(o_ch0_dq1_dfi_wrdata_p3      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p3_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq1_dfi_wrdata_mask_p3 ), .o_q(o_ch0_dq1_dfi_wrdata_mask_p3 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p3_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p3       ), .o_q(o_ch0_dq1_dfi_parity_in_p3       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p3_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p3       ), .o_q(o_ch0_dq1_dfi_wrdata_cs_p3       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p3_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p3       ), .o_q(o_ch0_dq1_dfi_wrdata_en_p3       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p3_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p3          ), .o_q(o_ch0_dq1_dfi_wck_cs_p3          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p3_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p3          ), .o_q(o_ch0_dq1_dfi_wck_en_p3          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p3_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p3      ), .o_q(o_ch0_dq1_dfi_wck_toggle_p3      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p3_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p3       ), .o_q(o_ch0_dq1_dfi_rddata_cs_p3       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p3_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p3       ), .o_q(o_ch0_dq1_dfi_rddata_en_p3       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p4_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq0_dfi_wrdata_p4      ), .o_q(o_ch0_dq0_dfi_wrdata_p4      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p4_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq0_dfi_wrdata_mask_p4 ), .o_q(o_ch0_dq0_dfi_wrdata_mask_p4 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p4_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p4       ), .o_q(o_ch0_dq0_dfi_parity_in_p4       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p4_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p4       ), .o_q(o_ch0_dq0_dfi_wrdata_cs_p4       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p4_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p4       ), .o_q(o_ch0_dq0_dfi_wrdata_en_p4       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p4_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p4          ), .o_q(o_ch0_dq0_dfi_wck_cs_p4          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p4_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p4          ), .o_q(o_ch0_dq0_dfi_wck_en_p4          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p4_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p4      ), .o_q(o_ch0_dq0_dfi_wck_toggle_p4      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p4_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p4       ), .o_q(o_ch0_dq0_dfi_rddata_cs_p4       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p4_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p4       ), .o_q(o_ch0_dq0_dfi_rddata_en_p4       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p4_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq1_dfi_wrdata_p4      ), .o_q(o_ch0_dq1_dfi_wrdata_p4      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p4_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq1_dfi_wrdata_mask_p4 ), .o_q(o_ch0_dq1_dfi_wrdata_mask_p4 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p4_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p4       ), .o_q(o_ch0_dq1_dfi_parity_in_p4       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p4_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p4       ), .o_q(o_ch0_dq1_dfi_wrdata_cs_p4       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p4_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p4       ), .o_q(o_ch0_dq1_dfi_wrdata_en_p4       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p4_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p4          ), .o_q(o_ch0_dq1_dfi_wck_cs_p4          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p4_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p4          ), .o_q(o_ch0_dq1_dfi_wck_en_p4          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p4_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p4      ), .o_q(o_ch0_dq1_dfi_wck_toggle_p4      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p4_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p4       ), .o_q(o_ch0_dq1_dfi_rddata_cs_p4       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p4_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p4       ), .o_q(o_ch0_dq1_dfi_rddata_en_p4       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p5_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq0_dfi_wrdata_p5      ), .o_q(o_ch0_dq0_dfi_wrdata_p5      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p5_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq0_dfi_wrdata_mask_p5 ), .o_q(o_ch0_dq0_dfi_wrdata_mask_p5 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p5_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p5       ), .o_q(o_ch0_dq0_dfi_parity_in_p5       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p5_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p5       ), .o_q(o_ch0_dq0_dfi_wrdata_cs_p5       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p5_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p5       ), .o_q(o_ch0_dq0_dfi_wrdata_en_p5       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p5_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p5          ), .o_q(o_ch0_dq0_dfi_wck_cs_p5          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p5_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p5          ), .o_q(o_ch0_dq0_dfi_wck_en_p5          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p5_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p5      ), .o_q(o_ch0_dq0_dfi_wck_toggle_p5      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p5_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p5       ), .o_q(o_ch0_dq0_dfi_rddata_cs_p5       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p5_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p5       ), .o_q(o_ch0_dq0_dfi_rddata_en_p5       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p5_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq1_dfi_wrdata_p5      ), .o_q(o_ch0_dq1_dfi_wrdata_p5      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p5_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq1_dfi_wrdata_mask_p5 ), .o_q(o_ch0_dq1_dfi_wrdata_mask_p5 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p5_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p5       ), .o_q(o_ch0_dq1_dfi_parity_in_p5       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p5_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p5       ), .o_q(o_ch0_dq1_dfi_wrdata_cs_p5       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p5_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p5       ), .o_q(o_ch0_dq1_dfi_wrdata_en_p5       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p5_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p5          ), .o_q(o_ch0_dq1_dfi_wck_cs_p5          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p5_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p5          ), .o_q(o_ch0_dq1_dfi_wck_en_p5          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p5_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p5      ), .o_q(o_ch0_dq1_dfi_wck_toggle_p5      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p5_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p5       ), .o_q(o_ch0_dq1_dfi_rddata_cs_p5       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p5_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p5       ), .o_q(o_ch0_dq1_dfi_rddata_en_p5       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p6_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq0_dfi_wrdata_p6      ), .o_q(o_ch0_dq0_dfi_wrdata_p6      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p6_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq0_dfi_wrdata_mask_p6 ), .o_q(o_ch0_dq0_dfi_wrdata_mask_p6 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p6_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p6       ), .o_q(o_ch0_dq0_dfi_parity_in_p6       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p6_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p6       ), .o_q(o_ch0_dq0_dfi_wrdata_cs_p6       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p6_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p6       ), .o_q(o_ch0_dq0_dfi_wrdata_en_p6       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p6_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p6          ), .o_q(o_ch0_dq0_dfi_wck_cs_p6          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p6_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p6          ), .o_q(o_ch0_dq0_dfi_wck_en_p6          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p6_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p6      ), .o_q(o_ch0_dq0_dfi_wck_toggle_p6      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p6_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p6       ), .o_q(o_ch0_dq0_dfi_rddata_cs_p6       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p6_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p6       ), .o_q(o_ch0_dq0_dfi_rddata_en_p6       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p6_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq1_dfi_wrdata_p6      ), .o_q(o_ch0_dq1_dfi_wrdata_p6      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p6_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq1_dfi_wrdata_mask_p6 ), .o_q(o_ch0_dq1_dfi_wrdata_mask_p6 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p6_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p6       ), .o_q(o_ch0_dq1_dfi_parity_in_p6       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p6_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p6       ), .o_q(o_ch0_dq1_dfi_wrdata_cs_p6       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p6_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p6       ), .o_q(o_ch0_dq1_dfi_wrdata_en_p6       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p6_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p6          ), .o_q(o_ch0_dq1_dfi_wck_cs_p6          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p6_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p6          ), .o_q(o_ch0_dq1_dfi_wck_en_p6          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p6_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p6      ), .o_q(o_ch0_dq1_dfi_wck_toggle_p6      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p6_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p6       ), .o_q(o_ch0_dq1_dfi_rddata_cs_p6       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p6_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p6       ), .o_q(o_ch0_dq1_dfi_rddata_en_p6       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p7_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq0_dfi_wrdata_p7      ), .o_q(o_ch0_dq0_dfi_wrdata_p7      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p7_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq0_dfi_wrdata_mask_p7 ), .o_q(o_ch0_dq0_dfi_wrdata_mask_p7 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p7_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p7       ), .o_q(o_ch0_dq0_dfi_parity_in_p7       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p7_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p7       ), .o_q(o_ch0_dq0_dfi_wrdata_cs_p7       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p7_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p7       ), .o_q(o_ch0_dq0_dfi_wrdata_en_p7       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p7_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p7          ), .o_q(o_ch0_dq0_dfi_wck_cs_p7          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p7_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p7          ), .o_q(o_ch0_dq0_dfi_wck_en_p7          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p7_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p7      ), .o_q(o_ch0_dq0_dfi_wck_toggle_p7      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p7_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p7       ), .o_q(o_ch0_dq0_dfi_rddata_cs_p7       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq0_pipe_p7_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p7       ), .o_q(o_ch0_dq0_dfi_rddata_en_p7       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p7_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq1_dfi_wrdata_p7      ), .o_q(o_ch0_dq1_dfi_wrdata_p7      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p7_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq1_dfi_wrdata_mask_p7 ), .o_q(o_ch0_dq1_dfi_wrdata_mask_p7 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p7_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p7       ), .o_q(o_ch0_dq1_dfi_parity_in_p7       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p7_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p7       ), .o_q(o_ch0_dq1_dfi_wrdata_cs_p7       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p7_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p7       ), .o_q(o_ch0_dq1_dfi_wrdata_en_p7       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p7_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p7          ), .o_q(o_ch0_dq1_dfi_wck_cs_p7          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p7_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p7          ), .o_q(o_ch0_dq1_dfi_wck_en_p7          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p7_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p7      ), .o_q(o_ch0_dq1_dfi_wck_toggle_p7      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p7_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p7       ), .o_q(o_ch0_dq1_dfi_rddata_cs_p7       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch0_dq1_pipe_p7_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p7       ), .o_q(o_ch0_dq1_dfi_rddata_en_p7       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p0_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq2_dfi_wrdata_p0      ), .o_q(o_ch1_dq0_dfi_wrdata_p0      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p0_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq2_dfi_wrdata_mask_p0 ), .o_q(o_ch1_dq0_dfi_wrdata_mask_p0 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p0_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p0       ), .o_q(o_ch1_dq0_dfi_parity_in_p0       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p0_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p0       ), .o_q(o_ch1_dq0_dfi_wrdata_cs_p0       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p0_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p0       ), .o_q(o_ch1_dq0_dfi_wrdata_en_p0       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p0_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p0          ), .o_q(o_ch1_dq0_dfi_wck_cs_p0          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p0_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p0          ), .o_q(o_ch1_dq0_dfi_wck_en_p0          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p0_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p0      ), .o_q(o_ch1_dq0_dfi_wck_toggle_p0      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p0_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p0       ), .o_q(o_ch1_dq0_dfi_rddata_cs_p0       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p0_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p0       ), .o_q(o_ch1_dq0_dfi_rddata_en_p0       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p0_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq3_dfi_wrdata_p0      ), .o_q(o_ch1_dq1_dfi_wrdata_p0      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p0_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq3_dfi_wrdata_mask_p0 ), .o_q(o_ch1_dq1_dfi_wrdata_mask_p0 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p0_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p0       ), .o_q(o_ch1_dq1_dfi_parity_in_p0       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p0_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p0       ), .o_q(o_ch1_dq1_dfi_wrdata_cs_p0       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p0_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p0       ), .o_q(o_ch1_dq1_dfi_wrdata_en_p0       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p0_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p0          ), .o_q(o_ch1_dq1_dfi_wck_cs_p0          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p0_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p0          ), .o_q(o_ch1_dq1_dfi_wck_en_p0          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p0_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p0      ), .o_q(o_ch1_dq1_dfi_wck_toggle_p0      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p0_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p0       ), .o_q(o_ch1_dq1_dfi_rddata_cs_p0       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p0_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p0       ), .o_q(o_ch1_dq1_dfi_rddata_en_p0       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p1_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq2_dfi_wrdata_p1      ), .o_q(o_ch1_dq0_dfi_wrdata_p1      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p1_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq2_dfi_wrdata_mask_p1 ), .o_q(o_ch1_dq0_dfi_wrdata_mask_p1 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p1_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p1       ), .o_q(o_ch1_dq0_dfi_parity_in_p1       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p1_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p1       ), .o_q(o_ch1_dq0_dfi_wrdata_cs_p1       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p1_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p1       ), .o_q(o_ch1_dq0_dfi_wrdata_en_p1       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p1_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p1          ), .o_q(o_ch1_dq0_dfi_wck_cs_p1          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p1_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p1          ), .o_q(o_ch1_dq0_dfi_wck_en_p1          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p1_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p1      ), .o_q(o_ch1_dq0_dfi_wck_toggle_p1      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p1_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p1       ), .o_q(o_ch1_dq0_dfi_rddata_cs_p1       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p1_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p1       ), .o_q(o_ch1_dq0_dfi_rddata_en_p1       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p1_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq3_dfi_wrdata_p1      ), .o_q(o_ch1_dq1_dfi_wrdata_p1      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p1_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq3_dfi_wrdata_mask_p1 ), .o_q(o_ch1_dq1_dfi_wrdata_mask_p1 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p1_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p1       ), .o_q(o_ch1_dq1_dfi_parity_in_p1       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p1_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p1       ), .o_q(o_ch1_dq1_dfi_wrdata_cs_p1       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p1_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p1       ), .o_q(o_ch1_dq1_dfi_wrdata_en_p1       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p1_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p1          ), .o_q(o_ch1_dq1_dfi_wck_cs_p1          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p1_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p1          ), .o_q(o_ch1_dq1_dfi_wck_en_p1          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p1_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p1      ), .o_q(o_ch1_dq1_dfi_wck_toggle_p1      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p1_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p1       ), .o_q(o_ch1_dq1_dfi_rddata_cs_p1       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p1_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p1       ), .o_q(o_ch1_dq1_dfi_rddata_en_p1       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p2_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq2_dfi_wrdata_p2      ), .o_q(o_ch1_dq0_dfi_wrdata_p2      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p2_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq2_dfi_wrdata_mask_p2 ), .o_q(o_ch1_dq0_dfi_wrdata_mask_p2 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p2_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p2       ), .o_q(o_ch1_dq0_dfi_parity_in_p2       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p2_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p2       ), .o_q(o_ch1_dq0_dfi_wrdata_cs_p2       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p2_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p2       ), .o_q(o_ch1_dq0_dfi_wrdata_en_p2       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p2_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p2          ), .o_q(o_ch1_dq0_dfi_wck_cs_p2          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p2_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p2          ), .o_q(o_ch1_dq0_dfi_wck_en_p2          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p2_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p2      ), .o_q(o_ch1_dq0_dfi_wck_toggle_p2      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p2_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p2       ), .o_q(o_ch1_dq0_dfi_rddata_cs_p2       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p2_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p2       ), .o_q(o_ch1_dq0_dfi_rddata_en_p2       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p2_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq3_dfi_wrdata_p2      ), .o_q(o_ch1_dq1_dfi_wrdata_p2      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p2_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq3_dfi_wrdata_mask_p2 ), .o_q(o_ch1_dq1_dfi_wrdata_mask_p2 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p2_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p2       ), .o_q(o_ch1_dq1_dfi_parity_in_p2       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p2_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p2       ), .o_q(o_ch1_dq1_dfi_wrdata_cs_p2       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p2_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p2       ), .o_q(o_ch1_dq1_dfi_wrdata_en_p2       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p2_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p2          ), .o_q(o_ch1_dq1_dfi_wck_cs_p2          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p2_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p2          ), .o_q(o_ch1_dq1_dfi_wck_en_p2          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p2_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p2      ), .o_q(o_ch1_dq1_dfi_wck_toggle_p2      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p2_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p2       ), .o_q(o_ch1_dq1_dfi_rddata_cs_p2       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p2_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p2       ), .o_q(o_ch1_dq1_dfi_rddata_en_p2       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p3_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq2_dfi_wrdata_p3      ), .o_q(o_ch1_dq0_dfi_wrdata_p3      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p3_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq2_dfi_wrdata_mask_p3 ), .o_q(o_ch1_dq0_dfi_wrdata_mask_p3 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p3_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p3       ), .o_q(o_ch1_dq0_dfi_parity_in_p3       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p3_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p3       ), .o_q(o_ch1_dq0_dfi_wrdata_cs_p3       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p3_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p3       ), .o_q(o_ch1_dq0_dfi_wrdata_en_p3       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p3_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p3          ), .o_q(o_ch1_dq0_dfi_wck_cs_p3          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p3_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p3          ), .o_q(o_ch1_dq0_dfi_wck_en_p3          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p3_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p3      ), .o_q(o_ch1_dq0_dfi_wck_toggle_p3      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p3_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p3       ), .o_q(o_ch1_dq0_dfi_rddata_cs_p3       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p3_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p3       ), .o_q(o_ch1_dq0_dfi_rddata_en_p3       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p3_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq3_dfi_wrdata_p3      ), .o_q(o_ch1_dq1_dfi_wrdata_p3      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p3_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq3_dfi_wrdata_mask_p3 ), .o_q(o_ch1_dq1_dfi_wrdata_mask_p3 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p3_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p3       ), .o_q(o_ch1_dq1_dfi_parity_in_p3       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p3_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p3       ), .o_q(o_ch1_dq1_dfi_wrdata_cs_p3       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p3_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p3       ), .o_q(o_ch1_dq1_dfi_wrdata_en_p3       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p3_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p3          ), .o_q(o_ch1_dq1_dfi_wck_cs_p3          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p3_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p3          ), .o_q(o_ch1_dq1_dfi_wck_en_p3          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p3_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p3      ), .o_q(o_ch1_dq1_dfi_wck_toggle_p3      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p3_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p3       ), .o_q(o_ch1_dq1_dfi_rddata_cs_p3       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p3_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p3       ), .o_q(o_ch1_dq1_dfi_rddata_en_p3       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p4_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq2_dfi_wrdata_p4      ), .o_q(o_ch1_dq0_dfi_wrdata_p4      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p4_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq2_dfi_wrdata_mask_p4 ), .o_q(o_ch1_dq0_dfi_wrdata_mask_p4 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p4_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p4       ), .o_q(o_ch1_dq0_dfi_parity_in_p4       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p4_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p4       ), .o_q(o_ch1_dq0_dfi_wrdata_cs_p4       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p4_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p4       ), .o_q(o_ch1_dq0_dfi_wrdata_en_p4       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p4_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p4          ), .o_q(o_ch1_dq0_dfi_wck_cs_p4          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p4_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p4          ), .o_q(o_ch1_dq0_dfi_wck_en_p4          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p4_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p4      ), .o_q(o_ch1_dq0_dfi_wck_toggle_p4      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p4_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p4       ), .o_q(o_ch1_dq0_dfi_rddata_cs_p4       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p4_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p4       ), .o_q(o_ch1_dq0_dfi_rddata_en_p4       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p4_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq3_dfi_wrdata_p4      ), .o_q(o_ch1_dq1_dfi_wrdata_p4      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p4_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq3_dfi_wrdata_mask_p4 ), .o_q(o_ch1_dq1_dfi_wrdata_mask_p4 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p4_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p4       ), .o_q(o_ch1_dq1_dfi_parity_in_p4       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p4_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p4       ), .o_q(o_ch1_dq1_dfi_wrdata_cs_p4       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p4_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p4       ), .o_q(o_ch1_dq1_dfi_wrdata_en_p4       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p4_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p4          ), .o_q(o_ch1_dq1_dfi_wck_cs_p4          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p4_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p4          ), .o_q(o_ch1_dq1_dfi_wck_en_p4          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p4_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p4      ), .o_q(o_ch1_dq1_dfi_wck_toggle_p4      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p4_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p4       ), .o_q(o_ch1_dq1_dfi_rddata_cs_p4       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p4_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p4       ), .o_q(o_ch1_dq1_dfi_rddata_en_p4       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p5_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq2_dfi_wrdata_p5      ), .o_q(o_ch1_dq0_dfi_wrdata_p5      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p5_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq2_dfi_wrdata_mask_p5 ), .o_q(o_ch1_dq0_dfi_wrdata_mask_p5 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p5_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p5       ), .o_q(o_ch1_dq0_dfi_parity_in_p5       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p5_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p5       ), .o_q(o_ch1_dq0_dfi_wrdata_cs_p5       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p5_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p5       ), .o_q(o_ch1_dq0_dfi_wrdata_en_p5       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p5_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p5          ), .o_q(o_ch1_dq0_dfi_wck_cs_p5          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p5_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p5          ), .o_q(o_ch1_dq0_dfi_wck_en_p5          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p5_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p5      ), .o_q(o_ch1_dq0_dfi_wck_toggle_p5      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p5_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p5       ), .o_q(o_ch1_dq0_dfi_rddata_cs_p5       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p5_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p5       ), .o_q(o_ch1_dq0_dfi_rddata_en_p5       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p5_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq3_dfi_wrdata_p5      ), .o_q(o_ch1_dq1_dfi_wrdata_p5      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p5_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq3_dfi_wrdata_mask_p5 ), .o_q(o_ch1_dq1_dfi_wrdata_mask_p5 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p5_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p5       ), .o_q(o_ch1_dq1_dfi_parity_in_p5       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p5_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p5       ), .o_q(o_ch1_dq1_dfi_wrdata_cs_p5       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p5_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p5       ), .o_q(o_ch1_dq1_dfi_wrdata_en_p5       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p5_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p5          ), .o_q(o_ch1_dq1_dfi_wck_cs_p5          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p5_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p5          ), .o_q(o_ch1_dq1_dfi_wck_en_p5          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p5_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p5      ), .o_q(o_ch1_dq1_dfi_wck_toggle_p5      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p5_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p5       ), .o_q(o_ch1_dq1_dfi_rddata_cs_p5       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p5_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p5       ), .o_q(o_ch1_dq1_dfi_rddata_en_p5       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p6_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq2_dfi_wrdata_p6      ), .o_q(o_ch1_dq0_dfi_wrdata_p6      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p6_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq2_dfi_wrdata_mask_p6 ), .o_q(o_ch1_dq0_dfi_wrdata_mask_p6 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p6_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p6       ), .o_q(o_ch1_dq0_dfi_parity_in_p6       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p6_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p6       ), .o_q(o_ch1_dq0_dfi_wrdata_cs_p6       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p6_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p6       ), .o_q(o_ch1_dq0_dfi_wrdata_en_p6       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p6_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p6          ), .o_q(o_ch1_dq0_dfi_wck_cs_p6          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p6_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p6          ), .o_q(o_ch1_dq0_dfi_wck_en_p6          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p6_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p6      ), .o_q(o_ch1_dq0_dfi_wck_toggle_p6      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p6_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p6       ), .o_q(o_ch1_dq0_dfi_rddata_cs_p6       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p6_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p6       ), .o_q(o_ch1_dq0_dfi_rddata_en_p6       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p6_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq3_dfi_wrdata_p6      ), .o_q(o_ch1_dq1_dfi_wrdata_p6      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p6_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq3_dfi_wrdata_mask_p6 ), .o_q(o_ch1_dq1_dfi_wrdata_mask_p6 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p6_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p6       ), .o_q(o_ch1_dq1_dfi_parity_in_p6       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p6_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p6       ), .o_q(o_ch1_dq1_dfi_wrdata_cs_p6       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p6_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p6       ), .o_q(o_ch1_dq1_dfi_wrdata_en_p6       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p6_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p6          ), .o_q(o_ch1_dq1_dfi_wck_cs_p6          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p6_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p6          ), .o_q(o_ch1_dq1_dfi_wck_en_p6          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p6_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p6      ), .o_q(o_ch1_dq1_dfi_wck_toggle_p6      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p6_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p6       ), .o_q(o_ch1_dq1_dfi_rddata_cs_p6       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p6_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p6       ), .o_q(o_ch1_dq1_dfi_rddata_en_p6       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p7_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq2_dfi_wrdata_p7      ), .o_q(o_ch1_dq0_dfi_wrdata_p7      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p7_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq2_dfi_wrdata_mask_p7 ), .o_q(o_ch1_dq0_dfi_wrdata_mask_p7 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p7_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p7       ), .o_q(o_ch1_dq0_dfi_parity_in_p7       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p7_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p7       ), .o_q(o_ch1_dq0_dfi_wrdata_cs_p7       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p7_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p7       ), .o_q(o_ch1_dq0_dfi_wrdata_en_p7       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p7_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p7          ), .o_q(o_ch1_dq0_dfi_wck_cs_p7          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p7_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p7          ), .o_q(o_ch1_dq0_dfi_wck_en_p7          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p7_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p7      ), .o_q(o_ch1_dq0_dfi_wck_toggle_p7      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p7_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p7       ), .o_q(o_ch1_dq0_dfi_rddata_cs_p7       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq0_pipe_p7_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p7       ), .o_q(o_ch1_dq0_dfi_rddata_en_p7       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p7_0 [SWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq3_dfi_wrdata_p7      ), .o_q(o_ch1_dq1_dfi_wrdata_p7      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p7_1 [MWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dq3_dfi_wrdata_mask_p7 ), .o_q(o_ch1_dq1_dfi_wrdata_mask_p7 ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p7_2              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_parity_in_p7       ), .o_q(o_ch1_dq1_dfi_parity_in_p7       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p7_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_cs_p7       ), .o_q(o_ch1_dq1_dfi_wrdata_cs_p7       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p7_4              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wrdata_en_p7       ), .o_q(o_ch1_dq1_dfi_wrdata_en_p7       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p7_5              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_cs_p7          ), .o_q(o_ch1_dq1_dfi_wck_cs_p7          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p7_6              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_en_p7          ), .o_q(o_ch1_dq1_dfi_wck_en_p7          ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p7_7 [TWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_wck_toggle_p7      ), .o_q(o_ch1_dq1_dfi_wck_toggle_p7      ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p7_8              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_cs_p7       ), .o_q(o_ch1_dq1_dfi_rddata_cs_p7       ));
   ddr_pipeline #(.DWIDTH(1)) u_ch1_dq1_pipe_p7_9              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_rddata_en_p7       ), .o_q(o_ch1_dq1_dfi_rddata_en_p7       ));

   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p0_0 [AWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_address_p0         ), .o_q(o_ch0_dfi_address_p0         ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p0_1        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cs_p0              ), .o_q(o_ch0_dfi_cs_p0              ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p0_2        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cke_p0             ), .o_q(o_ch0_dfi_cke_p0             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p0_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_dcd_p0             ), .o_q(o_ch0_dfi_dcd_p0             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p1_0 [AWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_address_p1         ), .o_q(o_ch0_dfi_address_p1         ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p1_1        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cs_p1              ), .o_q(o_ch0_dfi_cs_p1              ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p1_2        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cke_p1             ), .o_q(o_ch0_dfi_cke_p1             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p1_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_dcd_p1             ), .o_q(o_ch0_dfi_dcd_p1             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p2_0 [AWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_address_p2         ), .o_q(o_ch0_dfi_address_p2         ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p2_1        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cs_p2              ), .o_q(o_ch0_dfi_cs_p2              ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p2_2        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cke_p2             ), .o_q(o_ch0_dfi_cke_p2             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p2_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_dcd_p2             ), .o_q(o_ch0_dfi_dcd_p2             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p3_0 [AWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_address_p3         ), .o_q(o_ch0_dfi_address_p3         ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p3_1        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cs_p3              ), .o_q(o_ch0_dfi_cs_p3              ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p3_2        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cke_p3             ), .o_q(o_ch0_dfi_cke_p3             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p3_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_dcd_p3             ), .o_q(o_ch0_dfi_dcd_p3             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p4_0 [AWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_address_p4         ), .o_q(o_ch0_dfi_address_p4         ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p4_1        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cs_p4              ), .o_q(o_ch0_dfi_cs_p4              ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p4_2        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cke_p4             ), .o_q(o_ch0_dfi_cke_p4             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p4_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_dcd_p4             ), .o_q(o_ch0_dfi_dcd_p4             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p5_0 [AWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_address_p5         ), .o_q(o_ch0_dfi_address_p5         ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p5_1        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cs_p5              ), .o_q(o_ch0_dfi_cs_p5              ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p5_2        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cke_p5             ), .o_q(o_ch0_dfi_cke_p5             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p5_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_dcd_p5             ), .o_q(o_ch0_dfi_dcd_p5             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p6_0 [AWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_address_p6         ), .o_q(o_ch0_dfi_address_p6         ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p6_1        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cs_p6              ), .o_q(o_ch0_dfi_cs_p6              ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p6_2        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cke_p6             ), .o_q(o_ch0_dfi_cke_p6             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p6_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_dcd_p6             ), .o_q(o_ch0_dfi_dcd_p6             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p7_0 [AWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_address_p7         ), .o_q(o_ch0_dfi_address_p7         ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p7_1        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cs_p7              ), .o_q(o_ch0_dfi_cs_p7              ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p7_2        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cke_p7             ), .o_q(o_ch0_dfi_cke_p7             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch0_ca_pipe_p7_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_dcd_p7             ), .o_q(o_ch0_dfi_dcd_p7             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p0_0 [AWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_address_p0         ), .o_q(o_ch1_dfi_address_p0         ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p0_1        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cs_p0              ), .o_q(o_ch1_dfi_cs_p0              ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p0_2        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cke_p0             ), .o_q(o_ch1_dfi_cke_p0             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p0_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_dcd_p0             ), .o_q(o_ch1_dfi_dcd_p0             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p1_0 [AWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_address_p1         ), .o_q(o_ch1_dfi_address_p1         ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p1_1        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cs_p1              ), .o_q(o_ch1_dfi_cs_p1              ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p1_2        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cke_p1             ), .o_q(o_ch1_dfi_cke_p1             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p1_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_dcd_p1             ), .o_q(o_ch1_dfi_dcd_p1             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p2_0 [AWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_address_p2         ), .o_q(o_ch1_dfi_address_p2         ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p2_1        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cs_p2              ), .o_q(o_ch1_dfi_cs_p2              ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p2_2        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cke_p2             ), .o_q(o_ch1_dfi_cke_p2             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p2_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_dcd_p2             ), .o_q(o_ch1_dfi_dcd_p2             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p3_0 [AWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_address_p3         ), .o_q(o_ch1_dfi_address_p3         ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p3_1        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cs_p3              ), .o_q(o_ch1_dfi_cs_p3              ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p3_2        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cke_p3             ), .o_q(o_ch1_dfi_cke_p3             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p3_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_dcd_p3             ), .o_q(o_ch1_dfi_dcd_p3             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p4_0 [AWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_address_p4         ), .o_q(o_ch1_dfi_address_p4         ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p4_1        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cs_p4              ), .o_q(o_ch1_dfi_cs_p4              ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p4_2        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cke_p4             ), .o_q(o_ch1_dfi_cke_p4             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p4_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_dcd_p4             ), .o_q(o_ch1_dfi_dcd_p4             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p5_0 [AWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_address_p5         ), .o_q(o_ch1_dfi_address_p5         ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p5_1        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cs_p5              ), .o_q(o_ch1_dfi_cs_p5              ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p5_2        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cke_p5             ), .o_q(o_ch1_dfi_cke_p5             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p5_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_dcd_p5             ), .o_q(o_ch1_dfi_dcd_p5             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p6_0 [AWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_address_p6         ), .o_q(o_ch1_dfi_address_p6         ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p6_1        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cs_p6              ), .o_q(o_ch1_dfi_cs_p6              ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p6_2        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cke_p6             ), .o_q(o_ch1_dfi_cke_p6             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p6_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_dcd_p6             ), .o_q(o_ch1_dfi_dcd_p6             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p7_0 [AWIDTH-1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_address_p7         ), .o_q(o_ch1_dfi_address_p7         ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p7_1        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cs_p7              ), .o_q(o_ch1_dfi_cs_p7              ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p7_2        [1:0] (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_cke_p7             ), .o_q(o_ch1_dfi_cke_p7             ));
   ddr_pipeline #(.DWIDTH(1))  u_ch1_ca_pipe_p7_3              (.i_clk(i_clk), .i_pipe_en(i_intf_pipe_en), .i_d(int_dfi_dcd_p7             ), .o_q(o_ch1_dfi_dcd_p7             ));

   //---------------------------------------------------------------------------
   // Debug Bus
   //---------------------------------------------------------------------------
   assign o_debug = { 24'b0,
                      ig_write,
                      ig_read,
                      ig_empty_n,
                      o_ig_overflow,
                      eg_write,
                      eg_read,
                      eg_empty_n,
                      o_eg_overflow
                    } ;
endmodule

module ddr_gearbox_down # (
   parameter NUM_IN_PHASES   = 8,
   parameter NUM_OUT_PHASES  = 8
) (
   input  logic                      i_scan_cgc_ctrl,
   input  logic                      i_clk_1,
   input  logic                      i_clk_2,
   input  dwgb_t                     i_mode,
   input  logic [NUM_IN_PHASES-1:0]  i_d,
   output logic                      o_gb_en,
   output logic [NUM_OUT_PHASES-1:0] o_d
);

   logic [31:0] d_32to16;
   logic [31:0] d_32to8;
   logic [15:0] d_16to8;
   logic [7:0]  d_8to8;
   logic [7:0]  d_8to4;
   logic [3:0]  d_4to4;

   // ------------------------------------------------------------------------
   // Gearbox mapping
   // ------------------------------------------------------------------------

   integer q,r,s,t,v,w,x,y,z;

   //logic [31:0] map_8to8   [ 7:0] = {7,6,5,4,3,2,1,0};
   logic [31:0] map_8to8 [7:0];
   always_comb begin
      for (w=0; w<8; w=w+1) begin
         map_8to8[w] = w;
      end
   end

   integer p;
   always_comb begin
      for (p=0; p<8; p=p+1)
         d_8to8[p] = i_d[map_8to8[p]];
   end





   // ------------------------------------------------------------------------
   // Output
   // ------------------------------------------------------------------------
   logic [NUM_OUT_PHASES-1:0]  d_out;
   assign o_d     = d_8to8 ;
   assign o_gb_en = '0 ;

endmodule

module ddr_dfi_clk_ctrl # (
   parameter WR_PULSE_EXT_WIDTH           =  6
) (
   input  logic                           i_scan_cgc_ctrl,
   input  logic                           i_rst,
   input  logic                           i_phy_clk,
   input  logic                           i_wr_clk_1,
   input  logic                           i_wr_clk_2  ,

   input  dwgb_t                          i_wrgb_mode,
   input  drgb_t                          i_rdgb_mode,
   input  logic                           i_dq_wrclk_en ,           // WR data Enbale @ dfi clock rate.
   input  logic                           i_dqs_wrclk_en ,          // WR data Enbale or WCK enable @ dfi clock rate.
   input  logic                           i_ca_clk_en ,             // CS  @ dfi clock rate.
   input  logic                           i_ck_clk_en ,             // CA Clk Enbale @ dfi clock rate.
   input  logic [WR_PULSE_EXT_WIDTH-1:0]  i_dq_wrclk_en_pulse_ext,  // WR data Enbale pulse extension cycles @ dfi clock rate.
   input  logic [WR_PULSE_EXT_WIDTH-1:0]  i_dqs_wrclk_en_pulse_ext, // WR data Enbale or WCK OE  pulse extension cycles @ dfi clock rate.
   input  logic [WR_PULSE_EXT_WIDTH-1:0]  i_ck_clk_en_pulse_ext,    // CS pulse extension cycles @ dfi clock rate.
   input  logic [WR_PULSE_EXT_WIDTH-1:0]  i_ca_clk_en_pulse_ext,    // CA clk en pulse extension cycles @ dfi clock rate.
   input  logic                           i_ca_traffic_ovr_sel,
   input  logic                           i_ca_traffic_ovr,
   input  logic                           i_ck_traffic_ovr_sel,
   input  logic                           i_ck_traffic_ovr,
   input  logic                           i_dq_wrtraffic_ovr_sel,
   input  logic                           i_dq_wrtraffic_ovr,
   input  logic                           i_dqs_wrtraffic_ovr_sel,
   input  logic                           i_dqs_wrtraffic_ovr,

   output logic                           o_dqs_wrtraffic,
   output logic                           o_dq_wrtraffic,
   output logic                           o_ca_traffic,
   output logic                           o_ck_traffic,
   output logic [DEC_DFIGBWIDTH-1:0]      o_dfiwrgb_mode,
   output logic [DEC_DFIGBWIDTH-1:0]      o_dfirdgb_mode,
   output logic                           o_wrc_clk_0  ,
   output logic                           o_wrc_clk_1  ,
   output logic                           o_wrc_clk_2  ,
   output logic                           o_wrd_clk_0  ,
   output logic                           o_wrd_clk_1  ,
   output logic                           o_wrd_clk_2  ,
   output logic                           o_cmda_clk_0  ,
   output logic                           o_cmda_clk_1  ,
   output logic                           o_cmda_clk_2  ,
   output logic                           o_cmdc_clk_0  ,
   output logic                           o_cmdc_clk_1  ,
   output logic                           o_cmdc_clk_2  ,
   output logic                           o_dfi_clk
);

   // WR Clock gating and Dividers
   logic dqs_wrclk_en_extended;
   logic dq_wrclk_en_extended;
   logic ca_clk_en_extended;
   logic ck_clk_en_extended;

   logic dqs_wrtraffic_ovr_sel_sync, dqs_wrtraffic_ovr_sync;
   logic dq_wrtraffic_ovr_sel_sync,  dq_wrtraffic_ovr_sync;
   logic ck_traffic_ovr_sel_sync,    ck_traffic_ovr_sync;
   logic ca_traffic_ovr_sel_sync,    ca_traffic_ovr_sync;

   ddr_demet_s u_demet_0     (.i_clk(o_dfi_clk), .i_set(i_rst), .i_d(i_dqs_wrtraffic_ovr_sel), .o_q(dqs_wrtraffic_ovr_sel_sync));
   ddr_demet_s u_demet_1     (.i_clk(o_dfi_clk), .i_set(i_rst), .i_d(i_dqs_wrtraffic_ovr),     .o_q(dqs_wrtraffic_ovr_sync));
   ddr_demet_s u_demet_2     (.i_clk(o_dfi_clk), .i_set(i_rst), .i_d(i_dq_wrtraffic_ovr_sel),  .o_q(dq_wrtraffic_ovr_sel_sync));
   ddr_demet_s u_demet_3     (.i_clk(o_dfi_clk), .i_set(i_rst), .i_d(i_dq_wrtraffic_ovr),      .o_q(dq_wrtraffic_ovr_sync));
   ddr_demet_s u_demet_4     (.i_clk(o_dfi_clk), .i_set(i_rst), .i_d(i_ck_traffic_ovr_sel),    .o_q(ck_traffic_ovr_sel_sync));
   ddr_demet_s u_demet_5     (.i_clk(o_dfi_clk), .i_set(i_rst), .i_d(i_ck_traffic_ovr),        .o_q(ck_traffic_ovr_sync));
   ddr_demet_s u_demet_6     (.i_clk(o_dfi_clk), .i_set(i_rst), .i_d(i_ca_traffic_ovr_sel),    .o_q(ca_traffic_ovr_sel_sync));
   ddr_demet_s u_demet_7     (.i_clk(o_dfi_clk), .i_set(i_rst), .i_d(i_ca_traffic_ovr),        .o_q(ca_traffic_ovr_sync));

   ddr_pulse_extender #(.WIDTH(WR_PULSE_EXT_WIDTH)) u_dqs_wrclk_en_pulse_ext ( .i_clk(o_dfi_clk), .i_rst(i_rst), .i_d(i_dqs_wrclk_en), .i_num_pulses(i_dqs_wrclk_en_pulse_ext), .o_d (dqs_wrclk_en_extended));
   ddr_pulse_extender #(.WIDTH(WR_PULSE_EXT_WIDTH)) u_dq_wrclk_en_pulse_ext  ( .i_clk(o_dfi_clk), .i_rst(i_rst), .i_d(i_dq_wrclk_en),  .i_num_pulses(i_dq_wrclk_en_pulse_ext),  .o_d (dq_wrclk_en_extended));
   ddr_pulse_extender #(.WIDTH(WR_PULSE_EXT_WIDTH)) u_ck_clk_en_pulse_ext    ( .i_clk(o_dfi_clk), .i_rst(i_rst), .i_d(i_ck_clk_en),    .i_num_pulses(i_ck_clk_en_pulse_ext),    .o_d (ck_clk_en_extended));
   ddr_pulse_extender #(.WIDTH(WR_PULSE_EXT_WIDTH)) u_ca_clk_en_pulse_ext    ( .i_clk(o_dfi_clk), .i_rst(i_rst), .i_d(i_ca_clk_en),    .i_num_pulses(i_ca_clk_en_pulse_ext),    .o_d (ca_clk_en_extended));

   assign o_dqs_wrtraffic = dqs_wrtraffic_ovr_sel_sync ? dqs_wrtraffic_ovr_sync : dqs_wrclk_en_extended ;
   assign o_dq_wrtraffic  = dq_wrtraffic_ovr_sel_sync  ? dq_wrtraffic_ovr_sync  : dq_wrclk_en_extended ;
   assign o_ck_traffic    = ck_traffic_ovr_sel_sync    ? ck_traffic_ovr_sync    : ck_clk_en_extended ;
   assign o_ca_traffic    = ca_traffic_ovr_sel_sync    ? ca_traffic_ovr_sync    : ca_clk_en_extended ;

   assign o_dfi_clk    = i_wr_clk_2 ;

   ddr_cgc_rl u_wrc_clk_0_cgc_rl   (.i_clk(i_phy_clk),   .i_clk_en(o_dqs_wrtraffic), .i_cgc_en(i_scan_cgc_ctrl), .o_clk(o_wrc_clk_0));
   ddr_cgc_rl u_wrc_clk_1_cgc_rl   (.i_clk(i_wr_clk_1),  .i_clk_en(o_dqs_wrtraffic), .i_cgc_en(i_scan_cgc_ctrl), .o_clk(o_wrc_clk_1));
   ddr_cgc_rl u_wrc_clk_2_cgc_rl   (.i_clk(i_wr_clk_2),  .i_clk_en(o_dqs_wrtraffic), .i_cgc_en(i_scan_cgc_ctrl), .o_clk(o_wrc_clk_2));

   ddr_cgc_rl u_wrd_clk_0_cgc_rl   (.i_clk(i_phy_clk),   .i_clk_en(o_dq_wrtraffic), .i_cgc_en(i_scan_cgc_ctrl), .o_clk(o_wrd_clk_0));
   ddr_cgc_rl u_wrd_clk_1_cgc_rl   (.i_clk(i_wr_clk_1),  .i_clk_en(o_dq_wrtraffic), .i_cgc_en(i_scan_cgc_ctrl), .o_clk(o_wrd_clk_1));
   ddr_cgc_rl u_wrd_clk_2_cgc_rl   (.i_clk(i_wr_clk_2),  .i_clk_en(o_dq_wrtraffic), .i_cgc_en(i_scan_cgc_ctrl), .o_clk(o_wrd_clk_2));

   ddr_cgc_rl u_ck_clk_0_cgc_rl   (.i_clk(i_phy_clk),   .i_clk_en(o_ck_traffic), .i_cgc_en(i_scan_cgc_ctrl), .o_clk(o_cmdc_clk_0));
   ddr_cgc_rl u_ck_clk_1_cgc_rl   (.i_clk(i_wr_clk_1),  .i_clk_en(o_ck_traffic), .i_cgc_en(i_scan_cgc_ctrl), .o_clk(o_cmdc_clk_1));
   ddr_cgc_rl u_ck_clk_2_cgc_rl   (.i_clk(i_wr_clk_2),  .i_clk_en(o_ck_traffic), .i_cgc_en(i_scan_cgc_ctrl), .o_clk(o_cmdc_clk_2));

   ddr_cgc_rl u_ca_clk_0_cgc_rl   (.i_clk(i_phy_clk),   .i_clk_en(o_ca_traffic), .i_cgc_en(i_scan_cgc_ctrl), .o_clk(o_cmda_clk_0));
   ddr_cgc_rl u_ca_clk_1_cgc_rl   (.i_clk(i_wr_clk_1),  .i_clk_en(o_ca_traffic), .i_cgc_en(i_scan_cgc_ctrl), .o_clk(o_cmda_clk_1));
   ddr_cgc_rl u_ca_clk_2_cgc_rl   (.i_clk(i_wr_clk_2),  .i_clk_en(o_ca_traffic), .i_cgc_en(i_scan_cgc_ctrl), .o_clk(o_cmda_clk_2));

   always_comb begin
      o_dfiwrgb_mode = '0 ;
      case(i_wrgb_mode)
         DFIWGB_32TO16 : o_dfiwrgb_mode[`DFIWGB_32TO16_IDX] = 1'b1 ;
         DFIWGB_32TO8  : o_dfiwrgb_mode[`DFIWGB_32TO8_IDX]  = 1'b1 ;
         DFIWGB_16TO8  : o_dfiwrgb_mode[`DFIWGB_16TO8_IDX]  = 1'b1 ;
         DFIWGB_8TO8   : o_dfiwrgb_mode[`DFIWGB_8TO8_IDX]   = 1'b1 ;
         DFIWGB_8TO4   : o_dfiwrgb_mode[`DFIWGB_8TO4_IDX]   = 1'b1 ;
         DFIWGB_8TO2   : o_dfiwrgb_mode[`DFIWGB_8TO2_IDX]   = 1'b1 ;
         DFIWGB_4TO4   : o_dfiwrgb_mode[`DFIWGB_4TO4_IDX]   = 1'b1 ;
         DFIWGB_4TO2   : o_dfiwrgb_mode[`DFIWGB_4TO2_IDX]   = 1'b1 ;
         DFIWGB_2TO2   : o_dfiwrgb_mode[`DFIWGB_2TO2_IDX]   = 1'b1 ;
         default       : o_dfiwrgb_mode[`DFIWGB_2TO2_IDX]   = 1'b1 ;
      endcase
   end

   always_comb begin
      o_dfirdgb_mode = '0 ;
      case(i_rdgb_mode)
         DFIRGB_16TO32 : o_dfirdgb_mode[`DFIRGB_16TO32_IDX] = 1'b1 ;
         DFIRGB_8TO32  : o_dfirdgb_mode[`DFIRGB_8TO32_IDX]  = 1'b1 ;
         DFIRGB_8TO16  : o_dfirdgb_mode[`DFIRGB_8TO16_IDX]  = 1'b1 ;
         DFIRGB_8TO8   : o_dfirdgb_mode[`DFIRGB_8TO8_IDX]   = 1'b1 ;
         DFIRGB_4TO8   : o_dfirdgb_mode[`DFIRGB_4TO8_IDX]   = 1'b1 ;
         DFIRGB_4TO4   : o_dfirdgb_mode[`DFIRGB_4TO4_IDX]   = 1'b1 ;
         DFIRGB_2TO8   : o_dfirdgb_mode[`DFIRGB_2TO8_IDX]   = 1'b1 ;
         DFIRGB_2TO4   : o_dfirdgb_mode[`DFIRGB_2TO4_IDX]   = 1'b1 ;
         DFIRGB_2TO2   : o_dfirdgb_mode[`DFIRGB_2TO2_IDX]   = 1'b1 ;
         DFIRGB_1TO1   : o_dfirdgb_mode[`DFIRGB_1TO1_IDX]   = 1'b1 ;
         default       : o_dfirdgb_mode[`DFIRGB_1TO1_IDX]   = 1'b1 ;
      endcase
   end

endmodule

module ddr_pulse_extender # (
   parameter  WIDTH         = 4
) (
   input  logic             i_d,
   input  logic             i_clk,
   input  logic             i_rst,
   input  logic [WIDTH-1:0] i_num_pulses,
   output logic             o_d
);

   logic [WIDTH-1:0] cnt_q;
   logic d_q;
   logic d_asserted ;

   always_ff @ (posedge i_clk, posedge i_rst)
   begin
      if(i_rst)
         cnt_q <= '0;
      else if (i_d)
         cnt_q <= i_num_pulses;
      else if (~i_d && cnt_q != '0)
         cnt_q <= cnt_q - 1'b1;
   end

   always_ff @ (posedge i_clk, posedge i_rst)
   begin
      if(i_rst)
        d_q <= '0;
      else if (i_d || ~i_d && cnt_q == '0)
        d_q <= i_d;
   end

   assign d_asserted = i_d & ~d_q ;
   assign o_d = i_d | d_q ;

endmodule

module ddr_dfi_phase_extender # (
   parameter  PWIDTH = 4,
   parameter  NPH    = 4
) (
   input  dwgb_t                i_gb_mode,
   input  logic [NPH-1:0]       i_d,
   input  logic                 i_clk,
   input  logic                 i_rst,
   input  logic [PWIDTH-1:0]    i_num_pulses,
   output logic [NPH-1:0]       o_d
);

   localparam WIDTH = $clog2(NPH);

   // ------------------------------------------------------------------------
   // Mask
   // ------------------------------------------------------------------------

   logic [15:0]       gb_mask;
   logic [4:0]        active_ph ;
   logic [4:0]        sum_ph ;
   logic [4:0]        sum_ph_q ;
   logic [PWIDTH:0]   cnt_q ;
   logic [PWIDTH:0]   cnt_d ;
   logic [NPH-1:0]    q;

   // All control signals are SDR signals, use even bits.
   always_comb begin
      case(i_gb_mode)
         DFIWGB_32TO8  : begin gb_mask = 16'h00FF; active_ph = 5'd8;  sum_ph = (i_d[0]+i_d[2]+i_d[4]+i_d[6]) << 1'b1; end
         DFIWGB_16TO8  : begin gb_mask = 16'h00FF; active_ph = 5'd8;  sum_ph = (i_d[0]+i_d[2]+i_d[4]+i_d[6]) << 1'b1; end
         DFIWGB_8TO8   : begin gb_mask = 16'h00FF; active_ph = 5'd8;  sum_ph = (i_d[0]+i_d[2]+i_d[4]+i_d[6]) << 1'b1; end
         DFIWGB_8TO4   : begin gb_mask = 16'h000F; active_ph = 5'd4;  sum_ph = (i_d[0]+i_d[2]              ) << 1'b1; end
         DFIWGB_4TO4   : begin gb_mask = 16'h000F; active_ph = 5'd4;  sum_ph = (i_d[0]+i_d[2]              ) << 1'b1; end
         DFIWGB_8TO2   : begin gb_mask = 16'h0003; active_ph = 5'd2;  sum_ph = (i_d[0]                     ) << 1'b1; end
         DFIWGB_4TO2   : begin gb_mask = 16'h0003; active_ph = 5'd2;  sum_ph = (i_d[0]                     ) << 1'b1; end
         DFIWGB_2TO2   : begin gb_mask = 16'h0003; active_ph = 5'd2;  sum_ph = (i_d[0]                     ) << 1'b1; end
         default       : begin gb_mask = 16'h0003; active_ph = 5'd2;  sum_ph = (i_d[0]                     ) << 1'b1; end
      endcase
   end

   // ------------------------------------------------------------------------
   // FSM
   // ------------------------------------------------------------------------

   typedef enum logic [1:0] {
      START       = 2'd0,
      STOP        = 2'd1,
      EXTEND      = 2'd2,
      EXTEND_LAST = 2'd3
   } fsm_t;

   fsm_t fsm_state_q, fsm_state_d;

   always_ff @(posedge i_clk, posedge i_rst)
      if (i_rst) begin
         fsm_state_q <= START;
         cnt_q       <= '0;
      end else begin
         fsm_state_q <= fsm_state_d;
         cnt_q       <= cnt_d;
      end

   logic [NPH-1:0]    q_vld ;
   logic [NPH-1:0]    d_vld ;

   `ifdef DDR_ECO_PHASE_EXTENDER_VLD_PHASES
      assign d_vld = i_d & gb_mask[NPH-1:0] ;
      assign q_vld = q   & gb_mask[NPH-1:0] ;
   `else //DDR_ECO_PHASE_EXTENDER_VLD_PHASES
      assign d_vld = i_d  ;
      assign q_vld = q    ;
   `endif

   always_comb begin
      fsm_state_d = fsm_state_q;
      cnt_d       = i_num_pulses;
      case(fsm_state_q)
         START       : begin
                          // Phase activation - some (all) phase is asserted
                          if (d_vld != '0)
                             fsm_state_d = STOP;
                       end
         STOP        : begin
                          // Phase deactivation - some (all) phase is deasserted
                          //if (i_d != '1) begin
                          if ((i_d & gb_mask[NPH-1:0]) != gb_mask[NPH-1:0]) begin
                             // Extended by 1 cycle or more.
                             if (cnt_q >= active_ph ) begin
                                fsm_state_d = EXTEND;
                                cnt_d       = cnt_q - active_ph ;
                             // Extend by last cycle by phases less than active phases but need to be split across 2 cycles.
                             end else if ((d_vld & ({NPH{1'b1}} << (active_ph-cnt_q))) != '0 ) begin
                                fsm_state_d = EXTEND_LAST;
                                cnt_d       = cnt_q - (active_ph - sum_ph) ;
                             // Extend by additional phases in same cycle.
                             end else begin
                                fsm_state_d = START;
                             end
                          end
                       end
         EXTEND      : begin
                          if (d_vld != '0) begin
                             fsm_state_d = STOP;
                          end else if(cnt_q >= active_ph) begin
                             cnt_d       = cnt_q - active_ph ;
                          end else if ((q_vld & ({NPH{1'b1}} << (active_ph-cnt_q))) != '0 ) begin
                             fsm_state_d = EXTEND_LAST;
                             cnt_d       = cnt_q - (active_ph - sum_ph_q) ;
                          end else  begin
                             fsm_state_d = START;
                          end
                       end
         EXTEND_LAST : begin
                         if (d_vld != '0)
                            fsm_state_d = STOP;
                         else
                            fsm_state_d = START;
                       end

         default       : fsm_state_d = START;
      endcase
   end

   always_ff @(posedge i_clk, posedge i_rst)
      if (i_rst) begin
         q        <= '0;
         sum_ph_q <= '0;
      end else begin
         if ((fsm_state_d == EXTEND) && (fsm_state_q == STOP  )) begin
            q        <= i_d;
            sum_ph_q <= sum_ph ;
         end
      end

   // Shift the phase of the last cycle of the pulse which will pulse extend
   assign o_d = (fsm_state_d == START ) && (fsm_state_q == STOP  )                                       ? ~(~i_d << cnt_q)                 :       // Use inversion to shift in 1's
                ((fsm_state_d == EXTEND_LAST) || (fsm_state_d == EXTEND)) && (fsm_state_q == STOP  )     ? {NPH{1'b1}}                      :       // Extra cycle
                ((fsm_state_d == EXTEND_LAST) || (fsm_state_d == EXTEND)) && (fsm_state_q == EXTEND)     ? {NPH{1'b1}}                      :       // Extra cycle
                ((fsm_state_d == START )      || (fsm_state_d == STOP  )) && (fsm_state_q == EXTEND)     ? (~(~q << cnt_q )) | i_d          :       // Use inversion to shift in 1's
                ((fsm_state_d == START )      || (fsm_state_d == STOP  )) && (fsm_state_q == EXTEND_LAST)? (~({NPH{1'b1}} << cnt_q)) | i_d  : i_d;  // Use inversion to shift in 1's

endmodule

module ddr_dfi_read_cmd #(
   parameter       CWIDTH           = 11,           // CA Slice Width
   parameter       AWIDTH           = 7             // Address Slice Width
) (

   input  logic                     i_clk_1,
   input  logic                     i_clk_2,
   input  logic                     i_dfi_clk,

   input  drgb_t                    i_rgb_mode ,
   input  logic                     i_intf_pipe_en,
   input  logic [AWIDTH-1:0]        i_dfi_address_w0,
   input  logic [AWIDTH-1:0]        i_dfi_address_w1,
   input  logic [AWIDTH-1:0]        i_dfi_address_w2,
   input  logic [AWIDTH-1:0]        i_dfi_address_w3,
   input  logic [AWIDTH-1:0]        i_dfi_address_w4,
   input  logic [AWIDTH-1:0]        i_dfi_address_w5,
   input  logic [AWIDTH-1:0]        i_dfi_address_w6,
   input  logic [AWIDTH-1:0]        i_dfi_address_w7,
   input  logic [1:0]               i_dfi_cke_w0,
   input  logic [1:0]               i_dfi_cke_w1,
   input  logic [1:0]               i_dfi_cke_w2,
   input  logic [1:0]               i_dfi_cke_w3,
   input  logic [1:0]               i_dfi_cke_w4,
   input  logic [1:0]               i_dfi_cke_w5,
   input  logic [1:0]               i_dfi_cke_w6,
   input  logic [1:0]               i_dfi_cke_w7,
   input  logic [1:0]               i_dfi_cs_w0,
   input  logic [1:0]               i_dfi_cs_w1,
   input  logic [1:0]               i_dfi_cs_w2,
   input  logic [1:0]               i_dfi_cs_w3,
   input  logic [1:0]               i_dfi_cs_w4,
   input  logic [1:0]               i_dfi_cs_w5,
   input  logic [1:0]               i_dfi_cs_w6,
   input  logic [1:0]               i_dfi_cs_w7,
   input  logic [CWIDTH-1:0]        i_dfi_address_valid,

   output logic [AWIDTH-1:0]        o_dfi_address_w0,
   output logic [AWIDTH-1:0]        o_dfi_address_w1,
   output logic [AWIDTH-1:0]        o_dfi_address_w2,
   output logic [AWIDTH-1:0]        o_dfi_address_w3,
   output logic [AWIDTH-1:0]        o_dfi_address_w4,
   output logic [AWIDTH-1:0]        o_dfi_address_w5,
   output logic [AWIDTH-1:0]        o_dfi_address_w6,
   output logic [AWIDTH-1:0]        o_dfi_address_w7,
   output logic [1:0]               o_dfi_cke_w0,
   output logic [1:0]               o_dfi_cke_w1,
   output logic [1:0]               o_dfi_cke_w2,
   output logic [1:0]               o_dfi_cke_w3,
   output logic [1:0]               o_dfi_cke_w4,
   output logic [1:0]               o_dfi_cke_w5,
   output logic [1:0]               o_dfi_cke_w6,
   output logic [1:0]               o_dfi_cke_w7,
   output logic [1:0]               o_dfi_cs_w0,
   output logic [1:0]               o_dfi_cs_w1,
   output logic [1:0]               o_dfi_cs_w2,
   output logic [1:0]               o_dfi_cs_w3,
   output logic [1:0]               o_dfi_cs_w4,
   output logic [1:0]               o_dfi_cs_w5,
   output logic [1:0]               o_dfi_cs_w6,
   output logic [1:0]               o_dfi_cs_w7,
   output logic                     o_dfi_address_valid_w0,
   output logic                     o_dfi_address_valid_w1,
   output logic                     o_dfi_address_valid_w2,
   output logic                     o_dfi_address_valid_w3,
   output logic                     o_dfi_address_valid_w4,
   output logic                     o_dfi_address_valid_w5,
   output logic                     o_dfi_address_valid_w6,
   output logic                     o_dfi_address_valid_w7,

   output logic [31:0]              o_debug
);

 assign o_debug = '0 ; //FXIME

 localparam RWIDTH = CWIDTH+1;  //READ Bus Width

 logic [2:0] gb_mode_sel;
 assign gb_mode_sel[0] = (i_rgb_mode  == DFIRGB_2TO4) | (i_rgb_mode  == DFIRGB_4TO8) | (i_rgb_mode  == DFIRGB_8TO16) | (i_rgb_mode  == DFIRGB_16TO32) | gb_mode_sel[1]  | gb_mode_sel[2]   ; // phy:dfi clock ratio = 1to2
 assign gb_mode_sel[1] = (i_rgb_mode  == DFIRGB_2TO8) | (i_rgb_mode  == DFIRGB_8TO32) | gb_mode_sel[2]  ;    // phy:dfi clock ratio = 1to4
 assign gb_mode_sel[2] = '0  ;                                                                               // phy:dfi clock ratio = 1to8

   logic [RWIDTH-1:0] d_in_w0 ;
   logic [RWIDTH-1:0] d_in_w1 ;
   logic [RWIDTH-1:0] d_in_w2 ;
   logic [RWIDTH-1:0] d_in_w3 ;
   logic [RWIDTH-1:0] d_in_w4 ;
   logic [RWIDTH-1:0] d_in_w5 ;
   logic [RWIDTH-1:0] d_in_w6 ;
   logic [RWIDTH-1:0] d_in_w7 ;
   logic [RWIDTH-1:0] d_out_w0 ;
   logic [RWIDTH-1:0] d_out_w0_q ;
   logic [RWIDTH-1:0] d_out_w1 ;
   logic [RWIDTH-1:0] d_out_w1_q ;
   logic [RWIDTH-1:0] d_out_w2 ;
   logic [RWIDTH-1:0] d_out_w2_q ;
   logic [RWIDTH-1:0] d_out_w3 ;
   logic [RWIDTH-1:0] d_out_w3_q ;
   logic [RWIDTH-1:0] d_out_w4 ;
   logic [RWIDTH-1:0] d_out_w4_q ;
   logic [RWIDTH-1:0] d_out_w5 ;
   logic [RWIDTH-1:0] d_out_w5_q ;
   logic [RWIDTH-1:0] d_out_w6 ;
   logic [RWIDTH-1:0] d_out_w6_q ;
   logic [RWIDTH-1:0] d_out_w7 ;
   logic [RWIDTH-1:0] d_out_w7_q ;

//Generate Valid signal phases based on GB mode.

   logic dfi_address_valid_w0 ;
   logic dfi_address_valid_w1 ;
   logic dfi_address_valid_w2 ;
   logic dfi_address_valid_w3 ;
   logic dfi_address_valid_w4 ;
   logic dfi_address_valid_w5 ;
   logic dfi_address_valid_w6 ;
   logic dfi_address_valid_w7 ;

   logic address_valid;
   assign address_valid = i_dfi_address_valid[0];

   always_comb
   begin
      dfi_address_valid_w0 = '0 ;
      dfi_address_valid_w1 = '0 ;
      dfi_address_valid_w2 = '0 ;
      dfi_address_valid_w3 = '0 ;
      dfi_address_valid_w4 = '0 ;
      dfi_address_valid_w5 = '0 ;
      dfi_address_valid_w6 = '0 ;
      dfi_address_valid_w7 = '0 ;
      case (i_rgb_mode)
         DFIRGB_8TO32  : begin
                           dfi_address_valid_w0 = address_valid;
                           dfi_address_valid_w1 = address_valid;
                           dfi_address_valid_w2 = address_valid;
                           dfi_address_valid_w3 = address_valid;
                           dfi_address_valid_w4 = address_valid;
                           dfi_address_valid_w5 = address_valid;
                           dfi_address_valid_w6 = address_valid;
                           dfi_address_valid_w7 = address_valid;
         end
         DFIRGB_8TO16  : begin
                           dfi_address_valid_w0 = address_valid;
                           dfi_address_valid_w1 = address_valid;
                           dfi_address_valid_w2 = address_valid;
                           dfi_address_valid_w3 = address_valid;
                           dfi_address_valid_w4 = address_valid;
                           dfi_address_valid_w5 = address_valid;
                           dfi_address_valid_w6 = address_valid;
                           dfi_address_valid_w7 = address_valid;
         end
         DFIRGB_8TO8   : begin
                           dfi_address_valid_w0 = address_valid;
                           dfi_address_valid_w1 = address_valid;
                           dfi_address_valid_w2 = address_valid;
                           dfi_address_valid_w3 = address_valid;
                           dfi_address_valid_w4 = address_valid;
                           dfi_address_valid_w5 = address_valid;
                           dfi_address_valid_w6 = address_valid;
                           dfi_address_valid_w7 = address_valid;
         end
         DFIRGB_4TO8   : begin
                           dfi_address_valid_w0 = address_valid;
                           dfi_address_valid_w1 = address_valid;
                           dfi_address_valid_w2 = address_valid;
                           dfi_address_valid_w3 = address_valid;
         end
         DFIRGB_4TO4   : begin
                           dfi_address_valid_w0 = address_valid;
                           dfi_address_valid_w1 = address_valid;
                           dfi_address_valid_w2 = address_valid;
                           dfi_address_valid_w3 = address_valid;
         end
         DFIRGB_2TO8   : begin
                           dfi_address_valid_w0 = address_valid;
                           dfi_address_valid_w1 = address_valid;
         end
         DFIRGB_2TO4   : begin
                           dfi_address_valid_w0 = address_valid;
                           dfi_address_valid_w1 = address_valid;
         end
         DFIRGB_2TO2   : begin
                           dfi_address_valid_w0 = address_valid;
                           dfi_address_valid_w1 = address_valid;
         end
         DFIRGB_1TO1   : begin
                           dfi_address_valid_w0 = address_valid;
         end
      endcase
   end

    assign d_in_w0 = {
                        dfi_address_valid_w0,
                        i_dfi_cs_w0,
                        i_dfi_cke_w0,
                        i_dfi_address_w0
                    };
    assign d_in_w1 = {
                        dfi_address_valid_w1,
                        i_dfi_cs_w1,
                        i_dfi_cke_w1,
                        i_dfi_address_w1
                    };
    assign d_in_w2 = {
                        dfi_address_valid_w2,
                        i_dfi_cs_w2,
                        i_dfi_cke_w2,
                        i_dfi_address_w2
                    };
    assign d_in_w3 = {
                        dfi_address_valid_w3,
                        i_dfi_cs_w3,
                        i_dfi_cke_w3,
                        i_dfi_address_w3
                    };
    assign d_in_w4 = {
                        dfi_address_valid_w4,
                        i_dfi_cs_w4,
                        i_dfi_cke_w4,
                        i_dfi_address_w4
                    };
    assign d_in_w5 = {
                        dfi_address_valid_w5,
                        i_dfi_cs_w5,
                        i_dfi_cke_w5,
                        i_dfi_address_w5
                    };
    assign d_in_w6 = {
                        dfi_address_valid_w6,
                        i_dfi_cs_w6,
                        i_dfi_cke_w6,
                        i_dfi_address_w6
                    };
    assign d_in_w7 = {
                        dfi_address_valid_w7,
                        i_dfi_cs_w7,
                        i_dfi_cke_w7,
                        i_dfi_address_w7
                    };

   assign o_dfi_address_w0       = {d_out_w0_q[(AWIDTH-1):0]} ;
   assign o_dfi_cke_w0           = {d_out_w0_q[(AWIDTH+0)+:2]} ;
   assign o_dfi_cs_w0            = {d_out_w0_q[(AWIDTH+2)+:2]} ;
   assign o_dfi_address_valid_w0 = {d_out_w0_q[RWIDTH-1]} ;
   assign o_dfi_address_w1       = {d_out_w1_q[(AWIDTH-1):0]} ;
   assign o_dfi_cke_w1           = {d_out_w1_q[(AWIDTH+0)+:2]} ;
   assign o_dfi_cs_w1            = {d_out_w1_q[(AWIDTH+2)+:2]} ;
   assign o_dfi_address_valid_w1 = {d_out_w1_q[RWIDTH-1]} ;
   assign o_dfi_address_w2       = {d_out_w2_q[(AWIDTH-1):0]} ;
   assign o_dfi_cke_w2           = {d_out_w2_q[(AWIDTH+0)+:2]} ;
   assign o_dfi_cs_w2            = {d_out_w2_q[(AWIDTH+2)+:2]} ;
   assign o_dfi_address_valid_w2 = {d_out_w2_q[RWIDTH-1]} ;
   assign o_dfi_address_w3       = {d_out_w3_q[(AWIDTH-1):0]} ;
   assign o_dfi_cke_w3           = {d_out_w3_q[(AWIDTH+0)+:2]} ;
   assign o_dfi_cs_w3            = {d_out_w3_q[(AWIDTH+2)+:2]} ;
   assign o_dfi_address_valid_w3 = {d_out_w3_q[RWIDTH-1]} ;
   assign o_dfi_address_w4       = {d_out_w4_q[(AWIDTH-1):0]} ;
   assign o_dfi_cke_w4           = {d_out_w4_q[(AWIDTH+0)+:2]} ;
   assign o_dfi_cs_w4            = {d_out_w4_q[(AWIDTH+2)+:2]} ;
   assign o_dfi_address_valid_w4 = {d_out_w4_q[RWIDTH-1]} ;
   assign o_dfi_address_w5       = {d_out_w5_q[(AWIDTH-1):0]} ;
   assign o_dfi_cke_w5           = {d_out_w5_q[(AWIDTH+0)+:2]} ;
   assign o_dfi_cs_w5            = {d_out_w5_q[(AWIDTH+2)+:2]} ;
   assign o_dfi_address_valid_w5 = {d_out_w5_q[RWIDTH-1]} ;
   assign o_dfi_address_w6       = {d_out_w6_q[(AWIDTH-1):0]} ;
   assign o_dfi_cke_w6           = {d_out_w6_q[(AWIDTH+0)+:2]} ;
   assign o_dfi_cs_w6            = {d_out_w6_q[(AWIDTH+2)+:2]} ;
   assign o_dfi_address_valid_w6 = {d_out_w6_q[RWIDTH-1]} ;
   assign o_dfi_address_w7       = {d_out_w7_q[(AWIDTH-1):0]} ;
   assign o_dfi_cke_w7           = {d_out_w7_q[(AWIDTH+0)+:2]} ;
   assign o_dfi_cs_w7            = {d_out_w7_q[(AWIDTH+2)+:2]} ;
   assign o_dfi_address_valid_w7 = {d_out_w7_q[RWIDTH-1]} ;

   genvar j;
   generate
      for (j=0; j<(RWIDTH); j=j+1) begin : GEARBOX
         ddr_gearbox_up u_gearbox_up (
            .i_clk_1                             (i_clk_1  ),
            .i_clk_2                             (i_clk_2  ),
            .i_clk_3                             ('0),
            .i_d_0                              (d_in_w0[j]),
            .i_d_1                              (d_in_w1[j]),
            .i_d_2                              (d_in_w2[j]),
            .i_d_3                              (d_in_w3[j]),
            .i_d_4                              (d_in_w4[j]),
            .i_d_5                              (d_in_w5[j]),
            .i_d_6                              (d_in_w6[j]),
            .i_d_7                              (d_in_w7[j]),
            .o_d_p0                             (d_out_w0[j]),
            .o_d_p1                             (d_out_w1[j]),
            .o_d_p2                             (d_out_w2[j]),
            .o_d_p3                             (d_out_w3[j]),
            .o_d_p4                             (d_out_w4[j]),
            .o_d_p5                             (d_out_w5[j]),
            .o_d_p6                             (d_out_w6[j]),
            .o_d_p7                             (d_out_w7[j]),
            .i_gb_mode_sel                       (gb_mode_sel)
         );
      end
   endgenerate

   ddr_pipeline #(
      .DWIDTH      (RWIDTH)
   ) u_pipe_w0 (
      .i_clk       (i_dfi_clk),
      .i_pipe_en   ({RWIDTH{i_intf_pipe_en}}),
      .i_d         (d_out_w0),
      .o_q         (d_out_w0_q)
   );
   ddr_pipeline #(
      .DWIDTH      (RWIDTH)
   ) u_pipe_w1 (
      .i_clk       (i_dfi_clk),
      .i_pipe_en   ({RWIDTH{i_intf_pipe_en}}),
      .i_d         (d_out_w1),
      .o_q         (d_out_w1_q)
   );
   ddr_pipeline #(
      .DWIDTH      (RWIDTH)
   ) u_pipe_w2 (
      .i_clk       (i_dfi_clk),
      .i_pipe_en   ({RWIDTH{i_intf_pipe_en}}),
      .i_d         (d_out_w2),
      .o_q         (d_out_w2_q)
   );
   ddr_pipeline #(
      .DWIDTH      (RWIDTH)
   ) u_pipe_w3 (
      .i_clk       (i_dfi_clk),
      .i_pipe_en   ({RWIDTH{i_intf_pipe_en}}),
      .i_d         (d_out_w3),
      .o_q         (d_out_w3_q)
   );
   ddr_pipeline #(
      .DWIDTH      (RWIDTH)
   ) u_pipe_w4 (
      .i_clk       (i_dfi_clk),
      .i_pipe_en   ({RWIDTH{i_intf_pipe_en}}),
      .i_d         (d_out_w4),
      .o_q         (d_out_w4_q)
   );
   ddr_pipeline #(
      .DWIDTH      (RWIDTH)
   ) u_pipe_w5 (
      .i_clk       (i_dfi_clk),
      .i_pipe_en   ({RWIDTH{i_intf_pipe_en}}),
      .i_d         (d_out_w5),
      .o_q         (d_out_w5_q)
   );
   ddr_pipeline #(
      .DWIDTH      (RWIDTH)
   ) u_pipe_w6 (
      .i_clk       (i_dfi_clk),
      .i_pipe_en   ({RWIDTH{i_intf_pipe_en}}),
      .i_d         (d_out_w6),
      .o_q         (d_out_w6_q)
   );
   ddr_pipeline #(
      .DWIDTH      (RWIDTH)
   ) u_pipe_w7 (
      .i_clk       (i_dfi_clk),
      .i_pipe_en   ({RWIDTH{i_intf_pipe_en}}),
      .i_d         (d_out_w7),
      .o_q         (d_out_w7_q)
   );

endmodule

module ddr_dfi_read #(
   parameter       NUM_DQ           = 2,
   parameter       SWIDTH           = 8,            // PHY Slice Width
   parameter       BWIDTH           = SWIDTH / 8,   // BYTE Width
   parameter       MWIDTH           = BWIDTH        // Mask width
) (

   input  logic                     i_clk_1,
   input  logic                     i_clk_2,
   input  logic                     i_dfi_clk,

   input  drgb_t                    i_rgb_mode ,
   input  logic                     i_intf_pipe_en ,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_rddata_w0,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_rddata_w1,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_rddata_w2,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_rddata_w3,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_rddata_w4,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_rddata_w5,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_rddata_w6,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_rddata_w7,
   input  logic [MWIDTH-1:0]        i_dq0_dfi_rddata_dbi_w0,
   input  logic [MWIDTH-1:0]        i_dq0_dfi_rddata_dbi_w1,
   input  logic [MWIDTH-1:0]        i_dq0_dfi_rddata_dbi_w2,
   input  logic [MWIDTH-1:0]        i_dq0_dfi_rddata_dbi_w3,
   input  logic [MWIDTH-1:0]        i_dq0_dfi_rddata_dbi_w4,
   input  logic [MWIDTH-1:0]        i_dq0_dfi_rddata_dbi_w5,
   input  logic [MWIDTH-1:0]        i_dq0_dfi_rddata_dbi_w6,
   input  logic [MWIDTH-1:0]        i_dq0_dfi_rddata_dbi_w7,
   input  logic [SWIDTH-1:0]        i_dq0_dfi_rddata_valid,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_rddata_w0,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_rddata_w1,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_rddata_w2,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_rddata_w3,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_rddata_w4,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_rddata_w5,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_rddata_w6,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_rddata_w7,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_rddata_dbi_w0,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_rddata_dbi_w1,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_rddata_dbi_w2,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_rddata_dbi_w3,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_rddata_dbi_w4,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_rddata_dbi_w5,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_rddata_dbi_w6,
   input  logic [MWIDTH-1:0]        i_dq1_dfi_rddata_dbi_w7,
   input  logic [SWIDTH-1:0]        i_dq1_dfi_rddata_valid,
   input  logic [NUM_DQ-1:0]        i_dq_dfi_rddata_valid_mask ,
   output logic [NUM_DQ*SWIDTH-1:0] o_dfi_rddata_w0,
   output logic [NUM_DQ*SWIDTH-1:0] o_dfi_rddata_w1,
   output logic [NUM_DQ*SWIDTH-1:0] o_dfi_rddata_w2,
   output logic [NUM_DQ*SWIDTH-1:0] o_dfi_rddata_w3,
   output logic [NUM_DQ*SWIDTH-1:0] o_dfi_rddata_w4,
   output logic [NUM_DQ*SWIDTH-1:0] o_dfi_rddata_w5,
   output logic [NUM_DQ*SWIDTH-1:0] o_dfi_rddata_w6,
   output logic [NUM_DQ*SWIDTH-1:0] o_dfi_rddata_w7,
   output logic [NUM_DQ*MWIDTH-1:0] o_dfi_rddata_dbi_w0,
   output logic [NUM_DQ*MWIDTH-1:0] o_dfi_rddata_dbi_w1,
   output logic [NUM_DQ*MWIDTH-1:0] o_dfi_rddata_dbi_w2,
   output logic [NUM_DQ*MWIDTH-1:0] o_dfi_rddata_dbi_w3,
   output logic [NUM_DQ*MWIDTH-1:0] o_dfi_rddata_dbi_w4,
   output logic [NUM_DQ*MWIDTH-1:0] o_dfi_rddata_dbi_w5,
   output logic [NUM_DQ*MWIDTH-1:0] o_dfi_rddata_dbi_w6,
   output logic [NUM_DQ*MWIDTH-1:0] o_dfi_rddata_dbi_w7,
   output logic                     o_dfi_rddata_valid_w0,
   output logic                     o_dfi_rddata_valid_w1,
   output logic                     o_dfi_rddata_valid_w2,
   output logic                     o_dfi_rddata_valid_w3,
   output logic                     o_dfi_rddata_valid_w4,
   output logic                     o_dfi_rddata_valid_w5,
   output logic                     o_dfi_rddata_valid_w6,
   output logic                     o_dfi_rddata_valid_w7,

   output logic [31:0]              o_debug
);

 assign o_debug = '0 ; //FXIME

 localparam RWIDTH = (SWIDTH+MWIDTH)*NUM_DQ + 1 ;  //READ Bus Width

 logic [2:0] gb_mode_sel;
 assign gb_mode_sel[0] = (i_rgb_mode  == DFIRGB_2TO4) | (i_rgb_mode  == DFIRGB_4TO8) | (i_rgb_mode  == DFIRGB_8TO16) | (i_rgb_mode  == DFIRGB_16TO32) | gb_mode_sel[1]  | gb_mode_sel[2]   ; // phy:dfi clock ratio = 1to2
 assign gb_mode_sel[1] = (i_rgb_mode  == DFIRGB_2TO8) | (i_rgb_mode  == DFIRGB_8TO32) | gb_mode_sel[2]  ;    // phy:dfi clock ratio = 1to4
 assign gb_mode_sel[2] = '0  ;                                                                               // phy:dfi clock ratio = 1to8

   logic [RWIDTH-1:0] d_in_w0 ;
   logic [RWIDTH-1:0] d_in_w1 ;
   logic [RWIDTH-1:0] d_in_w2 ;
   logic [RWIDTH-1:0] d_in_w3 ;
   logic [RWIDTH-1:0] d_in_w4 ;
   logic [RWIDTH-1:0] d_in_w5 ;
   logic [RWIDTH-1:0] d_in_w6 ;
   logic [RWIDTH-1:0] d_in_w7 ;
   logic [RWIDTH-1:0] d_out_w0 ;
   logic [RWIDTH-1:0] d_out_w0_q ;
   logic [RWIDTH-1:0] d_out_w1 ;
   logic [RWIDTH-1:0] d_out_w1_q ;
   logic [RWIDTH-1:0] d_out_w2 ;
   logic [RWIDTH-1:0] d_out_w2_q ;
   logic [RWIDTH-1:0] d_out_w3 ;
   logic [RWIDTH-1:0] d_out_w3_q ;
   logic [RWIDTH-1:0] d_out_w4 ;
   logic [RWIDTH-1:0] d_out_w4_q ;
   logic [RWIDTH-1:0] d_out_w5 ;
   logic [RWIDTH-1:0] d_out_w5_q ;
   logic [RWIDTH-1:0] d_out_w6 ;
   logic [RWIDTH-1:0] d_out_w6_q ;
   logic [RWIDTH-1:0] d_out_w7 ;
   logic [RWIDTH-1:0] d_out_w7_q ;

//Generate Valid signal phases based on GB mode.

   logic dq_dfi_rddata_valid_w0 ;
   logic dq_dfi_rddata_valid_w1 ;
   logic dq_dfi_rddata_valid_w2 ;
   logic dq_dfi_rddata_valid_w3 ;
   logic dq_dfi_rddata_valid_w4 ;
   logic dq_dfi_rddata_valid_w5 ;
   logic dq_dfi_rddata_valid_w6 ;
   logic dq_dfi_rddata_valid_w7 ;
   logic rddata_valid;

   assign rddata_valid =
                        (i_dq1_dfi_rddata_valid[0] | i_dq_dfi_rddata_valid_mask[1]) &
                        (i_dq0_dfi_rddata_valid[0] | i_dq_dfi_rddata_valid_mask[0]) ;

   always_comb
   begin
      dq_dfi_rddata_valid_w0 = '0 ;
      dq_dfi_rddata_valid_w1 = '0 ;
      dq_dfi_rddata_valid_w2 = '0 ;
      dq_dfi_rddata_valid_w3 = '0 ;
      dq_dfi_rddata_valid_w4 = '0 ;
      dq_dfi_rddata_valid_w5 = '0 ;
      dq_dfi_rddata_valid_w6 = '0 ;
      dq_dfi_rddata_valid_w7 = '0 ;
      case (i_rgb_mode)
         DFIRGB_8TO32  : begin
                           dq_dfi_rddata_valid_w0 = rddata_valid;
                           dq_dfi_rddata_valid_w1 = rddata_valid;
                           dq_dfi_rddata_valid_w2 = rddata_valid;
                           dq_dfi_rddata_valid_w3 = rddata_valid;
                           dq_dfi_rddata_valid_w4 = rddata_valid;
                           dq_dfi_rddata_valid_w5 = rddata_valid;
                           dq_dfi_rddata_valid_w6 = rddata_valid;
                           dq_dfi_rddata_valid_w7 = rddata_valid;
         end
         DFIRGB_8TO16  : begin
                           dq_dfi_rddata_valid_w0 = rddata_valid;
                           dq_dfi_rddata_valid_w1 = rddata_valid;
                           dq_dfi_rddata_valid_w2 = rddata_valid;
                           dq_dfi_rddata_valid_w3 = rddata_valid;
                           dq_dfi_rddata_valid_w4 = rddata_valid;
                           dq_dfi_rddata_valid_w5 = rddata_valid;
                           dq_dfi_rddata_valid_w6 = rddata_valid;
                           dq_dfi_rddata_valid_w7 = rddata_valid;
         end
         DFIRGB_8TO8   : begin
                           dq_dfi_rddata_valid_w0 = rddata_valid;
                           dq_dfi_rddata_valid_w1 = rddata_valid;
                           dq_dfi_rddata_valid_w2 = rddata_valid;
                           dq_dfi_rddata_valid_w3 = rddata_valid;
                           dq_dfi_rddata_valid_w4 = rddata_valid;
                           dq_dfi_rddata_valid_w5 = rddata_valid;
                           dq_dfi_rddata_valid_w6 = rddata_valid;
                           dq_dfi_rddata_valid_w7 = rddata_valid;
         end
         DFIRGB_4TO8   : begin
                           dq_dfi_rddata_valid_w0 = rddata_valid;
                           dq_dfi_rddata_valid_w1 = rddata_valid;
                           dq_dfi_rddata_valid_w2 = rddata_valid;
                           dq_dfi_rddata_valid_w3 = rddata_valid;
         end
         DFIRGB_4TO4   : begin
                           dq_dfi_rddata_valid_w0 = rddata_valid;
                           dq_dfi_rddata_valid_w1 = rddata_valid;
                           dq_dfi_rddata_valid_w2 = rddata_valid;
                           dq_dfi_rddata_valid_w3 = rddata_valid;
         end
         DFIRGB_2TO8   : begin
                           dq_dfi_rddata_valid_w0 = rddata_valid;
                           dq_dfi_rddata_valid_w1 = rddata_valid;
         end
         DFIRGB_2TO4   : begin
                           dq_dfi_rddata_valid_w0 = rddata_valid;
                           dq_dfi_rddata_valid_w1 = rddata_valid;
         end
         DFIRGB_2TO2   : begin
                           dq_dfi_rddata_valid_w0 = rddata_valid;
                           dq_dfi_rddata_valid_w1 = rddata_valid;
         end
         DFIRGB_1TO1   : begin
                           dq_dfi_rddata_valid_w0 = rddata_valid;
         end
      endcase
   end

    assign d_in_w0 = {
                        dq_dfi_rddata_valid_w0,
                        i_dq1_dfi_rddata_dbi_w0,
                        i_dq0_dfi_rddata_dbi_w0,
                        i_dq1_dfi_rddata_w0,
                        i_dq0_dfi_rddata_w0
                    };
    assign d_in_w1 = {
                        dq_dfi_rddata_valid_w1,
                        i_dq1_dfi_rddata_dbi_w1,
                        i_dq0_dfi_rddata_dbi_w1,
                        i_dq1_dfi_rddata_w1,
                        i_dq0_dfi_rddata_w1
                    };
    assign d_in_w2 = {
                        dq_dfi_rddata_valid_w2,
                        i_dq1_dfi_rddata_dbi_w2,
                        i_dq0_dfi_rddata_dbi_w2,
                        i_dq1_dfi_rddata_w2,
                        i_dq0_dfi_rddata_w2
                    };
    assign d_in_w3 = {
                        dq_dfi_rddata_valid_w3,
                        i_dq1_dfi_rddata_dbi_w3,
                        i_dq0_dfi_rddata_dbi_w3,
                        i_dq1_dfi_rddata_w3,
                        i_dq0_dfi_rddata_w3
                    };
    assign d_in_w4 = {
                        dq_dfi_rddata_valid_w4,
                        i_dq1_dfi_rddata_dbi_w4,
                        i_dq0_dfi_rddata_dbi_w4,
                        i_dq1_dfi_rddata_w4,
                        i_dq0_dfi_rddata_w4
                    };
    assign d_in_w5 = {
                        dq_dfi_rddata_valid_w5,
                        i_dq1_dfi_rddata_dbi_w5,
                        i_dq0_dfi_rddata_dbi_w5,
                        i_dq1_dfi_rddata_w5,
                        i_dq0_dfi_rddata_w5
                    };
    assign d_in_w6 = {
                        dq_dfi_rddata_valid_w6,
                        i_dq1_dfi_rddata_dbi_w6,
                        i_dq0_dfi_rddata_dbi_w6,
                        i_dq1_dfi_rddata_w6,
                        i_dq0_dfi_rddata_w6
                    };
    assign d_in_w7 = {
                        dq_dfi_rddata_valid_w7,
                        i_dq1_dfi_rddata_dbi_w7,
                        i_dq0_dfi_rddata_dbi_w7,
                        i_dq1_dfi_rddata_w7,
                        i_dq0_dfi_rddata_w7
                    };

   assign o_dfi_rddata_w0       = {d_out_w0_q[(NUM_DQ*SWIDTH)-1:0]} ;
   assign o_dfi_rddata_dbi_w0   = {d_out_w0_q[(NUM_DQ*SWIDTH)+:(NUM_DQ*MWIDTH)]} ;
   assign o_dfi_rddata_valid_w0 = {d_out_w0_q[RWIDTH-1]} ;
   assign o_dfi_rddata_w1       = {d_out_w1_q[(NUM_DQ*SWIDTH)-1:0]} ;
   assign o_dfi_rddata_dbi_w1   = {d_out_w1_q[(NUM_DQ*SWIDTH)+:(NUM_DQ*MWIDTH)]} ;
   assign o_dfi_rddata_valid_w1 = {d_out_w1_q[RWIDTH-1]} ;
   assign o_dfi_rddata_w2       = {d_out_w2_q[(NUM_DQ*SWIDTH)-1:0]} ;
   assign o_dfi_rddata_dbi_w2   = {d_out_w2_q[(NUM_DQ*SWIDTH)+:(NUM_DQ*MWIDTH)]} ;
   assign o_dfi_rddata_valid_w2 = {d_out_w2_q[RWIDTH-1]} ;
   assign o_dfi_rddata_w3       = {d_out_w3_q[(NUM_DQ*SWIDTH)-1:0]} ;
   assign o_dfi_rddata_dbi_w3   = {d_out_w3_q[(NUM_DQ*SWIDTH)+:(NUM_DQ*MWIDTH)]} ;
   assign o_dfi_rddata_valid_w3 = {d_out_w3_q[RWIDTH-1]} ;
   assign o_dfi_rddata_w4       = {d_out_w4_q[(NUM_DQ*SWIDTH)-1:0]} ;
   assign o_dfi_rddata_dbi_w4   = {d_out_w4_q[(NUM_DQ*SWIDTH)+:(NUM_DQ*MWIDTH)]} ;
   assign o_dfi_rddata_valid_w4 = {d_out_w4_q[RWIDTH-1]} ;
   assign o_dfi_rddata_w5       = {d_out_w5_q[(NUM_DQ*SWIDTH)-1:0]} ;
   assign o_dfi_rddata_dbi_w5   = {d_out_w5_q[(NUM_DQ*SWIDTH)+:(NUM_DQ*MWIDTH)]} ;
   assign o_dfi_rddata_valid_w5 = {d_out_w5_q[RWIDTH-1]} ;
   assign o_dfi_rddata_w6       = {d_out_w6_q[(NUM_DQ*SWIDTH)-1:0]} ;
   assign o_dfi_rddata_dbi_w6   = {d_out_w6_q[(NUM_DQ*SWIDTH)+:(NUM_DQ*MWIDTH)]} ;
   assign o_dfi_rddata_valid_w6 = {d_out_w6_q[RWIDTH-1]} ;
   assign o_dfi_rddata_w7       = {d_out_w7_q[(NUM_DQ*SWIDTH)-1:0]} ;
   assign o_dfi_rddata_dbi_w7   = {d_out_w7_q[(NUM_DQ*SWIDTH)+:(NUM_DQ*MWIDTH)]} ;
   assign o_dfi_rddata_valid_w7 = {d_out_w7_q[RWIDTH-1]} ;

   genvar j;
   generate
      for (j=0; j<(RWIDTH); j=j+1) begin : GEARBOX
         ddr_gearbox_up u_gearbox_up (
            .i_clk_1                             (i_clk_1  ),
            .i_clk_2                             (i_clk_2  ),
            .i_clk_3                             ('0),
            .i_d_0                              (d_in_w0[j]),
            .i_d_1                              (d_in_w1[j]),
            .i_d_2                              (d_in_w2[j]),
            .i_d_3                              (d_in_w3[j]),
            .i_d_4                              (d_in_w4[j]),
            .i_d_5                              (d_in_w5[j]),
            .i_d_6                              (d_in_w6[j]),
            .i_d_7                              (d_in_w7[j]),
            .o_d_p0                             (d_out_w0[j]),
            .o_d_p1                             (d_out_w1[j]),
            .o_d_p2                             (d_out_w2[j]),
            .o_d_p3                             (d_out_w3[j]),
            .o_d_p4                             (d_out_w4[j]),
            .o_d_p5                             (d_out_w5[j]),
            .o_d_p6                             (d_out_w6[j]),
            .o_d_p7                             (d_out_w7[j]),
            .i_gb_mode_sel                       (gb_mode_sel)
         );
      end
   endgenerate

   ddr_pipeline #(
      .DWIDTH      (RWIDTH)
   ) u_pipe_w0 (
      .i_clk       (i_dfi_clk),
      .i_pipe_en   ({RWIDTH{i_intf_pipe_en}}),
      .i_d         (d_out_w0),
      .o_q         (d_out_w0_q)
   );
   ddr_pipeline #(
      .DWIDTH      (RWIDTH)
   ) u_pipe_w1 (
      .i_clk       (i_dfi_clk),
      .i_pipe_en   ({RWIDTH{i_intf_pipe_en}}),
      .i_d         (d_out_w1),
      .o_q         (d_out_w1_q)
   );
   ddr_pipeline #(
      .DWIDTH      (RWIDTH)
   ) u_pipe_w2 (
      .i_clk       (i_dfi_clk),
      .i_pipe_en   ({RWIDTH{i_intf_pipe_en}}),
      .i_d         (d_out_w2),
      .o_q         (d_out_w2_q)
   );
   ddr_pipeline #(
      .DWIDTH      (RWIDTH)
   ) u_pipe_w3 (
      .i_clk       (i_dfi_clk),
      .i_pipe_en   ({RWIDTH{i_intf_pipe_en}}),
      .i_d         (d_out_w3),
      .o_q         (d_out_w3_q)
   );
   ddr_pipeline #(
      .DWIDTH      (RWIDTH)
   ) u_pipe_w4 (
      .i_clk       (i_dfi_clk),
      .i_pipe_en   ({RWIDTH{i_intf_pipe_en}}),
      .i_d         (d_out_w4),
      .o_q         (d_out_w4_q)
   );
   ddr_pipeline #(
      .DWIDTH      (RWIDTH)
   ) u_pipe_w5 (
      .i_clk       (i_dfi_clk),
      .i_pipe_en   ({RWIDTH{i_intf_pipe_en}}),
      .i_d         (d_out_w5),
      .o_q         (d_out_w5_q)
   );
   ddr_pipeline #(
      .DWIDTH      (RWIDTH)
   ) u_pipe_w6 (
      .i_clk       (i_dfi_clk),
      .i_pipe_en   ({RWIDTH{i_intf_pipe_en}}),
      .i_d         (d_out_w6),
      .o_q         (d_out_w6_q)
   );
   ddr_pipeline #(
      .DWIDTH      (RWIDTH)
   ) u_pipe_w7 (
      .i_clk       (i_dfi_clk),
      .i_pipe_en   ({RWIDTH{i_intf_pipe_en}}),
      .i_d         (d_out_w7),
      .o_q         (d_out_w7_q)
   );

endmodule

module ddr_gearbox_up (

   input  logic                i_clk_1,
   input  logic                i_clk_2,
   input  logic                i_clk_3,
   input  logic                i_d_0,
   input  logic                i_d_1,
   input  logic                i_d_2,
   input  logic                i_d_3,
   input  logic                i_d_4,
   input  logic                i_d_5,
   input  logic                i_d_6,
   input  logic                i_d_7,
   output logic                o_d_p0,
   output logic                o_d_p1,
   output logic                o_d_p2,
   output logic                o_d_p3,
   output logic                o_d_p4,
   output logic                o_d_p5,
   output logic                o_d_p6,
   output logic                o_d_p7,
   input  logic [2:0]          i_gb_mode_sel
);

   // Max support 4:32 and 8:32
   logic                                clk_1_b;
   logic                                clk_2_b;
   logic                                clk_3_b;
   logic sel_1to2, sel_1to4, sel_1to8;
   logic [8-1:0] d;
   logic [8-1:0] l1_d0  ;
   logic [8-1:0] l1_d1  ;
   logic [8-1:0] l1_d0_r;
   logic [8-1:0] l1_d0_f;
   logic [8-1:0] l1_d1_f;
   logic [8-1:0] l2_d0  ;
   logic [8-1:0] l2_d1  ;
   logic [8-1:0] l2_d2  ;
   logic [8-1:0] l2_d3  ;
   logic [8-1:0] l2_d0_r;
   logic [8-1:0] l2_d0_f;
   logic [8-1:0] l2_d1_r;
   logic [8-1:0] l2_d1_f;
   logic [8-1:0] l2_d2_r;
   logic [8-1:0] l2_d3_r;
   logic [8-1:0] l3_d0_r;
   logic [8-1:0] l3_d0_f;
   logic [8-1:0] l3_d1_r;
   logic [8-1:0] l3_d1_f;
   logic [8-1:0] l3_d2_r;
   logic [8-1:0] l3_d2_f;
   logic [8-1:0] l3_d3_r;
   logic [8-1:0] l3_d3_f;
   logic [8-1:0] l3_d4_f;
   logic [8-1:0] l3_d5_f;
   logic [8-1:0] l3_d6_f;
   logic [8-1:0] l3_d7_f;
   logic [8-1:0] d0;
   logic [8-1:0] d1;
   logic [8-1:0] d2;
   logic [8-1:0] d3;
   logic [8-1:0] d4;
   logic [8-1:0] d5;
   logic [8-1:0] d6;
   logic [8-1:0] d7;

   assign sel_1to2 = i_gb_mode_sel[0];
   assign sel_1to4 = i_gb_mode_sel[1];
   assign sel_1to8 = i_gb_mode_sel[2];

   assign d = {
                     i_d_7,
                     i_d_6,
                     i_d_5,
                     i_d_4,
                     i_d_3,
                     i_d_2,
                     i_d_1,
                     i_d_0
                   };

   ddr_inv clk_1_inv (.i_a(i_clk_1), .o_z(clk_1_b));
   ddr_inv clk_2_inv (.i_a(i_clk_2), .o_z(clk_2_b));
   ddr_inv clk_3_inv (.i_a(i_clk_3), .o_z(clk_3_b));

   assign d0 = d;

    assign o_d_p0 = d0[0];
    assign o_d_p1 = d0[1];
    assign o_d_p2 = d0[2];
    assign o_d_p3 = d0[3];
    assign o_d_p4 = d0[4];
    assign o_d_p5 = d0[5];
    assign o_d_p6 = d0[6];
    assign o_d_p7 = d0[7];

endmodule

module ddr_pipeline #(
   parameter DWIDTH          = 8
) (
   input  logic              i_clk,
   input  logic [DWIDTH-1:0] i_pipe_en,
   input  logic [DWIDTH-1:0] i_d,
   output logic [DWIDTH-1:0] o_q
);

   logic [DWIDTH-1:0] q;

   // Pipeline
   ddr_dff #(.DWIDTH(DWIDTH)) u_dff (.i_clk(i_clk), .i_d(i_d), .o_q(q));
   ddr_mux #(.DWIDTH(1)) u_clk_mux [DWIDTH-1:0] (.i_sel(i_pipe_en), .i_a(i_d), .i_b(q), .o_z(o_q));

endmodule

module ddr_dfi_ig_req_intf #(
   parameter POR_SW_ACK_HI = 0,
   parameter POR_SW_REQ_HI = 0,
   parameter POR_SW_REQ_LO = 0,
   parameter RH_EDGE_TRIG  = 1'b0,
   parameter CWIDTH        = 8      // Counter width
) (

   input  logic              i_clk,
   input  logic              i_rst,
   input  logic              i_req,
   output logic              o_req,
   output logic              o_ack,
   output logic              o_irq_ack,
   input  logic              i_event_0_en,
   input  logic              i_event_0,
   input  logic              i_event_1_en,
   input  logic              i_event_1,

   input  logic [CWIDTH-1:0] i_hw_event_0_cnt,
   input  logic [CWIDTH-1:0] i_hw_event_1_cnt,
   input  logic [CWIDTH-1:0] i_sw_event_0_cnt,
   input  logic [CWIDTH-1:0] i_sw_event_1_cnt,
   input  logic              i_sw_event_0_cnt_sel,
   input  logic              i_sw_event_1_cnt_sel,

   input  logic              i_sw_req_ovr,
   input  logic              i_sw_req_val,
   input  logic              i_sw_ack_ovr,
   input  logic              i_sw_ack_val,
   input  logic              i_sw_event_0_ovr,
   input  logic              i_sw_event_0_val,
   input  logic              i_sw_event_1_ovr,
   input  logic              i_sw_event_1_val

);

   // ------------------------------------------------------------------------
   // Demets and Edge Detects
   // ------------------------------------------------------------------------

   logic sw_req_ovr, sw_req_val, sw_ack_ovr, sw_ack_val;
   generate
     if(POR_SW_REQ_HI == 1) begin: REQ_RST_HI
        ddr_demet_s u_demet_0 (.i_clk(i_clk), .i_set(i_rst), .i_d(i_sw_req_ovr), .o_q(sw_req_ovr));
        ddr_demet_s u_demet_1 (.i_clk(i_clk), .i_set(i_rst), .i_d(i_sw_req_val), .o_q(sw_req_val));
     end else if(POR_SW_REQ_LO == 1) begin: REQ_RST_LO
        ddr_demet_s u_demet_0 (.i_clk(i_clk), .i_set(i_rst), .i_d(i_sw_req_ovr), .o_q(sw_req_ovr));
        ddr_demet_r u_demet_1 (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_sw_req_val), .o_q(sw_req_val));
     end else begin : NO_SW_REQ
        ddr_demet_r u_demet_0 (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_sw_req_ovr), .o_q(sw_req_ovr));
        ddr_demet_r u_demet_1 (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_sw_req_val), .o_q(sw_req_val));
     end
   endgenerate

   generate
     if(POR_SW_ACK_HI == 1) begin: ACK_RST_HI
        ddr_demet_s u_demet_2 (.i_clk(i_clk), .i_set(i_rst), .i_d(i_sw_ack_ovr), .o_q(sw_ack_ovr));
        ddr_demet_s u_demet_3 (.i_clk(i_clk), .i_set(i_rst), .i_d(i_sw_ack_val), .o_q(sw_ack_val));
     end else begin : ACK_RST_LO
        ddr_demet_r u_demet_2 (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_sw_ack_ovr), .o_q(sw_ack_ovr));
        ddr_demet_r u_demet_3 (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_sw_ack_val), .o_q(sw_ack_val));
     end
   endgenerate

   logic sw_event_0_ovr, sw_event_0_val, sw_event_1_ovr, sw_event_1_val;
   ddr_demet_r u_demet_4 (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_sw_event_0_ovr), .o_q(sw_event_0_ovr));
   ddr_demet_r u_demet_5 (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_sw_event_0_val), .o_q(sw_event_0_val));
   ddr_demet_r u_demet_6 (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_sw_event_1_ovr), .o_q(sw_event_1_ovr));
   ddr_demet_r u_demet_7 (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_sw_event_1_val), .o_q(sw_event_1_val));

   logic sw_event_0_cnt_sel, sw_event_1_cnt_sel;
   ddr_demet_r u_demet_8 (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_sw_event_0_cnt_sel), .o_q(sw_event_0_cnt_sel));
   ddr_demet_r u_demet_9 (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_sw_event_1_cnt_sel), .o_q(sw_event_1_cnt_sel));

   logic event_0_edge, event_1_edge;
   ddr_edge_det u_edge_det_0 (.i_clk(i_clk),.i_rst(i_rst),.i_async(i_event_0),.o_sync(event_0_edge),.o_sync_pulse());
   ddr_edge_det u_edge_det_1 (.i_clk(i_clk),.i_rst(i_rst),.i_async(i_event_1),.o_sync(event_1_edge),.o_sync_pulse());

   // ------------------------------------------------------------------------
   // Flops
   // ------------------------------------------------------------------------
   logic req, req_q, req_q1;
   logic req_asserted ;
   logic req_deasserted ;

   always_ff @(posedge i_clk, posedge i_rst)
      if (i_rst) begin
         req_q  <= POR_SW_REQ_HI ? 1'b1: 1'b0;
         req_q1 <= POR_SW_REQ_HI ? 1'b1: 1'b0;
      end else begin
         req_q  <= i_req;
         req_q1 <= req ;
      end

   assign req_deasserted = ~i_req & req_q ;
   assign req_asserted   = i_req & ~req_q ;

   // ------------------------------------------------------------------------
   // Software Overrides
   // ------------------------------------------------------------------------
   logic swreq_asserted ;
   logic event_0, event_1;
   logic ack_q;
   logic cnt_tc;

   assign req       = sw_req_ovr     ? sw_req_val     : req_q ;
   assign o_ack     = sw_ack_ovr     ? sw_ack_val     : ack_q ;
   assign o_irq_ack = ack_q ;
   assign event_0   = sw_event_0_ovr ? sw_event_0_val : i_event_0_en ? event_0_edge : cnt_tc;
   assign event_1   = sw_event_1_ovr ? sw_event_1_val : i_event_1_en ? event_1_edge : cnt_tc;

   assign o_req = req_q1;
   assign swreq_asserted = req & ~req_q1 ;

   // ------------------------------------------------------------------------
   // Counter Logic
   // ------------------------------------------------------------------------

   logic [CWIDTH-1:0] cnt_q;
   logic event_en, event_sel;
   logic [CWIDTH-1:0] hw_event_0_cnt;
   logic [CWIDTH-1:0] hw_event_1_cnt;
   logic [CWIDTH-1:0] event_0_cnt;
   logic [CWIDTH-1:0] event_1_cnt;

   always_ff @(posedge i_clk, posedge i_rst)
      if (i_rst) begin
         hw_event_0_cnt <= '0 ;
         hw_event_1_cnt <= '0 ;
      end else begin
         if(req_asserted)
           hw_event_0_cnt <= i_hw_event_0_cnt  ;
         if(req_deasserted)
           hw_event_1_cnt <= i_hw_event_1_cnt ;
      end

   assign event_0_cnt  = sw_event_0_cnt_sel ? i_sw_event_0_cnt : hw_event_0_cnt ;
   assign event_1_cnt  = sw_event_1_cnt_sel ? i_sw_event_1_cnt : hw_event_1_cnt ;

   // Counter
   always_ff @(posedge i_clk, posedge i_rst)
      if (i_rst)
         cnt_q <= '0;
      else
         if (event_en)
            cnt_q <= cnt_q - 'b1;
         else
            cnt_q <= event_sel ? event_1_cnt : event_0_cnt;

   // Terminal Count
   assign cnt_tc = cnt_q == '0;

   // ------------------------------------------------------------------------
   // FSM
   // ------------------------------------------------------------------------

   typedef enum logic [1:0] {
      AL = 2'b00,   // ACK Low
      RH = 2'b01,   // REQ High
      AH = 2'b11,   // ACK High
      RL = 2'b10    // REQ Low
   } fsm_t;

   fsm_t fsm_state_q, fsm_state_d;

   always_ff @(posedge i_clk, posedge i_rst)
      if (i_rst)
         fsm_state_q <= AL;
      else
         fsm_state_q <= fsm_state_d;

   always_comb begin
      event_sel   = '0;
      event_en    = '0;
      fsm_state_d = fsm_state_q;

      case(fsm_state_q)
         AL     : begin
                     if ((RH_EDGE_TRIG & swreq_asserted) || (!RH_EDGE_TRIG & req))
                        fsm_state_d = RH;
                  end
         RH     : begin
                     if (event_0)
                        fsm_state_d = AH;
                     else
                        event_en = 'b1;
                  end
         AH     : begin
                     if (!req_q1) begin
                        fsm_state_d = RL;
                        event_sel = 'b1;
                     end
                  end
         RL     : begin
                     if (event_1)
                        fsm_state_d = AL;
                     else
                        event_en = 'b1;
                  end
      endcase
   end

   // ------------------------------------------------------------------------
   // Output
   // ------------------------------------------------------------------------

   always_ff @(posedge i_clk, posedge i_rst)
      if (i_rst)
         ack_q <= '0;
      else
         if (fsm_state_d == AH)
            ack_q <= 1'b1;
         else if (fsm_state_d == AL)
            ack_q <= 1'b0;

endmodule

module ddr_dfi_eg_req_intf #(
   parameter CWIDTH = 8      // Counter width
) (

   input  logic              i_clk,
   input  logic              i_rst,
   input  logic              i_event,      // core side
   input  logic              i_req,        // core side
   output logic              o_ack,        // core side
   output logic              o_req,        // port side
   input  logic              i_ack,        // port side

   input  logic              i_sw_req_ovr,
   input  logic              i_sw_req_val,
   input  logic              i_sw_ack_ovr,
   input  logic              i_sw_ack_val,
   input  logic              i_sw_event_ovr,
   input  logic              i_sw_event_val

);

   // ------------------------------------------------------------------------
   // Demets
   // ------------------------------------------------------------------------

   logic sw_req_ovr, sw_req_val, sw_ack_ovr, sw_ack_val;
   ddr_demet_r u_demet_0 (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_sw_req_ovr), .o_q(sw_req_ovr));
   ddr_demet_r u_demet_1 (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_sw_req_val), .o_q(sw_req_val));
   ddr_demet_r u_demet_2 (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_sw_ack_ovr), .o_q(sw_ack_ovr));
   ddr_demet_r u_demet_3 (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_sw_ack_val), .o_q(sw_ack_val));

   logic sw_event_ovr, sw_event_val;
   ddr_demet_r u_demet_4 (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_sw_event_ovr), .o_q(sw_event_ovr));
   ddr_demet_r u_demet_5 (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_sw_event_val), .o_q(sw_event_val));

   // ------------------------------------------------------------------------
   // Flops
   // ------------------------------------------------------------------------
   logic ack, ack_q;

   always_ff @(posedge i_clk, posedge i_rst)
      if (i_rst)
         ack_q <= '0;
      else
         ack_q <= i_ack;

   // ------------------------------------------------------------------------
   // Software Overrides
   // ------------------------------------------------------------------------

   logic event_0;
   logic req;

   assign req     = sw_req_ovr   ? sw_req_val   : i_req  ;
   assign ack     = sw_ack_ovr   ? sw_ack_val   : ack_q  ;
   assign event_0 = sw_event_ovr ? sw_event_val : i_event;

   assign o_ack = ack;

   // ------------------------------------------------------------------------
   // FSM
   // ------------------------------------------------------------------------

   typedef enum logic [1:0] {
      AL = 2'b00,   // ACK Low
      RH = 2'b01,   // REQ High
      AH = 2'b11,   // ACK High
      RL = 2'b10    // REQ Low
   } fsm_t;

   fsm_t fsm_state_q, fsm_state_d;

   always_ff @(posedge i_clk, posedge i_rst)
      if (i_rst)
         fsm_state_q <= AL;
      else
         fsm_state_q <= fsm_state_d;

   always_comb begin
      fsm_state_d = fsm_state_q;

      case(fsm_state_q)
         AL     : begin
                     if (req)
                        fsm_state_d = RH;
                  end
         RH     : begin
                     if (ack)
                        fsm_state_d = AH;
                  end
         AH     : begin
                     if (event_0)
                        fsm_state_d = RL;
                  end
         RL     : begin
                     if (!ack)
                        fsm_state_d = AL;
                  end
      endcase
   end

   // ------------------------------------------------------------------------
   // Output
   // ------------------------------------------------------------------------

   logic req_q;

   always_ff @(posedge i_clk, posedge i_rst)
      if (i_rst)
         req_q <= '0;
      else
         if (fsm_state_d == RH)
            req_q <= 1'b1;
         else if (fsm_state_d == RL)
            req_q <= 1'b0;

   assign o_req = req_q;

endmodule
