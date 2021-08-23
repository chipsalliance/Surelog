
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

import ddr_global_pkg::*;

module ddr_phy_1x32 (

   // Reset
   input  logic                      i_phy_rst,

   // Clocks
   input  logic                      i_dfi_clk_on,
   output logic                      o_dfi_clk,

`ifdef DDR_ECO_ANA_REF_CLK
   input  logic                      i_ana_refclk,
`endif
   input  logic                      i_refclk,
   output logic                      o_refclk_on,
   input  logic                      i_refclk_alt,

   // Interrupts
   input  logic [3:0]                i_irq,
   output logic [1:0]                o_irq,


   // General Purpose Bus
   input  logic [7:0]                i_gpb,
   output logic [7:0]                o_gpb,


   // TEST
   input  logic                      i_scan_mode,
   input  logic                      i_scan_clk,
   input  logic                      i_scan_en,
   input  logic [7:0]                i_scan_freq_en,
   input  logic                      i_scan_cgc_ctrl,
   input  logic                      i_scan_rst_ctrl,
   input  logic                      i_scan_set_ctrl,
   input  logic [15:0]               i_scan,
   output logic [15:0]               o_scan,

   input  logic                      i_freeze_n,
   input  logic                      i_hiz_n,
   input  logic                      i_iddq_mode,
   output logic                      o_dtst,


   // JTAG Interface
   input  logic                      i_jtag_tck,
   input  logic                      i_jtag_trst_n,
   input  logic                      i_jtag_tms,
   input  logic                      i_jtag_tdi,
   output logic                      o_jtag_tdo,


   // AHB Interface
   input  logic                      i_ahb_clk,
   output logic                      o_ahb_clk_on,
   input  logic                      i_ahb_rst,
   input  logic                      i_ahb_csr_rst,

   // AHB Slave
   input  logic [31:0]               i_ahb_haddr,
   input  logic                      i_ahb_hwrite,
   input  logic                      i_ahb_hsel,
   input  logic [31:0]               i_ahb_hwdata,
   input  logic [1:0]                i_ahb_htrans,
   input  logic [2:0]                i_ahb_hsize,
   input  logic [2:0]                i_ahb_hburst,
   input  logic                      i_ahb_hreadyin,
   output logic                      o_ahb_hready,
   output logic [31:0]               o_ahb_hrdata,
   output logic [1:0]                o_ahb_hresp,

   // AHB Master
   output logic [31:0]               o_ahb_haddr,
   output logic                      o_ahb_hwrite,
   output logic [31:0]               o_ahb_hwdata,
   output logic [1:0]                o_ahb_htrans,
   output logic [2:0]                o_ahb_hsize,
   output logic [2:0]                o_ahb_hburst,
   output logic                      o_ahb_hbusreq,
   input  logic                      i_ahb_hgrant,
   input  logic                      i_ahb_hready,
   input  logic [31:0]               i_ahb_hrdata,
   input  logic [1:0]                i_ahb_hresp,

   //FIXME: DFI control interface aggregation logic missing for 2x16 config.
   // Update
   output logic                      o_dfi_ctrlupd_ack,
   input  logic                      i_dfi_ctrlupd_req,
   input  logic                      i_dfi_phyupd_ack,
   output logic                      o_dfi_phyupd_req,
   output logic [1:0]                o_dfi_phyupd_type,

   // Status
   input  logic [1:0]                i_dfi_freq_fsp,
   input  logic [1:0]                i_dfi_freq_ratio,
   input  logic [4:0]                i_dfi_frequency,
   output logic                      o_dfi_init_complete,
   input  logic                      i_dfi_init_start,

   // PHY Master
   input  logic                      i_dfi_phymstr_ack,
   output logic [1:0]                o_dfi_phymstr_cs_state,
   output logic                      o_dfi_phymstr_req,
   output logic                      o_dfi_phymstr_state_sel,
   output logic [1:0]                o_dfi_phymstr_type,

   // Low Power Control
   output logic                      o_dfi_lp_ctrl_ack,
   input  logic                      i_dfi_lp_ctrl_req,
   input  logic [5:0]                i_dfi_lp_ctrl_wakeup,
   output logic                      o_dfi_lp_data_ack,
   input  logic                      i_dfi_lp_data_req,
   input  logic [5:0]                i_dfi_lp_data_wakeup,

   // Command
   input  logic                      i_dfi_reset_n_p0,
   input  logic                      i_dfi_reset_n_p1,
   input  logic                      i_dfi_reset_n_p2,
   input  logic                      i_dfi_reset_n_p3,
   input  logic [13:0]               i_dfi_address_p0,
   input  logic [13:0]               i_dfi_address_p1,
   input  logic [13:0]               i_dfi_address_p2,
   input  logic [13:0]               i_dfi_address_p3,
   input  logic [1:0]                i_dfi_cke_p0,
   input  logic [1:0]                i_dfi_cke_p1,
   input  logic [1:0]                i_dfi_cke_p2,
   input  logic [1:0]                i_dfi_cke_p3,
   input  logic [1:0]                i_dfi_cs_p0,
   input  logic [1:0]                i_dfi_cs_p1,
   input  logic [1:0]                i_dfi_cs_p2,
   input  logic [1:0]                i_dfi_cs_p3,
   input  logic                      i_dfi_dram_clk_disable_p0,
   input  logic                      i_dfi_dram_clk_disable_p1,
   input  logic                      i_dfi_dram_clk_disable_p2,
   input  logic                      i_dfi_dram_clk_disable_p3,

   // Write
   input  logic [63:0]               i_dfi_wrdata_p0,
   input  logic [63:0]               i_dfi_wrdata_p1,
   input  logic [63:0]               i_dfi_wrdata_p2,
   input  logic [63:0]               i_dfi_wrdata_p3,
   input  logic                      i_dfi_parity_in_p0,
   input  logic                      i_dfi_parity_in_p1,
   input  logic                      i_dfi_parity_in_p2,
   input  logic                      i_dfi_parity_in_p3,
   input  logic [1:0]                i_dfi_wrdata_cs_p0,
   input  logic [1:0]                i_dfi_wrdata_cs_p1,
   input  logic [1:0]                i_dfi_wrdata_cs_p2,
   input  logic [1:0]                i_dfi_wrdata_cs_p3,
   input  logic [7:0]                i_dfi_wrdata_mask_p0,
   input  logic [7:0]                i_dfi_wrdata_mask_p1,
   input  logic [7:0]                i_dfi_wrdata_mask_p2,
   input  logic [7:0]                i_dfi_wrdata_mask_p3,
   input  logic                      i_dfi_wrdata_en_p0,
   input  logic                      i_dfi_wrdata_en_p1,
   input  logic                      i_dfi_wrdata_en_p2,
   input  logic                      i_dfi_wrdata_en_p3,
   input  logic [1:0]                i_dfi_wck_cs_p0,
   input  logic [1:0]                i_dfi_wck_cs_p1,
   input  logic [1:0]                i_dfi_wck_cs_p2,
   input  logic [1:0]                i_dfi_wck_cs_p3,
   input  logic                      i_dfi_wck_en_p0,
   input  logic                      i_dfi_wck_en_p1,
   input  logic                      i_dfi_wck_en_p2,
   input  logic                      i_dfi_wck_en_p3,
   input  logic [1:0]                i_dfi_wck_toggle_p0,
   input  logic [1:0]                i_dfi_wck_toggle_p1,
   input  logic [1:0]                i_dfi_wck_toggle_p2,
   input  logic [1:0]                i_dfi_wck_toggle_p3,

   // Read Data
   input  logic [1:0]                i_dfi_rddata_cs_p0,
   input  logic [1:0]                i_dfi_rddata_cs_p1,
   input  logic [1:0]                i_dfi_rddata_cs_p2,
   input  logic [1:0]                i_dfi_rddata_cs_p3,
   input  logic                      i_dfi_rddata_en_p0,
   input  logic                      i_dfi_rddata_en_p1,
   input  logic                      i_dfi_rddata_en_p2,
   input  logic                      i_dfi_rddata_en_p3,
   output logic [7:0]                o_dfi_rddata_dbi_w0,
   output logic [7:0]                o_dfi_rddata_dbi_w1,
   output logic [7:0]                o_dfi_rddata_dbi_w2,
   output logic [7:0]                o_dfi_rddata_dbi_w3,
   output logic [63:0]               o_dfi_rddata_w0,
   output logic [63:0]               o_dfi_rddata_w1,
   output logic [63:0]               o_dfi_rddata_w2,
   output logic [63:0]               o_dfi_rddata_w3,
   output logic                      o_dfi_rddata_valid_w0,
   output logic                      o_dfi_rddata_valid_w1,
   output logic                      o_dfi_rddata_valid_w2,
   output logic                      o_dfi_rddata_valid_w3,


   // Pads
   inout  wire                       pad_ddr_rext,
   inout  wire                       pad_ddr_test,
   inout  wire                       pad_ddr_reset_n,

   inout  wire                       pad_ch0_ddr_ca_ca0,
   inout  wire                       pad_ch0_ddr_ca_ca1,
   inout  wire                       pad_ch0_ddr_ca_ca2,
   inout  wire                       pad_ch0_ddr_ca_ca3,
   inout  wire                       pad_ch0_ddr_ca_ca4,
   inout  wire                       pad_ch0_ddr_ca_ca5,
   inout  wire                       pad_ch0_ddr_ca_ca6,
   inout  wire                       pad_ch0_ddr_ca_cs0,
   inout  wire                       pad_ch0_ddr_ca_cs1,
   inout  wire                       pad_ch0_ddr_ca_cke0,
   inout  wire                       pad_ch0_ddr_ca_cke1,
   inout  wire                       pad_ch0_ddr_ca_ck_c,
   inout  wire                       pad_ch0_ddr_ca_ck_t,

   inout  wire                       pad_ch0_ddr_dq0_dbim,
   inout  wire                       pad_ch0_ddr_dq0_dq0,
   inout  wire                       pad_ch0_ddr_dq0_dq1,
   inout  wire                       pad_ch0_ddr_dq0_dq2,
   inout  wire                       pad_ch0_ddr_dq0_dq3,
   inout  wire                       pad_ch0_ddr_dq0_dq4,
   inout  wire                       pad_ch0_ddr_dq0_dq5,
   inout  wire                       pad_ch0_ddr_dq0_dq6,
   inout  wire                       pad_ch0_ddr_dq0_dq7,
   inout  wire                       pad_ch0_ddr_dq0_wck_c,
   inout  wire                       pad_ch0_ddr_dq0_wck_t,
   inout  wire                       pad_ch0_ddr_dq0_dqs_c,
   inout  wire                       pad_ch0_ddr_dq0_dqs_t,
   inout  wire                       pad_ch0_ddr_dq1_dbim,
   inout  wire                       pad_ch0_ddr_dq1_dq0,
   inout  wire                       pad_ch0_ddr_dq1_dq1,
   inout  wire                       pad_ch0_ddr_dq1_dq2,
   inout  wire                       pad_ch0_ddr_dq1_dq3,
   inout  wire                       pad_ch0_ddr_dq1_dq4,
   inout  wire                       pad_ch0_ddr_dq1_dq5,
   inout  wire                       pad_ch0_ddr_dq1_dq6,
   inout  wire                       pad_ch0_ddr_dq1_dq7,
   inout  wire                       pad_ch0_ddr_dq1_wck_c,
   inout  wire                       pad_ch0_ddr_dq1_wck_t,
   inout  wire                       pad_ch0_ddr_dq1_dqs_c,
   inout  wire                       pad_ch0_ddr_dq1_dqs_t,
   inout  wire                       pad_ch1_ddr_ca_ca0,
   inout  wire                       pad_ch1_ddr_ca_ca1,
   inout  wire                       pad_ch1_ddr_ca_ca2,
   inout  wire                       pad_ch1_ddr_ca_ca3,
   inout  wire                       pad_ch1_ddr_ca_ca4,
   inout  wire                       pad_ch1_ddr_ca_ca5,
   inout  wire                       pad_ch1_ddr_ca_ca6,
   inout  wire                       pad_ch1_ddr_ca_cs0,
   inout  wire                       pad_ch1_ddr_ca_cs1,
   inout  wire                       pad_ch1_ddr_ca_cke0,
   inout  wire                       pad_ch1_ddr_ca_cke1,
   inout  wire                       pad_ch1_ddr_ca_ck_c,
   inout  wire                       pad_ch1_ddr_ca_ck_t,

   inout  wire                       pad_ch1_ddr_dq0_dbim,
   inout  wire                       pad_ch1_ddr_dq0_dq0,
   inout  wire                       pad_ch1_ddr_dq0_dq1,
   inout  wire                       pad_ch1_ddr_dq0_dq2,
   inout  wire                       pad_ch1_ddr_dq0_dq3,
   inout  wire                       pad_ch1_ddr_dq0_dq4,
   inout  wire                       pad_ch1_ddr_dq0_dq5,
   inout  wire                       pad_ch1_ddr_dq0_dq6,
   inout  wire                       pad_ch1_ddr_dq0_dq7,
   inout  wire                       pad_ch1_ddr_dq0_wck_c,
   inout  wire                       pad_ch1_ddr_dq0_wck_t,
   inout  wire                       pad_ch1_ddr_dq0_dqs_c,
   inout  wire                       pad_ch1_ddr_dq0_dqs_t,
   inout  wire                       pad_ch1_ddr_dq1_dbim,
   inout  wire                       pad_ch1_ddr_dq1_dq0,
   inout  wire                       pad_ch1_ddr_dq1_dq1,
   inout  wire                       pad_ch1_ddr_dq1_dq2,
   inout  wire                       pad_ch1_ddr_dq1_dq3,
   inout  wire                       pad_ch1_ddr_dq1_dq4,
   inout  wire                       pad_ch1_ddr_dq1_dq5,
   inout  wire                       pad_ch1_ddr_dq1_dq6,
   inout  wire                       pad_ch1_ddr_dq1_dq7,
   inout  wire                       pad_ch1_ddr_dq1_wck_c,
   inout  wire                       pad_ch1_ddr_dq1_wck_t,
   inout  wire                       pad_ch1_ddr_dq1_dqs_c,
   inout  wire                       pad_ch1_ddr_dq1_dqs_t,
   output logic [31:0]               o_debug
);

 // LS
   logic                             freeze_n_ls;
   logic                             freeze_n_ls_buf;
   logic [0:0]                       gpb_buf ;

  ddr_buf u_buf_vddd_domain (
   .i_a                              (gpb_buf[0]),
   .o_z                              (o_gpb[0])
  );

  ddr_ls_vddaon_wrapper u_phy_vddaon_ls (
   .i_freeze_n                       (i_freeze_n),
   .o_freeze_n_ls                    (freeze_n_ls)
  );

  ddr_vddaon_island u_phy_vddaon_island (
   .i_freeze_n                       (freeze_n_ls),
   .o_freeze_n                       (freeze_n_ls_buf)
  );

   // PHY Phases
   // Command
   logic                      dfi_reset_n_p0;
   logic                      dfi_reset_n_p1;
   logic                      dfi_reset_n_p2;
   logic                      dfi_reset_n_p3;
   logic                      dfi_reset_n_p4;
   logic                      dfi_reset_n_p5;
   logic                      dfi_reset_n_p6;
   logic                      dfi_reset_n_p7;
   logic [6:0]                dfi_address_p0;
   logic [6:0]                dfi_address_p1;
   logic [6:0]                dfi_address_p2;
   logic [6:0]                dfi_address_p3;
   logic [6:0]                dfi_address_p4;
   logic [6:0]                dfi_address_p5;
   logic [6:0]                dfi_address_p6;
   logic [6:0]                dfi_address_p7;
   logic [1:0]                dfi_cke_p0;
   logic [1:0]                dfi_cke_p1;
   logic [1:0]                dfi_cke_p2;
   logic [1:0]                dfi_cke_p3;
   logic [1:0]                dfi_cke_p4;
   logic [1:0]                dfi_cke_p5;
   logic [1:0]                dfi_cke_p6;
   logic [1:0]                dfi_cke_p7;
   logic [1:0]                dfi_cs_p0;
   logic [1:0]                dfi_cs_p1;
   logic [1:0]                dfi_cs_p2;
   logic [1:0]                dfi_cs_p3;
   logic [1:0]                dfi_cs_p4;
   logic [1:0]                dfi_cs_p5;
   logic [1:0]                dfi_cs_p6;
   logic [1:0]                dfi_cs_p7;
   logic                      dfi_dram_clk_disable_p0;
   logic                      dfi_dram_clk_disable_p1;
   logic                      dfi_dram_clk_disable_p2;
   logic                      dfi_dram_clk_disable_p3;
   logic                      dfi_dram_clk_disable_p4;
   logic                      dfi_dram_clk_disable_p5;
   logic                      dfi_dram_clk_disable_p6;
   logic                      dfi_dram_clk_disable_p7;

   logic [31:0]               dfi_wrdata_p0;
   logic [31:0]               dfi_wrdata_p1;
   logic [31:0]               dfi_wrdata_p2;
   logic [31:0]               dfi_wrdata_p3;
   logic [31:0]               dfi_wrdata_p4;
   logic [31:0]               dfi_wrdata_p5;
   logic [31:0]               dfi_wrdata_p6;
   logic [31:0]               dfi_wrdata_p7;
   logic                      dfi_parity_in_p0;
   logic                      dfi_parity_in_p1;
   logic                      dfi_parity_in_p2;
   logic                      dfi_parity_in_p3;
   logic                      dfi_parity_in_p4;
   logic                      dfi_parity_in_p5;
   logic                      dfi_parity_in_p6;
   logic                      dfi_parity_in_p7;
   logic [1:0]                dfi_wrdata_cs_p0;
   logic [1:0]                dfi_wrdata_cs_p1;
   logic [1:0]                dfi_wrdata_cs_p2;
   logic [1:0]                dfi_wrdata_cs_p3;
   logic [1:0]                dfi_wrdata_cs_p4;
   logic [1:0]                dfi_wrdata_cs_p5;
   logic [1:0]                dfi_wrdata_cs_p6;
   logic [1:0]                dfi_wrdata_cs_p7;
   logic [3:0]                dfi_wrdata_mask_p0;
   logic [3:0]                dfi_wrdata_mask_p1;
   logic [3:0]                dfi_wrdata_mask_p2;
   logic [3:0]                dfi_wrdata_mask_p3;
   logic [3:0]                dfi_wrdata_mask_p4;
   logic [3:0]                dfi_wrdata_mask_p5;
   logic [3:0]                dfi_wrdata_mask_p6;
   logic [3:0]                dfi_wrdata_mask_p7;
   logic                      dfi_wrdata_en_p0;
   logic                      dfi_wrdata_en_p1;
   logic                      dfi_wrdata_en_p2;
   logic                      dfi_wrdata_en_p3;
   logic                      dfi_wrdata_en_p4;
   logic                      dfi_wrdata_en_p5;
   logic                      dfi_wrdata_en_p6;
   logic                      dfi_wrdata_en_p7;
   logic [1:0]                dfi_wck_cs_p0;
   logic [1:0]                dfi_wck_cs_p1;
   logic [1:0]                dfi_wck_cs_p2;
   logic [1:0]                dfi_wck_cs_p3;
   logic [1:0]                dfi_wck_cs_p4;
   logic [1:0]                dfi_wck_cs_p5;
   logic [1:0]                dfi_wck_cs_p6;
   logic [1:0]                dfi_wck_cs_p7;
   logic                      dfi_wck_en_p0;
   logic                      dfi_wck_en_p1;
   logic                      dfi_wck_en_p2;
   logic                      dfi_wck_en_p3;
   logic                      dfi_wck_en_p4;
   logic                      dfi_wck_en_p5;
   logic                      dfi_wck_en_p6;
   logic                      dfi_wck_en_p7;
   logic [1:0]                dfi_wck_toggle_p0;
   logic [1:0]                dfi_wck_toggle_p1;
   logic [1:0]                dfi_wck_toggle_p2;
   logic [1:0]                dfi_wck_toggle_p3;
   logic [1:0]                dfi_wck_toggle_p4;
   logic [1:0]                dfi_wck_toggle_p5;
   logic [1:0]                dfi_wck_toggle_p6;
   logic [1:0]                dfi_wck_toggle_p7;

   // Read Data
   logic [31:0]               dfi_rddata_w0;
   logic [31:0]               dfi_rddata_w1;
   logic [31:0]               dfi_rddata_w2;
   logic [31:0]               dfi_rddata_w3;
   logic [31:0]               dfi_rddata_w4;
   logic [31:0]               dfi_rddata_w5;
   logic [31:0]               dfi_rddata_w6;
   logic [31:0]               dfi_rddata_w7;
   logic [1:0]                dfi_rddata_cs_p0;
   logic [1:0]                dfi_rddata_cs_p1;
   logic [1:0]                dfi_rddata_cs_p2;
   logic [1:0]                dfi_rddata_cs_p3;
   logic [1:0]                dfi_rddata_cs_p4;
   logic [1:0]                dfi_rddata_cs_p5;
   logic [1:0]                dfi_rddata_cs_p6;
   logic [1:0]                dfi_rddata_cs_p7;
   logic [3:0]                dfi_rddata_dbi_w0;
   logic [3:0]                dfi_rddata_dbi_w1;
   logic [3:0]                dfi_rddata_dbi_w2;
   logic [3:0]                dfi_rddata_dbi_w3;
   logic [3:0]                dfi_rddata_dbi_w4;
   logic [3:0]                dfi_rddata_dbi_w5;
   logic [3:0]                dfi_rddata_dbi_w6;
   logic [3:0]                dfi_rddata_dbi_w7;
   logic                      dfi_rddata_en_p0;
   logic                      dfi_rddata_en_p1;
   logic                      dfi_rddata_en_p2;
   logic                      dfi_rddata_en_p3;
   logic                      dfi_rddata_en_p4;
   logic                      dfi_rddata_en_p5;
   logic                      dfi_rddata_en_p6;
   logic                      dfi_rddata_en_p7;
   logic                      dfi_rddata_valid_w0;
   logic                      dfi_rddata_valid_w1;
   logic                      dfi_rddata_valid_w2;
   logic                      dfi_rddata_valid_w3;
   logic                      dfi_rddata_valid_w4;
   logic                      dfi_rddata_valid_w5;
   logic                      dfi_rddata_valid_w6;
   logic                      dfi_rddata_valid_w7;

   ddr_phy_dfi_mapper u_dfi_mapper (
      .i_dfi_reset_n_p0             (i_dfi_reset_n_p0),
      .i_dfi_reset_n_p1             (i_dfi_reset_n_p1),
      .i_dfi_reset_n_p2             (i_dfi_reset_n_p2),
      .i_dfi_reset_n_p3             (i_dfi_reset_n_p3),
      .i_dfi_address_p0             (i_dfi_address_p0),
      .i_dfi_cke_p0                 (i_dfi_cke_p0),
      .i_dfi_cs_p0                  (i_dfi_cs_p0),
      .i_dfi_dram_clk_disable_p0    (i_dfi_dram_clk_disable_p0),
      .i_dfi_address_p1             (i_dfi_address_p1),
      .i_dfi_cke_p1                 (i_dfi_cke_p1),
      .i_dfi_cs_p1                  (i_dfi_cs_p1),
      .i_dfi_dram_clk_disable_p1    (i_dfi_dram_clk_disable_p1),
      .i_dfi_address_p2             (i_dfi_address_p2),
      .i_dfi_cke_p2                 (i_dfi_cke_p2),
      .i_dfi_cs_p2                  (i_dfi_cs_p2),
      .i_dfi_dram_clk_disable_p2    (i_dfi_dram_clk_disable_p2),
      .i_dfi_address_p3             (i_dfi_address_p3),
      .i_dfi_cke_p3                 (i_dfi_cke_p3),
      .i_dfi_cs_p3                  (i_dfi_cs_p3),
      .i_dfi_dram_clk_disable_p3    (i_dfi_dram_clk_disable_p3),

      .i_dfi_wrdata_p0              (i_dfi_wrdata_p0),
      .i_dfi_parity_in_p0           (i_dfi_parity_in_p0),
      .i_dfi_wrdata_cs_p0           (i_dfi_wrdata_cs_p0),
      .i_dfi_wrdata_mask_p0         (i_dfi_wrdata_mask_p0),
      .i_dfi_wrdata_en_p0           (i_dfi_wrdata_en_p0),
      .i_dfi_wck_cs_p0              (i_dfi_wck_cs_p0),
      .i_dfi_wck_en_p0              (i_dfi_wck_en_p0),
      .i_dfi_wck_toggle_p0          (i_dfi_wck_toggle_p0),
      .i_dfi_rddata_cs_p0           (i_dfi_rddata_cs_p0),
      .i_dfi_rddata_en_p0           (i_dfi_rddata_en_p0),
      .i_dfi_wrdata_p1              (i_dfi_wrdata_p1),
      .i_dfi_parity_in_p1           (i_dfi_parity_in_p1),
      .i_dfi_wrdata_cs_p1           (i_dfi_wrdata_cs_p1),
      .i_dfi_wrdata_mask_p1         (i_dfi_wrdata_mask_p1),
      .i_dfi_wrdata_en_p1           (i_dfi_wrdata_en_p1),
      .i_dfi_wck_cs_p1              (i_dfi_wck_cs_p1),
      .i_dfi_wck_en_p1              (i_dfi_wck_en_p1),
      .i_dfi_wck_toggle_p1          (i_dfi_wck_toggle_p1),
      .i_dfi_rddata_cs_p1           (i_dfi_rddata_cs_p1),
      .i_dfi_rddata_en_p1           (i_dfi_rddata_en_p1),
      .i_dfi_wrdata_p2              (i_dfi_wrdata_p2),
      .i_dfi_parity_in_p2           (i_dfi_parity_in_p2),
      .i_dfi_wrdata_cs_p2           (i_dfi_wrdata_cs_p2),
      .i_dfi_wrdata_mask_p2         (i_dfi_wrdata_mask_p2),
      .i_dfi_wrdata_en_p2           (i_dfi_wrdata_en_p2),
      .i_dfi_wck_cs_p2              (i_dfi_wck_cs_p2),
      .i_dfi_wck_en_p2              (i_dfi_wck_en_p2),
      .i_dfi_wck_toggle_p2          (i_dfi_wck_toggle_p2),
      .i_dfi_rddata_cs_p2           (i_dfi_rddata_cs_p2),
      .i_dfi_rddata_en_p2           (i_dfi_rddata_en_p2),
      .i_dfi_wrdata_p3              (i_dfi_wrdata_p3),
      .i_dfi_parity_in_p3           (i_dfi_parity_in_p3),
      .i_dfi_wrdata_cs_p3           (i_dfi_wrdata_cs_p3),
      .i_dfi_wrdata_mask_p3         (i_dfi_wrdata_mask_p3),
      .i_dfi_wrdata_en_p3           (i_dfi_wrdata_en_p3),
      .i_dfi_wck_cs_p3              (i_dfi_wck_cs_p3),
      .i_dfi_wck_en_p3              (i_dfi_wck_en_p3),
      .i_dfi_wck_toggle_p3          (i_dfi_wck_toggle_p3),
      .i_dfi_rddata_cs_p3           (i_dfi_rddata_cs_p3),
      .i_dfi_rddata_en_p3           (i_dfi_rddata_en_p3),

      .o_dfi_rddata_w0              (o_dfi_rddata_w0),
      .o_dfi_rddata_dbi_w0          (o_dfi_rddata_dbi_w0),
      .o_dfi_rddata_valid_w0        (o_dfi_rddata_valid_w0),
      .o_dfi_rddata_w1              (o_dfi_rddata_w1),
      .o_dfi_rddata_dbi_w1          (o_dfi_rddata_dbi_w1),
      .o_dfi_rddata_valid_w1        (o_dfi_rddata_valid_w1),
      .o_dfi_rddata_w2              (o_dfi_rddata_w2),
      .o_dfi_rddata_dbi_w2          (o_dfi_rddata_dbi_w2),
      .o_dfi_rddata_valid_w2        (o_dfi_rddata_valid_w2),
      .o_dfi_rddata_w3              (o_dfi_rddata_w3),
      .o_dfi_rddata_dbi_w3          (o_dfi_rddata_dbi_w3),
      .o_dfi_rddata_valid_w3        (o_dfi_rddata_valid_w3),

      // PHY Phases
      .o_dfi_reset_n_p0             (dfi_reset_n_p0),
      .o_dfi_reset_n_p1             (dfi_reset_n_p1),
      .o_dfi_reset_n_p2             (dfi_reset_n_p2),
      .o_dfi_reset_n_p3             (dfi_reset_n_p3),
      .o_dfi_reset_n_p4             (dfi_reset_n_p4),
      .o_dfi_reset_n_p5             (dfi_reset_n_p5),
      .o_dfi_reset_n_p6             (dfi_reset_n_p6),
      .o_dfi_reset_n_p7             (dfi_reset_n_p7),
      .o_dfi_address_p0             (dfi_address_p0),
      .o_dfi_cke_p0                 (dfi_cke_p0),
      .o_dfi_cs_p0                  (dfi_cs_p0),
      .o_dfi_dram_clk_disable_p0    (dfi_dram_clk_disable_p0),
      .o_dfi_address_p1             (dfi_address_p1),
      .o_dfi_cke_p1                 (dfi_cke_p1),
      .o_dfi_cs_p1                  (dfi_cs_p1),
      .o_dfi_dram_clk_disable_p1    (dfi_dram_clk_disable_p1),
      .o_dfi_address_p2             (dfi_address_p2),
      .o_dfi_cke_p2                 (dfi_cke_p2),
      .o_dfi_cs_p2                  (dfi_cs_p2),
      .o_dfi_dram_clk_disable_p2    (dfi_dram_clk_disable_p2),
      .o_dfi_address_p3             (dfi_address_p3),
      .o_dfi_cke_p3                 (dfi_cke_p3),
      .o_dfi_cs_p3                  (dfi_cs_p3),
      .o_dfi_dram_clk_disable_p3    (dfi_dram_clk_disable_p3),
      .o_dfi_address_p4             (dfi_address_p4),
      .o_dfi_cke_p4                 (dfi_cke_p4),
      .o_dfi_cs_p4                  (dfi_cs_p4),
      .o_dfi_dram_clk_disable_p4    (dfi_dram_clk_disable_p4),
      .o_dfi_address_p5             (dfi_address_p5),
      .o_dfi_cke_p5                 (dfi_cke_p5),
      .o_dfi_cs_p5                  (dfi_cs_p5),
      .o_dfi_dram_clk_disable_p5    (dfi_dram_clk_disable_p5),
      .o_dfi_address_p6             (dfi_address_p6),
      .o_dfi_cke_p6                 (dfi_cke_p6),
      .o_dfi_cs_p6                  (dfi_cs_p6),
      .o_dfi_dram_clk_disable_p6    (dfi_dram_clk_disable_p6),
      .o_dfi_address_p7             (dfi_address_p7),
      .o_dfi_cke_p7                 (dfi_cke_p7),
      .o_dfi_cs_p7                  (dfi_cs_p7),
      .o_dfi_dram_clk_disable_p7    (dfi_dram_clk_disable_p7),

      .o_dfi_wrdata_p0              (dfi_wrdata_p0),
      .o_dfi_parity_in_p0           (dfi_parity_in_p0),
      .o_dfi_wrdata_cs_p0           (dfi_wrdata_cs_p0),
      .o_dfi_wrdata_mask_p0         (dfi_wrdata_mask_p0),
      .o_dfi_wrdata_en_p0           (dfi_wrdata_en_p0),
      .o_dfi_wck_cs_p0              (dfi_wck_cs_p0),
      .o_dfi_wck_en_p0              (dfi_wck_en_p0),
      .o_dfi_wck_toggle_p0          (dfi_wck_toggle_p0),
      .o_dfi_rddata_cs_p0           (dfi_rddata_cs_p0),
      .o_dfi_rddata_en_p0           (dfi_rddata_en_p0),
      .o_dfi_wrdata_p1              (dfi_wrdata_p1),
      .o_dfi_parity_in_p1           (dfi_parity_in_p1),
      .o_dfi_wrdata_cs_p1           (dfi_wrdata_cs_p1),
      .o_dfi_wrdata_mask_p1         (dfi_wrdata_mask_p1),
      .o_dfi_wrdata_en_p1           (dfi_wrdata_en_p1),
      .o_dfi_wck_cs_p1              (dfi_wck_cs_p1),
      .o_dfi_wck_en_p1              (dfi_wck_en_p1),
      .o_dfi_wck_toggle_p1          (dfi_wck_toggle_p1),
      .o_dfi_rddata_cs_p1           (dfi_rddata_cs_p1),
      .o_dfi_rddata_en_p1           (dfi_rddata_en_p1),
      .o_dfi_wrdata_p2              (dfi_wrdata_p2),
      .o_dfi_parity_in_p2           (dfi_parity_in_p2),
      .o_dfi_wrdata_cs_p2           (dfi_wrdata_cs_p2),
      .o_dfi_wrdata_mask_p2         (dfi_wrdata_mask_p2),
      .o_dfi_wrdata_en_p2           (dfi_wrdata_en_p2),
      .o_dfi_wck_cs_p2              (dfi_wck_cs_p2),
      .o_dfi_wck_en_p2              (dfi_wck_en_p2),
      .o_dfi_wck_toggle_p2          (dfi_wck_toggle_p2),
      .o_dfi_rddata_cs_p2           (dfi_rddata_cs_p2),
      .o_dfi_rddata_en_p2           (dfi_rddata_en_p2),
      .o_dfi_wrdata_p3              (dfi_wrdata_p3),
      .o_dfi_parity_in_p3           (dfi_parity_in_p3),
      .o_dfi_wrdata_cs_p3           (dfi_wrdata_cs_p3),
      .o_dfi_wrdata_mask_p3         (dfi_wrdata_mask_p3),
      .o_dfi_wrdata_en_p3           (dfi_wrdata_en_p3),
      .o_dfi_wck_cs_p3              (dfi_wck_cs_p3),
      .o_dfi_wck_en_p3              (dfi_wck_en_p3),
      .o_dfi_wck_toggle_p3          (dfi_wck_toggle_p3),
      .o_dfi_rddata_cs_p3           (dfi_rddata_cs_p3),
      .o_dfi_rddata_en_p3           (dfi_rddata_en_p3),
      .o_dfi_wrdata_p4              (dfi_wrdata_p4),
      .o_dfi_parity_in_p4           (dfi_parity_in_p4),
      .o_dfi_wrdata_cs_p4           (dfi_wrdata_cs_p4),
      .o_dfi_wrdata_mask_p4         (dfi_wrdata_mask_p4),
      .o_dfi_wrdata_en_p4           (dfi_wrdata_en_p4),
      .o_dfi_wck_cs_p4              (dfi_wck_cs_p4),
      .o_dfi_wck_en_p4              (dfi_wck_en_p4),
      .o_dfi_wck_toggle_p4          (dfi_wck_toggle_p4),
      .o_dfi_rddata_cs_p4           (dfi_rddata_cs_p4),
      .o_dfi_rddata_en_p4           (dfi_rddata_en_p4),
      .o_dfi_wrdata_p5              (dfi_wrdata_p5),
      .o_dfi_parity_in_p5           (dfi_parity_in_p5),
      .o_dfi_wrdata_cs_p5           (dfi_wrdata_cs_p5),
      .o_dfi_wrdata_mask_p5         (dfi_wrdata_mask_p5),
      .o_dfi_wrdata_en_p5           (dfi_wrdata_en_p5),
      .o_dfi_wck_cs_p5              (dfi_wck_cs_p5),
      .o_dfi_wck_en_p5              (dfi_wck_en_p5),
      .o_dfi_wck_toggle_p5          (dfi_wck_toggle_p5),
      .o_dfi_rddata_cs_p5           (dfi_rddata_cs_p5),
      .o_dfi_rddata_en_p5           (dfi_rddata_en_p5),
      .o_dfi_wrdata_p6              (dfi_wrdata_p6),
      .o_dfi_parity_in_p6           (dfi_parity_in_p6),
      .o_dfi_wrdata_cs_p6           (dfi_wrdata_cs_p6),
      .o_dfi_wrdata_mask_p6         (dfi_wrdata_mask_p6),
      .o_dfi_wrdata_en_p6           (dfi_wrdata_en_p6),
      .o_dfi_wck_cs_p6              (dfi_wck_cs_p6),
      .o_dfi_wck_en_p6              (dfi_wck_en_p6),
      .o_dfi_wck_toggle_p6          (dfi_wck_toggle_p6),
      .o_dfi_rddata_cs_p6           (dfi_rddata_cs_p6),
      .o_dfi_rddata_en_p6           (dfi_rddata_en_p6),
      .o_dfi_wrdata_p7              (dfi_wrdata_p7),
      .o_dfi_parity_in_p7           (dfi_parity_in_p7),
      .o_dfi_wrdata_cs_p7           (dfi_wrdata_cs_p7),
      .o_dfi_wrdata_mask_p7         (dfi_wrdata_mask_p7),
      .o_dfi_wrdata_en_p7           (dfi_wrdata_en_p7),
      .o_dfi_wck_cs_p7              (dfi_wck_cs_p7),
      .o_dfi_wck_en_p7              (dfi_wck_en_p7),
      .o_dfi_wck_toggle_p7          (dfi_wck_toggle_p7),
      .o_dfi_rddata_cs_p7           (dfi_rddata_cs_p7),
      .o_dfi_rddata_en_p7           (dfi_rddata_en_p7),

      .i_dfi_rddata_w0              (dfi_rddata_w0),
      .i_dfi_rddata_dbi_w0          (dfi_rddata_dbi_w0),
      .i_dfi_rddata_w1              (dfi_rddata_w1),
      .i_dfi_rddata_dbi_w1          (dfi_rddata_dbi_w1),
      .i_dfi_rddata_w2              (dfi_rddata_w2),
      .i_dfi_rddata_dbi_w2          (dfi_rddata_dbi_w2),
      .i_dfi_rddata_w3              (dfi_rddata_w3),
      .i_dfi_rddata_dbi_w3          (dfi_rddata_dbi_w3),
      .i_dfi_rddata_w4              (dfi_rddata_w4),
      .i_dfi_rddata_dbi_w4          (dfi_rddata_dbi_w4),
      .i_dfi_rddata_w5              (dfi_rddata_w5),
      .i_dfi_rddata_dbi_w5          (dfi_rddata_dbi_w5),
      .i_dfi_rddata_w6              (dfi_rddata_w6),
      .i_dfi_rddata_dbi_w6          (dfi_rddata_dbi_w6),
      .i_dfi_rddata_w7              (dfi_rddata_w7),
      .i_dfi_rddata_dbi_w7          (dfi_rddata_dbi_w7),
      .i_dfi_rddata_valid_w7        (dfi_rddata_valid_w7),
      .i_dfi_rddata_valid_w6        (dfi_rddata_valid_w6),
      .i_dfi_rddata_valid_w5        (dfi_rddata_valid_w5),
      .i_dfi_rddata_valid_w4        (dfi_rddata_valid_w4),
      .i_dfi_rddata_valid_w3        (dfi_rddata_valid_w3),
      .i_dfi_rddata_valid_w2        (dfi_rddata_valid_w2),
      .i_dfi_rddata_valid_w1        (dfi_rddata_valid_w1),
      .i_dfi_rddata_valid_w0        (dfi_rddata_valid_w0)
   );

   ddr_phy u_phy (

      .i_phy_rst                     (i_phy_rst),

      .i_dfi_clk_on                  (i_dfi_clk_on),
      .o_dfi_clk                     (o_dfi_clk),

`ifdef DDR_ECO_ANA_REF_CLK
      .i_ana_refclk                  (i_ana_refclk),
`endif
      .i_refclk                      (i_refclk),
      .o_refclk_on                   (o_refclk_on),
      .i_refclk_alt                  (i_refclk_alt),

      .i_irq                         (i_irq),
      .o_irq                         (o_irq),


      .i_gpb                         (i_gpb),
      .o_gpb                         ({o_gpb[7:1],gpb_buf[0]}),

      .i_pll_clk_0                   ('0),
      .i_pll_clk_90                  ('0),
      .i_pll_clk_180                 ('0),
      .i_pll_clk_270                 ('0),
      .i_vco0_clk                    ('0),

      .o_pll_clk_0                   (/*OPEN*/),
      .o_pll_clk_90                  (/*OPEN*/),
      .o_pll_clk_180                 (/*OPEN*/),
      .o_pll_clk_270                 (/*OPEN*/),
      .o_vco0_clk                    (/*OPEN*/),

      .i_scan_clk                    (i_scan_clk),
      .i_scan_mode                   (i_scan_mode),
      .i_scan_en                     (i_scan_en),
      .i_scan_freq_en                (i_scan_freq_en),
      .i_scan_cgc_ctrl               (i_scan_cgc_ctrl),
      .i_scan_rst_ctrl               (i_scan_rst_ctrl),
      .i_scan                        (i_scan),
      .o_scan                        (o_scan),

      .i_freeze_n                    (freeze_n_ls_buf),
      .i_hiz_n                       (i_hiz_n),
      .i_iddq_mode                   (i_iddq_mode),
      .o_dtst                        (o_dtst),

      .i_ret_en                      ('0),
      .i_hs_en                       ('0),

      .i_jtag_tck                    (i_jtag_tck),
      .i_jtag_trst_n                 (i_jtag_trst_n),
      .i_jtag_tms                    (i_jtag_tms),
      .i_jtag_tdi                    (i_jtag_tdi),
      .o_jtag_tdo                    (o_jtag_tdo),

      .i_ahb_clk                     (i_ahb_clk),
      .o_ahb_clk_on                  (o_ahb_clk_on),
      .i_ahb_rst                     (i_ahb_rst),
      .i_ahb_csr_rst                 (i_ahb_csr_rst),

      .i_ahb_haddr                   (i_ahb_haddr),
      .i_ahb_hwrite                  (i_ahb_hwrite),
      .i_ahb_hsel                    (i_ahb_hsel),
      .i_ahb_hwdata                  (i_ahb_hwdata),
      .i_ahb_htrans                  (i_ahb_htrans),
      .i_ahb_hsize                   (i_ahb_hsize),
      .i_ahb_hburst                  (i_ahb_hburst),
      .i_ahb_hreadyin                (i_ahb_hreadyin),
      .o_ahb_hready                  (o_ahb_hready),
      .o_ahb_hrdata                  (o_ahb_hrdata),
      .o_ahb_hresp                   (o_ahb_hresp),

      .o_ahb_haddr                   (o_ahb_haddr),
      .o_ahb_hwrite                  (o_ahb_hwrite),
      .o_ahb_hwdata                  (o_ahb_hwdata),
      .o_ahb_htrans                  (o_ahb_htrans),
      .o_ahb_hsize                   (o_ahb_hsize),
      .o_ahb_hburst                  (o_ahb_hburst),
      .o_ahb_hbusreq                 (o_ahb_hbusreq),
      .i_ahb_hgrant                  (i_ahb_hgrant),
      .i_ahb_hready                  (i_ahb_hready),
      .i_ahb_hrdata                  (i_ahb_hrdata),
      .i_ahb_hresp                   (i_ahb_hresp),

      .o_dfi_ctrlupd_ack             (o_dfi_ctrlupd_ack),
      .i_dfi_ctrlupd_req             (i_dfi_ctrlupd_req),
      .i_dfi_phyupd_ack              (i_dfi_phyupd_ack),
      .o_dfi_phyupd_req              (o_dfi_phyupd_req),
      .o_dfi_phyupd_type             (o_dfi_phyupd_type),

      .i_dfi_freq_fsp                (i_dfi_freq_fsp),
      .i_dfi_freq_ratio              (i_dfi_freq_ratio),
      .i_dfi_frequency               (i_dfi_frequency),
      .o_dfi_init_complete           (o_dfi_init_complete),
      .i_dfi_init_start              (i_dfi_init_start),

      .i_dfi_phymstr_ack             (i_dfi_phymstr_ack),
      .o_dfi_phymstr_cs_state        (o_dfi_phymstr_cs_state),
      .o_dfi_phymstr_req             (o_dfi_phymstr_req),
      .o_dfi_phymstr_state_sel       (o_dfi_phymstr_state_sel),
      .o_dfi_phymstr_type            (o_dfi_phymstr_type),



      .o_dfi_lp_ctrl_ack             (o_dfi_lp_ctrl_ack),
      .i_dfi_lp_ctrl_req             (i_dfi_lp_ctrl_req),
      .i_dfi_lp_ctrl_wakeup          (i_dfi_lp_ctrl_wakeup),
      .o_dfi_lp_data_ack             (o_dfi_lp_data_ack),
      .i_dfi_lp_data_req             (i_dfi_lp_data_req),
      .i_dfi_lp_data_wakeup          (i_dfi_lp_data_wakeup),


      .i_dfi_reset_n_p0              (dfi_reset_n_p0),
      .i_dfi_address_p0              (dfi_address_p0),
      .i_dfi_cke_p0                  (dfi_cke_p0),
      .i_dfi_cs_p0                   (dfi_cs_p0),
      .i_dfi_dram_clk_disable_p0     (dfi_dram_clk_disable_p0),
      .i_dfi_reset_n_p1              (dfi_reset_n_p1),
      .i_dfi_address_p1              (dfi_address_p1),
      .i_dfi_cke_p1                  (dfi_cke_p1),
      .i_dfi_cs_p1                   (dfi_cs_p1),
      .i_dfi_dram_clk_disable_p1     (dfi_dram_clk_disable_p1),
      .i_dfi_reset_n_p2              (dfi_reset_n_p2),
      .i_dfi_address_p2              (dfi_address_p2),
      .i_dfi_cke_p2                  (dfi_cke_p2),
      .i_dfi_cs_p2                   (dfi_cs_p2),
      .i_dfi_dram_clk_disable_p2     (dfi_dram_clk_disable_p2),
      .i_dfi_reset_n_p3              (dfi_reset_n_p3),
      .i_dfi_address_p3              (dfi_address_p3),
      .i_dfi_cke_p3                  (dfi_cke_p3),
      .i_dfi_cs_p3                   (dfi_cs_p3),
      .i_dfi_dram_clk_disable_p3     (dfi_dram_clk_disable_p3),
      .i_dfi_reset_n_p4              (dfi_reset_n_p4),
      .i_dfi_address_p4              (dfi_address_p4),
      .i_dfi_cke_p4                  (dfi_cke_p4),
      .i_dfi_cs_p4                   (dfi_cs_p4),
      .i_dfi_dram_clk_disable_p4     (dfi_dram_clk_disable_p4),
      .i_dfi_reset_n_p5              (dfi_reset_n_p5),
      .i_dfi_address_p5              (dfi_address_p5),
      .i_dfi_cke_p5                  (dfi_cke_p5),
      .i_dfi_cs_p5                   (dfi_cs_p5),
      .i_dfi_dram_clk_disable_p5     (dfi_dram_clk_disable_p5),
      .i_dfi_reset_n_p6              (dfi_reset_n_p6),
      .i_dfi_address_p6              (dfi_address_p6),
      .i_dfi_cke_p6                  (dfi_cke_p6),
      .i_dfi_cs_p6                   (dfi_cs_p6),
      .i_dfi_dram_clk_disable_p6     (dfi_dram_clk_disable_p6),
      .i_dfi_reset_n_p7              (dfi_reset_n_p7),
      .i_dfi_address_p7              (dfi_address_p7),
      .i_dfi_cke_p7                  (dfi_cke_p7),
      .i_dfi_cs_p7                   (dfi_cs_p7),
      .i_dfi_dram_clk_disable_p7     (dfi_dram_clk_disable_p7),

      .i_dfi_wrdata_p0               (dfi_wrdata_p0),
      .i_dfi_wrdata_mask_p0          (dfi_wrdata_mask_p0),
      .i_dfi_wrdata_cs_p0            (dfi_wrdata_cs_p0),
      .i_dfi_wrdata_en_p0            (dfi_wrdata_en_p0),
      .i_dfi_parity_in_p0            (dfi_parity_in_p0),
      .i_dfi_wck_cs_p0               (dfi_wck_cs_p0),
      .i_dfi_wck_en_p0               (dfi_wck_en_p0),
      .i_dfi_wck_toggle_p0           (dfi_wck_toggle_p0),
      .i_dfi_rddata_cs_p0            (dfi_rddata_cs_p0),
      .i_dfi_rddata_en_p0            (dfi_rddata_en_p0),
      .i_dfi_wrdata_p1               (dfi_wrdata_p1),
      .i_dfi_wrdata_mask_p1          (dfi_wrdata_mask_p1),
      .i_dfi_wrdata_cs_p1            (dfi_wrdata_cs_p1),
      .i_dfi_wrdata_en_p1            (dfi_wrdata_en_p1),
      .i_dfi_parity_in_p1            (dfi_parity_in_p1),
      .i_dfi_wck_cs_p1               (dfi_wck_cs_p1),
      .i_dfi_wck_en_p1               (dfi_wck_en_p1),
      .i_dfi_wck_toggle_p1           (dfi_wck_toggle_p1),
      .i_dfi_rddata_cs_p1            (dfi_rddata_cs_p1),
      .i_dfi_rddata_en_p1            (dfi_rddata_en_p1),
      .i_dfi_wrdata_p2               (dfi_wrdata_p2),
      .i_dfi_wrdata_mask_p2          (dfi_wrdata_mask_p2),
      .i_dfi_wrdata_cs_p2            (dfi_wrdata_cs_p2),
      .i_dfi_wrdata_en_p2            (dfi_wrdata_en_p2),
      .i_dfi_parity_in_p2            (dfi_parity_in_p2),
      .i_dfi_wck_cs_p2               (dfi_wck_cs_p2),
      .i_dfi_wck_en_p2               (dfi_wck_en_p2),
      .i_dfi_wck_toggle_p2           (dfi_wck_toggle_p2),
      .i_dfi_rddata_cs_p2            (dfi_rddata_cs_p2),
      .i_dfi_rddata_en_p2            (dfi_rddata_en_p2),
      .i_dfi_wrdata_p3               (dfi_wrdata_p3),
      .i_dfi_wrdata_mask_p3          (dfi_wrdata_mask_p3),
      .i_dfi_wrdata_cs_p3            (dfi_wrdata_cs_p3),
      .i_dfi_wrdata_en_p3            (dfi_wrdata_en_p3),
      .i_dfi_parity_in_p3            (dfi_parity_in_p3),
      .i_dfi_wck_cs_p3               (dfi_wck_cs_p3),
      .i_dfi_wck_en_p3               (dfi_wck_en_p3),
      .i_dfi_wck_toggle_p3           (dfi_wck_toggle_p3),
      .i_dfi_rddata_cs_p3            (dfi_rddata_cs_p3),
      .i_dfi_rddata_en_p3            (dfi_rddata_en_p3),
      .i_dfi_wrdata_p4               (dfi_wrdata_p4),
      .i_dfi_wrdata_mask_p4          (dfi_wrdata_mask_p4),
      .i_dfi_wrdata_cs_p4            (dfi_wrdata_cs_p4),
      .i_dfi_wrdata_en_p4            (dfi_wrdata_en_p4),
      .i_dfi_parity_in_p4            (dfi_parity_in_p4),
      .i_dfi_wck_cs_p4               (dfi_wck_cs_p4),
      .i_dfi_wck_en_p4               (dfi_wck_en_p4),
      .i_dfi_wck_toggle_p4           (dfi_wck_toggle_p4),
      .i_dfi_rddata_cs_p4            (dfi_rddata_cs_p4),
      .i_dfi_rddata_en_p4            (dfi_rddata_en_p4),
      .i_dfi_wrdata_p5               (dfi_wrdata_p5),
      .i_dfi_wrdata_mask_p5          (dfi_wrdata_mask_p5),
      .i_dfi_wrdata_cs_p5            (dfi_wrdata_cs_p5),
      .i_dfi_wrdata_en_p5            (dfi_wrdata_en_p5),
      .i_dfi_parity_in_p5            (dfi_parity_in_p5),
      .i_dfi_wck_cs_p5               (dfi_wck_cs_p5),
      .i_dfi_wck_en_p5               (dfi_wck_en_p5),
      .i_dfi_wck_toggle_p5           (dfi_wck_toggle_p5),
      .i_dfi_rddata_cs_p5            (dfi_rddata_cs_p5),
      .i_dfi_rddata_en_p5            (dfi_rddata_en_p5),
      .i_dfi_wrdata_p6               (dfi_wrdata_p6),
      .i_dfi_wrdata_mask_p6          (dfi_wrdata_mask_p6),
      .i_dfi_wrdata_cs_p6            (dfi_wrdata_cs_p6),
      .i_dfi_wrdata_en_p6            (dfi_wrdata_en_p6),
      .i_dfi_parity_in_p6            (dfi_parity_in_p6),
      .i_dfi_wck_cs_p6               (dfi_wck_cs_p6),
      .i_dfi_wck_en_p6               (dfi_wck_en_p6),
      .i_dfi_wck_toggle_p6           (dfi_wck_toggle_p6),
      .i_dfi_rddata_cs_p6            (dfi_rddata_cs_p6),
      .i_dfi_rddata_en_p6            (dfi_rddata_en_p6),
      .i_dfi_wrdata_p7               (dfi_wrdata_p7),
      .i_dfi_wrdata_mask_p7          (dfi_wrdata_mask_p7),
      .i_dfi_wrdata_cs_p7            (dfi_wrdata_cs_p7),
      .i_dfi_wrdata_en_p7            (dfi_wrdata_en_p7),
      .i_dfi_parity_in_p7            (dfi_parity_in_p7),
      .i_dfi_wck_cs_p7               (dfi_wck_cs_p7),
      .i_dfi_wck_en_p7               (dfi_wck_en_p7),
      .i_dfi_wck_toggle_p7           (dfi_wck_toggle_p7),
      .i_dfi_rddata_cs_p7            (dfi_rddata_cs_p7),
      .i_dfi_rddata_en_p7            (dfi_rddata_en_p7),
      .o_dfi_rddata_w0               (dfi_rddata_w0),
      .o_dfi_rddata_dbi_w0           (dfi_rddata_dbi_w0),
      .o_dfi_rddata_valid_w0         (dfi_rddata_valid_w0),
      .o_dfi_rddata_w1               (dfi_rddata_w1),
      .o_dfi_rddata_dbi_w1           (dfi_rddata_dbi_w1),
      .o_dfi_rddata_valid_w1         (dfi_rddata_valid_w1),
      .o_dfi_rddata_w2               (dfi_rddata_w2),
      .o_dfi_rddata_dbi_w2           (dfi_rddata_dbi_w2),
      .o_dfi_rddata_valid_w2         (dfi_rddata_valid_w2),
      .o_dfi_rddata_w3               (dfi_rddata_w3),
      .o_dfi_rddata_dbi_w3           (dfi_rddata_dbi_w3),
      .o_dfi_rddata_valid_w3         (dfi_rddata_valid_w3),
      .o_dfi_rddata_w4               (dfi_rddata_w4),
      .o_dfi_rddata_dbi_w4           (dfi_rddata_dbi_w4),
      .o_dfi_rddata_valid_w4         (dfi_rddata_valid_w4),
      .o_dfi_rddata_w5               (dfi_rddata_w5),
      .o_dfi_rddata_dbi_w5           (dfi_rddata_dbi_w5),
      .o_dfi_rddata_valid_w5         (dfi_rddata_valid_w5),
      .o_dfi_rddata_w6               (dfi_rddata_w6),
      .o_dfi_rddata_dbi_w6           (dfi_rddata_dbi_w6),
      .o_dfi_rddata_valid_w6         (dfi_rddata_valid_w6),
      .o_dfi_rddata_w7               (dfi_rddata_w7),
      .o_dfi_rddata_dbi_w7           (dfi_rddata_dbi_w7),
      .o_dfi_rddata_valid_w7         (dfi_rddata_valid_w7),

      .i_txrx_mode                         ('0),
      .i_ch0_tx0_sdr                 ('0),
      .i_ch0_tx_ck0_sdr              ('0),
      .o_ch0_rx0_sdr                 (/*OPEN*/),
      .o_ch0_rx0_sdr_vld             (/*OPEN*/),
      .i_ch0_tx1_sdr                 ('0),
      .i_ch0_tx_ck1_sdr              ('0),
      .o_ch0_rx1_sdr                 (/*OPEN*/),
      .o_ch0_rx1_sdr_vld             (/*OPEN*/),
      .i_ch1_tx0_sdr                 ('0),
      .i_ch1_tx_ck0_sdr              ('0),
      .o_ch1_rx0_sdr                 (/*OPEN*/),
      .o_ch1_rx0_sdr_vld             (/*OPEN*/),
      .i_ch1_tx1_sdr                 ('0),
      .i_ch1_tx_ck1_sdr              ('0),
      .o_ch1_rx1_sdr                 (/*OPEN*/),
      .o_ch1_rx1_sdr_vld             (/*OPEN*/),

      .pad_rext                      (pad_ddr_rext),
      .pad_test                      (pad_ddr_test),
      .pad_reset_n                   (pad_ddr_reset_n),

      .pad_ch0_ck_t                  (pad_ch0_ddr_ca_ck_t),
      .pad_ch0_ck_c                  (pad_ch0_ddr_ca_ck_c),
      .pad_ch0_ca                    ({
                                       pad_ch0_ddr_ca_cke1,
                                       pad_ch0_ddr_ca_cke0,
                                       pad_ch0_ddr_ca_cs1,
                                       pad_ch0_ddr_ca_cs0,
                                       pad_ch0_ddr_ca_ca6,
                                       pad_ch0_ddr_ca_ca5,
                                       pad_ch0_ddr_ca_ca4,
                                       pad_ch0_ddr_ca_ca3,
                                       pad_ch0_ddr_ca_ca2,
                                       pad_ch0_ddr_ca_ca1,
                                       pad_ch0_ddr_ca_ca0
                                    }),
      .pad_ch0_wck_t                 ({
                                       pad_ch0_ddr_dq1_wck_t,
                                       pad_ch0_ddr_dq0_wck_t
                                     }),
      .pad_ch0_wck_c                 ({
                                       pad_ch0_ddr_dq1_wck_c,
                                       pad_ch0_ddr_dq0_wck_c
                                     }),
      .pad_ch0_dqs_t                 ({
                                       pad_ch0_ddr_dq1_dqs_t,
                                       pad_ch0_ddr_dq0_dqs_t
                                     }),
      .pad_ch0_dqs_c                 ({
                                       pad_ch0_ddr_dq1_dqs_c,
                                       pad_ch0_ddr_dq0_dqs_c
                                     }),
      .pad_ch0_dq                    ({
                                       pad_ch0_ddr_dq1_dbim,
                                       pad_ch0_ddr_dq1_dq7,
                                       pad_ch0_ddr_dq1_dq6,
                                       pad_ch0_ddr_dq1_dq5,
                                       pad_ch0_ddr_dq1_dq4,
                                       pad_ch0_ddr_dq1_dq3,
                                       pad_ch0_ddr_dq1_dq2,
                                       pad_ch0_ddr_dq1_dq1,
                                       pad_ch0_ddr_dq1_dq0,
                                       pad_ch0_ddr_dq0_dbim,
                                       pad_ch0_ddr_dq0_dq7,
                                       pad_ch0_ddr_dq0_dq6,
                                       pad_ch0_ddr_dq0_dq5,
                                       pad_ch0_ddr_dq0_dq4,
                                       pad_ch0_ddr_dq0_dq3,
                                       pad_ch0_ddr_dq0_dq2,
                                       pad_ch0_ddr_dq0_dq1,
                                       pad_ch0_ddr_dq0_dq0
                                     }),
      .pad_ch1_ck_t                  (pad_ch1_ddr_ca_ck_t),
      .pad_ch1_ck_c                  (pad_ch1_ddr_ca_ck_c),
      .pad_ch1_ca                    ({
                                       pad_ch1_ddr_ca_cke1,
                                       pad_ch1_ddr_ca_cke0,
                                       pad_ch1_ddr_ca_cs1,
                                       pad_ch1_ddr_ca_cs0,
                                       pad_ch1_ddr_ca_ca6,
                                       pad_ch1_ddr_ca_ca5,
                                       pad_ch1_ddr_ca_ca4,
                                       pad_ch1_ddr_ca_ca3,
                                       pad_ch1_ddr_ca_ca2,
                                       pad_ch1_ddr_ca_ca1,
                                       pad_ch1_ddr_ca_ca0
                                    }),
      .pad_ch1_wck_t                 ({
                                       pad_ch1_ddr_dq1_wck_t,
                                       pad_ch1_ddr_dq0_wck_t
                                     }),
      .pad_ch1_wck_c                 ({
                                       pad_ch1_ddr_dq1_wck_c,
                                       pad_ch1_ddr_dq0_wck_c
                                     }),
      .pad_ch1_dqs_t                 ({
                                       pad_ch1_ddr_dq1_dqs_t,
                                       pad_ch1_ddr_dq0_dqs_t
                                     }),
      .pad_ch1_dqs_c                 ({
                                       pad_ch1_ddr_dq1_dqs_c,
                                       pad_ch1_ddr_dq0_dqs_c
                                     }),
      .pad_ch1_dq                    ({
                                       pad_ch1_ddr_dq1_dbim,
                                       pad_ch1_ddr_dq1_dq7,
                                       pad_ch1_ddr_dq1_dq6,
                                       pad_ch1_ddr_dq1_dq5,
                                       pad_ch1_ddr_dq1_dq4,
                                       pad_ch1_ddr_dq1_dq3,
                                       pad_ch1_ddr_dq1_dq2,
                                       pad_ch1_ddr_dq1_dq1,
                                       pad_ch1_ddr_dq1_dq0,
                                       pad_ch1_ddr_dq0_dbim,
                                       pad_ch1_ddr_dq0_dq7,
                                       pad_ch1_ddr_dq0_dq6,
                                       pad_ch1_ddr_dq0_dq5,
                                       pad_ch1_ddr_dq0_dq4,
                                       pad_ch1_ddr_dq0_dq3,
                                       pad_ch1_ddr_dq0_dq2,
                                       pad_ch1_ddr_dq0_dq1,
                                       pad_ch1_ddr_dq0_dq0
                                     }),
      .o_debug                       (o_debug)
   );

`ifndef SYNTHESIS
`ifdef DDR_TRACE
   initial begin
      $dumpfile("ddr_phy_1x32.vcd");
      $dumpvars(1, ddr_phy_1x32);
      $dumpon;
   end
 `endif // DDR_TRACE
`endif // SYNTHESIS

endmodule

module ddr_phy_dfi_mapper (

   // DFI SPEC Phases
   input  logic                     i_dfi_reset_n_p0,
   input  logic                     i_dfi_reset_n_p1,
   input  logic                     i_dfi_reset_n_p2,
   input  logic                     i_dfi_reset_n_p3,
   // Command
   input  logic [13:0]               i_dfi_address_p0,
   input  logic [13:0]               i_dfi_address_p1,
   input  logic [13:0]               i_dfi_address_p2,
   input  logic [13:0]               i_dfi_address_p3,
   input  logic [1:0]                i_dfi_cke_p0,
   input  logic [1:0]                i_dfi_cke_p1,
   input  logic [1:0]                i_dfi_cke_p2,
   input  logic [1:0]                i_dfi_cke_p3,
   input  logic [1:0]                i_dfi_cs_p0,
   input  logic [1:0]                i_dfi_cs_p1,
   input  logic [1:0]                i_dfi_cs_p2,
   input  logic [1:0]                i_dfi_cs_p3,
   input  logic                      i_dfi_dram_clk_disable_p0,
   input  logic                      i_dfi_dram_clk_disable_p1,
   input  logic                      i_dfi_dram_clk_disable_p2,
   input  logic                      i_dfi_dram_clk_disable_p3,

   // Write
   input  logic [63:0]               i_dfi_wrdata_p0,
   input  logic [63:0]               i_dfi_wrdata_p1,
   input  logic [63:0]               i_dfi_wrdata_p2,
   input  logic [63:0]               i_dfi_wrdata_p3,
   input  logic                      i_dfi_parity_in_p0,
   input  logic                      i_dfi_parity_in_p1,
   input  logic                      i_dfi_parity_in_p2,
   input  logic                      i_dfi_parity_in_p3,
   input  logic [1:0]                i_dfi_wrdata_cs_p0,
   input  logic [1:0]                i_dfi_wrdata_cs_p1,
   input  logic [1:0]                i_dfi_wrdata_cs_p2,
   input  logic [1:0]                i_dfi_wrdata_cs_p3,
   input  logic [7:0]                i_dfi_wrdata_mask_p0,
   input  logic [7:0]                i_dfi_wrdata_mask_p1,
   input  logic [7:0]                i_dfi_wrdata_mask_p2,
   input  logic [7:0]                i_dfi_wrdata_mask_p3,
   input  logic                      i_dfi_wrdata_en_p0,
   input  logic                      i_dfi_wrdata_en_p1,
   input  logic                      i_dfi_wrdata_en_p2,
   input  logic                      i_dfi_wrdata_en_p3,
   input  logic [1:0]                i_dfi_wck_cs_p0,
   input  logic [1:0]                i_dfi_wck_cs_p1,
   input  logic [1:0]                i_dfi_wck_cs_p2,
   input  logic [1:0]                i_dfi_wck_cs_p3,
   input  logic                      i_dfi_wck_en_p0,
   input  logic                      i_dfi_wck_en_p1,
   input  logic                      i_dfi_wck_en_p2,
   input  logic                      i_dfi_wck_en_p3,
   input  logic [1:0]                i_dfi_wck_toggle_p0,
   input  logic [1:0]                i_dfi_wck_toggle_p1,
   input  logic [1:0]                i_dfi_wck_toggle_p2,
   input  logic [1:0]                i_dfi_wck_toggle_p3,

   // Read Data
   output logic [63:0]               o_dfi_rddata_w0,
   output logic [63:0]               o_dfi_rddata_w1,
   output logic [63:0]               o_dfi_rddata_w2,
   output logic [63:0]               o_dfi_rddata_w3,
   input  logic [1:0]                i_dfi_rddata_cs_p0,
   input  logic [1:0]                i_dfi_rddata_cs_p1,
   input  logic [1:0]                i_dfi_rddata_cs_p2,
   input  logic [1:0]                i_dfi_rddata_cs_p3,
   output logic [7:0]                o_dfi_rddata_dbi_w0,
   output logic [7:0]                o_dfi_rddata_dbi_w1,
   output logic [7:0]                o_dfi_rddata_dbi_w2,
   output logic [7:0]                o_dfi_rddata_dbi_w3,
   input  logic                      i_dfi_rddata_en_p0,
   input  logic                      i_dfi_rddata_en_p1,
   input  logic                      i_dfi_rddata_en_p2,
   input  logic                      i_dfi_rddata_en_p3,
   output logic                      o_dfi_rddata_valid_w0,
   output logic                      o_dfi_rddata_valid_w1,
   output logic                      o_dfi_rddata_valid_w2,
   output logic                      o_dfi_rddata_valid_w3,

   // PHY Phases
   // Command
   output logic                      o_dfi_reset_n_p0,
   output logic                      o_dfi_reset_n_p1,
   output logic                      o_dfi_reset_n_p2,
   output logic                      o_dfi_reset_n_p3,
   output logic                      o_dfi_reset_n_p4,
   output logic                      o_dfi_reset_n_p5,
   output logic                      o_dfi_reset_n_p6,
   output logic                      o_dfi_reset_n_p7,
   output logic [6:0]                o_dfi_address_p0,
   output logic [6:0]                o_dfi_address_p1,
   output logic [6:0]                o_dfi_address_p2,
   output logic [6:0]                o_dfi_address_p3,
   output logic [6:0]                o_dfi_address_p4,
   output logic [6:0]                o_dfi_address_p5,
   output logic [6:0]                o_dfi_address_p6,
   output logic [6:0]                o_dfi_address_p7,
   output logic [1:0]                o_dfi_cke_p0,
   output logic [1:0]                o_dfi_cke_p1,
   output logic [1:0]                o_dfi_cke_p2,
   output logic [1:0]                o_dfi_cke_p3,
   output logic [1:0]                o_dfi_cke_p4,
   output logic [1:0]                o_dfi_cke_p5,
   output logic [1:0]                o_dfi_cke_p6,
   output logic [1:0]                o_dfi_cke_p7,
   output logic [1:0]                o_dfi_cs_p0,
   output logic [1:0]                o_dfi_cs_p1,
   output logic [1:0]                o_dfi_cs_p2,
   output logic [1:0]                o_dfi_cs_p3,
   output logic [1:0]                o_dfi_cs_p4,
   output logic [1:0]                o_dfi_cs_p5,
   output logic [1:0]                o_dfi_cs_p6,
   output logic [1:0]                o_dfi_cs_p7,
   output logic                      o_dfi_dram_clk_disable_p0,
   output logic                      o_dfi_dram_clk_disable_p1,
   output logic                      o_dfi_dram_clk_disable_p2,
   output logic                      o_dfi_dram_clk_disable_p3,
   output logic                      o_dfi_dram_clk_disable_p4,
   output logic                      o_dfi_dram_clk_disable_p5,
   output logic                      o_dfi_dram_clk_disable_p6,
   output logic                      o_dfi_dram_clk_disable_p7,


   // Write
   output logic [31:0]               o_dfi_wrdata_p0,
   output logic [31:0]               o_dfi_wrdata_p1,
   output logic [31:0]               o_dfi_wrdata_p2,
   output logic [31:0]               o_dfi_wrdata_p3,
   output logic [31:0]               o_dfi_wrdata_p4,
   output logic [31:0]               o_dfi_wrdata_p5,
   output logic [31:0]               o_dfi_wrdata_p6,
   output logic [31:0]               o_dfi_wrdata_p7,
   output logic                      o_dfi_parity_in_p0,
   output logic                      o_dfi_parity_in_p1,
   output logic                      o_dfi_parity_in_p2,
   output logic                      o_dfi_parity_in_p3,
   output logic                      o_dfi_parity_in_p4,
   output logic                      o_dfi_parity_in_p5,
   output logic                      o_dfi_parity_in_p6,
   output logic                      o_dfi_parity_in_p7,
   output logic [1:0]                o_dfi_wrdata_cs_p0,
   output logic [1:0]                o_dfi_wrdata_cs_p1,
   output logic [1:0]                o_dfi_wrdata_cs_p2,
   output logic [1:0]                o_dfi_wrdata_cs_p3,
   output logic [1:0]                o_dfi_wrdata_cs_p4,
   output logic [1:0]                o_dfi_wrdata_cs_p5,
   output logic [1:0]                o_dfi_wrdata_cs_p6,
   output logic [1:0]                o_dfi_wrdata_cs_p7,
   output logic [3:0]                o_dfi_wrdata_mask_p0,
   output logic [3:0]                o_dfi_wrdata_mask_p1,
   output logic [3:0]                o_dfi_wrdata_mask_p2,
   output logic [3:0]                o_dfi_wrdata_mask_p3,
   output logic [3:0]                o_dfi_wrdata_mask_p4,
   output logic [3:0]                o_dfi_wrdata_mask_p5,
   output logic [3:0]                o_dfi_wrdata_mask_p6,
   output logic [3:0]                o_dfi_wrdata_mask_p7,
   output logic                      o_dfi_wrdata_en_p0,
   output logic                      o_dfi_wrdata_en_p1,
   output logic                      o_dfi_wrdata_en_p2,
   output logic                      o_dfi_wrdata_en_p3,
   output logic                      o_dfi_wrdata_en_p4,
   output logic                      o_dfi_wrdata_en_p5,
   output logic                      o_dfi_wrdata_en_p6,
   output logic                      o_dfi_wrdata_en_p7,
   output logic [1:0]                o_dfi_wck_cs_p0,
   output logic [1:0]                o_dfi_wck_cs_p1,
   output logic [1:0]                o_dfi_wck_cs_p2,
   output logic [1:0]                o_dfi_wck_cs_p3,
   output logic [1:0]                o_dfi_wck_cs_p4,
   output logic [1:0]                o_dfi_wck_cs_p5,
   output logic [1:0]                o_dfi_wck_cs_p6,
   output logic [1:0]                o_dfi_wck_cs_p7,
   output logic                      o_dfi_wck_en_p0,
   output logic                      o_dfi_wck_en_p1,
   output logic                      o_dfi_wck_en_p2,
   output logic                      o_dfi_wck_en_p3,
   output logic                      o_dfi_wck_en_p4,
   output logic                      o_dfi_wck_en_p5,
   output logic                      o_dfi_wck_en_p6,
   output logic                      o_dfi_wck_en_p7,
   output logic [1:0]                o_dfi_wck_toggle_p0,
   output logic [1:0]                o_dfi_wck_toggle_p1,
   output logic [1:0]                o_dfi_wck_toggle_p2,
   output logic [1:0]                o_dfi_wck_toggle_p3,
   output logic [1:0]                o_dfi_wck_toggle_p4,
   output logic [1:0]                o_dfi_wck_toggle_p5,
   output logic [1:0]                o_dfi_wck_toggle_p6,
   output logic [1:0]                o_dfi_wck_toggle_p7,

   // Read Data
   output logic                      o_dfi_rddata_en_p0,
   output logic                      o_dfi_rddata_en_p1,
   output logic                      o_dfi_rddata_en_p2,
   output logic                      o_dfi_rddata_en_p3,
   output logic                      o_dfi_rddata_en_p4,
   output logic                      o_dfi_rddata_en_p5,
   output logic                      o_dfi_rddata_en_p6,
   output logic                      o_dfi_rddata_en_p7,
   output logic [1:0]                o_dfi_rddata_cs_p0,
   output logic [1:0]                o_dfi_rddata_cs_p1,
   output logic [1:0]                o_dfi_rddata_cs_p2,
   output logic [1:0]                o_dfi_rddata_cs_p3,
   output logic [1:0]                o_dfi_rddata_cs_p4,
   output logic [1:0]                o_dfi_rddata_cs_p5,
   output logic [1:0]                o_dfi_rddata_cs_p6,
   output logic [1:0]                o_dfi_rddata_cs_p7,
   input  logic [31:0]               i_dfi_rddata_w0,
   input  logic [31:0]               i_dfi_rddata_w1,
   input  logic [31:0]               i_dfi_rddata_w2,
   input  logic [31:0]               i_dfi_rddata_w3,
   input  logic [31:0]               i_dfi_rddata_w4,
   input  logic [31:0]               i_dfi_rddata_w5,
   input  logic [31:0]               i_dfi_rddata_w6,
   input  logic [31:0]               i_dfi_rddata_w7,
   input  logic [3:0]                i_dfi_rddata_dbi_w0,
   input  logic [3:0]                i_dfi_rddata_dbi_w1,
   input  logic [3:0]                i_dfi_rddata_dbi_w2,
   input  logic [3:0]                i_dfi_rddata_dbi_w3,
   input  logic [3:0]                i_dfi_rddata_dbi_w4,
   input  logic [3:0]                i_dfi_rddata_dbi_w5,
   input  logic [3:0]                i_dfi_rddata_dbi_w6,
   input  logic [3:0]                i_dfi_rddata_dbi_w7,
   input  logic                      i_dfi_rddata_valid_w1,
   input  logic                      i_dfi_rddata_valid_w2,
   input  logic                      i_dfi_rddata_valid_w3,
   input  logic                      i_dfi_rddata_valid_w4,
   input  logic                      i_dfi_rddata_valid_w5,
   input  logic                      i_dfi_rddata_valid_w6,
   input  logic                      i_dfi_rddata_valid_w7,
   input  logic                      i_dfi_rddata_valid_w0

);

   // PHY Phases
   // Command
   assign o_dfi_reset_n_p0 = i_dfi_reset_n_p0;
   assign o_dfi_reset_n_p1 = i_dfi_reset_n_p0;
   assign o_dfi_reset_n_p2 = i_dfi_reset_n_p1;
   assign o_dfi_reset_n_p3 = i_dfi_reset_n_p1;
   assign o_dfi_reset_n_p4 = i_dfi_reset_n_p2;
   assign o_dfi_reset_n_p5 = i_dfi_reset_n_p2;
   assign o_dfi_reset_n_p6 = i_dfi_reset_n_p3;
   assign o_dfi_reset_n_p7 = i_dfi_reset_n_p3;

   assign o_dfi_address_p0 = i_dfi_address_p0[6:0];
   assign o_dfi_address_p1 = i_dfi_address_p0[13:7];
   assign o_dfi_address_p2 = i_dfi_address_p1[6:0];
   assign o_dfi_address_p3 = i_dfi_address_p1[13:7];
   assign o_dfi_address_p4 = i_dfi_address_p2[6:0];
   assign o_dfi_address_p5 = i_dfi_address_p2[13:7];
   assign o_dfi_address_p6 = i_dfi_address_p3[6:0];
   assign o_dfi_address_p7 = i_dfi_address_p3[13:7];
   assign o_dfi_cke_p0     = i_dfi_cke_p0;
   assign o_dfi_cke_p1     = i_dfi_cke_p0;
   assign o_dfi_cke_p2     = i_dfi_cke_p1;
   assign o_dfi_cke_p3     = i_dfi_cke_p1;
   assign o_dfi_cke_p4     = i_dfi_cke_p2;
   assign o_dfi_cke_p5     = i_dfi_cke_p2;
   assign o_dfi_cke_p6     = i_dfi_cke_p3;
   assign o_dfi_cke_p7     = i_dfi_cke_p3;

   assign o_dfi_cs_p0      = i_dfi_cs_p0;
   assign o_dfi_cs_p1      = i_dfi_cs_p0;
   assign o_dfi_cs_p2      = i_dfi_cs_p1;
   assign o_dfi_cs_p3      = i_dfi_cs_p1;
   assign o_dfi_cs_p4      = i_dfi_cs_p2;
   assign o_dfi_cs_p5      = i_dfi_cs_p2;
   assign o_dfi_cs_p6      = i_dfi_cs_p3;
   assign o_dfi_cs_p7      = i_dfi_cs_p3;
   assign o_dfi_dram_clk_disable_p0 = i_dfi_dram_clk_disable_p0;
   assign o_dfi_dram_clk_disable_p1 = i_dfi_dram_clk_disable_p0;
   assign o_dfi_dram_clk_disable_p2 = i_dfi_dram_clk_disable_p1;
   assign o_dfi_dram_clk_disable_p3 = i_dfi_dram_clk_disable_p1;
   assign o_dfi_dram_clk_disable_p4 = i_dfi_dram_clk_disable_p2;
   assign o_dfi_dram_clk_disable_p5 = i_dfi_dram_clk_disable_p2;
   assign o_dfi_dram_clk_disable_p6 = i_dfi_dram_clk_disable_p3;
   assign o_dfi_dram_clk_disable_p7 = i_dfi_dram_clk_disable_p3;

   // Write
   assign o_dfi_wrdata_p0       = i_dfi_wrdata_p0[31:0];
   assign o_dfi_wrdata_p1       = i_dfi_wrdata_p0[63:32];
   assign o_dfi_wrdata_p2       = i_dfi_wrdata_p1[31:0];
   assign o_dfi_wrdata_p3       = i_dfi_wrdata_p1[63:32];
   assign o_dfi_wrdata_p4       = i_dfi_wrdata_p2[31:0];
   assign o_dfi_wrdata_p5       = i_dfi_wrdata_p2[63:32];
   assign o_dfi_wrdata_p6       = i_dfi_wrdata_p3[31:0];
   assign o_dfi_wrdata_p7       = i_dfi_wrdata_p3[63:32];
   assign o_dfi_parity_in_p0    = i_dfi_parity_in_p0;
   assign o_dfi_parity_in_p1    = i_dfi_parity_in_p0;
   assign o_dfi_parity_in_p2    = i_dfi_parity_in_p1;
   assign o_dfi_parity_in_p3    = i_dfi_parity_in_p1;
   assign o_dfi_parity_in_p4    = i_dfi_parity_in_p2;
   assign o_dfi_parity_in_p5    = i_dfi_parity_in_p2;
   assign o_dfi_parity_in_p6    = i_dfi_parity_in_p3;
   assign o_dfi_parity_in_p7    = i_dfi_parity_in_p3;
   assign o_dfi_wrdata_cs_p0    = i_dfi_wrdata_cs_p0;
   assign o_dfi_wrdata_cs_p1    = i_dfi_wrdata_cs_p0;
   assign o_dfi_wrdata_cs_p2    = i_dfi_wrdata_cs_p1;
   assign o_dfi_wrdata_cs_p3    = i_dfi_wrdata_cs_p1;
   assign o_dfi_wrdata_cs_p4    = i_dfi_wrdata_cs_p2;
   assign o_dfi_wrdata_cs_p5    = i_dfi_wrdata_cs_p2;
   assign o_dfi_wrdata_cs_p6    = i_dfi_wrdata_cs_p3;
   assign o_dfi_wrdata_cs_p7    = i_dfi_wrdata_cs_p3;
   assign o_dfi_wrdata_mask_p0  = i_dfi_wrdata_mask_p0[3:0];
   assign o_dfi_wrdata_mask_p1  = i_dfi_wrdata_mask_p0[7:4];
   assign o_dfi_wrdata_mask_p2  = i_dfi_wrdata_mask_p1[3:0];
   assign o_dfi_wrdata_mask_p3  = i_dfi_wrdata_mask_p1[7:4];
   assign o_dfi_wrdata_mask_p4  = i_dfi_wrdata_mask_p2[3:0];
   assign o_dfi_wrdata_mask_p5  = i_dfi_wrdata_mask_p2[7:4];
   assign o_dfi_wrdata_mask_p6  = i_dfi_wrdata_mask_p3[3:0];
   assign o_dfi_wrdata_mask_p7  = i_dfi_wrdata_mask_p3[7:4];
   assign o_dfi_wrdata_en_p0    = i_dfi_wrdata_en_p0;
   assign o_dfi_wrdata_en_p1    = i_dfi_wrdata_en_p0;
   assign o_dfi_wrdata_en_p2    = i_dfi_wrdata_en_p1;
   assign o_dfi_wrdata_en_p3    = i_dfi_wrdata_en_p1;
   assign o_dfi_wrdata_en_p4    = i_dfi_wrdata_en_p2;
   assign o_dfi_wrdata_en_p5    = i_dfi_wrdata_en_p2;
   assign o_dfi_wrdata_en_p6    = i_dfi_wrdata_en_p3;
   assign o_dfi_wrdata_en_p7    = i_dfi_wrdata_en_p3;
   assign o_dfi_wck_cs_p0       = i_dfi_wck_cs_p0;
   assign o_dfi_wck_cs_p1       = i_dfi_wck_cs_p0;
   assign o_dfi_wck_cs_p2       = i_dfi_wck_cs_p1;
   assign o_dfi_wck_cs_p3       = i_dfi_wck_cs_p1;
   assign o_dfi_wck_cs_p4       = i_dfi_wck_cs_p2;
   assign o_dfi_wck_cs_p5       = i_dfi_wck_cs_p2;
   assign o_dfi_wck_cs_p6       = i_dfi_wck_cs_p3;
   assign o_dfi_wck_cs_p7       = i_dfi_wck_cs_p3;
   assign o_dfi_wck_en_p0       = i_dfi_wck_en_p0;
   assign o_dfi_wck_en_p1       = i_dfi_wck_en_p0;
   assign o_dfi_wck_en_p2       = i_dfi_wck_en_p1;
   assign o_dfi_wck_en_p3       = i_dfi_wck_en_p1;
   assign o_dfi_wck_en_p4       = i_dfi_wck_en_p2;
   assign o_dfi_wck_en_p5       = i_dfi_wck_en_p2;
   assign o_dfi_wck_en_p6       = i_dfi_wck_en_p3;
   assign o_dfi_wck_en_p7       = i_dfi_wck_en_p3;
   assign o_dfi_wck_toggle_p0   = i_dfi_wck_toggle_p0;
   assign o_dfi_wck_toggle_p1   = i_dfi_wck_toggle_p0;
   assign o_dfi_wck_toggle_p2   = i_dfi_wck_toggle_p1;
   assign o_dfi_wck_toggle_p3   = i_dfi_wck_toggle_p1;
   assign o_dfi_wck_toggle_p4   = i_dfi_wck_toggle_p2;
   assign o_dfi_wck_toggle_p5   = i_dfi_wck_toggle_p2;
   assign o_dfi_wck_toggle_p6   = i_dfi_wck_toggle_p3;
   assign o_dfi_wck_toggle_p7   = i_dfi_wck_toggle_p3;

   assign  o_dfi_rddata_en_p0   = i_dfi_rddata_en_p0;
   assign  o_dfi_rddata_en_p1   = i_dfi_rddata_en_p0;
   assign  o_dfi_rddata_en_p2   = i_dfi_rddata_en_p1;
   assign  o_dfi_rddata_en_p3   = i_dfi_rddata_en_p1;
   assign  o_dfi_rddata_en_p4   = i_dfi_rddata_en_p2;
   assign  o_dfi_rddata_en_p5   = i_dfi_rddata_en_p2;
   assign  o_dfi_rddata_en_p6   = i_dfi_rddata_en_p3;
   assign  o_dfi_rddata_en_p7   = i_dfi_rddata_en_p3;
   assign  o_dfi_rddata_cs_p0   = i_dfi_rddata_cs_p0;
   assign  o_dfi_rddata_cs_p1   = i_dfi_rddata_cs_p0;
   assign  o_dfi_rddata_cs_p2   = i_dfi_rddata_cs_p1;
   assign  o_dfi_rddata_cs_p3   = i_dfi_rddata_cs_p1;
   assign  o_dfi_rddata_cs_p4   = i_dfi_rddata_cs_p2;
   assign  o_dfi_rddata_cs_p5   = i_dfi_rddata_cs_p2;
   assign  o_dfi_rddata_cs_p6   = i_dfi_rddata_cs_p3;
   assign  o_dfi_rddata_cs_p7   = i_dfi_rddata_cs_p3;

   assign  o_dfi_rddata_w0       = {i_dfi_rddata_w1, i_dfi_rddata_w0};
   assign  o_dfi_rddata_w1       = {i_dfi_rddata_w3, i_dfi_rddata_w2};
   assign  o_dfi_rddata_w2       = {i_dfi_rddata_w5, i_dfi_rddata_w4};
   assign  o_dfi_rddata_w3       = {i_dfi_rddata_w7, i_dfi_rddata_w6};
   assign o_dfi_rddata_dbi_w0   = {i_dfi_rddata_dbi_w1, i_dfi_rddata_dbi_w0};
   assign o_dfi_rddata_dbi_w1   = {i_dfi_rddata_dbi_w3, i_dfi_rddata_dbi_w2};
   assign o_dfi_rddata_dbi_w2   = {i_dfi_rddata_dbi_w5, i_dfi_rddata_dbi_w4};
   assign o_dfi_rddata_dbi_w3   = {i_dfi_rddata_dbi_w7, i_dfi_rddata_dbi_w6};
   assign o_dfi_rddata_valid_w0 = i_dfi_rddata_valid_w0;
   assign o_dfi_rddata_valid_w1 = i_dfi_rddata_valid_w2;
   assign o_dfi_rddata_valid_w2 = i_dfi_rddata_valid_w4;
   assign o_dfi_rddata_valid_w3 = i_dfi_rddata_valid_w6;

endmodule

module ddr_ls_vddaon_wrapper (
   input  logic                 i_freeze_n,
   output logic                 o_freeze_n_ls
);
   assign o_freeze_n_ls         = i_freeze_n;

endmodule

module ddr_vddaon_island (
   input  logic                 i_freeze_n,
   output logic                 o_freeze_n
);
   ddr_buf u_aon_freeze_buf (.i_a(i_freeze_n), .o_z(o_freeze_n));

endmodule
