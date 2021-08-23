
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
import wav_ahb_pkg::*;

module ddr_ahb_ic #(
   parameter                            AWIDTH   = 32,
   parameter                            DWIDTH   = 32
) (
   input  logic                         i_scan_cgc_ctrl,
   input  logic                         i_scan_mode    ,
   input  logic                         i_scan_rst_ctrl,
   input  logic                         i_mcu_clk,
   input  logic                         i_mcu_rst,

   input  logic                         i_ahb_extclk,
   input  logic                         i_ahb_extrst,

   input  logic                         i_hclk,
   input  logic                         i_hrst,

   // Intf AHB Slave Port
   input  logic [AWIDTH-1:0]            i_intf_ahbs_haddr,
   input  logic                         i_intf_ahbs_hwrite,
   input  logic                         i_intf_ahbs_hsel,
   input  logic [31:0]                  i_intf_ahbs_hwdata,
   input  logic [1:0]                   i_intf_ahbs_htrans,
   input  logic [2:0]                   i_intf_ahbs_hsize,
   input  logic [2:0]                   i_intf_ahbs_hburst,
   input  logic                         i_intf_ahbs_hreadyin,
   output logic                         o_intf_ahbs_hready,
   output logic [DWIDTH-1:0]            o_intf_ahbs_hrdata,
   output logic [1:0]                   o_intf_ahbs_hresp,

   // MCU AHB Master Port
   input  logic [AWIDTH-1:0]            i_mcu_ahbm_haddr,
   input  logic                         i_mcu_ahbm_hwrite,
   input  logic                         i_mcu_ahbm_hbusreq,
   input  logic [31:0]                  i_mcu_ahbm_hwdata,
   input  logic [1:0]                   i_mcu_ahbm_htrans,
   input  logic [2:0]                   i_mcu_ahbm_hsize,
   input  logic [2:0]                   i_mcu_ahbm_hburst,
   input  logic                         i_mcu_ahbm_hreadyin,
   output logic                         o_mcu_ahbm_hready,
   output logic [DWIDTH-1:0]            o_mcu_ahbm_hrdata,
   output logic [1:0]                   o_mcu_ahbm_hresp,
   output logic                         o_mcu_ahbm_hgrant,

   // External Master Port
   output logic [AWIDTH-1:0]            o_ext_ahbm_haddr,
   output logic                         o_ext_ahbm_hwrite,
   output logic                         o_ext_ahbm_hbusreq,
   output logic [DWIDTH-1:0]            o_ext_ahbm_hwdata,
   output logic [1:0]                   o_ext_ahbm_htrans,
   output logic [2:0]                   o_ext_ahbm_hsize,
   output logic [2:0]                   o_ext_ahbm_hburst,
   input  logic                         i_ext_ahbm_hready,
   input  logic [DWIDTH-1:0]            i_ext_ahbm_hrdata,
   input  logic [1:0]                   i_ext_ahbm_hresp,
   input  logic                         i_ext_ahbm_hgrant,

   // CPU CSR AHB Slave Port - Pre Arbitration
   output logic [AWIDTH-1:0]            o_mcutop_ahbs_haddr,
   output logic                         o_mcutop_ahbs_hwrite,
   output logic                         o_mcutop_ahbs_hsel,
   output logic [31:0]                  o_mcutop_ahbs_hwdata,
   output logic [1:0]                   o_mcutop_ahbs_htrans,
   output logic [2:0]                   o_mcutop_ahbs_hsize,
   output logic [2:0]                   o_mcutop_ahbs_hburst,
   output logic                         o_mcutop_ahbs_hreadyin,
   input  logic                         i_mcutop_ahbs_hready,
   input  logic [DWIDTH-1:0]            i_mcutop_ahbs_hrdata,
   input  logic [1:0]                   i_mcutop_ahbs_hresp,
   // CPU CSR AHB Slave port - Post Arbitration
   output logic [AWIDTH-1:0]            o_mcu_cfg_ahbs_haddr,
   output logic                         o_mcu_cfg_ahbs_hwrite,
   output logic                         o_mcu_cfg_ahbs_hsel,
   output logic [31:0]                  o_mcu_cfg_ahbs_hwdata,
   output logic [1:0]                   o_mcu_cfg_ahbs_htrans,
   output logic [2:0]                   o_mcu_cfg_ahbs_hsize,
   output logic [2:0]                   o_mcu_cfg_ahbs_hburst,
   output logic                         o_mcu_cfg_ahbs_hreadyin,
   input  logic                         i_mcu_cfg_ahbs_hready,
   input  logic [DWIDTH-1:0]            i_mcu_cfg_ahbs_hrdata,
   input  logic [1:0]                   i_mcu_cfg_ahbs_hresp,

   // MCU AHB Slave Port - DTCM/ITCM - mcu clk
   output logic [AWIDTH-1:0]            o_mcu_ahbs_haddr,
   output logic                         o_mcu_ahbs_hwrite,
   output logic                         o_mcu_ahbs_hsel,
   output logic [31:0]                  o_mcu_ahbs_hwdata,
   output logic [1:0]                   o_mcu_ahbs_htrans,
   output logic [2:0]                   o_mcu_ahbs_hsize,
   output logic [2:0]                   o_mcu_ahbs_hburst,
   output logic                         o_mcu_ahbs_hreadyin,
   input  logic                         i_mcu_ahbs_hready,
   input  logic [DWIDTH-1:0]            i_mcu_ahbs_hrdata,
   input  logic [1:0]                   i_mcu_ahbs_hresp,
   input  logic                         i_mcu_ahbs_hgrant,

   output logic [AWIDTH-1:0]            o_cmn_ahbs_haddr,
   output logic                         o_cmn_ahbs_hwrite,
   output logic                         o_cmn_ahbs_hsel,
   output logic [31:0]                  o_cmn_ahbs_hwdata,
   output logic [1:0]                   o_cmn_ahbs_htrans,
   output logic [2:0]                   o_cmn_ahbs_hsize,
   output logic [2:0]                   o_cmn_ahbs_hburst,
   output logic                         o_cmn_ahbs_hreadyin,
   input  logic                         i_cmn_ahbs_hready,
   input  logic [DWIDTH-1:0]            i_cmn_ahbs_hrdata,
   input  logic [1:0]                   i_cmn_ahbs_hresp,

   output logic [AWIDTH-1:0]            o_dfi_ahbs_haddr,
   output logic                         o_dfi_ahbs_hwrite,
   output logic                         o_dfi_ahbs_hsel,
   output logic [31:0]                  o_dfi_ahbs_hwdata,
   output logic [1:0]                   o_dfi_ahbs_htrans,
   output logic [2:0]                   o_dfi_ahbs_hsize,
   output logic [2:0]                   o_dfi_ahbs_hburst,
   output logic                         o_dfi_ahbs_hreadyin,
   input  logic                         i_dfi_ahbs_hready,
   input  logic [DWIDTH-1:0]            i_dfi_ahbs_hrdata,
   input  logic [1:0]                   i_dfi_ahbs_hresp,

   output logic [AWIDTH-1:0]            o_ch0_dq0_ahbs_haddr,
   output logic                         o_ch0_dq0_ahbs_hwrite,
   output logic                         o_ch0_dq0_ahbs_hsel,
   output logic [31:0]                  o_ch0_dq0_ahbs_hwdata,
   output logic [1:0]                   o_ch0_dq0_ahbs_htrans,
   output logic [2:0]                   o_ch0_dq0_ahbs_hsize,
   output logic [2:0]                   o_ch0_dq0_ahbs_hburst,
   output logic                         o_ch0_dq0_ahbs_hreadyin,
   input  logic                         i_ch0_dq0_ahbs_hready,
   input  logic [DWIDTH-1:0]            i_ch0_dq0_ahbs_hrdata,
   input  logic [1:0]                   i_ch0_dq0_ahbs_hresp,

   output logic [AWIDTH-1:0]            o_ch0_dq1_ahbs_haddr,
   output logic                         o_ch0_dq1_ahbs_hwrite,
   output logic                         o_ch0_dq1_ahbs_hsel,
   output logic [31:0]                  o_ch0_dq1_ahbs_hwdata,
   output logic [1:0]                   o_ch0_dq1_ahbs_htrans,
   output logic [2:0]                   o_ch0_dq1_ahbs_hsize,
   output logic [2:0]                   o_ch0_dq1_ahbs_hburst,
   output logic                         o_ch0_dq1_ahbs_hreadyin,
   input  logic                         i_ch0_dq1_ahbs_hready,
   input  logic [DWIDTH-1:0]            i_ch0_dq1_ahbs_hrdata,
   input  logic [1:0]                   i_ch0_dq1_ahbs_hresp,

   output logic [AWIDTH-1:0]            o_ch0_ca_ahbs_haddr,
   output logic                         o_ch0_ca_ahbs_hwrite,
   output logic                         o_ch0_ca_ahbs_hsel,
   output logic [31:0]                  o_ch0_ca_ahbs_hwdata,
   output logic [1:0]                   o_ch0_ca_ahbs_htrans,
   output logic [2:0]                   o_ch0_ca_ahbs_hsize,
   output logic [2:0]                   o_ch0_ca_ahbs_hburst,
   output logic                         o_ch0_ca_ahbs_hreadyin,
   input  logic                         i_ch0_ca_ahbs_hready,
   input  logic [DWIDTH-1:0]            i_ch0_ca_ahbs_hrdata,
   input  logic [1:0]                   i_ch0_ca_ahbs_hresp,

   output logic [AWIDTH-1:0]            o_ch1_dq0_ahbs_haddr,
   output logic                         o_ch1_dq0_ahbs_hwrite,
   output logic                         o_ch1_dq0_ahbs_hsel,
   output logic [31:0]                  o_ch1_dq0_ahbs_hwdata,
   output logic [1:0]                   o_ch1_dq0_ahbs_htrans,
   output logic [2:0]                   o_ch1_dq0_ahbs_hsize,
   output logic [2:0]                   o_ch1_dq0_ahbs_hburst,
   output logic                         o_ch1_dq0_ahbs_hreadyin,
   input  logic                         i_ch1_dq0_ahbs_hready,
   input  logic [DWIDTH-1:0]            i_ch1_dq0_ahbs_hrdata,
   input  logic [1:0]                   i_ch1_dq0_ahbs_hresp,

   output logic [AWIDTH-1:0]            o_ch1_dq1_ahbs_haddr,
   output logic                         o_ch1_dq1_ahbs_hwrite,
   output logic                         o_ch1_dq1_ahbs_hsel,
   output logic [31:0]                  o_ch1_dq1_ahbs_hwdata,
   output logic [1:0]                   o_ch1_dq1_ahbs_htrans,
   output logic [2:0]                   o_ch1_dq1_ahbs_hsize,
   output logic [2:0]                   o_ch1_dq1_ahbs_hburst,
   output logic                         o_ch1_dq1_ahbs_hreadyin,
   input  logic                         i_ch1_dq1_ahbs_hready,
   input  logic [DWIDTH-1:0]            i_ch1_dq1_ahbs_hrdata,
   input  logic [1:0]                   i_ch1_dq1_ahbs_hresp,

   output logic [AWIDTH-1:0]            o_ch1_ca_ahbs_haddr,
   output logic                         o_ch1_ca_ahbs_hwrite,
   output logic                         o_ch1_ca_ahbs_hsel,
   output logic [31:0]                  o_ch1_ca_ahbs_hwdata,
   output logic [1:0]                   o_ch1_ca_ahbs_htrans,
   output logic [2:0]                   o_ch1_ca_ahbs_hsize,
   output logic [2:0]                   o_ch1_ca_ahbs_hburst,
   output logic                         o_ch1_ca_ahbs_hreadyin,
   input  logic                         i_ch1_ca_ahbs_hready,
   input  logic [DWIDTH-1:0]            i_ch1_ca_ahbs_hrdata,
   input  logic [1:0]                   i_ch1_ca_ahbs_hresp,

   output logic [AWIDTH-1:0]            o_ctrl_ahbs_haddr,
   output logic                         o_ctrl_ahbs_hwrite,
   output logic                         o_ctrl_ahbs_hsel,
   output logic [31:0]                  o_ctrl_ahbs_hwdata,
   output logic [1:0]                   o_ctrl_ahbs_htrans,
   output logic [2:0]                   o_ctrl_ahbs_hsize,
   output logic [2:0]                   o_ctrl_ahbs_hburst,
   output logic                         o_ctrl_ahbs_hreadyin,
   input  logic                         i_ctrl_ahbs_hready,
   input  logic [DWIDTH-1:0]            i_ctrl_ahbs_hrdata,
   input  logic [1:0]                   i_ctrl_ahbs_hresp

);

   logic                               async_intf_ahbm_hgrant;
   logic [AWIDTH-1:0]                  async_intf_ahbm_haddr;
   logic                               async_intf_ahbm_hwrite;
   logic                               async_intf_ahbm_hbusreq;
   logic [DWIDTH-1:0]                  async_intf_ahbm_hwdata;
   logic [1:0]                         async_intf_ahbm_htrans;
   logic [2:0]                         async_intf_ahbm_hsize;
   logic [2:0]                         async_intf_ahbm_hburst;
   logic                               async_intf_ahbm_hready;
   logic [DWIDTH-1:0]                  async_intf_ahbm_hrdata;
   logic [1:0]                         async_intf_ahbm_hresp;

   logic                               intf_ahbm_hgrant;
   logic [AWIDTH-1:0]                  intf_ahbm_haddr;
   logic                               intf_ahbm_hwrite;
   logic                               intf_ahbm_hbusreq;
   logic [DWIDTH-1:0]                  intf_ahbm_hwdata;
   logic [1:0]                         intf_ahbm_htrans;
   logic [2:0]                         intf_ahbm_hsize;
   logic [2:0]                         intf_ahbm_hburst;
   logic                               intf_ahbm_hready;
   logic [DWIDTH-1:0]                  intf_ahbm_hrdata;
   logic [1:0]                         intf_ahbm_hresp;

   logic                               mcu_ahbm_hgrant;
   logic [AWIDTH-1:0]                  mcu_ahbm_haddr;
   logic                               mcu_ahbm_hwrite;
   logic                               mcu_ahbm_hbusreq;
   logic [DWIDTH-1:0]                  mcu_ahbm_hwdata;
   logic [1:0]                         mcu_ahbm_htrans;
   logic [2:0]                         mcu_ahbm_hsize;
   logic [2:0]                         mcu_ahbm_hburst;
   logic                               mcu_ahbm_hready;
   logic [DWIDTH-1:0]                  mcu_ahbm_hrdata;
   logic [1:0]                         mcu_ahbm_hresp;

   wav_ahb_slave2master #(
      .AWIDTH  (32)
   ) u_intf_ahbm_s2m (
      .i_hclk                          (i_ahb_extclk),
      .i_hreset                        (i_ahb_extrst),
      .i_ahbs_haddr                    (i_intf_ahbs_haddr ),
      .i_ahbs_hwrite                   (i_intf_ahbs_hwrite),
      .i_ahbs_hsel                     (i_intf_ahbs_hsel  ),
      .i_ahbs_hwdata                   (i_intf_ahbs_hwdata),
      .i_ahbs_htrans                   (i_intf_ahbs_htrans),
      .i_ahbs_hsize                    (i_intf_ahbs_hsize ),
      .i_ahbs_hburst                   (i_intf_ahbs_hburst),
      .i_ahbs_hreadyin                 (i_intf_ahbs_hreadyin),
      .o_ahbs_hready                   (o_intf_ahbs_hready),
      .o_ahbs_hrdata                   (o_intf_ahbs_hrdata),
      .o_ahbs_hresp                    (o_intf_ahbs_hresp ),

      .i_ahbm_hgrant                   (async_intf_ahbm_hgrant),
      .o_ahbm_haddr                    (async_intf_ahbm_haddr ),
      .o_ahbm_hwrite                   (async_intf_ahbm_hwrite),
      .o_ahbm_hbusreq                  (async_intf_ahbm_hbusreq),
      .o_ahbm_hwdata                   (async_intf_ahbm_hwdata),
      .o_ahbm_htrans                   (async_intf_ahbm_htrans),
      .o_ahbm_hsize                    (async_intf_ahbm_hsize ),
      .o_ahbm_hburst                   (async_intf_ahbm_hburst),
      .i_ahbm_hready                   (async_intf_ahbm_hready),
      .i_ahbm_hrdata                   (async_intf_ahbm_hrdata),
      .i_ahbm_hresp                    (async_intf_ahbm_hresp )
   );

   // AHB Sync block AHB Ext Clock to hclk
   ddr_ahb2ahb_sync #(
      .AWIDTH     (32),
      .ASYNC      (1)
   ) u_intfahb_sync (

      .i_scan_cgc_ctrl               (i_scan_cgc_ctrl),
      .i_scan_mode                   (i_scan_mode    ),
      .i_scan_rst_ctrl               (i_scan_rst_ctrl),
      .i_m2freq_hi                   (1'b1),

      .i_m1_hclk                     (i_ahb_extclk),
      .i_m1_hreset                   (i_ahb_extrst),

      .i_m2_hclk                     (i_hclk),
      .i_m2_hreset                   (i_hrst),

      .i_m1_haddr                    (async_intf_ahbm_haddr ),
      .i_m1_hwrite                   (async_intf_ahbm_hwrite),
      .i_m1_hbusreq                  (async_intf_ahbm_hbusreq),
      .i_m1_hwdata                   (async_intf_ahbm_hwdata),
      .i_m1_htrans                   (async_intf_ahbm_htrans),
      .i_m1_hsize                    (async_intf_ahbm_hsize ),
      .i_m1_hburst                   (async_intf_ahbm_hburst),
      .o_m1_hready                   (async_intf_ahbm_hready),
      .o_m1_hrdata                   (async_intf_ahbm_hrdata),
      .o_m1_hresp                    (async_intf_ahbm_hresp ),
      .o_m1_hgrant                   (async_intf_ahbm_hgrant),
      .o_m1_clkon                    (/*OPEN*/),//FIXME
      .o_m2_clkon                    (/*OPEN*/),//FIXME

      .o_m2_haddr                    (intf_ahbm_haddr ),
      .o_m2_hwrite                   (intf_ahbm_hwrite),
      .o_m2_hbusreq                  (intf_ahbm_hbusreq),
      .o_m2_hwdata                   (intf_ahbm_hwdata),
      .o_m2_htrans                   (intf_ahbm_htrans),
      .o_m2_hsize                    (intf_ahbm_hsize ),
      .o_m2_hburst                   (intf_ahbm_hburst),
      .i_m2_hready                   (intf_ahbm_hready),
      .i_m2_hrdata                   (intf_ahbm_hrdata),
      .i_m2_hresp                    (intf_ahbm_hresp ),
      .i_m2_hgrant                   (intf_ahbm_hgrant)
   );

   //----------------------------------------------------------------------
   // AHB Sync block MCU Clock to hclk
   //----------------------------------------------------------------------
   logic vld_mcu_ahbm_hbusreq ;
   assign  vld_mcu_ahbm_hbusreq = i_mcu_ahbm_hbusreq & i_mcu_ahbm_hreadyin ;

   ddr_ahb2ahb_sync #(
      .AWIDTH     (32),
      .ASYNC      (1)
   ) u_mcu2ahbic_sync (

      .i_scan_cgc_ctrl               (i_scan_cgc_ctrl),
      .i_scan_mode                   (i_scan_mode    ),
      .i_scan_rst_ctrl               (i_scan_rst_ctrl),
      .i_m2freq_hi                   (1'b0),

      .i_m1_hclk                     (i_mcu_clk),
      .i_m1_hreset                   (i_mcu_rst),
      .i_m2_hclk                     (i_hclk),
      .i_m2_hreset                   (i_hrst),

      .i_m1_haddr                    (i_mcu_ahbm_haddr ),
      .i_m1_hwrite                   (i_mcu_ahbm_hwrite),
      .i_m1_hbusreq                  (vld_mcu_ahbm_hbusreq),
      .i_m1_hwdata                   (i_mcu_ahbm_hwdata),
      .i_m1_htrans                   (i_mcu_ahbm_htrans),
      .i_m1_hsize                    (i_mcu_ahbm_hsize ),
      .i_m1_hburst                   (i_mcu_ahbm_hburst),
      .o_m1_hready                   (o_mcu_ahbm_hready),
      .o_m1_hrdata                   (o_mcu_ahbm_hrdata),
      .o_m1_hresp                    (o_mcu_ahbm_hresp ),
      .o_m1_hgrant                   (o_mcu_ahbm_hgrant),
      .o_m1_clkon                    (/*OPEN*/),//FIXME
      .o_m2_clkon                    (/*OPEN*/),//FIXME

      .o_m2_haddr                    (mcu_ahbm_haddr ),
      .o_m2_hwrite                   (mcu_ahbm_hwrite),
      .o_m2_hbusreq                  (mcu_ahbm_hbusreq),
      .o_m2_hwdata                   (mcu_ahbm_hwdata),
      .o_m2_htrans                   (mcu_ahbm_htrans),
      .o_m2_hsize                    (mcu_ahbm_hsize ),
      .o_m2_hburst                   (mcu_ahbm_hburst),
      .i_m2_hready                   (mcu_ahbm_hready),
      .i_m2_hrdata                   (mcu_ahbm_hrdata),
      .i_m2_hresp                    (mcu_ahbm_hresp ),
      .i_m2_hgrant                   (mcu_ahbm_hgrant)
   );

   //----------------------------------------------------------------------
   // INTF AHB Slaves
   //----------------------------------------------------------------------
   localparam NUM_INTF_SLVS = 4;
   localparam INTF_SWIDTH   = $clog2(NUM_INTF_SLVS)+'b1;

   localparam INT_SLV_IDX         = 0 ;
   localparam MCUTOP_SLV_IDX      = 1 ;
   localparam MCU_SLV_IDX         = 2 ;
   localparam MCU_DEFAULT_SLV_IDX = 3 ;

   logic [AWIDTH-1:0]                  intf_ahbm_haddr_local ;
   logic [AWIDTH-1:0]                  intf_ahbm_haddr_offset;

   logic [AWIDTH*NUM_INTF_SLVS-1:0]    intf_slv_mux_haddr ;
   logic [NUM_INTF_SLVS-1:0]           intf_slv_mux_hwrite;
   logic [NUM_INTF_SLVS-1:0]           intf_slv_mux_hsel  ;
   logic [DWIDTH*NUM_INTF_SLVS-1:0]    intf_slv_mux_hwdata;
   logic [2*NUM_INTF_SLVS-1:0]         intf_slv_mux_htrans;
   logic [3*NUM_INTF_SLVS-1:0]         intf_slv_mux_hsize ;
   logic [3*NUM_INTF_SLVS-1:0]         intf_slv_mux_hburst;
   logic [NUM_INTF_SLVS-1:0]           intf_slv_mux_hready;
   logic [NUM_INTF_SLVS-1:0]           intf_slv_mux_hreadyin;
   logic [DWIDTH*NUM_INTF_SLVS-1:0]    intf_slv_mux_hrdata;
   logic [2*NUM_INTF_SLVS-1:0]         intf_slv_mux_hresp ;
   logic [INTF_SWIDTH-1:0]             intf_slv_sel ;

   logic [AWIDTH-1:0]                  int_ahbs_haddr;
   logic                               int_ahbs_hwrite;
   logic                               int_ahbs_hsel;
   logic [31:0]                        int_ahbs_hwdata;
   logic [1:0]                         int_ahbs_htrans;
   logic [2:0]                         int_ahbs_hsize;
   logic [2:0]                         int_ahbs_hburst;
   logic                               int_ahbs_hready;
   logic                               int_ahbs_hreadyin;
   logic [DWIDTH-1:0]                  int_ahbs_hrdata;
   logic [1:0]                         int_ahbs_hresp;

   logic [AWIDTH-1:0]                  mcu_default_ahbs_haddr;
   logic                               mcu_default_ahbs_hwrite;
   logic                               mcu_default_ahbs_hsel;
   logic [31:0]                        mcu_default_ahbs_hwdata;
   logic [1:0]                         mcu_default_ahbs_htrans;
   logic [2:0]                         mcu_default_ahbs_hsize;
   logic [2:0]                         mcu_default_ahbs_hburst;
   logic                               mcu_default_ahbs_hready;
   logic                               mcu_default_ahbs_hreadyin;
   logic [DWIDTH-1:0]                  mcu_default_ahbs_hrdata;
   logic [1:0]                         mcu_default_ahbs_hresp;

   logic [AWIDTH-1:0]                  mcu_ahbs_haddr;
   logic                               mcu_ahbs_hwrite;
   logic                               mcu_ahbs_hsel;
   logic [31:0]                        mcu_ahbs_hwdata;
   logic [1:0]                         mcu_ahbs_htrans;
   logic [2:0]                         mcu_ahbs_hsize;
   logic [2:0]                         mcu_ahbs_hburst;
   logic                               mcu_ahbs_hready;
   logic                               mcu_ahbs_hreadyin;
   logic [DWIDTH-1:0]                  mcu_ahbs_hrdata;
   logic [1:0]                         mcu_ahbs_hresp;
   logic                               mcu_ahbs_hgrant;

   logic                               int_ahbm_hgrant;
   logic [AWIDTH-1:0]                  int_ahbm_haddr;
   logic                               int_ahbm_hwrite;
   logic                               int_ahbm_hbusreq;
   logic [DWIDTH-1:0]                  int_ahbm_hwdata;
   logic [1:0]                         int_ahbm_htrans;
   logic [2:0]                         int_ahbm_hsize;
   logic [2:0]                         int_ahbm_hburst;
   logic                               int_ahbm_hready;
   logic [DWIDTH-1:0]                  int_ahbm_hrdata;
   logic [1:0]                         int_ahbm_hresp;

   assign {mcu_default_ahbs_haddr,    mcu_ahbs_haddr,   o_mcutop_ahbs_haddr,   int_ahbs_haddr    } =  intf_slv_mux_haddr ;
   assign {mcu_default_ahbs_hwrite,   mcu_ahbs_hwrite,  o_mcutop_ahbs_hwrite,  int_ahbs_hwrite   } =  intf_slv_mux_hwrite;
   assign {mcu_default_ahbs_hsel,     mcu_ahbs_hsel,    o_mcutop_ahbs_hsel,    int_ahbs_hsel     } =  intf_slv_mux_hsel  ;
   assign {mcu_default_ahbs_hreadyin, mcu_ahbs_hreadyin,o_mcutop_ahbs_hreadyin,int_ahbs_hreadyin } =  intf_slv_mux_hreadyin  ;
   assign {mcu_default_ahbs_hwdata,   mcu_ahbs_hwdata,  o_mcutop_ahbs_hwdata,  int_ahbs_hwdata   } =  intf_slv_mux_hwdata;
   assign {mcu_default_ahbs_htrans,   mcu_ahbs_htrans,  o_mcutop_ahbs_htrans,  int_ahbs_htrans   } =  intf_slv_mux_htrans;
   assign {mcu_default_ahbs_hsize,    mcu_ahbs_hsize,   o_mcutop_ahbs_hsize,   int_ahbs_hsize    } =  intf_slv_mux_hsize ;
   assign {mcu_default_ahbs_hburst,   mcu_ahbs_hburst,  o_mcutop_ahbs_hburst,  int_ahbs_hburst   } =  intf_slv_mux_hburst;

   assign intf_slv_mux_hready                                          = {mcu_default_ahbs_hready, mcu_ahbs_hready, i_mcutop_ahbs_hready,  int_ahbs_hready};
   assign intf_slv_mux_hrdata                                          = {mcu_default_ahbs_hrdata, mcu_ahbs_hrdata, i_mcutop_ahbs_hrdata,  int_ahbs_hrdata};
   assign intf_slv_mux_hresp                                           = {mcu_default_ahbs_hresp,  mcu_ahbs_hresp,  i_mcutop_ahbs_hresp,   int_ahbs_hresp };

   //Slave sel and slave decode
   assign intf_slv_sel = ((intf_ahbm_haddr >= DDR_MCUMEM_SLV_OFFSET) & (intf_ahbm_haddr < DDR_INT_SLV_OFFSET))     ? ('b1+MCU_SLV_IDX   ) :
                         ((intf_ahbm_haddr >= DDR_MCUTOP_OFFSET    ) & (intf_ahbm_haddr < DDR_MCUINTF_OFFSET   )) ? ('b1+MCUTOP_SLV_IDX) :
                         ((intf_ahbm_haddr >= DDR_INT_SLV_OFFSET   ) | ((intf_ahbm_haddr >= DDR_MCUINTF_OFFSET) & (intf_ahbm_haddr < DDR_MCU_ITCM_OFFSET)))     ? ('b1+INT_SLV_IDX   ) :
                         ('b1+MCU_DEFAULT_SLV_IDX) ;

   assign intf_ahbm_haddr_offset = (intf_slv_sel == (MCUTOP_SLV_IDX+'b1)) ? DDR_MCUTOP_OFFSET :
                                   (intf_slv_sel == (MCU_SLV_IDX+'b1))    ? DDR_MCU_ITCM_OFFSET : '0 ;
   assign intf_ahbm_haddr_local  = intf_ahbm_haddr - intf_ahbm_haddr_offset ;

   assign intf_ahbm_hgrant = (intf_slv_sel == (INT_SLV_IDX+'b1)) ? int_ahbm_hgrant :
                             (intf_slv_sel == (MCU_SLV_IDX+'b1)) ? mcu_ahbs_hgrant : 'b1 ;

   wav_ahb_slave_mux #(
      .DWIDTH           (32),
      .AWIDTH           (32),
      .NUM_SLV          (NUM_INTF_SLVS )
   ) u_intf_slv_mux (

      .i_hclk           (i_hclk),
      .i_hreset         (i_hrst),

      .i_slv_sel        (intf_slv_sel),
      .i_hbusreq        (intf_ahbm_hbusreq),
      .i_haddr          (intf_ahbm_haddr_local),
      .i_hwrite         (intf_ahbm_hwrite),
      .i_hwdata         (intf_ahbm_hwdata),
      .i_htrans         (intf_ahbm_htrans),
      .i_hsize          (intf_ahbm_hsize ),
      .i_hburst         (intf_ahbm_hburst),
      .i_hreadyin       (1'b1),
      .o_hready         (intf_ahbm_hready),
      .o_hrdata         (intf_ahbm_hrdata),
      .o_hresp          (intf_ahbm_hresp ),

      .o_haddr          (intf_slv_mux_haddr ),
      .o_hwrite         (intf_slv_mux_hwrite),
      .o_hsel           (intf_slv_mux_hsel  ),
      .o_hwdata         (intf_slv_mux_hwdata),
      .o_htrans         (intf_slv_mux_htrans),
      .o_hsize          (intf_slv_mux_hsize ),
      .o_hburst         (intf_slv_mux_hburst),
      .o_hreadyin       (intf_slv_mux_hreadyin),
      .i_hready         (intf_slv_mux_hready),
      .i_hrdata         (intf_slv_mux_hrdata),
      .i_hresp          (intf_slv_mux_hresp )
   );

   wav_default_ahb_slave u_mcu_default_ahb_slave (
      .i_hclk           (i_hclk),
      .i_hreset         (i_hrst),
      .i_haddr          (mcu_default_ahbs_haddr),
      .i_hwrite         (mcu_default_ahbs_hwrite),
      .i_hsel           (mcu_default_ahbs_hsel),
      .i_hwdata         (mcu_default_ahbs_hwdata),
      .i_htrans         (mcu_default_ahbs_htrans),
      .i_hsize          (mcu_default_ahbs_hsize),
      .i_hburst         (mcu_default_ahbs_hburst),
      .i_hreadyin       (mcu_default_ahbs_hreadyin),
      .o_hready         (mcu_default_ahbs_hready),
      .o_hrdata         (mcu_default_ahbs_hrdata),
      .o_hresp          (mcu_default_ahbs_hresp)
   );

   //----------------------------------------------------------------------
   // AHB Sync block hclk to MCU clock
   //----------------------------------------------------------------------
   logic vld_mcu_ahbs_hbusreq;
   assign vld_mcu_ahbs_hbusreq = mcu_ahbs_hreadyin & mcu_ahbs_hsel ;
   assign o_mcu_ahbs_hreadyin  = '1 ;

   ddr_ahb2ahb_sync #(
      .AWIDTH     (32),
      .ASYNC      (1)
   ) u_ahbic2mcu_sync (

      .i_scan_cgc_ctrl               (i_scan_cgc_ctrl),
      .i_scan_mode                   (i_scan_mode    ),
      .i_scan_rst_ctrl               (i_scan_rst_ctrl),
      .i_m2freq_hi                   (1'b1),

      .i_m1_hclk                     (i_hclk),
      .i_m1_hreset                   (i_hrst),
      .i_m2_hclk                     (i_mcu_clk),
      .i_m2_hreset                   (i_mcu_rst),

      .i_m1_haddr                    (mcu_ahbs_haddr ),
      .i_m1_hwrite                   (mcu_ahbs_hwrite),
      .i_m1_hbusreq                  (vld_mcu_ahbs_hbusreq),
      .i_m1_hwdata                   (mcu_ahbs_hwdata),
      .i_m1_htrans                   (mcu_ahbs_htrans),
      .i_m1_hsize                    (mcu_ahbs_hsize ),
      .i_m1_hburst                   (mcu_ahbs_hburst),
      .o_m1_hready                   (mcu_ahbs_hready),
      .o_m1_hrdata                   (mcu_ahbs_hrdata),
      .o_m1_hresp                    (mcu_ahbs_hresp ),
      .o_m1_hgrant                   (mcu_ahbs_hgrant),
      .o_m1_clkon                    (/*OPEN*/), // FIXME
      .o_m2_clkon                    (/*OPEN*/), // FIXME

      .o_m2_haddr                    (o_mcu_ahbs_haddr ),
      .o_m2_hwrite                   (o_mcu_ahbs_hwrite),
      .o_m2_hbusreq                  (o_mcu_ahbs_hsel),
      .o_m2_hwdata                   (o_mcu_ahbs_hwdata),
      .o_m2_htrans                   (o_mcu_ahbs_htrans),
      .o_m2_hsize                    (o_mcu_ahbs_hsize ),
      .o_m2_hburst                   (o_mcu_ahbs_hburst),
      .i_m2_hready                   (i_mcu_ahbs_hready),
      .i_m2_hrdata                   (i_mcu_ahbs_hrdata),
      .i_m2_hresp                    (i_mcu_ahbs_hresp ),
      .i_m2_hgrant                   (i_mcu_ahbs_hgrant)
   );

   //----------------------------------------------------------
   // Internal AHBS to AHBM
   //----------------------------------------------------------

   wav_ahb_slave2master #(
      .AWIDTH  (32)
   ) u_int_ahbm_s2m (
      .i_hclk                          (i_hclk),
      .i_hreset                        (i_hrst),
      .i_ahbs_haddr                    (int_ahbs_haddr ),
      .i_ahbs_hwrite                   (int_ahbs_hwrite),
      .i_ahbs_hsel                     (int_ahbs_hsel  ),
      .i_ahbs_hreadyin                 (int_ahbs_hreadyin),
      .i_ahbs_hwdata                   (int_ahbs_hwdata),
      .i_ahbs_htrans                   (int_ahbs_htrans),
      .i_ahbs_hsize                    (int_ahbs_hsize ),
      .i_ahbs_hburst                   (int_ahbs_hburst),
      .o_ahbs_hready                   (int_ahbs_hready),
      .o_ahbs_hrdata                   (int_ahbs_hrdata),
      .o_ahbs_hresp                    (int_ahbs_hresp ),

      .i_ahbm_hgrant                   (int_ahbm_hgrant),
      .o_ahbm_haddr                    (int_ahbm_haddr ),
      .o_ahbm_hwrite                   (int_ahbm_hwrite),
      .o_ahbm_hbusreq                  (int_ahbm_hbusreq),
      .o_ahbm_hwdata                   (int_ahbm_hwdata),
      .o_ahbm_htrans                   (int_ahbm_htrans),
      .o_ahbm_hsize                    (int_ahbm_hsize ),
      .o_ahbm_hburst                   (int_ahbm_hburst),
      .i_ahbm_hready                   (int_ahbm_hready),
      .i_ahbm_hrdata                   (int_ahbm_hrdata),
      .i_ahbm_hresp                    (int_ahbm_hresp )
   );

  //-----------------------------------------------------------
  // AHB Master Mux
  //------------------------------------------------------------
   localparam NUM_MSTR = 2;

   logic [32*NUM_MSTR-1:0] ahbm_hwdata;
   logic [32*NUM_MSTR-1:0] ahbm_haddr;
   logic [2*NUM_MSTR-1:0]  ahbm_htrans;
   logic [3*NUM_MSTR-1:0]  ahbm_hsize;
   logic [3*NUM_MSTR-1:0]  ahbm_hburst;
   logic [NUM_MSTR-1:0]    ahbm_hwrite;
   logic [NUM_MSTR-1:0]    ahbm_hbusreq;
   logic [NUM_MSTR-1:0]    ahbm_hgrant;
   logic [NUM_MSTR-1:0]    ahbm_hready;
   logic [2*NUM_MSTR-1:0]  ahbm_hresp;
   logic [32*NUM_MSTR-1:0] ahbm_hrdata;

   logic [AWIDTH-1:0]      phy_ahbs_haddr;
   logic                   phy_ahbs_hwrite;
   logic                   phy_ahbs_hsel;
   logic [31:0]            phy_ahbs_hwdata;
   logic [1:0]             phy_ahbs_htrans;
   logic [2:0]             phy_ahbs_hsize;
   logic [2:0]             phy_ahbs_hburst;
   logic                   phy_ahbs_hready;
   logic [DWIDTH-1:0]      phy_ahbs_hrdata;
   logic [1:0]             phy_ahbs_hresp;

   assign ahbm_haddr   = {mcu_ahbm_haddr  , int_ahbm_haddr  };
   assign ahbm_hbusreq = {mcu_ahbm_hbusreq, int_ahbm_hbusreq};
   assign ahbm_hwrite  = {mcu_ahbm_hwrite , int_ahbm_hwrite };
   assign ahbm_hwdata  = {mcu_ahbm_hwdata , int_ahbm_hwdata };
   assign ahbm_htrans  = {mcu_ahbm_htrans , int_ahbm_htrans };
   assign ahbm_hsize   = {mcu_ahbm_hsize  , int_ahbm_hsize  };
   assign ahbm_hburst  = {mcu_ahbm_hburst , int_ahbm_hburst };

   assign {mcu_ahbm_hgrant, int_ahbm_hgrant } = ahbm_hgrant;
   assign {mcu_ahbm_hready, int_ahbm_hready } = ahbm_hready;
   assign {mcu_ahbm_hrdata, int_ahbm_hrdata } = ahbm_hrdata;
   assign {mcu_ahbm_hresp , int_ahbm_hresp  } = ahbm_hresp ;

   wav_ahb_master_arbiter_mux #(
      .AWIDTH            (AWIDTH),
      .DWIDTH            (32),
      .NUM_MSTR          (NUM_MSTR)
   ) u_ahbm_arbiter_mux (
      .i_hclk            (i_hclk),
      .i_hreset          (i_hrst),

      .i_ahbm_haddr      (ahbm_haddr),
      .i_ahbm_hwrite     (ahbm_hwrite),
      .i_ahbm_hwdata     (ahbm_hwdata),
      .i_ahbm_htrans     (ahbm_htrans),
      .i_ahbm_hsize      (ahbm_hsize),
      .i_ahbm_hburst     (ahbm_hburst),
      .i_ahbm_hbusreq    (ahbm_hbusreq),
      .o_ahbm_hgrant     (ahbm_hgrant),
      .o_ahbm_hrdata     (ahbm_hrdata),
      .o_ahbm_hresp      (ahbm_hresp ),
      .o_ahbm_hready     (ahbm_hready),

      .o_ahbm_haddr      (phy_ahbs_haddr),
      .o_ahbm_hwrite     (phy_ahbs_hwrite),
      .o_ahbm_hwdata     (phy_ahbs_hwdata),
      .o_ahbm_htrans     (phy_ahbs_htrans),
      .o_ahbm_hsize      (phy_ahbs_hsize),
      .o_ahbm_hburst     (phy_ahbs_hburst),
      .o_ahbm_hbusreq    (phy_ahbs_hsel),
      .i_ahbm_hready     (phy_ahbs_hready),
      .i_ahbm_hrdata     (phy_ahbs_hrdata),
      .i_ahbm_hresp      (phy_ahbs_hresp),
      .o_ahbm_hmaster    (/*OPEN*/),
      .o_ahbm_hmastlock  (/*OPEN*/)
   );

  //--------------------------------------------------------------
  //AHB Slave Mux
  //--------------------------------------------------------------
   localparam NUM_PHY_SLVS    = 12;
   localparam PHY_SWIDTH      = $clog2(NUM_PHY_SLVS)+'b1;

   localparam MCUCFG_SLV_IDX  = 0  ;
   localparam CMN_SLV_IDX     = 1  ;
   localparam CTRL_SLV_IDX    = 2  ;
   localparam DFI_SLV_IDX     = 3  ;
   localparam CH0_DQ0_SLV_IDX = 4  ;
   localparam CH0_DQ1_SLV_IDX = 5  ;
   localparam CH0_CA_SLV_IDX  = 6  ;
   localparam CH1_DQ0_SLV_IDX = 7  ;
   localparam CH1_DQ1_SLV_IDX = 8  ;
   localparam CH1_CA_SLV_IDX  = 9  ;
   localparam EXT_SLV_IDX     = 10 ;
   localparam DEFAULT_SLV_IDX = 11 ;

   logic [AWIDTH-1:0]                 phy_ahbs_haddr_offset;
   logic [AWIDTH-1:0]                 phy_ahbs_haddr_local;

   logic [AWIDTH*NUM_PHY_SLVS-1:0]    phy_slv_mux_haddr ;
   logic [NUM_PHY_SLVS-1:0]           phy_slv_mux_hwrite;
   logic [NUM_PHY_SLVS-1:0]           phy_slv_mux_hsel  ;
   logic [NUM_PHY_SLVS-1:0]           phy_slv_mux_hreadyin ;
   logic [DWIDTH*NUM_PHY_SLVS-1:0]    phy_slv_mux_hwdata;
   logic [2*NUM_PHY_SLVS-1:0]         phy_slv_mux_htrans;
   logic [3*NUM_PHY_SLVS-1:0]         phy_slv_mux_hsize ;
   logic [3*NUM_PHY_SLVS-1:0]         phy_slv_mux_hburst;
   logic [NUM_PHY_SLVS-1:0]           phy_slv_mux_hready;
   logic [DWIDTH*NUM_PHY_SLVS-1:0]    phy_slv_mux_hrdata;
   logic [2*NUM_PHY_SLVS-1:0]         phy_slv_mux_hresp ;
   logic [PHY_SWIDTH-1:0]             phy_slv_sel ;

   logic [AWIDTH-1:0]                 ext_ahbs_haddr;
   logic                              ext_ahbs_hwrite;
   logic                              ext_ahbs_hsel;
   logic [DWIDTH-1:0]                 ext_ahbs_hwdata;
   logic [1:0]                        ext_ahbs_htrans;
   logic [2:0]                        ext_ahbs_hsize;
   logic [2:0]                        ext_ahbs_hburst;
   logic                              ext_ahbs_hready;
   logic [DWIDTH-1:0]                 ext_ahbs_hrdata;
   logic [1:0]                        ext_ahbs_hresp;

   logic [AWIDTH-1:0]                 default_ahbs_haddr;
   logic                              default_ahbs_hwrite;
   logic                              default_ahbs_hsel;
   logic [DWIDTH-1:0]                 default_ahbs_hwdata;
   logic [1:0]                        default_ahbs_htrans;
   logic [2:0]                        default_ahbs_hsize;
   logic [2:0]                        default_ahbs_hburst;
   logic                              default_ahbs_hready;
   logic [DWIDTH-1:0]                 default_ahbs_hrdata;
   logic [1:0]                        default_ahbs_hresp;

   assign o_mcu_cfg_ahbs_haddr    =  phy_slv_mux_haddr   [MCUCFG_SLV_IDX*AWIDTH+:AWIDTH];
   assign o_mcu_cfg_ahbs_hwrite   =  phy_slv_mux_hwrite  [MCUCFG_SLV_IDX];
   assign o_mcu_cfg_ahbs_hsel     =  phy_slv_mux_hsel    [MCUCFG_SLV_IDX];
   assign o_mcu_cfg_ahbs_hreadyin =  phy_slv_mux_hreadyin[MCUCFG_SLV_IDX];
   assign o_mcu_cfg_ahbs_hwdata   =  phy_slv_mux_hwdata  [MCUCFG_SLV_IDX*DWIDTH+:DWIDTH];
   assign o_mcu_cfg_ahbs_htrans   =  phy_slv_mux_htrans  [MCUCFG_SLV_IDX*2+:2];
   assign o_mcu_cfg_ahbs_hsize    =  phy_slv_mux_hsize   [MCUCFG_SLV_IDX*3+:3];
   assign o_mcu_cfg_ahbs_hburst   =  phy_slv_mux_hburst  [MCUCFG_SLV_IDX*3+:3];

   assign o_cmn_ahbs_haddr        =  phy_slv_mux_haddr   [CMN_SLV_IDX*AWIDTH+:AWIDTH];
   assign o_cmn_ahbs_hwrite       =  phy_slv_mux_hwrite  [CMN_SLV_IDX];
   assign o_cmn_ahbs_hsel         =  phy_slv_mux_hsel    [CMN_SLV_IDX];
   assign o_cmn_ahbs_hreadyin     =  phy_slv_mux_hreadyin[CMN_SLV_IDX];
   assign o_cmn_ahbs_hwdata       =  phy_slv_mux_hwdata  [CMN_SLV_IDX*DWIDTH+:DWIDTH];
   assign o_cmn_ahbs_htrans       =  phy_slv_mux_htrans  [CMN_SLV_IDX*2+:2];
   assign o_cmn_ahbs_hsize        =  phy_slv_mux_hsize   [CMN_SLV_IDX*3+:3];
   assign o_cmn_ahbs_hburst       =  phy_slv_mux_hburst  [CMN_SLV_IDX*3+:3];

   assign o_ctrl_ahbs_haddr       =  phy_slv_mux_haddr   [CTRL_SLV_IDX*AWIDTH+:AWIDTH];
   assign o_ctrl_ahbs_hwrite      =  phy_slv_mux_hwrite  [CTRL_SLV_IDX];
   assign o_ctrl_ahbs_hsel        =  phy_slv_mux_hsel    [CTRL_SLV_IDX];
   assign o_ctrl_ahbs_hreadyin    =  phy_slv_mux_hreadyin[CTRL_SLV_IDX];
   assign o_ctrl_ahbs_hwdata      =  phy_slv_mux_hwdata  [CTRL_SLV_IDX*DWIDTH+:DWIDTH];
   assign o_ctrl_ahbs_htrans      =  phy_slv_mux_htrans  [CTRL_SLV_IDX*2+:2];
   assign o_ctrl_ahbs_hsize       =  phy_slv_mux_hsize   [CTRL_SLV_IDX*3+:3];
   assign o_ctrl_ahbs_hburst      =  phy_slv_mux_hburst  [CTRL_SLV_IDX*3+:3];

   assign o_dfi_ahbs_haddr        =  phy_slv_mux_haddr   [DFI_SLV_IDX*AWIDTH+:AWIDTH];
   assign o_dfi_ahbs_hwrite       =  phy_slv_mux_hwrite  [DFI_SLV_IDX];
   assign o_dfi_ahbs_hsel         =  phy_slv_mux_hsel    [DFI_SLV_IDX];
   assign o_dfi_ahbs_hreadyin     =  phy_slv_mux_hreadyin[DFI_SLV_IDX];
   assign o_dfi_ahbs_hwdata       =  phy_slv_mux_hwdata  [DFI_SLV_IDX*DWIDTH+:DWIDTH];
   assign o_dfi_ahbs_htrans       =  phy_slv_mux_htrans  [DFI_SLV_IDX*2+:2];
   assign o_dfi_ahbs_hsize        =  phy_slv_mux_hsize   [DFI_SLV_IDX*3+:3];
   assign o_dfi_ahbs_hburst       =  phy_slv_mux_hburst  [DFI_SLV_IDX*3+:3];

   assign o_ch0_dq0_ahbs_haddr    =  phy_slv_mux_haddr   [CH0_DQ0_SLV_IDX*AWIDTH+:AWIDTH];
   assign o_ch0_dq0_ahbs_hwrite   =  phy_slv_mux_hwrite  [CH0_DQ0_SLV_IDX];
   assign o_ch0_dq0_ahbs_hsel     =  phy_slv_mux_hsel    [CH0_DQ0_SLV_IDX];
   assign o_ch0_dq0_ahbs_hreadyin =  phy_slv_mux_hreadyin[CH0_DQ0_SLV_IDX];
   assign o_ch0_dq0_ahbs_hwdata   =  phy_slv_mux_hwdata  [CH0_DQ0_SLV_IDX*DWIDTH+:DWIDTH];
   assign o_ch0_dq0_ahbs_htrans   =  phy_slv_mux_htrans  [CH0_DQ0_SLV_IDX*2+:2];
   assign o_ch0_dq0_ahbs_hsize    =  phy_slv_mux_hsize   [CH0_DQ0_SLV_IDX*3+:3];
   assign o_ch0_dq0_ahbs_hburst   =  phy_slv_mux_hburst  [CH0_DQ0_SLV_IDX*3+:3];

   assign o_ch0_dq1_ahbs_haddr    =  phy_slv_mux_haddr   [CH0_DQ1_SLV_IDX*AWIDTH+:AWIDTH];
   assign o_ch0_dq1_ahbs_hwrite   =  phy_slv_mux_hwrite  [CH0_DQ1_SLV_IDX];
   assign o_ch0_dq1_ahbs_hsel     =  phy_slv_mux_hsel    [CH0_DQ1_SLV_IDX];
   assign o_ch0_dq1_ahbs_hreadyin =  phy_slv_mux_hreadyin[CH0_DQ1_SLV_IDX];
   assign o_ch0_dq1_ahbs_hwdata   =  phy_slv_mux_hwdata  [CH0_DQ1_SLV_IDX*DWIDTH+:DWIDTH];
   assign o_ch0_dq1_ahbs_htrans   =  phy_slv_mux_htrans  [CH0_DQ1_SLV_IDX*2+:2];
   assign o_ch0_dq1_ahbs_hsize    =  phy_slv_mux_hsize   [CH0_DQ1_SLV_IDX*3+:3];
   assign o_ch0_dq1_ahbs_hburst   =  phy_slv_mux_hburst  [CH0_DQ1_SLV_IDX*3+:3];

   assign o_ch0_ca_ahbs_haddr     =  phy_slv_mux_haddr   [CH0_CA_SLV_IDX*AWIDTH+:AWIDTH];
   assign o_ch0_ca_ahbs_hwrite    =  phy_slv_mux_hwrite  [CH0_CA_SLV_IDX];
   assign o_ch0_ca_ahbs_hsel      =  phy_slv_mux_hsel    [CH0_CA_SLV_IDX];
   assign o_ch0_ca_ahbs_hreadyin  =  phy_slv_mux_hreadyin[CH0_CA_SLV_IDX];
   assign o_ch0_ca_ahbs_hwdata    =  phy_slv_mux_hwdata  [CH0_CA_SLV_IDX*DWIDTH+:DWIDTH];
   assign o_ch0_ca_ahbs_htrans    =  phy_slv_mux_htrans  [CH0_CA_SLV_IDX*2+:2];
   assign o_ch0_ca_ahbs_hsize     =  phy_slv_mux_hsize   [CH0_CA_SLV_IDX*3+:3];
   assign o_ch0_ca_ahbs_hburst    =  phy_slv_mux_hburst  [CH0_CA_SLV_IDX*3+:3];

   assign o_ch1_dq0_ahbs_haddr    =  phy_slv_mux_haddr   [CH1_DQ0_SLV_IDX*AWIDTH+:AWIDTH];
   assign o_ch1_dq0_ahbs_hwrite   =  phy_slv_mux_hwrite  [CH1_DQ0_SLV_IDX];
   assign o_ch1_dq0_ahbs_hsel     =  phy_slv_mux_hsel    [CH1_DQ0_SLV_IDX];
   assign o_ch1_dq0_ahbs_hreadyin =  phy_slv_mux_hreadyin[CH1_DQ0_SLV_IDX];
   assign o_ch1_dq0_ahbs_hwdata   =  phy_slv_mux_hwdata  [CH1_DQ0_SLV_IDX*DWIDTH+:DWIDTH];
   assign o_ch1_dq0_ahbs_htrans   =  phy_slv_mux_htrans  [CH1_DQ0_SLV_IDX*2+:2];
   assign o_ch1_dq0_ahbs_hsize    =  phy_slv_mux_hsize   [CH1_DQ0_SLV_IDX*3+:3];
   assign o_ch1_dq0_ahbs_hburst   =  phy_slv_mux_hburst  [CH1_DQ0_SLV_IDX*3+:3];

   assign o_ch1_dq1_ahbs_haddr    =  phy_slv_mux_haddr   [CH1_DQ1_SLV_IDX*AWIDTH+:AWIDTH];
   assign o_ch1_dq1_ahbs_hwrite   =  phy_slv_mux_hwrite  [CH1_DQ1_SLV_IDX];
   assign o_ch1_dq1_ahbs_hsel     =  phy_slv_mux_hsel    [CH1_DQ1_SLV_IDX];
   assign o_ch1_dq1_ahbs_hreadyin =  phy_slv_mux_hreadyin[CH1_DQ1_SLV_IDX];
   assign o_ch1_dq1_ahbs_hwdata   =  phy_slv_mux_hwdata  [CH1_DQ1_SLV_IDX*DWIDTH+:DWIDTH];
   assign o_ch1_dq1_ahbs_htrans   =  phy_slv_mux_htrans  [CH1_DQ1_SLV_IDX*2+:2];
   assign o_ch1_dq1_ahbs_hsize    =  phy_slv_mux_hsize   [CH1_DQ1_SLV_IDX*3+:3];
   assign o_ch1_dq1_ahbs_hburst   =  phy_slv_mux_hburst  [CH1_DQ1_SLV_IDX*3+:3];

   assign o_ch1_ca_ahbs_haddr     =  phy_slv_mux_haddr   [CH1_CA_SLV_IDX*AWIDTH+:AWIDTH];
   assign o_ch1_ca_ahbs_hwrite    =  phy_slv_mux_hwrite  [CH1_CA_SLV_IDX];
   assign o_ch1_ca_ahbs_hsel      =  phy_slv_mux_hsel    [CH1_CA_SLV_IDX];
   assign o_ch1_ca_ahbs_hreadyin  =  phy_slv_mux_hreadyin[CH1_CA_SLV_IDX];
   assign o_ch1_ca_ahbs_hwdata    =  phy_slv_mux_hwdata  [CH1_CA_SLV_IDX*DWIDTH+:DWIDTH];
   assign o_ch1_ca_ahbs_htrans    =  phy_slv_mux_htrans  [CH1_CA_SLV_IDX*2+:2];
   assign o_ch1_ca_ahbs_hsize     =  phy_slv_mux_hsize   [CH1_CA_SLV_IDX*3+:3];
   assign o_ch1_ca_ahbs_hburst    =  phy_slv_mux_hburst  [CH1_CA_SLV_IDX*3+:3];

   assign ext_ahbs_haddr          =  phy_slv_mux_haddr   [EXT_SLV_IDX*AWIDTH+:AWIDTH];
   assign ext_ahbs_hwrite         =  phy_slv_mux_hwrite  [EXT_SLV_IDX];
   assign ext_ahbs_hsel           =  phy_slv_mux_hsel    [EXT_SLV_IDX];
   assign ext_ahbs_hreadyin       =  phy_slv_mux_hreadyin[EXT_SLV_IDX];
   assign ext_ahbs_hwdata         =  phy_slv_mux_hwdata  [EXT_SLV_IDX*DWIDTH+:DWIDTH];
   assign ext_ahbs_htrans         =  phy_slv_mux_htrans  [EXT_SLV_IDX*2+:2];
   assign ext_ahbs_hsize          =  phy_slv_mux_hsize   [EXT_SLV_IDX*3+:3];
   assign ext_ahbs_hburst         =  phy_slv_mux_hburst  [EXT_SLV_IDX*3+:3];

   assign default_ahbs_haddr      =  phy_slv_mux_haddr   [DEFAULT_SLV_IDX*AWIDTH+:AWIDTH];
   assign default_ahbs_hwrite     =  phy_slv_mux_hwrite  [DEFAULT_SLV_IDX];
   assign default_ahbs_hsel       =  phy_slv_mux_hsel    [DEFAULT_SLV_IDX];
   assign default_ahbs_hreadyin   =  phy_slv_mux_hreadyin[DEFAULT_SLV_IDX];
   assign default_ahbs_hwdata     =  phy_slv_mux_hwdata  [DEFAULT_SLV_IDX*DWIDTH+:DWIDTH];
   assign default_ahbs_htrans     =  phy_slv_mux_htrans  [DEFAULT_SLV_IDX*2+:2];
   assign default_ahbs_hsize      =  phy_slv_mux_hsize   [DEFAULT_SLV_IDX*3+:3];
   assign default_ahbs_hburst     =  phy_slv_mux_hburst  [DEFAULT_SLV_IDX*3+:3];

   assign phy_slv_mux_hready[MCUCFG_SLV_IDX]                 = i_mcu_cfg_ahbs_hready;
   assign phy_slv_mux_hrdata[MCUCFG_SLV_IDX*DWIDTH+:DWIDTH]  = i_mcu_cfg_ahbs_hrdata;
   assign phy_slv_mux_hresp [MCUCFG_SLV_IDX*2+:2]            = i_mcu_cfg_ahbs_hresp ;

   assign phy_slv_mux_hready[CMN_SLV_IDX]                    = i_cmn_ahbs_hready;
   assign phy_slv_mux_hrdata[CMN_SLV_IDX*DWIDTH+:DWIDTH]     = i_cmn_ahbs_hrdata;
   assign phy_slv_mux_hresp [CMN_SLV_IDX*2+:2]               = i_cmn_ahbs_hresp ;

   assign phy_slv_mux_hready[CTRL_SLV_IDX]                   = i_ctrl_ahbs_hready;
   assign phy_slv_mux_hrdata[CTRL_SLV_IDX*DWIDTH+:DWIDTH]    = i_ctrl_ahbs_hrdata;
   assign phy_slv_mux_hresp [CTRL_SLV_IDX*2+:2]              = i_ctrl_ahbs_hresp ;

   assign phy_slv_mux_hready[DFI_SLV_IDX]                    = i_dfi_ahbs_hready;
   assign phy_slv_mux_hrdata[DFI_SLV_IDX*DWIDTH+:DWIDTH]     = i_dfi_ahbs_hrdata;
   assign phy_slv_mux_hresp [DFI_SLV_IDX*2+:2]               = i_dfi_ahbs_hresp ;

   assign phy_slv_mux_hready[CH0_DQ0_SLV_IDX]                = i_ch0_dq0_ahbs_hready;
   assign phy_slv_mux_hrdata[CH0_DQ0_SLV_IDX*DWIDTH+:DWIDTH] = i_ch0_dq0_ahbs_hrdata;
   assign phy_slv_mux_hresp [CH0_DQ0_SLV_IDX*2+:2]           = i_ch0_dq0_ahbs_hresp ;

   assign phy_slv_mux_hready[CH0_DQ1_SLV_IDX]                = i_ch0_dq1_ahbs_hready;
   assign phy_slv_mux_hrdata[CH0_DQ1_SLV_IDX*DWIDTH+:DWIDTH] = i_ch0_dq1_ahbs_hrdata;
   assign phy_slv_mux_hresp [CH0_DQ1_SLV_IDX*2+:2]           = i_ch0_dq1_ahbs_hresp ;

   assign phy_slv_mux_hready[CH0_CA_SLV_IDX]                 = i_ch0_ca_ahbs_hready;
   assign phy_slv_mux_hrdata[CH0_CA_SLV_IDX*DWIDTH+:DWIDTH]  = i_ch0_ca_ahbs_hrdata;
   assign phy_slv_mux_hresp [CH0_CA_SLV_IDX*2+:2]            = i_ch0_ca_ahbs_hresp ;

   assign phy_slv_mux_hready[CH1_DQ0_SLV_IDX]                = i_ch1_dq0_ahbs_hready;
   assign phy_slv_mux_hrdata[CH1_DQ0_SLV_IDX*DWIDTH+:DWIDTH] = i_ch1_dq0_ahbs_hrdata;
   assign phy_slv_mux_hresp [CH1_DQ0_SLV_IDX*2+:2]           = i_ch1_dq0_ahbs_hresp ;

   assign phy_slv_mux_hready[CH1_DQ1_SLV_IDX]                = i_ch1_dq1_ahbs_hready;
   assign phy_slv_mux_hrdata[CH1_DQ1_SLV_IDX*DWIDTH+:DWIDTH] = i_ch1_dq1_ahbs_hrdata;
   assign phy_slv_mux_hresp [CH1_DQ1_SLV_IDX*2+:2]           = i_ch1_dq1_ahbs_hresp ;

   assign phy_slv_mux_hready[CH1_CA_SLV_IDX]                 = i_ch1_ca_ahbs_hready;
   assign phy_slv_mux_hrdata[CH1_CA_SLV_IDX*DWIDTH+:DWIDTH]  = i_ch1_ca_ahbs_hrdata;
   assign phy_slv_mux_hresp [CH1_CA_SLV_IDX*2+:2]            = i_ch1_ca_ahbs_hresp ;

   assign phy_slv_mux_hready[EXT_SLV_IDX]                    = ext_ahbs_hready;
   assign phy_slv_mux_hrdata[EXT_SLV_IDX*DWIDTH+:DWIDTH]     = ext_ahbs_hrdata;
   assign phy_slv_mux_hresp [EXT_SLV_IDX*2+:2]               = ext_ahbs_hresp ;

   assign phy_slv_mux_hready[DEFAULT_SLV_IDX]                = default_ahbs_hready;
   assign phy_slv_mux_hrdata[DEFAULT_SLV_IDX*DWIDTH+:DWIDTH] = default_ahbs_hrdata;
   assign phy_slv_mux_hresp [DEFAULT_SLV_IDX*2+:2]           = default_ahbs_hresp ;

   //Slave sel and slave decode
   assign phy_slv_sel = ((phy_ahbs_haddr >= DDR_MCUINTF_OFFSET ) & (phy_ahbs_haddr < DDR_MCU_ITCM_OFFSET    )) ? ('b1+MCUCFG_SLV_IDX) :
                        ((phy_ahbs_haddr >= DDR_CMN_OFFSET     ) & (phy_ahbs_haddr < DDR_CTRL_OFFSET        )) ? ('b1+CMN_SLV_IDX ) :
                        ((phy_ahbs_haddr >= DDR_CTRL_OFFSET    ) & (phy_ahbs_haddr < DDR_DFI_OFFSET         )) ? ('b1+CTRL_SLV_IDX) :
                        ((phy_ahbs_haddr >= DDR_DFI_OFFSET     ) & (phy_ahbs_haddr < DDR_CH0_DQ0_OFFSET     )) ? ('b1+DFI_SLV_IDX ) :
                        ((phy_ahbs_haddr >= DDR_CH0_DQ0_OFFSET ) & (phy_ahbs_haddr < DDR_CH0_DQ1_OFFSET     )) ? ('b1+CH0_DQ0_SLV_IDX ) :
                        ((phy_ahbs_haddr >= DDR_CH0_DQ1_OFFSET ) & (phy_ahbs_haddr < DDR_CH0_CA_OFFSET      )) ? ('b1+CH0_DQ1_SLV_IDX ) :
                        ((phy_ahbs_haddr >= DDR_CH0_CA_OFFSET  ) & (phy_ahbs_haddr < DDR_CH1_DQ0_OFFSET     )) ? ('b1+CH0_CA_SLV_IDX  ) :
                        ((phy_ahbs_haddr >= DDR_CH1_DQ0_OFFSET ) & (phy_ahbs_haddr < DDR_CH1_DQ1_OFFSET     )) ? ('b1+CH1_DQ0_SLV_IDX ) :
                        ((phy_ahbs_haddr >= DDR_CH1_DQ1_OFFSET ) & (phy_ahbs_haddr < DDR_CH1_CA_OFFSET      )) ? ('b1+CH1_DQ1_SLV_IDX ) :
                        ((phy_ahbs_haddr >= DDR_CH1_CA_OFFSET  ) & (phy_ahbs_haddr < DDR_PHY_SLV_RSVD_OFFSET)) ? ('b1+CH1_CA_SLV_IDX  ) :
                        ((phy_ahbs_haddr >= DDR_EXT_SLV_OFFSET ) & (phy_ahbs_haddr < DDR_EXT_RSVD_OFFSET    )) ? ('b1+EXT_SLV_IDX ) :
                        ('b1+DEFAULT_SLV_IDX) ;

   assign phy_ahbs_haddr_offset = (phy_slv_sel == ('b1+MCUCFG_SLV_IDX  )) ? DDR_MCUINTF_OFFSET  :
                                  (phy_slv_sel == ('b1+CMN_SLV_IDX     )) ? DDR_CMN_OFFSET      :
                                  (phy_slv_sel == ('b1+CTRL_SLV_IDX    )) ? DDR_CTRL_OFFSET     :
                                  (phy_slv_sel == ('b1+DFI_SLV_IDX     )) ? DDR_DFI_OFFSET      :
                                  (phy_slv_sel == ('b1+CH0_DQ0_SLV_IDX )) ? DDR_CH0_DQ0_OFFSET  :
                                  (phy_slv_sel == ('b1+CH0_DQ1_SLV_IDX )) ? DDR_CH0_DQ1_OFFSET  :
                                  (phy_slv_sel == ('b1+CH0_CA_SLV_IDX  )) ? DDR_CH0_CA_OFFSET   :
                                  (phy_slv_sel == ('b1+CH1_DQ0_SLV_IDX )) ? DDR_CH1_DQ0_OFFSET  :
                                  (phy_slv_sel == ('b1+CH1_DQ1_SLV_IDX )) ? DDR_CH1_DQ1_OFFSET  :
                                  (phy_slv_sel == ('b1+CH1_CA_SLV_IDX  )) ? DDR_CH1_CA_OFFSET   :
                                  '0;

   assign phy_ahbs_haddr_local  = phy_ahbs_haddr - phy_ahbs_haddr_offset;

   wav_ahb_slave_mux #(
      .DWIDTH           (32),
      .AWIDTH           (32),
      .NUM_SLV          (NUM_PHY_SLVS)
   ) u_phy_slv_mux (

      .i_hclk           (i_hclk),
      .i_hreset         (i_hrst),

      .i_slv_sel        (phy_slv_sel),
      .i_hbusreq        (phy_ahbs_hsel),
      .i_hreadyin       (1'b1),
      .i_haddr          (phy_ahbs_haddr_local),
      .i_hwrite         (phy_ahbs_hwrite),
      .i_hwdata         (phy_ahbs_hwdata),
      .i_htrans         (phy_ahbs_htrans),
      .i_hsize          (phy_ahbs_hsize ),
      .i_hburst         (phy_ahbs_hburst),
      .o_hready         (phy_ahbs_hready),
      .o_hrdata         (phy_ahbs_hrdata),
      .o_hresp          (phy_ahbs_hresp ),

      .o_haddr          (phy_slv_mux_haddr ),
      .o_hreadyin       (phy_slv_mux_hreadyin),
      .o_hwrite         (phy_slv_mux_hwrite),
      .o_hsel           (phy_slv_mux_hsel  ),
      .o_hwdata         (phy_slv_mux_hwdata),
      .o_htrans         (phy_slv_mux_htrans),
      .o_hsize          (phy_slv_mux_hsize ),
      .o_hburst         (phy_slv_mux_hburst),
      .i_hready         (phy_slv_mux_hready),
      .i_hrdata         (phy_slv_mux_hrdata),
      .i_hresp          (phy_slv_mux_hresp )
   );

   wav_default_ahb_slave u_default_ahb_slave (
      .i_hclk           (i_hclk),
      .i_hreset         (i_hrst),
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

   //----------------------------------------------------------
   // External PHY Channel AHBS to AHBM
   //----------------------------------------------------------
   logic [AWIDTH-1:0]            async_ext_ahbm_haddr;
   logic                         async_ext_ahbm_hwrite;
   logic                         async_ext_ahbm_hbusreq;
   logic [DWIDTH-1:0]            async_ext_ahbm_hwdata;
   logic [1:0]                   async_ext_ahbm_htrans;
   logic [2:0]                   async_ext_ahbm_hsize;
   logic [2:0]                   async_ext_ahbm_hburst;
   logic                         async_ext_ahbm_hreadyin;
   logic                         async_ext_ahbm_hready;
   logic [DWIDTH-1:0]            async_ext_ahbm_hrdata;
   logic [1:0]                   async_ext_ahbm_hresp;
   logic                         async_ext_ahbm_hgrant;

   wav_ahb_slave2master #(
      .AWIDTH  (32)
   ) u_ext_ahbm_s2m (
      .i_hclk                          (i_hclk),
      .i_hreset                        (i_hrst),
      .i_ahbs_haddr                    (ext_ahbs_haddr ),
      .i_ahbs_hwrite                   (ext_ahbs_hwrite),
      .i_ahbs_hsel                     (ext_ahbs_hsel  ),
      .i_ahbs_hreadyin                 (ext_ahbs_hreadyin),
      .i_ahbs_hwdata                   (ext_ahbs_hwdata),
      .i_ahbs_htrans                   (ext_ahbs_htrans),
      .i_ahbs_hsize                    (ext_ahbs_hsize ),
      .i_ahbs_hburst                   (ext_ahbs_hburst),
      .o_ahbs_hready                   (ext_ahbs_hready),
      .o_ahbs_hrdata                   (ext_ahbs_hrdata),
      .o_ahbs_hresp                    (ext_ahbs_hresp ),

      .i_ahbm_hgrant                   (async_ext_ahbm_hgrant),
      .o_ahbm_haddr                    (async_ext_ahbm_haddr ),
      .o_ahbm_hwrite                   (async_ext_ahbm_hwrite),
      .o_ahbm_hbusreq                  (async_ext_ahbm_hbusreq),
      .o_ahbm_hwdata                   (async_ext_ahbm_hwdata),
      .o_ahbm_htrans                   (async_ext_ahbm_htrans),
      .o_ahbm_hsize                    (async_ext_ahbm_hsize ),
      .o_ahbm_hburst                   (async_ext_ahbm_hburst),
      .i_ahbm_hready                   (async_ext_ahbm_hready),
      .i_ahbm_hrdata                   (async_ext_ahbm_hrdata),
      .i_ahbm_hresp                    (async_ext_ahbm_hresp )
   );

   // AHB Sync block AHB Ext Clock to hclk
   ddr_ahb2ahb_sync #(
      .AWIDTH     (32),
      .ASYNC      (1)
   ) u_extahb_sync (

      .i_scan_cgc_ctrl               (i_scan_cgc_ctrl),
      .i_scan_mode                   (i_scan_mode    ),
      .i_scan_rst_ctrl               (i_scan_rst_ctrl),
      .i_m2freq_hi                   (1'b0),

      .i_m1_hclk                     (i_hclk),
      .i_m1_hreset                   (i_hrst),

      .i_m2_hclk                     (i_ahb_extclk),
      .i_m2_hreset                   (i_ahb_extrst),

      .i_m1_haddr                    (async_ext_ahbm_haddr ),
      .i_m1_hwrite                   (async_ext_ahbm_hwrite),
      .i_m1_hbusreq                  (async_ext_ahbm_hbusreq),
      .i_m1_hwdata                   (async_ext_ahbm_hwdata),
      .i_m1_htrans                   (async_ext_ahbm_htrans),
      .i_m1_hsize                    (async_ext_ahbm_hsize ),
      .i_m1_hburst                   (async_ext_ahbm_hburst),
      .o_m1_hready                   (async_ext_ahbm_hready),
      .o_m1_hrdata                   (async_ext_ahbm_hrdata),
      .o_m1_hresp                    (async_ext_ahbm_hresp ),
      .o_m1_hgrant                   (async_ext_ahbm_hgrant),
      .o_m1_clkon                    (/*OPEN*/),//FIXME
      .o_m2_clkon                    (/*OPEN*/),//FIXME

      .o_m2_haddr                    (o_ext_ahbm_haddr ),
      .o_m2_hwrite                   (o_ext_ahbm_hwrite),
      .o_m2_hbusreq                  (o_ext_ahbm_hbusreq),
      .o_m2_hwdata                   (o_ext_ahbm_hwdata),
      .o_m2_htrans                   (o_ext_ahbm_htrans),
      .o_m2_hsize                    (o_ext_ahbm_hsize ),
      .o_m2_hburst                   (o_ext_ahbm_hburst),
      .i_m2_hready                   (i_ext_ahbm_hready),
      .i_m2_hrdata                   (i_ext_ahbm_hrdata),
      .i_m2_hresp                    (i_ext_ahbm_hresp ),
      .i_m2_hgrant                   (i_ext_ahbm_hgrant)
   );

endmodule

module ddr_ahb_slave #(
   parameter AWIDTH = 32,
   parameter DWIDTH = 32
)(
   input   logic                i_hclk,
   input   logic                i_hreset,
   input   logic [AWIDTH-1:0]   i_haddr,
   input   logic                i_hwrite,
   input   logic                i_hsel,
   input   logic                i_hreadyin,
   input   logic [DWIDTH-1:0]   i_hwdata,
   input   logic [1:0]          i_htrans,
   input   logic [2:0]          i_hsize,
   input   logic [2:0]          i_hburst,
   output  logic                o_hready,
   output  logic [DWIDTH-1:0]   o_hrdata,
   output  logic [1:0]          o_hresp,

   output  logic                o_write,
   output  logic                o_read,
   output  logic [AWIDTH-1:0]   o_addr,
   output  logic [DWIDTH-1:0]   o_wdata,
   input   logic [DWIDTH-1:0]   i_rdata,
   input   logic                i_error,
   input   logic                i_ready
);

   logic [AWIDTH-1:0] addr_d;
   logic [AWIDTH-1:0] addr_q;
   logic write_d;
   logic write_q;
   logic read_d;
   logic read_q;
   logic [DWIDTH-1:0] wdata_q;
   //logic [DWIDTH-1:0] rdata_q;
   logic [DWIDTH-1:0] wdata_d;
   logic wr_q;

   assign write_d  =  i_hwrite & i_hsel /*& i_hreadyin*/ & ((i_htrans == AHB_TRANS_SEQ) | (i_htrans == AHB_TRANS_NONSEQ));
   assign read_d   = ~i_hwrite & i_hsel /*& i_hreadyin*/ & ((i_htrans == AHB_TRANS_SEQ) | (i_htrans == AHB_TRANS_NONSEQ));
   assign addr_d   =             i_hsel /*& i_hreadyin*/ & ((i_htrans == AHB_TRANS_SEQ) | (i_htrans == AHB_TRANS_NONSEQ)) ? i_haddr : addr_q;

   always_ff @(posedge i_hclk, posedge i_hreset) begin
      if (i_hreset) begin
         addr_q  <= '0;
         write_q <= '0;
         read_q  <= '0;
         wr_q    <= '0;
         wdata_q <= '0;
         //rdata_q <= '0;
      end
      else begin
         // Write or Read to start the transaction, ready to keep the command
         // on the output. A slave must only sample the address and control
         // signals and hsel when HREADY is asserted.
         if (i_ready || write_d || read_d) begin
            addr_q  <= addr_d;
            write_q <= write_d;
            read_q  <= read_d;
         end

         // Write signal delayed one cycle to align with data
         wr_q <= write_d;

         // Capture data if not ready and previous cycle was a write
         if (wr_q && !i_ready) begin
            wdata_q <= i_hwdata;
         end
         //if (read_d) begin
         //   rdata_q <= i_rdata;
         //end
      end
   end

   // Previous cycle was not command cycle, but slave may not be ready so
   // select the captured data
   assign wdata_d = !wr_q ? wdata_q : i_hwdata;

   // Delay the write address by one cycle to align to data
   assign o_addr   = addr_q;
   assign o_write  = write_q;
   assign o_read   = read_q;
   assign o_wdata  = wdata_d;
   assign o_hrdata = i_rdata;
   assign o_hready = i_ready;
   assign o_hresp  = (i_error==1'b0) ? AHB_RESP_OK : AHB_RESP_ERROR ;

endmodule

module ddr_ahb2ahb_sync #(
   parameter DWIDTH           = 32,
   parameter AWIDTH           = 32,
   parameter ASYNC            = 0
) (

    input logic                 i_scan_cgc_ctrl,
    input logic                 i_scan_mode    ,
    input logic                 i_scan_rst_ctrl,
    input logic                 i_m2freq_hi    ,

    input logic                 i_m1_hclk    ,
    input logic                 i_m1_hreset  ,
    input logic                 i_m2_hclk    ,
    input logic                 i_m2_hreset  ,
    output logic                o_m1_clkon   ,
    output logic                o_m2_clkon   ,

    input  logic [AWIDTH-1:0]   i_m1_haddr,
    input  logic                i_m1_hwrite,
    input  logic                i_m1_hbusreq,
    input  logic [DWIDTH-1:0]   i_m1_hwdata,
    input  logic [1:0]          i_m1_htrans,
    input  logic [2:0]          i_m1_hsize,
    input  logic [2:0]          i_m1_hburst,
    output logic                o_m1_hready,
    output logic [DWIDTH-1:0]   o_m1_hrdata,
    output logic [1:0]          o_m1_hresp ,
    output logic                o_m1_hgrant,

    output logic [AWIDTH-1:0]   o_m2_haddr,
    output logic                o_m2_hwrite,
    output logic                o_m2_hbusreq,
    output logic [DWIDTH-1:0]   o_m2_hwdata,
    output logic [1:0]          o_m2_htrans,
    output logic [2:0]          o_m2_hsize,
    output logic [2:0]          o_m2_hburst,
    input  logic                i_m2_hready,
    input  logic [DWIDTH-1:0]   i_m2_hrdata,
    input  logic [1:0]          i_m2_hresp ,
    input  logic                i_m2_hgrant
   );

   localparam CWIDTH = AWIDTH+10;
   localparam WWIDTH = DWIDTH ;
   localparam RWIDTH = DWIDTH+4;

   if(ASYNC==1) begin: ASYNC_FIFO
     // ASYNC FIFO
     logic [AWIDTH-1:0]   m1_haddr_q;
     logic                m1_hwrite_q;
     logic                m1_hbusreq_q;
     logic [DWIDTH-1:0]   m1_hwdata_q;
     logic [1:0]          m1_htrans_q;
     logic [2:0]          m1_hsize_q;
     logic [2:0]          m1_hburst_q;

     logic                m1_hready;
     logic [DWIDTH-1:0]   m1_hrdata;
     logic [1:0]          m1_hresp ;
     logic                m1_hgrant;

     logic [AWIDTH-1:0]   m2_haddr;
     logic                m2_hwrite;
     logic                m2_hbusreq;
     logic [DWIDTH-1:0]   m2_hwdata;
     logic [1:0]          m2_htrans;
     logic [2:0]          m2_hsize;
     logic [2:0]          m2_hburst;

     logic                hready ;

     logic [AWIDTH-1:0]   m2_haddr_q;
     logic                m2_hwrite_q;
     logic                m2_hbusreq_q;
     logic [DWIDTH-1:0]   m2_hwdata_q;
     logic [1:0]          m2_htrans_q;
     logic [2:0]          m2_hsize_q;
     logic [2:0]          m2_hburst_q;

     logic                m1_vld_wrtrans  , m2_vld_wrtrans ;
     logic                m1_vld_rdtrans  , m2_vld_rdtrans ;
     logic                m1_vld_rsp      , m2_vld_rsp     ;

     logic                req_fifo_wr  ;
     logic                reqd_fifo_wr ;
     logic                rsp_fifo_wr  ;

     logic                req_fifo_rd,  req_fifo_rd_q;
     logic                reqd_fifo_rd, reqd_fifo_rd_q;
     logic                rsp_fifo_rd,  rsp_fifo_rd_q;

     logic [CWIDTH-1:0]   req_fifo_wdata;
     logic [CWIDTH-1:0]   req_fifo_rdata;
     logic [WWIDTH-1:0]   reqd_fifo_wdata;
     logic [WWIDTH-1:0]   reqd_fifo_rdata;
     logic [RWIDTH-1:0]   rsp_fifo_wdata;
     logic [RWIDTH-1:0]   rsp_fifo_rdata;

     logic                rsp_fifo_empty_n;
     logic                rsp_fifo_full;
     logic                rsp_fifo_full_q;
     logic                req_fifo_empty_n;
     logic                req_fifo_full;
     logic                req_fifo_full_q;
     logic                reqd_fifo_empty_n;
     logic                reqd_fifo_early_empty_n;
     logic                reqd_fifo_full;
     logic                reqd_fifo_full_q;
     logic                wrreq_fifo_full;

     typedef enum logic [2:0] {
        IDLE                  = 3'h0,
        WR_PHASE              = 3'h1,
        WR_DATA_PHASE         = 3'h2,
        RD_PHASE              = 3'h3,
        RD_DATA_PHASE         = 3'h4,
        RD_DATA_WR_ADDR_PHASE = 3'h5,
        RD_DATA_RD_ADDR_PHASE = 3'h6
     } state_t;

     state_t reqwr_state_q, reqwr_state_d ;
     state_t reqrd_state_q, reqrd_state_d ;

     assign wrreq_fifo_full     = (req_fifo_full_q | reqd_fifo_full_q);
     assign m1_vld_wrtrans      = o_m1_hready & ~wrreq_fifo_full & i_m1_hbusreq & (i_m1_hwrite & ((i_m1_htrans == AHB_TRANS_SEQ) | (i_m1_htrans == AHB_TRANS_NONSEQ)));
     assign m1_vld_rdtrans      = o_m1_hready & ~req_fifo_full_q & i_m1_hbusreq & (~i_m1_hwrite & ((i_m1_htrans == AHB_TRANS_SEQ) | (i_m1_htrans == AHB_TRANS_NONSEQ)));
     assign m1_vld_rsp          = m1_hready & rsp_fifo_empty_n;

     assign req_fifo_wdata      = { i_m1_htrans, i_m1_hsize, i_m1_hburst, i_m1_hwrite, i_m1_hbusreq, i_m1_haddr };
     assign reqd_fifo_wdata     = i_m1_hwdata ;

     assign { m1_hresp, m1_hgrant, m1_hready, m1_hrdata } = rsp_fifo_rdata;

     always_ff @(posedge i_m1_hclk, posedge i_m1_hreset) begin
        if (i_m1_hreset) begin
          reqwr_state_q     <= IDLE;
          req_fifo_full_q   <= '0;
          reqd_fifo_full_q  <= '0;
        end
        else begin
          reqwr_state_q     <= reqwr_state_d ;
          req_fifo_full_q   <= req_fifo_full   ;
          reqd_fifo_full_q  <= reqd_fifo_full  ;
        end
     end

     assign o_m1_hready = ((reqwr_state_q == RD_PHASE) && m1_vld_rsp) ?  m1_hready : hready      ;
     assign o_m1_hrdata = ((reqwr_state_q == RD_PHASE) && m1_vld_rsp) ?  m1_hrdata : '0          ;
     assign o_m1_hresp  = ((reqwr_state_q == RD_PHASE) && m1_vld_rsp) ?  m1_hresp  : AHB_RESP_OK ;
     assign o_m1_hgrant = (reqwr_state_q == RD_PHASE)                 ?  1'b1      : hready      ;
     assign o_m1_clkon  = (reqwr_state_q != IDLE) ;

     always_comb begin
        reqwr_state_d = reqwr_state_q ;
        req_fifo_wr   = '0 ;
        reqd_fifo_wr  = '0 ;
        rsp_fifo_rd   = '0 ;
        hready        = ~wrreq_fifo_full ;
        case(reqwr_state_q)
           IDLE : begin
              if(m1_vld_wrtrans ) begin
                 reqwr_state_d   = WR_PHASE ;
                 req_fifo_wr    = 1'b1 ;
              end
              else if (m1_vld_rdtrans) begin
                 reqwr_state_d   = RD_PHASE ;
                 req_fifo_wr    = 1'b1 ;
              end
           end
           WR_PHASE : begin
              reqd_fifo_wr = 1'b1;
              if(m1_vld_wrtrans) begin
                 req_fifo_wr    = 1'b1 ;
                 reqwr_state_d   = WR_PHASE ;
              end
              else if(m1_vld_rdtrans) begin
                 req_fifo_wr    = 1'b1 ;
                 reqwr_state_d   = RD_PHASE ;
              end
              else begin
                 reqwr_state_d   = IDLE ;
              end
           end
           RD_PHASE : begin
              hready = 1'b0 ;
              if(m1_vld_wrtrans && m1_vld_rsp) begin
                 reqwr_state_d   = WR_PHASE ;
                 req_fifo_wr     = 1'b1 ;
                 rsp_fifo_rd     = 1'b1 ;
              end
              else if (m1_vld_rdtrans && m1_vld_rsp) begin
                 reqwr_state_d   = RD_PHASE ;
                 req_fifo_wr     = 1'b1 ;
                 rsp_fifo_rd     = 1'b1 ;
              end
              else if (m1_vld_rsp) begin
                 reqwr_state_d   = IDLE;
                 rsp_fifo_rd     = 1'b1 ;
              end
           end
        endcase
     end

     ddr_fifo #(
        .WWIDTH    ( CWIDTH ),
        .RWIDTH    ( CWIDTH ),
        .DEPTH     ( 4  )
     ) u_ahb_req_buf (

        .i_scan_cgc_ctrl (i_scan_cgc_ctrl),
        .i_scan_mode     (i_scan_mode    ),
        .i_scan_rst_ctrl (i_scan_rst_ctrl),

        .i_clr           (1'b0),
        .i_loop_mode     ('0),
        .i_load_ptr      ('0),
        .i_stop_ptr      ('0),
        .i_start_ptr     ('0),

        .i_wclk          (i_m1_hclk),
        .i_wrst          (i_m1_hreset),
        .i_write         (req_fifo_wr),
        .i_wdata         (req_fifo_wdata),
        .o_early_full    (req_fifo_full),
        .o_full          (/*OPEN*/),

        .i_rclk          (i_m2_hclk),
        .i_rrst          (i_m2_hreset),
        .i_read          (req_fifo_rd),
        .o_rdata         (req_fifo_rdata),
        .o_early_empty_n (/*OPEN*/),
        .o_empty_n       (req_fifo_empty_n)
     );

     ddr_fifo #(
        .WWIDTH    ( WWIDTH ),
        .RWIDTH    ( WWIDTH ),
        .DEPTH     ( 4  )
     ) u_ahb_wrd_buf (
        .i_scan_cgc_ctrl (i_scan_cgc_ctrl),
        .i_scan_mode     (i_scan_mode    ),
        .i_scan_rst_ctrl (i_scan_rst_ctrl),

        .i_clr           (1'b0),
        .i_loop_mode     ('0),
        .i_load_ptr      ('0),
        .i_stop_ptr      ('0),
        .i_start_ptr     ('0),

        .i_wclk          (i_m1_hclk),
        .i_wrst          (i_m1_hreset),
        .i_write         (reqd_fifo_wr),
        .i_wdata         (reqd_fifo_wdata),
        .o_early_full    (reqd_fifo_full),
        .o_full          (/*OPEN*/),

        .i_rclk          (i_m2_hclk),
        .i_rrst          (i_m2_hreset),
        .i_read          (reqd_fifo_rd),
        .o_rdata         (reqd_fifo_rdata),
        .o_early_empty_n (reqd_fifo_early_empty_n),
        .o_empty_n       (reqd_fifo_empty_n)
     );

     assign { m2_htrans, m2_hsize, m2_hburst, m2_hwrite, m2_hbusreq, m2_haddr } = req_fifo_rdata ;
     assign m2_hwdata                                                           = reqd_fifo_rdata ;

     assign m2_vld_rsp        = i_m2_hready ;
     //assign m2_vld_rsp        = i_m2_hready & i_m2_hgrant ;
     assign m2_vld_wrtrans    = (req_fifo_empty_n & reqd_fifo_empty_n) & (m2_hbusreq & m2_hwrite & ((m2_htrans == AHB_TRANS_SEQ) | (m2_htrans == AHB_TRANS_NONSEQ)));
     assign m2_vld_rdtrans    = (req_fifo_empty_n & ~rsp_fifo_full_q) & (m2_hbusreq & ~m2_hwrite & ((m2_htrans == AHB_TRANS_SEQ) | (m2_htrans == AHB_TRANS_NONSEQ)));
     assign rsp_fifo_wdata    = { i_m2_hresp, i_m2_hgrant, i_m2_hready, i_m2_hrdata };

     always_ff @(posedge i_m2_hclk, posedge i_m2_hreset) begin
        if (i_m2_hreset) begin
          reqrd_state_q   <= IDLE ;
          req_fifo_rd_q   <= '0 ;
          reqd_fifo_rd_q  <= '0 ;
          rsp_fifo_full_q <= '0;
        end
        else begin
          reqrd_state_q   <= reqrd_state_d ;
          reqd_fifo_rd_q  <= reqd_fifo_rd ;
          rsp_fifo_full_q <= rsp_fifo_full ;
          if (req_fifo_rd | (req_fifo_rd_q & m2_vld_rsp))
             req_fifo_rd_q   <= req_fifo_rd ;
        end
     end

     always_ff @(posedge i_m2_hclk, posedge i_m2_hreset) begin
        if (i_m2_hreset) begin
          m2_haddr_q      <= '0;
          m2_hwrite_q     <= '0;
          m2_hbusreq_q    <= '0;
          m2_htrans_q     <= '0;
          m2_hsize_q      <= '0;
          m2_hburst_q     <= '0;
          m2_hwdata_q     <= '0;
        end
        else begin
          if (req_fifo_rd_q && !req_fifo_rd  && m2_vld_rsp ) begin
            m2_haddr_q      <= m2_haddr_q ;
            m2_hbusreq_q    <= 1'b0 ;
            m2_hwrite_q     <= 1'b0 ;
            m2_htrans_q     <= AHB_TRANS_IDLE  ;
            m2_hsize_q      <= m2_hsize   ;
            m2_hburst_q     <= m2_hburst  ;
          end
          else if(req_fifo_rd) begin
            m2_haddr_q      <= m2_haddr   ;
            m2_hwrite_q     <= m2_hwrite  ;
            m2_hbusreq_q    <= m2_hbusreq ;
            m2_htrans_q     <= m2_htrans  ;
            m2_hsize_q      <= m2_hsize   ;
            m2_hburst_q     <= m2_hburst  ;
          end
          if(reqd_fifo_rd) begin
            m2_hwdata_q     <= m2_hwdata  ;
          end

        end
     end

     assign o_m2_haddr      = m2_haddr_q  ;
     assign o_m2_hwrite     = m2_hwrite_q ;
     assign o_m2_hbusreq    = m2_hbusreq_q;
     assign o_m2_htrans     = m2_htrans_q ;
     assign o_m2_hsize      = m2_hsize_q  ;
     assign o_m2_hburst     = m2_hburst_q ;
     assign o_m2_hwdata     = m2_hwdata_q ;
     assign o_m2_clkon      = (reqrd_state_q != IDLE) ;

     always_comb begin
        reqrd_state_d  = reqrd_state_q ;
        req_fifo_rd    = '0 ;
        reqd_fifo_rd   = '0 ;
        rsp_fifo_wr    = '0 ;
        case(reqrd_state_q)
           IDLE : begin
              if( m2_vld_wrtrans ) begin
                 reqrd_state_d   = WR_PHASE ;
                 req_fifo_rd    = 1'b1 ;
              end
              else if ( m2_vld_rdtrans ) begin
                 reqrd_state_d   = RD_PHASE ;
                 req_fifo_rd    = 1'b1 ;
              end
           end
           WR_PHASE : begin
              if(~i_m2freq_hi & m2_vld_rsp & m2_vld_wrtrans & reqd_fifo_early_empty_n ) begin
                 reqd_fifo_rd   = 1'b1 ;
                 req_fifo_rd    = 1'b1 ;
                 reqrd_state_d  = WR_PHASE ;
              end
              else if(~i_m2freq_hi & m2_vld_rsp & m2_vld_rdtrans ) begin
                 reqd_fifo_rd   = 1'b1 ;
                 req_fifo_rd    = 1'b1 ;
                 reqrd_state_d  = RD_PHASE ;
              end
              else if(m2_vld_rsp) begin
                 reqd_fifo_rd    = 1'b1 ;
                 reqrd_state_d   = WR_DATA_PHASE ;
              end
           end
           WR_DATA_PHASE : begin
              if(m2_vld_rsp & m2_vld_wrtrans & reqd_fifo_early_empty_n ) begin
                 req_fifo_rd   = 1'b1 ;
                 reqrd_state_d  = WR_PHASE ;
              end
              else if(m2_vld_rsp & m2_vld_rdtrans ) begin
                 req_fifo_rd   = 1'b1 ;
                 reqrd_state_d  = RD_PHASE ;
              end
              else if(m2_vld_rsp) begin
                 reqrd_state_d  = IDLE ;
              end
           end
           RD_PHASE : begin
              if( ~i_m2freq_hi & m2_vld_rsp & m2_vld_wrtrans ) begin
                 req_fifo_rd    = 1'b1 ;
                 reqrd_state_d  = RD_DATA_WR_ADDR_PHASE ;
              end
              else if(~i_m2freq_hi & m2_vld_rsp & m2_vld_rdtrans ) begin
                 req_fifo_rd    = 1'b1 ;
                 reqrd_state_d  = RD_DATA_RD_ADDR_PHASE ;
              end
              else if(m2_vld_rsp) begin
                 reqrd_state_d  = RD_DATA_PHASE ;
              end
           end
           RD_DATA_WR_ADDR_PHASE : begin
              if(m2_vld_rsp & m2_vld_wrtrans ) begin
                 rsp_fifo_wr    = 1'b1 ;
                 reqd_fifo_rd   = 1'b1 ;
                 req_fifo_rd    = 1'b1 ;
                 reqrd_state_d  = WR_PHASE ;
              end
              else if(m2_vld_rsp & m2_vld_rdtrans ) begin
                 reqd_fifo_rd   = 1'b1 ;
                 rsp_fifo_wr    = 1'b1 ;
                 req_fifo_rd    = 1'b1 ;
                 reqrd_state_d  = RD_PHASE ;
              end
              else if(m2_vld_rsp) begin
                 reqd_fifo_rd   = 1'b1 ;
                 rsp_fifo_wr    = 1'b1 ;
                 reqrd_state_d  = WR_DATA_PHASE ;
              end
           end
           RD_DATA_RD_ADDR_PHASE : begin
              if(m2_vld_rsp & m2_vld_wrtrans ) begin
                 rsp_fifo_wr    = 1'b1 ;
                 req_fifo_rd    = 1'b1 ;
                 reqrd_state_d  = WR_PHASE ;
              end
              else if(m2_vld_rsp & m2_vld_rdtrans ) begin
                 rsp_fifo_wr    = 1'b1 ;
                 req_fifo_rd    = 1'b1 ;
                 reqrd_state_d  = RD_PHASE ;
              end
              else if(m2_vld_rsp) begin
                 rsp_fifo_wr    = 1'b1 ;
                 reqrd_state_d  = RD_DATA_PHASE ;
              end
           end
           RD_DATA_PHASE : begin
              if(m2_vld_rsp & m2_vld_wrtrans ) begin
                 rsp_fifo_wr    = 1'b1 ;
                 req_fifo_rd    = 1'b1 ;
                 reqrd_state_d  = WR_PHASE ;
              end
              else if(~i_m2freq_hi & m2_vld_rsp & m2_vld_rdtrans ) begin
                 rsp_fifo_wr    = 1'b1 ;
                 req_fifo_rd    = 1'b1 ;
                 reqrd_state_d  = RD_PHASE ;
              end
              else if(m2_vld_rsp) begin
                 rsp_fifo_wr    = 1'b1 ;
                 reqrd_state_d  = IDLE ;
              end
           end
        endcase
     end

     ddr_fifo #(
        .WWIDTH    ( RWIDTH ),
        .RWIDTH    ( RWIDTH ),
        .DEPTH     ( 4  )
     ) u_ahbm_rsp_buf (
        .i_scan_cgc_ctrl (i_scan_cgc_ctrl),
        .i_scan_mode     (i_scan_mode    ),
        .i_scan_rst_ctrl (i_scan_rst_ctrl),

        .i_clr           (1'b0),  //FIXME
        .i_loop_mode     ('0),
        .i_load_ptr      ('0),
        .i_stop_ptr      ('0),
        .i_start_ptr     ('0),

        .i_wclk          (i_m2_hclk),
        .i_wrst          (i_m2_hreset),
        .i_write         (rsp_fifo_wr),
        .i_wdata         (rsp_fifo_wdata),
        .o_early_full    (rsp_fifo_full),
        .o_full          (/*OPEN*/),

        .i_rclk          (i_m1_hclk),
        .i_rrst          (i_m1_hreset),
        .i_read          (rsp_fifo_rd),
        .o_rdata         (rsp_fifo_rdata),
        .o_early_empty_n (/*OPEN*/),
        .o_empty_n       (rsp_fifo_empty_n)
     );

  end
//else if (ISO_SYNC2LO==1) begin

//end
//else if (ISO_SYNC2HI==1) begin

//end
  else begin : FEEDTHROUGH
    assign  o_m2_haddr   = i_m1_haddr  ;
    assign  o_m2_hwrite  = i_m1_hwrite ;
    assign  o_m2_hbusreq = i_m1_hbusreq;
    assign  o_m2_hwdata  = i_m1_hwdata ;
    assign  o_m2_htrans  = i_m1_htrans ;
    assign  o_m2_hsize   = i_m1_hsize  ;
    assign  o_m2_hburst  = i_m1_hburst ;

    assign  o_m1_hready  = i_m2_hready;
    assign  o_m1_hrdata  = i_m2_hrdata;
    assign  o_m1_hresp   = i_m2_hresp ;
    assign  o_m1_hgrant  = i_m2_hgrant;
  end

endmodule
