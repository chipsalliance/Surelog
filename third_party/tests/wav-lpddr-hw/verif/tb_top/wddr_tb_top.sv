/****************************************************************************
*****************************************************************************
** Wavious LLC Proprietary
**
** Copyright (c) 2020 Wavious LLC. All rights reserved.
**
** All data and information contained in or disclosed by this document
** are confidential and proprietary information of Wavious LLC,
** and all rights therein are expressly reserved. By accepting this
** material, the recipient agrees that this material and the information
** contained therein are held in confidence and in trust and will not be
** used, copied, reproduced in whole or in part, nor its contents
** revealed in any manner to others without the express written
** permission of Wavious LLC.
*****************************************************************************
*
* Module    : ddr_phy_tb_top.sv
* Date      : 2020-02-25
* Desciption:
*
* Features:
* -----------------------------------------------------------------------
*    1) Run the "vpp" script to compile the *.sv.vpp file to *.sv
* $Id: wddr_tb_top.sv,v 1.85 2021/04/16 14:34:59 schilukuri Exp $
*
****************************************************************************/

`ifndef DDR_SYNTH
module wddr_tb_top;

`include "ddr_tb_defines.vh"

//Importing ALL Required Pkgs
import uvm_pkg::*;
//import wddr_pkg::*;

`ifdef DFIMC
    import dfimc::*;
`endif

`ifdef LPDDR4
    import lpddr4::*;
`endif

// Reset
logic                      i_rst         = '0;
logic                      i_prst         = '1;
// PLL
logic                      i_refclk      = '0;
logic                      i_refclk_alt  = '0;
logic                      o_pll_dtest;

// JTAG Interface
logic                      i_jtag_tck      = '0;
logic                      i_jtag_trst_n   = '1;
logic                      i_jtag_tms      = '0;
logic                      i_jtag_tdi      = '0;
logic                      o_jtag_tdo;

logic                      i_freeze_n      = '1;
logic                      i_hiz_n         = '1;
// AHB Interface
logic                      i_ahb_clk     = '0;
logic                      i_ahb_rst     = '0;
logic [AHB_AWIDTH-1:0]     o_ahb_haddr;
logic                      o_ahb_hwrite;
logic [31:0]               o_ahb_hwdata;
logic [1:0]                o_ahb_htrans;
logic [2:0]                o_ahb_hsize;
logic [2:0]                o_ahb_hburst;
logic                      o_ahb_hbusreq;
logic                      i_ahb_hgrant  = '0;
logic                      i_ahb_hready  = '0;
logic [31:0]               i_ahb_hrdata  = '0;
logic [1:0]                i_ahb_hresp   = '0;

// Update
logic                        o_dfi_ctrlupd_ack;
logic                        i_dfi_ctrlupd_req;
logic                        i_dfi_phyupd_ack;
logic                        o_dfi_phyupd_req;
logic [1:0]                  o_dfi_phyupd_type;

// Status
logic [1:0]                  i_dfi_freq_fsp;
logic [1:0]                  i_dfi_freq_ratio;
logic [4:0]                  i_dfi_frequency;
logic                        o_dfi_init_complete;
logic                        i_dfi_init_start;

// PHY Master
logic                        i_dfi_phymstr_ack;
logic                        o_dfi_phymstr_cs_state;
logic                        o_dfi_phymstr_req;
logic                        o_dfi_phymstr_state_sel;
logic [1:0]                  o_dfi_phymstr_type;

// Low Power Control
logic                        o_dfi_lp_ctrl_ack;
logic                        i_dfi_lp_ctrl_req;
logic [5:0]                  i_dfi_lp_ctrl_wakeup;
logic                        o_dfi_lp_data_ack;
logic                        i_dfi_lp_data_req;
logic [5:0]                  i_dfi_lp_data_wakeup;

// Value plus args
logic                      loopback = 1;
logic                      gbmode = 0;

reg dfi_reset;
reg ddr_reset;

`ifdef DFIMC
    reg clk;
    reg freq_change_done = 0;
    reg [13:0] dfi_address_p0;
    reg [13:0] dfi_address_p1;
    reg [13:0] dfi_address_p2;
    reg [13:0] dfi_address_p3;
    reg [1:0] dfi_cke_p0;
    reg [1:0] dfi_cke_p1;
    reg [1:0] dfi_cke_p2;
    reg [1:0] dfi_cke_p3;
    reg [1:0] dfi_cs_p0;
    reg [1:0] dfi_cs_p1;
    reg [1:0] dfi_cs_p2;
    reg [1:0] dfi_cs_p3;
    logic [1:0] dfi_dram_clk_disable = 0;
    reg dfi_dram_clk_disable_p0;
    reg dfi_dram_clk_disable_p1;
    reg dfi_dram_clk_disable_p2;
    reg dfi_dram_clk_disable_p3;
    reg dfi_parity_in_p0;
    reg dfi_parity_in_p1;
    reg dfi_parity_in_p2;
    reg dfi_parity_in_p3;
    reg [1:0] dfi_reset_n_p0;
    reg [1:0] dfi_reset_n_p1;
    reg [1:0] dfi_reset_n_p2;
    reg [1:0] dfi_reset_n_p3;
    reg [31:0] dfi_wrdata_p0;
    reg [31:0] dfi_wrdata_p1;
    reg [31:0] dfi_wrdata_p2;
    reg [31:0] dfi_wrdata_p3;
    reg [1:0] dfi_wrdata_cs_n_p0;
    reg [1:0] dfi_wrdata_cs_n_p1;
    reg [1:0] dfi_wrdata_cs_n_p2;
    reg [1:0] dfi_wrdata_cs_n_p3;
    reg       dfi_wrdata_en_p0;
    reg       dfi_wrdata_en_p1;
    reg       dfi_wrdata_en_p2;
    reg       dfi_wrdata_en_p3;
    reg [3:0] dfi_wrdata_mask_p0;
    reg [3:0] dfi_wrdata_mask_p1;
    reg [3:0] dfi_wrdata_mask_p2;
    reg [3:0] dfi_wrdata_mask_p3;
    reg [31:0] dfi_rddata_w0;
    reg [31:0] dfi_rddata_w1;
    reg [31:0] dfi_rddata_w2;
    reg [31:0] dfi_rddata_w3;
    reg [31:0] dfi_rddata_w0_dq2_dq3; // FIXME
    reg [31:0] dfi_rddata_w1_dq2_dq3; // FIXME
    reg [31:0] dfi_rddata_w2_dq2_dq3; // FIXME
    reg [31:0] dfi_rddata_w3_dq2_dq3; // FIXME
    reg [1:0] dfi_rddata_cs_n_p0;
    reg [1:0] dfi_rddata_cs_n_p1;
    reg [1:0] dfi_rddata_cs_n_p2;
    reg [1:0] dfi_rddata_cs_n_p3;
    reg [3:0] dfi_rddata_dbi_w0;
    reg [3:0] dfi_rddata_dbi_w1;
    reg [3:0] dfi_rddata_dbi_w2;
    reg [3:0] dfi_rddata_dbi_w3;
    reg [3:0] dfi_rddata_dbi_w0_dq2_dq3; // FIXME
    reg [3:0] dfi_rddata_dbi_w1_dq2_dq3; // FIXME
    reg [3:0] dfi_rddata_dbi_w2_dq2_dq3; // FIXME
    reg [3:0] dfi_rddata_dbi_w3_dq2_dq3; // FIXME
    reg [1:0] dfi_rddata_dnv_w0 = 0;
    reg [1:0] dfi_rddata_dnv_w1 = 0;
    reg [1:0] dfi_rddata_dnv_w2 = 0;
    reg [1:0] dfi_rddata_dnv_w3 = 0;
    reg       dfi_rddata_en_p0;
    reg       dfi_rddata_en_p1;
    reg       dfi_rddata_en_p2;
    reg       dfi_rddata_en_p3;
    reg       dfi_rddata_valid_w0;
    reg       dfi_rddata_valid_w1;
    reg       dfi_rddata_valid_w2;
    reg       dfi_rddata_valid_w3;

    reg         dfi_ctrlupd_req_sig = '0;
    reg         dfi_phyupd_ack_sig = '0;
    reg         dfi_phymstr_ack_sig = '0;
    reg         dfi_lp_ctrl_req_sig = '0;
    reg [5:0]   dfi_lp_ctrl_wakeup_sig = '0;
    reg         dfi_lp_data_req_sig = '0;
    reg [5:0]   dfi_lp_data_wakeup_sig = '0;

    reg dfi_ctrlupd_req;
    reg dfi_ctrlupd_ack;
    reg dfi_phyupd_req;
    reg [1:0] dfi_phyupd_type;
    reg dfi_phyupd_ack;
    reg [7:0] dfi_data_byte_disable;
    //reg dfi_init_complete;
    reg dfi_init_start;
    logic dfi_init_start_sig = 1;
    logic dfi_reset_sig = 0;
    reg [1:0] dfi_freq_ratio;
    reg [4:0] dfi_frequency;
    reg dfi_lp_ctrl_req;
    reg dfi_lp_data_req;
    logic [5:0] dfi_lp_wakeup = 0;
    reg [5:0] dfi_lp_ctrl_wakeup;
    reg [5:0] dfi_lp_data_wakeup;
    reg dfi_lp_ack = 0;
    reg dfi_lp_ctrl_ack;
    reg dfi_lp_data_ack;
    reg [1:0] dfi_error = 0;
    reg [7:0] dfi_error_info = 0;
    reg dfi_phymstr_cs_state;
    reg dfi_phymstr_req;
    reg dfi_phymstr_state_sel;
    reg [1:0] dfi_phymstr_type;
    reg dfi_phymstr_ack;
    reg dfi_disconnect_error;
    reg [7:0] dfi_rdlvl_req =0;
    reg [15:0] dfi_phy_rdlvl_cs_n =0;
    reg [7:0] dfi_rdlvl_en;
    reg [15:0] dfi_rdlvl_resp =0;
    reg [7:0] dfi_rdlvl_gate_req =0;
    reg [15:0] dfi_phy_rdlvl_gate_cs_n =0;
    reg [7:0] dfi_rdlvl_gate_en;
    reg [7:0] dfi_wrlvl_req =0;
    reg [15:0] dfi_phy_wrlvl_cs_n =0;
    reg [7:0] dfi_wrlvl_en ;
    reg [7:0] dfi_wrlvl_resp =0;
    reg dfi_calvl_req = 0;
    reg [1:0] dfi_phy_calvl_cs_n = 0;
    reg dfi_calvl_en;
    reg dfi_calvl_capture;
    reg [1:0] dfi_calvl_resp = 0;
    reg [31:0] dfi_lvl_pattern;
    reg [7:0] dfi_lvl_periodic ;
    reg [1:0] dfi_phylvl_req_cs_n =0;
    reg [1:0] dfi_phylvl_ack_cs_n ;
    reg [63:0] dfi_db_train_resp_p2 =0;
    reg [63:0] dfi_db_train_resp_p3 =0;
    reg dfi_calvl_ca_sel_p0 ;
    reg dfi_calvl_ca_sel_p1 ;
    reg dfi_calvl_ca_sel_p2 ;
    reg dfi_calvl_ca_sel_p3 ;
    reg dfi_calvl_strobe_p0 ;
    reg dfi_calvl_strobe_p1 ;
    reg dfi_calvl_strobe_p2 ;
    reg dfi_calvl_strobe_p3 ;
    reg [6:0] dfi_calvl_data_p0 ;
    reg [6:0] dfi_calvl_data_p1 ;
    reg [6:0] dfi_calvl_data_p2 ;
    reg [6:0] dfi_calvl_data_p3 ;
    reg dfi_calvl_done ;
    reg dfi_calvl_result = 0;
    reg [7:0] dfi_rdlvl_done;
    reg [7:0] dfi_wrlvl_strobe_p0 ;
    reg [7:0] dfi_wrlvl_strobe_p1 ;
    reg [7:0] dfi_wrlvl_strobe_p2 ;
    reg [7:0] dfi_wrlvl_strobe_p3 ;
    reg [15:0] dfi_phy_wdqlvl_cs =0;
    reg [7:0] dfi_wdqlvl_en ;
    reg [7:0] dfi_wdqlvl_req =0;
    reg [15:0] dfi_wdqlvl_resp =0;
    reg [7:0] dfi_rdlvl_edge =0;
    reg dfi_parity_error;
    reg dfi_wdqlvl_result =0;
    logic [7:0] dfi_wdqlvl_done;
    int clockdelay = 2;
    int changedelay = 10;
    bit initialized = 0;
    bit freqChangeAccepted = 0;
    int count = 0;

    logic [1:0]                dfi_wck_cs_p0           = '0;
    logic                      dfi_wck_en_p0           = '0;
    logic [TWIDTH-1:0]         dfi_wck_toggle_p0       = '0;
    logic [1:0]                dfi_wck_cs_p1           = '0;
    logic                      dfi_wck_en_p1           = '0;
    logic [TWIDTH-1:0]         dfi_wck_toggle_p1       = '0;
    logic [1:0]                dfi_wck_cs_p2           = '0;
    logic                      dfi_wck_en_p2           = '0;
    logic [TWIDTH-1:0]         dfi_wck_toggle_p2       = '0;
    logic [1:0]                dfi_wck_cs_p3           = '0;
    logic                      dfi_wck_en_p3           = '0;
    logic [TWIDTH-1:0]         dfi_wck_toggle_p3       = '0;

    reg [1:0] dfi_freq_fsp;
    reg dfi_ctrlmsg_req;
    reg dfi_ctrlmsg_ack = 0;
    reg [7:0] dfi_ctrlmsg;
    reg [15:0] dfi_ctrlmsg_data;

`else
    // Command
    logic [2*AWIDTH-1:0]         i_dfi_address_p0          = '0;     // For DDR4 bits[16:14] are not used
    logic [1:0]                  i_dfi_cke_p0              = '0;     // DDR1/2/3/4 and LPDDR3/4
    logic [1:0]                  i_dfi_cs_p0               = '0;
    logic                        i_dfi_dram_clk_disable_p0 = '1;
    logic [2*AWIDTH-1:0]         i_dfi_address_p1          = '0;     // For DDR4 bits[16:14] are not used
    logic [1:0]                  i_dfi_cke_p1              = '0;     // DDR1/2/3/4 and LPDDR3/4
    logic [1:0]                  i_dfi_cs_p1               = '0;
    logic                        i_dfi_dram_clk_disable_p1 = '1;
    logic [2*AWIDTH-1:0]         i_dfi_address_p2          = '0;     // For DDR4 bits[16:14] are not used
    logic [1:0]                  i_dfi_cke_p2              = '0;     // DDR1/2/3/4 and LPDDR3/4
    logic [1:0]                  i_dfi_cs_p2               = '0;
    logic                        i_dfi_dram_clk_disable_p2 = '1;
    logic [2*AWIDTH-1:0]         i_dfi_address_p3          = '0;     // For DDR4 bits[16:14] are not used
    logic [1:0]                  i_dfi_cke_p3              = '0;     // DDR1/2/3/4 and LPDDR3/4
    logic [1:0]                  i_dfi_cs_p3               = '0;
    logic                        i_dfi_dram_clk_disable_p3 = '1;

    // Write
    logic [2*NUM_DQ*SWIDTH-1:0]  i_dfi_wrdata_p0           = '0;
    logic [2*NUM_DQ*MWIDTH-1:0]  i_dfi_wrdata_mask_p0      = '0;
    logic                        i_dfi_parity_in_p0        = '0;
    logic [1:0]                  i_dfi_wrdata_cs_p0        = '0;
    logic                        i_dfi_wrdata_en_p0        = '0;
    logic [1:0]                  i_dfi_wck_cs_p0           = '0;
    logic                        i_dfi_wck_en_p0           = '0;
    logic [TWIDTH-1:0]           i_dfi_wck_toggle_p0       = '0;
    logic [2*NUM_DQ*SWIDTH-1:0]  i_dfi_wrdata_p1           = '0;
    logic [2*NUM_DQ*MWIDTH-1:0]  i_dfi_wrdata_mask_p1      = '0;
    logic                        i_dfi_parity_in_p1        = '0;
    logic [1:0]                  i_dfi_wrdata_cs_p1        = '0;
    logic                        i_dfi_wrdata_en_p1        = '0;
    logic [1:0]                  i_dfi_wck_cs_p1           = '0;
    logic                        i_dfi_wck_en_p1           = '0;
    logic [TWIDTH-1:0]           i_dfi_wck_toggle_p1       = '0;
    logic [2*NUM_DQ*SWIDTH-1:0]  i_dfi_wrdata_p2           = '0;
    logic [2*NUM_DQ*MWIDTH-1:0]  i_dfi_wrdata_mask_p2      = '0;
    logic                        i_dfi_parity_in_p2        = '0;
    logic [1:0]                  i_dfi_wrdata_cs_p2        = '0;
    logic                        i_dfi_wrdata_en_p2        = '0;
    logic [1:0]                  i_dfi_wck_cs_p2           = '0;
    logic                        i_dfi_wck_en_p2           = '0;
    logic [TWIDTH-1:0]           i_dfi_wck_toggle_p2       = '0;
    logic [2*NUM_DQ*SWIDTH-1:0]  i_dfi_wrdata_p3           = '0;
    logic [2*NUM_DQ*MWIDTH-1:0]  i_dfi_wrdata_mask_p3      = '0;
    logic                        i_dfi_parity_in_p3        = '0;
    logic [1:0]                  i_dfi_wrdata_cs_p3        = '0;
    logic                        i_dfi_wrdata_en_p3        = '0;
    logic [1:0]                  i_dfi_wck_cs_p3           = '0;
    logic                        i_dfi_wck_en_p3           = '0;
    logic [TWIDTH-1:0]           i_dfi_wck_toggle_p3       = '0;

    // Read Data
    logic [1:0]                  i_dfi_rddata_cs_p0        = '0;
    logic                        i_dfi_rddata_en_p0        = '0;
    logic [2*NUM_DQ*SWIDTH-1:0]  o_dfi_rddata_w0;
    logic [2*NUM_DQ*MWIDTH-1:0]  o_dfi_rddata_dbi_w0;
    logic                        o_dfi_rddata_valid_w0;
    logic [1:0]                  i_dfi_rddata_cs_p1        = '0;
    logic                        i_dfi_rddata_en_p1        = '0;
    logic [2*NUM_DQ*SWIDTH-1:0]  o_dfi_rddata_w1;
    logic [2*NUM_DQ*MWIDTH-1:0]  o_dfi_rddata_dbi_w1;
    logic                        o_dfi_rddata_valid_w1;
    logic [1:0]                  i_dfi_rddata_cs_p2        = '0;
    logic                        i_dfi_rddata_en_p2        = '0;
    logic [2*NUM_DQ*SWIDTH-1:0]  o_dfi_rddata_w2;
    logic [2*NUM_DQ*MWIDTH-1:0]  o_dfi_rddata_dbi_w2;
    logic                        o_dfi_rddata_valid_w2;
    logic [1:0]                  i_dfi_rddata_cs_p3        = '0;
    logic                        i_dfi_rddata_en_p3        = '0;
    logic [2*NUM_DQ*SWIDTH-1:0]  o_dfi_rddata_w3;
    logic [2*NUM_DQ*MWIDTH-1:0]  o_dfi_rddata_dbi_w3;
    logic                        o_dfi_rddata_valid_w3;

`endif

logic                      o_dfi_clk;
logic                      dfi_clk_nodly;
// Pads
wire                       pad_ddr_reset ;
wire [NUM_DQ-1:0]          pad_wck_t     ;
wire [NUM_DQ-1:0]          pad_wck_c     ;
wire [NUM_DQ-1:0]          pad_dqs_t     ;
wire [NUM_DQ-1:0]          pad_dqs_c     ;
wire [NUM_DQ*DQ_WIDTH-1:0] pad_dq        ;
wire [10:0]                pad_ca        ;
wire                       pad_ck_c      ;
wire                       pad_ck_t      ;

wire pad_ddr_ca_ca0 ;
wire pad_ddr_ca_ca1 ;
wire pad_ddr_ca_ca2 ;
wire pad_ddr_ca_ca3 ;
wire pad_ddr_ca_ca4 ;
wire pad_ddr_ca_ca5 ;
wire pad_ddr_ca_ca6 ;
wire pad_ddr_ca_cs0 ;
wire pad_ddr_ca_cs1 ;
wire pad_ddr_ca_cke0 ;
wire pad_ddr_ca_cke1 ;
wire pad_ddr_ca_ck_c ;
wire pad_ddr_ca_ck_t ;

int state = 0;

`include "ddr_tb_ramfile_map.sv"
`include "sequences/wddr_seq_lib.svh"
`ifdef DFIMC
    `include "dfiSeqlib.sv"
`endif
`include "tests/wddr_test_lib.svh"

//--------------------------------------------------------------------
// GLS
//--------------------------------------------------------------------
`ifdef GLS
//import "DPI-C" function string getenv(input string env_name);

initial begin
  bit valid_corner = 0;

  `ifdef CORNER_FF
   $sdf_annotate({"../gls/ddr_phy_1x32.func.sigRCminDP_FASTM40C.sdf"}, wddr_tb_top.u_phy_1x32, , "sdf.fast.log", "MINIMUM");
   valid_corner = 1;
   $display("INFO: SDF Anntation for FF corner and min delays...");
 `endif

  `ifdef CORNER_SS
   $sdf_annotate({"../gls/ddr_phy_1x32.func.sigRCminDP_SLOW125C.sdf"}, wddr_tb_top.u_phy_1x32, , "sdf.slow.log", "MAXIMUM");
    valid_corner = 1;
   $display("INFO: SDF Anntation for SS corner and max delays...");
  `endif

  if(!valid_corner) begin
    `uvm_fatal("no valid GLS corner!", "put one in")
  end
end
// Added 200ps delay to account for internal clock to o_dfi_clk skew.
// o_dfi_clk is ~110ps faster than internal clock to DFI interface flops.
assign #200ps o_dfi_clk = dfi_clk_nodly ;

`else
assign o_dfi_clk = dfi_clk_nodly ;

`endif

//--------------------------------------------------------------------
// SPICE
//--------------------------------------------------------------------
`ifdef DUMP_SPICE_VCD
`ifdef DDR_SPICE_VCD_DDR_DQ
   initial begin
         $dumpfile("/simulation2/schilukuri/sims/dv_spice/t_ddr_spice.dq.vcd");
         $dumpvars(1, wddr_tb_top, `TB_HIER.u_phy_ch0.u_phy_dq0.u_dq);
         $dumpoff;
         #100ns ;
         @(posedge wddr_tb_top.u_phy_1x32.u_phy.u_dfi.u_dfi_buf.i_ts_enable) ;
         @(posedge wddr_tb_top.u_phy_1x32.u_phy.u_dfi.u_dfi_buf.i_ts_enable) ;
         $dumpon;
         #200ns ;
         $dumpoff;
   end
`endif

`ifdef DDR_SPICE_VCD_DDR_CA
   initial begin
         $dumpfile("/simulation2/schilukuri/sims/dv_spice/t_ddr_spice.ca.vcd");
         $dumpvars(1, wddr_tb_top, `TB_HIER.u_phy_ch0.u_phy_ca.u_ca);
         $dumpoff;
         #100ns ;
         @(posedge wddr_tb_top.u_phy_1x32.u_phy.u_dfi.u_dfi_buf.i_ts_enable) ;
         @(posedge wddr_tb_top.u_phy_1x32.u_phy.u_dfi.u_dfi_buf.i_ts_enable) ;
         $dumpon;
         #200ns ;
         $dumpoff;
   end
`endif

`ifdef DDR_SPICE_VCD_DDR_1X32
   initial begin
         $dumpfile("/simulation2/schilukuri/sims/dv_spice/t_ddr_spice.phy.vcd");
         $dumpvars(0, wddr_tb_top, wddr_tb_top.u_phy_1x32);
         $dumpoff;
         #100ns ;
         @(posedge wddr_tb_top.u_phy_1x32.u_phy.u_dfi.u_dfi_buf.i_ts_enable) ;
         @(posedge wddr_tb_top.u_phy_1x32.u_phy.u_dfi.u_dfi_buf.i_ts_enable) ;
         $dumpon;
         #200ns ;
         $dumpoff;
   end
`endif

`endif

//--------------------Clock and reset
logic pll_clk_0, pll_clk_90, pll_clk_180, pll_clk_270 ;
int i, x,y,z;

logic [31:0]  wdata;
logic [31:0]  rdata;

//AHB Signals
wire          s_ahb_hsel;
wire [31:0]   s_ahb_haddr;
wire [1:0]    s_ahb_htrans;
wire [2:0]    s_ahb_hsize;
wire          s_ahb_hwrite;
wire          s_ahb_hready;
wire [3:0]    s_ahb_hprot;
wire [2:0]    s_ahb_hburst;
wire          s_ahb_hmastlock;
wire [31:0]   s_ahb_hwdata;

wire          s_ahb_hreadyout;
wire [1:0]    s_ahb_hresp;
wire [31:0]   s_ahb_hrdata;

logic [1:0] o_irq;

wav_APB_if APB_if (.reset(i_prst), .clock (i_ahb_clk));

initial begin
    $timeformat(-9, 0, " ns", 10);
    //uvm_config_db #(virtual wav_AHB_if)::set(uvm_root::get(), "*tb.AHB_agent*" , "AHB_vif", AHB_if);
    //uvm_config_db #(virtual ahb_if)::set(uvm_root::get(), "*tb.ahb_agent*" , "ahb_if", AHB_if);
    uvm_config_db#(virtual wav_APB_if)::set(uvm_root::get(), "*", "APB_vif", APB_if);
    run_test();
end

always #(PLL_PERIOD/2)         pll_clk_0    = ~pll_clk_0 ;
assign #(PLL_PERIOD/4)         pll_clk_90   = pll_clk_0 ;
assign                         pll_clk_180  = ~pll_clk_0 ;
assign                         pll_clk_270  = ~pll_clk_90 ;

//always #(AHBCLK_PERIOD/2)      i_ahb_clk    = ~i_ahb_clk ;
always #(REFCLK_PERIOD/2)      i_ahb_clk    = ~i_ahb_clk ;
always #(REFCLK_PERIOD/2)      i_refclk     = ~i_refclk ;
always #(REFCLK_ALT_PERIOD/2)  i_refclk_alt = ~i_refclk_alt ;
always #(TCK_PERIOD/2)         i_jtag_tck   = ~i_jtag_tck ;

//--------------------Wait clock tasks
//TBD Later - remove whichever taks is not required
//TBD refer the other tasks which are part of test for config reference
task automatic wait_tck;
    input [31:0] num_cycles;
    begin
        repeat (num_cycles) @(posedge i_jtag_tck);
        #1ps;
    end
endtask

task automatic wait_hclk;
    input [31:0] num_cycles;
    begin
        repeat (num_cycles) @(posedge i_ahb_clk);
        #1;
    end
endtask

task automatic wait_dficlk;
    input [31:0] num_cycles;
    begin
        repeat (num_cycles) @(posedge o_dfi_clk);
        #1;
    end
endtask

task automatic wait_refclk;
    input [31:0] num_cycles;
    begin
        repeat (num_cycles) @(posedge i_refclk);
        #1;
    end
endtask

task automatic wait_refclk_alt;
    input [31:0] num_cycles;
    begin
        repeat (num_cycles) @(posedge i_refclk_alt);
        #1;
    end
endtask

//--------------------DUT reset
task automatic por;
    begin
        force wddr_tb_top.u_phy_1x32.i_ahb_clk    = '0;
        force wddr_tb_top.u_phy_1x32.i_ana_refclk = '0;
        force wddr_tb_top.u_phy_1x32.i_refclk     = '0;
        force wddr_tb_top.u_phy_1x32.i_refclk_alt = '0;
        force wddr_tb_top.u_phy_1x32.i_jtag_tck   = '0;
        wait_refclk(2);
        i_prst        = 1'b0;
        i_rst         = 1'b1;
        i_jtag_trst_n = 1'b0;
        wait_refclk(5);
        i_prst        = 1'b1;
        wait_refclk(5);
        i_rst         = 1'b0;
        i_jtag_trst_n = 1'b1;
        wait_refclk(5);
        release wddr_tb_top.u_phy_1x32.i_ahb_clk    ;
        release wddr_tb_top.u_phy_1x32.i_ana_refclk ;
        release wddr_tb_top.u_phy_1x32.i_refclk     ;
        release wddr_tb_top.u_phy_1x32.i_refclk_alt ;
        release wddr_tb_top.u_phy_1x32.i_jtag_tck   ;
        wait_refclk(10);
    end
endtask

initial begin
    $assertoff(0,wddr_tb_top.u_phy_1x32.u_phy.u_mcu.u_ibex_core);
    por();
    #1000;
end

initial begin

    if ($value$plusargs("LOOPBACK=%f", loopback)) begin
        $display("LOOPBACK Disabled");
    end

    if ($value$plusargs("GBMODE=%f", gbmode)) begin
        $display("GBMODE Enabled");
    end
end

wire [31:0] paddr;
wire psel;
wire pwrite;
wire [31:0] pwdata;

assign paddr = i_prst ? APB_if.paddr : 32'h0;
assign pwdata = i_prst ? APB_if.pwdata : 32'h0;
assign pwrite = i_prst  ? APB_if.pwrite : 0;
assign psel = i_prst ? APB_if.psel : 0;

//AHB Signals
wire           hsel;
wire  [31:0]   haddr;
wire  [1:0]    htrans;
wire  [2:0]    hsize;
wire           hwrite;
wire           hready;
wire  [2:0]    hburst;
wire  [31:0]   hwdata;
wire           hreadyout;
wire  [1:0]    hresp;
wire  [31:0]   hrdata;

`ifdef GLS
  assign #2ns hsel    = s_ahb_hsel;
  assign #2ns haddr   = s_ahb_haddr;
  assign #2ns htrans  = s_ahb_htrans;
  assign #2ns hsize   = s_ahb_hsize;
  assign #2ns hwrite  = s_ahb_hwrite;
  assign #2ns hready  = s_ahb_hready;
  assign #2ns hburst  = s_ahb_hburst;
  assign #2ns hwdata  = s_ahb_hwdata;

  assign s_ahb_hreadyout = hreadyout;
  assign s_ahb_hresp          = hresp    ;
  assign s_ahb_hrdata         = hrdata   ;
`else
  assign hsel    = s_ahb_hsel;
  assign haddr   = s_ahb_haddr;
  assign htrans  = s_ahb_htrans;
  assign hsize   = s_ahb_hsize;
  assign hwrite  = s_ahb_hwrite;
  assign hready  = s_ahb_hready;
  assign hburst  = s_ahb_hburst;
  assign hwdata  = s_ahb_hwdata;

  assign s_ahb_hreadyout = hreadyout;
  assign s_ahb_hresp     = hresp    ;
  assign s_ahb_hrdata    = hrdata   ;
`endif

apb_to_ahb  apb2ahb(
    .hburst      (s_ahb_hburst     ),
    .hsel        (s_ahb_hsel       ),
    .hsize       (s_ahb_hsize      ),
    .htrans      (s_ahb_htrans     ),
    .hwrite      (s_ahb_hwrite     ),
    .haddr       (s_ahb_haddr      ),
    .hwdata      (s_ahb_hwdata     ),
    .hmastlock   (s_ahb_hmastlock  ),
    .hprot       (s_ahb_hprot      ),
    .hready      (s_ahb_hready     ),
    .hreadyout   (s_ahb_hreadyout  ), //Input
    //.hgrant      (1'b1 ),
    .hresp       (s_ahb_hresp      ),
    .hrdata      (s_ahb_hrdata     ),
    .pclk        (i_ahb_clk        ),
    .presetn     (i_prst           ),
    .psel        (psel             ),
    .penable     (APB_if.penable   ),
    .pwrite      (pwrite           ),
    .pwdata      (pwdata           ),
    .paddr       (paddr            ),
    .prdata      (APB_if.prdata    ),
    .pready      (APB_if.pready    ),
    .pslverr     (APB_if.pslverr   )
);

/*
ddr_phy_1x16 u_phy_1x16 (

    .i_phy_rst                   (i_rst             ),

    .i_dfi_clk_on                ('0                ), // FIXME
    .o_dfi_clk                   (o_dfi_clk         ),

    .i_ana_refclk                (i_refclk          ),
    .i_refclk                    (i_refclk          ),
    .i_refclk_alt                (i_refclk_alt      ),
    .o_refclk_on                 (                  ),
    .o_dtst                      (                  ),

    .i_irq                       ('0),
    .o_irq                       (o_irq),

    .ana_vref_in                 ('0),
    .ana_vref_out                (),

    .i_gpb                       ('0),
    .o_gpb                       (),

    .i_pll_clk_0                 ('0),
    .i_pll_clk_90                ('0),
    .i_pll_clk_180               ('0),
    .i_pll_clk_270               ('0),
    .i_vco0_clk                  ('0),

    .o_pll_clk_0                 (),
    .o_pll_clk_90                (),
    .o_pll_clk_180               (),
    .o_pll_clk_270               (),
    .o_vco0_clk                  (),

    .i_test_mode                 ('0),
    .i_scan_mode                 ('0),
    .i_scan_clk                  ('0),
    .i_scan_freq_en              ('0),
    .i_scan_en                   ('0),
    .i_scan_cgc_ctrl             ('0),
    .i_scan_rst_ctrl             ('0),
    .i_scan_set_ctrl             ('0),

    .i_freeze_n                  ('1),
    .i_freeze_n_aon              ('1),
    .i_freeze_n_hv               ('1),
    .o_freeze_n_aon              (),
    .o_freeze_n_hv               (),

    .i_hiz_n                     ('1),

    .i_jtag_tck                  (i_jtag_tck),
    .i_jtag_trst_n               (i_jtag_trst_n),
    .i_jtag_bsr_mode             (i_jtag_bsr_mode),
    .i_jtag_capture              (i_jtag_capture),
    .i_jtag_shift                (i_jtag_shift),
    .i_jtag_update               (i_jtag_update),
    .i_jtag_tdi                  (i_jtag_tdi),
    .o_jtag_tdo                  (o_jtag_tdo),

    .i_ahb_clk                   (i_ahb_clk        ),
    .i_ahb_rst                   (i_rst            ),
    .i_ahb_csr_rst               (i_rst            ),
    .o_ahb_clk_on                (                 ),

    .i_ahb_haddr                 (s_ahb_haddr      ),
    .i_ahb_hwrite                (s_ahb_hwrite     ),
    .i_ahb_hsel                  (s_ahb_hsel       ),
    .i_ahb_hwdata                (s_ahb_hwdata     ),
    .i_ahb_htrans                (s_ahb_htrans     ),
    .i_ahb_hsize                 (s_ahb_hsize      ),
    .i_ahb_hburst                (s_ahb_hburst     ),
    .o_ahb_hready                (s_ahb_hreadyout  ),
    .o_ahb_hrdata                (s_ahb_hrdata     ),
    .o_ahb_hresp                 (s_ahb_hresp      ),

    .o_ahb_haddr                 (o_ahb_haddr       ),
    .o_ahb_hwrite                (o_ahb_hwrite      ),
    .o_ahb_hwdata                (o_ahb_hwdata      ),
    .o_ahb_htrans                (o_ahb_htrans      ),
    .o_ahb_hsize                 (o_ahb_hsize       ),
    .o_ahb_hburst                (o_ahb_hburst      ),
    .o_ahb_hbusreq               (o_ahb_hbusreq     ),
    .i_ahb_hgrant                (i_ahb_hgrant      ),
    .i_ahb_hready                (i_ahb_hready      ),
    .i_ahb_hrdata                (i_ahb_hrdata      ),
    .i_ahb_hresp                 (i_ahb_hresp       ),

    `ifdef DFIMC
        .o_dfi_ctrlupd_ack           (dfi_ctrlupd_ack),
        .i_dfi_ctrlupd_req           (dfi_ctrlupd_req),
        .i_dfi_phyupd_ack            (dfi_phyupd_ack),
        .o_dfi_phyupd_req            (dfi_phyupd_req),
        .o_dfi_phyupd_type           (dfi_phyupd_type),

        .i_dfi_freq_fsp              ('0),
        .i_dfi_freq_ratio            (dfi_freq_ratio),
        .i_dfi_frequency             (dfi_frequency),
        .o_dfi_init_complete         (o_dfi_init_complete),
        //.i_dfi_init_start            (dfi_init_start_sig),
        .i_dfi_init_start            (dfi_init_start),

        .i_dfi_phymstr_ack           (dfi_phymstr_ack),
        .o_dfi_phymstr_cs_state      (dfi_phymstr_cs_state),
        .o_dfi_phymstr_req           (dfi_phymstr_req),
        .o_dfi_phymstr_state_sel     (dfi_phymstr_state_sel),
        .o_dfi_phymstr_type          (dfi_phymstr_type),

        .o_dfi_lp_ctrl_ack           (dfi_lp_ctrl_ack),
        .i_dfi_lp_ctrl_req           (dfi_lp_ctrl_req),
        .i_dfi_lp_ctrl_wakeup        (dfi_lp_ctrl_wakeup),
        .o_dfi_lp_data_ack           (dfi_lp_data_ack),
        .i_dfi_lp_data_req           (dfi_lp_data_req),
        .i_dfi_lp_data_wakeup        (dfi_lp_data_wakeup),

        .i_dfi_address_p0            (dfi_address_p0         ),
        .i_dfi_cke_p0                (dfi_cke_p0             ),
        .i_dfi_cs_p0                 (dfi_cs_p0              ),
        .i_dfi_dram_clk_disable_p0   (dfi_dram_clk_disable_p0),
        .i_dfi_address_p1            (dfi_address_p1         ),
        .i_dfi_cke_p1                (dfi_cke_p1             ),//fix
        .i_dfi_cs_p1                 (dfi_cs_p1              ),
        .i_dfi_dram_clk_disable_p1   (dfi_dram_clk_disable_p1),
        .i_dfi_address_p2            (dfi_address_p2         ),
        .i_dfi_cke_p2                (dfi_cke_p2             ),//fix
        .i_dfi_cs_p2                 (dfi_cs_p2              ),
        .i_dfi_dram_clk_disable_p2   (dfi_dram_clk_disable_p2),
        .i_dfi_address_p3            (dfi_address_p3         ),
        .i_dfi_cke_p3                (dfi_cke_p3             ),//fix
        .i_dfi_cs_p3                 (dfi_cs_p3              ),
        .i_dfi_dram_clk_disable_p3   (dfi_dram_clk_disable_p3),
        .i_dfi_wrdata_p0             (dfi_wrdata_p0          ),
        .i_dfi_wrdata_mask_p0        (dfi_wrdata_mask_p0     ),
        .i_dfi_wrdata_cs_p0          (dfi_wrdata_cs_n_p0     ),
        .i_dfi_wrdata_en_p0          (dfi_wrdata_en_p0       ),
        .i_dfi_parity_in_p0          (dfi_parity_in_p0       ),
        .i_dfi_wck_cs_p0             (dfi_wck_cs_p0          ),
        .i_dfi_wck_en_p0             (dfi_wck_en_p0          ),
        .i_dfi_wck_toggle_p0         (dfi_wck_toggle_p0      ),
        .i_dfi_rddata_cs_p0          (dfi_rddata_cs_n_p0     ),
        .i_dfi_rddata_en_p0          (dfi_rddata_en_p0       ),
        .i_dfi_wrdata_p1             (dfi_wrdata_p1          ),
        .i_dfi_wrdata_mask_p1        (dfi_wrdata_mask_p1     ),
        .i_dfi_wrdata_cs_p1          (dfi_wrdata_cs_n_p1     ),
        .i_dfi_wrdata_en_p1          (dfi_wrdata_en_p1       ),
        .i_dfi_parity_in_p1          (dfi_parity_in_p1       ),
        .i_dfi_wck_cs_p1             (dfi_wck_cs_p1          ),
        .i_dfi_wck_en_p1             (dfi_wck_en_p1          ),
        .i_dfi_wck_toggle_p1         (dfi_wck_toggle_p1      ),
        .i_dfi_wrdata_p2             (dfi_wrdata_p2          ),
        .i_dfi_wrdata_mask_p2        (dfi_wrdata_mask_p2     ),
        .i_dfi_wrdata_cs_p2          (dfi_wrdata_cs_n_p2     ),
        .i_dfi_wrdata_en_p2          (dfi_wrdata_en_p2       ),
        .i_dfi_parity_in_p2          (dfi_parity_in_p2       ),
        .i_dfi_wck_cs_p2             (dfi_wck_cs_p2          ),
        .i_dfi_wck_en_p2             (dfi_wck_en_p2          ),
        .i_dfi_wck_toggle_p2         (dfi_wck_toggle_p2      ),
        .i_dfi_wrdata_p3             (dfi_wrdata_p3          ),
        .i_dfi_wrdata_mask_p3        (dfi_wrdata_mask_p3     ),
        .i_dfi_wrdata_cs_p3          (dfi_wrdata_cs_n_p3     ),
        .i_dfi_wrdata_en_p3          (dfi_wrdata_en_p3       ),
        .i_dfi_parity_in_p3          (dfi_parity_in_p3       ),
        .i_dfi_wck_cs_p3             (dfi_wck_cs_p3          ),
        .i_dfi_wck_en_p3             (dfi_wck_en_p3          ),
        .i_dfi_wck_toggle_p3         (dfi_wck_toggle_p3      ),
        .i_dfi_rddata_cs_p1          (dfi_rddata_cs_n_p1     ),
        .i_dfi_rddata_en_p1          (dfi_rddata_en_p1       ),
        .i_dfi_rddata_cs_p2          (dfi_rddata_cs_n_p2     ),
        .i_dfi_rddata_en_p2          (dfi_rddata_en_p2       ),
        .i_dfi_rddata_cs_p3          (dfi_rddata_cs_n_p3     ),
        .i_dfi_rddata_en_p3          (dfi_rddata_en_p3       ),
        .o_dfi_rddata_w0             (dfi_rddata_w0          ),
        .o_dfi_rddata_dbi_w0         (dfi_rddata_dbi_w0      ),
        .o_dfi_rddata_valid_w0       (dfi_rddata_valid_w0    ),
        .o_dfi_rddata_w1             (dfi_rddata_w1          ),
        .o_dfi_rddata_dbi_w1         (dfi_rddata_dbi_w1      ),
        .o_dfi_rddata_valid_w1       (dfi_rddata_valid_w1    ),
        .o_dfi_rddata_w2             (dfi_rddata_w2          ),
        .o_dfi_rddata_dbi_w2         (dfi_rddata_dbi_w2      ),
        .o_dfi_rddata_valid_w2       (dfi_rddata_valid_w2    ),
        .o_dfi_rddata_w3             (dfi_rddata_w3          ),
        .o_dfi_rddata_dbi_w3         (dfi_rddata_dbi_w3      ),
        .o_dfi_rddata_valid_w3       (dfi_rddata_valid_w3    ),

    `else

        .o_dfi_ctrlupd_ack           (),
        .i_dfi_ctrlupd_req           ('0),
        .i_dfi_phyupd_ack            ('0),
        .o_dfi_phyupd_req            (),
        .o_dfi_phyupd_type           (),

        .i_dfi_freq_fsp              ('0),
        .i_dfi_freq_ratio            ('0),
        .i_dfi_frequency             ('0),
        .o_dfi_init_complete         (),
        .i_dfi_init_start            ('0),

        .i_dfi_phymstr_ack           ('0),
        .o_dfi_phymstr_cs_state      (),
        .o_dfi_phymstr_req           (),
        .o_dfi_phymstr_state_sel     (),
        .o_dfi_phymstr_type          (),

        .o_dfi_lp_ctrl_ack           (),
        .i_dfi_lp_ctrl_req           ('0),
        .i_dfi_lp_ctrl_wakeup        ('0),
        .o_dfi_lp_data_ack           (),
        .i_dfi_lp_data_req           ('0),
        .i_dfi_lp_data_wakeup        ('0),

        .i_dfi_address_p0            (i_dfi_address_p0         ),
        .i_dfi_cke_p0                (i_dfi_cke_p0             ),
        .i_dfi_cs_p0                 (i_dfi_cs_p0              ),
        .i_dfi_dram_clk_disable_p0   (i_dfi_dram_clk_disable_p0),
        .i_dfi_address_p1            (i_dfi_address_p1         ),
        .i_dfi_cke_p1                (i_dfi_cke_p1             ),
        .i_dfi_cs_p1                 (i_dfi_cs_p1              ),
        .i_dfi_dram_clk_disable_p1   (i_dfi_dram_clk_disable_p1),
        .i_dfi_address_p2            (i_dfi_address_p2         ),
        .i_dfi_cke_p2                (i_dfi_cke_p2             ),
        .i_dfi_cs_p2                 (i_dfi_cs_p2              ),
        .i_dfi_dram_clk_disable_p2   (i_dfi_dram_clk_disable_p2),
        .i_dfi_address_p3            (i_dfi_address_p3         ),
        .i_dfi_cke_p3                (i_dfi_cke_p3             ),
        .i_dfi_cs_p3                 (i_dfi_cs_p3              ),
        .i_dfi_dram_clk_disable_p3   (i_dfi_dram_clk_disable_p3),

        .i_dfi_wrdata_p0             (i_dfi_wrdata_p0          ),
        .i_dfi_wrdata_mask_p0        (i_dfi_wrdata_mask_p0     ),
        .i_dfi_parity_in_p0          (i_dfi_parity_in_p0       ),
        .i_dfi_wrdata_cs_p0          (i_dfi_wrdata_cs_p0       ),
        .i_dfi_wrdata_en_p0          (i_dfi_wrdata_en_p0       ),
        .i_dfi_wck_cs_p0             (i_dfi_wck_cs_p0          ),
        .i_dfi_wck_en_p0             (i_dfi_wck_en_p0          ),
        .i_dfi_wck_toggle_p0         (i_dfi_wck_toggle_p0      ),
        .i_dfi_rddata_cs_p0          (i_dfi_rddata_cs_p0       ),
        .i_dfi_rddata_en_p0          (i_dfi_rddata_en_p0       ),
        .i_dfi_wrdata_p1             (i_dfi_wrdata_p1          ),
        .i_dfi_wrdata_mask_p1        (i_dfi_wrdata_mask_p1     ),
        .i_dfi_parity_in_p1          (i_dfi_parity_in_p1       ),
        .i_dfi_wrdata_cs_p1          (i_dfi_wrdata_cs_p1       ),
        .i_dfi_wrdata_en_p1          (i_dfi_wrdata_en_p1       ),
        .i_dfi_wck_cs_p1             (i_dfi_wck_cs_p1          ),
        .i_dfi_wck_en_p1             (i_dfi_wck_en_p1          ),
        .i_dfi_wck_toggle_p1         (i_dfi_wck_toggle_p1      ),
        .i_dfi_rddata_cs_p1          (i_dfi_rddata_cs_p1       ),
        .i_dfi_rddata_en_p1          (i_dfi_rddata_en_p1       ),
        .i_dfi_wrdata_p2             (i_dfi_wrdata_p2          ),
        .i_dfi_wrdata_mask_p2        (i_dfi_wrdata_mask_p2     ),
        .i_dfi_parity_in_p2          (i_dfi_parity_in_p2       ),
        .i_dfi_wrdata_cs_p2          (i_dfi_wrdata_cs_p2       ),
        .i_dfi_wrdata_en_p2          (i_dfi_wrdata_en_p2       ),
        .i_dfi_wck_cs_p2             (i_dfi_wck_cs_p2          ),
        .i_dfi_wck_en_p2             (i_dfi_wck_en_p2          ),
        .i_dfi_wck_toggle_p2         (i_dfi_wck_toggle_p2      ),
        .i_dfi_rddata_cs_p2          (i_dfi_rddata_cs_p2       ),
        .i_dfi_rddata_en_p2          (i_dfi_rddata_en_p2       ),
        .i_dfi_wrdata_p3             (i_dfi_wrdata_p3          ),
        .i_dfi_wrdata_mask_p3        (i_dfi_wrdata_mask_p3     ),
        .i_dfi_parity_in_p3          (i_dfi_parity_in_p3       ),
        .i_dfi_wrdata_cs_p3          (i_dfi_wrdata_cs_p3       ),
        .i_dfi_wrdata_en_p3          (i_dfi_wrdata_en_p3       ),
        .i_dfi_wck_cs_p3             (i_dfi_wck_cs_p3          ),
        .i_dfi_wck_en_p3             (i_dfi_wck_en_p3          ),
        .i_dfi_wck_toggle_p3         (i_dfi_wck_toggle_p3      ),
        .i_dfi_rddata_cs_p3          (i_dfi_rddata_cs_p3       ),
        .i_dfi_rddata_en_p3          (i_dfi_rddata_en_p3       ),
        .o_dfi_rddata_w0             (o_dfi_rddata_w0          ),
        .o_dfi_rddata_dbi_w0         (o_dfi_rddata_dbi_w0      ),
        .o_dfi_rddata_valid_w0       (o_dfi_rddata_valid_w0    ),
        .o_dfi_rddata_w1             (o_dfi_rddata_w1          ),
        .o_dfi_rddata_dbi_w1         (o_dfi_rddata_dbi_w1      ),
        .o_dfi_rddata_valid_w1       (o_dfi_rddata_valid_w1    ),
        .o_dfi_rddata_w2             (o_dfi_rddata_w2          ),
        .o_dfi_rddata_dbi_w2         (o_dfi_rddata_dbi_w2      ),
        .o_dfi_rddata_valid_w2       (o_dfi_rddata_valid_w2    ),
        .o_dfi_rddata_w3             (o_dfi_rddata_w3          ),
        .o_dfi_rddata_dbi_w3         (o_dfi_rddata_dbi_w3      ),
        .o_dfi_rddata_valid_w3       (o_dfi_rddata_valid_w3    ),
    `endif

    .pad_ddr_rext                (),
    .pad_ddr_test                (),

    .pad_ddr_ca_ca0              (pad_ddr_ca_ca0  ), // FIXME
    .pad_ddr_ca_ca1              (pad_ddr_ca_ca1  ), // FIXME
    .pad_ddr_ca_ca2              (pad_ddr_ca_ca2  ), // FIXME
    .pad_ddr_ca_ca3              (pad_ddr_ca_ca3  ), // FIXME
    .pad_ddr_ca_ca4              (pad_ddr_ca_ca4  ), // FIXME
    .pad_ddr_ca_ca5              (pad_ddr_ca_ca5  ), // FIXME
    .pad_ddr_ca_ca6              (pad_ddr_ca_ca6  ), // FIXME
    .pad_ddr_ca_cs0              (pad_ddr_ca_cs0  ), // FIXME
    .pad_ddr_ca_cs1              (pad_ddr_ca_cs1  ), // FIXME
    .pad_ddr_ca_cke0             (pad_ddr_ca_cke0 ), // FIXME
    .pad_ddr_ca_cke1             (pad_ddr_ca_cke1 ), // FIXME
    .pad_ddr_ca_ck_c             (pad_ddr_ca_ck_c ), // FIXME
    .pad_ddr_ca_ck_t             (pad_ddr_ca_ck_t ), // FIXME

    .pad_ddr_dq0_wck_t           (pad_wck_t[0]),
    .pad_ddr_dq1_wck_t           (pad_wck_t[1]),
    .pad_ddr_dq0_wck_c           (pad_wck_c[0]),
    .pad_ddr_dq1_wck_c           (pad_wck_c[1]),
    .pad_ddr_dq0_dqs_t           (pad_dqs_t[0]),
    .pad_ddr_dq1_dqs_t           (pad_dqs_t[1]),
    .pad_ddr_dq0_dqs_c           (pad_dqs_c[0]),
    .pad_ddr_dq1_dqs_c           (pad_dqs_c[1]),
    .pad_ddr_dq0_dq0             (pad_dq[0]),
    .pad_ddr_dq0_dq1             (pad_dq[1]),
    .pad_ddr_dq0_dq2             (pad_dq[2]),
    .pad_ddr_dq0_dq3             (pad_dq[3]),
    .pad_ddr_dq0_dq4             (pad_dq[4]),
    .pad_ddr_dq0_dq5             (pad_dq[5]),
    .pad_ddr_dq0_dq6             (pad_dq[6]),
    .pad_ddr_dq0_dq7             (pad_dq[7]),
    .pad_ddr_dq0_dbim            (pad_dq[8]),
    .pad_ddr_dq1_dq0             (pad_dq[9]),
    .pad_ddr_dq1_dq1             (pad_dq[10]),
    .pad_ddr_dq1_dq2             (pad_dq[11]),
    .pad_ddr_dq1_dq3             (pad_dq[12]),
    .pad_ddr_dq1_dq4             (pad_dq[13]),
    .pad_ddr_dq1_dq5             (pad_dq[14]),
    .pad_ddr_dq1_dq6             (pad_dq[15]),
    .pad_ddr_dq1_dq7             (pad_dq[16]),
    .pad_ddr_dq1_dbim            (pad_dq[17]),

    .o_debug                     ()
);
*/

ddr_phy_1x32 u_phy_1x32 (

    .i_phy_rst                   (i_rst             ),

    .i_dfi_clk_on                ('0                ), // FIXME
    .o_dfi_clk                   (dfi_clk_nodly     ),

    .i_ana_refclk                (i_refclk          ),
    .i_refclk                    (i_refclk          ),
    .i_refclk_alt                (i_refclk_alt      ),
    .o_refclk_on                 (                  ),
    .o_dtst                      (                  ),

    .i_irq                       ('0),
    .o_irq                       (o_irq),

    .i_gpb                       ('0),
    .o_gpb                       (),

    .i_scan_mode                 ('0),
    .i_scan_clk                  ('0),
    .i_scan_freq_en              ('0),
    .i_scan_en                   ('0),
    .i_scan_cgc_ctrl             ('0),
    .i_scan_rst_ctrl             ('0),
    .i_scan_set_ctrl             ('0),
`ifdef GLS
    .i_scan                      ('0),
    .o_scan                      (),
 `endif

    .i_freeze_n                  (i_freeze_n),
    .i_iddq_mode                 ('0),

    .i_hiz_n                     (i_hiz_n),

    .i_jtag_tck                  (i_jtag_tck),
    .i_jtag_trst_n               (i_jtag_trst_n),
    .i_jtag_tms                  (i_jtag_tms),
    .i_jtag_tdi                  (i_jtag_tdi),
    .o_jtag_tdo                  (o_jtag_tdo),

    .i_ahb_clk                   (i_ahb_clk        ),
    .i_ahb_rst                   (i_rst            ),
    .i_ahb_csr_rst               (i_rst            ),
    .o_ahb_clk_on                (                 ),

    .i_ahb_haddr                 (haddr      ),
    .i_ahb_hwrite                (hwrite     ),
    .i_ahb_hsel                  (hsel       ),
    .i_ahb_hwdata                (hwdata     ),
    .i_ahb_htrans                (htrans     ),
    .i_ahb_hsize                 (hsize      ),
    .i_ahb_hburst                (hburst     ),
    .i_ahb_hreadyin              (hready     ),
    .o_ahb_hready                (hreadyout  ),
    .o_ahb_hrdata                (hrdata     ),
    .o_ahb_hresp                 (hresp      ),

    .o_ahb_haddr                 (o_ahb_haddr       ),
    .o_ahb_hwrite                (o_ahb_hwrite      ),
    .o_ahb_hwdata                (o_ahb_hwdata      ),
    .o_ahb_htrans                (o_ahb_htrans      ),
    .o_ahb_hsize                 (o_ahb_hsize       ),
    .o_ahb_hburst                (o_ahb_hburst      ),
    .o_ahb_hbusreq               (o_ahb_hbusreq     ),
    .i_ahb_hgrant                (i_ahb_hgrant      ),
    .i_ahb_hready                (i_ahb_hready      ),
    .i_ahb_hrdata                (i_ahb_hrdata      ),
    .i_ahb_hresp                 (i_ahb_hresp       ),

    `ifdef DFIMC
        .o_dfi_ctrlupd_ack           (dfi_ctrlupd_ack),
        .i_dfi_ctrlupd_req           (dfi_ctrlupd_req_sig),
        .i_dfi_phyupd_ack            (dfi_phyupd_ack_sig),
        .o_dfi_phyupd_req            (dfi_phyupd_req),
        .o_dfi_phyupd_type           (dfi_phyupd_type),

        .i_dfi_freq_fsp              ('0),
        .i_dfi_freq_ratio            (dfi_freq_ratio),
        .i_dfi_frequency             (dfi_frequency),
        .o_dfi_init_complete         (o_dfi_init_complete),
        .i_dfi_init_start            (dfi_init_start_sig),
        //.i_dfi_init_start            (dfi_init_start),

        .i_dfi_phymstr_ack           (dfi_phymstr_ack_sig),
        .o_dfi_phymstr_cs_state      (dfi_phymstr_cs_state),
        .o_dfi_phymstr_req           (dfi_phymstr_req),
        .o_dfi_phymstr_state_sel     (dfi_phymstr_state_sel),
        .o_dfi_phymstr_type          (dfi_phymstr_type),

        .o_dfi_lp_ctrl_ack           (dfi_lp_ctrl_ack),
        .i_dfi_lp_ctrl_req           (dfi_lp_ctrl_req_sig),
        .i_dfi_lp_ctrl_wakeup        (dfi_lp_ctrl_wakeup_sig),
        .o_dfi_lp_data_ack           (dfi_lp_data_ack),
        .i_dfi_lp_data_req           (dfi_lp_data_req_sig),
        .i_dfi_lp_data_wakeup        (dfi_lp_data_wakeup_sig),

        .i_dfi_reset_n_p0            (dfi_reset_sig),// FIXME
        .i_dfi_reset_n_p1            (dfi_reset_sig),// FIXME
        .i_dfi_reset_n_p2            (dfi_reset_sig),// FIXME
        .i_dfi_reset_n_p3            (dfi_reset_sig),// FIXME
        .i_dfi_address_p0            (dfi_address_p0         ),
        .i_dfi_cke_p0                (dfi_cke_p0             ),
        .i_dfi_cs_p0                 (dfi_cs_p0              ),
        .i_dfi_dram_clk_disable_p0   (dfi_dram_clk_disable_p0),
        .i_dfi_address_p1            (dfi_address_p1         ),
        .i_dfi_cke_p1                (dfi_cke_p1             ),//fix
        .i_dfi_cs_p1                 (dfi_cs_p1              ),
        .i_dfi_dram_clk_disable_p1   (dfi_dram_clk_disable_p1),
        .i_dfi_address_p2            (dfi_address_p2         ),
        .i_dfi_cke_p2                (dfi_cke_p2             ),//fix
        .i_dfi_cs_p2                 (dfi_cs_p2              ),
        .i_dfi_dram_clk_disable_p2   (dfi_dram_clk_disable_p2),
        .i_dfi_address_p3            (dfi_address_p3         ),
        .i_dfi_cke_p3                (dfi_cke_p3             ),//fix
        .i_dfi_cs_p3                 (dfi_cs_p3              ),
        .i_dfi_dram_clk_disable_p3   (dfi_dram_clk_disable_p3),

        .i_dfi_wrdata_p0             ({16'b0,dfi_wrdata_p0[31:16],16'b0,dfi_wrdata_p0[15:0]}),
        .i_dfi_wrdata_mask_p0        ({2'b0,dfi_wrdata_mask_p0[3:2],2'b0,dfi_wrdata_mask_p0[1:0]}),
        .i_dfi_wrdata_cs_p0          (dfi_wrdata_cs_n_p0     ),
        .i_dfi_wrdata_en_p0          (dfi_wrdata_en_p0       ),
        .i_dfi_parity_in_p0          (dfi_parity_in_p0       ),
        .i_dfi_wck_cs_p0             (dfi_wck_cs_p0          ),
        .i_dfi_wck_en_p0             (dfi_wck_en_p0          ),
        .i_dfi_wck_toggle_p0         (dfi_wck_toggle_p0      ),
        .i_dfi_rddata_cs_p0          (dfi_rddata_cs_n_p0     ),
        .i_dfi_rddata_en_p0          (dfi_rddata_en_p0       ),
        .i_dfi_wrdata_p1             ({16'b0,dfi_wrdata_p1[31:16],16'b0,dfi_wrdata_p1[15:0]}),
        .i_dfi_wrdata_mask_p1        ({2'b0,dfi_wrdata_mask_p1[3:2],2'b0,dfi_wrdata_mask_p1[1:0]}),
        .i_dfi_wrdata_cs_p1          (dfi_wrdata_cs_n_p1     ),
        .i_dfi_wrdata_en_p1          (dfi_wrdata_en_p1       ),
        .i_dfi_parity_in_p1          (dfi_parity_in_p1       ),
        .i_dfi_wck_cs_p1             (dfi_wck_cs_p1          ),
        .i_dfi_wck_en_p1             (dfi_wck_en_p1          ),
        .i_dfi_wck_toggle_p1         (dfi_wck_toggle_p1      ),
        .i_dfi_wrdata_p2             ({16'b0,dfi_wrdata_p2[31:16],16'b0,dfi_wrdata_p2[15:0]}),
        .i_dfi_wrdata_mask_p2        ({2'b0,dfi_wrdata_mask_p2[3:2],2'b0,dfi_wrdata_mask_p2[1:0]}),
        .i_dfi_wrdata_cs_p2          (dfi_wrdata_cs_n_p2     ),
        .i_dfi_wrdata_en_p2          (dfi_wrdata_en_p2       ),
        .i_dfi_parity_in_p2          (dfi_parity_in_p2       ),
        .i_dfi_wck_cs_p2             (dfi_wck_cs_p2          ),
        .i_dfi_wck_en_p2             (dfi_wck_en_p2          ),
        .i_dfi_wck_toggle_p2         (dfi_wck_toggle_p2      ),
        .i_dfi_wrdata_p3             ({16'b0,dfi_wrdata_p3[31:16],16'b0,dfi_wrdata_p3[15:0]}),
        .i_dfi_wrdata_mask_p3        ({2'b0,dfi_wrdata_mask_p3[3:2],2'b0,dfi_wrdata_mask_p3[1:0]}),
        .i_dfi_wrdata_cs_p3          (dfi_wrdata_cs_n_p3     ),
        .i_dfi_wrdata_en_p3          (dfi_wrdata_en_p3       ),
        .i_dfi_parity_in_p3          (dfi_parity_in_p3       ),
        .i_dfi_wck_cs_p3             (dfi_wck_cs_p3          ),
        .i_dfi_wck_en_p3             (dfi_wck_en_p3          ),
        .i_dfi_wck_toggle_p3         (dfi_wck_toggle_p3      ),
        .i_dfi_rddata_cs_p1          (dfi_rddata_cs_n_p1     ),
        .i_dfi_rddata_en_p1          (dfi_rddata_en_p1       ),
        .i_dfi_rddata_cs_p2          (dfi_rddata_cs_n_p2     ),
        .i_dfi_rddata_en_p2          (dfi_rddata_en_p2       ),
        .i_dfi_rddata_cs_p3          (dfi_rddata_cs_n_p3     ),
        .i_dfi_rddata_en_p3          (dfi_rddata_en_p3       ),
        .o_dfi_rddata_w0             ({dfi_rddata_w0_dq2_dq3[31:16],dfi_rddata_w0[31:16],dfi_rddata_w0_dq2_dq3[15:0],dfi_rddata_w0[15:0]}),
        .o_dfi_rddata_dbi_w0         ({dfi_rddata_dbi_w0_dq2_dq3[31:16],dfi_rddata_dbi_w0[31:16],dfi_rddata_dbi_w0_dq2_dq3[15:0],dfi_rddata_dbi_w0[15:0]}),
        .o_dfi_rddata_valid_w0       (dfi_rddata_valid_w0    ),
        .o_dfi_rddata_w1             ({dfi_rddata_w1_dq2_dq3[31:16],dfi_rddata_w1[31:16],dfi_rddata_w1_dq2_dq3[15:0],dfi_rddata_w1[15:0]}),
        .o_dfi_rddata_dbi_w1         ({dfi_rddata_dbi_w1_dq2_dq3[31:16],dfi_rddata_dbi_w1[31:16],dfi_rddata_dbi_w1_dq2_dq3[15:0],dfi_rddata_dbi_w1[15:0]}),
        .o_dfi_rddata_valid_w1       (dfi_rddata_valid_w1    ),
        .o_dfi_rddata_w2             ({dfi_rddata_w2_dq2_dq3[31:16],dfi_rddata_w2[31:16],dfi_rddata_w2_dq2_dq3[15:0],dfi_rddata_w2[15:0]}),
        .o_dfi_rddata_dbi_w2         ({dfi_rddata_dbi_w2_dq2_dq3[31:16],dfi_rddata_dbi_w2[31:16],dfi_rddata_dbi_w2_dq2_dq3[15:0],dfi_rddata_dbi_w2[15:0]}),
        .o_dfi_rddata_valid_w2       (dfi_rddata_valid_w2    ),
        .o_dfi_rddata_w3             ({dfi_rddata_w3_dq2_dq3[31:16],dfi_rddata_w3[31:16],dfi_rddata_w3_dq2_dq3[15:0],dfi_rddata_w3[15:0]}),
        .o_dfi_rddata_dbi_w3         ({dfi_rddata_dbi_w3_dq2_dq3[31:16],dfi_rddata_dbi_w3[31:16],dfi_rddata_dbi_w3_dq2_dq3[15:0],dfi_rddata_dbi_w3[15:0]}),
        .o_dfi_rddata_valid_w3       (dfi_rddata_valid_w3    ),

    `else

        .o_dfi_ctrlupd_ack           (),
        .i_dfi_ctrlupd_req           ('0),
        .i_dfi_phyupd_ack            ('0),
        .o_dfi_phyupd_req            (),
        .o_dfi_phyupd_type           (),

        .i_dfi_freq_fsp              ('0),
        .i_dfi_freq_ratio            ('0),
        .i_dfi_frequency             ('0),
        .o_dfi_init_complete         (),
        .i_dfi_init_start            ('0),

        .i_dfi_phymstr_ack           ('0),
        .o_dfi_phymstr_cs_state      (),
        .o_dfi_phymstr_req           (),
        .o_dfi_phymstr_state_sel     (),
        .o_dfi_phymstr_type          (),

        .o_dfi_lp_ctrl_ack           (),
        .i_dfi_lp_ctrl_req           ('0),
        .i_dfi_lp_ctrl_wakeup        ('0),
        .o_dfi_lp_data_ack           (),
        .i_dfi_lp_data_req           ('0),
        .i_dfi_lp_data_wakeup        ('0),

        .i_dfi_reset_n_p0            (dfi_reset_sig),// FIXME
        .i_dfi_reset_n_p1            (dfi_reset_sig),// FIXME
        .i_dfi_reset_n_p2            (dfi_reset_sig),// FIXME
        .i_dfi_reset_n_p3            (dfi_reset_sig),// FIXME
        .i_dfi_address_p0            (i_dfi_address_p0         ),
        .i_dfi_cke_p0                (i_dfi_cke_p0             ),
        .i_dfi_cs_p0                 (i_dfi_cs_p0              ),
        .i_dfi_dram_clk_disable_p0   (i_dfi_dram_clk_disable_p0),
        .i_dfi_address_p1            (i_dfi_address_p1         ),
        .i_dfi_cke_p1                (i_dfi_cke_p1             ),
        .i_dfi_cs_p1                 (i_dfi_cs_p1              ),
        .i_dfi_dram_clk_disable_p1   (i_dfi_dram_clk_disable_p1),
        .i_dfi_address_p2            (i_dfi_address_p2         ),
        .i_dfi_cke_p2                (i_dfi_cke_p2             ),
        .i_dfi_cs_p2                 (i_dfi_cs_p2              ),
        .i_dfi_dram_clk_disable_p2   (i_dfi_dram_clk_disable_p2),
        .i_dfi_address_p3            (i_dfi_address_p3         ),
        .i_dfi_cke_p3                (i_dfi_cke_p3             ),
        .i_dfi_cs_p3                 (i_dfi_cs_p3              ),
        .i_dfi_dram_clk_disable_p3   (i_dfi_dram_clk_disable_p3),

        .i_dfi_wrdata_p0             (i_dfi_wrdata_p0          ),
        .i_dfi_wrdata_mask_p0        (i_dfi_wrdata_mask_p0     ),
        .i_dfi_parity_in_p0          (i_dfi_parity_in_p0       ),
        .i_dfi_wrdata_cs_p0          (i_dfi_wrdata_cs_p0       ),
        .i_dfi_wrdata_en_p0          (i_dfi_wrdata_en_p0       ),
        .i_dfi_wck_cs_p0             (i_dfi_wck_cs_p0          ),
        .i_dfi_wck_en_p0             (i_dfi_wck_en_p0          ),
        .i_dfi_wck_toggle_p0         (i_dfi_wck_toggle_p0      ),
        .i_dfi_rddata_cs_p0          (i_dfi_rddata_cs_p0       ),
        .i_dfi_rddata_en_p0          (i_dfi_rddata_en_p0       ),
        .i_dfi_wrdata_p1             (i_dfi_wrdata_p1          ),
        .i_dfi_wrdata_mask_p1        (i_dfi_wrdata_mask_p1     ),
        .i_dfi_parity_in_p1          (i_dfi_parity_in_p1       ),
        .i_dfi_wrdata_cs_p1          (i_dfi_wrdata_cs_p1       ),
        .i_dfi_wrdata_en_p1          (i_dfi_wrdata_en_p1       ),
        .i_dfi_wck_cs_p1             (i_dfi_wck_cs_p1          ),
        .i_dfi_wck_en_p1             (i_dfi_wck_en_p1          ),
        .i_dfi_wck_toggle_p1         (i_dfi_wck_toggle_p1      ),
        .i_dfi_rddata_cs_p1          (i_dfi_rddata_cs_p1       ),
        .i_dfi_rddata_en_p1          (i_dfi_rddata_en_p1       ),
        .i_dfi_wrdata_p2             (i_dfi_wrdata_p2          ),
        .i_dfi_wrdata_mask_p2        (i_dfi_wrdata_mask_p2     ),
        .i_dfi_parity_in_p2          (i_dfi_parity_in_p2       ),
        .i_dfi_wrdata_cs_p2          (i_dfi_wrdata_cs_p2       ),
        .i_dfi_wrdata_en_p2          (i_dfi_wrdata_en_p2       ),
        .i_dfi_wck_cs_p2             (i_dfi_wck_cs_p2          ),
        .i_dfi_wck_en_p2             (i_dfi_wck_en_p2          ),
        .i_dfi_wck_toggle_p2         (i_dfi_wck_toggle_p2      ),
        .i_dfi_rddata_cs_p2          (i_dfi_rddata_cs_p2       ),
        .i_dfi_rddata_en_p2          (i_dfi_rddata_en_p2       ),
        .i_dfi_wrdata_p3             (i_dfi_wrdata_p3          ),
        .i_dfi_wrdata_mask_p3        (i_dfi_wrdata_mask_p3     ),
        .i_dfi_parity_in_p3          (i_dfi_parity_in_p3       ),
        .i_dfi_wrdata_cs_p3          (i_dfi_wrdata_cs_p3       ),
        .i_dfi_wrdata_en_p3          (i_dfi_wrdata_en_p3       ),
        .i_dfi_wck_cs_p3             (i_dfi_wck_cs_p3          ),
        .i_dfi_wck_en_p3             (i_dfi_wck_en_p3          ),
        .i_dfi_wck_toggle_p3         (i_dfi_wck_toggle_p3      ),
        .i_dfi_rddata_cs_p3          (i_dfi_rddata_cs_p3       ),
        .i_dfi_rddata_en_p3          (i_dfi_rddata_en_p3       ),
        .o_dfi_rddata_w0             (o_dfi_rddata_w0          ),
        .o_dfi_rddata_dbi_w0         (o_dfi_rddata_dbi_w0      ),
        .o_dfi_rddata_valid_w0       (o_dfi_rddata_valid_w0    ),
        .o_dfi_rddata_w1             (o_dfi_rddata_w1          ),
        .o_dfi_rddata_dbi_w1         (o_dfi_rddata_dbi_w1      ),
        .o_dfi_rddata_valid_w1       (o_dfi_rddata_valid_w1    ),
        .o_dfi_rddata_w2             (o_dfi_rddata_w2          ),
        .o_dfi_rddata_dbi_w2         (o_dfi_rddata_dbi_w2      ),
        .o_dfi_rddata_valid_w2       (o_dfi_rddata_valid_w2    ),
        .o_dfi_rddata_w3             (o_dfi_rddata_w3          ),
        .o_dfi_rddata_dbi_w3         (o_dfi_rddata_dbi_w3      ),
        .o_dfi_rddata_valid_w3       (o_dfi_rddata_valid_w3    ),
    `endif

    .pad_ddr_reset_n             (pad_ddr_reset),
    .pad_ddr_rext                (),
    .pad_ddr_test                (),

    .pad_ch0_ddr_ca_ca0              (pad_ddr_ca_ca0  ), // FIXME
    .pad_ch0_ddr_ca_ca1              (pad_ddr_ca_ca1  ), // FIXME
    .pad_ch0_ddr_ca_ca2              (pad_ddr_ca_ca2  ), // FIXME
    .pad_ch0_ddr_ca_ca3              (pad_ddr_ca_ca3  ), // FIXME
    .pad_ch0_ddr_ca_ca4              (pad_ddr_ca_ca4  ), // FIXME
    .pad_ch0_ddr_ca_ca5              (pad_ddr_ca_ca5  ), // FIXME
    .pad_ch0_ddr_ca_ca6              (pad_ddr_ca_ca6  ), // FIXME
    .pad_ch0_ddr_ca_cs0              (pad_ddr_ca_cs0  ), // FIXME
    .pad_ch0_ddr_ca_cs1              (pad_ddr_ca_cs1  ), // FIXME
    .pad_ch0_ddr_ca_cke0             (pad_ddr_ca_cke0 ), // FIXME
    .pad_ch0_ddr_ca_cke1             (pad_ddr_ca_cke1 ), // FIXME
    .pad_ch0_ddr_ca_ck_c             (pad_ddr_ca_ck_c ), // FIXME
    .pad_ch0_ddr_ca_ck_t             (pad_ddr_ca_ck_t ), // FIXME

    .pad_ch0_ddr_dq0_wck_t           (pad_wck_t[0]),
    .pad_ch0_ddr_dq1_wck_t           (pad_wck_t[1]),
    .pad_ch0_ddr_dq0_wck_c           (pad_wck_c[0]),
    .pad_ch0_ddr_dq1_wck_c           (pad_wck_c[1]),
    .pad_ch0_ddr_dq0_dqs_t           (pad_dqs_t[0]),
    .pad_ch0_ddr_dq1_dqs_t           (pad_dqs_t[1]),
    .pad_ch0_ddr_dq0_dqs_c           (pad_dqs_c[0]),
    .pad_ch0_ddr_dq1_dqs_c           (pad_dqs_c[1]),
    .pad_ch0_ddr_dq0_dq0             (pad_dq[0]),
    .pad_ch0_ddr_dq0_dq1             (pad_dq[1]),
    .pad_ch0_ddr_dq0_dq2             (pad_dq[2]),
    .pad_ch0_ddr_dq0_dq3             (pad_dq[3]),
    .pad_ch0_ddr_dq0_dq4             (pad_dq[4]),
    .pad_ch0_ddr_dq0_dq5             (pad_dq[5]),
    .pad_ch0_ddr_dq0_dq6             (pad_dq[6]),
    .pad_ch0_ddr_dq0_dq7             (pad_dq[7]),
    .pad_ch0_ddr_dq0_dbim            (pad_dq[8]),
    .pad_ch0_ddr_dq1_dq0             (pad_dq[9]),
    .pad_ch0_ddr_dq1_dq1             (pad_dq[10]),
    .pad_ch0_ddr_dq1_dq2             (pad_dq[11]),
    .pad_ch0_ddr_dq1_dq3             (pad_dq[12]),
    .pad_ch0_ddr_dq1_dq4             (pad_dq[13]),
    .pad_ch0_ddr_dq1_dq5             (pad_dq[14]),
    .pad_ch0_ddr_dq1_dq6             (pad_dq[15]),
    .pad_ch0_ddr_dq1_dq7             (pad_dq[16]),
    .pad_ch0_ddr_dq1_dbim            (pad_dq[17]),

    .pad_ch1_ddr_ca_ca0              (/*OPEN*/),
    .pad_ch1_ddr_ca_ca1              (/*OPEN*/),
    .pad_ch1_ddr_ca_ca2              (/*OPEN*/),
    .pad_ch1_ddr_ca_ca3              (/*OPEN*/),
    .pad_ch1_ddr_ca_ca4              (/*OPEN*/),
    .pad_ch1_ddr_ca_ca5              (/*OPEN*/),
    .pad_ch1_ddr_ca_ca6              (/*OPEN*/),
    .pad_ch1_ddr_ca_cs0              (/*OPEN*/),
    .pad_ch1_ddr_ca_cs1              (/*OPEN*/),
    .pad_ch1_ddr_ca_cke0             (/*OPEN*/),
    .pad_ch1_ddr_ca_cke1             (/*OPEN*/),
    .pad_ch1_ddr_ca_ck_c             (/*OPEN*/),
    .pad_ch1_ddr_ca_ck_t             (/*OPEN*/),

    .pad_ch1_ddr_dq0_wck_t           (/*OPEN*/),
    .pad_ch1_ddr_dq1_wck_t           (/*OPEN*/),
    .pad_ch1_ddr_dq0_wck_c           (/*OPEN*/),
    .pad_ch1_ddr_dq1_wck_c           (/*OPEN*/),
    .pad_ch1_ddr_dq0_dqs_t           (/*OPEN*/),
    .pad_ch1_ddr_dq1_dqs_t           (/*OPEN*/),
    .pad_ch1_ddr_dq0_dqs_c           (/*OPEN*/),
    .pad_ch1_ddr_dq1_dqs_c           (/*OPEN*/),
    .pad_ch1_ddr_dq0_dq0             (/*OPEN*/),
    .pad_ch1_ddr_dq0_dq1             (/*OPEN*/),
    .pad_ch1_ddr_dq0_dq2             (/*OPEN*/),
    .pad_ch1_ddr_dq0_dq3             (/*OPEN*/),
    .pad_ch1_ddr_dq0_dq4             (/*OPEN*/),
    .pad_ch1_ddr_dq0_dq5             (/*OPEN*/),
    .pad_ch1_ddr_dq0_dq6             (/*OPEN*/),
    .pad_ch1_ddr_dq0_dq7             (/*OPEN*/),
    .pad_ch1_ddr_dq0_dbim            (/*OPEN*/),
    .pad_ch1_ddr_dq1_dq0             (/*OPEN*/),
    .pad_ch1_ddr_dq1_dq1             (/*OPEN*/),
    .pad_ch1_ddr_dq1_dq2             (/*OPEN*/),
    .pad_ch1_ddr_dq1_dq3             (/*OPEN*/),
    .pad_ch1_ddr_dq1_dq4             (/*OPEN*/),
    .pad_ch1_ddr_dq1_dq5             (/*OPEN*/),
    .pad_ch1_ddr_dq1_dq6             (/*OPEN*/),
    .pad_ch1_ddr_dq1_dq7             (/*OPEN*/),
    .pad_ch1_ddr_dq1_dbim            (/*OPEN*/),

    .o_debug                     ()
);

//------------------------------------------------------
// LPDDR4
//------------------------------------------------------

`ifdef LPDDR4

    integer rc;

    lp4_debug_interface lp4_debug_ChA(.clk(o_dfi_clk),.clk1(o_dfi_clk));
    lp4_debug_interface lp4_debug_ChB(.clk(o_dfi_clk),.clk1(o_dfi_clk));

    // ****************************************************************
    // Instantiate the LPDDR4 slave memory device model.
    // ****************************************************************

    jedec_lpddr4_16gb_2133 lp4 (
        .CA_A ({pad_ddr_ca_ca5,pad_ddr_ca_ca4,pad_ddr_ca_ca3,pad_ddr_ca_ca2,pad_ddr_ca_ca1,pad_ddr_ca_ca0}),
        .CA_B ({pad_ddr_ca_ca5,pad_ddr_ca_ca4,pad_ddr_ca_ca3,pad_ddr_ca_ca2,pad_ddr_ca_ca1,pad_ddr_ca_ca0}),
        .CKE_A(pad_ddr_ca_cke0),
        .CKE_B(pad_ddr_ca_cke1),
        .CK_C_A(pad_ddr_ca_ck_c),
        .CK_C_B(pad_ddr_ca_ck_c),
        .CK_T_A(pad_ddr_ca_ck_t),
        .CK_T_B(pad_ddr_ca_ck_t),
        .CS_A(pad_ddr_ca_cs0),
        .CS_B(pad_ddr_ca_cs1),
        .DMI_A({pad_dq[17],pad_dq[8]}),
        .DMI_B({pad_dq[17],pad_dq[8]}),
        .ODT_CA_A(1'b0),
        .ODT_CA_B(1'b0),
        .DQS_C_A(pad_dqs_c[1:0]),
        .DQS_C_B(pad_dqs_c[1:0]),
        .DQS_T_A(pad_dqs_t[1:0]),
        .DQS_T_B(pad_dqs_t[1:0]),
        .DQ_A({pad_dq[16:9],pad_dq[7:0]}),
        .DQ_B({pad_dq[16:9],pad_dq[7:0]}),
    .RESET_N(pad_ddr_reset));

    defparam lp4.memory_spec = "${verif}/sv/agents/lpddr4/jedec_lpddr4_16gb_4266.spc";

    initial
    begin
        uvm_config_db#(virtual interface lp4_debug_interface)::set(null,"*", "debug_interface_chA", lp4_debug_ChA);
        uvm_config_db#(virtual interface lp4_debug_interface)::set(null,"*", "debug_interface_chB", lp4_debug_ChB);
        rc = $mmsomaset("wddr_tb_top.lp4", "tinit1", "60", "ns");
        rc = $mmsomaset("wddr_tb_top.lp4", "tinit3", "4", "ns");
        rc = $mmsomaset("wddr_tb_top.lp4", "tinit5", "50", "ns");
        ddr_reset = 0;
        repeat (15) @(negedge pad_ddr_ca_ck_c);
        ddr_reset = 1;

        #500ns;
        rc = $mmsomaset("wddr_tb_top.lp4", "tvreflong", "10", "ns");
        rc = $mmsomaset("wddr_tb_top.lp4", "tzqcal", "10", "ns");
        rc = $mmsomaset("wddr_tb_top.lp4", "tzqlat", "10", "ns");

        #1us;
    end

`endif

//------------------------------------------------------
// MM
//------------------------------------------------------

`ifdef MM
    wav_mm lp4 (
        .CA_A ({pad_ddr_ca_ca5,pad_ddr_ca_ca4,pad_ddr_ca_ca3,pad_ddr_ca_ca2,pad_ddr_ca_ca1,pad_ddr_ca_ca0}),
        .CA_B ({pad_ddr_ca_ca5,pad_ddr_ca_ca4,pad_ddr_ca_ca3,pad_ddr_ca_ca2,pad_ddr_ca_ca1,pad_ddr_ca_ca0}),
        .CKE_A(pad_ddr_ca_cke0),
        .CKE_B(pad_ddr_ca_cke1),
        .CK_C_A(pad_ddr_ca_ck_c),
        .CK_C_B(pad_ddr_ca_ck_c),
        .CK_T_A(pad_ddr_ca_ck_t),
        .CK_T_B(pad_ddr_ca_ck_t),
        .CS_A(pad_ddr_ca_cs0),
        .CS_B(pad_ddr_ca_cs1),
        .DMI_A({pad_dq[17],pad_dq[8]}),
        .DMI_B({pad_dq[17],pad_dq[8]}),
        .ODT_CA_A(1'b0),
        .ODT_CA_B(1'b0),
        .DQS_C_A(pad_dqs_c[1:0]),
        .DQS_C_B(pad_dqs_c[1:0]),
        .DQS_T_A(pad_dqs_t[1:0]),
        .DQS_T_B(pad_dqs_t[1:0]),
        .DQ_A({pad_dq[16:9],pad_dq[7:0]}),
        .DQ_B({pad_dq[16:9],pad_dq[7:0]}),
        .RESET_N(pad_ddr_reset)
    );

    initial
    begin
        ddr_reset = 0;
        repeat (15) @(negedge pad_ddr_ca_ck_c);
        ddr_reset = 1;
    end

`endif

//------------------------------------------------------
// DFIMC
//------------------------------------------------------

`ifdef DFIMC

    passiveDfi #("${verif}/sv/agents/dfimc/soma_uvm/passiveDfi.soma") passiveDfiInst( o_dfi_clk,dfi_reset,dfi_lvl_pattern,dfi_lvl_periodic,dfi_address_p0,dfi_address_p1,
        dfi_address_p2,dfi_address_p3,dfi_cke_p0,dfi_cke_p1,dfi_cke_p2,dfi_cke_p3,dfi_cs_p0,dfi_cs_p1,dfi_cs_p2,dfi_cs_p3,dfi_reset_n_p0,dfi_reset_n_p1,dfi_reset_n_p2,
        dfi_reset_n_p3,dfi_wrdata_en_p0,dfi_wrdata_en_p1,dfi_wrdata_en_p2,dfi_wrdata_en_p3,dfi_wrdata_p0,dfi_wrdata_p1,dfi_wrdata_p2,dfi_wrdata_p3,dfi_wrdata_mask_p0,
        dfi_wrdata_mask_p1,dfi_wrdata_mask_p2,dfi_wrdata_mask_p3,dfi_wrdata_cs_n_p0,dfi_wrdata_cs_n_p1,dfi_wrdata_cs_n_p2,dfi_wrdata_cs_n_p3,dfi_rddata_en_p0,dfi_rddata_en_p1,
        dfi_rddata_en_p2,dfi_rddata_en_p3,dfi_rddata_w0,dfi_rddata_w1,dfi_rddata_w2,dfi_rddata_w3,dfi_rddata_valid_w0,dfi_rddata_valid_w1,dfi_rddata_valid_w2,dfi_rddata_valid_w3,
        dfi_rddata_cs_n_p0,dfi_rddata_cs_n_p1,dfi_rddata_cs_n_p2,dfi_rddata_cs_n_p3,dfi_ctrlupd_ack,dfi_ctrlupd_req,dfi_phyupd_ack,dfi_phyupd_req,dfi_phyupd_type,dfi_freq_ratio,
        dfi_parity_in_p0,dfi_parity_in_p1,dfi_parity_in_p2,dfi_parity_in_p3,1'd0,dfi_dram_clk_disable,dfi_init_start,o_dfi_init_complete,dfi_error,dfi_error_info,dfi_rdlvl_en,
        dfi_rdlvl_gate_en,dfi_rdlvl_req,dfi_rdlvl_gate_req,dfi_rdlvl_resp,dfi_phy_rdlvl_cs_n,dfi_phy_rdlvl_gate_cs_n,8'd0,dfi_rdlvl_done,dfi_wrlvl_en,dfi_wrlvl_req,dfi_wrlvl_resp,
        dfi_phy_wrlvl_cs_n,dfi_wrlvl_strobe_p0,dfi_wrlvl_strobe_p1,dfi_wrlvl_strobe_p2,dfi_wrlvl_strobe_p3,dfi_calvl_req,dfi_calvl_ca_sel_p0,dfi_calvl_ca_sel_p1,dfi_calvl_ca_sel_p2,
        dfi_calvl_ca_sel_p3,dfi_calvl_capture,dfi_phy_calvl_cs_n,dfi_calvl_en,dfi_calvl_resp,dfi_calvl_strobe_p0,dfi_calvl_strobe_p1,dfi_calvl_strobe_p2,dfi_calvl_strobe_p3,
        dfi_calvl_data_p0,dfi_calvl_data_p1,dfi_calvl_data_p2,dfi_calvl_data_p3,dfi_calvl_result,dfi_calvl_done,dfi_phy_wdqlvl_cs,dfi_wdqlvl_en,dfi_wdqlvl_req,dfi_wdqlvl_resp,
        dfi_wdqlvl_result,dfi_wdqlvl_done,dfi_phymstr_ack,dfi_phymstr_req,dfi_phymstr_type,dfi_phymstr_cs_state,dfi_phymstr_state_sel,dfi_frequency,dfi_disconnect_error,
        dfi_lp_ctrl_req,dfi_lp_data_req,dfi_lp_wakeup,dfi_lp_ctrl_wakeup,dfi_lp_data_wakeup,dfi_lp_ack,dfi_lp_ctrl_ack,dfi_lp_data_ack,dfi_freq_fsp,dfi_ctrlmsg_req,
    dfi_ctrlmsg_ack,dfi_ctrlmsg,dfi_ctrlmsg_data);

    activeDfiMC #("${verif}/sv/agents/dfimc/soma_uvm/activeDfiMC.soma") activeDfiMCInst( o_dfi_clk,dfi_reset,freq_change_done,dfi_address_p0,dfi_address_p1,
        dfi_address_p2,dfi_address_p3,dfi_cke_p0,dfi_cke_p1,dfi_cke_p2,dfi_cke_p3,dfi_cs_p0,dfi_cs_p1,dfi_cs_p2,dfi_cs_p3,dfi_dram_clk_disable,dfi_parity_in_p0,
        dfi_parity_in_p1,dfi_parity_in_p2,dfi_parity_in_p3,dfi_reset_n_p0,dfi_reset_n_p1,dfi_reset_n_p2,dfi_reset_n_p3,dfi_wrdata_p0,dfi_wrdata_p1,dfi_wrdata_p2,
        dfi_wrdata_p3,dfi_wrdata_cs_n_p0,dfi_wrdata_cs_n_p1,dfi_wrdata_cs_n_p2,dfi_wrdata_cs_n_p3,dfi_wrdata_en_p0,dfi_wrdata_en_p1,dfi_wrdata_en_p2,dfi_wrdata_en_p3,
        dfi_wrdata_mask_p0,dfi_wrdata_mask_p1,dfi_wrdata_mask_p2,dfi_wrdata_mask_p3,dfi_rddata_w0,dfi_rddata_w1,dfi_rddata_w2,dfi_rddata_w3,dfi_rddata_cs_n_p0,
        dfi_rddata_cs_n_p1,dfi_rddata_cs_n_p2,dfi_rddata_cs_n_p3,dfi_rddata_dbi_w0,dfi_rddata_dbi_w1,dfi_rddata_dbi_w2,dfi_rddata_dbi_w3,dfi_rddata_dnv_w0,dfi_rddata_dnv_w1,
        dfi_rddata_dnv_w2,dfi_rddata_dnv_w3,dfi_rddata_en_p0,dfi_rddata_en_p1,dfi_rddata_en_p2,dfi_rddata_en_p3,dfi_rddata_valid_w0,dfi_rddata_valid_w1,dfi_rddata_valid_w2,
        dfi_rddata_valid_w3,dfi_ctrlupd_req,dfi_ctrlupd_ack,dfi_phyupd_req,dfi_phyupd_type,dfi_phyupd_ack,dfi_data_byte_disable,o_dfi_init_complete,dfi_init_start,
        dfi_freq_ratio,dfi_frequency,dfi_lp_ctrl_req,dfi_lp_data_req,dfi_lp_wakeup,dfi_lp_ctrl_wakeup,dfi_lp_data_wakeup,dfi_lp_ack, dfi_lp_ctrl_ack,dfi_lp_data_ack,
        dfi_error,dfi_error_info,dfi_phymstr_cs_state,dfi_phymstr_req,dfi_phymstr_state_sel,dfi_phymstr_type,dfi_phymstr_ack,dfi_disconnect_error,dfi_rdlvl_req,dfi_phy_rdlvl_cs_n,
        dfi_rdlvl_en,dfi_rdlvl_resp,dfi_rdlvl_gate_req,dfi_phy_rdlvl_gate_cs_n,dfi_rdlvl_gate_en,dfi_wrlvl_req,dfi_phy_wrlvl_cs_n,dfi_wrlvl_en,dfi_wrlvl_resp,dfi_calvl_req,
        dfi_phy_calvl_cs_n,dfi_calvl_en,dfi_calvl_capture,dfi_calvl_resp,dfi_lvl_pattern,dfi_lvl_periodic,dfi_phylvl_req_cs_n,dfi_phylvl_ack_cs_n,dfi_db_train_resp_p2,
        dfi_db_train_resp_p3,dfi_calvl_ca_sel_p0,dfi_calvl_ca_sel_p1,dfi_calvl_ca_sel_p2,dfi_calvl_ca_sel_p3,dfi_calvl_strobe_p0,dfi_calvl_strobe_p1,dfi_calvl_strobe_p2,
        dfi_calvl_strobe_p3,dfi_calvl_data_p0,dfi_calvl_data_p1,dfi_calvl_data_p2,dfi_calvl_data_p3,dfi_calvl_done,dfi_calvl_result,dfi_rdlvl_done,dfi_wrlvl_strobe_p0,
        dfi_wrlvl_strobe_p1,dfi_wrlvl_strobe_p2,dfi_wrlvl_strobe_p3,dfi_phy_wdqlvl_cs,dfi_wdqlvl_en,dfi_wdqlvl_req,dfi_wdqlvl_resp,dfi_wdqlvl_result,dfi_wdqlvl_done,dfi_freq_fsp,
    dfi_ctrlmsg_req, dfi_ctrlmsg_ack,dfi_ctrlmsg,dfi_ctrlmsg_data,dfi_dram_clk_disable_p0,dfi_dram_clk_disable_p1,dfi_dram_clk_disable_p2,dfi_dram_clk_disable_p3);

    logic flag  = 1'b0 ;
    initial
    begin
        freq_change_done = 0;
        dfi_reset = 0;
        repeat (15) @(negedge o_dfi_clk);
        dfi_reset = 1;

    end

    // Frequency change logic
    always@ (posedge o_dfi_clk)
    begin

        if(freq_change_done == 0) begin
            if(o_dfi_init_complete == 0 && dfi_init_start == 1 && initialized == 1)
            begin
                clockdelay = dfi_frequency/2;
                freqChangeAccepted  = 1;
            end
            else if(o_dfi_init_complete && initialized == 0)
            begin
                initialized = 1;
            end
        end
        if(freqChangeAccepted == 1) begin
            if (count == changedelay) begin
                freq_change_done = 1;
            end
            count++;
        end
        if(freq_change_done == 1 && dfi_init_start == 0 && o_dfi_init_complete ==1)
        begin
            freqChangeAccepted  = 0;
            freq_change_done = 0;
            count = 0;
        end
    end

    always @ ( posedge o_dfi_init_complete )
    begin
        flag = 1'b1;
    end

    logic flag0;
    always @ ( posedge dfi_init_start )
    begin
        flag0 = 1'b1;
    end

    always @ (posedge dfi_init_start or negedge dfi_init_start or posedge flag)
    begin
        if (flag == 1'b1 && (dfi_init_start !== 1'bx) && (flag0 == 1'b1)) begin
            dfi_init_start_sig = dfi_init_start ;
        end
    end
    always @ (posedge ddr_reset or negedge ddr_reset or posedge flag)
    begin
        if (flag == 1'b1 ) begin
            dfi_reset_sig      = ddr_reset ;
        end
    end

    logic flag1  = 1'b0 ;
    logic flag2  = 1'b0 ;
    always @ (posedge o_dfi_clk)
    begin
        flag1 <= 1'b1;
        flag2 <= flag1;
    end
    always @ (*) begin
       dfi_ctrlupd_req_sig    = (flag2 == 1'b1) ? dfi_ctrlupd_req    : dfi_ctrlupd_req_sig    ;
       dfi_phyupd_ack_sig     = (flag2 == 1'b1) ? dfi_phyupd_ack     : dfi_phyupd_ack_sig     ;
       dfi_phymstr_ack_sig    = (flag2 == 1'b1) ? dfi_phymstr_ack    : dfi_phymstr_ack_sig    ;
       dfi_lp_ctrl_req_sig    = (flag2 == 1'b1) ? dfi_lp_ctrl_req    : dfi_lp_ctrl_req_sig    ;
       dfi_lp_ctrl_wakeup_sig = (flag2 == 1'b1) ? dfi_lp_ctrl_wakeup : dfi_lp_ctrl_wakeup_sig ;
       dfi_lp_data_req_sig    = (flag2 == 1'b1) ? dfi_lp_data_req    : dfi_lp_data_req_sig    ;
       dfi_lp_data_wakeup_sig = (flag2 == 1'b1) ? dfi_lp_data_wakeup : dfi_lp_data_wakeup_sig ;
    end

`endif

endmodule

`endif // DDR_SYNTH
