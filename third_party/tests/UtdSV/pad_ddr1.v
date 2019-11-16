// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: pad_ddr1.v
// Copyright (c) 2006 Sun Microsystems, Inc.  All Rights Reserved.
// DO NOT ALTER OR REMOVE COPYRIGHT NOTICES.
// 
// The above named program is free software; you can redistribute it and/or
// modify it under the terms of the GNU General Public
// License version 2 as published by the Free Software Foundation.
// 
// The above named program is distributed in the hope that it will be 
// useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// General Public License for more details.
// 
// You should have received a copy of the GNU General Public
// License along with this work; if not, write to the Free Software
// Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301, USA.
// 
// ========== Copyright Header End ============================================
module pad_ddr1(ddr1_bypass_data ,spare_ddr1_pindata ,spare_ddr1_pin ,
     ddr_testmode_l ,ddr1_dll_bypass_l ,bscan_mode_ctl_in ,
     spare_ddr1_pad ,spare_ddr1_paddata ,ps_select ,ddr_se ,ddr_so ,
     ddr_si ,bscan_hiz_l_in ,test_mode ,serial_in ,afo ,bypass_enable ,
     serial_out ,afi ,bscan_update_dr_out ,bscan_shift_dr_out ,
     bscan_clock_dr_out ,bscan_hiz_l_out ,bypass_enable_out ,
     ps_select_out ,bscan_mode_ctl_out ,pad_ddr1_bso ,dram_arst_l ,
     dram_gdbginit_l ,ddr0_ddr1_cbu ,dram1_io_ptr_clk_inv ,dram1_io_bank
      ,dram1_dq ,dram_gclk ,clk_ddr1_cken ,dram1_cb ,dram1_ck_p ,
     ddr0_ddr1_cbd ,dram_grst_l ,dram1_ba ,dram1_cas_l ,dram1_ras_l ,
     dram1_cke ,vdd18 ,ctu_ddr1_dll_delayctr ,bscan_clock_dr_in ,
     ctu_ddr1_iodll_rst_l ,dram1_io_pad_enable ,pad_ddr1_bsi ,
     ddr1_ctu_dll_lock ,dram_adbginit_l ,dram1_dqs ,dram1_addr ,
     dram1_we_l ,dram1_ck_n ,dram1_io_cs_l ,bscan_shift_dr_in ,
     dram1_io_write_en_l ,bscan_update_dr_in ,dram1_io_drive_enable ,
     ddr1_ctu_dll_overflow ,dram1_io_cas_l ,dram1_io_ras_l ,
     dram1_io_clk_enable ,io_dram1_data_valid ,dram1_io_addr ,
     io_dram1_data_in ,dram1_io_channel_disabled ,io_dram1_ecc_in ,
     dram1_io_drive_data ,dram1_io_data_out ,dram1_io_cke ,
     dram1_io_pad_clk_inv ,dram1_cs_l, ddr1_lpf_code );
output [4:0]	ddr1_lpf_code ;
output [143:0]	serial_out ;
output [143:0]	afi ;
output [3:0]	dram1_ck_p ;
output [2:0]	dram1_ba ;
output [14:0]	dram1_addr ;
output [3:0]	dram1_ck_n ;
output [255:0]	io_dram1_data_in ;
output [31:0]	io_dram1_ecc_in ;
output [3:0]	dram1_cs_l ;
input [4:0]	ddr1_bypass_data ;
input [2:0]	spare_ddr1_pindata ;
input [6:0]	spare_ddr1_paddata ;
input [143:0]	serial_in ;
input [143:0]	afo ;
input [8:1]	ddr0_ddr1_cbu ;
input [4:0]	dram1_io_ptr_clk_inv ;
input [2:0]	dram1_io_bank ;
input [1:0]	dram_gclk ;
input [8:1]	ddr0_ddr1_cbd ;
input [2:0]	ctu_ddr1_dll_delayctr ;
input [3:0]	dram1_io_cs_l ;
input [14:0]	dram1_io_addr ;
input [287:0]	dram1_io_data_out ;
inout [2:0]	spare_ddr1_pin ;
inout [6:0]	spare_ddr1_pad ;
inout [127:0]	dram1_dq ;
inout [15:0]	dram1_cb ;
inout [35:0]	dram1_dqs ;
output		ddr_so ;
output		bscan_update_dr_out ;
output		bscan_shift_dr_out ;
output		bscan_clock_dr_out ;
output		bscan_hiz_l_out ;
output		bypass_enable_out ;
output		ps_select_out ;
output		bscan_mode_ctl_out ;
output		pad_ddr1_bso ;
output		dram1_cas_l ;
output		dram1_ras_l ;
output		dram1_cke ;
output		ddr1_ctu_dll_lock ;
output		dram1_we_l ;
output		ddr1_ctu_dll_overflow ;
output		io_dram1_data_valid ;
input		ddr_testmode_l ;
input		ddr1_dll_bypass_l ;
input		bscan_mode_ctl_in ;
input		ps_select ;
input		ddr_se ;
input		ddr_si ;
input		bscan_hiz_l_in ;
input		test_mode ;
input		bypass_enable ;
input		dram_arst_l ;
input		dram_gdbginit_l ;
input		clk_ddr1_cken ;
input		dram_grst_l ;
input		vdd18 ;
input		bscan_clock_dr_in ;
input		ctu_ddr1_iodll_rst_l ;
input		dram1_io_pad_enable ;
input		pad_ddr1_bsi ;
input		dram_adbginit_l ;
input		bscan_shift_dr_in ;
input		dram1_io_write_en_l ;
input		bscan_update_dr_in ;
input		dram1_io_drive_enable ;
input		dram1_io_cas_l ;
input		dram1_io_ras_l ;
input		dram1_io_clk_enable ;
input		dram1_io_channel_disabled ;
input		dram1_io_drive_data ;
input		dram1_io_cke ;
input		dram1_io_pad_clk_inv ;
supply1		vdd ;
 
wire		strobe ;
wire		rst_l ;
wire		scan0 ;
wire		scan1 ;
wire		net147 ;
wire		rclk ;
wire		arst2_l ;
 
 
ddr_ch_b ddr1_ddr_ch_b (
     .arst_l_out      (arst2_l ),
     .afo             ({afo } ),
     .serial_in       ({serial_in } ),
     .afi             ({afi } ),
     .serial_out      ({serial_out } ),
     .dram_io_data_out ({dram1_io_data_out } ),
     .spare_ddr_pin   ({spare_ddr1_pin[2] ,spare_ddr1_pad[6:0] ,
            spare_ddr1_pin[1:0] } ),
     .spare_ddr_data  ({spare_ddr1_pindata[2] ,spare_ddr1_paddata[6:0] ,
            spare_ddr1_pindata[1:0] } ),
     .dram_io_ptr_clk_inv ({dram1_io_ptr_clk_inv } ),
     .io_dram_data_in ({io_dram1_data_in } ),
     .io_dram_ecc_in  ({io_dram1_ecc_in } ),
     .dram_io_addr    ({dram1_io_addr } ),
     .dram_io_bank    ({dram1_io_bank } ),
     .dram_io_cs_l    ({dram1_io_cs_l } ),
     .dram_dq         ({dram1_dq } ),
     .dram_addr       ({dram1_addr } ),
     .dram_cb         ({dram1_cb } ),
     .dram_dqs        ({dram1_dqs } ),
     .dram_ba         ({dram1_ba } ),
     .dram_ck_n       ({dram1_ck_n } ),
     .dram_ck_p       ({dram1_ck_p } ),
     .dram_cs_l       ({dram1_cs_l } ),
     .lpf_code        ({ddr1_lpf_code } ),
     .cbu             ({ddr0_ddr1_cbu } ),
     .cbd             ({ddr0_ddr1_cbd } ),
     .pad_clk_si      (ddr_si ),
     .testmode_l      (ddr_testmode_l ),
     .test_mode       (test_mode ),
     .bypass_enable_out (bypass_enable_out ),
     .ps_select_out   (ps_select_out ),
     .rclk            (rclk ),
     .se              (ddr_se ),
     .pad_clk_so      (scan0 ),
     .update_dr_in    (bscan_update_dr_in ),
     .bso             (pad_ddr1_bso ),
     .bsi             (pad_ddr1_bsi ),
     .bypass_enable_in (bypass_enable ),
     .mode_ctrl_out   (bscan_mode_ctl_out ),
     .update_dr_out   (bscan_update_dr_out ),
     .shift_dr_out    (bscan_shift_dr_out ),
     .clock_dr_out    (bscan_clock_dr_out ),
     .hiz_n_out       (bscan_hiz_l_out ),
     .ps_select_in    (ps_select ),
     .mode_ctrl_in    (bscan_mode_ctl_in ),
     .shift_dr_in     (bscan_shift_dr_in ),
     .clock_dr_in     (bscan_clock_dr_in ),
     .hiz_n_in        (bscan_hiz_l_in ),
     .strobe          (strobe ),
     .dram_io_clk_enable (dram1_io_clk_enable ),
     .dram_io_cke     (dram1_io_cke ),
     .dram_io_ras_l   (dram1_io_ras_l ),
     .dram_io_write_en_l (dram1_io_write_en_l ),
     .dram_io_cas_l   (dram1_io_cas_l ),
     .dram_cke        (dram1_cke ),
     .io_dram_data_valid (io_dram1_data_valid ),
     .dram_ras_l      (dram1_ras_l ),
     .dram_we_l       (dram1_we_l ),
     .dram_cas_l      (dram1_cas_l ),
     .burst_length_four (vdd ),
     .dram_io_pad_clk_inv (dram1_io_pad_clk_inv ),
     .dram_io_pad_enable (dram1_io_pad_enable ),
     .dram_io_drive_enable (dram1_io_drive_enable ),
     .rst_l           (rst_l ),
     .dram_arst_l     (dram_arst_l ),
     .dram_io_channel_disabled (dram1_io_channel_disabled ),
     .dram_io_drive_data (dram1_io_drive_data ),
     .vdd_h           (vdd18 ) );

// ECO 7016: added ddr1_iodll_code_adjust 10/11/04

wire [4:0] ddr1_lpf_code_pre;
wire scan1_pre;

bw_iodll_code_adjust ddr1_iodll_code_adjust (
  .bypass_data (ddr1_bypass_data[4:0]),
  .ddr_clk_in (rclk),
  .delay_ctrl (ctu_ddr1_dll_delayctr[2:0]),
  .io_dll_bypass_l (ddr1_dll_bypass_l),
  .iodll_reset_l (ctu_ddr1_iodll_rst_l),
  .s_controller_out (ddr1_lpf_code_pre[4:0]),
  .s_percent_ctrl_out (ddr1_lpf_code[4:0]),
  .se (ddr_se),
  .si (scan1_pre),
  .so (scan1));

bw_iodll ddr1_master_dll (
     .ddr_testmode_l  (ddr_testmode_l ),
     .bypass_data     ({ddr1_bypass_data } ),
     .lpf_out         ({ddr1_lpf_code_pre } ),
     .delay_ctrl      ({ctu_ddr1_dll_delayctr } ),
     .so              (scan1_pre ),
     .io_dll_bypass_l (ddr1_dll_bypass_l ),
     .io_dll_reset_l  (ctu_ddr1_iodll_rst_l ),
     .se              (ddr_se ),
     .si              (scan0 ),
     .ddr_clk_in      (rclk ),
     .iodll_lock      (ddr1_ctu_dll_lock ),
     .overflow        (ddr1_ctu_dll_overflow ),
     .strobe          (strobe ) );
// End ECO 7016

bw_clk_cl_ddr_ddr pad_ddr1_header (
     .gclk            ({dram_gclk } ),
     .ddr_rclk        (rclk ),
     .so              (ddr_so_pre_latch ),
     .si              (scan1 ),
     .gdbginit_l      (dram_gdbginit_l ),
     .grst_l          (dram_grst_l ),
     .cluster_grst_l  (rst_l ),
     .dbginit_l       (net147 ),
     .rclk            (rclk ),
     .se              (ddr_se ),
     .adbginit_l      (dram_adbginit_l ),
     .arst_l          (dram_arst_l ),
     .arst2_l         (arst2_l ),
     .cluster_cken    (clk_ddr1_cken ) );
bw_u1_scanl_2x lockup_latch(
                .so(ddr_so),
                .sd(ddr_so_pre_latch),
                .ck(rclk));
endmodule

