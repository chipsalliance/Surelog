// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: pad_ddr3.v
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
module pad_ddr3(ps_select ,bscan_mode_ctl_in ,spare_ddr3_pad ,
     spare_ddr3_paddata ,ddr_testmode_l ,bscan_clock_dr_in ,
     ddr3_bypass_data ,ddr3_dll_bypass_l ,spare_ddr3_pindata ,
     spare_ddr3_pin ,bscan_mode_ctl_out ,pad_ddr3_bso ,dram_adbginit_l ,
     dram_gclk ,ddr2_ddr3_cbd ,dram3_dq ,clk_ddr3_cken ,dram3_cb ,
     dram3_ck_p ,dram_arst_l ,dram_gdbginit_l ,dram3_ba ,dram3_cas_l ,
     dram3_ras_l ,dram3_cke ,ctu_ddr3_dll_delayctr ,bscan_hiz_l_out ,
     bypass_enable_out ,bscan_shift_dr_out ,dram3_io_bank ,
     bscan_hiz_l_in ,bscan_clock_dr_out ,bscan_update_dr_out ,serial_out
      ,ddr_so ,dram3_io_pad_enable ,ps_select_out ,vdd18 ,
     ctu_ddr3_iodll_rst_l ,dram3_io_ptr_clk_inv ,afi ,bypass_enable ,
     serial_in ,pad_ddr3_bsi ,test_mode ,ddr3_ctu_dll_lock ,ddr_si ,
     dram_grst_l ,ddr_se ,dram3_dqs ,dram3_addr ,dram3_we_l ,dram3_ck_n
      ,dram3_io_cs_l ,afo ,bscan_shift_dr_in ,dram3_io_write_en_l ,
     bscan_update_dr_in ,dram3_io_drive_enable ,ddr3_ctu_dll_overflow ,
     dram3_io_cas_l ,dram3_io_ras_l ,dram3_io_clk_enable ,
     io_dram3_data_valid ,dram3_io_addr ,io_dram3_data_in ,ddr2_ddr3_cbu
      ,dram3_io_channel_disabled ,io_dram3_ecc_in ,dram3_io_drive_data ,
     dram3_io_data_out ,dram3_io_cke ,dram3_io_pad_clk_inv ,dram3_cs_l,
     ddr3_lpf_code );
output [4:0]	ddr3_lpf_code ;
output [3:0]	dram3_ck_p ;
output [2:0]	dram3_ba ;
output [143:0]	serial_out ;
output [143:0]	afi ;
output [14:0]	dram3_addr ;
output [3:0]	dram3_ck_n ;
output [255:0]	io_dram3_data_in ;
output [31:0]	io_dram3_ecc_in ;
output [3:0]	dram3_cs_l ;
input [6:0]	spare_ddr3_paddata ;
input [4:0]	ddr3_bypass_data ;
input [2:0]	spare_ddr3_pindata ;
input [1:0]	dram_gclk ;
input [8:1]	ddr2_ddr3_cbd ;
input [2:0]	ctu_ddr3_dll_delayctr ;
input [2:0]	dram3_io_bank ;
input [4:0]	dram3_io_ptr_clk_inv ;
input [143:0]	serial_in ;
input [3:0]	dram3_io_cs_l ;
input [143:0]	afo ;
input [14:0]	dram3_io_addr ;
input [8:1]	ddr2_ddr3_cbu ;
input [287:0]	dram3_io_data_out ;
inout [6:0]	spare_ddr3_pad ;
inout [2:0]	spare_ddr3_pin ;
inout [127:0]	dram3_dq ;
inout [15:0]	dram3_cb ;
inout [35:0]	dram3_dqs ;
output		bscan_mode_ctl_out ;
output		pad_ddr3_bso ;
output		dram3_cas_l ;
output		dram3_ras_l ;
output		dram3_cke ;
output		bscan_hiz_l_out ;
output		bypass_enable_out ;
output		bscan_shift_dr_out ;
output		bscan_clock_dr_out ;
output		bscan_update_dr_out ;
output		ddr_so ;
output		ps_select_out ;
output		ddr3_ctu_dll_lock ;
output		dram3_we_l ;
output		ddr3_ctu_dll_overflow ;
output		io_dram3_data_valid ;
input		ps_select ;
input		bscan_mode_ctl_in ;
input		ddr_testmode_l ;
input		bscan_clock_dr_in ;
input		ddr3_dll_bypass_l ;
input		dram_adbginit_l ;
input		clk_ddr3_cken ;
input		dram_arst_l ;
input		dram_gdbginit_l ;
input		bscan_hiz_l_in ;
input		dram3_io_pad_enable ;
input		vdd18 ;
input		ctu_ddr3_iodll_rst_l ;
input		bypass_enable ;
input		pad_ddr3_bsi ;
input		test_mode ;
input		ddr_si ;
input		dram_grst_l ;
input		ddr_se ;
input		bscan_shift_dr_in ;
input		dram3_io_write_en_l ;
input		bscan_update_dr_in ;
input		dram3_io_drive_enable ;
input		dram3_io_cas_l ;
input		dram3_io_ras_l ;
input		dram3_io_clk_enable ;
input		dram3_io_channel_disabled ;
input		dram3_io_drive_data ;
input		dram3_io_cke ;
input		dram3_io_pad_clk_inv ;
supply1		vdd ;
 
wire		strobe ;
wire		rst_l ;
wire		scan0 ;
wire		scan1 ;
wire		net157 ;
wire		rclk ;
wire		arst2_l ;
 
 
ddr_ch_b ddr3_ddr_ch_b (
     .arst_l_out      (arst2_l ),
     .afo             ({afo } ),
     .serial_in       ({serial_in } ),
     .afi             ({afi } ),
     .serial_out      ({serial_out } ),
     .dram_io_data_out ({dram3_io_data_out } ),
     .spare_ddr_pin   ({spare_ddr3_pin[2] ,spare_ddr3_pad[6:0] ,
            spare_ddr3_pin[1:0] } ),
     .spare_ddr_data  ({spare_ddr3_pindata[2] ,spare_ddr3_paddata[6:0] ,
            spare_ddr3_pindata[1:0] } ),
     .dram_io_ptr_clk_inv ({dram3_io_ptr_clk_inv } ),
     .io_dram_data_in ({io_dram3_data_in } ),
     .io_dram_ecc_in  ({io_dram3_ecc_in } ),
     .dram_io_addr    ({dram3_io_addr } ),
     .dram_io_bank    ({dram3_io_bank } ),
     .dram_io_cs_l    ({dram3_io_cs_l } ),
     .dram_dq         ({dram3_dq } ),
     .dram_addr       ({dram3_addr } ),
     .dram_cb         ({dram3_cb } ),
     .dram_dqs        ({dram3_dqs } ),
     .dram_ba         ({dram3_ba } ),
     .dram_ck_n       ({dram3_ck_n } ),
     .dram_ck_p       ({dram3_ck_p } ),
     .dram_cs_l       ({dram3_cs_l } ),
     .lpf_code        ({ddr3_lpf_code } ),
     .cbu             ({ddr2_ddr3_cbu } ),
     .cbd             ({ddr2_ddr3_cbd } ),
     .pad_clk_si      (ddr_si ),
     .testmode_l      (ddr_testmode_l ),
     .test_mode       (test_mode ),
     .bypass_enable_out (bypass_enable_out ),
     .ps_select_out   (ps_select_out ),
     .rclk            (rclk ),
     .se              (ddr_se ),
     .pad_clk_so      (scan0 ),
     .update_dr_in    (bscan_update_dr_in ),
     .bso             (pad_ddr3_bso ),
     .bsi             (pad_ddr3_bsi ),
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
     .dram_io_clk_enable (dram3_io_clk_enable ),
     .dram_io_cke     (dram3_io_cke ),
     .dram_io_ras_l   (dram3_io_ras_l ),
     .dram_io_write_en_l (dram3_io_write_en_l ),
     .dram_io_cas_l   (dram3_io_cas_l ),
     .dram_cke        (dram3_cke ),
     .io_dram_data_valid (io_dram3_data_valid ),
     .dram_ras_l      (dram3_ras_l ),
     .dram_we_l       (dram3_we_l ),
     .dram_cas_l      (dram3_cas_l ),
     .burst_length_four (vdd ),
     .dram_io_pad_clk_inv (dram3_io_pad_clk_inv ),
     .dram_io_pad_enable (dram3_io_pad_enable ),
     .dram_io_drive_enable (dram3_io_drive_enable ),
     .rst_l           (rst_l ),
     .dram_arst_l     (dram_arst_l ),
     .dram_io_channel_disabled (dram3_io_channel_disabled ),
     .dram_io_drive_data (dram3_io_drive_data ),
     .vdd_h           (vdd18 ) );
bw_clk_cl_ddr_ddr pad_ddr3_header (
     .gclk            ({dram_gclk } ),
     .ddr_rclk        (rclk ),
     .so              (ddr_so_pre_latch ),
     .si              (scan1 ),
     .gdbginit_l      (dram_gdbginit_l ),
     .grst_l          (dram_grst_l ),
     .cluster_grst_l  (rst_l ),
     .dbginit_l       (net157 ),
     .rclk            (rclk ),
     .se              (ddr_se ),
     .adbginit_l      (dram_adbginit_l ),
     .arst2_l         (arst2_l ),
     .arst_l          (dram_arst_l ),
     .cluster_cken    (clk_ddr3_cken ) );
// ECO 7016: added instance ddr3_iodll_code_adjust 10/11/04
// ECO 7016: changed so, lpf_out connections on ddr3_master_dll

wire [4:0] ddr3_lpf_code_pre;
wire scan1_pre;

bw_iodll_code_adjust ddr3_iodll_code_adjust (
  .bypass_data (ddr3_bypass_data[4:0]),
  .ddr_clk_in (rclk),
  .delay_ctrl (ctu_ddr3_dll_delayctr[2:0]),
  .io_dll_bypass_l (ddr3_dll_bypass_l),
  .iodll_reset_l (ctu_ddr3_iodll_rst_l),
  .s_controller_out (ddr3_lpf_code_pre[4:0]),
  .s_percent_ctrl_out (ddr3_lpf_code[4:0]),
  .se (ddr_se),
  .si (scan1_pre),
  .so (scan1));

bw_iodll ddr3_master_dll (
     .ddr_testmode_l  (ddr_testmode_l ),
     .bypass_data     ({ddr3_bypass_data } ),
     .lpf_out         ({ddr3_lpf_code_pre } ),
     .delay_ctrl      ({ctu_ddr3_dll_delayctr } ),
     .so              (scan1_pre ),
     .io_dll_bypass_l (ddr3_dll_bypass_l ),
     .io_dll_reset_l  (ctu_ddr3_iodll_rst_l ),
     .se              (ddr_se ),
     .si              (scan0 ),
     .ddr_clk_in      (rclk ),
     .iodll_lock      (ddr3_ctu_dll_lock ),
     .overflow        (ddr3_ctu_dll_overflow ),
     .strobe          (strobe ) );
// End ECO 7016

bw_u1_scanl_2x lockup_latch(
                .so(ddr_so),
                .sd(ddr_so_pre_latch),
                .ck(rclk));
endmodule

