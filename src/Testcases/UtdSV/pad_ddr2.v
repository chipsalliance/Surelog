// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: pad_ddr2.v
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
module pad_ddr2(ddr2_dll_bypass_l ,ddr2_bypass_data ,clk_ddr2_cken ,
     spare_ddr2_pin ,bscan_mode_ctl_in ,spare_ddr2_pad ,bscan_hiz_l_in ,
     ddr_si ,tck ,pad_ddr2_sscan_out ,dram2_io_bank ,dram2_dq ,dram2_cb
      ,dram2_ba ,dram2_cas_l ,dram2_ras_l ,dram2_cke ,pad_ddr2_sscan_in
      ,ddr_testmode_l ,ctu_ddr2_dll_delayctr ,dram2_io_cs_l ,afo ,
     bypass_enable ,bypass_enable_out ,bscan_shift_dr_out ,
     bscan_clock_dr_out ,bscan_hiz_l_out ,ps_select_out ,
     bscan_update_dr_out ,serial_out ,afi ,vdd18 ,ddr2_ctu_dll_overflow
      ,bscan_mode_ctl_out ,pad_ddr2_bsi ,dram_arst_l ,dram_grst_l ,
     dram_gclk ,dram2_ck_p ,ctu_global_snap ,dram_gdbginit_l ,
     ctu_ddr2_iodll_rst_l ,test_mode ,bscan_clock_dr_in ,serial_in ,
     dram2_io_ptr_clk_inv ,ctu_io_sscan_update ,ctu_io_sscan_se ,
     spare_ddr2_paddata ,dram23_p_ref_res ,ddr2_ddr3_cbd ,ddr_so ,
     ps_select ,dram23_n_ref_res ,dram2_dqs ,pad_ddr2_bso ,ddr_se ,
     dram2_addr ,dram2_we_l ,dram2_ck_n ,dram_adbginit_l
      ,ddr2_ddr3_cbu ,bscan_shift_dr_in ,ddr2_ctu_dll_lock ,
     dram2_io_pad_enable ,bscan_update_dr_in ,dram2_io_drive_enable ,
     dram2_io_write_en_l ,dram2_io_cas_l ,dram2_io_ras_l ,
     dram2_io_clk_enable ,io_dram2_data_valid ,dram2_io_addr ,
     io_dram2_data_in ,dram2_io_channel_disabled ,io_dram2_ecc_in ,
     dram2_io_drive_data ,dram2_io_data_out ,dram2_io_cke ,
     dram2_io_pad_clk_inv ,dram2_cs_l ,spare_ddr2_pindata, ddr2_lpf_code );
output [4:0]	ddr2_lpf_code ;
output [2:0]	dram2_ba ;
output [143:0]	serial_out ;
output [143:0]	afi ;
output [3:0]	dram2_ck_p ;
output [8:1]	ddr2_ddr3_cbd ;
output [14:0]	dram2_addr ;
output [3:0]	dram2_ck_n ;
output [8:1]	ddr2_ddr3_cbu ;
output [255:0]	io_dram2_data_in ;
output [31:0]	io_dram2_ecc_in ;
output [3:0]	dram2_cs_l ;
input [4:0]	ddr2_bypass_data ;
input [2:0]	dram2_io_bank ;
input [2:0]	ctu_ddr2_dll_delayctr ;
input [3:0]	dram2_io_cs_l ;
input [143:0]	afo ;
input [1:0]	dram_gclk ;
input [143:0]	serial_in ;
input [4:0]	dram2_io_ptr_clk_inv ;
input [6:0]	spare_ddr2_paddata ;
input [14:0]	dram2_io_addr ;
input [287:0]	dram2_io_data_out ;
input [2:0]	spare_ddr2_pindata ;
inout [2:0]	spare_ddr2_pin ;
inout [6:0]	spare_ddr2_pad ;
inout [127:0]	dram2_dq ;
inout [15:0]	dram2_cb ;
inout [35:0]	dram2_dqs ;
output		pad_ddr2_sscan_out ;
output		dram2_cas_l ;
output		dram2_ras_l ;
output		dram2_cke ;
output		bypass_enable_out ;
output		bscan_shift_dr_out ;
output		bscan_clock_dr_out ;
output		bscan_hiz_l_out ;
output		ps_select_out ;
output		bscan_update_dr_out ;
output		ddr2_ctu_dll_overflow ;
output		bscan_mode_ctl_out ;
output		ddr_so ;
output		pad_ddr2_bso ;
output		dram2_we_l ;
output		ddr2_ctu_dll_lock ;
output		io_dram2_data_valid ;
input		ddr2_dll_bypass_l ;
input		clk_ddr2_cken ;
input		bscan_mode_ctl_in ;
input		bscan_hiz_l_in ;
input		ddr_si ;
input		tck ;
input		pad_ddr2_sscan_in ;
input		ddr_testmode_l ;
input		bypass_enable ;
input		vdd18 ;
input		pad_ddr2_bsi ;
input		dram_arst_l ;
input		dram_grst_l ;
input		ctu_global_snap ;
input		dram_gdbginit_l ;
input		ctu_ddr2_iodll_rst_l ;
input		test_mode ;
input		bscan_clock_dr_in ;
input		ctu_io_sscan_update ;
input		ctu_io_sscan_se ;
input		dram23_p_ref_res ;
input		ps_select ;
input		dram23_n_ref_res ;
input		ddr_se ;
input		dram_adbginit_l ;
input		bscan_shift_dr_in ;
input		dram2_io_pad_enable ;
input		bscan_update_dr_in ;
input		dram2_io_drive_enable ;
input		dram2_io_write_en_l ;
input		dram2_io_cas_l ;
input		dram2_io_ras_l ;
input		dram2_io_clk_enable ;
input		dram2_io_channel_disabled ;
input		dram2_io_drive_data ;
input		dram2_io_cke ;
input		dram2_io_pad_clk_inv ;
supply1		vdd ;
supply0		vss ;
 
wire [7:0]	net227 ;
wire [7:0]	net246 ;
wire		net0204 ;
wire		net196 ;
wire		rst_l ;
wire		sscan0 ;
wire		net228 ;
wire		scan0 ;
wire		scan1 ;
wire		scan2 ;
wire		scan3 ;
wire		clk_ddr2_cken_buf ;
wire		net247 ;
wire		ddr_se_buf ;
wire		rclk ;
wire		arst2_l ;
 
 
bw_io_ddr_impctl_pulldown ddr2_impctl_pulldown (
     .z               ({ddr2_ddr3_cbd } ),
     .from_csr        ({vss ,vss ,vss ,vss ,vss ,vss ,vss ,vss } ),
     .to_csr          ({net246[0] ,net246[1] ,net246[2] ,net246[3] ,
            net246[4] ,net246[5] ,net246[6] ,net246[7] } ),
     .tclk            (tck ),
     .ctu_global_snap (ctu_global_snap ),
     .ctu_io_sscan_in (sscan0 ),
     .ctu_io_sscan_se (ctu_io_sscan_se ),
     .ctu_io_sscan_update (ctu_io_sscan_update ),
     .ctu_io_sscan_out (pad_ddr2_sscan_out ),
     .rclk            (rclk ),
     .deltabit        (net247 ),
     .hard_reset_n    (rst_l ),
     .clk_dis_l       (clk_ddr2_cken_buf ),
     .we_csr          (vss ),
     .si              (scan1 ),
     .se              (ddr_se_buf ),
     .vdd18           (vdd18 ),
     .pad             (dram23_n_ref_res ),
     .so              (scan2 ) );
bw_io_ddr_impctl_pullup ddr2_impctl_pullup (
     .z               ({ddr2_ddr3_cbu } ),
     .from_csr        ({vss ,vss ,vss ,vss ,vss ,vss ,vss ,vss } ),
     .to_csr          ({net227[0] ,net227[1] ,net227[2] ,net227[3] ,
            net227[4] ,net227[5] ,net227[6] ,net227[7] } ),
     .rclk            (rclk ),
     .so              (scan1 ),
     .deltabit        (net228 ),
     .hard_reset_n    (rst_l ),
     .clk_dis_l       (clk_ddr2_cken_buf ),
     .we_csr          (vss ),
     .si              (scan0 ),
     .se              (ddr_se_buf ),
     .ctu_io_sscan_se (ctu_io_sscan_se ),
     .vdd18           (vdd18 ),
     .ctu_io_sscan_in (pad_ddr2_sscan_in ),
     .ctu_io_sscan_out (sscan0 ),
     .ctu_io_sscan_update (ctu_io_sscan_update ),
     .pad             (dram23_p_ref_res ),
     .ctu_global_snap (ctu_global_snap ),
     .tclk            (tck ) );
// ECO 7016: added instance ddr2_iodll_code_adjust 10/11/04
// ECO 7016: Changed so, lpf_out connections on ddr2_master_dll

wire [4:0] ddr2_lpf_code_pre;
wire scan3_pre;

bw_iodll_code_adjust ddr2_iodll_code_adjust (
  .bypass_data (ddr2_bypass_data[4:0]),
  .ddr_clk_in (rclk),
  .delay_ctrl (ctu_ddr2_dll_delayctr[2:0]),
  .io_dll_bypass_l (ddr2_dll_bypass_l),
  .iodll_reset_l (ctu_ddr2_iodll_rst_l),
  .s_controller_out (ddr2_lpf_code_pre[4:0]),
  .s_percent_ctrl_out (ddr2_lpf_code[4:0]),
  .se (ddr_se_buf),
  .si (scan3_pre),
  .so (scan3));

bw_iodll ddr2_master_dll (
     .ddr_testmode_l  (ddr_testmode_l ),
     .bypass_data     ({ddr2_bypass_data } ),
     .lpf_out         (ddr2_lpf_code_pre ),
     .delay_ctrl      ({ctu_ddr2_dll_delayctr } ),
     .so              (scan3_pre ),
     .io_dll_bypass_l (ddr2_dll_bypass_l ),
     .io_dll_reset_l  (ctu_ddr2_iodll_rst_l ),
     .se              (ddr_se_buf ),
     .si              (scan2 ),
     .ddr_clk_in      (rclk ),
     .iodll_lock      (ddr2_ctu_dll_lock ),
     .overflow        (ddr2_ctu_dll_overflow ),
     .strobe          (net0204 ) );
// End ECO 7016

bw_clk_cl_ddr_ddr pad_ddr2_header (
     .gclk            ({dram_gclk } ),
     .ddr_rclk        (rclk ),
     .so              (ddr_so_pre_latch ),
     .si              (scan3 ),
     .gdbginit_l      (dram_gdbginit_l ),
     .grst_l          (dram_grst_l ),
     .cluster_grst_l  (rst_l ),
     .dbginit_l       (net196 ),
     .rclk            (rclk ),
     .se              (ddr_se_buf ),
     .adbginit_l      (dram_adbginit_l ),
     .arst2_l         (arst2_l ),
     .arst_l          (dram_arst_l ),
     .cluster_cken    (clk_ddr2_cken_buf ) );
bw_u1_buf_40x I223 (
     .z               (ddr_se_buf ),
     .a               (ddr_se ) );
ddr_ch ddr2_ddr_ch (
     .arst_l_out      (arst2_l ),
     .afo             ({afo } ),
     .serial_in       ({serial_in } ),
     .afi             ({afi } ),
     .serial_out      ({serial_out } ),
     .dram_io_data_out ({dram2_io_data_out } ),
     .spare_ddr_pin   ({spare_ddr2_pin[2] ,spare_ddr2_pad[6:0] ,
            spare_ddr2_pin[1:0] } ),
     .spare_ddr_data  ({spare_ddr2_pindata[2] ,spare_ddr2_paddata[6:0] ,
            spare_ddr2_pindata[1:0] } ),
     .dram_io_ptr_clk_inv ({dram2_io_ptr_clk_inv } ),
     .io_dram_data_in ({io_dram2_data_in } ),
     .io_dram_ecc_in  ({io_dram2_ecc_in } ),
     .dram_io_addr    ({dram2_io_addr } ),
     .dram_io_bank    ({dram2_io_bank } ),
     .dram_io_cs_l    ({dram2_io_cs_l } ),
     .dram_dq         ({dram2_dq } ),
     .dram_addr       ({dram2_addr } ),
     .dram_cb         ({dram2_cb } ),
     .dram_dqs        ({dram2_dqs } ),
     .dram_ba         ({dram2_ba } ),
     .dram_ck_n       ({dram2_ck_n } ),
     .dram_ck_p       ({dram2_ck_p } ),
     .dram_cs_l       ({dram2_cs_l } ),
     .lpf_code        (ddr2_lpf_code ),
     .cbu             ({ddr2_ddr3_cbu } ),
     .cbd             ({ddr2_ddr3_cbd } ),
     .update_dr_in    (bscan_update_dr_in ),
     .mode_ctrl_in    (bscan_mode_ctl_in ),
     .shift_dr_in     (bscan_shift_dr_in ),
     .clock_dr_in     (bscan_clock_dr_in ),
     .hiz_n_in        (bscan_hiz_l_in ),
     .testmode_l      (ddr_testmode_l ),
     .test_mode       (test_mode ),
     .bypass_enable_out (bypass_enable_out ),
     .ps_select_out   (ps_select_out ),
     .rclk            (rclk ),
     .se              (ddr_se_buf ),
     .pad_clk_so      (scan0 ),
     .pad_clk_si      (ddr_si ),
     .bso             (pad_ddr2_bso ),
     .bsi             (pad_ddr2_bsi ),
     .mode_ctrl_out   (bscan_mode_ctl_out ),
     .update_dr_out   (bscan_update_dr_out ),
     .shift_dr_out    (bscan_shift_dr_out ),
     .clock_dr_out    (bscan_clock_dr_out ),
     .hiz_n_out       (bscan_hiz_l_out ),
     .bypass_enable_in (bypass_enable ),
     .ps_select_in    (ps_select ),
     .strobe          (net0204 ),
     .dram_io_clk_enable (dram2_io_clk_enable ),
     .dram_io_cke     (dram2_io_cke ),
     .dram_io_ras_l   (dram2_io_ras_l ),
     .dram_io_write_en_l (dram2_io_write_en_l ),
     .dram_io_cas_l   (dram2_io_cas_l ),
     .dram_cke        (dram2_cke ),
     .io_dram_data_valid (io_dram2_data_valid ),
     .dram_ras_l      (dram2_ras_l ),
     .dram_we_l       (dram2_we_l ),
     .dram_cas_l      (dram2_cas_l ),
     .burst_length_four (vdd ),
     .dram_io_pad_clk_inv (dram2_io_pad_clk_inv ),
     .dram_io_pad_enable (dram2_io_pad_enable ),
     .dram_io_drive_enable (dram2_io_drive_enable ),
     .rst_l           (rst_l ),
     .dram_arst_l     (dram_arst_l ),
     .dram_io_channel_disabled (dram2_io_channel_disabled ),
     .dram_io_drive_data (dram2_io_drive_data ),
     .vdd_h           (vdd18 ) );
bw_u1_buf_40x I225 (
     .z               (clk_ddr2_cken_buf ),
     .a               (clk_ddr2_cken ) );
bw_u1_scanl_2x lockup_latch(
                .so(ddr_so),
                .sd(ddr_so_pre_latch),
                .ck(rclk));
endmodule

