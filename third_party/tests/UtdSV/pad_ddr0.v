// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: pad_ddr0.v
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
module pad_ddr0(bscan_mode_ctl_in ,spare_ddr0_paddata ,ddr_si ,
     ddr0_dll_bypass_l ,ddr0_bypass_data ,spare_ddr0_pin ,clkobs ,
     spare_ddr0_pindata ,ctu_io_clkobs ,tck ,spare_ddr0_pad ,
     ddr_testmode_l ,ddr_se ,ps_select ,ddr_so ,pad_ddr0_sscan_out ,afo
      ,bypass_enable ,bscan_hiz_l_out ,bscan_shift_dr_out ,ps_select_out
      ,bscan_update_dr_out ,vdd18 ,test_mode ,serial_in ,
     bypass_enable_out ,bscan_clock_dr_out ,serial_out ,afi ,
     bscan_mode_ctl_out ,bscan_hiz_l_in ,dram0_dq ,dram0_dqs ,dram0_cb ,
     dram0_addr ,dram0_ba ,dram0_cs_l ,dram0_we_l ,dram0_cas_l ,
     dram0_ras_l ,dram0_cke ,dram0_ck_n ,dram0_ck_p ,
     ctu_ddr0_iodll_rst_l ,dram_adbginit_l ,pad_ddr0_bso ,ddr0_ddr1_cbd
      ,dram_arst_l ,dram_gdbginit_l ,bscan_clock_dr_in ,
     ctu_ddr0_dll_delayctr ,pad_ddr0_bsi ,pad_ddr0_sscan_in ,
     ctu_io_sscan_se ,ctu_io_sscan_update ,ctu_global_snap ,
     dram01_p_ref_res ,ddr0_ddr1_cbu ,bscan_shift_dr_in
      ,dram01_n_ref_res ,ddr0_ctu_dll_overflow ,bscan_update_dr_in ,
     dram0_io_ptr_clk_inv ,dram_gclk ,dram0_io_write_en_l ,
     dram0_io_ras_l ,dram0_io_cke ,io_dram0_data_in ,dram0_io_drive_data
      ,dram0_io_addr ,io_dram0_data_valid ,dram0_io_pad_enable ,
     io_dram0_ecc_in ,dram0_io_data_out ,dram0_io_drive_enable ,
     dram0_io_channel_disabled ,dram_grst_l ,clk_ddr0_cken ,
     dram0_io_cs_l ,dram0_io_cas_l ,dram0_io_clk_enable ,dram0_io_bank ,
     dram0_io_pad_clk_inv ,ddr0_ctu_dll_lock, ddr0_lpf_code );
output [4:0]	ddr0_lpf_code ;
output [143:0]	serial_out ;
output [143:0]	afi ;
output [14:0]	dram0_addr ;
output [2:0]	dram0_ba ;
output [3:0]	dram0_cs_l ;
output [3:0]	dram0_ck_n ;
output [3:0]	dram0_ck_p ;
output [8:1]	ddr0_ddr1_cbd ;
output [8:1]	ddr0_ddr1_cbu ;
output [255:0]	io_dram0_data_in ;
output [31:0]	io_dram0_ecc_in ;
input [6:0]	spare_ddr0_paddata ;
input [4:0]	ddr0_bypass_data ;
input [2:2]	spare_ddr0_pindata ;
input [1:0]	ctu_io_clkobs ;
input [143:0]	afo ;
input [143:0]	serial_in ;
input [2:0]	ctu_ddr0_dll_delayctr ;
input [4:0]	dram0_io_ptr_clk_inv ;
input [1:0]	dram_gclk ;
input [14:0]	dram0_io_addr ;
input [287:0]	dram0_io_data_out ;
input [3:0]	dram0_io_cs_l ;
input [2:0]	dram0_io_bank ;
inout [2:2]	spare_ddr0_pin ;
inout [1:0]	clkobs ;
inout [6:0]	spare_ddr0_pad ;
inout [127:0]	dram0_dq ;
inout [35:0]	dram0_dqs ;
inout [15:0]	dram0_cb ;
output		ddr_so ;
output		pad_ddr0_sscan_out ;
output		bscan_hiz_l_out ;
output		bscan_shift_dr_out ;
output		ps_select_out ;
output		bscan_update_dr_out ;
output		bypass_enable_out ;
output		bscan_clock_dr_out ;
output		bscan_mode_ctl_out ;
output		dram0_we_l ;
output		dram0_cas_l ;
output		dram0_ras_l ;
output		dram0_cke ;
output		pad_ddr0_bso ;
output		ddr0_ctu_dll_overflow ;
output		io_dram0_data_valid ;
output		ddr0_ctu_dll_lock ;
input		bscan_mode_ctl_in ;
input		ddr_si ;
input		ddr0_dll_bypass_l ;
input		tck ;
input		ddr_testmode_l ;
input		ddr_se ;
input		ps_select ;
input		bypass_enable ;
input		vdd18 ;
input		test_mode ;
input		bscan_hiz_l_in ;
input		ctu_ddr0_iodll_rst_l ;
input		dram_adbginit_l ;
input		dram_arst_l ;
input		dram_gdbginit_l ;
input		bscan_clock_dr_in ;
input		pad_ddr0_bsi ;
input		pad_ddr0_sscan_in ;
input		ctu_io_sscan_se ;
input		ctu_io_sscan_update ;
input		ctu_global_snap ;
input		dram01_p_ref_res ;
input		bscan_shift_dr_in ;
input		dram01_n_ref_res ;
input		bscan_update_dr_in ;
input		dram0_io_write_en_l ;
input		dram0_io_ras_l ;
input		dram0_io_cke ;
input		dram0_io_drive_data ;
input		dram0_io_pad_enable ;
input		dram0_io_drive_enable ;
input		dram0_io_channel_disabled ;
input		dram_grst_l ;
input		clk_ddr0_cken ;
input		dram0_io_cas_l ;
input		dram0_io_clk_enable ;
input		dram0_io_pad_clk_inv ;
supply1		vdd ;
supply0		vss ;
 
wire [7:0]	net223 ;
wire [7:0]	net243 ;
wire		net191 ;
wire		clk_ddr0_cken_buf ;
wire		strobe ;
wire		rst_l ;
wire		sscan0 ;
wire		net224 ;
wire		scan0 ;
wire		scan1 ;
wire		scan2 ;
wire		scan3 ;
wire		net244 ;
wire		ddr_se_buf ;
wire		rclk ;
wire		arst2_l ;

 
bw_clk_cl_ddr_ddr pad_ddr0_header (
     .gclk            ({dram_gclk } ),
     .ddr_rclk        (rclk ),
     .so              (ddr_so_pre_latch ),
     .si              (scan3 ),
     .gdbginit_l      (dram_gdbginit_l ),
     .grst_l          (dram_grst_l ),
     .cluster_grst_l  (rst_l ),
     .dbginit_l       (net191 ),
     .rclk            (rclk ),
     .se              (ddr_se_buf ),
     .adbginit_l      (dram_adbginit_l ),
     .arst_l          (dram_arst_l ),
     .arst2_l         (arst2_l ),
     .cluster_cken    (clk_ddr0_cken_buf ) );
ddr_ch ddr0_ddr_ch (
     .arst_l_out      (arst2_l ),
     .afo             ({afo } ),
     .serial_in       ({serial_in } ),
     .afi             ({afi } ),
     .serial_out      ({serial_out } ),
     .dram_io_data_out ({dram0_io_data_out } ),
     .spare_ddr_pin   ({spare_ddr0_pin[2] ,spare_ddr0_pad[6:0] ,
            clkobs[1:0] } ),
     .spare_ddr_data  ({spare_ddr0_pindata[2] ,spare_ddr0_paddata[6:0] ,
            ctu_io_clkobs[1:0] } ),
     .dram_io_ptr_clk_inv ({dram0_io_ptr_clk_inv } ),
     .io_dram_data_in ({io_dram0_data_in } ),
     .io_dram_ecc_in  ({io_dram0_ecc_in } ),
     .dram_io_addr    ({dram0_io_addr } ),
     .dram_io_bank    ({dram0_io_bank } ),
     .dram_io_cs_l    ({dram0_io_cs_l } ),
     .dram_dq         ({dram0_dq } ),
     .dram_addr       ({dram0_addr } ),
     .dram_cb         ({dram0_cb } ),
     .dram_dqs        ({dram0_dqs } ),
     .dram_ba         ({dram0_ba } ),
     .dram_ck_n       ({dram0_ck_n } ),
     .dram_ck_p       ({dram0_ck_p } ),
     .dram_cs_l       ({dram0_cs_l } ),
     .lpf_code        ({ddr0_lpf_code } ),
     .cbu             ({ddr0_ddr1_cbu } ),
     .cbd             ({ddr0_ddr1_cbd } ),
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
     .bso             (pad_ddr0_bso ),
     .bsi             (pad_ddr0_bsi ),
     .mode_ctrl_out   (bscan_mode_ctl_out ),
     .update_dr_out   (bscan_update_dr_out ),
     .shift_dr_out    (bscan_shift_dr_out ),
     .clock_dr_out    (bscan_clock_dr_out ),
     .hiz_n_out       (bscan_hiz_l_out ),
     .bypass_enable_in (bypass_enable ),
     .ps_select_in    (ps_select ),
     .strobe          (strobe ),
     .dram_io_clk_enable (dram0_io_clk_enable ),
     .dram_io_cke     (dram0_io_cke ),
     .dram_io_ras_l   (dram0_io_ras_l ),
     .dram_io_write_en_l (dram0_io_write_en_l ),
     .dram_io_cas_l   (dram0_io_cas_l ),
     .dram_cke        (dram0_cke ),
     .io_dram_data_valid (io_dram0_data_valid ),
     .dram_ras_l      (dram0_ras_l ),
     .dram_we_l       (dram0_we_l ),
     .dram_cas_l      (dram0_cas_l ),
     .burst_length_four (vdd ),
     .dram_io_pad_clk_inv (dram0_io_pad_clk_inv ),
     .dram_io_pad_enable (dram0_io_pad_enable ),
     .dram_io_drive_enable (dram0_io_drive_enable ),
     .rst_l           (rst_l ),
     .dram_arst_l     (dram_arst_l ),
     .dram_io_channel_disabled (dram0_io_channel_disabled ),
     .dram_io_drive_data (dram0_io_drive_data ),
     .vdd_h           (vdd18 ) );
bw_io_ddr_impctl_pulldown ddr0_impctl_pulldown (
     .z               ({ddr0_ddr1_cbd } ),
     .from_csr        ({vss ,vss ,vss ,vss ,vss ,vss ,vss ,vss } ),
     .to_csr          ({net243[0] ,net243[1] ,net243[2] ,net243[3] ,
            net243[4] ,net243[5] ,net243[6] ,net243[7] } ),
     .tclk            (tck ),
     .ctu_global_snap (ctu_global_snap ),
     .ctu_io_sscan_in (sscan0 ),
     .ctu_io_sscan_se (ctu_io_sscan_se ),
     .ctu_io_sscan_update (ctu_io_sscan_update ),
     .ctu_io_sscan_out (pad_ddr0_sscan_out ),
     .rclk            (rclk ),
     .deltabit        (net244 ),
     .hard_reset_n    (rst_l ),
     .clk_dis_l       (clk_ddr0_cken_buf ),
     .we_csr          (vss ),
     .si              (scan1 ),
     .se              (ddr_se_buf ),
     .vdd18           (vdd18 ),
     .pad             (dram01_n_ref_res ),
     .so              (scan2 ) );

// ECO 7016 added ddr0_iodll_code_adjust 10/11/04
// ECO 7016 Changed so, lpf_out port connections on ddr0_master_dll

wire [4:0] ddr0_lpf_code_pre;
wire scan3_pre;

bw_iodll_code_adjust ddr0_iodll_code_adjust (
	.bypass_data (ddr0_bypass_data[4:0]),
	.ddr_clk_in (rclk),
	.delay_ctrl (ctu_ddr0_dll_delayctr[2:0]),
	.io_dll_bypass_l (ddr0_dll_bypass_l),
	.iodll_reset_l (ctu_ddr0_iodll_rst_l),
	.s_controller_out (ddr0_lpf_code_pre[4:0]),
	.s_percent_ctrl_out (ddr0_lpf_code[4:0]),
	.se (ddr_se_buf),
	.si (scan3_pre),
	.so (scan3));

bw_iodll ddr0_master_dll (
     .ddr_testmode_l  (ddr_testmode_l ),
     .bypass_data     ({ddr0_bypass_data } ),
     .lpf_out         ({ddr0_lpf_code_pre } ),
     .delay_ctrl      ({ctu_ddr0_dll_delayctr } ),
     .so              (scan3_pre ),
     .io_dll_bypass_l (ddr0_dll_bypass_l ),
     .io_dll_reset_l  (ctu_ddr0_iodll_rst_l ),
     .se              (ddr_se_buf ),
     .si              (scan2 ),
     .ddr_clk_in      (rclk ),
     .iodll_lock      (ddr0_ctu_dll_lock ),
     .overflow        (ddr0_ctu_dll_overflow ),
     .strobe          (strobe ) );
// End ECO 7016

bw_io_ddr_impctl_pullup ddr0_impctl_pullup (
     .z               ({ddr0_ddr1_cbu } ),
     .from_csr        ({vss ,vss ,vss ,vss ,vss ,vss ,vss ,vss } ),
     .to_csr          ({net223[0] ,net223[1] ,net223[2] ,net223[3] ,
            net223[4] ,net223[5] ,net223[6] ,net223[7] } ),
     .rclk            (rclk ),
     .so              (scan1 ),
     .deltabit        (net224 ),
     .hard_reset_n    (rst_l ),
     .clk_dis_l       (clk_ddr0_cken_buf ),
     .we_csr          (vss ),
     .si              (scan0 ),
     .se              (ddr_se_buf ),
     .ctu_io_sscan_se (ctu_io_sscan_se ),
     .vdd18           (vdd18 ),
     .ctu_io_sscan_in (pad_ddr0_sscan_in ),
     .ctu_io_sscan_out (sscan0 ),
     .ctu_io_sscan_update (ctu_io_sscan_update ),
     .pad             (dram01_p_ref_res ),
     .ctu_global_snap (ctu_global_snap ),
     .tclk            (tck ) );
bw_u1_buf_40x I223 (
     .z               (ddr_se_buf ),
     .a               (ddr_se ) );
bw_u1_buf_40x I225 (
     .z               (clk_ddr0_cken_buf ),
     .a               (clk_ddr0_cken ) );
bw_u1_scanl_2x lockup_latch(
                .so(ddr_so),
                .sd(ddr_so_pre_latch),
                .ck(rclk));
endmodule


