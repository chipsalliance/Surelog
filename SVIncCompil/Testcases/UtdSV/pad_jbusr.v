// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: pad_jbusr.v
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
module pad_jbusr(bscan_hiz_l_out ,bscan_update_dr_out ,
     bscan_clock_dr_out ,bscan_shift_dr_out ,bscan_clock_dr_in ,
     jbus_n_ref_res ,jbi_io_j_ad ,j_adp ,bscan_mode_ctl_out ,
     j_req1_out_l ,j_pack5 ,j_pack4 ,j_pack1 ,j_pack0 ,j_req4_in_l ,
     dtl_r_vref ,jbus_p_ref_res ,jbi_io_j_req1_out_en ,j_adtype ,
     jbi_io_j_req1_out_l ,serial_in ,j_ad ,spare_jbusr_pin ,
     jbi_io_config_dtl ,io_jbi_j_ad ,ps_select ,bypass_enable ,
     ps_select_out ,bypass_enable_out ,clk_jbusr_cken ,jbus_gclk ,
     jbus_grst_l ,jbus_arst_l ,jbus_gdbginit_l ,jbus_adbginit_l ,
     pad_jbusr_se ,j_req0_out_l ,bscan_shift_dr_in ,j_par ,
     pad_jbusr_sscan_out ,jbi_io_j_err ,tclk ,serial_out ,pad_jbusr_so ,
     pad_jbusr_si ,pad_jbusr_bsi ,vddo ,jbi_io_j_adtype ,rst_val_up ,
     bscan_hiz_l_in ,jbi_io_j_ad_en ,sel_bypass ,bscan_mode_ctl_in ,
     bscan_update_dr_in ,rst_val_dn ,rst_io_l ,por_l ,jbi_io_j_adp_en ,
     jbi_io_j_pack0 ,jbi_io_j_pack1 ,jbi_io_j_pack0_en ,
     jbi_io_j_pack1_en ,spare_jbusr_data ,jbi_io_j_adtype_en ,hard_rst_l
      ,jbi_io_j_par_en ,jbi_io_j_adp ,jbi_io_j_req0_out_en ,
     ctu_io_sscan_update ,jbi_io_j_req0_out_l ,jbi_io_j_par ,
     pad_jbusr_sscan_in ,ctu_io_sscan_se ,j_req5_in_l ,spare_jbusr_oe ,
     spare_jbusr_to_core ,j_rst_l ,pad_jbusr_bso ,j_err ,io_jbi_j_adtype
      ,io_jbi_j_pack4 ,io_jbi_j_adp ,io_jbi_j_pack5 ,io_jbi_j_req5_in_l
      ,io_jbi_j_req4_in_l ,io_jbi_j_par ,io_jbi_j_rst_l ,jbusr_jbusl_cbu
      ,jbusr_jbusl_cbd ,ctu_global_snap );
output [2:0]	j_pack1 ;
output [2:0]	j_pack0 ;
output [56:0]	io_jbi_j_ad ;
output [56:0]	serial_out ;
output [0:0]	spare_jbusr_to_core ;
output [7:0]	io_jbi_j_adtype ;
output [2:0]	io_jbi_j_pack4 ;
output [3:0]	io_jbi_j_adp ;
output [2:0]	io_jbi_j_pack5 ;
output [8:1]	jbusr_jbusl_cbu ;
output [8:1]	jbusr_jbusl_cbd ;
input [56:0]	jbi_io_j_ad ;
input [2:0]	j_pack5 ;
input [2:0]	j_pack4 ;
input [56:0]	serial_in ;
input [1:0]	jbi_io_config_dtl ;
input [7:0]	jbi_io_j_adtype ;
input [1:0]	jbi_io_j_ad_en ;
input [2:0]	jbi_io_j_pack0 ;
input [2:0]	jbi_io_j_pack1 ;
input [0:0]	spare_jbusr_data ;
input [3:0]	jbi_io_j_adp ;
input [0:0]	spare_jbusr_oe ;
inout [3:0]	j_adp ;
inout [7:0]	j_adtype ;
inout [56:0]	j_ad ;
inout [0:0]	spare_jbusr_pin ;
output		bscan_hiz_l_out ;
output		bscan_update_dr_out ;
output		bscan_clock_dr_out ;
output		bscan_shift_dr_out ;
output		bscan_mode_ctl_out ;
output		j_req1_out_l ;
output		ps_select_out ;
output		bypass_enable_out ;
output		j_req0_out_l ;
output		pad_jbusr_sscan_out ;
output		pad_jbusr_so ;
output		pad_jbusr_bso ;
output		j_err ;
output		io_jbi_j_req5_in_l ;
output		io_jbi_j_req4_in_l ;
output		io_jbi_j_par ;
output		io_jbi_j_rst_l ;
input		bscan_clock_dr_in ;
input		jbus_n_ref_res ;
input		j_req4_in_l ;
input		jbus_p_ref_res ;
input		jbi_io_j_req1_out_en ;
input		jbi_io_j_req1_out_l ;
input		ps_select ;
input		bypass_enable ;
input		clk_jbusr_cken ;
input		jbus_gclk ;
input		jbus_grst_l ;
input		jbus_arst_l ;
input		jbus_gdbginit_l ;
input		jbus_adbginit_l ;
input		pad_jbusr_se ;
input		bscan_shift_dr_in ;
input		jbi_io_j_err ;
input		tclk ;
input		pad_jbusr_si ;
input		pad_jbusr_bsi ;
input		vddo ;
input		rst_val_up ;
input		bscan_hiz_l_in ;
input		sel_bypass ;
input		bscan_mode_ctl_in ;
input		bscan_update_dr_in ;
input		rst_val_dn ;
input		rst_io_l ;
input		por_l ;
input		jbi_io_j_adp_en ;
input		jbi_io_j_pack0_en ;
input		jbi_io_j_pack1_en ;
input		jbi_io_j_adtype_en ;
input		hard_rst_l ;
input		jbi_io_j_par_en ;
input		jbi_io_j_req0_out_en ;
input		ctu_io_sscan_update ;
input		jbi_io_j_req0_out_l ;
input		jbi_io_j_par ;
input		pad_jbusr_sscan_in ;
input		ctu_io_sscan_se ;
input		j_req5_in_l ;
input		j_rst_l ;
input		ctu_global_snap ;
inout		dtl_r_vref ;
inout		j_par ;
supply1		vdd ;
supply0		vss ;
 
wire [1:0]	_spare_jbusr_to_core ;
wire [1:0]	config_dtl ;
wire [1:0]	scan_mode0 ;
wire [1:0]	net743 ;
wire [7:0]	net710 ;
wire [1:0]	net697 ;
wire [1:0]	hiz_l3 ;
wire [1:0]	net657 ;
wire [7:0]	net593 ;
wire [7:0]	net595 ;
wire [7:0]	net596 ;
wire [1:0]	clock_dr3 ;
wire [1:0]	net693 ;
wire [7:0]	net594 ;
wire [1:0]	scan_mode4 ;
wire [1:0]	clock_dr_end ;
wire [8:2]	bscan ;
wire [7:0]	net669 ;
wire [7:0]	net0478 ;
wire [8:1]	cbd0 ;
wire [8:1]	cbd1 ;
wire [1:0]	upd_dr3 ;
wire [1:0]	net667 ;
wire [1:0]	shift_dr_end ;
wire [7:0]	net672 ;
wire [7:0]	net670 ;
wire [7:0]	net671 ;
wire [7:0]	net0480 ;
wire [1:0]	net663 ;
wire [1:0]	net867 ;
wire [8:1]	mid2 ;
wire [8:1]	cbu0 ;
wire [7:0]	net872 ;
wire [1:0]	hiz_l_end ;
wire [8:1]	mid0 ;
wire [1:0]	bypass_en_mid ;
wire [1:0]	net863 ;
wire [1:0]	mid5 ;
wire [8:1]	mid1 ;
wire [8:1]	cbu1 ;
wire [8:1]	cbd ;
wire [8:2]	scan ;
wire [1:0]	mid9 ;
wire [1:0]	net579 ;
wire [8:1]	mid3 ;
wire [1:0]	shift_dr4 ;
wire [7:0]	net874 ;
wire [1:0]	net738 ;
wire [8:1]	l1 ;
wire [8:1]	l0 ;
wire [1:0]	net581 ;
wire [1:0]	mid15 ;
wire [1:0]	shift_dr0 ;
wire [1:0]	net734 ;
wire [1:0]	ps_select_end ;
wire [1:0]	l5 ;
wire [8:1]	l3 ;
wire [8:1]	l2 ;
wire [1:0]	l9 ;
wire [7:0]	dnr ;
wire [1:0]	net740 ;
wire [7:0]	net709 ;
wire [8:1]	cbu ;
wire [1:0]	l13 ;
wire [1:0]	net700 ;
wire [7:0]	net707 ;
wire [1:0]	mode_ctl_end ;
wire [1:0]	net585 ;
wire [7:0]	upr ;
wire [1:0]	mid11 ;
wire [1:0]	l17 ;
wire [7:0]	net748 ;
wire [1:0]	hiz_l1 ;
wire [7:0]	net746 ;
wire [1:0]	net591 ;
wire [7:0]	net708 ;
wire [7:0]	net747 ;
wire [7:0]	net745 ;
wire [1:0]	clock_dr1 ;
wire [1:0]	scan_mode2 ;
wire [1:0]	net658 ;
wire [1:0]	hiz_l5 ;
wire [1:0]	net858 ;
wire [1:0]	clock_dr5 ;
wire [1:0]	net660 ;
wire [1:0]	net860 ;
wire [1:0]	upd_dr5 ;
wire [1:0]	net470 ;
wire [1:0]	upd_dr1 ;
wire [1:0]	net664 ;
wire [1:0]	net864 ;
wire [1:0]	net870 ;
wire [1:0]	bypass_en_end ;
wire [1:0]	shift_dr2 ;
wire [1:0]	mid16 ;
wire [1:0]	net582 ;
wire [1:0]	l10 ;
wire [1:0]	l6 ;
wire [1:0]	net701 ;
wire [1:0]	net488 ;
wire [1:0]	net484 ;
wire [1:0]	l18 ;
wire [1:0]	net586 ;
wire [1:0]	mid12 ;
wire [1:0]	net705 ;
wire [1:0]	net490 ;
wire [1:0]	hiz_l2 ;
wire [1:0]	scan_mode1 ;
wire [1:0]	clock_dr2 ;
wire [1:0]	net498 ;
wire [1:0]	net698 ;
wire [1:0]	scan_mode5 ;
wire [1:0]	update_dr_end ;
wire [1:0]	upd_dr4 ;
wire [1:0]	upd_dr0 ;
wire [1:0]	net731 ;
wire [1:0]	net739 ;
wire [1:0]	shift_dr3 ;
wire [1:0]	net735 ;
wire [1:0]	hiz_l0 ;
wire [1:0]	clock_dr0 ;
wire [1:0]	net659 ;
wire [1:0]	hiz_l4 ;
wire [1:0]	clock_dr4 ;
wire [1:0]	net655 ;
wire [1:0]	scan_mode3 ;
wire [1:0]	net661 ;
wire [1:0]	net861 ;
wire [1:0]	upd_dr2 ;
wire [1:0]	net865 ;
wire [1:0]	shift_dr5 ;
wire [1:0]	bypass_en_m ;
wire [1:0]	mid13 ;
wire [1:0]	shift_dr1 ;
wire [1:0]	net502 ;
wire [1:0]	l7 ;
wire [1:0]	net702 ;
wire [1:0]	l11 ;
wire [1:0]	net587 ;
wire [1:0]	l15 ;
wire [1:0]	l19 ;
wire [1:0]	net583 ;
wire [1:0]	net699 ;
wire [1:0]	net695 ;
wire [1:0]	tout ;
wire [1:0]	ps_select_m ;
wire [1:0]	net736 ;
wire [1:0]	net662 ;
wire [1:0]	net862 ;
wire [1:0]	net472 ;
wire [1:0]	net866 ;
wire [1:0]	net482 ;
wire [1:0]	l4 ;
wire [1:0]	mid18 ;
wire [1:0]	l12 ;
wire [1:0]	l8 ;
wire [1:0]	mid10 ;
wire [1:0]	l16 ;
wire [1:0]	net486 ;
wire [1:0]	net588 ;
wire [1:0]	net492 ;
wire [1:0]	net584 ;
wire [1:0]	net696 ;
wire [1:0]	net737 ;
wire [1:0]	ps_select_mid ;
wire [1:0]	net733 ;
wire		clk ;
wire		net402 ;
wire		net0384 ;
wire		deltabitd ;
wire		net396 ;
wire		net0387 ;
wire		net398 ;
wire		sscan ;
wire		deltabitu ;
wire		jbusrsebuf ;
wire		rstiolbuf ;
wire		dbginit_l ;
wire		reset_l ;
wire		pad_jbusr_header_si ;
wire		pad_jbusr_header_so ;
wire		net439 ;
wire		por_l_buf ;
wire		rstvaldnbuf ;
wire		rstvalupbuf ;
wire		net0433 ;
wire		net01028 ;
wire		net01029 ;
wire		se_buf_imp ;
wire		net0390 ;
wire		scan_imp ;
wire		sscan_updatebuf ;
wire		selbypassbuf ;
 
assign	spare_jbusr_to_core[0] = _spare_jbusr_to_core[0] ;
 
bw_u1_buf_15x I225_1_ (
     .z               (shift_dr0[1] ),
     .a               (bscan_shift_dr_in ) );
bw_u1_buf_15x I228 (
     .z               (bscan_mode_ctl_out ),
     .a               (mode_ctl_end[0] ) );
bw_u1_buf_40x I165_6_ (
     .z               (cbu1[6] ),
     .a               (cbu[6] ) );
bw_u1_buf_15x I229 (
     .z               (bscan_update_dr_out ),
     .a               (update_dr_end[0] ) );
bw_u1_buf_40x I166_8_ (
     .z               (cbu0[8] ),
     .a               (cbu[8] ) );
bw_u1_buf_15x I201_0_ (
     .z               (net486[1] ),
     .a               (net484[1] ) );
bw_io_dtl_padx12 I2 (
     .ps_select_buf   ({ps_select_end } ),
     .bypass_en_buf   ({bypass_en_end } ),
     .serial_out      ({serial_out[56:45] } ),
     .serial_in       ({serial_in[56:45] } ),
     .to_core         ({io_jbi_j_ad[56:45] } ),
     .pad             ({j_ad[56:45] } ),
     .por_l_buf       ({net866[0] ,net866[1] } ),
     .oe_buf          ({net867[0] ,net867[1] } ),
     .reset_l_buf     ({net865[0] ,net865[1] } ),
     .update_dr_buf   ({update_dr_end } ),
     .cbu1            ({net872[0] ,net872[1] ,net872[2] ,net872[3] ,
            net872[4] ,net872[5] ,net872[6] ,net872[7] } ),
     .cbd1            ({net874[0] ,net874[1] ,net874[2] ,net874[3] ,
            net874[4] ,net874[5] ,net874[6] ,net874[7] } ),
     .up_open_buf     ({net858[0] ,net858[1] } ),
     .mode_ctl_buf    ({mode_ctl_end } ),
     .se_buf          ({net861[0] ,net861[1] } ),
     .shift_dr_buf    ({shift_dr_end } ),
     .hiz_l_buf       ({hiz_l_end } ),
     .rst_val_dn_buf  ({net863[0] ,net863[1] } ),
     .down_25_buf     ({net870[0] ,net870[1] } ),
     .data            ({jbi_io_j_ad[56:45] } ),
     .clock_dr_buf    ({clock_dr_end } ),
     .rst_val_up_buf  ({net862[0] ,net862[1] } ),
     .sel_bypass_buf  ({net860[0] ,net860[1] } ),
     .cbu0            ({net0480[0] ,net0480[1] ,net0480[2] ,net0480[3] ,
            net0480[4] ,net0480[5] ,net0480[6] ,net0480[7] } ),
     .cbd0            ({net0478[0] ,net0478[1] ,net0478[2] ,net0478[3] ,
            net0478[4] ,net0478[5] ,net0478[6] ,net0478[7] } ),
     .rst_io_l_buf    ({net864[0] ,net864[1] } ),
     .bso             (bscan[8] ),
     .so              (scan[8] ),
     .bsr_si          (pad_jbusr_bsi ),
     .si              (pad_jbusr_header_so ),
     .clk             (clk ),
     .vddo            (vddo ),
     .ref             (dtl_r_vref ) );
bw_io_dtl_padx12 I61 (
     .ps_select_buf   ({net482[0] ,net482[1] } ),
     .bypass_en_buf   ({net484[0] ,net484[1] } ),
     .serial_out      ({serial_out[19:8] } ),
     .serial_in       ({serial_in[19:8] } ),
     .to_core         ({io_jbi_j_ad[19:8] } ),
     .pad             ({j_ad[19:8] } ),
     .por_l_buf       ({net587[0] ,net587[1] } ),
     .oe_buf          ({net588[0] ,net588[1] } ),
     .reset_l_buf     ({net586[0] ,net586[1] } ),
     .update_dr_buf   ({upd_dr2 } ),
     .cbu1            ({net593[0] ,net593[1] ,net593[2] ,net593[3] ,
            net593[4] ,net593[5] ,net593[6] ,net593[7] } ),
     .cbd1            ({net595[0] ,net595[1] ,net595[2] ,net595[3] ,
            net595[4] ,net595[5] ,net595[6] ,net595[7] } ),
     .up_open_buf     ({net579[0] ,net579[1] } ),
     .mode_ctl_buf    ({scan_mode2 } ),
     .se_buf          ({net582[0] ,net582[1] } ),
     .shift_dr_buf    ({shift_dr2 } ),
     .hiz_l_buf       ({hiz_l2 } ),
     .rst_val_dn_buf  ({net584[0] ,net584[1] } ),
     .down_25_buf     ({net591[0] ,net591[1] } ),
     .data            ({jbi_io_j_ad[19:8] } ),
     .clock_dr_buf    ({clock_dr2 } ),
     .rst_val_up_buf  ({net583[0] ,net583[1] } ),
     .sel_bypass_buf  ({net581[0] ,net581[1] } ),
     .cbu0            ({net594[0] ,net594[1] ,net594[2] ,net594[3] ,
            net594[4] ,net594[5] ,net594[6] ,net594[7] } ),
     .cbd0            ({net596[0] ,net596[1] ,net596[2] ,net596[3] ,
            net596[4] ,net596[5] ,net596[6] ,net596[7] } ),
     .rst_io_l_buf    ({net585[0] ,net585[1] } ),
     .bso             (bscan[3] ),
     .so              (scan[3] ),
     .bsr_si          (bscan[4] ),
     .si              (scan[4] ),
     .clk             (clk ),
     .vddo            (vddo ),
     .ref             (dtl_r_vref ) );
bw_u1_buf_15x I205_0_ (
     .z               (bypass_en_end[0] ),
     .a               (net492[1] ) );
bw_u1_buf_15x I230 (
     .z               (bscan_clock_dr_out ),
     .a               (clock_dr_end[0] ) );
bw_io_dtl_rpt I3 (
     .out18           ({net858[0] ,net858[1] } ),
     .in7             ({l7 } ),
     .in0             ({l0 } ),
     .out16           ({net860[0] ,net860[1] } ),
     .in3             ({l3 } ),
     .in2             ({l2 } ),
     .in6             ({l6 } ),
     .out19           ({update_dr_end } ),
     .in8             ({l8 } ),
     .in9             ({l9 } ),
     .out15           ({net861[0] ,net861[1] } ),
     .out17           ({shift_dr_end } ),
     .in1             ({l1 } ),
     .in4             ({l4 } ),
     .in5             ({l5 } ),
     .out13           ({net862[0] ,net862[1] } ),
     .in10            ({l10 } ),
     .in11            ({l11 } ),
     .in12            ({l12 } ),
     .in13            ({l13 } ),
     .in19            ({l19 } ),
     .in18            ({l18 } ),
     .in17            ({l17 } ),
     .in16            ({l16 } ),
     .in15            ({l15 } ),
     .out6            ({hiz_l_end } ),
     .out7            ({mode_ctl_end } ),
     .out8            ({net867[0] ,net867[1] } ),
     .out9            ({net866[0] ,net866[1] } ),
     .out10           ({net865[0] ,net865[1] } ),
     .out11           ({net864[0] ,net864[1] } ),
     .out12           ({net863[0] ,net863[1] } ),
     .out0            ({net0478[0] ,net0478[1] ,net0478[2] ,net0478[3] ,
            net0478[4] ,net0478[5] ,net0478[6] ,net0478[7] } ),
     .out1            ({net874[0] ,net874[1] ,net874[2] ,net874[3] ,
            net874[4] ,net874[5] ,net874[6] ,net874[7] } ),
     .out2            ({net0480[0] ,net0480[1] ,net0480[2] ,net0480[3] ,
            net0480[4] ,net0480[5] ,net0480[6] ,net0480[7] } ),
     .out3            ({net872[0] ,net872[1] ,net872[2] ,net872[3] ,
            net872[4] ,net872[5] ,net872[6] ,net872[7] } ),
     .out4            ({clock_dr_end } ),
     .out5            ({net870[0] ,net870[1] } ) );
bw_u1_buf_15x I209_0_ (
     .z               (net490[1] ),
     .a               (ps_select_m[0] ) );
bw_u1_buf_15x I231 (
     .z               (bscan_shift_dr_out ),
     .a               (shift_dr_end[0] ) );
bw_u1_buf_30x I149_5_ (
     .z               (cbd1[5] ),
     .a               (cbd[5] ) );
bw_u1_buf_30x I148_3_ (
     .z               (cbd0[3] ),
     .a               (cbd[3] ) );
bw_io_dtl_rpt I63 (
     .out18           ({net655[0] ,net655[1] } ),
     .in7             ({scan_mode1 } ),
     .in0             ({net596[0] ,net596[1] ,net596[2] ,net596[3] ,
            net596[4] ,net596[5] ,net596[6] ,net596[7] } ),
     .out16           ({net657[0] ,net657[1] } ),
     .in3             ({net593[0] ,net593[1] ,net593[2] ,net593[3] ,
            net593[4] ,net593[5] ,net593[6] ,net593[7] } ),
     .in2             ({net594[0] ,net594[1] ,net594[2] ,net594[3] ,
            net594[4] ,net594[5] ,net594[6] ,net594[7] } ),
     .in6             ({hiz_l1 } ),
     .out19           ({upd_dr2 } ),
     .in8             ({net588[0] ,net588[1] } ),
     .in9             ({net587[0] ,net587[1] } ),
     .out15           ({net658[0] ,net658[1] } ),
     .out17           ({shift_dr2 } ),
     .in1             ({net595[0] ,net595[1] ,net595[2] ,net595[3] ,
            net595[4] ,net595[5] ,net595[6] ,net595[7] } ),
     .in4             ({clock_dr1 } ),
     .in5             ({net591[0] ,net591[1] } ),
     .out13           ({net659[0] ,net659[1] } ),
     .in10            ({net586[0] ,net586[1] } ),
     .in11            ({net585[0] ,net585[1] } ),
     .in12            ({net584[0] ,net584[1] } ),
     .in13            ({net583[0] ,net583[1] } ),
     .in19            ({upd_dr1 } ),
     .in18            ({net579[0] ,net579[1] } ),
     .in17            ({shift_dr1 } ),
     .in16            ({net581[0] ,net581[1] } ),
     .in15            ({net582[0] ,net582[1] } ),
     .out6            ({hiz_l2 } ),
     .out7            ({scan_mode2 } ),
     .out8            ({net664[0] ,net664[1] } ),
     .out9            ({net663[0] ,net663[1] } ),
     .out10           ({net662[0] ,net662[1] } ),
     .out11           ({net661[0] ,net661[1] } ),
     .out12           ({net660[0] ,net660[1] } ),
     .out0            ({net672[0] ,net672[1] ,net672[2] ,net672[3] ,
            net672[4] ,net672[5] ,net672[6] ,net672[7] } ),
     .out1            ({net671[0] ,net671[1] ,net671[2] ,net671[3] ,
            net671[4] ,net671[5] ,net671[6] ,net671[7] } ),
     .out2            ({net670[0] ,net670[1] ,net670[2] ,net670[3] ,
            net670[4] ,net670[5] ,net670[6] ,net670[7] } ),
     .out3            ({net669[0] ,net669[1] ,net669[2] ,net669[3] ,
            net669[4] ,net669[5] ,net669[6] ,net669[7] } ),
     .out4            ({clock_dr2 } ),
     .out5            ({net667[0] ,net667[1] } ) );
bw_io_dtl_rpt I4 (
     .out18           ({l18 } ),
     .in7             ({scan_mode5 } ),
     .in0             ({cbd0 } ),
     .out16           ({l16 } ),
     .in3             ({cbu1 } ),
     .in2             ({cbu0 } ),
     .in6             ({hiz_l5 } ),
     .out19           ({l19 } ),
     .in8             ({jbi_io_j_ad_en[1] ,jbi_io_j_ad_en[1] } ),
     .in9             ({{2 {por_l_buf }} } ),
     .out15           ({l15 } ),
     .out17           ({l17 } ),
     .in1             ({cbd1 } ),
     .in4             ({clock_dr5 } ),
     .in5             ({config_dtl[1] ,config_dtl[1] } ),
     .out13           ({l13 } ),
     .in10            ({{2 {reset_l }} } ),
     .in11            ({{2 {rstiolbuf }} } ),
     .in12            ({{2 {rstvaldnbuf }} } ),
     .in13            ({{2 {rstvalupbuf }} } ),
     .in19            ({upd_dr5 } ),
     .in18            ({config_dtl[0] ,config_dtl[0] } ),
     .in17            ({shift_dr5 } ),
     .in16            ({{2 {selbypassbuf }} } ),
     .in15            ({{2 {jbusrsebuf }} } ),
     .out6            ({l6 } ),
     .out7            ({l7 } ),
     .out8            ({l8 } ),
     .out9            ({l9 } ),
     .out10           ({l10 } ),
     .out11           ({l11 } ),
     .out12           ({l12 } ),
     .out0            ({l0 } ),
     .out1            ({l1 } ),
     .out2            ({l2 } ),
     .out3            ({l3 } ),
     .out4            ({l4 } ),
     .out5            ({l5 } ) );
bw_io_dtl_padx12 I5 (
     .ps_select_buf   ({net490[0] ,net490[1] } ),
     .bypass_en_buf   ({net492[0] ,net492[1] } ),
     .serial_out      ({serial_out[44:33] } ),
     .serial_in       ({serial_in[44:33] } ),
     .to_core         ({io_jbi_j_ad[44:33] } ),
     .pad             ({j_ad[44:33] } ),
     .por_l_buf       ({l9 } ),
     .oe_buf          ({l8 } ),
     .reset_l_buf     ({l10 } ),
     .update_dr_buf   ({l19 } ),
     .cbu1            ({l3 } ),
     .cbd1            ({l1 } ),
     .up_open_buf     ({l18 } ),
     .mode_ctl_buf    ({l7 } ),
     .se_buf          ({l15 } ),
     .shift_dr_buf    ({l17 } ),
     .hiz_l_buf       ({l6 } ),
     .rst_val_dn_buf  ({l12 } ),
     .down_25_buf     ({l5 } ),
     .data            ({jbi_io_j_ad[44:33] } ),
     .clock_dr_buf    ({l4 } ),
     .rst_val_up_buf  ({l13 } ),
     .sel_bypass_buf  ({l16 } ),
     .cbu0            ({l2 } ),
     .cbd0            ({l0 } ),
     .rst_io_l_buf    ({l11 } ),
     .bso             (bscan[7] ),
     .so              (scan[7] ),
     .bsr_si          (bscan[8] ),
     .si              (scan[8] ),
     .clk             (clk ),
     .vddo            (vddo ),
     .ref             (dtl_r_vref ) );
bw_io_dtl_rpt I64 (
     .out18           ({net693[0] ,net693[1] } ),
     .in7             ({scan_mode0 } ),
     .in0             ({net672[0] ,net672[1] ,net672[2] ,net672[3] ,
            net672[4] ,net672[5] ,net672[6] ,net672[7] } ),
     .out16           ({net695[0] ,net695[1] } ),
     .in3             ({net669[0] ,net669[1] ,net669[2] ,net669[3] ,
            net669[4] ,net669[5] ,net669[6] ,net669[7] } ),
     .in2             ({net670[0] ,net670[1] ,net670[2] ,net670[3] ,
            net670[4] ,net670[5] ,net670[6] ,net670[7] } ),
     .in6             ({hiz_l0 } ),
     .out19           ({upd_dr1 } ),
     .in8             ({{2 {jbi_io_j_adtype_en }} } ),
     .in9             ({net663[0] ,net663[1] } ),
     .out15           ({net696[0] ,net696[1] } ),
     .out17           ({shift_dr1 } ),
     .in1             ({net671[0] ,net671[1] ,net671[2] ,net671[3] ,
            net671[4] ,net671[5] ,net671[6] ,net671[7] } ),
     .in4             ({clock_dr0 } ),
     .in5             ({net667[0] ,net667[1] } ),
     .out13           ({net697[0] ,net697[1] } ),
     .in10            ({net662[0] ,net662[1] } ),
     .in11            ({net661[0] ,net661[1] } ),
     .in12            ({net660[0] ,net660[1] } ),
     .in13            ({net659[0] ,net659[1] } ),
     .in19            ({upd_dr0 } ),
     .in18            ({net655[0] ,net655[1] } ),
     .in17            ({shift_dr0 } ),
     .in16            ({net657[0] ,net657[1] } ),
     .in15            ({net658[0] ,net658[1] } ),
     .out6            ({hiz_l1 } ),
     .out7            ({scan_mode1 } ),
     .out8            ({net702[0] ,net702[1] } ),
     .out9            ({net701[0] ,net701[1] } ),
     .out10           ({net700[0] ,net700[1] } ),
     .out11           ({net699[0] ,net699[1] } ),
     .out12           ({net698[0] ,net698[1] } ),
     .out0            ({net710[0] ,net710[1] ,net710[2] ,net710[3] ,
            net710[4] ,net710[5] ,net710[6] ,net710[7] } ),
     .out1            ({net709[0] ,net709[1] ,net709[2] ,net709[3] ,
            net709[4] ,net709[5] ,net709[6] ,net709[7] } ),
     .out2            ({net708[0] ,net708[1] ,net708[2] ,net708[3] ,
            net708[4] ,net708[5] ,net708[6] ,net708[7] } ),
     .out3            ({net707[0] ,net707[1] ,net707[2] ,net707[3] ,
            net707[4] ,net707[5] ,net707[6] ,net707[7] } ),
     .out4            ({clock_dr1 } ),
     .out5            ({net705[0] ,net705[1] } ) );
bw_u1_buf_15x I211_0_ (
     .z               (ps_select_m[0] ),
     .a               (ps_select_mid[0] ) );
bw_u1_buf_15x I251_1_ (
     .z               (jbusr_jbusl_cbu[1] ),
     .a               (net0480[7] ) );
bw_u1_buf_15x I250_7_ (
     .z               (jbusr_jbusl_cbd[7] ),
     .a               (net0478[1] ) );
bw_u1_buf_15x I225_0_ (
     .z               (shift_dr0[0] ),
     .a               (bscan_shift_dr_in ) );
bw_u1_buf_40x I165_5_ (
     .z               (cbu1[5] ),
     .a               (cbu[5] ) );
bw_clk_cl_jbusr_jbus I69 (
     .cluster_grst_l  (reset_l ),
     .so              (net0433 ),
     .dbginit_l       (dbginit_l ),
     .rclk            (clk ),
     .si              (pad_jbusr_header_si ),
     .se              (jbusrsebuf ),
     .adbginit_l      (jbus_adbginit_l ),
     .gdbginit_l      (jbus_gdbginit_l ),
     .arst_l          (jbus_arst_l ),
     .grst_l          (jbus_grst_l ),
     .cluster_cken    (clk_jbusr_cken ),
     .gclk            (jbus_gclk ) );
bw_u1_buf_40x I166_7_ (
     .z               (cbu0[7] ),
     .a               (cbu[7] ) );
bw_io_dtl_drv I140 (
     .cbu             ({cbu0 } ),
     .cbd             ({cbd0 } ),
     .pad             (dtl_r_vref ),
     .sel_data_n      (vss ),
     .pad_up          (vss ),
     .pad_dn_l        (vdd ),
     .pad_dn25_l      (vdd ),
     .por             (vss ),
     .bsr_up          (vss ),
     .bsr_dn_l        (vdd ),
     .bsr_dn25_l      (vdd ),
     .vddo            (vddo ) );
bw_u1_buf_15x I202_1_ (
     .z               (bypass_en_mid[1] ),
     .a               (net486[0] ) );
bw_u1_buf_30x I148_2_ (
     .z               (cbd0[2] ),
     .a               (cbd[2] ) );
bw_u1_buf_30x I149_4_ (
     .z               (cbd1[4] ),
     .a               (cbd[4] ) );
bw_u1_buf_30x I144 (
     .z               (pad_jbusr_bso ),
     .a               (net0390 ) );
bw_u1_buf_15x I212_1_ (
     .z               (net498[0] ),
     .a               (net470[0] ) );
bw_u1_buf_15x I250_6_ (
     .z               (jbusr_jbusl_cbd[6] ),
     .a               (net0478[2] ) );
bw_u1_buf_30x I243 (
     .z               (pad_jbusr_sscan_out ),
     .a               (net398 ) );
bw_dtl_impctl_pulldown I145 (
     .from_csr        ({vss ,vss ,vss ,vss ,vss ,vss ,vss ,vss } ),
     .z               ({cbd } ),
     .to_csr          ({dnr } ),
     .rclk            (clk ),
     .se              (se_buf_imp ),
     .hard_reset_n    (hard_rst_l ),
     .we_csr          (vss ),
     .ctu_io_sscan_se (ctu_io_sscan_se ),
     .ctu_io_sscan_in (pad_jbusr_sscan_in ),
     .tclk            (tclk ),
     .ctu_global_snap (ctu_global_snap ),
     .so              (net402 ),
     .si              (scan[7] ),
     .io_ctu_sscan_out (sscan ),
     .ctu_io_sscan_update (sscan_updatebuf ),
     .deltabit        (deltabitd ),
     .clk_dis_l       (vdd ),
     .vddo            (vddo ),
     .pad             (jbus_n_ref_res ) );
bw_u1_buf_15x I197_1_ (
     .z               (net482[0] ),
     .a               (net502[0] ) );
bw_u1_buf_15x I216_1_ (
     .z               (net472[0] ),
     .a               (ps_select ) );
bw_u1_buf_15x I251_8_ (
     .z               (jbusr_jbusl_cbu[8] ),
     .a               (net0480[0] ) );
bw_u1_buf_15x I147 (
     .z               (pad_jbusr_header_si ),
     .a               (pad_jbusr_si ) );
bw_u1_buf_15x I226_1_ (
     .z               (upd_dr0[1] ),
     .a               (bscan_update_dr_in ) );
bw_u1_buf_40x I166_6_ (
     .z               (cbu0[6] ),
     .a               (cbu[6] ) );
bw_u1_buf_40x I165_4_ (
     .z               (cbu1[4] ),
     .a               (cbu[4] ) );
bw_u1_buf_20x I249 (
     .z               (pad_jbusr_header_so ),
     .a               (net0433 ) );
bw_u1_buf_15x I202_0_ (
     .z               (bypass_en_mid[0] ),
     .a               (net486[1] ) );
bw_u1_buf_30x I148_1_ (
     .z               (cbd0[1] ),
     .a               (cbd[1] ) );
bw_u1_scanl_2x I152 (
     .so              (net0387 ),
     .sd              (net01028 ),
     .ck              (net0384 ) );
bw_u1_buf_30x I149_3_ (
     .z               (cbd1[3] ),
     .a               (cbd[3] ) );
bw_u1_scanl_2x I153 (
     .so              (net0390 ),
     .sd              (net01029 ),
     .ck              (bscan_clock_dr_in ) );
bw_u1_buf_15x I212_0_ (
     .z               (net498[1] ),
     .a               (net470[1] ) );
bw_u1_buf_15x I253 (
     .z               (por_l_buf ),
     .a               (por_l ) );
bw_u1_buf_15x I252_1_ (
     .z               (config_dtl[1] ),
     .a               (jbi_io_config_dtl[1] ) );
bw_u1_buf_15x I250_5_ (
     .z               (jbusr_jbusl_cbd[5] ),
     .a               (net0478[3] ) );
bw_u1_buf_30x I155 (
     .z               (pad_jbusr_so ),
     .a               (net0387 ) );
bw_u1_buf_15x I197_0_ (
     .z               (net482[1] ),
     .a               (net502[1] ) );
bw_u1_buf_15x I216_0_ (
     .z               (net472[1] ),
     .a               (ps_select ) );
bw_u1_buf_15x I254 (
     .z               (selbypassbuf ),
     .a               (sel_bypass ) );
bw_u1_buf_15x I251_7_ (
     .z               (jbusr_jbusl_cbu[7] ),
     .a               (net0480[1] ) );
bw_u1_buf_15x I255 (
     .z               (rstvalupbuf ),
     .a               (rst_val_up ) );
bw_u1_buf_15x I256 (
     .z               (rstvaldnbuf ),
     .a               (rst_val_dn ) );
bw_u1_buf_15x I88 (
     .z               (bscan_hiz_l_out ),
     .a               (hiz_l_end[0] ) );
bw_u1_buf_15x I257 (
     .z               (rstiolbuf ),
     .a               (rst_io_l ) );
bw_u1_buf_15x I226_0_ (
     .z               (upd_dr0[0] ),
     .a               (bscan_update_dr_in ) );
bw_u1_buf_15x I258 (
     .z               (sscan_updatebuf ),
     .a               (ctu_io_sscan_update ) );
bw_u1_buf_40x I166_5_ (
     .z               (cbu0[5] ),
     .a               (cbu[5] ) );
bw_u1_buf_40x I165_3_ (
     .z               (cbu1[3] ),
     .a               (cbu[3] ) );
bw_u1_buf_15x I259 (
     .z               (jbusrsebuf ),
     .a               (pad_jbusr_se ) );
bw_u1_buf_15x I203_1_ (
     .z               (ps_select_mid[1] ),
     .a               (net488[0] ) );
bw_u1_buf_30x I149_2_ (
     .z               (cbd1[2] ),
     .a               (cbd[2] ) );
bw_dtl_impctl_pullup I162 (
     .from_csr        ({vss ,vss ,vss ,vss ,vss ,vss ,vss ,vss } ),
     .z               ({cbu } ),
     .to_csr          ({upr } ),
     .rclk            (clk ),
     .ctu_io_sscan_update (sscan_updatebuf ),
     .ctu_global_snap (ctu_global_snap ),
     .tclk            (tclk ),
     .ctu_io_sscan_se (ctu_io_sscan_se ),
     .si              (net439 ),
     .we_csr          (vss ),
     .se              (se_buf_imp ),
     .ctu_io_sscan_in (sscan ),
     .hard_reset_n    (hard_rst_l ),
     .clk_dis_l       (vdd ),
     .vddo            (vddo ),
     .so_l            (net396 ),
     .imped_shadow_so (net398 ),
     .deltabit        (deltabitu ),
     .pad             (jbus_p_ref_res ) );
bw_u1_ckbuf_1p5x I260 (
     .clk             (net0384 ),
     .rclk            (clk ) );
bw_u1_buf_30x I148_8_ (
     .z               (cbd0[8] ),
     .a               (cbd[8] ) );
bw_u1_buf_15x I213_1_ (
     .z               (net502[0] ),
     .a               (net472[0] ) );
bw_u1_buf_15x I252_0_ (
     .z               (config_dtl[0] ),
     .a               (jbi_io_config_dtl[0] ) );
bw_u1_buf_15x I251_6_ (
     .z               (jbusr_jbusl_cbu[6] ),
     .a               (net0480[2] ) );
bw_u1_buf_15x I250_4_ (
     .z               (jbusr_jbusl_cbd[4] ),
     .a               (net0478[4] ) );
bw_u1_buf_15x I198_1_ (
     .z               (net484[0] ),
     .a               (net498[0] ) );
bw_u1_buf_15x I217_1_ (
     .z               (net470[0] ),
     .a               (bypass_enable ) );
bw_io_dtl_rpt I17 (
     .out18           ({mid18 } ),
     .in7             ({scan_mode4 } ),
     .in0             ({cbd0 } ),
     .out16           ({mid16 } ),
     .in3             ({cbu1 } ),
     .in2             ({cbu0 } ),
     .in6             ({hiz_l4 } ),
     .out19           ({upd_dr5 } ),
     .in8             ({vss ,vss } ),
     .in9             ({{2 {por_l_buf }} } ),
     .out15           ({mid15 } ),
     .out17           ({shift_dr5 } ),
     .in1             ({cbd1 } ),
     .in4             ({clock_dr4 } ),
     .in5             ({config_dtl[1] ,config_dtl[1] } ),
     .out13           ({mid13 } ),
     .in10            ({{2 {reset_l }} } ),
     .in11            ({{2 {rstiolbuf }} } ),
     .in12            ({{2 {rstvaldnbuf }} } ),
     .in13            ({{2 {rstvalupbuf }} } ),
     .in19            ({upd_dr4 } ),
     .in18            ({config_dtl[0] ,config_dtl[0] } ),
     .in17            ({shift_dr4 } ),
     .in16            ({{2 {selbypassbuf }} } ),
     .in15            ({{2 {jbusrsebuf }} } ),
     .out6            ({hiz_l5 } ),
     .out7            ({scan_mode5 } ),
     .out8            ({tout } ),
     .out9            ({mid9 } ),
     .out10           ({mid10 } ),
     .out11           ({mid11 } ),
     .out12           ({mid12 } ),
     .out0            ({mid0 } ),
     .out1            ({mid1 } ),
     .out2            ({mid2 } ),
     .out3            ({mid3 } ),
     .out4            ({clock_dr5 } ),
     .out5            ({mid5 } ) );
bw_u1_buf_15x I223_1_ (
     .z               (clock_dr0[1] ),
     .a               (bscan_clock_dr_in ) );
bw_u1_buf_40x I165_2_ (
     .z               (cbu1[2] ),
     .a               (cbu[2] ) );
bw_u1_buf_15x I227_1_ (
     .z               (scan_mode0[1] ),
     .a               (bscan_mode_ctl_in ) );
bw_u1_buf_40x I166_4_ (
     .z               (cbu0[4] ),
     .a               (cbu[4] ) );
bw_u1_buf_15x I203_0_ (
     .z               (ps_select_mid[0] ),
     .a               (net488[1] ) );
bw_u1_buf_30x I171 (
     .z               (se_buf_imp ),
     .a               (jbusrsebuf ) );
bw_io_dtl_rpt I20 (
     .out18           ({net731[0] ,net731[1] } ),
     .in7             ({scan_mode3 } ),
     .in0             ({mid0 } ),
     .out16           ({net733[0] ,net733[1] } ),
     .in3             ({mid3 } ),
     .in2             ({mid2 } ),
     .in6             ({hiz_l3 } ),
     .out19           ({upd_dr4 } ),
     .in8             ({jbi_io_j_ad_en[0] ,jbi_io_j_ad_en[0] } ),
     .in9             ({mid9 } ),
     .out15           ({net734[0] ,net734[1] } ),
     .out17           ({shift_dr4 } ),
     .in1             ({mid1 } ),
     .in4             ({clock_dr3 } ),
     .in5             ({mid5 } ),
     .out13           ({net735[0] ,net735[1] } ),
     .in10            ({mid10 } ),
     .in11            ({mid11 } ),
     .in12            ({mid12 } ),
     .in13            ({mid13 } ),
     .in19            ({upd_dr3 } ),
     .in18            ({mid18 } ),
     .in17            ({shift_dr3 } ),
     .in16            ({mid16 } ),
     .in15            ({mid15 } ),
     .out6            ({hiz_l4 } ),
     .out7            ({scan_mode4 } ),
     .out8            ({net740[0] ,net740[1] } ),
     .out9            ({net739[0] ,net739[1] } ),
     .out10           ({net738[0] ,net738[1] } ),
     .out11           ({net737[0] ,net737[1] } ),
     .out12           ({net736[0] ,net736[1] } ),
     .out0            ({net748[0] ,net748[1] ,net748[2] ,net748[3] ,
            net748[4] ,net748[5] ,net748[6] ,net748[7] } ),
     .out1            ({net747[0] ,net747[1] ,net747[2] ,net747[3] ,
            net747[4] ,net747[5] ,net747[6] ,net747[7] } ),
     .out2            ({net746[0] ,net746[1] ,net746[2] ,net746[3] ,
            net746[4] ,net746[5] ,net746[6] ,net746[7] } ),
     .out3            ({net745[0] ,net745[1] ,net745[2] ,net745[3] ,
            net745[4] ,net745[5] ,net745[6] ,net745[7] } ),
     .out4            ({clock_dr4 } ),
     .out5            ({net743[0] ,net743[1] } ) );
bw_u1_buf_30x I149_1_ (
     .z               (cbd1[1] ),
     .a               (cbd[1] ) );
bw_u1_buf_30x I148_7_ (
     .z               (cbd0[7] ),
     .a               (cbd[7] ) );
bw_u1_buf_10x I173 (
     .z               (net439 ),
     .a               (net402 ) );
bw_u1_inv_8x I174 (
     .z               (scan_imp ),
     .a               (net396 ) );
bw_u1_buf_15x I213_0_ (
     .z               (net502[1] ),
     .a               (net472[1] ) );
bw_u1_buf_15x I251_5_ (
     .z               (jbusr_jbusl_cbu[5] ),
     .a               (net0480[3] ) );
bw_u1_buf_15x I250_3_ (
     .z               (jbusr_jbusl_cbd[3] ),
     .a               (net0478[5] ) );
bw_u1_buf_15x I198_0_ (
     .z               (net484[1] ),
     .a               (net498[1] ) );
bw_u1_buf_15x I217_0_ (
     .z               (net470[1] ),
     .a               (bypass_enable ) );
bw_u1_buf_15x I223_0_ (
     .z               (clock_dr0[0] ),
     .a               (bscan_clock_dr_in ) );
bw_u1_buf_40x I165_1_ (
     .z               (cbu1[1] ),
     .a               (cbu[1] ) );
bw_u1_buf_15x I227_0_ (
     .z               (scan_mode0[0] ),
     .a               (bscan_mode_ctl_in ) );
bw_u1_buf_40x I166_3_ (
     .z               (cbu0[3] ),
     .a               (cbu[3] ) );
bw_u1_buf_15x I200_1_ (
     .z               (net488[0] ),
     .a               (net482[0] ) );
bw_u1_buf_15x I204_1_ (
     .z               (ps_select_end[1] ),
     .a               (net490[0] ) );
bw_u1_buf_15x I208_1_ (
     .z               (net492[0] ),
     .a               (bypass_en_m[1] ) );
bw_u1_buf_30x I148_6_ (
     .z               (cbd0[6] ),
     .a               (cbd[6] ) );
bw_u1_buf_30x I149_8_ (
     .z               (cbd1[8] ),
     .a               (cbd[8] ) );
bw_u1_buf_15x I210_1_ (
     .z               (bypass_en_m[1] ),
     .a               (bypass_en_mid[1] ) );
bw_u1_buf_15x I250_2_ (
     .z               (jbusr_jbusl_cbd[2] ),
     .a               (net0478[6] ) );
bw_u1_buf_15x I251_4_ (
     .z               (jbusr_jbusl_cbu[4] ),
     .a               (net0480[4] ) );
bw_zckgatedcap_h I156_2_ (
     .ld              (net0384 ) );
bw_u1_buf_15x I206 (
     .z               (ps_select_out ),
     .a               (ps_select_end[0] ) );
bw_io_dtl_padx12 I37 (
     .ps_select_buf   ({net488[0] ,net488[1] } ),
     .bypass_en_buf   ({net486[0] ,net486[1] } ),
     .serial_out      ({serial_out[31:20] } ),
     .serial_in       ({serial_in[31:20] } ),
     .to_core         ({io_jbi_j_ad[31:20] } ),
     .pad             ({j_ad[31:20] } ),
     .por_l_buf       ({net739[0] ,net739[1] } ),
     .oe_buf          ({net740[0] ,net740[1] } ),
     .reset_l_buf     ({net738[0] ,net738[1] } ),
     .update_dr_buf   ({upd_dr3 } ),
     .cbu1            ({net745[0] ,net745[1] ,net745[2] ,net745[3] ,
            net745[4] ,net745[5] ,net745[6] ,net745[7] } ),
     .cbd1            ({net747[0] ,net747[1] ,net747[2] ,net747[3] ,
            net747[4] ,net747[5] ,net747[6] ,net747[7] } ),
     .up_open_buf     ({net731[0] ,net731[1] } ),
     .mode_ctl_buf    ({scan_mode3 } ),
     .se_buf          ({net734[0] ,net734[1] } ),
     .shift_dr_buf    ({shift_dr3 } ),
     .hiz_l_buf       ({hiz_l3 } ),
     .rst_val_dn_buf  ({net736[0] ,net736[1] } ),
     .down_25_buf     ({net743[0] ,net743[1] } ),
     .data            ({jbi_io_j_ad[31:20] } ),
     .clock_dr_buf    ({clock_dr3 } ),
     .rst_val_up_buf  ({net735[0] ,net735[1] } ),
     .sel_bypass_buf  ({net733[0] ,net733[1] } ),
     .cbu0            ({net746[0] ,net746[1] ,net746[2] ,net746[3] ,
            net746[4] ,net746[5] ,net746[6] ,net746[7] } ),
     .cbd0            ({net748[0] ,net748[1] ,net748[2] ,net748[3] ,
            net748[4] ,net748[5] ,net748[6] ,net748[7] } ),
     .rst_io_l_buf    ({net737[0] ,net737[1] } ),
     .bso             (bscan[4] ),
     .so              (scan[4] ),
     .bsr_si          (bscan[5] ),
     .si              (scan[5] ),
     .clk             (clk ),
     .vddo            (vddo ),
     .ref             (dtl_r_vref ) );
bw_u1_buf_15x I224_1_ (
     .z               (hiz_l0[1] ),
     .a               (bscan_hiz_l_in ) );
bw_u1_buf_40x I166_2_ (
     .z               (cbu0[2] ),
     .a               (cbu[2] ) );
bw_io_dtl_pad_r3 I38 (
     .cbu0            ({cbu0 } ),
     .cbu1            ({cbu1 } ),
     .spare_out       ({_spare_jbusr_to_core } ),
     .down_25_buf     ({config_dtl[1] ,config_dtl[1] } ),
     .cbd0            ({cbd0 } ),
     .cbd1            ({cbd1 } ),
     .spare_in        ({spare_jbusr_data[0] } ),
     .por_l_buf       ({{2 {por_l_buf }} } ),
     .rst_io_l_buf    ({{2 {rstiolbuf }} } ),
     .shift_dr_buf    ({shift_dr5 } ),
     .hiz_l_buf       ({hiz_l5 } ),
     .rst_val_dn_buf  ({{2 {rstvaldnbuf }} } ),
     .update_dr_buf   ({upd_dr5 } ),
     .spare_en        ({spare_jbusr_oe[0] } ),
     .se_buf          ({{2 {jbusrsebuf }} } ),
     .up_open_buf     ({config_dtl[0] ,config_dtl[0] } ),
     .mode_ctl_buf    ({scan_mode5 } ),
     .rst_val_up_buf  ({{2 {rstvalupbuf }} } ),
     .reset_l_buf     ({{2 {reset_l }} } ),
     .clock_dr_buf    ({clock_dr5 } ),
     .spare           ({j_req1_out_l ,spare_jbusr_pin[0] } ),
     .sel_bypass_buf  ({{2 {selbypassbuf }} } ),
     .j_ad            (j_ad[32] ),
     .req1_oe         (jbi_io_j_req1_out_en ),
     .j_rst_l         (j_rst_l ),
     .j_req1_i        (jbi_io_j_req1_out_l ),
     .j_par_data      (jbi_io_j_par ),
     .serial_in       (serial_in[32] ),
     .j_par_en        (jbi_io_j_par_en ),
     .serial_out      (serial_out[32] ),
     .ps_select       (ps_select_m[0] ),
     .bypass_enable   (bypass_en_m[0] ),
     .bso             (bscan[6] ),
     .j_err_i         (jbi_io_j_err ),
     .jad32           (io_jbi_j_ad[32] ),
     .jpar_o          (io_jbi_j_par ),
     .j_rst_l_o       (io_jbi_j_rst_l ),
     .so              (scan[6] ),
     .j_req5          (j_req5_in_l ),
     .req5_l          (io_jbi_j_req5_in_l ),
     .j_req0          (j_req0_out_l ),
     .j_err           (j_err ),
     .j_req4          (j_req4_in_l ),
     .jpar            (j_par ),
     .j_req0_i        (jbi_io_j_req0_out_l ),
     .j_req0_en       (jbi_io_j_req0_out_en ),
     .vddo            (vddo ),
     .bsr_si          (bscan[7] ),
     .ref             (dtl_r_vref ),
     .req4_l          (io_jbi_j_req4_in_l ),
     .jad32_en        (jbi_io_j_ad_en[1] ),
     .jad32_data      (jbi_io_j_ad[32] ),
     .si              (scan_imp ),
     .clk             (clk ) );
bw_u1_buf_40x I165_8_ (
     .z               (cbu1[8] ),
     .a               (cbu[8] ) );
bw_io_dtl_pad_pack12 I39 (
     .se_buf          ({mid15 } ),
     .up_open_buf     ({mid18 } ),
     .down_25_buf     ({mid5 } ),
     .cbu1            ({mid3 } ),
     .cbu0            ({mid2 } ),
     .cbd0            ({mid0 } ),
     .j_pack1         ({jbi_io_j_pack1 } ),
     .rst_val_up_buf  ({mid13 } ),
     .j_pack0         ({jbi_io_j_pack0 } ),
     .jpack5          ({j_pack5 } ),
     .rst_val_dn_buf  ({mid12 } ),
     .pack5           ({io_jbi_j_pack5 } ),
     .pack4           ({io_jbi_j_pack4 } ),
     .update_dr_buf   ({upd_dr4 } ),
     .por_l_buf       ({mid9 } ),
     .rst_io_l_buf    ({mid11 } ),
     .hiz_l_buf       ({hiz_l4 } ),
     .reset_l_buf     ({mid10 } ),
     .sel_bypass_buf  ({mid16 } ),
     .clock_dr_buf    ({clock_dr4 } ),
     .cbd1            ({mid1 } ),
     .mode_ctl_buf    ({scan_mode4 } ),
     .jpack4          ({j_pack4 } ),
     .jpack1          ({j_pack1 } ),
     .jpack0          ({j_pack0 } ),
     .shift_dr_buf    ({shift_dr4 } ),
     .ref             (dtl_r_vref ),
     .si              (scan[6] ),
     .clk             (clk ),
     .vddo            (vddo ),
     .pack0_en        (jbi_io_j_pack0_en ),
     .pack1_en        (jbi_io_j_pack1_en ),
     .bsr_si          (bscan[6] ),
     .so              (scan[5] ),
     .bso             (bscan[5] ) );
bw_u1_buf_15x I200_0_ (
     .z               (net488[1] ),
     .a               (net482[1] ) );
bw_u1_buf_15x I204_0_ (
     .z               (ps_select_end[0] ),
     .a               (net490[1] ) );
bw_io_dtl_padx8 I40 (
     .update_dr_buf   ({upd_dr0 } ),
     .por_l_buf       ({net701[0] ,net701[1] } ),
     .shift_dr_buf    ({shift_dr0 } ),
     .rst_io_l_buf    ({net699[0] ,net699[1] } ),
     .reset_l_buf     ({net700[0] ,net700[1] } ),
     .mode_ctl_buf    ({scan_mode0 } ),
     .sel_bypass_buf  ({net695[0] ,net695[1] } ),
     .clock_dr_buf    ({clock_dr0 } ),
     .rst_val_up_buf  ({net697[0] ,net697[1] } ),
     .se_buf          ({net696[0] ,net696[1] } ),
     .oe_buf          ({net702[0] ,net702[1] } ),
     .up_open_buf     ({net693[0] ,net693[1] } ),
     .down_25_buf     ({net705[0] ,net705[1] } ),
     .cbu0            ({net708[0] ,net708[1] ,net708[2] ,net708[3] ,
            net708[4] ,net708[5] ,net708[6] ,net708[7] } ),
     .cbd0            ({net710[0] ,net710[1] ,net710[2] ,net710[3] ,
            net710[4] ,net710[5] ,net710[6] ,net710[7] } ),
     .data            ({jbi_io_j_adtype } ),
     .cbd1            ({net709[0] ,net709[1] ,net709[2] ,net709[3] ,
            net709[4] ,net709[5] ,net709[6] ,net709[7] } ),
     .cbu1            ({net707[0] ,net707[1] ,net707[2] ,net707[3] ,
            net707[4] ,net707[5] ,net707[6] ,net707[7] } ),
     .hiz_l_buf       ({hiz_l0 } ),
     .rst_val_dn_buf  ({net698[0] ,net698[1] } ),
     .pad             ({j_adtype } ),
     .to_core         ({io_jbi_j_adtype } ),
     .clk             (clk ),
     .vddo            (vddo ),
     .si              (scan[2] ),
     .bsr_si          (bscan[2] ),
     .ref             (dtl_r_vref ),
     .bso             (net01029 ),
     .so              (net01028 ) );
bw_u1_buf_15x I208_0_ (
     .z               (net492[1] ),
     .a               (bypass_en_m[0] ) );
bw_u1_buf_30x I148_5_ (
     .z               (cbd0[5] ),
     .a               (cbd[5] ) );
bw_io_dtl_pad_adp I41 (
     .serial_in       ({serial_in[7:0] } ),
     .serial_out      ({serial_out[7:0] } ),
     .ps_select_buf   ({net502[0] ,net502[1] } ),
     .bypass_en_buf   ({net498[0] ,net498[1] } ),
     .cbd0            ({net672[0] ,net672[1] ,net672[2] ,net672[3] ,
            net672[4] ,net672[5] ,net672[6] ,net672[7] } ),
     .cbu0            ({net670[0] ,net670[1] ,net670[2] ,net670[3] ,
            net670[4] ,net670[5] ,net670[6] ,net670[7] } ),
     .cbd1            ({net671[0] ,net671[1] ,net671[2] ,net671[3] ,
            net671[4] ,net671[5] ,net671[6] ,net671[7] } ),
     .cbu1            ({net669[0] ,net669[1] ,net669[2] ,net669[3] ,
            net669[4] ,net669[5] ,net669[6] ,net669[7] } ),
     .por_l_buf       ({net663[0] ,net663[1] } ),
     .rst_io_l_buf    ({net661[0] ,net661[1] } ),
     .shift_dr_buf    ({shift_dr1 } ),
     .hiz_l_buf       ({hiz_l1 } ),
     .rst_val_dn_buf  ({net660[0] ,net660[1] } ),
     .update_dr_buf   ({upd_dr1 } ),
     .reset_l_buf     ({net662[0] ,net662[1] } ),
     .mode_ctl_buf    ({scan_mode1 } ),
     .sel_bypass_buf  ({net657[0] ,net657[1] } ),
     .clock_dr_buf    ({clock_dr1 } ),
     .rst_val_up_buf  ({net659[0] ,net659[1] } ),
     .se_buf          ({net658[0] ,net658[1] } ),
     .up_open_buf     ({net655[0] ,net655[1] } ),
     .down_25_buf     ({net667[0] ,net667[1] } ),
     .data            ({jbi_io_j_ad[7:0] } ),
     .oe_buf          ({net664[0] ,net664[1] } ),
     .j_adp           ({jbi_io_j_adp } ),
     .to_core         ({io_jbi_j_ad[7:0] } ),
     .jadpout         ({io_jbi_j_adp } ),
     .pad             ({j_ad[7:0] } ),
     .jadp            ({j_adp } ),
     .vddo            (vddo ),
     .clk             (clk ),
     .ref             (dtl_r_vref ),
     .j_adp_en        (jbi_io_j_adp_en ),
     .si              (scan[3] ),
     .bsr_si          (bscan[3] ),
     .bso             (bscan[2] ),
     .so              (scan[2] ) );
bw_u1_buf_30x I149_7_ (
     .z               (cbd1[7] ),
     .a               (cbd[7] ) );
bw_u1_buf_15x I210_0_ (
     .z               (bypass_en_m[0] ),
     .a               (bypass_en_mid[0] ) );
bw_u1_buf_15x I115 (
     .z               (bypass_enable_out ),
     .a               (bypass_en_end[0] ) );
bw_u1_buf_15x I250_1_ (
     .z               (jbusr_jbusl_cbd[1] ),
     .a               (net0478[7] ) );
bw_u1_buf_15x I251_3_ (
     .z               (jbusr_jbusl_cbu[3] ),
     .a               (net0480[5] ) );
bw_zckgatedcap_h I156_1_ (
     .ld              (net0384 ) );
bw_u1_buf_15x I224_0_ (
     .z               (hiz_l0[0] ),
     .a               (bscan_hiz_l_in ) );
bw_u1_buf_40x I166_1_ (
     .z               (cbu0[1] ),
     .a               (cbu[1] ) );
bw_u1_buf_40x I165_7_ (
     .z               (cbu1[7] ),
     .a               (cbu[7] ) );
bw_u1_buf_15x I201_1_ (
     .z               (net486[0] ),
     .a               (net484[0] ) );
bw_u1_buf_15x I205_1_ (
     .z               (bypass_en_end[1] ),
     .a               (net492[0] ) );
bw_u1_buf_15x I209_1_ (
     .z               (net490[0] ),
     .a               (ps_select_m[1] ) );
bw_u1_buf_30x I149_6_ (
     .z               (cbd1[6] ),
     .a               (cbd[6] ) );
bw_u1_buf_30x I148_4_ (
     .z               (cbd0[4] ),
     .a               (cbd[4] ) );
bw_u1_buf_15x I211_1_ (
     .z               (ps_select_m[1] ),
     .a               (ps_select_mid[1] ) );
bw_u1_buf_15x I251_2_ (
     .z               (jbusr_jbusl_cbu[2] ),
     .a               (net0480[6] ) );
bw_u1_buf_15x I250_8_ (
     .z               (jbusr_jbusl_cbd[8] ),
     .a               (net0478[0] ) );
bw_zckgatedcap_h I156_0_ (
     .ld              (net0384 ) );
bw_io_dtl_rpt I56 (
     .out18           ({net579[0] ,net579[1] } ),
     .in7             ({scan_mode2 } ),
     .in0             ({net748[0] ,net748[1] ,net748[2] ,net748[3] ,
            net748[4] ,net748[5] ,net748[6] ,net748[7] } ),
     .out16           ({net581[0] ,net581[1] } ),
     .in3             ({net745[0] ,net745[1] ,net745[2] ,net745[3] ,
            net745[4] ,net745[5] ,net745[6] ,net745[7] } ),
     .in2             ({net746[0] ,net746[1] ,net746[2] ,net746[3] ,
            net746[4] ,net746[5] ,net746[6] ,net746[7] } ),
     .in6             ({hiz_l2 } ),
     .out19           ({upd_dr3 } ),
     .in8             ({net740[0] ,net740[1] } ),
     .in9             ({net739[0] ,net739[1] } ),
     .out15           ({net582[0] ,net582[1] } ),
     .out17           ({shift_dr3 } ),
     .in1             ({net747[0] ,net747[1] ,net747[2] ,net747[3] ,
            net747[4] ,net747[5] ,net747[6] ,net747[7] } ),
     .in4             ({clock_dr2 } ),
     .in5             ({net743[0] ,net743[1] } ),
     .out13           ({net583[0] ,net583[1] } ),
     .in10            ({net738[0] ,net738[1] } ),
     .in11            ({net737[0] ,net737[1] } ),
     .in12            ({net736[0] ,net736[1] } ),
     .in13            ({net735[0] ,net735[1] } ),
     .in19            ({upd_dr2 } ),
     .in18            ({net731[0] ,net731[1] } ),
     .in17            ({shift_dr2 } ),
     .in16            ({net733[0] ,net733[1] } ),
     .in15            ({net734[0] ,net734[1] } ),
     .out6            ({hiz_l3 } ),
     .out7            ({scan_mode3 } ),
     .out8            ({net588[0] ,net588[1] } ),
     .out9            ({net587[0] ,net587[1] } ),
     .out10           ({net586[0] ,net586[1] } ),
     .out11           ({net585[0] ,net585[1] } ),
     .out12           ({net584[0] ,net584[1] } ),
     .out0            ({net596[0] ,net596[1] ,net596[2] ,net596[3] ,
            net596[4] ,net596[5] ,net596[6] ,net596[7] } ),
     .out1            ({net595[0] ,net595[1] ,net595[2] ,net595[3] ,
            net595[4] ,net595[5] ,net595[6] ,net595[7] } ),
     .out2            ({net594[0] ,net594[1] ,net594[2] ,net594[3] ,
            net594[4] ,net594[5] ,net594[6] ,net594[7] } ),
     .out3            ({net593[0] ,net593[1] ,net593[2] ,net593[3] ,
            net593[4] ,net593[5] ,net593[6] ,net593[7] } ),
     .out4            ({clock_dr3 } ),
     .out5            ({net591[0] ,net591[1] } ) );
endmodule
