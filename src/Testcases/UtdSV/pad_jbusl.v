// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: pad_jbusl.v
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
module pad_jbusl(jbi_io_j_ad_en_chunk56 ,jbi_io_config_dtl_chunk0 ,
     dtl_l_vref ,bscan_hiz_l_out ,bscan_mode_ctl_out ,
     bscan_update_dr_out ,bscan_hiz_l_in ,serial_out ,pad_jbusl_se ,
     jbus_arst_l ,jbus_adbginit_l ,jbi_io_config_dtl ,jbus_gclk ,
     jbus_grst_l ,clk_jbusl_cken ,jbus_gdbginit_l ,bscan_update_dr_in ,
     pad_jbusl_si ,serial_in ,bscan_shift_dr_out ,bscan_clock_dr_out ,
     bscan_mode_ctl_in ,bscan_clock_dr_in ,bypass_enable ,ps_select ,
     bypass_enable_out ,ps_select_out ,j_ad ,jbi_io_j_ad ,pad_jbusl_bso
      ,io_jbi_j_ad ,jbusr_jbusl_cbd ,bscan_shift_dr_in ,jbi_io_j_ad_en ,
     pad_jbusl_bsi ,por_l ,rst_io_l ,rst_val_up ,pad_jbusl_so ,
     rst_val_dn ,vddo ,jbusr_jbusl_cbu ,sel_bypass );
output [127:57]	serial_out ;
output [127:57]	io_jbi_j_ad ;
input [0:0]	jbi_io_config_dtl_chunk0 ;
input [1:0]	jbi_io_config_dtl ;
input [127:57]	serial_in ;
input [127:57]	jbi_io_j_ad ;
input [8:1]	jbusr_jbusl_cbd ;
input [3:2]	jbi_io_j_ad_en ;
input [8:1]	jbusr_jbusl_cbu ;
inout [127:57]	j_ad ;
output		bscan_hiz_l_out ;
output		bscan_mode_ctl_out ;
output		bscan_update_dr_out ;
output		bscan_shift_dr_out ;
output		bscan_clock_dr_out ;
output		bypass_enable_out ;
output		ps_select_out ;
output		pad_jbusl_bso ;
output		pad_jbusl_so ;
input		jbi_io_j_ad_en_chunk56 ;
input		bscan_hiz_l_in ;
input		pad_jbusl_se ;
input		jbus_arst_l ;
input		jbus_adbginit_l ;
input		jbus_gclk ;
input		jbus_grst_l ;
input		clk_jbusl_cken ;
input		jbus_gdbginit_l ;
input		bscan_update_dr_in ;
input		pad_jbusl_si ;
input		bscan_mode_ctl_in ;
input		bscan_clock_dr_in ;
input		bypass_enable ;
input		ps_select ;
input		bscan_shift_dr_in ;
input		pad_jbusl_bsi ;
input		por_l ;
input		rst_io_l ;
input		rst_val_up ;
input		rst_val_dn ;
input		vddo ;
input		sel_bypass ;
inout		dtl_l_vref ;
supply1		vdd ;
supply0		vss ;
 
wire [1:0]	net497 ;
wire [1:0]	net493 ;
wire [1:0]	net453 ;
wire [1:0]	net416 ;
wire [1:0]	net422 ;
wire [1:0]	clock_dr_end ;
wire [7:0]	net467 ;
wire [8:1]	cbd3 ;
wire [7:0]	net465 ;
wire [7:0]	net427 ;
wire [1:0]	rstl2 ;
wire [7:0]	net428 ;
wire [7:0]	net466 ;
wire [7:0]	net464 ;
wire [7:0]	net429 ;
wire [1:0]	net667 ;
wire [1:0]	net463 ;
wire [1:0]	shift_dr_end ;
wire [7:0]	net426 ;
wire [8:1]	mid2 ;
wire [1:0]	net379 ;
wire [1:0]	hiz_l_end ;
wire [8:1]	mid0 ;
wire [1:0]	mid5 ;
wire [8:1]	mid1 ;
wire [1:0]	net375 ;
wire [5:1]	scan ;
wire [1:0]	mid9 ;
wire [1:0]	net273 ;
wire [8:1]	mid3 ;
wire [8:1]	cbu3 ;
wire [1:0]	mid15 ;
wire [7:0]	net682 ;
wire [1:0]	net287 ;
wire [7:0]	net389 ;
wire [1:0]	net500 ;
wire [1:0]	mid19 ;
wire [7:0]	net388 ;
wire [1:0]	net385 ;
wire [7:0]	net505 ;
wire [1:0]	net487 ;
wire [1:0]	net283 ;
wire [7:0]	net391 ;
wire [1:0]	mode_ctl_end ;
wire [7:0]	net503 ;
wire [7:0]	net684 ;
wire [7:0]	net685 ;
wire [1:0]	mid11 ;
wire [7:0]	net390 ;
wire [7:0]	net683 ;
wire [1:0]	net450 ;
wire [1:0]	net412 ;
wire [1:0]	net458 ;
wire [1:0]	rstl4 ;
wire [1:0]	net454 ;
wire [1:0]	net460 ;
wire [1:0]	bypass_en ;
wire [1:0]	rstl0 ;
wire [5:1]	bscan ;
wire [1:0]	net664 ;
wire [1:0]	net670 ;
wire [1:0]	mid7 ;
wire [1:0]	net376 ;
wire [1:0]	bypass_en_end ;
wire [1:0]	net382 ;
wire [1:0]	net576 ;
wire [1:0]	net678 ;
wire [1:0]	net501 ;
wire [1:0]	mid16 ;
wire [1:0]	net674 ;
wire [1:0]	net386 ;
wire [1:0]	net488 ;
wire [1:0]	mid12 ;
wire [1:0]	net490 ;
wire [1:0]	net498 ;
wire [1:0]	rstl3 ;
wire [1:0]	net417 ;
wire [1:0]	net413 ;
wire [1:0]	net494 ;
wire [1:0]	net0234 ;
wire [1:0]	update_dr_end ;
wire [1:0]	net423 ;
wire [1:0]	mid6 ;
wire [1:0]	net451 ;
wire [1:0]	net459 ;
wire [1:0]	net455 ;
wire [1:0]	net461 ;
wire [1:0]	net269 ;
wire [1:0]	rstl1 ;
wire [1:0]	net669 ;
wire [1:0]	net271 ;
wire [1:0]	net671 ;
wire [1:0]	mid4 ;
wire [1:0]	net275 ;
wire [1:0]	net377 ;
wire [1:0]	net281 ;
wire [1:0]	net373 ;
wire [1:0]	net675 ;
wire [1:0]	mid13 ;
wire [1:0]	mid17 ;
wire [1:0]	net285 ;
wire [1:0]	net387 ;
wire [1:0]	net489 ;
wire [1:0]	net383 ;
wire [1:0]	net491 ;
wire [1:0]	net499 ;
wire [1:0]	net418 ;
wire [1:0]	net414 ;
wire [1:0]	net420 ;
wire [1:0]	net424 ;
wire [1:0]	ps_sel ;
wire [1:0]	ps_sel_end ;
wire [1:0]	net0494 ;
wire [1:0]	se_buf_end ;
wire [1:0]	net452 ;
wire [1:0]	net0503 ;
wire [1:0]	net456 ;
wire [1:0]	net462 ;
wire [1:0]	net378 ;
wire [1:0]	net374 ;
wire [1:0]	net380 ;
wire [1:0]	mid18 ;
wire [1:0]	net384 ;
wire [1:0]	net492 ;
wire [1:0]	net411 ;
wire [1:0]	net415 ;
wire [1:0]	net496 ;
wire [1:0]	net421 ;
wire [1:0]	net425 ;
wire [1:0]	net449 ;
wire		clk ;
wire		pad_jbusl_headel_si ;
wire		pad_jbusl_headel_so ;
wire		dbginit_l ;
wire		reset_l ;
wire		net241 ;
wire		net0236 ;
wire		net0237 ;
wire		net0239 ;
wire		net0242 ;
wire		net656 ;
wire		net0682 ;
 
 
bw_io_dtl_rpt I57 (
     .out18           ({net412[0] ,net412[1] } ),
     .in7             ({net498[0] ,net498[1] } ),
     .in0             ({net505[0] ,net505[1] ,net505[2] ,net505[3] ,
            net505[4] ,net505[5] ,net505[6] ,net505[7] } ),
     .out16           ({net414[0] ,net414[1] } ),
     .in3             ({cbu3 } ),
     .in2             ({net503[0] ,net503[1] ,net503[2] ,net503[3] ,
            net503[4] ,net503[5] ,net503[6] ,net503[7] } ),
     .in6             ({net499[0] ,net499[1] } ),
     .out19           ({net411[0] ,net411[1] } ),
     .in8             ({net0503[0] ,net0503[1] } ),
     .in9             ({net496[0] ,net496[1] } ),
     .out15           ({net415[0] ,net415[1] } ),
     .out17           ({net413[0] ,net413[1] } ),
     .in1             ({cbd3 } ),
     .in4             ({net501[0] ,net501[1] } ),
     .in5             ({net500[0] ,net500[1] } ),
     .out13           ({net416[0] ,net416[1] } ),
     .in10            ({rstl0 } ),
     .in11            ({net494[0] ,net494[1] } ),
     .in12            ({net493[0] ,net493[1] } ),
     .in13            ({net492[0] ,net492[1] } ),
     .in19            ({net487[0] ,net487[1] } ),
     .in18            ({net0494[0] ,net0494[1] } ),
     .in17            ({net489[0] ,net489[1] } ),
     .in16            ({net490[0] ,net490[1] } ),
     .in15            ({net491[0] ,net491[1] } ),
     .out6            ({net423[0] ,net423[1] } ),
     .out7            ({net422[0] ,net422[1] } ),
     .out8            ({net421[0] ,net421[1] } ),
     .out9            ({net420[0] ,net420[1] } ),
     .out10           ({rstl1 } ),
     .out11           ({net418[0] ,net418[1] } ),
     .out12           ({net417[0] ,net417[1] } ),
     .out0            ({net429[0] ,net429[1] ,net429[2] ,net429[3] ,
            net429[4] ,net429[5] ,net429[6] ,net429[7] } ),
     .out1            ({net428[0] ,net428[1] ,net428[2] ,net428[3] ,
            net428[4] ,net428[5] ,net428[6] ,net428[7] } ),
     .out2            ({net427[0] ,net427[1] ,net427[2] ,net427[3] ,
            net427[4] ,net427[5] ,net427[6] ,net427[7] } ),
     .out3            ({net426[0] ,net426[1] ,net426[2] ,net426[3] ,
            net426[4] ,net426[5] ,net426[6] ,net426[7] } ),
     .out4            ({net425[0] ,net425[1] } ),
     .out5            ({net424[0] ,net424[1] } ) );
bw_io_dtl_rpt I58 (
     .out18           ({net664[0] ,net664[1] } ),
     .in7             ({net422[0] ,net422[1] } ),
     .in0             ({net429[0] ,net429[1] ,net429[2] ,net429[3] ,
            net429[4] ,net429[5] ,net429[6] ,net429[7] } ),
     .out16           ({net667[0] ,net667[1] } ),
     .in3             ({net426[0] ,net426[1] ,net426[2] ,net426[3] ,
            net426[4] ,net426[5] ,net426[6] ,net426[7] } ),
     .in2             ({net427[0] ,net427[1] ,net427[2] ,net427[3] ,
            net427[4] ,net427[5] ,net427[6] ,net427[7] } ),
     .in6             ({net423[0] ,net423[1] } ),
     .out19           ({update_dr_end } ),
     .in8             ({net421[0] ,net421[1] } ),
     .in9             ({net420[0] ,net420[1] } ),
     .out15           ({se_buf_end } ),
     .out17           ({shift_dr_end } ),
     .in1             ({net428[0] ,net428[1] ,net428[2] ,net428[3] ,
            net428[4] ,net428[5] ,net428[6] ,net428[7] } ),
     .in4             ({net425[0] ,net425[1] } ),
     .in5             ({net424[0] ,net424[1] } ),
     .out13           ({net669[0] ,net669[1] } ),
     .in10            ({net0234[0] ,net0234[1] } ),
     .in11            ({net418[0] ,net418[1] } ),
     .in12            ({net417[0] ,net417[1] } ),
     .in13            ({net416[0] ,net416[1] } ),
     .in19            ({net411[0] ,net411[1] } ),
     .in18            ({net412[0] ,net412[1] } ),
     .in17            ({net413[0] ,net413[1] } ),
     .in16            ({net414[0] ,net414[1] } ),
     .in15            ({net415[0] ,net415[1] } ),
     .out6            ({hiz_l_end } ),
     .out7            ({mode_ctl_end } ),
     .out8            ({net675[0] ,net675[1] } ),
     .out9            ({net674[0] ,net674[1] } ),
     .out10           ({rstl0 } ),
     .out11           ({net671[0] ,net671[1] } ),
     .out12           ({net670[0] ,net670[1] } ),
     .out0            ({net685[0] ,net685[1] ,net685[2] ,net685[3] ,
            net685[4] ,net685[5] ,net685[6] ,net685[7] } ),
     .out1            ({net684[0] ,net684[1] ,net684[2] ,net684[3] ,
            net684[4] ,net684[5] ,net684[6] ,net684[7] } ),
     .out2            ({net683[0] ,net683[1] ,net683[2] ,net683[3] ,
            net683[4] ,net683[5] ,net683[6] ,net683[7] } ),
     .out3            ({net682[0] ,net682[1] ,net682[2] ,net682[3] ,
            net682[4] ,net682[5] ,net682[6] ,net682[7] } ),
     .out4            ({clock_dr_end } ),
     .out5            ({net678[0] ,net678[1] } ) );
bw_io_dtl_padx12 I61 (
     .ps_select_buf   ({ps_sel_end } ),
     .bypass_en_buf   ({bypass_en_end } ),
     .serial_out      ({serial_out[127:116] } ),
     .serial_in       ({serial_in[127:116] } ),
     .to_core         ({io_jbi_j_ad[127:116] } ),
     .pad             ({j_ad[127:116] } ),
     .por_l_buf       ({net674[0] ,net674[1] } ),
     .oe_buf          ({net675[0] ,net675[1] } ),
     .reset_l_buf     ({net0234[0] ,net0234[1] } ),
     .update_dr_buf   ({update_dr_end } ),
     .cbu1            ({net682[0] ,net682[1] ,net682[2] ,net682[3] ,
            net682[4] ,net682[5] ,net682[6] ,net682[7] } ),
     .cbd1            ({net684[0] ,net684[1] ,net684[2] ,net684[3] ,
            net684[4] ,net684[5] ,net684[6] ,net684[7] } ),
     .up_open_buf     ({net664[0] ,net664[1] } ),
     .mode_ctl_buf    ({mode_ctl_end } ),
     .se_buf          ({se_buf_end } ),
     .shift_dr_buf    ({shift_dr_end } ),
     .hiz_l_buf       ({hiz_l_end } ),
     .rst_val_dn_buf  ({net670[0] ,net670[1] } ),
     .down_25_buf     ({net678[0] ,net678[1] } ),
     .data            ({jbi_io_j_ad[127:116] } ),
     .clock_dr_buf    ({clock_dr_end } ),
     .rst_val_up_buf  ({net669[0] ,net669[1] } ),
     .sel_bypass_buf  ({net667[0] ,net667[1] } ),
     .cbu0            ({net683[0] ,net683[1] ,net683[2] ,net683[3] ,
            net683[4] ,net683[5] ,net683[6] ,net683[7] } ),
     .cbd0            ({net685[0] ,net685[1] ,net685[2] ,net685[3] ,
            net685[4] ,net685[5] ,net685[6] ,net685[7] } ),
     .rst_io_l_buf    ({net671[0] ,net671[1] } ),
     .bso             (bscan[5] ),
     .so              (scan[5] ),
     .bsr_si          (pad_jbusl_bsi ),
     .si              (pad_jbusl_headel_so ),
     .clk             (clk ),
     .vddo            (vddo ),
     .ref             (dtl_l_vref ) );
bw_io_dtl_padx12 I63 (
     .ps_select_buf   ({net287[0] ,net287[1] } ),
     .bypass_en_buf   ({net285[0] ,net285[1] } ),
     .serial_out      ({serial_out[115:104] } ),
     .serial_in       ({serial_in[115:104] } ),
     .to_core         ({io_jbi_j_ad[115:104] } ),
     .pad             ({j_ad[115:104] } ),
     .por_l_buf       ({net420[0] ,net420[1] } ),
     .oe_buf          ({net421[0] ,net421[1] } ),
     .reset_l_buf     ({rstl0 } ),
     .update_dr_buf   ({net411[0] ,net411[1] } ),
     .cbu1            ({net426[0] ,net426[1] ,net426[2] ,net426[3] ,
            net426[4] ,net426[5] ,net426[6] ,net426[7] } ),
     .cbd1            ({net428[0] ,net428[1] ,net428[2] ,net428[3] ,
            net428[4] ,net428[5] ,net428[6] ,net428[7] } ),
     .up_open_buf     ({net412[0] ,net412[1] } ),
     .mode_ctl_buf    ({net422[0] ,net422[1] } ),
     .se_buf          ({net415[0] ,net415[1] } ),
     .shift_dr_buf    ({net413[0] ,net413[1] } ),
     .hiz_l_buf       ({net423[0] ,net423[1] } ),
     .rst_val_dn_buf  ({net417[0] ,net417[1] } ),
     .down_25_buf     ({net424[0] ,net424[1] } ),
     .data            ({jbi_io_j_ad[115:104] } ),
     .clock_dr_buf    ({net425[0] ,net425[1] } ),
     .rst_val_up_buf  ({net416[0] ,net416[1] } ),
     .sel_bypass_buf  ({net414[0] ,net414[1] } ),
     .cbu0            ({net427[0] ,net427[1] ,net427[2] ,net427[3] ,
            net427[4] ,net427[5] ,net427[6] ,net427[7] } ),
     .cbd0            ({net429[0] ,net429[1] ,net429[2] ,net429[3] ,
            net429[4] ,net429[5] ,net429[6] ,net429[7] } ),
     .rst_io_l_buf    ({net418[0] ,net418[1] } ),
     .bso             (bscan[4] ),
     .so              (scan[4] ),
     .bsr_si          (bscan[5] ),
     .si              (scan[5] ),
     .clk             (clk ),
     .vddo            (vddo ),
     .ref             (dtl_l_vref ) );
bw_u1_buf_15x I113_0_ (
     .z               (bypass_en_end[0] ),
     .a               (net285[1] ) );
bw_u1_buf_10x I138 (
     .z               (net241 ),
     .a               (se_buf_end[0] ) );
bw_io_dtl_rpt I69 (
     .out18           ({net374[0] ,net374[1] } ),
     .in7             ({{2 {bscan_mode_ctl_in }} } ),
     .in0             ({jbusr_jbusl_cbd } ),
     .out16           ({net376[0] ,net376[1] } ),
     .in3             ({jbusr_jbusl_cbu } ),
     .in2             ({jbusr_jbusl_cbu } ),
     .in6             ({{2 {bscan_hiz_l_in }} } ),
     .out19           ({net373[0] ,net373[1] } ),
     .in8             ({jbi_io_j_ad_en[2] ,jbi_io_j_ad_en[2] } ),
     .in9             ({{2 {por_l }} } ),
     .out15           ({net377[0] ,net377[1] } ),
     .out17           ({net375[0] ,net375[1] } ),
     .in1             ({jbusr_jbusl_cbd } ),
     .in4             ({{2 {bscan_clock_dr_in }} } ),
     .in5             ({jbi_io_config_dtl[1] ,jbi_io_config_dtl[1] } ),
     .out13           ({net378[0] ,net378[1] } ),
     .in10            ({{2 {bypass_enable }} } ),
     .in11            ({{2 {rst_io_l }} } ),
     .in12            ({{2 {rst_val_dn }} } ),
     .in13            ({{2 {rst_val_up }} } ),
     .in19            ({{2 {bscan_update_dr_in }} } ),
     .in18            ({jbi_io_config_dtl[0] ,jbi_io_config_dtl[0] } ),
     .in17            ({{2 {bscan_shift_dr_in }} } ),
     .in16            ({{2 {sel_bypass }} } ),
     .in15            ({{2 {pad_jbusl_se }} } ),
     .out6            ({net385[0] ,net385[1] } ),
     .out7            ({net384[0] ,net384[1] } ),
     .out8            ({net383[0] ,net383[1] } ),
     .out9            ({net382[0] ,net382[1] } ),
     .out10           ({net271[0] ,net271[1] } ),
     .out11           ({net380[0] ,net380[1] } ),
     .out12           ({net379[0] ,net379[1] } ),
     .out0            ({net391[0] ,net391[1] ,net391[2] ,net391[3] ,
            net391[4] ,net391[5] ,net391[6] ,net391[7] } ),
     .out1            ({net390[0] ,net390[1] ,net390[2] ,net390[3] ,
            net390[4] ,net390[5] ,net390[6] ,net390[7] } ),
     .out2            ({net389[0] ,net389[1] ,net389[2] ,net389[3] ,
            net389[4] ,net389[5] ,net389[6] ,net389[7] } ),
     .out3            ({net388[0] ,net388[1] ,net388[2] ,net388[3] ,
            net388[4] ,net388[5] ,net388[6] ,net388[7] } ),
     .out4            ({net387[0] ,net387[1] } ),
     .out5            ({net386[0] ,net386[1] } ) );
bw_u1_buf_15x I100_1_ (
     .z               (net269[0] ),
     .a               (ps_select ) );
bw_io_dtl_drv I140 (
     .cbu             ({cbu3 } ),
     .cbd             ({cbd3 } ),
     .pad             (dtl_l_vref ),
     .sel_data_n      (vss ),
     .pad_up          (vss ),
     .pad_dn_l        (vdd ),
     .pad_dn25_l      (vdd ),
     .por             (vss ),
     .bsr_up          (vss ),
     .bsr_dn_l        (vdd ),
     .bsr_dn25_l      (vdd ),
     .vddo            (vddo ) );
bw_io_dtl_rpt I70 (
     .out18           ({net488[0] ,net488[1] } ),
     .in7             ({mid7 } ),
     .in0             ({mid0 } ),
     .out16           ({net490[0] ,net490[1] } ),
     .in3             ({mid3 } ),
     .in2             ({mid2 } ),
     .in6             ({mid6 } ),
     .out19           ({net487[0] ,net487[1] } ),
     .in8             ({jbi_io_j_ad_en[3] ,jbi_io_j_ad_en[3] } ),
     .in9             ({mid9 } ),
     .out15           ({net491[0] ,net491[1] } ),
     .out17           ({net489[0] ,net489[1] } ),
     .in1             ({mid1 } ),
     .in4             ({mid4 } ),
     .in5             ({mid5 } ),
     .out13           ({net492[0] ,net492[1] } ),
     .in10            ({rstl1 } ),
     .in11            ({mid11 } ),
     .in12            ({mid12 } ),
     .in13            ({mid13 } ),
     .in19            ({mid19 } ),
     .in18            ({mid18 } ),
     .in17            ({mid17 } ),
     .in16            ({mid16 } ),
     .in15            ({mid15 } ),
     .out6            ({net499[0] ,net499[1] } ),
     .out7            ({net498[0] ,net498[1] } ),
     .out8            ({net497[0] ,net497[1] } ),
     .out9            ({net496[0] ,net496[1] } ),
     .out10           ({rstl2 } ),
     .out11           ({net494[0] ,net494[1] } ),
     .out12           ({net493[0] ,net493[1] } ),
     .out0            ({net505[0] ,net505[1] ,net505[2] ,net505[3] ,
            net505[4] ,net505[5] ,net505[6] ,net505[7] } ),
     .out1            ({cbd3 } ),
     .out2            ({net503[0] ,net503[1] ,net503[2] ,net503[3] ,
            net503[4] ,net503[5] ,net503[6] ,net503[7] } ),
     .out3            ({cbu3 } ),
     .out4            ({net501[0] ,net501[1] } ),
     .out5            ({net500[0] ,net500[1] } ) );
bw_u1_buf_15x I104_1_ (
     .z               (net275[0] ),
     .a               (net269[0] ) );
bw_u1_buf_15x I108_1_ (
     .z               (ps_sel[1] ),
     .a               (net275[0] ) );
bw_u1_buf_15x I110_1_ (
     .z               (net283[0] ),
     .a               (ps_sel[1] ) );
bw_u1_buf_30x I144 (
     .z               (pad_jbusl_bso ),
     .a               (net0239 ) );
bw_u1_buf_15x I114_1_ (
     .z               (ps_sel_end[1] ),
     .a               (net287[0] ) );
bw_u1_buf_15x I147 (
     .z               (pad_jbusl_headel_si ),
     .a               (pad_jbusl_si ) );
bw_u1_buf_15x I100_0_ (
     .z               (net269[1] ),
     .a               (ps_select ) );
bw_u1_buf_20x I150 (
     .z               (pad_jbusl_headel_so ),
     .a               (net0237 ) );
bw_u1_buf_15x I104_0_ (
     .z               (net275[1] ),
     .a               (net269[1] ) );
bw_clk_cl_jbusl_jbus I80 (
     .cluster_grst_l  (reset_l ),
     .so              (net0237 ),
     .dbginit_l       (dbginit_l ),
     .si              (pad_jbusl_headel_si ),
     .se              (net241 ),
     .adbginit_l      (jbus_adbginit_l ),
     .gdbginit_l      (jbus_gdbginit_l ),
     .arst_l          (jbus_arst_l ),
     .grst_l          (jbus_grst_l ),
     .cluster_cken    (clk_jbusl_cken ),
     .gclk            (jbus_gclk ),
     .rclk            (clk ) );
bw_u1_buf_15x I108_0_ (
     .z               (ps_sel[0] ),
     .a               (net275[1] ) );
bw_u1_buf_10x I148_1_ (
     .z               (net0503[0] ),
     .a               (jbi_io_j_ad_en_chunk56 ) );
bw_u1_scanl_2x I152 (
     .so              (net0242 ),
     .sd              (net0682 ),
     .ck              (net0236 ) );
bw_u1_scanl_2x I153 (
     .so              (net0239 ),
     .sd              (net656 ),
     .ck              (bscan_clock_dr_in ) );
bw_u1_buf_15x I110_0_ (
     .z               (net283[1] ),
     .a               (ps_sel[0] ) );
bw_u1_ckbuf_1p5x I154 (
     .clk             (net0236 ),
     .rclk            (clk ) );
bw_u1_buf_15x I114_0_ (
     .z               (ps_sel_end[0] ),
     .a               (net287[1] ) );
bw_u1_buf_30x I155 (
     .z               (pad_jbusl_so ),
     .a               (net0242 ) );
bw_u1_buf_15x I88 (
     .z               (bscan_hiz_l_out ),
     .a               (hiz_l_end[0] ) );
bw_u1_buf_15x I105_1_ (
     .z               (net273[0] ),
     .a               (net271[0] ) );
bw_u1_buf_15x I109_1_ (
     .z               (net281[0] ),
     .a               (bypass_en[1] ) );
bw_u1_buf_15x I91 (
     .z               (bscan_mode_ctl_out ),
     .a               (mode_ctl_end[0] ) );
bw_u1_buf_10x I148_0_ (
     .z               (net0503[1] ),
     .a               (jbi_io_j_ad_en_chunk56 ) );
bw_u1_buf_15x I111_1_ (
     .z               (net285[0] ),
     .a               (net281[0] ) );
bw_u1_buf_15x I93 (
     .z               (bscan_update_dr_out ),
     .a               (update_dr_end[0] ) );
bw_u1_buf_15x I95 (
     .z               (bscan_clock_dr_out ),
     .a               (clock_dr_end[0] ) );
bw_u1_buf_15x I97 (
     .z               (bscan_shift_dr_out ),
     .a               (shift_dr_end[0] ) );
bw_u1_buf_15x I105_0_ (
     .z               (net273[1] ),
     .a               (net271[1] ) );
bw_u1_buf_15x I109_0_ (
     .z               (net281[1] ),
     .a               (bypass_en[0] ) );
bw_u1_buf_10x I149_1_ (
     .z               (net0494[0] ),
     .a               (jbi_io_config_dtl_chunk0[0] ) );
bw_u1_buf_15x I111_0_ (
     .z               (net285[1] ),
     .a               (net281[1] ) );
bw_u1_buf_20x I151_1_ (
     .z               (net0234[0] ),
     .a               (reset_l ) );
bw_u1_buf_15x I106_1_ (
     .z               (bypass_en[1] ),
     .a               (net273[0] ) );
bw_u1_buf_10x I149_0_ (
     .z               (net0494[1] ),
     .a               (jbi_io_config_dtl_chunk0[0] ) );
bw_u1_buf_15x I112_1_ (
     .z               (net287[0] ),
     .a               (net283[0] ) );
bw_u1_buf_20x I151_0_ (
     .z               (net0234[1] ),
     .a               (reset_l ) );
bw_zckgatedcap_h I156_2_ (
     .ld              (net0236 ) );
bw_io_dtl_padx11 I38 (
     .serial_in       ({serial_in[103:93] } ),
     .serial_out      ({serial_out[103:93] } ),
     .ps_select_buf   ({net283[0] ,net283[1] } ),
     .bypass_en_buf   ({net281[0] ,net281[1] } ),
     .oe_buf          ({net497[0] ,net497[1] } ),
     .cbu0            ({net503[0] ,net503[1] ,net503[2] ,net503[3] ,
            net503[4] ,net503[5] ,net503[6] ,net503[7] } ),
     .cbd0            ({net505[0] ,net505[1] ,net505[2] ,net505[3] ,
            net505[4] ,net505[5] ,net505[6] ,net505[7] } ),
     .data            ({jbi_io_j_ad[103:93] } ),
     .cbd1            ({cbd3 } ),
     .cbu1            ({cbu3 } ),
     .pad             ({j_ad[103:93] } ),
     .to_core         ({io_jbi_j_ad[103:93] } ),
     .rst_val_dn_buf  ({net493[0] ,net493[1] } ),
     .hiz_l_buf       ({net499[0] ,net499[1] } ),
     .down_25_buf     ({net500[0] ,net500[1] } ),
     .up_open_buf     ({net488[0] ,net488[1] } ),
     .se_buf          ({net491[0] ,net491[1] } ),
     .rst_val_up_buf  ({net492[0] ,net492[1] } ),
     .clock_dr_buf    ({net501[0] ,net501[1] } ),
     .sel_bypass_buf  ({net490[0] ,net490[1] } ),
     .mode_ctl_buf    ({net498[0] ,net498[1] } ),
     .reset_l_buf     ({rstl1 } ),
     .rst_io_l_buf    ({net494[0] ,net494[1] } ),
     .shift_dr_buf    ({net489[0] ,net489[1] } ),
     .por_l_buf       ({net496[0] ,net496[1] } ),
     .update_dr_buf   ({net487[0] ,net487[1] } ),
     .serial_out11    (serial_out[104] ),
     .clk             (clk ),
     .vddo            (vddo ),
     .si              (scan[4] ),
     .bsr_si          (bscan[4] ),
     .bso             (bscan[3] ),
     .so              (scan[3] ),
     .ref             (dtl_l_vref ) );
bw_io_dtl_padx12 I39 (
     .ps_select_buf   ({net269[0] ,net269[1] } ),
     .bypass_en_buf   ({net271[0] ,net271[1] } ),
     .serial_out      ({serial_out[68:57] } ),
     .serial_in       ({serial_in[68:57] } ),
     .to_core         ({io_jbi_j_ad[68:57] } ),
     .pad             ({j_ad[68:57] } ),
     .por_l_buf       ({net382[0] ,net382[1] } ),
     .oe_buf          ({net383[0] ,net383[1] } ),
     .reset_l_buf     ({rstl4 } ),
     .update_dr_buf   ({net373[0] ,net373[1] } ),
     .cbu1            ({net388[0] ,net388[1] ,net388[2] ,net388[3] ,
            net388[4] ,net388[5] ,net388[6] ,net388[7] } ),
     .cbd1            ({net390[0] ,net390[1] ,net390[2] ,net390[3] ,
            net390[4] ,net390[5] ,net390[6] ,net390[7] } ),
     .up_open_buf     ({net374[0] ,net374[1] } ),
     .mode_ctl_buf    ({net384[0] ,net384[1] } ),
     .se_buf          ({net377[0] ,net377[1] } ),
     .shift_dr_buf    ({net375[0] ,net375[1] } ),
     .hiz_l_buf       ({net385[0] ,net385[1] } ),
     .rst_val_dn_buf  ({net379[0] ,net379[1] } ),
     .down_25_buf     ({net386[0] ,net386[1] } ),
     .data            ({jbi_io_j_ad[68:57] } ),
     .clock_dr_buf    ({net387[0] ,net387[1] } ),
     .rst_val_up_buf  ({net378[0] ,net378[1] } ),
     .sel_bypass_buf  ({net376[0] ,net376[1] } ),
     .cbu0            ({net389[0] ,net389[1] ,net389[2] ,net389[3] ,
            net389[4] ,net389[5] ,net389[6] ,net389[7] } ),
     .cbd0            ({net391[0] ,net391[1] ,net391[2] ,net391[3] ,
            net391[4] ,net391[5] ,net391[6] ,net391[7] } ),
     .rst_io_l_buf    ({net380[0] ,net380[1] } ),
     .bso             (net656 ),
     .so              (net0682 ),
     .bsr_si          (bscan[1] ),
     .si              (scan[1] ),
     .clk             (clk ),
     .vddo            (vddo ),
     .ref             (dtl_l_vref ) );
bw_u1_buf_15x I106_0_ (
     .z               (bypass_en[0] ),
     .a               (net273[1] ) );
bw_u1_buf_15x I115 (
     .z               (bypass_enable_out ),
     .a               (bypass_en_end[0] ) );
bw_u1_buf_15x I112_0_ (
     .z               (net287[1] ),
     .a               (net283[1] ) );
bw_zckgatedcap_h I156_1_ (
     .ld              (net0236 ) );
bw_u1_buf_15x I117 (
     .z               (ps_select_out ),
     .a               (ps_sel_end[0] ) );
bw_io_dtl_rpt I51 (
     .out18           ({net450[0] ,net450[1] } ),
     .in7             ({net384[0] ,net384[1] } ),
     .in0             ({net391[0] ,net391[1] ,net391[2] ,net391[3] ,
            net391[4] ,net391[5] ,net391[6] ,net391[7] } ),
     .out16           ({net452[0] ,net452[1] } ),
     .in3             ({net388[0] ,net388[1] ,net388[2] ,net388[3] ,
            net388[4] ,net388[5] ,net388[6] ,net388[7] } ),
     .in2             ({net389[0] ,net389[1] ,net389[2] ,net389[3] ,
            net389[4] ,net389[5] ,net389[6] ,net389[7] } ),
     .in6             ({net385[0] ,net385[1] } ),
     .out19           ({net449[0] ,net449[1] } ),
     .in8             ({net383[0] ,net383[1] } ),
     .in9             ({net382[0] ,net382[1] } ),
     .out15           ({net453[0] ,net453[1] } ),
     .out17           ({net451[0] ,net451[1] } ),
     .in1             ({net390[0] ,net390[1] ,net390[2] ,net390[3] ,
            net390[4] ,net390[5] ,net390[6] ,net390[7] } ),
     .in4             ({net387[0] ,net387[1] } ),
     .in5             ({net386[0] ,net386[1] } ),
     .out13           ({net454[0] ,net454[1] } ),
     .in10            ({rstl3 } ),
     .in11            ({net380[0] ,net380[1] } ),
     .in12            ({net379[0] ,net379[1] } ),
     .in13            ({net378[0] ,net378[1] } ),
     .in19            ({net373[0] ,net373[1] } ),
     .in18            ({net374[0] ,net374[1] } ),
     .in17            ({net375[0] ,net375[1] } ),
     .in16            ({net376[0] ,net376[1] } ),
     .in15            ({net377[0] ,net377[1] } ),
     .out6            ({net461[0] ,net461[1] } ),
     .out7            ({net460[0] ,net460[1] } ),
     .out8            ({net459[0] ,net459[1] } ),
     .out9            ({net458[0] ,net458[1] } ),
     .out10           ({rstl4 } ),
     .out11           ({net456[0] ,net456[1] } ),
     .out12           ({net455[0] ,net455[1] } ),
     .out0            ({net467[0] ,net467[1] ,net467[2] ,net467[3] ,
            net467[4] ,net467[5] ,net467[6] ,net467[7] } ),
     .out1            ({net466[0] ,net466[1] ,net466[2] ,net466[3] ,
            net466[4] ,net466[5] ,net466[6] ,net466[7] } ),
     .out2            ({net465[0] ,net465[1] ,net465[2] ,net465[3] ,
            net465[4] ,net465[5] ,net465[6] ,net465[7] } ),
     .out3            ({net464[0] ,net464[1] ,net464[2] ,net464[3] ,
            net464[4] ,net464[5] ,net464[6] ,net464[7] } ),
     .out4            ({net463[0] ,net463[1] } ),
     .out5            ({net462[0] ,net462[1] } ) );
bw_io_dtl_padx12 I52 (
     .ps_select_buf   ({net275[0] ,net275[1] } ),
     .bypass_en_buf   ({net273[0] ,net273[1] } ),
     .serial_out      ({serial_out[80:69] } ),
     .serial_in       ({serial_in[80:69] } ),
     .to_core         ({io_jbi_j_ad[80:69] } ),
     .pad             ({j_ad[80:69] } ),
     .por_l_buf       ({net458[0] ,net458[1] } ),
     .oe_buf          ({net459[0] ,net459[1] } ),
     .reset_l_buf     ({rstl3 } ),
     .update_dr_buf   ({net449[0] ,net449[1] } ),
     .cbu1            ({net464[0] ,net464[1] ,net464[2] ,net464[3] ,
            net464[4] ,net464[5] ,net464[6] ,net464[7] } ),
     .cbd1            ({net466[0] ,net466[1] ,net466[2] ,net466[3] ,
            net466[4] ,net466[5] ,net466[6] ,net466[7] } ),
     .up_open_buf     ({net450[0] ,net450[1] } ),
     .mode_ctl_buf    ({net460[0] ,net460[1] } ),
     .se_buf          ({net453[0] ,net453[1] } ),
     .shift_dr_buf    ({net451[0] ,net451[1] } ),
     .hiz_l_buf       ({net461[0] ,net461[1] } ),
     .rst_val_dn_buf  ({net455[0] ,net455[1] } ),
     .down_25_buf     ({net462[0] ,net462[1] } ),
     .data            ({jbi_io_j_ad[80:69] } ),
     .clock_dr_buf    ({net463[0] ,net463[1] } ),
     .rst_val_up_buf  ({net454[0] ,net454[1] } ),
     .sel_bypass_buf  ({net452[0] ,net452[1] } ),
     .cbu0            ({net465[0] ,net465[1] ,net465[2] ,net465[3] ,
            net465[4] ,net465[5] ,net465[6] ,net465[7] } ),
     .cbd0            ({net467[0] ,net467[1] ,net467[2] ,net467[3] ,
            net467[4] ,net467[5] ,net467[6] ,net467[7] } ),
     .rst_io_l_buf    ({net456[0] ,net456[1] } ),
     .bso             (bscan[1] ),
     .so              (scan[1] ),
     .bsr_si          (bscan[2] ),
     .si              (scan[2] ),
     .clk             (clk ),
     .vddo            (vddo ),
     .ref             (dtl_l_vref ) );
bw_io_dtl_rpt I53 (
     .out18           ({mid18 } ),
     .in7             ({net460[0] ,net460[1] } ),
     .in0             ({net467[0] ,net467[1] ,net467[2] ,net467[3] ,
            net467[4] ,net467[5] ,net467[6] ,net467[7] } ),
     .out16           ({mid16 } ),
     .in3             ({net464[0] ,net464[1] ,net464[2] ,net464[3] ,
            net464[4] ,net464[5] ,net464[6] ,net464[7] } ),
     .in2             ({net465[0] ,net465[1] ,net465[2] ,net465[3] ,
            net465[4] ,net465[5] ,net465[6] ,net465[7] } ),
     .in6             ({net461[0] ,net461[1] } ),
     .out19           ({mid19 } ),
     .in8             ({net459[0] ,net459[1] } ),
     .in9             ({net458[0] ,net458[1] } ),
     .out15           ({mid15 } ),
     .out17           ({mid17 } ),
     .in1             ({net466[0] ,net466[1] ,net466[2] ,net466[3] ,
            net466[4] ,net466[5] ,net466[6] ,net466[7] } ),
     .in4             ({net463[0] ,net463[1] } ),
     .in5             ({net462[0] ,net462[1] } ),
     .out13           ({mid13 } ),
     .in10            ({rstl2 } ),
     .in11            ({net456[0] ,net456[1] } ),
     .in12            ({net455[0] ,net455[1] } ),
     .in13            ({net454[0] ,net454[1] } ),
     .in19            ({net449[0] ,net449[1] } ),
     .in18            ({net450[0] ,net450[1] } ),
     .in17            ({net451[0] ,net451[1] } ),
     .in16            ({net452[0] ,net452[1] } ),
     .in15            ({net453[0] ,net453[1] } ),
     .out6            ({mid6 } ),
     .out7            ({mid7 } ),
     .out8            ({net576[0] ,net576[1] } ),
     .out9            ({mid9 } ),
     .out10           ({rstl3 } ),
     .out11           ({mid11 } ),
     .out12           ({mid12 } ),
     .out0            ({mid0 } ),
     .out1            ({mid1 } ),
     .out2            ({mid2 } ),
     .out3            ({mid3 } ),
     .out4            ({mid4 } ),
     .out5            ({mid5 } ) );
bw_u1_buf_15x I113_1_ (
     .z               (bypass_en_end[1] ),
     .a               (net285[0] ) );
bw_io_dtl_padx12 I55 (
     .ps_select_buf   ({ps_sel } ),
     .bypass_en_buf   ({bypass_en } ),
     .serial_out      ({serial_out[92:81] } ),
     .serial_in       ({serial_in[92:81] } ),
     .to_core         ({io_jbi_j_ad[92:81] } ),
     .pad             ({j_ad[92:81] } ),
     .por_l_buf       ({mid9 } ),
     .oe_buf          ({net576[0] ,net576[1] } ),
     .reset_l_buf     ({rstl2 } ),
     .update_dr_buf   ({mid19 } ),
     .cbu1            ({mid3 } ),
     .cbd1            ({mid1 } ),
     .up_open_buf     ({mid18 } ),
     .mode_ctl_buf    ({mid7 } ),
     .se_buf          ({mid15 } ),
     .shift_dr_buf    ({mid17 } ),
     .hiz_l_buf       ({mid6 } ),
     .rst_val_dn_buf  ({mid12 } ),
     .down_25_buf     ({mid5 } ),
     .data            ({jbi_io_j_ad[92:81] } ),
     .clock_dr_buf    ({mid4 } ),
     .rst_val_up_buf  ({mid13 } ),
     .sel_bypass_buf  ({mid16 } ),
     .cbu0            ({mid2 } ),
     .cbd0            ({mid0 } ),
     .rst_io_l_buf    ({mid11 } ),
     .bso             (bscan[2] ),
     .so              (scan[2] ),
     .bsr_si          (bscan[3] ),
     .si              (scan[3] ),
     .clk             (clk ),
     .vddo            (vddo ),
     .ref             (dtl_l_vref ) );
bw_zckgatedcap_h I156_0_ (
     .ld              (net0236 ) );
endmodule
