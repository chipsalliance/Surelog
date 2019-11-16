// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: bw_dtl_impctl_pullup.v
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
module bw_dtl_impctl_pullup(rclk ,ctu_io_sscan_update ,ctu_global_snap ,
     tclk ,ctu_io_sscan_se ,si ,we_csr ,from_csr ,se ,ctu_io_sscan_in ,
     hard_reset_n ,clk_dis_l ,vddo ,z ,to_csr ,so_l ,imped_shadow_so ,
     deltabit ,pad );
output [7:0]	z ;
output [7:0]	to_csr ;
input [7:0]	from_csr ;
output		so_l ;
output		imped_shadow_so ;
output		deltabit ;
input		rclk ;
input		ctu_io_sscan_update ;
input		ctu_global_snap ;
input		tclk ;
input		ctu_io_sscan_se ;
input		si ;
input		we_csr ;
input		se ;
input		ctu_io_sscan_in ;
input		hard_reset_n ;
input		clk_dis_l ;
input		vddo ;
inout		pad ;
supply1		vdd ;
 
wire [7:0]	z_post ;
wire [7:0]	d ;
wire [7:0]	net097 ;
wire [7:0]	net47 ;
wire [7:0]	net054 ;
wire		clk ;
wire		above ;
wire		global_reset_n ;
wire		sodr_l ;
wire		bypass ;
wire		updclk ;
wire		sos ;
wire		net0110 ;
wire		clk_en_l ;
wire		net081 ;
wire		sclk ;
wire		avgcntr_rst ;
 
 
bw_u1_inv_5x I44_0_ (
     .z               (net054[7] ),
     .a               (d[7] ) );
bw_u1_inv_5x I43_2_ (
     .z               (net097[5] ),
     .a               (net054[5] ) );
bw_u1_inv_4x I28_1_ (
     .z               (net47[6] ),
     .a               (z_post[6] ) );
bw_u1_inv_10x I29_7_ (
     .z               (z[7] ),
     .a               (net47[0] ) );
bw_u1_inv_5x I44_1_ (
     .z               (net054[6] ),
     .a               (d[6] ) );
bw_u1_inv_5x I43_3_ (
     .z               (net097[4] ),
     .a               (net054[4] ) );
bw_u1_inv_4x I28_2_ (
     .z               (net47[5] ),
     .a               (z_post[5] ) );
bw_u1_inv_10x I29_0_ (
     .z               (z[0] ),
     .a               (net47[7] ) );
bw_io_impctl_dtl_uprcn I241 (
     .cbu             ({net097[0] ,net097[1] ,net097[2] ,net097[3] ,
            net097[4] ,net097[5] ,net097[6] ,net097[7] } ),
     .si_l            (net081 ),
     .so_l            (sodr_l ),
     .pad             (pad ),
     .sclk            (sclk ),
     .vddo            (vddo ),
     .above           (above ),
     .clk             (clk ),
     .se              (se ),
     .global_reset_n  (global_reset_n ) );
bw_u1_inv_5x I44_2_ (
     .z               (net054[5] ),
     .a               (d[5] ) );
bw_u1_inv_5x I43_4_ (
     .z               (net097[3] ),
     .a               (net054[3] ) );
bw_u1_inv_4x I28_3_ (
     .z               (net47[4] ),
     .a               (z_post[4] ) );
bw_u1_inv_10x I29_1_ (
     .z               (z[1] ),
     .a               (net47[6] ) );
bw_u1_inv_5x I44_3_ (
     .z               (net054[4] ),
     .a               (d[4] ) );
bw_u1_inv_5x I43_5_ (
     .z               (net097[2] ),
     .a               (net054[2] ) );
bw_u1_inv_4x I28_4_ (
     .z               (net47[3] ),
     .a               (z_post[3] ) );
bw_u1_inv_10x I29_2_ (
     .z               (z[2] ),
     .a               (net47[5] ) );
bw_u1_inv_5x I44_4_ (
     .z               (net054[3] ),
     .a               (d[3] ) );
bw_u1_inv_5x I43_6_ (
     .z               (net097[1] ),
     .a               (net054[1] ) );
bw_u1_inv_4x I28_5_ (
     .z               (net47[2] ),
     .a               (z_post[2] ) );
bw_u1_inv_10x I29_3_ (
     .z               (z[3] ),
     .a               (net47[4] ) );
bw_io_impctl_smachine_new I23 (
     .z_post          ({z_post } ),
     .from_csr        ({from_csr } ),
     .to_csr          ({to_csr } ),
     .d               ({d } ),
     .deltabit        (deltabit ),
     .ctu_io_sscan_se (ctu_io_sscan_se ),
     .updclk          (updclk ),
     .we_csr          (we_csr ),
     .l2clk           (rclk ),
     .ctu_io_sscan_in (ctu_io_sscan_in ),
     .above           (above ),
     .bypass          (bypass ),
     .config_pmos     (vdd ),
     .global_reset_n  (global_reset_n ),
     .hard_reset_n    (hard_reset_n ),
     .ctu_global_snap (ctu_global_snap ),
     .sclk            (sclk ),
     .avgcntr_rst     (avgcntr_rst ),
     .so              (sos ),
     .se              (se ),
     .si_l            (sodr_l ),
     .io_ctu_sscan_out (imped_shadow_so ),
     .tclk            (tclk ),
     .ctu_io_sscan_update (ctu_io_sscan_update ),
     .clk_en_l        (clk_en_l ) );
bw_io_impctl_dtl_clkgen I24 (
     .se              (se ),
     .updclk          (updclk ),
     .clk             (clk ),
     .so_l            (so_l ),
     .si_l            (sos ),
     .synced_upd_imped (ctu_io_sscan_update ),
     .avgcntr_rst     (avgcntr_rst ),
     .bypass          (bypass ),
     .global_reset_n  (global_reset_n ),
     .hard_reset_n    (hard_reset_n ),
     .sclk            (sclk ),
     .reset_l         (vdd ) );
bw_u1_inv_5x I44_5_ (
     .z               (net054[2] ),
     .a               (d[2] ) );
bw_u1_inv_5x I43_7_ (
     .z               (net097[0] ),
     .a               (net054[0] ) );
bw_u1_inv_4x I28_6_ (
     .z               (net47[1] ),
     .a               (z_post[1] ) );
bw_u1_inv_10x I29_4_ (
     .z               (z[4] ),
     .a               (net47[3] ) );
bw_u1_ckenbuf_14x I30 (
     .clk             (clk ),
     .rclk            (rclk ),
     .en_l            (clk_en_l ),
     .tm_l            (net0110 ) );
bw_u1_inv_10x I34 (
     .z               (clk_en_l ),
     .a               (clk_dis_l ) );
bw_u1_inv_5x I43_0_ (
     .z               (net097[7] ),
     .a               (net054[7] ) );
bw_u1_inv_5x I44_6_ (
     .z               (net054[1] ),
     .a               (d[1] ) );
bw_u1_inv_4x I28_7_ (
     .z               (net47[0] ),
     .a               (z_post[0] ) );
bw_u1_inv_10x I29_5_ (
     .z               (z[5] ),
     .a               (net47[2] ) );
bw_u1_inv_8x I41 (
     .z               (net081 ),
     .a               (si ) );
bw_u1_inv_4x I42 (
     .z               (net0110 ),
     .a               (se ) );
bw_u1_inv_5x I43_1_ (
     .z               (net097[6] ),
     .a               (net054[6] ) );
bw_u1_inv_5x I44_7_ (
     .z               (net054[0] ),
     .a               (d[0] ) );
bw_u1_inv_4x I28_0_ (
     .z               (net47[7] ),
     .a               (z_post[7] ) );
bw_u1_inv_10x I29_6_ (
     .z               (z[6] ),
     .a               (net47[1] ) );
endmodule
