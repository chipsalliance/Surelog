// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: bw_dtl_impctl_pulldown.v
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
module bw_dtl_impctl_pulldown(rclk ,se ,hard_reset_n ,we_csr ,
     ctu_io_sscan_se ,ctu_io_sscan_in ,tclk ,ctu_global_snap ,from_csr ,
     so ,si ,io_ctu_sscan_out ,z ,ctu_io_sscan_update ,deltabit ,to_csr
      ,clk_dis_l ,vddo ,pad );
output [7:0]	z ;
output [7:0]	to_csr ;
input [7:0]	from_csr ;
output		so ;
output		io_ctu_sscan_out ;
output		deltabit ;
input		rclk ;
input		se ;
input		hard_reset_n ;
input		we_csr ;
input		ctu_io_sscan_se ;
input		ctu_io_sscan_in ;
input		tclk ;
input		ctu_global_snap ;
input		si ;
input		ctu_io_sscan_update ;
input		clk_dis_l ;
input		vddo ;
inout		pad ;
supply1		vdd ;
supply0		vss ;
 
wire [7:0]	z_post ;
wire [7:0]	d ;
wire [7:0]	net51 ;
wire [7:0]	net088 ;
wire [7:0]	net050 ;
wire		clk ;
wire		net087 ;
wire		above ;
wire		global_reset_n ;
wire		sodr_l ;
wire		bypass ;
wire		net049 ;
wire		updclk ;
wire		sos ;
wire		net060 ;
wire		clk_en_l ;
wire		sclk ;
wire		avgcntr_rst ;
 
 
bw_u1_inv_5x I44_0_ (
     .z               (d[0] ),
     .a               (net050[7] ) );
bw_u1_inv_5x I43_2_ (
     .z               (net050[5] ),
     .a               (net088[5] ) );
bw_u1_inv_4x I28_1_ (
     .z               (net51[6] ),
     .a               (z_post[1] ) );
bw_u1_inv_10x I29_7_ (
     .z               (z[7] ),
     .a               (net51[0] ) );
bw_u1_inv_5x I44_1_ (
     .z               (d[1] ),
     .a               (net050[6] ) );
bw_u1_inv_5x I43_3_ (
     .z               (net050[4] ),
     .a               (net088[4] ) );
bw_u1_inv_10x I29_0_ (
     .z               (z[0] ),
     .a               (net51[7] ) );
bw_u1_inv_4x I28_2_ (
     .z               (net51[5] ),
     .a               (z_post[2] ) );
bw_io_impctl_dtl_dnrcn I241 (
     .cbd             ({d } ),
     .above           (above ),
     .global_reset_n  (global_reset_n ),
     .sclk            (sclk ),
     .se              (se ),
     .vddo            (vddo ),
     .si_l            (net049 ),
     .pad             (pad ),
     .clk             (clk ),
     .so_l            (sodr_l ) );
bw_u1_inv_5x I44_2_ (
     .z               (d[2] ),
     .a               (net050[5] ) );
bw_u1_inv_5x I43_4_ (
     .z               (net050[3] ),
     .a               (net088[3] ) );
bw_u1_inv_10x I29_1_ (
     .z               (z[1] ),
     .a               (net51[6] ) );
bw_u1_inv_4x I28_3_ (
     .z               (net51[4] ),
     .a               (z_post[3] ) );
bw_u1_inv_5x I44_3_ (
     .z               (d[3] ),
     .a               (net050[4] ) );
bw_u1_inv_5x I43_5_ (
     .z               (net050[2] ),
     .a               (net088[2] ) );
bw_u1_inv_10x I29_2_ (
     .z               (z[2] ),
     .a               (net51[5] ) );
bw_u1_inv_4x I28_4_ (
     .z               (net51[3] ),
     .a               (z_post[4] ) );
bw_u1_inv_5x I44_4_ (
     .z               (d[4] ),
     .a               (net050[3] ) );
bw_u1_inv_5x I43_6_ (
     .z               (net050[1] ),
     .a               (net088[1] ) );
bw_u1_inv_10x I29_3_ (
     .z               (z[3] ),
     .a               (net51[4] ) );
bw_u1_inv_4x I28_5_ (
     .z               (net51[2] ),
     .a               (z_post[5] ) );
bw_io_impctl_smachine_new I23 (
     .z_post          ({z_post } ),
     .from_csr        ({from_csr } ),
     .to_csr          ({to_csr } ),
     .d               ({net088[0] ,net088[1] ,net088[2] ,net088[3] ,
            net088[4] ,net088[5] ,net088[6] ,net088[7] } ),
     .deltabit        (deltabit ),
     .ctu_io_sscan_se (ctu_io_sscan_se ),
     .updclk          (updclk ),
     .we_csr          (we_csr ),
     .l2clk           (rclk ),
     .ctu_io_sscan_in (ctu_io_sscan_in ),
     .above           (above ),
     .bypass          (bypass ),
     .config_pmos     (vss ),
     .global_reset_n  (global_reset_n ),
     .hard_reset_n    (hard_reset_n ),
     .ctu_global_snap (ctu_global_snap ),
     .sclk            (sclk ),
     .avgcntr_rst     (avgcntr_rst ),
     .so              (sos ),
     .se              (se ),
     .si_l            (sodr_l ),
     .io_ctu_sscan_out (io_ctu_sscan_out ),
     .tclk            (tclk ),
     .ctu_io_sscan_update (ctu_io_sscan_update ),
     .clk_en_l        (clk_en_l ) );
bw_io_impctl_dtl_clkgen I24 (
     .se              (se ),
     .updclk          (updclk ),
     .clk             (clk ),
     .so_l            (net087 ),
     .si_l            (sos ),
     .synced_upd_imped (ctu_io_sscan_update ),
     .avgcntr_rst     (avgcntr_rst ),
     .bypass          (bypass ),
     .global_reset_n  (global_reset_n ),
     .hard_reset_n    (hard_reset_n ),
     .sclk            (sclk ),
     .reset_l         (vdd ) );
bw_u1_inv_5x I44_5_ (
     .z               (d[5] ),
     .a               (net050[2] ) );
bw_u1_inv_5x I43_7_ (
     .z               (net050[0] ),
     .a               (net088[0] ) );
bw_u1_inv_10x I29_4_ (
     .z               (z[4] ),
     .a               (net51[3] ) );
bw_u1_inv_4x I28_6_ (
     .z               (net51[1] ),
     .a               (z_post[6] ) );
bw_u1_ckenbuf_14x I30 (
     .clk             (clk ),
     .rclk            (rclk ),
     .en_l            (clk_en_l ),
     .tm_l            (net060 ) );
bw_u1_inv_10x I33 (
     .z               (clk_en_l ),
     .a               (clk_dis_l ) );
bw_u1_inv_5x I43_0_ (
     .z               (net050[7] ),
     .a               (net088[7] ) );
bw_u1_inv_5x I44_6_ (
     .z               (d[6] ),
     .a               (net050[1] ) );
bw_u1_inv_10x I29_5_ (
     .z               (z[5] ),
     .a               (net51[2] ) );
bw_u1_inv_4x I28_7_ (
     .z               (net51[0] ),
     .a               (z_post[7] ) );
bw_u1_inv_8x I40 (
     .z               (so ),
     .a               (net087 ) );
bw_u1_inv_8x I41 (
     .z               (net049 ),
     .a               (si ) );
bw_u1_inv_4x I42 (
     .z               (net060 ),
     .a               (se ) );
bw_u1_inv_5x I43_1_ (
     .z               (net050[6] ),
     .a               (net088[6] ) );
bw_u1_inv_5x I44_7_ (
     .z               (d[7] ),
     .a               (net050[0] ) );
bw_u1_inv_4x I28_0_ (
     .z               (net51[7] ),
     .a               (z_post[0] ) );
bw_u1_inv_10x I29_6_ (
     .z               (z[6] ),
     .a               (net51[1] ) );
endmodule
