// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: ccx.v
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

`include "sys.h"
`include "iop.h"

module ccx(/*AUTOARG*/
   // Outputs
   pcx_spc7_grant_px, pcx_spc6_grant_px, pcx_spc5_grant_px, 
   pcx_spc4_grant_px, pcx_spc3_grant_px, pcx_spc2_grant_px, 
   pcx_spc1_grant_px, pcx_spc0_grant_px, pcx_sctag3_data_rdy_px1, 
   pcx_sctag3_data_px2, pcx_sctag3_atm_px1, pcx_sctag2_data_rdy_px1, 
   pcx_sctag2_data_px2, pcx_sctag2_atm_px1, pcx_sctag1_data_rdy_px1, 
   pcx_sctag1_data_px2, pcx_sctag1_atm_px1, pcx_sctag0_data_rdy_px1, 
   pcx_sctag0_data_px2, pcx_sctag0_atm_px1, pcx_iob_data_rdy_px2, 
   pcx_iob_data_px2, pcx_fp_data_rdy_px2, pcx_fp_data_px2, 
   cpx_spc7_data_rdy_cx2, cpx_spc7_data_cx2, cpx_spc6_data_rdy_cx2, 
   cpx_spc6_data_cx2, cpx_spc5_data_rdy_cx2, cpx_spc5_data_cx2, 
   cpx_spc4_data_rdy_cx2, cpx_spc4_data_cx2, cpx_spc3_data_rdy_cx2, 
   cpx_spc3_data_cx2, cpx_spc2_data_rdy_cx2, cpx_spc2_data_cx2, 
   cpx_spc1_data_rdy_cx2, cpx_spc1_data_cx2, cpx_spc0_data_rdy_cx2, 
   cpx_spc0_data_cx2, cpx_sctag3_grant_cx, cpx_sctag2_grant_cx, 
   cpx_sctag1_grant_cx, cpx_sctag0_grant_cx, cpx_iob_grant_cx2, 
   ccx_scanout1, ccx_scanout0, rclk, 
   // Inputs
   spc7_pcx_req_pq, spc7_pcx_data_pa, spc7_pcx_atom_pq, 
   spc6_pcx_req_pq, spc6_pcx_data_pa, spc6_pcx_atom_pq, 
   spc5_pcx_req_pq, spc5_pcx_data_pa, spc5_pcx_atom_pq, 
   spc4_pcx_req_pq, spc4_pcx_data_pa, spc4_pcx_atom_pq, 
   spc3_pcx_req_pq, spc3_pcx_data_pa, spc3_pcx_atom_pq, 
   spc2_pcx_req_pq, spc2_pcx_data_pa, spc2_pcx_atom_pq, 
   spc1_pcx_req_pq, spc1_pcx_data_pa, spc1_pcx_atom_pq, 
   spc0_pcx_req_pq, spc0_pcx_data_pa, spc0_pcx_atom_pq, 
   sctag3_pcx_stall_pq, sctag3_cpx_req_cq, sctag3_cpx_data_ca, 
   sctag3_cpx_atom_cq, sctag2_pcx_stall_pq, sctag2_cpx_req_cq, 
   sctag2_cpx_data_ca, sctag2_cpx_atom_cq, sctag1_pcx_stall_pq, 
   sctag1_cpx_req_cq, sctag1_cpx_data_ca, sctag1_cpx_atom_cq, 
   sctag0_pcx_stall_pq, sctag0_cpx_req_cq, sctag0_cpx_data_ca, 
   sctag0_cpx_atom_cq, iob_cpx_req_cq, iob_cpx_data_ca, 
   global_shift_enable, gdbginit_l, gclk, fp_cpx_req_cq, 
   fp_cpx_data_ca, ctu_tst_short_chain, ctu_tst_scanmode, 
   ctu_tst_scan_disable, ctu_tst_pre_grst_l, ctu_tst_macrotest, 
   cmp_grst_l, cmp_arst_l, clk_ccx_cken, ccx_scanin1, ccx_scanin0, 
   adbginit_l, iob_pcx_stall_pq
   );
   
   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output		ccx_scanout0;		// From ccx_test_stub of test_stub_scan.v
   output		ccx_scanout1;		// From ccx_test_stub of test_stub_scan.v
   output [7:0]		cpx_iob_grant_cx2;	// From cpx of cpx.v
   output [7:0]		cpx_sctag0_grant_cx;	// From cpx of cpx.v
   output [7:0]		cpx_sctag1_grant_cx;	// From cpx of cpx.v
   output [7:0]		cpx_sctag2_grant_cx;	// From cpx of cpx.v
   output [7:0]		cpx_sctag3_grant_cx;	// From cpx of cpx.v
   output [`CPX_WIDTH-1:0]cpx_spc0_data_cx2;	// From cpx of cpx.v
   output		cpx_spc0_data_rdy_cx2;	// From cpx of cpx.v
   output [`CPX_WIDTH-1:0]cpx_spc1_data_cx2;	// From cpx of cpx.v
   output		cpx_spc1_data_rdy_cx2;	// From cpx of cpx.v
   output [`CPX_WIDTH-1:0]cpx_spc2_data_cx2;	// From cpx of cpx.v
   output		cpx_spc2_data_rdy_cx2;	// From cpx of cpx.v
   output [`CPX_WIDTH-1:0]cpx_spc3_data_cx2;	// From cpx of cpx.v
   output		cpx_spc3_data_rdy_cx2;	// From cpx of cpx.v
   output [`CPX_WIDTH-1:0]cpx_spc4_data_cx2;	// From cpx of cpx.v
   output		cpx_spc4_data_rdy_cx2;	// From cpx of cpx.v
   output [`CPX_WIDTH-1:0]cpx_spc5_data_cx2;	// From cpx of cpx.v
   output		cpx_spc5_data_rdy_cx2;	// From cpx of cpx.v
   output [`CPX_WIDTH-1:0]cpx_spc6_data_cx2;	// From cpx of cpx.v
   output		cpx_spc6_data_rdy_cx2;	// From cpx of cpx.v
   output [`CPX_WIDTH-1:0]cpx_spc7_data_cx2;	// From cpx of cpx.v
   output		cpx_spc7_data_rdy_cx2;	// From cpx of cpx.v
   output [`PCX_WIDTH-1:0]pcx_fp_data_px2;	// From pcx of pcx.v
   output		pcx_fp_data_rdy_px2;	// From pcx of pcx.v
   output [`PCX_WIDTH-1:0]pcx_iob_data_px2;	// From pcx of pcx.v
   output		pcx_iob_data_rdy_px2;	// From pcx of pcx.v
   output		pcx_sctag0_atm_px1;	// From pcx of pcx.v
   output [`PCX_WIDTH-1:0]pcx_sctag0_data_px2;	// From pcx of pcx.v
   output		pcx_sctag0_data_rdy_px1;// From pcx of pcx.v
   output		pcx_sctag1_atm_px1;	// From pcx of pcx.v
   output [`PCX_WIDTH-1:0]pcx_sctag1_data_px2;	// From pcx of pcx.v
   output		pcx_sctag1_data_rdy_px1;// From pcx of pcx.v
   output		pcx_sctag2_atm_px1;	// From pcx of pcx.v
   output [`PCX_WIDTH-1:0]pcx_sctag2_data_px2;	// From pcx of pcx.v
   output		pcx_sctag2_data_rdy_px1;// From pcx of pcx.v
   output		pcx_sctag3_atm_px1;	// From pcx of pcx.v
   output [`PCX_WIDTH-1:0]pcx_sctag3_data_px2;	// From pcx of pcx.v
   output		pcx_sctag3_data_rdy_px1;// From pcx of pcx.v
   output [4:0]		pcx_spc0_grant_px;	// From pcx of pcx.v
   output [4:0]		pcx_spc1_grant_px;	// From pcx of pcx.v
   output [4:0]		pcx_spc2_grant_px;	// From pcx of pcx.v
   output [4:0]		pcx_spc3_grant_px;	// From pcx of pcx.v
   output [4:0]		pcx_spc4_grant_px;	// From pcx of pcx.v
   output [4:0]		pcx_spc5_grant_px;	// From pcx of pcx.v
   output [4:0]		pcx_spc6_grant_px;	// From pcx of pcx.v
   output [4:0]		pcx_spc7_grant_px;	// From pcx of pcx.v
   // End of automatics
   
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input		adbginit_l;		// To buf_global_middle0 of ccx_global_int_buf.v
   input		ccx_scanin0;		// To pcx of pcx.v
   input		ccx_scanin1;		// To cpx of cpx.v
   input		clk_ccx_cken;		// To ccx_hdr of bw_clk_cl_ccx_cmp.v
   input		cmp_arst_l;		// To ccx_test_stub of test_stub_scan.v, ...
   input		cmp_grst_l;		// To ccx_hdr of bw_clk_cl_ccx_cmp.v
   input		ctu_tst_macrotest;	// To ccx_test_stub of test_stub_scan.v
   input		ctu_tst_pre_grst_l;	// To ccx_test_stub of test_stub_scan.v
   input		ctu_tst_scan_disable;	// To ccx_test_stub of test_stub_scan.v
   input		ctu_tst_scanmode;	// To ccx_test_stub of test_stub_scan.v
   input		ctu_tst_short_chain;	// To ccx_test_stub of test_stub_scan.v
   input [`CPX_WIDTH-1:0]fp_cpx_data_ca;	// To cpx of cpx.v
   input [7:0]		fp_cpx_req_cq;		// To cpx of cpx.v
   input [1:0]		gclk;			// To ccx_hdr of bw_clk_cl_ccx_cmp.v
   input		gdbginit_l;		// To ccx_hdr of bw_clk_cl_ccx_cmp.v
   input		global_shift_enable;	// To ccx_test_stub of test_stub_scan.v
   input [`CPX_WIDTH-1:0]iob_cpx_data_ca;	// To cpx of cpx.v
   input [7:0]		iob_cpx_req_cq;		// To cpx of cpx.v
   input		sctag0_cpx_atom_cq;	// To cpx of cpx.v
   input [`CPX_WIDTH-1:0]sctag0_cpx_data_ca;	// To cpx of cpx.v
   input [7:0]		sctag0_cpx_req_cq;	// To cpx of cpx.v
   input		sctag0_pcx_stall_pq;	// To pcx of pcx.v
   input		sctag1_cpx_atom_cq;	// To cpx of cpx.v
   input [`CPX_WIDTH-1:0]sctag1_cpx_data_ca;	// To cpx of cpx.v
   input [7:0]		sctag1_cpx_req_cq;	// To cpx of cpx.v
   input		sctag1_pcx_stall_pq;	// To pcx of pcx.v
   input		sctag2_cpx_atom_cq;	// To cpx of cpx.v
   input [`CPX_WIDTH-1:0]sctag2_cpx_data_ca;	// To cpx of cpx.v
   input [7:0]		sctag2_cpx_req_cq;	// To cpx of cpx.v
   input		sctag2_pcx_stall_pq;	// To pcx of pcx.v
   input		sctag3_cpx_atom_cq;	// To cpx of cpx.v
   input [`CPX_WIDTH-1:0]sctag3_cpx_data_ca;	// To cpx of cpx.v
   input [7:0]		sctag3_cpx_req_cq;	// To cpx of cpx.v
   input		sctag3_pcx_stall_pq;	// To pcx of pcx.v
   input		spc0_pcx_atom_pq;	// To pcx of pcx.v
   input [`PCX_WIDTH-1:0]spc0_pcx_data_pa;	// To pcx of pcx.v
   input [4:0]		spc0_pcx_req_pq;	// To pcx of pcx.v
   input		spc1_pcx_atom_pq;	// To pcx of pcx.v
   input [`PCX_WIDTH-1:0]spc1_pcx_data_pa;	// To pcx of pcx.v
   input [4:0]		spc1_pcx_req_pq;	// To pcx of pcx.v
   input		spc2_pcx_atom_pq;	// To pcx of pcx.v
   input [`PCX_WIDTH-1:0]spc2_pcx_data_pa;	// To pcx of pcx.v
   input [4:0]		spc2_pcx_req_pq;	// To pcx of pcx.v
   input		spc3_pcx_atom_pq;	// To pcx of pcx.v
   input [`PCX_WIDTH-1:0]spc3_pcx_data_pa;	// To pcx of pcx.v
   input [4:0]		spc3_pcx_req_pq;	// To pcx of pcx.v
   input		spc4_pcx_atom_pq;	// To pcx of pcx.v
   input [`PCX_WIDTH-1:0]spc4_pcx_data_pa;	// To pcx of pcx.v
   input [4:0]		spc4_pcx_req_pq;	// To pcx of pcx.v
   input		spc5_pcx_atom_pq;	// To pcx of pcx.v
   input [`PCX_WIDTH-1:0]spc5_pcx_data_pa;	// To pcx of pcx.v
   input [4:0]		spc5_pcx_req_pq;	// To pcx of pcx.v
   input		spc6_pcx_atom_pq;	// To pcx of pcx.v
   input [`PCX_WIDTH-1:0]spc6_pcx_data_pa;	// To pcx of pcx.v
   input [4:0]		spc6_pcx_req_pq;	// To pcx of pcx.v
   input		spc7_pcx_atom_pq;	// To pcx of pcx.v
   input [`PCX_WIDTH-1:0]spc7_pcx_data_pa;	// To pcx of pcx.v
   input [4:0]		spc7_pcx_req_pq;	// To pcx of pcx.v
   // End of automatics

   input iob_pcx_stall_pq;

// Test outputs
//


//ccx test/clk signals

//input cmp_gclk;                //840 Mhz global clock input to cluster header
//input tck     ;                //test clock
//input rst_l;                   //active low reset signal
//input clk_ccx_cken;           //ccx cluster clock enable
//input [1:0] tcu_sel;    //clock src selection
//output ccx_clk_tr;         //debug trigger
   //usually the next three signals would appear
   //at the test stub interface, but are generated
   //in tcu for the special case of the ccx
//input tcu_ccx_shiftenable;     //scan shift enable signal
//input tcu_ccx_rst_tri_en; //reset tri en
//input tcu_ccx_testmode_l; //active lo testmode signal

//input tcu_ccx_scanin_0;         //scan chain input
//output ccx_tcu_scanout_0;       //scan chain output
//input tcu_ccx_scanin_1;         //scan chain input
//output ccx_tcu_scanout_1;       //scan chain output
//input tcu_ccx_scanin_2;         //scan chain input
//output ccx_tcu_scanout_2;       //scan chain output
//input tcu_ccx_scanin_3;         //scan chain input
//output ccx_tcu_scanout_3;       //scan chain output

//input  ctu_ccx0_scanin;
//input  ctu_ccx1_scanin;
//input  ctu_ccx2_scanin;
//input  ctu_ccx3_scanin;
//output ccx0_ctu_scanout;
//output ccx1_ctu_scanout;
//output ccx2_ctu_scanout;
//output ccx3_ctu_scanout;

//input    ddr0_ccx_si ;
//input    ddr2_ccx_si ;
//output   ccx_ddr0_testmode_l ;
//output   ccx_ddr2_testmode_l ;
//output   ccx_ddr0_se ;
//output   ccx_ddr2_se ;
//output   ccx_ddr0_so ;
//output   ccx_ddr2_so ;

//input    ccx_scanin0 ;
//input    ccx_scanin1 ;
//output   ccx_scanout0 ;
//output   ccx_scanout1 ;
output   rclk;			// From ccx_hdr of bw_clk_cl_ccx_cmp.v
   
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire			adbginit_l_buf0_middle;	// From buf_global_middle0 of ccx_global_int_buf.v
   wire			adbginit_l_buf1_middle;	// From buf_global_middle1 of ccx_global_int_buf.v
   wire			adbginit_l_buf2_middle;	// From buf_global_middle2 of ccx_global_int_buf.v
   wire			adbginit_l_buf3_middle;	// From buf_global_middle3 of ccx_global_int_buf.v
   wire			adbginit_l_buf4_middle;	// From buf_global_middle4 of ccx_global_int_buf.v
   wire			adbginit_l_buf5_middle;	// From buf_global_middle5 of ccx_global_int_buf.v
   wire			adbginit_l_buf6_middle;	// From buf_global_middle6 of ccx_global_int_buf.v
   wire			arst_l_buf_fpio_inff;	// From pcx of pcx.v
   wire			ccx_clk_hdr_so_1;	// From ccx_hdr of bw_clk_cl_ccx_cmp.v
   wire			ccx_gdbginit_l;		// From ccx_hdr of bw_clk_cl_ccx_cmp.v
   wire			cpx_arb7_so_1;		// From cpx of cpx.v
   wire			cpx_buf_top_pt0_so_1;	// From cpx of cpx.v
   wire			cpx_dp_half_array_odd_so_0;// From cpx of cpx.v
   wire			pcx_buf_top_pt0_so_0;	// From pcx of pcx.v
   wire			pcx_iodata_px2_so_1;	// From pcx of pcx.v
   wire			pcx_scache0_dat_px2_so_1;// From pcx of pcx.v
   wire			pcx_scache1_dat_px2_so_1;// From pcx of pcx.v
   wire			pcx_scache2_dat_px2_so_1;// From pcx of pcx.v
   wire			pt1_so_1;		// From cpx of cpx.v
   wire			rst_l_buf1_middle;	// From buf_global_middle1 of ccx_global_int_buf.v
   wire			rst_l_buf2_middle;	// From buf_global_middle2 of ccx_global_int_buf.v
   wire			rst_l_buf3_middle;	// From buf_global_middle3 of ccx_global_int_buf.v
   wire			rst_l_buf4_middle;	// From buf_global_middle4 of ccx_global_int_buf.v
   wire			rst_l_buf5_middle;	// From buf_global_middle5 of ccx_global_int_buf.v
   wire			rst_l_buf6_middle;	// From buf_global_middle6 of ccx_global_int_buf.v
   wire			se;			// From ccx_test_stub of test_stub_scan.v
   wire			se_buf0_middle;		// From buf_global_middle0 of ccx_global_int_buf.v
   wire			se_buf1_bottom;		// From buf_global_bottom1 of ccx_global_int_buf.v
   wire			se_buf1_middle;		// From buf_global_middle1 of ccx_global_int_buf.v
   wire			se_buf1_top;		// From buf_global_top1 of ccx_global_int_buf.v
   wire			se_buf2_bottom;		// From buf_global_bottom2 of ccx_global_int_buf.v
   wire			se_buf2_middle;		// From buf_global_middle2 of ccx_global_int_buf.v
   wire			se_buf2_top;		// From buf_global_top2 of ccx_global_int_buf.v
   wire			se_buf3_bottom;		// From buf_global_bottom3 of ccx_global_int_buf.v
   wire			se_buf3_middle;		// From buf_global_middle3 of ccx_global_int_buf.v
   wire			se_buf3_top;		// From buf_global_top3 of ccx_global_int_buf.v
   wire			se_buf4_bottom;		// From buf_global_bottom4 of ccx_global_int_buf.v
   wire			se_buf4_middle;		// From buf_global_middle4 of ccx_global_int_buf.v
   wire			se_buf4_top;		// From buf_global_top4 of ccx_global_int_buf.v
   wire			se_buf5_bottom;		// From buf_global_bottom5 of ccx_global_int_buf.v
   wire			se_buf5_middle;		// From buf_global_middle5 of ccx_global_int_buf.v
   wire			se_buf5_top;		// From buf_global_top5 of ccx_global_int_buf.v
   wire			se_buf6_middle;		// From buf_global_middle6 of ccx_global_int_buf.v
   // End of automatics

   //wire shiftenable, tmb_l;
   
   //assign shiftenable = 1'b0;
   //assign tmb_l = 1'b1;

/*   bw_clk_cl_ccx_cmp AUTO_TEMPLATE(
                           //Inputs
                           .arst2_l      (arst_l_buf_fpio_inff),
                           .arst_l       (arst_l_buf_fpio_inff),
                           .grst_l       (cmp_grst_l),
                           .cluster_cken (clk_ccx_cken),
                           .si      (pcx_scache0_dat_px2_so_1),
                           .se      (se_buf5_middle),
                           .se2     (se_buf2_middle),
		           .adbginit_l(adbginit_l_buf5_middle),
                           // Outputs
                           .so      (ccx_clk_hdr_so_1),
                           .dbginit_l    (ccx_gdbginit_l),
                           .cluster_grst_l   ());
 */


    bw_clk_cl_ccx_cmp  ccx_hdr(/*AUTOINST*/
			       // Outputs
			       .so	(ccx_clk_hdr_so_1),	 // Templated
			       .dbginit_l(ccx_gdbginit_l),	 // Templated
			       .cluster_grst_l(),		 // Templated
			       .rclk	(rclk),
			       // Inputs
			       .grst_l	(cmp_grst_l),		 // Templated
			       .gdbginit_l(gdbginit_l),
			       .gclk	(gclk[1:0]),
			       .si	(pcx_scache0_dat_px2_so_1), // Templated
			       .se	(se_buf5_middle),	 // Templated
			       .se2	(se_buf2_middle),	 // Templated
			       .adbginit_l(adbginit_l_buf5_middle), // Templated
			       .arst_l	(arst_l_buf_fpio_inff),	 // Templated
			       .arst2_l	(arst_l_buf_fpio_inff),	 // Templated
			       .cluster_cken(clk_ccx_cken));	 // Templated
/*   test_stub_scan AUTO_TEMPLATE(
                           //Outputs
                           //.rst_tri_en(),
                           //.tst_ctu_data_out(),
                           .mux_drive_disable(),
                           .mem_write_disable(),
                           .mem_bypass(),
                           .macrotest(),
                           .sehold(),
			   .so_0(ccx_scanout0),
			   .so_1(ccx_scanout1),
                           .so_2(),
			   .testmode_l(),
                           //Inputs
                           //.ctu_tst_write_enable(ctu_ccx_tst_wen),
                           //.ctu_tst_data_in(ctu_ccx_tst_data_in[2:0]),
                           //.cluster_grst_l(ccx_grst_l),
                           .long_chain_so_0(cpx_dp_half_array_odd_so_0),  // connect ccx scanout chain0
                           .long_chain_so_1(pcx_iodata_px2_so_1),  // connect ccx scanout chain1
                           .long_chain_so_2(1'b0),
                           .short_chain_so_0(1'b0),
                           .short_chain_so_1(1'b0),
                           .short_chain_so_2(1'b0),
                           .arst_l (cmp_arst_l));
*/

     test_stub_scan  ccx_test_stub(/*AUTOINST*/
				   // Outputs
				   .mux_drive_disable(),	 // Templated
				   .mem_write_disable(),	 // Templated
				   .sehold(),			 // Templated
				   .se	(se),
				   .testmode_l(),		 // Templated
				   .mem_bypass(),		 // Templated
				   .so_0(ccx_scanout0),		 // Templated
				   .so_1(ccx_scanout1),		 // Templated
				   .so_2(),			 // Templated
				   // Inputs
				   .ctu_tst_pre_grst_l(ctu_tst_pre_grst_l),
				   .arst_l(cmp_arst_l),		 // Templated
				   .global_shift_enable(global_shift_enable),
				   .ctu_tst_scan_disable(ctu_tst_scan_disable),
				   .ctu_tst_scanmode(ctu_tst_scanmode),
				   .ctu_tst_macrotest(ctu_tst_macrotest),
				   .ctu_tst_short_chain(ctu_tst_short_chain),
				   .long_chain_so_0(cpx_dp_half_array_odd_so_0), // Templated
				   .short_chain_so_0(1'b0),	 // Templated
				   .long_chain_so_1(pcx_iodata_px2_so_1), // Templated
				   .short_chain_so_1(1'b0),	 // Templated
				   .long_chain_so_2(1'b0),	 // Templated
				   .short_chain_so_2(1'b0));	 // Templated
/*   cpx AUTO_TEMPLATE(
             //Outputs
	    .cpx_io_grant_cx2		(cpx_iob_grant_cx2[7:0]),
             //Inputs
            .si_0                       (pcx_buf_top_pt0_so_0),
            .si_1                       (ccx_scanin1),
	    .io_cpx_req_cq		(iob_cpx_req_cq[7:0]),
	    .io_cpx_data_ca		(iob_cpx_data_ca[`CPX_WIDTH-1:0]),
             //.tmb_l(testmode_l),
             //.rst_l(ccx_gdbginit_l),
             //.shiftenable(se));

*/
 
   cpx cpx (/*AUTOINST*/
	    // Outputs
	    .cpx_io_grant_cx2		(cpx_iob_grant_cx2[7:0]), // Templated
	    .cpx_sctag0_grant_cx	(cpx_sctag0_grant_cx[7:0]),
	    .cpx_sctag1_grant_cx	(cpx_sctag1_grant_cx[7:0]),
	    .cpx_sctag2_grant_cx	(cpx_sctag2_grant_cx[7:0]),
	    .cpx_sctag3_grant_cx	(cpx_sctag3_grant_cx[7:0]),
	    .cpx_spc0_data_cx2		(cpx_spc0_data_cx2[`CPX_WIDTH-1:0]),
	    .cpx_spc0_data_rdy_cx2	(cpx_spc0_data_rdy_cx2),
	    .cpx_spc1_data_cx2		(cpx_spc1_data_cx2[`CPX_WIDTH-1:0]),
	    .cpx_spc1_data_rdy_cx2	(cpx_spc1_data_rdy_cx2),
	    .cpx_spc2_data_cx2		(cpx_spc2_data_cx2[`CPX_WIDTH-1:0]),
	    .cpx_spc2_data_rdy_cx2	(cpx_spc2_data_rdy_cx2),
	    .cpx_spc3_data_cx2		(cpx_spc3_data_cx2[`CPX_WIDTH-1:0]),
	    .cpx_spc3_data_rdy_cx2	(cpx_spc3_data_rdy_cx2),
	    .cpx_spc4_data_cx2		(cpx_spc4_data_cx2[`CPX_WIDTH-1:0]),
	    .cpx_spc4_data_rdy_cx2	(cpx_spc4_data_rdy_cx2),
	    .cpx_spc5_data_cx2		(cpx_spc5_data_cx2[`CPX_WIDTH-1:0]),
	    .cpx_spc5_data_rdy_cx2	(cpx_spc5_data_rdy_cx2),
	    .cpx_spc6_data_cx2		(cpx_spc6_data_cx2[`CPX_WIDTH-1:0]),
	    .cpx_spc6_data_rdy_cx2	(cpx_spc6_data_rdy_cx2),
	    .cpx_spc7_data_cx2		(cpx_spc7_data_cx2[`CPX_WIDTH-1:0]),
	    .cpx_spc7_data_rdy_cx2	(cpx_spc7_data_rdy_cx2),
	    .cpx_dp_half_array_odd_so_0	(cpx_dp_half_array_odd_so_0),
	    .cpx_arb7_so_1		(cpx_arb7_so_1),
	    .pt1_so_1			(pt1_so_1),
	    .cpx_buf_top_pt0_so_1	(cpx_buf_top_pt0_so_1),
	    // Inputs
	    .adbginit_l_buf3_middle	(adbginit_l_buf3_middle),
	    .adbginit_l_buf4_middle	(adbginit_l_buf4_middle),
	    .adbginit_l_buf5_middle	(adbginit_l_buf5_middle),
	    .adbginit_l_buf6_middle	(adbginit_l_buf6_middle),
	    .fp_cpx_req_cq		(fp_cpx_req_cq[7:0]),
	    .io_cpx_req_cq		(iob_cpx_req_cq[7:0]),	 // Templated
	    .pcx_scache1_dat_px2_so_1	(pcx_scache1_dat_px2_so_1),
	    .pcx_scache2_dat_px2_so_1	(pcx_scache2_dat_px2_so_1),
	    .rclk			(rclk),
	    .rst_l_buf3_middle		(rst_l_buf3_middle),
	    .rst_l_buf4_middle		(rst_l_buf4_middle),
	    .rst_l_buf5_middle		(rst_l_buf5_middle),
	    .rst_l_buf6_middle		(rst_l_buf6_middle),
	    .sctag0_cpx_atom_cq		(sctag0_cpx_atom_cq),
	    .sctag0_cpx_req_cq		(sctag0_cpx_req_cq[7:0]),
	    .sctag1_cpx_atom_cq		(sctag1_cpx_atom_cq),
	    .sctag1_cpx_req_cq		(sctag1_cpx_req_cq[7:0]),
	    .sctag2_cpx_atom_cq		(sctag2_cpx_atom_cq),
	    .sctag2_cpx_req_cq		(sctag2_cpx_req_cq[7:0]),
	    .sctag3_cpx_atom_cq		(sctag3_cpx_atom_cq),
	    .sctag3_cpx_req_cq		(sctag3_cpx_req_cq[7:0]),
	    .se_buf0_middle		(se_buf0_middle),
	    .se_buf1_bottom		(se_buf1_bottom),
	    .se_buf1_top		(se_buf1_top),
	    .se_buf2_bottom		(se_buf2_bottom),
	    .se_buf2_top		(se_buf2_top),
	    .se_buf3_middle		(se_buf3_middle),
	    .se_buf3_top		(se_buf3_top),
	    .se_buf4_bottom		(se_buf4_bottom),
	    .se_buf4_middle		(se_buf4_middle),
	    .se_buf4_top		(se_buf4_top),
	    .se_buf5_middle		(se_buf5_middle),
	    .se_buf6_middle		(se_buf6_middle),
	    .si_0			(pcx_buf_top_pt0_so_0),	 // Templated
	    .si_1			(ccx_scanin1),		 // Templated
	    .sctag3_cpx_data_ca		(sctag3_cpx_data_ca[`CPX_WIDTH-1:0]),
	    .sctag2_cpx_data_ca		(sctag2_cpx_data_ca[`CPX_WIDTH-1:0]),
	    .sctag1_cpx_data_ca		(sctag1_cpx_data_ca[`CPX_WIDTH-1:0]),
	    .sctag0_cpx_data_ca		(sctag0_cpx_data_ca[`CPX_WIDTH-1:0]),
	    .io_cpx_data_ca		(iob_cpx_data_ca[`CPX_WIDTH-1:0]), // Templated
	    .fp_cpx_data_ca		(fp_cpx_data_ca[`CPX_WIDTH-1:0]));

/*   pcx AUTO_TEMPLATE(
             //Outputs
	    .pcx_io_data_px2		(pcx_iob_data_px2[`PCX_WIDTH-1:0]),
	    .pcx_io_data_rdy_px2	(pcx_iob_data_rdy_px2),
	    .pcx_fpio_data_px2		(pcx_fp_data_px2[`PCX_WIDTH-1:0]),
	    .pcx_fpio_data_rdy_px2	(pcx_fp_data_rdy_px2),
             //Inputs
            .si_0                       (ccx_scanin0),
            .si_1                       (cpx_arb7_so_1),
	    .io_pcx_stall_pq		(iob_pcx_stall_pq),
             //.tmb_l(testmode_l),
             //.rst_l(ccx_gdbginit_l),
             //.shiftenable(se));
*/

   pcx pcx (/*AUTOINST*/
	    // Outputs
	    .arst_l_buf_fpio_inff	(arst_l_buf_fpio_inff),
	    .pcx_buf_top_pt0_so_0	(pcx_buf_top_pt0_so_0),
	    .pcx_fpio_data_px2		(pcx_fp_data_px2[`PCX_WIDTH-1:0]), // Templated
	    .pcx_fpio_data_rdy_px2	(pcx_fp_data_rdy_px2),	 // Templated
	    .pcx_io_data_px2		(pcx_iob_data_px2[`PCX_WIDTH-1:0]), // Templated
	    .pcx_io_data_rdy_px2	(pcx_iob_data_rdy_px2),	 // Templated
	    .pcx_iodata_px2_so_1	(pcx_iodata_px2_so_1),
	    .pcx_scache0_dat_px2_so_1	(pcx_scache0_dat_px2_so_1),
	    .pcx_scache1_dat_px2_so_1	(pcx_scache1_dat_px2_so_1),
	    .pcx_scache2_dat_px2_so_1	(pcx_scache2_dat_px2_so_1),
	    .pcx_sctag0_atm_px1		(pcx_sctag0_atm_px1),
	    .pcx_sctag0_data_px2	(pcx_sctag0_data_px2[`PCX_WIDTH-1:0]),
	    .pcx_sctag0_data_rdy_px1	(pcx_sctag0_data_rdy_px1),
	    .pcx_sctag1_atm_px1		(pcx_sctag1_atm_px1),
	    .pcx_sctag1_data_px2	(pcx_sctag1_data_px2[`PCX_WIDTH-1:0]),
	    .pcx_sctag1_data_rdy_px1	(pcx_sctag1_data_rdy_px1),
	    .pcx_sctag2_atm_px1		(pcx_sctag2_atm_px1),
	    .pcx_sctag2_data_px2	(pcx_sctag2_data_px2[`PCX_WIDTH-1:0]),
	    .pcx_sctag2_data_rdy_px1	(pcx_sctag2_data_rdy_px1),
	    .pcx_sctag3_atm_px1		(pcx_sctag3_atm_px1),
	    .pcx_sctag3_data_px2	(pcx_sctag3_data_px2[`PCX_WIDTH-1:0]),
	    .pcx_sctag3_data_rdy_px1	(pcx_sctag3_data_rdy_px1),
	    .pcx_spc0_grant_px		(pcx_spc0_grant_px[4:0]),
	    .pcx_spc1_grant_px		(pcx_spc1_grant_px[4:0]),
	    .pcx_spc2_grant_px		(pcx_spc2_grant_px[4:0]),
	    .pcx_spc3_grant_px		(pcx_spc3_grant_px[4:0]),
	    .pcx_spc4_grant_px		(pcx_spc4_grant_px[4:0]),
	    .pcx_spc5_grant_px		(pcx_spc5_grant_px[4:0]),
	    .pcx_spc6_grant_px		(pcx_spc6_grant_px[4:0]),
	    .pcx_spc7_grant_px		(pcx_spc7_grant_px[4:0]),
	    // Inputs
	    .spc0_pcx_data_pa		(spc0_pcx_data_pa[`PCX_WIDTH-1:0]),
	    .spc1_pcx_data_pa		(spc1_pcx_data_pa[`PCX_WIDTH-1:0]),
	    .spc2_pcx_data_pa		(spc2_pcx_data_pa[`PCX_WIDTH-1:0]),
	    .spc3_pcx_data_pa		(spc3_pcx_data_pa[`PCX_WIDTH-1:0]),
	    .spc4_pcx_data_pa		(spc4_pcx_data_pa[`PCX_WIDTH-1:0]),
	    .spc5_pcx_data_pa		(spc5_pcx_data_pa[`PCX_WIDTH-1:0]),
	    .spc6_pcx_data_pa		(spc6_pcx_data_pa[`PCX_WIDTH-1:0]),
	    .spc7_pcx_data_pa		(spc7_pcx_data_pa[`PCX_WIDTH-1:0]),
	    .adbginit_l_buf1_middle	(adbginit_l_buf1_middle),
	    .adbginit_l_buf2_middle	(adbginit_l_buf2_middle),
	    .ccx_clk_hdr_so_1		(ccx_clk_hdr_so_1),
	    .cmp_arst_l			(cmp_arst_l),
	    .cpx_buf_top_pt0_so_1	(cpx_buf_top_pt0_so_1),
	    .io_pcx_stall_pq		(iob_pcx_stall_pq),	 // Templated
	    .pt1_so_1			(pt1_so_1),
	    .rclk			(rclk),
	    .rst_l_buf1_middle		(rst_l_buf1_middle),
	    .rst_l_buf2_middle		(rst_l_buf2_middle),
	    .sctag0_pcx_stall_pq	(sctag0_pcx_stall_pq),
	    .sctag1_pcx_stall_pq	(sctag1_pcx_stall_pq),
	    .sctag2_pcx_stall_pq	(sctag2_pcx_stall_pq),
	    .sctag3_pcx_stall_pq	(sctag3_pcx_stall_pq),
	    .se_buf0_middle		(se_buf0_middle),
	    .se_buf1_bottom		(se_buf1_bottom),
	    .se_buf1_middle		(se_buf1_middle),
	    .se_buf1_top		(se_buf1_top),
	    .se_buf2_bottom		(se_buf2_bottom),
	    .se_buf2_middle		(se_buf2_middle),
	    .se_buf2_top		(se_buf2_top),
	    .se_buf3_bottom		(se_buf3_bottom),
	    .se_buf3_middle		(se_buf3_middle),
	    .se_buf3_top		(se_buf3_top),
	    .se_buf4_bottom		(se_buf4_bottom),
	    .se_buf4_top		(se_buf4_top),
	    .se_buf5_bottom		(se_buf5_bottom),
	    .se_buf5_top		(se_buf5_top),
	    .si_0			(ccx_scanin0),		 // Templated
	    .si_1			(cpx_arb7_so_1),	 // Templated
	    .spc0_pcx_atom_pq		(spc0_pcx_atom_pq),
	    .spc0_pcx_req_pq		(spc0_pcx_req_pq[4:0]),
	    .spc1_pcx_atom_pq		(spc1_pcx_atom_pq),
	    .spc1_pcx_req_pq		(spc1_pcx_req_pq[4:0]),
	    .spc2_pcx_atom_pq		(spc2_pcx_atom_pq),
	    .spc2_pcx_req_pq		(spc2_pcx_req_pq[4:0]),
	    .spc3_pcx_atom_pq		(spc3_pcx_atom_pq),
	    .spc3_pcx_req_pq		(spc3_pcx_req_pq[4:0]),
	    .spc4_pcx_atom_pq		(spc4_pcx_atom_pq),
	    .spc4_pcx_req_pq		(spc4_pcx_req_pq[4:0]),
	    .spc5_pcx_atom_pq		(spc5_pcx_atom_pq),
	    .spc5_pcx_req_pq		(spc5_pcx_req_pq[4:0]),
	    .spc6_pcx_atom_pq		(spc6_pcx_atom_pq),
	    .spc6_pcx_req_pq		(spc6_pcx_req_pq[4:0]),
	    .spc7_pcx_atom_pq		(spc7_pcx_atom_pq),
	    .spc7_pcx_req_pq		(spc7_pcx_req_pq[4:0]));


/*  ccx_global_int_buf   AUTO_TEMPLATE(
			    // Outputs
			    .rst_l_buf	(),
			    .se_buf	(se_buf1_top),
                            .adbginit_l_buf (),
			    // Inputs
                            .adbginit_l (1'b1),
			    .rst_l	(1'b1),
			    .se		(se)); 
*/

  ccx_global_int_buf   buf_global_top1(/*AUTOINST*/
				       // Outputs
				       .rst_l_buf(),		 // Templated
				       .se_buf(se_buf1_top),	 // Templated
				       .adbginit_l_buf(),	 // Templated
				       // Inputs
				       .rst_l(1'b1),		 // Templated
				       .se(se),			 // Templated
				       .adbginit_l(1'b1));	 // Templated
/*  ccx_global_int_buf   AUTO_TEMPLATE(
			    // Outputs
			    .rst_l_buf	(),
			    .se_buf	(se_buf@_top),
                            .adbginit_l_buf (),
			    // Inputs
                            .adbginit_l (1'b1),
			    .rst_l	(1'b1),
			    .se		(se_buf@"(- @ 1)"_top)); 
*/

  ccx_global_int_buf   buf_global_top2(/*AUTOINST*/
				       // Outputs
				       .rst_l_buf(),		 // Templated
				       .se_buf(se_buf2_top),	 // Templated
				       .adbginit_l_buf(),	 // Templated
				       // Inputs
				       .rst_l(1'b1),		 // Templated
				       .se(se_buf1_top),	 // Templated
				       .adbginit_l(1'b1));	 // Templated
  ccx_global_int_buf   buf_global_top3(/*AUTOINST*/
				       // Outputs
				       .rst_l_buf(),		 // Templated
				       .se_buf(se_buf3_top),	 // Templated
				       .adbginit_l_buf(),	 // Templated
				       // Inputs
				       .rst_l(1'b1),		 // Templated
				       .se(se_buf2_top),	 // Templated
				       .adbginit_l(1'b1));	 // Templated
  ccx_global_int_buf   buf_global_top4(/*AUTOINST*/
				       // Outputs
				       .rst_l_buf(),		 // Templated
				       .se_buf(se_buf4_top),	 // Templated
				       .adbginit_l_buf(),	 // Templated
				       // Inputs
				       .rst_l(1'b1),		 // Templated
				       .se(se_buf3_top),	 // Templated
				       .adbginit_l(1'b1));	 // Templated
  ccx_global_int_buf   buf_global_top5(/*AUTOINST*/
				       // Outputs
				       .rst_l_buf(),		 // Templated
				       .se_buf(se_buf5_top),	 // Templated
				       .adbginit_l_buf(),	 // Templated
				       // Inputs
				       .rst_l(1'b1),		 // Templated
				       .se(se_buf4_top),	 // Templated
				       .adbginit_l(1'b1));	 // Templated
/*  ccx_global_int_buf   AUTO_TEMPLATE(
			    // Outputs
			    .rst_l_buf	(),
			    .se_buf	(se_buf1_bottom),
                            .adbginit_l_buf (),
			    // Inputs
                            .adbginit_l (1'b1),
			    .rst_l	(1'b1),
			    .se		(se)); 
*/
  ccx_global_int_buf   buf_global_bottom1(/*AUTOINST*/
					  // Outputs
					  .rst_l_buf(),		 // Templated
					  .se_buf(se_buf1_bottom), // Templated
					  .adbginit_l_buf(),	 // Templated
					  // Inputs
					  .rst_l(1'b1),		 // Templated
					  .se(se),		 // Templated
					  .adbginit_l(1'b1));	 // Templated
/*  ccx_global_int_buf   AUTO_TEMPLATE(
			    // Outputs
			    .rst_l_buf	(),
			    .se_buf	(se_buf@_bottom),
                            .adbginit_l_buf (),
			    // Inputs
                            .adbginit_l (1'b1),
			    .rst_l	(1'b1),
			    .se		(se_buf@"(- @ 1)"_bottom)); 
*/

  ccx_global_int_buf   buf_global_bottom2(/*AUTOINST*/
					  // Outputs
					  .rst_l_buf(),		 // Templated
					  .se_buf(se_buf2_bottom), // Templated
					  .adbginit_l_buf(),	 // Templated
					  // Inputs
					  .rst_l(1'b1),		 // Templated
					  .se(se_buf1_bottom),	 // Templated
					  .adbginit_l(1'b1));	 // Templated
  ccx_global_int_buf   buf_global_bottom3(/*AUTOINST*/
					  // Outputs
					  .rst_l_buf(),		 // Templated
					  .se_buf(se_buf3_bottom), // Templated
					  .adbginit_l_buf(),	 // Templated
					  // Inputs
					  .rst_l(1'b1),		 // Templated
					  .se(se_buf2_bottom),	 // Templated
					  .adbginit_l(1'b1));	 // Templated
  ccx_global_int_buf   buf_global_bottom4(/*AUTOINST*/
					  // Outputs
					  .rst_l_buf(),		 // Templated
					  .se_buf(se_buf4_bottom), // Templated
					  .adbginit_l_buf(),	 // Templated
					  // Inputs
					  .rst_l(1'b1),		 // Templated
					  .se(se_buf3_bottom),	 // Templated
					  .adbginit_l(1'b1));	 // Templated
  ccx_global_int_buf   buf_global_bottom5(/*AUTOINST*/
					  // Outputs
					  .rst_l_buf(),		 // Templated
					  .se_buf(se_buf5_bottom), // Templated
					  .adbginit_l_buf(),	 // Templated
					  // Inputs
					  .rst_l(1'b1),		 // Templated
					  .se(se_buf4_bottom),	 // Templated
					  .adbginit_l(1'b1));	 // Templated
/*  ccx_global_int_buf   AUTO_TEMPLATE(
			    // Outputs
			    .rst_l_buf	(),
			    .se_buf	(se_buf0_middle),
                            .adbginit_l_buf (adbginit_l_buf0_middle),
			    // Inputs
                            .adbginit_l (adbginit_l),
			    .rst_l	(1'b1),
			    .se		(se)); 
*/

  ccx_global_int_buf    buf_global_middle0(/*AUTOINST*/
					   // Outputs
					   .rst_l_buf(),	 // Templated
					   .se_buf(se_buf0_middle), // Templated
					   .adbginit_l_buf(adbginit_l_buf0_middle), // Templated
					   // Inputs
					   .rst_l(1'b1),	 // Templated
					   .se(se),		 // Templated
					   .adbginit_l(adbginit_l)); // Templated
/*  ccx_global_int_buf   AUTO_TEMPLATE(
			    // Outputs
			    .rst_l_buf	(rst_l_buf@_middle),
			    .se_buf	(se_buf@_middle),
                            .adbginit_l_buf (adbginit_l_buf@_middle),
			    // Inputs
                            .adbginit_l (adbginit_l_buf@"(- @ 1)"_middle),
			    .rst_l	(rst_l_buf@"(+ @ 1)"_middle),
			    .se		(se_buf@"(- @ 1)"_middle)); 
*/

  ccx_global_int_buf   buf_global_middle1(/*AUTOINST*/
					  // Outputs
					  .rst_l_buf(rst_l_buf1_middle), // Templated
					  .se_buf(se_buf1_middle), // Templated
					  .adbginit_l_buf(adbginit_l_buf1_middle), // Templated
					  // Inputs
					  .rst_l(rst_l_buf2_middle), // Templated
					  .se(se_buf0_middle),	 // Templated
					  .adbginit_l(adbginit_l_buf0_middle)); // Templated
  ccx_global_int_buf   buf_global_middle2(/*AUTOINST*/
					  // Outputs
					  .rst_l_buf(rst_l_buf2_middle), // Templated
					  .se_buf(se_buf2_middle), // Templated
					  .adbginit_l_buf(adbginit_l_buf2_middle), // Templated
					  // Inputs
					  .rst_l(rst_l_buf3_middle), // Templated
					  .se(se_buf1_middle),	 // Templated
					  .adbginit_l(adbginit_l_buf1_middle)); // Templated
  ccx_global_int_buf   buf_global_middle3(/*AUTOINST*/
					  // Outputs
					  .rst_l_buf(rst_l_buf3_middle), // Templated
					  .se_buf(se_buf3_middle), // Templated
					  .adbginit_l_buf(adbginit_l_buf3_middle), // Templated
					  // Inputs
					  .rst_l(rst_l_buf4_middle), // Templated
					  .se(se_buf2_middle),	 // Templated
					  .adbginit_l(adbginit_l_buf2_middle)); // Templated
  ccx_global_int_buf   buf_global_middle4(/*AUTOINST*/
					  // Outputs
					  .rst_l_buf(rst_l_buf4_middle), // Templated
					  .se_buf(se_buf4_middle), // Templated
					  .adbginit_l_buf(adbginit_l_buf4_middle), // Templated
					  // Inputs
					  .rst_l(rst_l_buf5_middle), // Templated
					  .se(se_buf3_middle),	 // Templated
					  .adbginit_l(adbginit_l_buf3_middle)); // Templated
  ccx_global_int_buf   buf_global_middle5(/*AUTOINST*/
					  // Outputs
					  .rst_l_buf(rst_l_buf5_middle), // Templated
					  .se_buf(se_buf5_middle), // Templated
					  .adbginit_l_buf(adbginit_l_buf5_middle), // Templated
					  // Inputs
					  .rst_l(rst_l_buf6_middle), // Templated
					  .se(se_buf4_middle),	 // Templated
					  .adbginit_l(adbginit_l_buf4_middle)); // Templated
/*  ccx_global_int_buf   AUTO_TEMPLATE(
			    // Outputs
			    .rst_l_buf	(rst_l_buf@_middle),
			    .se_buf	(se_buf@_middle),
                            .adbginit_l_buf (adbginit_l_buf@_middle),
			    // Inputs
                            .adbginit_l (adbginit_l_buf@"(- @ 1)"_middle),
			    .rst_l	(ccx_gdbginit_l),
			    .se		(se_buf@"(- @ 1)"_middle)); 
*/

  ccx_global_int_buf   buf_global_middle6(/*AUTOINST*/
					  // Outputs
					  .rst_l_buf(rst_l_buf6_middle), // Templated
					  .se_buf(se_buf6_middle), // Templated
					  .adbginit_l_buf(adbginit_l_buf6_middle), // Templated
					  // Inputs
					  .rst_l(ccx_gdbginit_l), // Templated
					  .se(se_buf5_middle),	 // Templated
					  .adbginit_l(adbginit_l_buf5_middle)); // Templated
endmodule // ccx

// Local Variables:
// verilog-library-directories:("." "../cpx/rtl" "../pcx/rtl" "../../../../common/rtl" "../../common/rtl")
// End:
