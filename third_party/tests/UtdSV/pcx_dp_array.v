// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: pcx_dp_array.v
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
////////////////////////////////////////////////////////////////////////
/*
//	Description:	datapath portion of CPX
*/
////////////////////////////////////////////////////////////////////////
// Global header file includes
////////////////////////////////////////////////////////////////////////

`include	"sys.h" // system level definition file which contains the 
			// time scale definition

`include "iop.h"


////////////////////////////////////////////////////////////////////////
// Local header file includes / local defines
////////////////////////////////////////////////////////////////////////
 

module pcx_dp_array(/*AUTOARG*/
   // Outputs
   pcx_scache3_data_px_l, pcx_scache2_data_px_l, 
   pcx_scache1_data_px_l, pcx_scache0_data_px_l, pcx_fpio_data_px_l, 
   pcx_dp_array134_so_0, pcx_dp_array02_so_1, 
   // Inputs
   spc7_pcx_data_pa, spc6_pcx_data_pa, spc5_pcx_data_pa, 
   spc4_pcx_data_pa, spc3_pcx_data_pa, spc2_pcx_data_pa, 
   spc1_pcx_data_pa, spc0_pcx_data_pa, si_1, si_0, se_buf1_top, 
   se_buf1_bottom, rclk, arbpc4_pcxdp_shift_px, 
   arbpc4_pcxdp_qsel1_pa, arbpc4_pcxdp_qsel0_pa, 
   arbpc4_pcxdp_q0_hold_pa, arbpc4_pcxdp_grant_pa, 
   arbpc3_pcxdp_shift_px, arbpc3_pcxdp_qsel1_pa, 
   arbpc3_pcxdp_qsel0_pa, arbpc3_pcxdp_q0_hold_pa, 
   arbpc3_pcxdp_grant_pa, arbpc2_pcxdp_shift_px, 
   arbpc2_pcxdp_qsel1_pa, arbpc2_pcxdp_qsel0_pa, 
   arbpc2_pcxdp_q0_hold_pa, arbpc2_pcxdp_grant_pa, 
   arbpc1_pcxdp_shift_px, arbpc1_pcxdp_qsel1_pa, 
   arbpc1_pcxdp_qsel0_pa, arbpc1_pcxdp_q0_hold_pa, 
   arbpc1_pcxdp_grant_pa, arbpc0_pcxdp_shift_px, 
   arbpc0_pcxdp_qsel1_pa, arbpc0_pcxdp_qsel0_pa, 
   arbpc0_pcxdp_q0_hold_pa, arbpc0_pcxdp_grant_pa
   );

   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output		pcx_dp_array02_so_1;	// From pcx_dp_array02 of pcx_dp_array02.v
   output		pcx_dp_array134_so_0;	// From pcx_dp_array134 of pcx_dp_array134.v
   output [`PCX_WIDTH-1:0]pcx_fpio_data_px_l;	// From pcx_dp_array134 of pcx_dp_array134.v
   output [`PCX_WIDTH-1:0]pcx_scache0_data_px_l;// From pcx_dp_array02 of pcx_dp_array02.v
   output [`PCX_WIDTH-1:0]pcx_scache1_data_px_l;// From pcx_dp_array134 of pcx_dp_array134.v
   output [`PCX_WIDTH-1:0]pcx_scache2_data_px_l;// From pcx_dp_array02 of pcx_dp_array02.v
   output [`PCX_WIDTH-1:0]pcx_scache3_data_px_l;// From pcx_dp_array134 of pcx_dp_array134.v
   // End of automatics

   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input [7:0]		arbpc0_pcxdp_grant_pa;	// To pcx_dp_array02 of pcx_dp_array02.v
   input [7:0]		arbpc0_pcxdp_q0_hold_pa;// To pcx_dp_array02 of pcx_dp_array02.v
   input [7:0]		arbpc0_pcxdp_qsel0_pa;	// To pcx_dp_array02 of pcx_dp_array02.v
   input [7:0]		arbpc0_pcxdp_qsel1_pa;	// To pcx_dp_array02 of pcx_dp_array02.v
   input [7:0]		arbpc0_pcxdp_shift_px;	// To pcx_dp_array02 of pcx_dp_array02.v
   input [7:0]		arbpc1_pcxdp_grant_pa;	// To pcx_dp_array134 of pcx_dp_array134.v
   input [7:0]		arbpc1_pcxdp_q0_hold_pa;// To pcx_dp_array134 of pcx_dp_array134.v
   input [7:0]		arbpc1_pcxdp_qsel0_pa;	// To pcx_dp_array134 of pcx_dp_array134.v
   input [7:0]		arbpc1_pcxdp_qsel1_pa;	// To pcx_dp_array134 of pcx_dp_array134.v
   input [7:0]		arbpc1_pcxdp_shift_px;	// To pcx_dp_array134 of pcx_dp_array134.v
   input [7:0]		arbpc2_pcxdp_grant_pa;	// To pcx_dp_array02 of pcx_dp_array02.v
   input [7:0]		arbpc2_pcxdp_q0_hold_pa;// To pcx_dp_array02 of pcx_dp_array02.v
   input [7:0]		arbpc2_pcxdp_qsel0_pa;	// To pcx_dp_array02 of pcx_dp_array02.v
   input [7:0]		arbpc2_pcxdp_qsel1_pa;	// To pcx_dp_array02 of pcx_dp_array02.v
   input [7:0]		arbpc2_pcxdp_shift_px;	// To pcx_dp_array02 of pcx_dp_array02.v
   input [7:0]		arbpc3_pcxdp_grant_pa;	// To pcx_dp_array134 of pcx_dp_array134.v
   input [7:0]		arbpc3_pcxdp_q0_hold_pa;// To pcx_dp_array134 of pcx_dp_array134.v
   input [7:0]		arbpc3_pcxdp_qsel0_pa;	// To pcx_dp_array134 of pcx_dp_array134.v
   input [7:0]		arbpc3_pcxdp_qsel1_pa;	// To pcx_dp_array134 of pcx_dp_array134.v
   input [7:0]		arbpc3_pcxdp_shift_px;	// To pcx_dp_array134 of pcx_dp_array134.v
   input [7:0]		arbpc4_pcxdp_grant_pa;	// To pcx_dp_array134 of pcx_dp_array134.v
   input [7:0]		arbpc4_pcxdp_q0_hold_pa;// To pcx_dp_array134 of pcx_dp_array134.v
   input [7:0]		arbpc4_pcxdp_qsel0_pa;	// To pcx_dp_array134 of pcx_dp_array134.v
   input [7:0]		arbpc4_pcxdp_qsel1_pa;	// To pcx_dp_array134 of pcx_dp_array134.v
   input [7:0]		arbpc4_pcxdp_shift_px;	// To pcx_dp_array134 of pcx_dp_array134.v
   input		rclk;			// To pcx_dp_array02 of pcx_dp_array02.v, ...
   input		se_buf1_bottom;		// To pcx_dp_array134 of pcx_dp_array134.v
   input		se_buf1_top;		// To pcx_dp_array02 of pcx_dp_array02.v
   input		si_0;			// To pcx_dp_array134 of pcx_dp_array134.v
   input		si_1;			// To pcx_dp_array02 of pcx_dp_array02.v
   input [`PCX_WIDTH-1:0]spc0_pcx_data_pa;	// To pcx_dp_array02 of pcx_dp_array02.v, ...
   input [`PCX_WIDTH-1:0]spc1_pcx_data_pa;	// To pcx_dp_array02 of pcx_dp_array02.v, ...
   input [`PCX_WIDTH-1:0]spc2_pcx_data_pa;	// To pcx_dp_array02 of pcx_dp_array02.v, ...
   input [`PCX_WIDTH-1:0]spc3_pcx_data_pa;	// To pcx_dp_array02 of pcx_dp_array02.v, ...
   input [`PCX_WIDTH-1:0]spc4_pcx_data_pa;	// To pcx_dp_array02 of pcx_dp_array02.v, ...
   input [`PCX_WIDTH-1:0]spc5_pcx_data_pa;	// To pcx_dp_array02 of pcx_dp_array02.v, ...
   input [`PCX_WIDTH-1:0]spc6_pcx_data_pa;	// To pcx_dp_array02 of pcx_dp_array02.v, ...
   input [`PCX_WIDTH-1:0]spc7_pcx_data_pa;	// To pcx_dp_array02 of pcx_dp_array02.v, ...
   // End of automatics

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   // End of automatics

   //input  scan_in;
   //output  scan_out;
   
       /*
   pcx_dp_array02 AUTO_TEMPLATE(
			  .shiftenable(se_buf1_top),
			  .scan_out	(pcx_dp_array02_so_1),
			  .scan_in	(si_1));
*/                 
                 
   pcx_dp_array02 pcx_dp_array02(/*AUTOINST*/
				 // Outputs
				 .pcx_scache0_data_px_l(pcx_scache0_data_px_l[`PCX_WIDTH-1:0]),
				 .pcx_scache2_data_px_l(pcx_scache2_data_px_l[`PCX_WIDTH-1:0]),
				 .scan_out(pcx_dp_array02_so_1), // Templated
				 // Inputs
				 .arbpc0_pcxdp_grant_pa(arbpc0_pcxdp_grant_pa[7:0]),
				 .arbpc0_pcxdp_q0_hold_pa(arbpc0_pcxdp_q0_hold_pa[7:0]),
				 .arbpc0_pcxdp_qsel0_pa(arbpc0_pcxdp_qsel0_pa[7:0]),
				 .arbpc0_pcxdp_qsel1_pa(arbpc0_pcxdp_qsel1_pa[7:0]),
				 .arbpc0_pcxdp_shift_px(arbpc0_pcxdp_shift_px[7:0]),
				 .arbpc2_pcxdp_grant_pa(arbpc2_pcxdp_grant_pa[7:0]),
				 .arbpc2_pcxdp_q0_hold_pa(arbpc2_pcxdp_q0_hold_pa[7:0]),
				 .arbpc2_pcxdp_qsel0_pa(arbpc2_pcxdp_qsel0_pa[7:0]),
				 .arbpc2_pcxdp_qsel1_pa(arbpc2_pcxdp_qsel1_pa[7:0]),
				 .arbpc2_pcxdp_shift_px(arbpc2_pcxdp_shift_px[7:0]),
				 .rclk	(rclk),
				 .shiftenable(se_buf1_top),	 // Templated
				 .spc0_pcx_data_pa(spc0_pcx_data_pa[`PCX_WIDTH-1:0]),
				 .spc1_pcx_data_pa(spc1_pcx_data_pa[`PCX_WIDTH-1:0]),
				 .spc2_pcx_data_pa(spc2_pcx_data_pa[`PCX_WIDTH-1:0]),
				 .spc3_pcx_data_pa(spc3_pcx_data_pa[`PCX_WIDTH-1:0]),
				 .spc4_pcx_data_pa(spc4_pcx_data_pa[`PCX_WIDTH-1:0]),
				 .spc5_pcx_data_pa(spc5_pcx_data_pa[`PCX_WIDTH-1:0]),
				 .spc6_pcx_data_pa(spc6_pcx_data_pa[`PCX_WIDTH-1:0]),
				 .spc7_pcx_data_pa(spc7_pcx_data_pa[`PCX_WIDTH-1:0]),
				 .scan_in(si_1));		 // Templated
       /*
   pcx_dp_array134 AUTO_TEMPLATE(
			  .shiftenable(se_buf1_bottom),
			  .scan_out	(pcx_dp_array134_so_0),
			  .scan_in	(si_0));
*/                 

   pcx_dp_array134 pcx_dp_array134(/*AUTOINST*/
				   // Outputs
				   .pcx_fpio_data_px_l(pcx_fpio_data_px_l[`PCX_WIDTH-1:0]),
				   .pcx_scache1_data_px_l(pcx_scache1_data_px_l[`PCX_WIDTH-1:0]),
				   .pcx_scache3_data_px_l(pcx_scache3_data_px_l[`PCX_WIDTH-1:0]),
				   .scan_out(pcx_dp_array134_so_0), // Templated
				   // Inputs
				   .arbpc1_pcxdp_grant_pa(arbpc1_pcxdp_grant_pa[7:0]),
				   .arbpc1_pcxdp_q0_hold_pa(arbpc1_pcxdp_q0_hold_pa[7:0]),
				   .arbpc1_pcxdp_qsel0_pa(arbpc1_pcxdp_qsel0_pa[7:0]),
				   .arbpc1_pcxdp_qsel1_pa(arbpc1_pcxdp_qsel1_pa[7:0]),
				   .arbpc1_pcxdp_shift_px(arbpc1_pcxdp_shift_px[7:0]),
				   .arbpc3_pcxdp_grant_pa(arbpc3_pcxdp_grant_pa[7:0]),
				   .arbpc3_pcxdp_q0_hold_pa(arbpc3_pcxdp_q0_hold_pa[7:0]),
				   .arbpc3_pcxdp_qsel0_pa(arbpc3_pcxdp_qsel0_pa[7:0]),
				   .arbpc3_pcxdp_qsel1_pa(arbpc3_pcxdp_qsel1_pa[7:0]),
				   .arbpc3_pcxdp_shift_px(arbpc3_pcxdp_shift_px[7:0]),
				   .arbpc4_pcxdp_grant_pa(arbpc4_pcxdp_grant_pa[7:0]),
				   .arbpc4_pcxdp_q0_hold_pa(arbpc4_pcxdp_q0_hold_pa[7:0]),
				   .arbpc4_pcxdp_qsel0_pa(arbpc4_pcxdp_qsel0_pa[7:0]),
				   .arbpc4_pcxdp_qsel1_pa(arbpc4_pcxdp_qsel1_pa[7:0]),
				   .arbpc4_pcxdp_shift_px(arbpc4_pcxdp_shift_px[7:0]),
				   .rclk(rclk),
				   .shiftenable(se_buf1_bottom), // Templated
				   .spc0_pcx_data_pa(spc0_pcx_data_pa[`PCX_WIDTH-1:0]),
				   .spc1_pcx_data_pa(spc1_pcx_data_pa[`PCX_WIDTH-1:0]),
				   .spc2_pcx_data_pa(spc2_pcx_data_pa[`PCX_WIDTH-1:0]),
				   .spc3_pcx_data_pa(spc3_pcx_data_pa[`PCX_WIDTH-1:0]),
				   .spc4_pcx_data_pa(spc4_pcx_data_pa[`PCX_WIDTH-1:0]),
				   .spc5_pcx_data_pa(spc5_pcx_data_pa[`PCX_WIDTH-1:0]),
				   .spc6_pcx_data_pa(spc6_pcx_data_pa[`PCX_WIDTH-1:0]),
				   .spc7_pcx_data_pa(spc7_pcx_data_pa[`PCX_WIDTH-1:0]),
				   .scan_in(si_0));		 // Templated
endmodule // pcx_dp_array





