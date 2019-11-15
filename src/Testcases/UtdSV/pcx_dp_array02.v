// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: pcx_dp_array02.v
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
 

module pcx_dp_array02(/*AUTOARG*/
   // Outputs
   pcx_scache2_data_px_l, pcx_scache0_data_px_l, scan_out, 
   // Inputs
   spc7_pcx_data_pa, spc6_pcx_data_pa, spc5_pcx_data_pa, 
   spc4_pcx_data_pa, spc3_pcx_data_pa, spc2_pcx_data_pa, 
   spc1_pcx_data_pa, spc0_pcx_data_pa, shiftenable, rclk, 
   arbpc2_pcxdp_shift_px, arbpc2_pcxdp_qsel1_pa, 
   arbpc2_pcxdp_qsel0_pa, arbpc2_pcxdp_q0_hold_pa, 
   arbpc2_pcxdp_grant_pa, arbpc0_pcxdp_shift_px, 
   arbpc0_pcxdp_qsel1_pa, arbpc0_pcxdp_qsel0_pa, 
   arbpc0_pcxdp_q0_hold_pa, arbpc0_pcxdp_grant_pa, scan_in
   );

   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output [`PCX_WIDTH-1:0]pcx_scache0_data_px_l;// From pcx_dp0 of pcx_dp0.v
   output [`PCX_WIDTH-1:0]pcx_scache2_data_px_l;// From pcx_dp2 of pcx_dp2.v
   // End of automatics

   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input [7:0]		arbpc0_pcxdp_grant_pa;	// To pcx_dp0 of pcx_dp0.v
   input [7:0]		arbpc0_pcxdp_q0_hold_pa;// To pcx_dp0 of pcx_dp0.v
   input [7:0]		arbpc0_pcxdp_qsel0_pa;	// To pcx_dp0 of pcx_dp0.v
   input [7:0]		arbpc0_pcxdp_qsel1_pa;	// To pcx_dp0 of pcx_dp0.v
   input [7:0]		arbpc0_pcxdp_shift_px;	// To pcx_dp0 of pcx_dp0.v
   input [7:0]		arbpc2_pcxdp_grant_pa;	// To pcx_dp2 of pcx_dp2.v
   input [7:0]		arbpc2_pcxdp_q0_hold_pa;// To pcx_dp2 of pcx_dp2.v
   input [7:0]		arbpc2_pcxdp_qsel0_pa;	// To pcx_dp2 of pcx_dp2.v
   input [7:0]		arbpc2_pcxdp_qsel1_pa;	// To pcx_dp2 of pcx_dp2.v
   input [7:0]		arbpc2_pcxdp_shift_px;	// To pcx_dp2 of pcx_dp2.v
   input		rclk;			// To pcx_dp0 of pcx_dp0.v, ...
   input		shiftenable;		// To pcx_dp0 of pcx_dp0.v, ...
   input [`PCX_WIDTH-1:0]spc0_pcx_data_pa;	// To pcx_dp0 of pcx_dp0.v, ...
   input [`PCX_WIDTH-1:0]spc1_pcx_data_pa;	// To pcx_dp0 of pcx_dp0.v, ...
   input [`PCX_WIDTH-1:0]spc2_pcx_data_pa;	// To pcx_dp0 of pcx_dp0.v, ...
   input [`PCX_WIDTH-1:0]spc3_pcx_data_pa;	// To pcx_dp0 of pcx_dp0.v, ...
   input [`PCX_WIDTH-1:0]spc4_pcx_data_pa;	// To pcx_dp0 of pcx_dp0.v, ...
   input [`PCX_WIDTH-1:0]spc5_pcx_data_pa;	// To pcx_dp0 of pcx_dp0.v, ...
   input [`PCX_WIDTH-1:0]spc6_pcx_data_pa;	// To pcx_dp0 of pcx_dp0.v, ...
   input [`PCX_WIDTH-1:0]spc7_pcx_data_pa;	// To pcx_dp0 of pcx_dp0.v, ...
   // End of automatics

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   // End of automatics

   input  scan_in;
   output scan_out;
   
       /*
   pcx_dp0 AUTO_TEMPLATE(
			  .scan_out	(),
			  .scan_in	());
*/                 
                 
   pcx_dp0 pcx_dp0(/*AUTOINST*/
		   // Outputs
		   .scan_out		(),			 // Templated
		   .pcx_scache0_data_px_l(pcx_scache0_data_px_l[`PCX_WIDTH-1:0]),
		   // Inputs
		   .arbpc0_pcxdp_grant_pa(arbpc0_pcxdp_grant_pa[7:0]),
		   .arbpc0_pcxdp_q0_hold_pa(arbpc0_pcxdp_q0_hold_pa[7:0]),
		   .arbpc0_pcxdp_qsel0_pa(arbpc0_pcxdp_qsel0_pa[7:0]),
		   .arbpc0_pcxdp_qsel1_pa(arbpc0_pcxdp_qsel1_pa[7:0]),
		   .arbpc0_pcxdp_shift_px(arbpc0_pcxdp_shift_px[7:0]),
		   .rclk		(rclk),
		   .scan_in		(),			 // Templated
		   .shiftenable		(shiftenable),
		   .spc0_pcx_data_pa	(spc0_pcx_data_pa[`PCX_WIDTH-1:0]),
		   .spc1_pcx_data_pa	(spc1_pcx_data_pa[`PCX_WIDTH-1:0]),
		   .spc2_pcx_data_pa	(spc2_pcx_data_pa[`PCX_WIDTH-1:0]),
		   .spc3_pcx_data_pa	(spc3_pcx_data_pa[`PCX_WIDTH-1:0]),
		   .spc4_pcx_data_pa	(spc4_pcx_data_pa[`PCX_WIDTH-1:0]),
		   .spc5_pcx_data_pa	(spc5_pcx_data_pa[`PCX_WIDTH-1:0]),
		   .spc6_pcx_data_pa	(spc6_pcx_data_pa[`PCX_WIDTH-1:0]),
		   .spc7_pcx_data_pa	(spc7_pcx_data_pa[`PCX_WIDTH-1:0]));

       /*
   pcx_dp2 AUTO_TEMPLATE(
			  .scan_out	(),
			  .scan_in	());
*/                 

   pcx_dp2 pcx_dp2(/*AUTOINST*/
		   // Outputs
		   .scan_out		(),			 // Templated
		   .pcx_scache2_data_px_l(pcx_scache2_data_px_l[`PCX_WIDTH-1:0]),
		   // Inputs
		   .arbpc2_pcxdp_grant_pa(arbpc2_pcxdp_grant_pa[7:0]),
		   .arbpc2_pcxdp_q0_hold_pa(arbpc2_pcxdp_q0_hold_pa[7:0]),
		   .arbpc2_pcxdp_qsel0_pa(arbpc2_pcxdp_qsel0_pa[7:0]),
		   .arbpc2_pcxdp_qsel1_pa(arbpc2_pcxdp_qsel1_pa[7:0]),
		   .arbpc2_pcxdp_shift_px(arbpc2_pcxdp_shift_px[7:0]),
		   .rclk		(rclk),
		   .scan_in		(),			 // Templated
		   .shiftenable		(shiftenable),
		   .spc0_pcx_data_pa	(spc0_pcx_data_pa[`PCX_WIDTH-1:0]),
		   .spc1_pcx_data_pa	(spc1_pcx_data_pa[`PCX_WIDTH-1:0]),
		   .spc2_pcx_data_pa	(spc2_pcx_data_pa[`PCX_WIDTH-1:0]),
		   .spc3_pcx_data_pa	(spc3_pcx_data_pa[`PCX_WIDTH-1:0]),
		   .spc4_pcx_data_pa	(spc4_pcx_data_pa[`PCX_WIDTH-1:0]),
		   .spc5_pcx_data_pa	(spc5_pcx_data_pa[`PCX_WIDTH-1:0]),
		   .spc6_pcx_data_pa	(spc6_pcx_data_pa[`PCX_WIDTH-1:0]),
		   .spc7_pcx_data_pa	(spc7_pcx_data_pa[`PCX_WIDTH-1:0]));

endmodule // pcx_dp_array02





