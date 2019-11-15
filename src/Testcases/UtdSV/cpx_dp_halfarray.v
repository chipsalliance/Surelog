// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: cpx_dp_halfarray.v
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
 

module cpx_dp_halfarray(/*AUTOARG*/
   // Outputs
   cpx_spc6_data_cx_l, cpx_spc4_data_cx_l, cpx_spc2_data_cx_l, 
   cpx_spc0_data_cx_l, scan_out, 
   // Inputs
   shiftenable, scache3_cpx_data_ca, scache2_cpx_data_ca, 
   scache1_cpx_data_ca, scache0_cpx_data_ca, rclk, io_cpx_data_ca, 
   fp_cpx_data_ca, arbcp6_cpxdp_shift_cx, arbcp6_cpxdp_qsel1_ca, 
   arbcp6_cpxdp_qsel0_ca, arbcp6_cpxdp_q0_hold_ca, 
   arbcp6_cpxdp_grant_ca, arbcp4_cpxdp_shift_cx, 
   arbcp4_cpxdp_qsel1_ca, arbcp4_cpxdp_qsel0_ca, 
   arbcp4_cpxdp_q0_hold_ca, arbcp4_cpxdp_grant_ca, 
   arbcp2_cpxdp_shift_cx, arbcp2_cpxdp_qsel1_ca, 
   arbcp2_cpxdp_qsel0_ca, arbcp2_cpxdp_q0_hold_ca, 
   arbcp2_cpxdp_grant_ca, arbcp0_cpxdp_shift_cx, 
   arbcp0_cpxdp_qsel1_ca, arbcp0_cpxdp_qsel0_ca, 
   arbcp0_cpxdp_q0_hold_ca, arbcp0_cpxdp_grant_ca, scan_in
   );

   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output [`CPX_WIDTH-1:0]cpx_spc0_data_cx_l;	// From cpx_dp0 of cpx_dp0.v
   output [`CPX_WIDTH-1:0]cpx_spc2_data_cx_l;	// From cpx_dp2 of cpx_dp2.v
   output [`CPX_WIDTH-1:0]cpx_spc4_data_cx_l;	// From cpx_dp4 of cpx_dp4.v
   output [`CPX_WIDTH-1:0]cpx_spc6_data_cx_l;	// From cpx_dp6 of cpx_dp6.v
   // End of automatics

   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input [5:0]		arbcp0_cpxdp_grant_ca;	// To cpx_dp0 of cpx_dp0.v
   input [5:0]		arbcp0_cpxdp_q0_hold_ca;// To cpx_dp0 of cpx_dp0.v
   input [5:0]		arbcp0_cpxdp_qsel0_ca;	// To cpx_dp0 of cpx_dp0.v
   input [5:0]		arbcp0_cpxdp_qsel1_ca;	// To cpx_dp0 of cpx_dp0.v
   input [5:0]		arbcp0_cpxdp_shift_cx;	// To cpx_dp0 of cpx_dp0.v
   input [5:0]		arbcp2_cpxdp_grant_ca;	// To cpx_dp2 of cpx_dp2.v
   input [5:0]		arbcp2_cpxdp_q0_hold_ca;// To cpx_dp2 of cpx_dp2.v
   input [5:0]		arbcp2_cpxdp_qsel0_ca;	// To cpx_dp2 of cpx_dp2.v
   input [5:0]		arbcp2_cpxdp_qsel1_ca;	// To cpx_dp2 of cpx_dp2.v
   input [5:0]		arbcp2_cpxdp_shift_cx;	// To cpx_dp2 of cpx_dp2.v
   input [5:0]		arbcp4_cpxdp_grant_ca;	// To cpx_dp4 of cpx_dp4.v
   input [5:0]		arbcp4_cpxdp_q0_hold_ca;// To cpx_dp4 of cpx_dp4.v
   input [5:0]		arbcp4_cpxdp_qsel0_ca;	// To cpx_dp4 of cpx_dp4.v
   input [5:0]		arbcp4_cpxdp_qsel1_ca;	// To cpx_dp4 of cpx_dp4.v
   input [5:0]		arbcp4_cpxdp_shift_cx;	// To cpx_dp4 of cpx_dp4.v
   input [5:0]		arbcp6_cpxdp_grant_ca;	// To cpx_dp6 of cpx_dp6.v
   input [5:0]		arbcp6_cpxdp_q0_hold_ca;// To cpx_dp6 of cpx_dp6.v
   input [5:0]		arbcp6_cpxdp_qsel0_ca;	// To cpx_dp6 of cpx_dp6.v
   input [5:0]		arbcp6_cpxdp_qsel1_ca;	// To cpx_dp6 of cpx_dp6.v
   input [5:0]		arbcp6_cpxdp_shift_cx;	// To cpx_dp6 of cpx_dp6.v
   input [`CPX_WIDTH-1:0]fp_cpx_data_ca;	// To cpx_dp0 of cpx_dp0.v, ...
   input [`CPX_WIDTH-1:0]io_cpx_data_ca;	// To cpx_dp0 of cpx_dp0.v, ...
   input		rclk;			// To cpx_dp0 of cpx_dp0.v, ...
   input [`CPX_WIDTH-1:0]scache0_cpx_data_ca;	// To cpx_dp0 of cpx_dp0.v, ...
   input [`CPX_WIDTH-1:0]scache1_cpx_data_ca;	// To cpx_dp0 of cpx_dp0.v, ...
   input [`CPX_WIDTH-1:0]scache2_cpx_data_ca;	// To cpx_dp0 of cpx_dp0.v, ...
   input [`CPX_WIDTH-1:0]scache3_cpx_data_ca;	// To cpx_dp0 of cpx_dp0.v, ...
   input		shiftenable;		// To cpx_dp0 of cpx_dp0.v, ...
   // End of automatics

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   // End of automatics

   input    scan_in;
   output   scan_out;
   
       /*
   cpx_dp0 AUTO_TEMPLATE(
			  .scan_out	(),
			  .scan_in	());
*/                 
   cpx_dp0 cpx_dp0(/*AUTOINST*/
		   // Outputs
		   .scan_out		(),			 // Templated
		   .cpx_spc0_data_cx_l	(cpx_spc0_data_cx_l[`CPX_WIDTH-1:0]),
		   // Inputs
		   .arbcp0_cpxdp_grant_ca(arbcp0_cpxdp_grant_ca[5:0]),
		   .arbcp0_cpxdp_q0_hold_ca(arbcp0_cpxdp_q0_hold_ca[5:0]),
		   .arbcp0_cpxdp_qsel0_ca(arbcp0_cpxdp_qsel0_ca[5:0]),
		   .arbcp0_cpxdp_qsel1_ca(arbcp0_cpxdp_qsel1_ca[5:0]),
		   .arbcp0_cpxdp_shift_cx(arbcp0_cpxdp_shift_cx[5:0]),
		   .rclk		(rclk),
		   .scan_in		(),			 // Templated
		   .shiftenable		(shiftenable),
		   .scache0_cpx_data_ca	(scache0_cpx_data_ca[`CPX_WIDTH-1:0]),
		   .scache1_cpx_data_ca	(scache1_cpx_data_ca[`CPX_WIDTH-1:0]),
		   .scache2_cpx_data_ca	(scache2_cpx_data_ca[`CPX_WIDTH-1:0]),
		   .scache3_cpx_data_ca	(scache3_cpx_data_ca[`CPX_WIDTH-1:0]),
		   .io_cpx_data_ca	(io_cpx_data_ca[`CPX_WIDTH-1:0]),
		   .fp_cpx_data_ca	(fp_cpx_data_ca[`CPX_WIDTH-1:0]));

       /*
   cpx_dp2 AUTO_TEMPLATE(
			  .scan_out	(),
			  .scan_in	());
*/                 

   cpx_dp2 cpx_dp2(/*AUTOINST*/
		   // Outputs
		   .scan_out		(),			 // Templated
		   .cpx_spc2_data_cx_l	(cpx_spc2_data_cx_l[`CPX_WIDTH-1:0]),
		   // Inputs
		   .arbcp2_cpxdp_grant_ca(arbcp2_cpxdp_grant_ca[5:0]),
		   .arbcp2_cpxdp_q0_hold_ca(arbcp2_cpxdp_q0_hold_ca[5:0]),
		   .arbcp2_cpxdp_qsel0_ca(arbcp2_cpxdp_qsel0_ca[5:0]),
		   .arbcp2_cpxdp_qsel1_ca(arbcp2_cpxdp_qsel1_ca[5:0]),
		   .arbcp2_cpxdp_shift_cx(arbcp2_cpxdp_shift_cx[5:0]),
		   .rclk		(rclk),
		   .scan_in		(),			 // Templated
		   .shiftenable		(shiftenable),
		   .scache0_cpx_data_ca	(scache0_cpx_data_ca[`CPX_WIDTH-1:0]),
		   .scache1_cpx_data_ca	(scache1_cpx_data_ca[`CPX_WIDTH-1:0]),
		   .scache2_cpx_data_ca	(scache2_cpx_data_ca[`CPX_WIDTH-1:0]),
		   .scache3_cpx_data_ca	(scache3_cpx_data_ca[`CPX_WIDTH-1:0]),
		   .io_cpx_data_ca	(io_cpx_data_ca[`CPX_WIDTH-1:0]),
		   .fp_cpx_data_ca	(fp_cpx_data_ca[`CPX_WIDTH-1:0]));
       /*
   cpx_dp4 AUTO_TEMPLATE(
			  .scan_out	(),
			  .scan_in	());
*/                 

   cpx_dp4 cpx_dp4(/*AUTOINST*/
		   // Outputs
		   .scan_out		(),			 // Templated
		   .cpx_spc4_data_cx_l	(cpx_spc4_data_cx_l[`CPX_WIDTH-1:0]),
		   // Inputs
		   .arbcp4_cpxdp_grant_ca(arbcp4_cpxdp_grant_ca[5:0]),
		   .arbcp4_cpxdp_q0_hold_ca(arbcp4_cpxdp_q0_hold_ca[5:0]),
		   .arbcp4_cpxdp_qsel0_ca(arbcp4_cpxdp_qsel0_ca[5:0]),
		   .arbcp4_cpxdp_qsel1_ca(arbcp4_cpxdp_qsel1_ca[5:0]),
		   .arbcp4_cpxdp_shift_cx(arbcp4_cpxdp_shift_cx[5:0]),
		   .rclk		(rclk),
		   .scan_in		(),			 // Templated
		   .shiftenable		(shiftenable),
		   .scache0_cpx_data_ca	(scache0_cpx_data_ca[`CPX_WIDTH-1:0]),
		   .scache1_cpx_data_ca	(scache1_cpx_data_ca[`CPX_WIDTH-1:0]),
		   .scache2_cpx_data_ca	(scache2_cpx_data_ca[`CPX_WIDTH-1:0]),
		   .scache3_cpx_data_ca	(scache3_cpx_data_ca[`CPX_WIDTH-1:0]),
		   .io_cpx_data_ca	(io_cpx_data_ca[`CPX_WIDTH-1:0]),
		   .fp_cpx_data_ca	(fp_cpx_data_ca[`CPX_WIDTH-1:0]));
       /*
   cpx_dp6 AUTO_TEMPLATE(
			  .scan_out	(),
			  .scan_in	());
*/                 

   cpx_dp6 cpx_dp6(/*AUTOINST*/
		   // Outputs
		   .scan_out		(),			 // Templated
		   .cpx_spc6_data_cx_l	(cpx_spc6_data_cx_l[`CPX_WIDTH-1:0]),
		   // Inputs
		   .arbcp6_cpxdp_grant_ca(arbcp6_cpxdp_grant_ca[5:0]),
		   .arbcp6_cpxdp_q0_hold_ca(arbcp6_cpxdp_q0_hold_ca[5:0]),
		   .arbcp6_cpxdp_qsel0_ca(arbcp6_cpxdp_qsel0_ca[5:0]),
		   .arbcp6_cpxdp_qsel1_ca(arbcp6_cpxdp_qsel1_ca[5:0]),
		   .arbcp6_cpxdp_shift_cx(arbcp6_cpxdp_shift_cx[5:0]),
		   .rclk		(rclk),
		   .scan_in		(),			 // Templated
		   .shiftenable		(shiftenable),
		   .scache0_cpx_data_ca	(scache0_cpx_data_ca[`CPX_WIDTH-1:0]),
		   .scache1_cpx_data_ca	(scache1_cpx_data_ca[`CPX_WIDTH-1:0]),
		   .scache2_cpx_data_ca	(scache2_cpx_data_ca[`CPX_WIDTH-1:0]),
		   .scache3_cpx_data_ca	(scache3_cpx_data_ca[`CPX_WIDTH-1:0]),
		   .io_cpx_data_ca	(io_cpx_data_ca[`CPX_WIDTH-1:0]),
		   .fp_cpx_data_ca	(fp_cpx_data_ca[`CPX_WIDTH-1:0]));

endmodule // cpx_dp_array





