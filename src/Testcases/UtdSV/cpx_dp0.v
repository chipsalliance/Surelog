// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: cpx_dp0.v
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

module cpx_dp0(/*AUTOARG*/
   // Outputs
   scan_out, cpx_spc0_data_cx_l, 
   // Inputs
   shiftenable, scan_in, rclk, arbcp0_cpxdp_shift_cx, 
   arbcp0_cpxdp_qsel1_ca, arbcp0_cpxdp_qsel0_ca, 
   arbcp0_cpxdp_q0_hold_ca, arbcp0_cpxdp_grant_ca, 
   scache0_cpx_data_ca, scache1_cpx_data_ca, scache2_cpx_data_ca, 
   scache3_cpx_data_ca, io_cpx_data_ca, fp_cpx_data_ca
   );	

              /*AUTOOUTPUT*/
	      // Beginning of automatic outputs (from unused autoinst outputs)
	      output [7:0]    scan_out;		      // From mac0 of cpx_dp_macc_r.v, ...
	      // End of automatics
   
output  [`CPX_WIDTH-1:0]  cpx_spc0_data_cx_l;   
   

              /*AUTOINPUT*/
	      // Beginning of automatic inputs (from unused autoinst inputs)
	      input [5:0]     arbcp0_cpxdp_grant_ca;  // To mac0 of cpx_dp_macc_r.v, ...
	      input [5:0]     arbcp0_cpxdp_q0_hold_ca;// To mac0 of cpx_dp_macc_r.v, ...
	      input [5:0]     arbcp0_cpxdp_qsel0_ca;  // To mac0 of cpx_dp_macc_r.v, ...
	      input [5:0]     arbcp0_cpxdp_qsel1_ca;  // To mac0 of cpx_dp_macc_r.v, ...
	      input [5:0]     arbcp0_cpxdp_shift_cx;  // To mac0 of cpx_dp_macc_r.v, ...
	      input	      rclk;		      // To mac0 of cpx_dp_macc_r.v, ...
	      input [7:0]     scan_in;		      // To mac0 of cpx_dp_macc_r.v, ...
	      input	      shiftenable;	      // To mac7 of cpx_dp_maca_l.v
	      // End of automatics

input  [`CPX_WIDTH-1:0]  scache0_cpx_data_ca;
input  [`CPX_WIDTH-1:0]  scache1_cpx_data_ca;
input  [`CPX_WIDTH-1:0]  scache2_cpx_data_ca;
input  [`CPX_WIDTH-1:0]  scache3_cpx_data_ca;
input  [`CPX_WIDTH-1:0]  io_cpx_data_ca;
input  [`CPX_WIDTH-1:0]  fp_cpx_data_ca;

              /*AUTOWIRE*/
	      // Beginning of automatic wires (for undeclared instantiated-module outputs)
	      wire [149:0]    cpx_col1_data_cx_l;     // From mac1 of cpx_dp_macb_l.v
	      wire [149:0]    cpx_col3_data_cx_l;     // From mac3 of cpx_dp_macb_l.v
	      wire [149:0]    cpx_col4_data_cx_l;     // From mac4 of cpx_dp_macb_l.v
	      wire [149:0]    cpx_col6_data_cx_l;     // From mac6 of cpx_dp_macb_l.v
	      wire [149:0]    cpx_col7_data_cx_l;     // From mac7 of cpx_dp_maca_l.v
	      wire [7:1]      shiftenable_buf;	      // From mac1 of cpx_dp_macb_l.v, ...
	      // End of automatics
wire  [4:0]  unused;
   
   wire 	[149:0]   tied_hi;
   assign   tied_hi = 150'b111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;

    

/*

   
// DATAPATH ORGANISATION(cpx_dp0)


to sparc0 cx2 flops
     ^
     |   
   mac0 <- mac1 <----- <- mac3 <- mac4 <----- <- mac6 <- mac7
new: cr      bl           bl      bl             bl       a
     ^       ^            ^       ^              ^        ^
     |       |            |       |              |        |
   sctag0   sctag1        io    sctag2         sctag3	    fp

old: c       b            b       b              b        a
     ^       ^            ^       ^              ^        ^
     |       |            |       |              |        |
   sctag0   fp          sctag1  sctag2           io     sctag3

 */
   
   
      /*
   cpx_dp_macc_r AUTO_TEMPLATE(
			  // Outputs
			  .data_out_cx_l	({unused[4:0],cpx_spc@_data_cx_l[`CPX_WIDTH-1:0]}),
		          .shiftenable_buf	(),
			  //.data_out_cx_l	(cpx_col@_data_cx_l[`CPX_WIDTH-1:0]),
			  // Inputs
			  .src_cpx_data_ca({5'b00000,scache@_cpx_data_ca[`CPX_WIDTH-1:0]}),
			  .arb_cpxdp_qsel1_ca(arbcp0_cpxdp_qsel1_ca[@]),
			  .arb_cpxdp_qsel0_ca(arbcp0_cpxdp_qsel0_ca[@]),
			  .arb_cpxdp_grant_ca(arbcp0_cpxdp_grant_ca[@]),
			  .arb_cpxdp_shift_cx(arbcp0_cpxdp_shift_cx[@]),
			  .arb_cpxdp_q0_hold_ca(arbcp0_cpxdp_q0_hold_ca[@]),
       			  .data_crit_cx_l(cpx_col@"(+ @ 1)"_data_cx_l[149:0]),
       			  .data_ncrit_cx_l(tied_hi[149:0]),
		    .clk		(clk),
		    //.tmb_l		(tmb_l),
		    .scan_in		(scan_in[@]),
		    .scan_out		(scan_out[@]),
		    .shiftenable	(shiftenable_buf[@"(+ @ 1)"]));

   
    */
 
   cpx_dp_macc_r mac0(/*AUTOINST*/
		      // Outputs
		      .data_out_cx_l	({unused[4:0],cpx_spc0_data_cx_l[`CPX_WIDTH-1:0]}), // Templated
		      .scan_out		(scan_out[0]),		 // Templated
		      .shiftenable_buf	(),			 // Templated
		      // Inputs
		      .arb_cpxdp_qsel1_ca(arbcp0_cpxdp_qsel1_ca[0]), // Templated
		      .arb_cpxdp_qsel0_ca(arbcp0_cpxdp_qsel0_ca[0]), // Templated
		      .arb_cpxdp_grant_ca(arbcp0_cpxdp_grant_ca[0]), // Templated
		      .arb_cpxdp_shift_cx(arbcp0_cpxdp_shift_cx[0]), // Templated
		      .arb_cpxdp_q0_hold_ca(arbcp0_cpxdp_q0_hold_ca[0]), // Templated
		      .src_cpx_data_ca	({5'b00000,scache0_cpx_data_ca[`CPX_WIDTH-1:0]}), // Templated
		      .data_crit_cx_l	(cpx_col1_data_cx_l[149:0]), // Templated
		      .data_ncrit_cx_l	(tied_hi[149:0]),	 // Templated
		      .rclk		(rclk),
		      .scan_in		(scan_in[0]),		 // Templated
		      .shiftenable	(shiftenable_buf[1]));	 // Templated
      /*
   cpx_dp_macb_l AUTO_TEMPLATE(
			  // Outputs
			  .data_out_cx_l	(cpx_col@_data_cx_l[149:0]),
		          .shiftenable_buf	(shiftenable_buf[@]),
			  // Inputs
			  .src_cpx_data_ca({5'b00000,scache@_cpx_data_ca[`CPX_WIDTH-1:0]}),
			  .arb_cpxdp_qsel1_ca(arbcp0_cpxdp_qsel1_ca[@]),
			  .arb_cpxdp_qsel0_ca(arbcp0_cpxdp_qsel0_ca[@]),
			  .arb_cpxdp_grant_ca(arbcp0_cpxdp_grant_ca[@]),
			  .arb_cpxdp_shift_cx(arbcp0_cpxdp_shift_cx[@]),
			  .arb_cpxdp_q0_hold_ca(arbcp0_cpxdp_q0_hold_ca[@]),
			  .data_prev_cx_l(cpx_col@"(+ @ 2)"_data_cx_l[149:0]),
		    .clk		(clk),
		    //.tmb_l		(tmb_l),
		    .scan_in		(scan_in[@]),
		    .scan_out		(scan_out[@]),
		    .shiftenable	(shiftenable_buf[@"(+ @ 2)"]));
   
    */

   cpx_dp_macb_l mac1(/*AUTOINST*/
		      // Outputs
		      .data_out_cx_l	(cpx_col1_data_cx_l[149:0]), // Templated
		      .scan_out		(scan_out[1]),		 // Templated
		      .shiftenable_buf	(shiftenable_buf[1]),	 // Templated
		      // Inputs
		      .arb_cpxdp_qsel1_ca(arbcp0_cpxdp_qsel1_ca[1]), // Templated
		      .arb_cpxdp_qsel0_ca(arbcp0_cpxdp_qsel0_ca[1]), // Templated
		      .arb_cpxdp_grant_ca(arbcp0_cpxdp_grant_ca[1]), // Templated
		      .arb_cpxdp_shift_cx(arbcp0_cpxdp_shift_cx[1]), // Templated
		      .arb_cpxdp_q0_hold_ca(arbcp0_cpxdp_q0_hold_ca[1]), // Templated
		      .src_cpx_data_ca	({5'b00000,scache1_cpx_data_ca[`CPX_WIDTH-1:0]}), // Templated
		      .data_prev_cx_l	(cpx_col3_data_cx_l[149:0]), // Templated
		      .rclk		(rclk),
		      .scan_in		(scan_in[1]),		 // Templated
		      .shiftenable	(shiftenable_buf[3]));	 // Templated
/*   cpx_dp_macb_l AUTO_TEMPLATE(
			  // Outputs
			  .data_out_cx_l	(cpx_col@_data_cx_l[149:0]),
		          .shiftenable_buf	(shiftenable_buf[@]),
			  // Inputs
			  .src_cpx_data_ca({5'b00000,io_cpx_data_ca[`CPX_WIDTH-1:0]}),
			  .arb_cpxdp_qsel1_ca(arbcp0_cpxdp_qsel1_ca[@"(+ @ 1)"]),
			  .arb_cpxdp_qsel0_ca(arbcp0_cpxdp_qsel0_ca[@"(+ @ 1)"]),
			  .arb_cpxdp_grant_ca(arbcp0_cpxdp_grant_ca[@"(+ @ 1)"]),
			  .arb_cpxdp_shift_cx(arbcp0_cpxdp_shift_cx[@"(+ @ 1)"]),
			  .arb_cpxdp_q0_hold_ca(arbcp0_cpxdp_q0_hold_ca[@"(+ @ 1)"]),
       			  .data_prev_cx_l(cpx_col@"(+ @ 1)"_data_cx_l[149:0]),
		    .clk		(clk),
		    //.tmb_l		(tmb_l),
		    .scan_in		(scan_in[@]),
		    .scan_out		(scan_out[@]),
		    .shiftenable	(shiftenable_buf[@"(+ @ 1)"]));

   
    */

   cpx_dp_macb_l mac3(/*AUTOINST*/
		      // Outputs
		      .data_out_cx_l	(cpx_col3_data_cx_l[149:0]), // Templated
		      .scan_out		(scan_out[3]),		 // Templated
		      .shiftenable_buf	(shiftenable_buf[3]),	 // Templated
		      // Inputs
		      .arb_cpxdp_qsel1_ca(arbcp0_cpxdp_qsel1_ca[4]), // Templated
		      .arb_cpxdp_qsel0_ca(arbcp0_cpxdp_qsel0_ca[4]), // Templated
		      .arb_cpxdp_grant_ca(arbcp0_cpxdp_grant_ca[4]), // Templated
		      .arb_cpxdp_shift_cx(arbcp0_cpxdp_shift_cx[4]), // Templated
		      .arb_cpxdp_q0_hold_ca(arbcp0_cpxdp_q0_hold_ca[4]), // Templated
		      .src_cpx_data_ca	({5'b00000,io_cpx_data_ca[`CPX_WIDTH-1:0]}), // Templated
		      .data_prev_cx_l	(cpx_col4_data_cx_l[149:0]), // Templated
		      .rclk		(rclk),
		      .scan_in		(scan_in[3]),		 // Templated
		      .shiftenable	(shiftenable_buf[4]));	 // Templated
/*   cpx_dp_macb_l AUTO_TEMPLATE(
			  // Outputs
			  .data_out_cx_l	(cpx_col@_data_cx_l[149:0]),
		          .shiftenable_buf	(shiftenable_buf[@]),
			  // Inputs
			  .src_cpx_data_ca({5'b00000,scache@"(- @ 2)"_cpx_data_ca[`CPX_WIDTH-1:0]}),
			  .arb_cpxdp_qsel1_ca(arbcp0_cpxdp_qsel1_ca[@"(- @ 2)"]),
			  .arb_cpxdp_qsel0_ca(arbcp0_cpxdp_qsel0_ca[@"(- @ 2)"]),
			  .arb_cpxdp_grant_ca(arbcp0_cpxdp_grant_ca[@"(- @ 2)"]),
			  .arb_cpxdp_shift_cx(arbcp0_cpxdp_shift_cx[@"(- @ 2)"]),
			  .arb_cpxdp_q0_hold_ca(arbcp0_cpxdp_q0_hold_ca[@"(- @ 2)"]),
       			  .data_prev_cx_l(cpx_col@"(+ @ 2)"_data_cx_l[149:0]),
		    .clk		(clk),
		    //.tmb_l		(tmb_l),
		    .scan_in		(scan_in[@]),
		    .scan_out		(scan_out[@]),
		    .shiftenable	(shiftenable_buf[@"(+ @ 2)"]));

   
    */

   cpx_dp_macb_l mac4(/*AUTOINST*/
		      // Outputs
		      .data_out_cx_l	(cpx_col4_data_cx_l[149:0]), // Templated
		      .scan_out		(scan_out[4]),		 // Templated
		      .shiftenable_buf	(shiftenable_buf[4]),	 // Templated
		      // Inputs
		      .arb_cpxdp_qsel1_ca(arbcp0_cpxdp_qsel1_ca[2]), // Templated
		      .arb_cpxdp_qsel0_ca(arbcp0_cpxdp_qsel0_ca[2]), // Templated
		      .arb_cpxdp_grant_ca(arbcp0_cpxdp_grant_ca[2]), // Templated
		      .arb_cpxdp_shift_cx(arbcp0_cpxdp_shift_cx[2]), // Templated
		      .arb_cpxdp_q0_hold_ca(arbcp0_cpxdp_q0_hold_ca[2]), // Templated
		      .src_cpx_data_ca	({5'b00000,scache2_cpx_data_ca[`CPX_WIDTH-1:0]}), // Templated
		      .data_prev_cx_l	(cpx_col6_data_cx_l[149:0]), // Templated
		      .rclk		(rclk),
		      .scan_in		(scan_in[4]),		 // Templated
		      .shiftenable	(shiftenable_buf[6]));	 // Templated
      /*  
   cpx_dp_macb_l AUTO_TEMPLATE(
			  // Outputs
			  .data_out_cx_l	(cpx_col@_data_cx_l[149:0]),
		          .shiftenable_buf	(shiftenable_buf[@]),
			  // Inputs
			  .src_cpx_data_ca({5'b00000,scache@"(- @ 3)"_cpx_data_ca[`CPX_WIDTH-1:0]}),
			  .arb_cpxdp_qsel1_ca(arbcp0_cpxdp_qsel1_ca[@"(- @ 3)"]),
			  .arb_cpxdp_qsel0_ca(arbcp0_cpxdp_qsel0_ca[@"(- @ 3)"]),
			  .arb_cpxdp_grant_ca(arbcp0_cpxdp_grant_ca[@"(- @ 3)"]),
			  .arb_cpxdp_shift_cx(arbcp0_cpxdp_shift_cx[@"(- @ 3)"]),
			  .arb_cpxdp_q0_hold_ca(arbcp0_cpxdp_q0_hold_ca[@"(- @ 3)"]),
       			  .data_prev_cx_l(cpx_col@"(+ @ 1)"_data_cx_l[149:0]),
		    .clk		(clk),
		    //.tmb_l		(tmb_l),
		    .scan_in		(scan_in[@]),
		    .scan_out		(scan_out[@]),
		    .shiftenable	(shiftenable_buf[@"(+ @ 1)"]));

   
    */

   cpx_dp_macb_l mac6(/*AUTOINST*/
		      // Outputs
		      .data_out_cx_l	(cpx_col6_data_cx_l[149:0]), // Templated
		      .scan_out		(scan_out[6]),		 // Templated
		      .shiftenable_buf	(shiftenable_buf[6]),	 // Templated
		      // Inputs
		      .arb_cpxdp_qsel1_ca(arbcp0_cpxdp_qsel1_ca[3]), // Templated
		      .arb_cpxdp_qsel0_ca(arbcp0_cpxdp_qsel0_ca[3]), // Templated
		      .arb_cpxdp_grant_ca(arbcp0_cpxdp_grant_ca[3]), // Templated
		      .arb_cpxdp_shift_cx(arbcp0_cpxdp_shift_cx[3]), // Templated
		      .arb_cpxdp_q0_hold_ca(arbcp0_cpxdp_q0_hold_ca[3]), // Templated
		      .src_cpx_data_ca	({5'b00000,scache3_cpx_data_ca[`CPX_WIDTH-1:0]}), // Templated
		      .data_prev_cx_l	(cpx_col7_data_cx_l[149:0]), // Templated
		      .rclk		(rclk),
		      .scan_in		(scan_in[6]),		 // Templated
		      .shiftenable	(shiftenable_buf[7]));	 // Templated
      /*
   cpx_dp_maca_l AUTO_TEMPLATE(
			  // Outputs
			  .data_out_cx_l	(cpx_col@_data_cx_l[149:0]),
		          .shiftenable_buf	(shiftenable_buf[@]),
			  // Inputs
			  .src_cpx_data_ca({5'b00000,fp_cpx_data_ca[`CPX_WIDTH-1:0]}),
			  .arb_cpxdp_qsel1_ca(arbcp0_cpxdp_qsel1_ca[@"(- @ 2)"]),
			  .arb_cpxdp_qsel0_ca(arbcp0_cpxdp_qsel0_ca[@"(- @ 2)"]),
			  .arb_cpxdp_grant_ca(arbcp0_cpxdp_grant_ca[@"(- @ 2)"]),
			  .arb_cpxdp_shift_cx(arbcp0_cpxdp_shift_cx[@"(- @ 2)"]),
			  .arb_cpxdp_q0_hold_ca(arbcp0_cpxdp_q0_hold_ca[@"(- @ 2)"]),
		    .clk		(clk),
		    //.tmb_l		(tmb_l),
		    .scan_in		(scan_in[@]),
		    .scan_out		(scan_out[@]),
		    .shiftenable	(shiftenable));

   
    */

   cpx_dp_maca_l mac7(/*AUTOINST*/
		      // Outputs
		      .data_out_cx_l	(cpx_col7_data_cx_l[149:0]), // Templated
		      .scan_out		(scan_out[7]),		 // Templated
		      .shiftenable_buf	(shiftenable_buf[7]),	 // Templated
		      // Inputs
		      .arb_cpxdp_qsel1_ca(arbcp0_cpxdp_qsel1_ca[5]), // Templated
		      .arb_cpxdp_qsel0_ca(arbcp0_cpxdp_qsel0_ca[5]), // Templated
		      .arb_cpxdp_grant_ca(arbcp0_cpxdp_grant_ca[5]), // Templated
		      .arb_cpxdp_shift_cx(arbcp0_cpxdp_shift_cx[5]), // Templated
		      .arb_cpxdp_q0_hold_ca(arbcp0_cpxdp_q0_hold_ca[5]), // Templated
		      .src_cpx_data_ca	({5'b00000,fp_cpx_data_ca[`CPX_WIDTH-1:0]}), // Templated
		      .rclk		(rclk),
		      .scan_in		(scan_in[7]),		 // Templated
		      .shiftenable	(shiftenable));		 // Templated
// Code start here 
//
// Local Variables:
// verilog-library-directories:("." "../../../../../common/rtl")
// End:



endmodule












