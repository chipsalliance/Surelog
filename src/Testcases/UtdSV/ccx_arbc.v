// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: ccx_arbc.v
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
// Global header file includes
////////////////////////////////////////////////////////////////////////

`include	"sys.h" // system level definition file which contains the 
			// time scale definition

`include "iop.h"

 
////////////////////////////////////////////////////////////////////////
// Local header file includes / local defines
////////////////////////////////////////////////////////////////////////


// Code start here 
//

module ccx_arbc(/*AUTOARG*/
   // Outputs
   scan_out, ccx_dest_data_rdy_x, arb_src5_grant_a, arb_src4_grant_a, 
   arb_src3_grant_a, arb_src2_grant_a, arb_src1_grant_a, 
   arb_src0_grant_a, arb_dp_grant_a, arb_dp_q0_hold_a, 
   arb_dp_qsel0_a, arb_dp_qsel1_a, arb_dp_shift_x, 
   // Inputs
   src5_arb_req_q, src5_arb_atom_q, src4_arb_req_q, src4_arb_atom_q, 
   src3_arb_req_q, src3_arb_atom_q, src2_arb_req_q, src2_arb_atom_q, 
   src1_arb_req_q, src1_arb_atom_q, src0_arb_req_q, src0_arb_atom_q, 
   se, scan_in, reset_l, rclk, adbginit_l
   );
   
/*AUTOOUTPUT*/
// Beginning of automatic outputs (from unused autoinst outputs)
output			arb_src0_grant_a;	// From ccx_arb of ccx_arb.v
output			arb_src1_grant_a;	// From ccx_arb of ccx_arb.v
output			arb_src2_grant_a;	// From ccx_arb of ccx_arb.v
output			arb_src3_grant_a;	// From ccx_arb of ccx_arb.v
output			arb_src4_grant_a;	// From ccx_arb of ccx_arb.v
output			arb_src5_grant_a;	// From ccx_arb of ccx_arb.v
output			ccx_dest_data_rdy_x;	// From ccx_arb of ccx_arb.v
output			scan_out;		// From ccx_arb of ccx_arb.v
// End of automatics



   output [5:0]		arb_dp_grant_a;		
   output [5:0]		arb_dp_q0_hold_a;	
   output [5:0]		arb_dp_qsel0_a;		
   output [5:0]		arb_dp_qsel1_a;		
   output [5:0]		arb_dp_shift_x;		


   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input		adbginit_l;		// To ccx_arb of ccx_arb.v
   input		rclk;			// To ccx_arb of ccx_arb.v
   input		reset_l;		// To ccx_arb of ccx_arb.v
   input		scan_in;		// To ccx_arb of ccx_arb.v
   input		se;			// To ccx_arb of ccx_arb.v
   input		src0_arb_atom_q;	// To ccx_arb of ccx_arb.v
   input		src0_arb_req_q;		// To ccx_arb of ccx_arb.v
   input		src1_arb_atom_q;	// To ccx_arb of ccx_arb.v
   input		src1_arb_req_q;		// To ccx_arb of ccx_arb.v
   input		src2_arb_atom_q;	// To ccx_arb of ccx_arb.v
   input		src2_arb_req_q;		// To ccx_arb of ccx_arb.v
   input		src3_arb_atom_q;	// To ccx_arb of ccx_arb.v
   input		src3_arb_req_q;		// To ccx_arb of ccx_arb.v
   input		src4_arb_atom_q;	// To ccx_arb of ccx_arb.v
   input		src4_arb_req_q;		// To ccx_arb of ccx_arb.v
   input		src5_arb_atom_q;	// To ccx_arb of ccx_arb.v
   input		src5_arb_req_q;		// To ccx_arb of ccx_arb.v
   // End of automatics


   

   wire  src6_arb_atom_q ;	
   wire  src6_arb_req_q ;	
   wire  src7_arb_atom_q ;	
   wire  src7_arb_req_q ;	
   wire  stall1_q ;		
   wire  stall2_q ;		


   wire [1:0] 		sinka;
   wire [1:0] 		sinkb;
   wire [1:0] 		sinkc;
   wire [1:0] 		sinkd;
   wire [1:0] 		sinke;
   
 
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   // End of automatics

   assign  src6_arb_atom_q = 1'b0;	
   assign  src6_arb_req_q = 1'b0;	
   assign  src7_arb_atom_q = 1'b0;	
   assign  src7_arb_req_q = 1'b0;	
   assign  stall1_q = 1'b0;
   assign  stall2_q = 1'b0;

// commented out - backend does not like this
//   sink #(2) sink1(.in (sinka[1:0]));
//   sink #(2) sink2(.in (sinkb[1:0]));
//   sink #(2) sink3(.in (sinkc[1:0]));
//   sink #(2) sink4(.in (sinkd[1:0]));
//   sink #(2) sink5(.in (sinke[1:0]));
   
/*
 
  ccx_arb AUTO_TEMPLATE(
		   .ccx_dest_atom_x	(),
		   .arb_dp_grant_a	({sinka[0], sinka[1],arb_dp_grant_a[5:0]}),
		   .arb_dp_q0_hold_a	({sinkb[0], sinkb[1],arb_dp_q0_hold_a[5:0]}),
		   .arb_dp_qsel0_a	({sinkc[0], sinkc[1],arb_dp_qsel0_a[5:0]}),
		   .arb_dp_qsel1_a	({sinkd[0], sinkd[1],arb_dp_qsel1_a[5:0]}),
		   .arb_dp_shift_x	({sinke[0], sinke[1],arb_dp_shift_x[5:0]}),
		   .arb_src6_grant_a	(),
		   .arb_src7_grant_a	());
 */
    
   ccx_arb ccx_arb(/*AUTOINST*/
		   // Outputs
		   .arb_dp_grant_a	({sinka[0], sinka[1],arb_dp_grant_a[5:0]}), // Templated
		   .arb_dp_q0_hold_a	({sinkb[0], sinkb[1],arb_dp_q0_hold_a[5:0]}), // Templated
		   .arb_dp_qsel0_a	({sinkc[0], sinkc[1],arb_dp_qsel0_a[5:0]}), // Templated
		   .arb_dp_qsel1_a	({sinkd[0], sinkd[1],arb_dp_qsel1_a[5:0]}), // Templated
		   .arb_dp_shift_x	({sinke[0], sinke[1],arb_dp_shift_x[5:0]}), // Templated
		   .arb_src0_grant_a	(arb_src0_grant_a),
		   .arb_src1_grant_a	(arb_src1_grant_a),
		   .arb_src2_grant_a	(arb_src2_grant_a),
		   .arb_src3_grant_a	(arb_src3_grant_a),
		   .arb_src4_grant_a	(arb_src4_grant_a),
		   .arb_src5_grant_a	(arb_src5_grant_a),
		   .arb_src6_grant_a	(),			 // Templated
		   .arb_src7_grant_a	(),			 // Templated
		   .ccx_dest_atom_x	(),			 // Templated
		   .ccx_dest_data_rdy_x	(ccx_dest_data_rdy_x),
		   .scan_out		(scan_out),
		   // Inputs
		   .adbginit_l		(adbginit_l),
		   .rclk		(rclk),
		   .reset_l		(reset_l),
		   .src0_arb_atom_q	(src0_arb_atom_q),
		   .src0_arb_req_q	(src0_arb_req_q),
		   .src1_arb_atom_q	(src1_arb_atom_q),
		   .src1_arb_req_q	(src1_arb_req_q),
		   .src2_arb_atom_q	(src2_arb_atom_q),
		   .src2_arb_req_q	(src2_arb_req_q),
		   .src3_arb_atom_q	(src3_arb_atom_q),
		   .src3_arb_req_q	(src3_arb_req_q),
		   .src4_arb_atom_q	(src4_arb_atom_q),
		   .src4_arb_req_q	(src4_arb_req_q),
		   .src5_arb_atom_q	(src5_arb_atom_q),
		   .src5_arb_req_q	(src5_arb_req_q),
		   .src6_arb_atom_q	(src6_arb_atom_q),
		   .src6_arb_req_q	(src6_arb_req_q),
		   .src7_arb_atom_q	(src7_arb_atom_q),
		   .src7_arb_req_q	(src7_arb_req_q),
		   .stall1_q		(stall1_q),
		   .stall2_q		(stall2_q),
		   .scan_in		(scan_in),
		   .se			(se));
   
endmodule // ccx_arb









