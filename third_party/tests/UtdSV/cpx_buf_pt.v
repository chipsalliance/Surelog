// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: cpx_buf_pt.v
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


////////////////////////////////////////////////////////////////////////
// Local header file includes / local defines
////////////////////////////////////////////////////////////////////////


`include	"sys.h"
`include	"iop.h"

module cpx_buf_pt(/*AUTOARG*/
   // Outputs
   out0_l, out1_l, cpx_src_grant_cx, so, 
   // Inputs
   in0, in1, cpx_src_grant_ca, rclk, si, se
   );
   

   output [7:0]		out0_l;	
   output 		out1_l;	
   output [7:0]		cpx_src_grant_cx;	
   output 		so;

   input [7:0] 		in0;
   input            	in1;
   input [7:0]		cpx_src_grant_ca;	
   input 		rclk;
   input 		si;
   input 		se;
   
   assign out0_l[7:0] = ~in0[7:0];
   assign out1_l = ~in1;

   dff_s #(8) dff_ccx_com_src(
            .din           (cpx_src_grant_ca[7:0]),
	    .q             (cpx_src_grant_cx[7:0]),
	    .clk           (rclk),
	    .se            (1'b0),
	    .si            (8'd0),
	    .so            ());

   




endmodule // pcx_grant_ff


















