// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: pcx_buf_pt.v
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

module pcx_buf_pt(/*AUTOARG*/
   // Outputs
   out0_l, out1_l, pcx_spc_grant_px, so, 
   // Inputs
   in0, in1, pcx_spc_grant_buf_pa, rclk, si, se
   );
   

   output [4:0]		out0_l;	
   output 		out1_l;	
   output [4:0]		pcx_spc_grant_px;	
   output 		so;
   

   input [4:0] 		in0;
   input            	in1;
   input [4:0]		pcx_spc_grant_buf_pa;	

   input 		rclk;
   input 		si, se;
   
   dff_s #(5) dff_ccx_com_spc(
            .din           (pcx_spc_grant_buf_pa[4:0]),
	    .q             (pcx_spc_grant_px[4:0]),
	    .clk           (rclk),
	    .se            (1'b0),
	    .si            (5'd0),
	    .so            ());

   
   assign out0_l[4:0] = ~in0[4:0];
   assign out1_l = ~in1;
   




endmodule // pcx_grant_ff


















