// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: cpx_io_grant_ff.v
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


module cpx_io_grant_ff(/*AUTOARG*/
   // Outputs
   cpx_io_grant_cx2, so, 
   // Inputs
   cpx_io_grant_cx, rclk, si, se
   );
   
 
   output [7:0]		cpx_io_grant_cx2;	
   output 		so;
   

   input [7:0]		cpx_io_grant_cx;	
   input 		rclk;
   input 		si;
   input 		se;
   
   dff_s #(8) dff_ccx_com_src(
            .din           (cpx_io_grant_cx[7:0]),
	    .q             (cpx_io_grant_cx2[7:0]),
	    .clk           (rclk),
	    .se            (1'b0),
	    .si            (8'd0),
	    .so            ());


endmodule // cpx_io_grant_ff


 






