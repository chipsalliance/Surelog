// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: cpx_datacx2_ff.v
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


module cpx_datacx2_ff(/*AUTOARG*/
   // Outputs
   cpx_spc_data_cx2, cpx_spc_data_rdy_cx2, so, 
   // Inputs
   cpx_spc_data_cx_l, cpx_spc_data_rdy_cx, rclk, si, se
   );
   

   output [`CPX_WIDTH-1:0]		cpx_spc_data_cx2;	
   output 		cpx_spc_data_rdy_cx2;	
   output 		so;
   
   input [`CPX_WIDTH-1:0]		cpx_spc_data_cx_l;	
   input 		cpx_spc_data_rdy_cx;	
   input 		rclk;
   input 		si;
   input 		se;
   

   wire [`CPX_WIDTH-1:0]		cpx_spc_data_cx2_l;	
   
   
   dff_s #(`CPX_WIDTH) dff_ccx_data_spc(
            .din           (cpx_spc_data_cx_l[`CPX_WIDTH-1:0]),
	    .q             (cpx_spc_data_cx2_l[`CPX_WIDTH-1:0]),
	    .clk           (rclk),
	    .se            (1'b0),
	    .si            (`CPX_WIDTH'd0),
	    .so            ());



assign cpx_spc_data_cx2 = ~cpx_spc_data_cx2_l; 



      dff_s #(1) dff_ccx_datardy_spc(
            .din           (cpx_spc_data_rdy_cx),
	    .q             (cpx_spc_data_rdy_cx2),
	    .clk           (rclk),
	    .se            (1'b0),
	    .si            (1'd0),
	    .so            ());


endmodule // cpx_grant_ff









 
