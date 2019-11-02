// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: pcx_data_px2.v
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

module pcx_data_px2(/*AUTOARG*/
   // Outputs
   pcx_data_px2, pcx_data_rdy_px2, pcx_stall_pq_buf, so, 
   // Inputs
   pcx_data_px_l, pcx_data_rdy_px, pcx_stall_pq, rclk, si, se
   );
   

   output [`PCX_WIDTH-1:0]		pcx_data_px2;	
   output 		pcx_data_rdy_px2;	
   output 		pcx_stall_pq_buf;	
   output 		so;
   
   input [`PCX_WIDTH-1:0]		pcx_data_px_l;	
   input 		pcx_data_rdy_px;	
   input 		pcx_stall_pq;	

   input 		rclk;
   input 		si;
   input 		se;
   

   wire [`PCX_WIDTH-1:0]		pcx_data_px2_l;	
   
   
   dff_s #(`PCX_WIDTH) dff_cpx_data(
            .din           (pcx_data_px_l[`PCX_WIDTH-1:0]),
	    .q             (pcx_data_px2_l[`PCX_WIDTH-1:0]),
	    .clk           (rclk),
	    .se            (1'b0),
	    .si            (`PCX_WIDTH'd0),
	    .so            ());

assign pcx_data_px2 = ~pcx_data_px2_l; 



      dff_s #(1) dff_cpx_datardy(
            .din           (pcx_data_rdy_px),
	    .q             (pcx_data_rdy_px2),
	    .clk           (rclk),
	    .se            (1'b0),
	    .si            (1'd0),
	    .so            ());


assign pcx_stall_pq_buf  =  pcx_stall_pq ;

endmodule // pcx_data_px2











 
