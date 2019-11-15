// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: io_cpx_reqdata_ff.v
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


module io_cpx_reqdata_ff(/*AUTOARG*/
   // Outputs
   io_cpx_data_ca2, io_cpx_req_cq2, scan_out, 
   // Inputs
   io_cpx_data_ca, io_cpx_req_cq, rclk, scan_in, se
   );
   

   output [`CPX_WIDTH-1:0]		io_cpx_data_ca2;	
   output [7:0]		io_cpx_req_cq2;	
   output 		scan_out;
   
   input [`CPX_WIDTH-1:0]		io_cpx_data_ca;	
   input [7:0]		io_cpx_req_cq;	

   input 		rclk;
   input 		scan_in;
   input 		se;
   

   
   dff_s #(`CPX_WIDTH) dff_io_cpx_data(
            .din           (io_cpx_data_ca[`CPX_WIDTH-1:0]),
	    .q             (io_cpx_data_ca2[`CPX_WIDTH-1:0]),
	    .clk           (rclk),
	    .se            (se),
	    .si            (`CPX_WIDTH'd0),
	    .so            ());




      dff_s #(8) dff_cpx_datardy_io(
            .din           (io_cpx_req_cq[7:0]),
	    .q             (io_cpx_req_cq2[7:0]),
	    .clk           (rclk),
	    .se            (se),
	    .si            (8'd0),
	    .so            ());


endmodule // io_cpxdata_cq2











 
