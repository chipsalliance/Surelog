// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: scdata_periph_io.v
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

module scdata_periph_io(/*AUTOARG*/
   // Outputs
   so, scdata_scbuf_decc_out_c7, scbuf_scdata_fbdecc_c5, 
   // Inputs
   scdata_decc_out_c6, scbuf_scdata_fbdecc_c4, rclk, se, si
   );

   input [623:0]  scdata_decc_out_c6;
   input [623:0]  scbuf_scdata_fbdecc_c4;
   input 	  rclk, se, si;   
   
   output 	  so;
   output [623:0] scdata_scbuf_decc_out_c7;
   output [623:0] scbuf_scdata_fbdecc_c5;

   wire [623:0]   scdata_decc_out_c6;
   

   dff_s #(624)  ff_scbuf_scdata_fbdecc_c5 (.q(scbuf_scdata_fbdecc_c5[623:0]),
					  .din(scbuf_scdata_fbdecc_c4[623:0]),
					  .clk(rclk), .se(se), .si(), .so());

   dff_s #(624)  ff_scdata_scbuf_decc_out_c7 (.q(scdata_scbuf_decc_out_c7[623:0]),
					    .din(scdata_decc_out_c6[623:0]),
					    .clk(rclk), .se(se), .si(), .so());

endmodule // scdata_periph_io

