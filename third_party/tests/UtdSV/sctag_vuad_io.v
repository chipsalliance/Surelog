// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_vuad_io.v
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
////////////////////////////////////////////////////////////////////////

module sctag_vuad_io
 (/*AUTOARG*/
   // Outputs
   data_out_io, array_data_in_buf_top, array_data_in_buf_bottom, 
   // Inputs
   data_out_col1, data_out_col2, data_out_col3, data_out_col4, 
   array_data_in, mux_sel
   ) ;


input	[25:0]	 data_out_col1; // from  vuad_col_dp.
input	[25:0]	 data_out_col2; // from  vuad_col_dp.
input	[25:0]	 data_out_col3; // from  vuad_col_dp.
input	[25:0]	 data_out_col4; // from  vuad_col_dp.

input	[25:0]	 array_data_in;

output	[25:0]	 data_out_io ; // output to vuad dp.
output	[25:0]	 array_data_in_buf_top;
output	[25:0]	 array_data_in_buf_bottom;

input	[3:0]	 mux_sel;  // 4-1 mux output to vuad dp.


assign	array_data_in_buf_top = array_data_in ; // use a 40x buffer
assign	array_data_in_buf_bottom = array_data_in ; // use another 40x buffer


mux4ds  #(26)   mux_data_out_io (.dout (data_out_io[25:0]),
                             .in0(data_out_col1[25:0]),
                             .in1(data_out_col2[25:0]),
                             .in2(data_out_col3[25:0]),
                             .in3(data_out_col4[25:0]),
                             .sel0(mux_sel[0]),
                             .sel1(mux_sel[1]),
                             .sel2(mux_sel[2]),
                             .sel3(mux_sel[3]));

endmodule
