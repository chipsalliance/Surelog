// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_retbuf.v
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

module sctag_retbuf(/*AUTOARG*/
   // Outputs
   retdp_data_c7, retdp_ecc_c7, 
   // Inputs
   retdp_data_c7_buf, retdp_ecc_c7_buf
   );

// Use the same pin posit ions as that used for
// the lhs of retdp.

output  [127:0]  retdp_data_c7;
output  [ 27:0]  retdp_ecc_c7;

input  [127:0]  retdp_data_c7_buf;
input  [ 27:0]  retdp_ecc_c7_buf;



// arrange these buffers in 16 rows and 10 columns
// row0 ->{ data[2:0],ecc[6:0]}
// row1 ->{ data[12:3]}
// row2 ->{ data[22:13]}
// row3 ->{ data[31:23]}
// and so 0n. Buffer the outputs of each 
// bit with a 40x buffer/inverter.

assign	retdp_data_c7 = retdp_data_c7_buf ;
assign	retdp_ecc_c7 = retdp_ecc_c7_buf ;


endmodule
