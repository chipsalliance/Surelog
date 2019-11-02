// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_stdatarep.v
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
module sctag_stdatarep(/*AUTOARG*/
   // Outputs
   rep_store_data_c2, sctag_scdata_stdecc_c2, 
   // Inputs
   arbdp_store_data_c2
   );


// The left has 78 M3 pins.
// This control block needs to be 300-350U tall and ~50-60U wide.
input  [77:0]	arbdp_store_data_c2; // LEft

output  [77:0]	rep_store_data_c2;  // Top
output  [77:0]	sctag_scdata_stdecc_c2;  // Right


// 78 data bits.
assign	sctag_scdata_stdecc_c2 = arbdp_store_data_c2 ;


assign	rep_store_data_c2 = arbdp_store_data_c2 ;


endmodule
