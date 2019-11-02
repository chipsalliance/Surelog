// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_dirg_buf.v
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
module sctag_dirg_buf(/*AUTOARG*/
   // Outputs
   lkup_wr_data_up_buf, lkup_wr_data_dn_buf, 
   // Inputs
   dirrep_dir_wr_par_c4, dir_vld_c4_l, lkup_addr8_c4, 
   tagdp_lkup_addr_c4
   );


input		dirrep_dir_wr_par_c4; // Right
input		dir_vld_c4_l; // Right
input		lkup_addr8_c4; // Right
input	[39:10]	tagdp_lkup_addr_c4; // Right Make sure that the pin order
				    // is same as in the driving block tagdp.

output	[32:0]	lkup_wr_data_up_buf;	// Top Msb to the left
output	[32:0]	lkup_wr_data_dn_buf;    // Bottom Msb to the left


// buffer should take 40-50 ps Max

assign	lkup_wr_data_up_buf = { tagdp_lkup_addr_c4, lkup_addr8_c4, dirrep_dir_wr_par_c4, dir_vld_c4_l };

assign	lkup_wr_data_dn_buf = { tagdp_lkup_addr_c4 , lkup_addr8_c4, dirrep_dir_wr_par_c4, dir_vld_c4_l }; 


endmodule
