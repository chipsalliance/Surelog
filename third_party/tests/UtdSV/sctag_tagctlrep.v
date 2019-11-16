// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_tagctlrep.v
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
module sctag_tagctlrep(/*AUTOARG*/
   // Outputs
   sctag_scdata_set_c2, sctag_scdata_way_sel_c2, 
   sctag_scdata_col_offset_c2, sctag_scdata_rd_wr_c2, 
   sctag_scdata_word_en_c2, sctag_scdata_fbrd_c3, 
   sctag_scdata_fb_hit_c3, 
   // Inputs
   scdata_set_c2, scdata_way_sel_c2, scdata_col_offset_c2, 
   scdata_rd_wr_c2, scdata_word_en_c2, scdata_fbrd_c3, 
   scdata_fb_hit_c3
   );


input  [9:0]	scdata_set_c2; // Left
input  [11:0]  scdata_way_sel_c2;
input  [3:0]   scdata_col_offset_c2;
input          scdata_rd_wr_c2;
input  [15:0]  scdata_word_en_c2;
input		scdata_fbrd_c3;
input		scdata_fb_hit_c3;


output  [9:0]	sctag_scdata_set_c2; // Right
output  [11:0]  sctag_scdata_way_sel_c2; // Right
output  [3:0]   sctag_scdata_col_offset_c2; // Right
output          sctag_scdata_rd_wr_c2; // Right
output  [15:0]  sctag_scdata_word_en_c2; // Right
output		sctag_scdata_fbrd_c3; // Right
output		sctag_scdata_fb_hit_c3; // Right


// 46 control bits.
assign	sctag_scdata_fb_hit_c3 = scdata_fb_hit_c3;
assign	sctag_scdata_fbrd_c3 = scdata_fbrd_c3 ;
assign	sctag_scdata_word_en_c2 = scdata_word_en_c2;
assign	sctag_scdata_rd_wr_c2 = scdata_rd_wr_c2 ;
assign	sctag_scdata_col_offset_c2 = scdata_col_offset_c2 ;
assign	sctag_scdata_way_sel_c2 = scdata_way_sel_c2;  
assign	sctag_scdata_set_c2 = scdata_set_c2 ; 




endmodule
