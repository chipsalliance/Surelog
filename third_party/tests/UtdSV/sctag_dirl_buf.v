// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_dirl_buf.v
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
module sctag_dirl_buf(/*AUTOARG*/
   // Outputs
   lkup_en_c4_buf, inval_mask_c4_buf, rw_dec_c4_buf, rd_en_c4_buf, 
   wr_en_c4_buf, rw_entry_c4_buf, lkup_wr_data_c4_buf, 
   dir_clear_c4_buf, 
   // Inputs
   rd_en_c4, wr_en_c4, inval_mask_c4, rw_row_en_c4, rw_panel_en_c4, 
   rw_entry_c4, lkup_row_en_c4, lkup_panel_en_c4, lkup_wr_data_c4, 
   dir_clear_c4
   );


input		rd_en_c4;	// Right
input		wr_en_c4;	// Right
input	[7:0]	inval_mask_c4;	// Right
input	[1:0]	rw_row_en_c4;	// Right
input	[3:0]	rw_panel_en_c4;	// Right
input	[5:0]	rw_entry_c4;	// Right
input	[1:0]	lkup_row_en_c4; // qualified already	// Right
input	[3:0]	lkup_panel_en_c4; // qualified already	// Right
input	[32:0]	lkup_wr_data_c4;  // Bottom
input		dir_clear_c4; // Right

output	[7:0]	lkup_en_c4_buf ;  // Left
output	[7:0]	inval_mask_c4_buf ; // Left
output	[7:0]	rw_dec_c4_buf; // Left
output		rd_en_c4_buf ; // Left
output		wr_en_c4_buf ; // Left
output	[5:0]	rw_entry_c4_buf; // Left
output	[32:0]	lkup_wr_data_c4_buf; // Left 31(top) to 0(bottom)
output		dir_clear_c4_buf; // Left




assign	inval_mask_c4_buf = inval_mask_c4 ;

assign	rd_en_c4_buf = rd_en_c4 ;

assign	wr_en_c4_buf = wr_en_c4 ;

assign	rw_entry_c4_buf = rw_entry_c4 ;

assign	lkup_wr_data_c4_buf = lkup_wr_data_c4 ;

assign	lkup_en_c4_buf[0] = lkup_row_en_c4[0] & lkup_panel_en_c4[0] ;
assign	lkup_en_c4_buf[1] = lkup_row_en_c4[0] & lkup_panel_en_c4[1] ;
assign	lkup_en_c4_buf[2] = lkup_row_en_c4[0] & lkup_panel_en_c4[2] ;
assign	lkup_en_c4_buf[3] = lkup_row_en_c4[0] & lkup_panel_en_c4[3] ;
assign	lkup_en_c4_buf[4] = lkup_row_en_c4[1] & lkup_panel_en_c4[0] ;
assign	lkup_en_c4_buf[5] = lkup_row_en_c4[1] & lkup_panel_en_c4[1] ;
assign	lkup_en_c4_buf[6] = lkup_row_en_c4[1] & lkup_panel_en_c4[2] ;
assign	lkup_en_c4_buf[7] = lkup_row_en_c4[1] & lkup_panel_en_c4[3] ;
assign	dir_clear_c4_buf = dir_clear_c4 ;

assign	rw_dec_c4_buf[0] = rw_row_en_c4[0] & rw_panel_en_c4[0] ;
assign	rw_dec_c4_buf[1] = rw_row_en_c4[0] & rw_panel_en_c4[1] ;
assign	rw_dec_c4_buf[2] = rw_row_en_c4[0] & rw_panel_en_c4[2] ;
assign	rw_dec_c4_buf[3] = rw_row_en_c4[0] & rw_panel_en_c4[3] ;
assign	rw_dec_c4_buf[4] = rw_row_en_c4[1] & rw_panel_en_c4[0] ;
assign	rw_dec_c4_buf[5] = rw_row_en_c4[1] & rw_panel_en_c4[1] ;
assign	rw_dec_c4_buf[6] = rw_row_en_c4[1] & rw_panel_en_c4[2] ;
assign	rw_dec_c4_buf[7] = rw_row_en_c4[1] & rw_panel_en_c4[3] ;

endmodule

