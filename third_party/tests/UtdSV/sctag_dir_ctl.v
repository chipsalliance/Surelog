// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_dir_ctl.v
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
module sctag_dir_ctl(/*AUTOARG*/
   // Outputs
   so, rd_data_en_c4, wr_data_en_c4, cam_en_c4, rw_entry_c4, 
   inval_mask_c4, warm_rst_c4, rd_data_sel0_c5, rd_data_sel1_c5, 
   rd_data_sel_right_c6, rd_data_sel_left_c6, 
   // Inputs
   lkup_en_c4_buf, inval_mask_c4_buf, rw_dec_c4_buf, rd_en_c4_buf, 
   wr_en_c4_buf, rw_entry_c4_buf, dir_clear_c4_buf, rclk, si, se, 
   sehold
   );



input	[3:0]	lkup_en_c4_buf ;  // Right 

input	[7:0]	inval_mask_c4_buf ; // Right

input	[3:0]	rw_dec_c4_buf; // Right
input		rd_en_c4_buf ; // Right
input		wr_en_c4_buf ; // Right

input	[5:0]	rw_entry_c4_buf; // Right

input		dir_clear_c4_buf ; // Right


input	rclk;
input	si, se;
input	sehold; // POST_4.2 pin
output	so;

output	[3:0]	rd_data_en_c4, wr_data_en_c4; //( 0 leftTOp, 1 rightTOp, 2 leftBOttom 3 RightBottom )
output	[3:0]	cam_en_c4; //( 0 leftTOp, 1 rightTOp, 2 leftBOttom 3 RightBottom )

// Pins on TOP
output	[5:0]	rw_entry_c4;
output	[7:0]	inval_mask_c4; // one output
output		warm_rst_c4;


// Pin on left
output		rd_data_sel0_c5;
// pin on right
output		rd_data_sel1_c5;

// Pin on the right
output	rd_data_sel_right_c6; 

// Pin on left
output	rd_data_sel_left_c6;

wire		rd_data_sel_left_c5, rd_data_sel_right_c5;

wire	[3:0]   rd_data_en_c5;	//( 0 leftTOp, 1 rightTOp, 2 leftBOttom 3 RightBottom )


assign	warm_rst_c4 = dir_clear_c4_buf ;

assign	rd_data_en_c4 = {4{rd_en_c4_buf}} & rw_dec_c4_buf ;
//---------------\/ added to prevent a write and valid bit reset conflict \/-----------
assign	wr_data_en_c4 = {4{wr_en_c4_buf & ~warm_rst_c4 }} & rw_dec_c4_buf ;

dffe_s   #(2) ff_rd_data_en_c5_en (
		.q   (rd_data_en_c5[1:0]), .din (rd_data_en_c4[1:0]),
		.en(~sehold),
               	.clk (rclk), .se(se), .si  (), .so  ()
              ) ;

dff_s   #(2) ff_rd_data_en_c5 (
		.q   (rd_data_en_c5[3:2]), .din (rd_data_en_c4[3:2]),
               	.clk (rclk), .se(se), .si  (), .so  ()
              ) ;

assign	rd_data_sel0_c5	= rd_data_en_c5[0] ;
assign	rd_data_sel1_c5	= rd_data_en_c5[1] ;



assign	rd_data_sel_left_c5 = rd_data_en_c5[0] | rd_data_en_c5[2] ;

dff_s   #(1) ff_rd_data_sel_left_c6 (
		.q   (rd_data_sel_left_c6), .din (rd_data_sel_left_c5),
               	.clk (rclk), .se(se), .si  (), .so  ()
              ) ;

assign	rd_data_sel_right_c5 = rd_data_en_c5[1] | rd_data_en_c5[3] ;

dff_s   #(1) ff_rd_data_sel_right_c6 (
		.q   (rd_data_sel_right_c6), .din (rd_data_sel_right_c5),
               	.clk (rclk), .se(se), .si  (), .so  ()
              ) ;


assign	cam_en_c4[3:0] = lkup_en_c4_buf[3:0] ;
assign	inval_mask_c4[7:0]	= inval_mask_c4_buf[7:0] ;
assign	rw_entry_c4[5:0] =  rw_entry_c4_buf[5:0] ;


endmodule

