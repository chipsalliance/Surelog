// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: scdata_ctr_io.v
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

module scdata_ctr_io(/*AUTOARG*/
   // Outputs
   so, scdata_sctag_decc_c6_ctr, scdata_decc_out_c6, 
   cache_decc_in_c3, cache_col_offset_c3, cache_word_en_c3, 
   cache_way_sel_c3_0, cache_set_c3_0, cache_wr_en_c3_0, 
   cache_way_sel_c3_1, cache_set_c3_1, cache_wr_en_c3_1, 
   cache_way_sel_c3_2, cache_set_c3_2, cache_wr_en_c3_2, 
   cache_way_sel_c3_3, cache_set_c3_3, cache_wr_en_c3_3, 
   // Inputs
   sctag_scdata_way_sel_c2_buf, sctag_scdata_rd_wr_c2_buf, 
   sctag_scdata_set_c2_buf, sctag_scdata_col_offset_c2_buf, 
   sctag_scdata_word_en_c2_buf, sctag_scdata_fbrd_c3_buf, 
   scbuf_scdata_fbdecc_c5, sctag_scdata_fb_hit_c3_buf, 
   sctag_scdata_stdecc_c2_buf, cache_decc_out_c5, rclk, se, si
   );

   input [11:0]    sctag_scdata_way_sel_c2_buf; // way select
   input 	   sctag_scdata_rd_wr_c2_buf; // Rd/WRbar 
   input [9:0] 	   sctag_scdata_set_c2_buf; //  index 
   input [3:0] 	   sctag_scdata_col_offset_c2_buf; // 16B column that is accessed
   input [15:0]    sctag_scdata_word_en_c2_buf; // word enables for stores
   input 	   sctag_scdata_fbrd_c3_buf; // if fill 1 else 0
   input [623:0]   scbuf_scdata_fbdecc_c5;
   input 	   sctag_scdata_fb_hit_c3_buf; // use bypass data from the Fill Buffer.
   input [77:0]    sctag_scdata_stdecc_c2_buf; // store data from sctag
   input [623:0]   cache_decc_out_c5; // data output from memory array
   input 	   rclk, se, si;

   output 	   so;
   output [155:0]  scdata_sctag_decc_c6_ctr;
   output [623:0]  scdata_decc_out_c6;
   output [623:0]  cache_decc_in_c3;
   output [3:0]    cache_col_offset_c3;
   output [15:0]   cache_word_en_c3;

   output [11:0]   cache_way_sel_c3_0;
   output [9:0]    cache_set_c3_0;
   output 	   cache_wr_en_c3_0;
   
   output [11:0]   cache_way_sel_c3_1;
   output [9:0]    cache_set_c3_1;
   output 	   cache_wr_en_c3_1;
   
   output [11:0]   cache_way_sel_c3_2;
   output [9:0]    cache_set_c3_2;
   output 	   cache_wr_en_c3_2;
   
   output [11:0]   cache_way_sel_c3_3;
   output [9:0]    cache_set_c3_3;
   output 	   cache_wr_en_c3_3;
   
   wire [11:0] 	   cache_way_sel_c3;
   wire [9:0] 	   cache_set_c3;
   wire 	   cache_wr_en_c3;

   wire [77:0] 	   st_decc_out_c3;
   wire [155:0]    scdata_sctag_decc_c5;
   wire  	   sel_decc_c5_23;
   wire [155:0]    decc_c5_01;
   wire [155:0]    decc_c5_23;
   wire [3:0] 	   cache_col_offset_c4, cache_col_offset_c5 ;
   wire 	   cache_sel_fbdecc_c4, cache_sel_fbdecc_c5 ;
   wire 	   cache_fb_hit_c4, cache_fb_hit_c5 ;
   wire [155:0]	   scdata_sctag_decc_c6_ctr ;
   wire [623:0]    rd_decc_out_c5;
   wire [623:0]    scdata_decc_out_c5;
   wire [623:0]    scdata_decc_out_c6;


   // way selects
   dff_s #(12)   ff_cache_way_sel_c3 (.q(cache_way_sel_c3[11:0]),
				    .din(sctag_scdata_way_sel_c2_buf[11:0]),
				    .clk(rclk), .se(se), .si(), .so());

   assign 	   cache_way_sel_c3_0 = cache_way_sel_c3;
   assign 	   cache_way_sel_c3_1 = cache_way_sel_c3;
   assign 	   cache_way_sel_c3_2 = cache_way_sel_c3;
   assign 	   cache_way_sel_c3_3 = cache_way_sel_c3;   
   
   // set
   dff_s #(10)   ff_cache_set_c3 (.q(cache_set_c3[9:0]),
				.din(sctag_scdata_set_c2_buf[9:0]),
				.clk(rclk), .se(se), .si(), .so());

   assign 	   cache_set_c3_0 = cache_set_c3;
   assign 	   cache_set_c3_1 = cache_set_c3;
   assign 	   cache_set_c3_2 = cache_set_c3;
   assign 	   cache_set_c3_3 = cache_set_c3;
   
   // col offset
   dff_s #(4)    ff_cache_col_offset_c3 (.q(cache_col_offset_c3[3:0]),
				       .din(sctag_scdata_col_offset_c2_buf[3:0]),
				       .clk(rclk), .se(se), .si(), .so());

   dff_s #(4)    ff_cache_col_offset_c4 (.q(cache_col_offset_c4[3:0]),
				       .din(cache_col_offset_c3[3:0]),
				       .clk(rclk), .se(se), .si(), .so());
   dff_s #(4)    ff_cache_col_offset_c5 (.q(cache_col_offset_c5[3:0]),
				       .din(cache_col_offset_c4[3:0]),
				       .clk(rclk), .se(se), .si(), .so());

   
   
   // word enables for writes
   dff_s #(16)   ff_cache_word_en_c3 (.q(cache_word_en_c3[15:0]),
				    .din(sctag_scdata_word_en_c2_buf[15:0]),
				    .clk(rclk), .se(se), .si(), .so());

   // write enable into cache
   dff_s #(1)   ff_cache_wr_en_c3 (.q(cache_wr_en_c3),
				 .din(~sctag_scdata_rd_wr_c2_buf),
				 .clk(rclk), .se(se), .si(), .so());

   assign 	   cache_wr_en_c3_0 = cache_wr_en_c3;
   assign 	   cache_wr_en_c3_1 = cache_wr_en_c3;
   assign 	   cache_wr_en_c3_2 = cache_wr_en_c3;
   assign 	   cache_wr_en_c3_3 = cache_wr_en_c3;
   
   // sel fill data instead of store data.
   dff_s #(1)   ff_cache_sel_fbdecc_c4 (.q(cache_sel_fbdecc_c4),
				      .din(sctag_scdata_fbrd_c3_buf),
				      .clk(rclk), .se(se), .si(), .so());
   dff_s #(1)   ff_cache_sel_fbdecc_c5 (.q(cache_sel_fbdecc_c5),
				      .din(cache_sel_fbdecc_c4),
				      .clk(rclk), .se(se), .si(), .so());

   // sel fill buffer data over l2$ data.
   dff_s #(1)   ff_cache_fb_hit_c4 (.q(cache_fb_hit_c4),
				  .din(sctag_scdata_fb_hit_c3_buf),
				  .clk(rclk), .se(se), .si(), .so());
   dff_s #(1)   ff_cache_fb_hit_c5 (.q(cache_fb_hit_c5),
				  .din(cache_fb_hit_c4),
				  .clk(rclk), .se(se), .si(), .so());

   // store data
   dff_s #(78)   ff_st_decc_out_c3 (.q(st_decc_out_c3[77:0]),
				       .din(sctag_scdata_stdecc_c2_buf[77:0]),
				       .clk(rclk), .se(se), .si(), .so());

   
   mux2ds #(624)  mux_cache_decc_in_c3 (.dout(cache_decc_in_c3[623:0]),
					.in0({8{st_decc_out_c3[77:0]}}),
					.in1(scbuf_scdata_fbdecc_c5[623:0]),
					.sel0(~cache_sel_fbdecc_c5),
				       	.sel1(cache_sel_fbdecc_c5));
   
   dff_s #(156)  ff_scdata_sctag_decc_c6 (.q(scdata_sctag_decc_c6_ctr[155:0]),
				     	.din(scdata_sctag_decc_c5[155:0]),
				     	.clk(rclk), .se(se), .si(), .so());
   
   


   mux2ds #(624)  mux_rd_decc_out_c5 (.dout(rd_decc_out_c5[623:0]),
				      .in0(cache_decc_out_c5[623:0]),
				      .in1(scbuf_scdata_fbdecc_c5[623:0]),
				      .sel0(~cache_fb_hit_c5),
				      .sel1(cache_fb_hit_c5));

   assign 	   scdata_decc_out_c5[623:0] = rd_decc_out_c5[623:0];
   
   dff_s #(624)  ff_scdata_decc_out_c6 (.q(scdata_decc_out_c6[623:0]),
				      .din(scdata_decc_out_c5[623:0]),
				      .clk(rclk), .se(se), .si(), .so());

   ////////////////////////////////////////////////////////////////////////
   // The 64B-16B mux will be performed in the full custom data array.
   // if the col offsets are non one hot, sctag will cause the hold signal
   // to be high causing the output mux to hold its old value.
   ////////////////////////////////////////////////////////////////////////
   
   
   assign 	   sel_decc_c5_23 = cache_col_offset_c5[3] || cache_col_offset_c5[2];
   
   mux2ds #(156)  mux_decc_c5_01 (.dout(decc_c5_01[155:0]),
				  .in0(rd_decc_out_c5[155:0]),
				  .in1(rd_decc_out_c5[311:156]),
				  .sel0(cache_col_offset_c5[0]),
				  .sel1(~cache_col_offset_c5[0]));
   
   mux2ds #(156)  mux_decc_c5_23 (.dout(decc_c5_23[155:0]),
				  .in0(rd_decc_out_c5[467:312]),
				  .in1(rd_decc_out_c5[623:468]),
				  .sel0(cache_col_offset_c5[2]),
				  .sel1(~cache_col_offset_c5[2]));
   
   mux2ds #(156)  mux_scdata_sctag_decc_c5 (.dout(scdata_sctag_decc_c5[155:0]),
					    .in0(decc_c5_01[155:0]),
					    .in1(decc_c5_23[155:0]),
					    .sel0(~sel_decc_c5_23),
					    .sel1(sel_decc_c5_23));
   
endmodule // scdata_ctr_io

