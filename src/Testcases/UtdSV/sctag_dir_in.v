// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_dir_in.v
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
module sctag_dir_in(/*AUTOARG*/
   // Outputs
   lkup_wr_data_c5, rddata_out_c6, so, 
   // Inputs
   lkup_wr_data_c4, rd_data1_out_c5, rd_data2_out_c5, rd_enable1_c5, 
   rclk, si, se, sehold
   );


output  [32:0]  lkup_wr_data_c5;	// Top	3 bits per bit pitch
output	[31:0]	rddata_out_c6;
output		so;

input   [32:0] 	lkup_wr_data_c4;
input	[31:0]	rd_data1_out_c5; // TOp 3 bits per bit pitch
input	[31:0]	rd_data2_out_c5; // Down 3 bits per bit pitch
input		rd_enable1_c5;	// Right
input		rclk;
input		si, se;
input		sehold;

wire	[31:0]	rddata_out_c5;
wire		clk_en;




// USE A MUX2 FLOP to replace sehold_mux & ff_lkup_wr_data_c5 
//mux2ds  #(33) sehold_mux(.dout (lkup_wr_data_c4_in[32:0]) ,
                //.in0(lkup_wr_data_c5[32:0]), .in1(lkup_wr_data_c4[32:0]),
                //.sel0(sehold), .sel1(~sehold));

clken_buf  clk_buf  (.clk(clk_en), .rclk(rclk), .enb_l(sehold), .tmb_l(~se));

// bits {0,1,2 } {3,4,5}.... occupy the same bit pitches 
dff_s   #(33) ff_lkup_wr_data_c5		// Use an 8X flop. no buffer following the flop.
              (.q   (lkup_wr_data_c5[32:0]),
               .din (lkup_wr_data_c4[32:0]),
               .clk (clk_en),
               .se  (se), .si  (), .so  ()
              ) ;



// bits {0,1,2 } {3,4,5}.... occupy the same bit pitches 
mux2ds  #(32) mux_rddata_out_c5(.dout (rddata_out_c5[31:0]) ,
                .in0(rd_data1_out_c5[31:0]), .in1(rd_data2_out_c5[31:0]),
                .sel0(rd_enable1_c5), .sel1(~rd_enable1_c5));

dff_s   	#(32) ff_rddata_out_c6		// Use an 16X buffer following a 1X mx flop.
              (.q   (rddata_out_c6[31:0]),
               .din (rddata_out_c5[31:0]),
               .clk (rclk),
               .se  (se), .si  (), .so  ()
              ) ;





endmodule
