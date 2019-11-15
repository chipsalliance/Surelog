// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_vuad_ctl.v
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

module sctag_vuad_ctl
 (/*AUTOARG*/
   // Outputs
   so, rd_addr1_r0, rd_addr2_r0, rd_addr_sel_r0, wr_addr_r0, 
   word_en_r0, wr_en_r0c0, wr_en_r0c1, mux1_h_sel_r0, mux1_l_sel_r0, 
   mux2_sel_r0, rd_en_r0, rd_addr1_r1, rd_addr2_r1, rd_addr_sel_r1, 
   wr_addr_r1, word_en_r1, wr_en_r1c0, wr_en_r1c1, rd_en_r1, 
   rd_addr1_r2, rd_addr2_r2, rd_addr_sel_r2, wr_addr_r2, word_en_r2, 
   wr_en_r2c0, wr_en_r2c1, mux1_h_sel_r2, mux1_l_sel_r2, mux2_sel_r2, 
   rd_en_r2, rd_addr1_r3, rd_addr2_r3, rd_addr_sel_r3, wr_addr_r3, 
   word_en_r3, wr_en_r3c0, wr_en_r3c1, rd_en_r3, rd_addr1_r4, 
   rd_addr2_r4, rd_addr_sel_r4, wr_addr_r4, word_en_r4, wr_en_r4c0, 
   wr_en_r4c1, mux1_h_sel_r4, mux1_l_sel_r4, mux2_sel_r4, rd_en_r4, 
   rd_addr1_r5, rd_addr2_r5, rd_addr_sel_r5, wr_addr_r5, word_en_r5, 
   wr_en_r5c0, wr_en_r5c1, rd_en_r5, rd_addr1_r6, rd_addr2_r6, 
   rd_addr_sel_r6, wr_addr_r6, word_en_r6, wr_en_r6c0, wr_en_r6c1, 
   mux1_h_sel_r6, mux1_l_sel_r6, mux2_sel_r6, rd_en_r6, rd_addr1_r7, 
   rd_addr2_r7, rd_addr_sel_r7, wr_addr_r7, word_en_r7, wr_en_r7c0, 
   wr_en_r7c1, rd_en_r7, mux_sel, 
   // Inputs
   rd_addr1, rd_addr2, rd_addr_sel, wr_addr, wr_en0, wr_en1, 
   array_rd_en, rclk, si, se, sehold
   ) ;

input	[9:0]	 rd_addr1;
input	[9:0]	 rd_addr2;
input		 rd_addr_sel;
input	[9:0]	 wr_addr;
input		 wr_en0;
input		 wr_en1;
input		 array_rd_en;

input		rclk;
input		si, se;

input		sehold; // POST_4.2
output		so;


output	[4:0]	 rd_addr1_r0;
output	[4:0]	 rd_addr2_r0;
output		 rd_addr_sel_r0;
output	[4:0]	 wr_addr_r0; // address bits 6:2
output	[3:0]	 word_en_r0; // decoded address bits 1:0
output		 wr_en_r0c0; // decoded address bits 9:7
output		 wr_en_r0c1; // decoded address bits 9:7
output	[3:0]	mux1_h_sel_r0;
output	[3:0]	mux1_l_sel_r0;
output		mux2_sel_r0;
output	rd_en_r0;

output	[4:0]	 rd_addr1_r1;
output	[4:0]	 rd_addr2_r1;
output		 rd_addr_sel_r1;
output	[4:0]	 wr_addr_r1; // address bits 6:2
output	[3:0]	 word_en_r1; // decoded address bits 1:0
output		 wr_en_r1c0; // decoded address bits 9:7
output		 wr_en_r1c1; // decoded address bits 9:7
output	rd_en_r1;

output	[4:0]	 rd_addr1_r2;
output	[4:0]	 rd_addr2_r2;
output		 rd_addr_sel_r2;
output	[4:0]	 wr_addr_r2; // address bits 6:2
output	[3:0]	 word_en_r2; // decoded address bits 1:0
output		 wr_en_r2c0; // decoded address bits 9:7
output		 wr_en_r2c1; // decoded address bits 9:7
output	[3:0]	mux1_h_sel_r2;
output	[3:0]	mux1_l_sel_r2;
output		mux2_sel_r2;
output	rd_en_r2;

output	[4:0]	 rd_addr1_r3;
output	[4:0]	 rd_addr2_r3;
output		 rd_addr_sel_r3;
output	[4:0]	 wr_addr_r3; // address bits 6:2
output	[3:0]	 word_en_r3; // decoded address bits 1:0
output		 wr_en_r3c0; // decoded address bits 9:7
output		 wr_en_r3c1; // decoded address bits 9:7
output	rd_en_r3;

output	[4:0]	 rd_addr1_r4;
output	[4:0]	 rd_addr2_r4;
output		 rd_addr_sel_r4;
output	[4:0]	 wr_addr_r4; // address bits 6:2
output	[3:0]	 word_en_r4; // decoded address bits 1:0
output		 wr_en_r4c0; // decoded address bits 9:7
output		 wr_en_r4c1; // decoded address bits 9:7
output	[3:0]	mux1_h_sel_r4;
output	[3:0]	mux1_l_sel_r4;
output		mux2_sel_r4;
output	rd_en_r4;

output	[4:0]	 rd_addr1_r5;
output	[4:0]	 rd_addr2_r5;
output		 rd_addr_sel_r5;
output	[4:0]	 wr_addr_r5; // address bits 6:2
output	[3:0]	 word_en_r5; // decoded address bits 1:0
output		 wr_en_r5c0; // decoded address bits 9:7
output		 wr_en_r5c1; // decoded address bits 9:7
output	rd_en_r5;

output	[4:0]	 rd_addr1_r6;
output	[4:0]	 rd_addr2_r6;
output		 rd_addr_sel_r6;
output	[4:0]	 wr_addr_r6; // address bits 6:2
output	[3:0]	 word_en_r6; // decoded address bits 1:0
output		 wr_en_r6c0; // decoded address bits 9:7
output		 wr_en_r6c1; // decoded address bits 9:7
output	[3:0]	mux1_h_sel_r6;
output	[3:0]	mux1_l_sel_r6;
output		mux2_sel_r6;
output	rd_en_r6;

output	[4:0]	 rd_addr1_r7;
output	[4:0]	 rd_addr2_r7;
output		 rd_addr_sel_r7;
output	[4:0]	 wr_addr_r7; // address bits 6:2
output	[3:0]	 word_en_r7; // decoded address bits 1:0
output		 wr_en_r7c0; // decoded address bits 9:7
output		 wr_en_r7c1; // decoded address bits 9:7
output	rd_en_r7;

output	[3:0]	mux_sel; // middle mux select.

// Write signals.
wire	[4:0]	wr_addr_entry;
wire	[3:0]	wr_word_en;
wire	[7:0]	wr_en;

wire	[1:0]	 addr1to0_px2;
wire		 addr7_px2;
wire	[1:0]	 addr9to8_px2;

wire	[1:0]	 addr1to0_c1;
wire		 addr7_c1;
wire	[1:0]	 addr9to8_c1;


// Logic at the top of vuad ctl.
assign	wr_addr_entry = wr_addr[6:2] ;

assign	wr_word_en[0]  = ~wr_addr[1] & ~wr_addr[0] ; 
assign	wr_word_en[1]  = ~wr_addr[1] & wr_addr[0] ; 
assign	wr_word_en[2]  = wr_addr[1] & ~wr_addr[0] ; 
assign	wr_word_en[3]  = wr_addr[1] & wr_addr[0] ; 


assign  wr_en[0] = ~wr_addr[9] & ~wr_addr[8] & ~wr_addr[7] ;
assign  wr_en[1] = ~wr_addr[9] & ~wr_addr[8] & wr_addr[7] ;
assign  wr_en[2] = ~wr_addr[9] & wr_addr[8] & ~wr_addr[7] ;
assign  wr_en[3] = ~wr_addr[9] & wr_addr[8] & wr_addr[7] ;
assign  wr_en[4] = wr_addr[9] & ~wr_addr[8] & ~wr_addr[7] ;
assign  wr_en[5] = wr_addr[9] & ~wr_addr[8] & wr_addr[7] ;
assign  wr_en[6] = wr_addr[9] & wr_addr[8] & ~wr_addr[7] ;
assign  wr_en[7] = wr_addr[9] & wr_addr[8] & wr_addr[7] ;

/////// ----\/ Fix for macrotest \/---------
// INdex <9:0> is used for array access as follows:
// <1:0> for 4:1 col muxing.
// <6:2> as the read address.
// <7> is used to enable odd subarrays.
// <9:8> is used to for the final 4:1 mux in io_left and io_right
/////// ----\/ Fix for macrotest \/---------

wire	clk_1 ; // is a clk gated with sehold.

clken_buf  clk_buf  (.clk(clk_1), .rclk(rclk), .enb_l(sehold), .tmb_l(~se));


// LSb 1:0
mux2ds #(2) mux_addr1to0_px2(.dout (addr1to0_px2[1:0] ) ,
                        .in0(rd_addr1[1:0]),
                        .in1(rd_addr2[1:0]),
                        .sel0(rd_addr_sel),
                        .sel1(~rd_addr_sel));

dff_s    #(2) ff_addr1to0_c1   (.din(addr1to0_px2[1:0]), .clk(clk_1),
                .q(addr1to0_c1[1:0]), .se(se), .si(), .so());

// LSb 9:8
mux2ds #(2) mux_addr9to8_px2(.dout (addr9to8_px2[1:0] ) ,
                        .in0(rd_addr1[9:8]),
                        .in1(rd_addr2[9:8]),
                        .sel0(rd_addr_sel),
                        .sel1(~rd_addr_sel));

dff_s    #(2) ff_addr9to8_c1   (.din(addr9to8_px2[1:0]), .clk(clk_1),
                .q(addr9to8_c1[1:0]), .se(se), .si(), .so());


// Lsb 7
mux2ds #(1) mux_addr7_px2(.dout (addr7_px2) ,
                        .in0(rd_addr1[7]),
                        .in1(rd_addr2[7]),
                        .sel0(rd_addr_sel),
                        .sel1(~rd_addr_sel));

dff_s    #(1) ff_addr7_c1   (.din(addr7_px2), .clk(clk_1),
                .q(addr7_c1), .se(se), .si(), .so());




// Mux2 of the read address.
// Buffer appropriately to get the following
// signals.


// XY = 75 X 50
assign	rd_addr1_r0 = rd_addr1[6:2];
assign	rd_addr2_r0 = rd_addr2[6:2];
assign	rd_addr_sel_r0 = rd_addr_sel ;
assign	wr_addr_r0 = wr_addr_entry ;
assign	word_en_r0 = wr_word_en ;
assign	wr_en_r0c0 = wr_en[0] & wr_en0 ;
assign	wr_en_r0c1 = wr_en[0] & wr_en1 ;
assign	mux1_h_sel_r0[0]  = ~addr1to0_c1[1] & ~addr1to0_c1[0] ;
assign	mux1_h_sel_r0[1]  = ~addr1to0_c1[1] & addr1to0_c1[0] ;
assign	mux1_h_sel_r0[2]  = addr1to0_c1[1] & ~addr1to0_c1[0] ;
assign	mux1_h_sel_r0[3]  = addr1to0_c1[1] & addr1to0_c1[0] ;
assign	mux1_l_sel_r0 = mux1_h_sel_r0 ;
assign	mux2_sel_r0 = addr7_c1;
assign	rd_en_r0  = ~addr7_px2 & array_rd_en;



// XY = 75 X 50
assign	rd_addr1_r1 = rd_addr1[6:2];
assign	rd_addr2_r1 = rd_addr2[6:2];
assign	rd_addr_sel_r1 = rd_addr_sel ;
assign	wr_addr_r1 = wr_addr_entry ;
assign	word_en_r1 = wr_word_en ;
assign	wr_en_r1c0 = wr_en[1] & wr_en0 ;
assign	wr_en_r1c1 = wr_en[1] & wr_en1 ;
assign	rd_en_r1  = addr7_px2 & array_rd_en ;

// XY = 75 X 50
assign	rd_addr1_r2 = rd_addr1[6:2];
assign	rd_addr2_r2 = rd_addr2[6:2];
assign	rd_addr_sel_r2 = rd_addr_sel ;
assign	wr_addr_r2 = wr_addr_entry ;
assign	word_en_r2 = wr_word_en ;
assign	wr_en_r2c0 = wr_en[2] & wr_en0 ;
assign	wr_en_r2c1 = wr_en[2] & wr_en1 ;
assign	mux1_h_sel_r2[0]  = ~addr1to0_c1[1] & ~addr1to0_c1[0] ;
assign	mux1_h_sel_r2[1]  = ~addr1to0_c1[1] & addr1to0_c1[0] ;
assign	mux1_h_sel_r2[2]  = addr1to0_c1[1] & ~addr1to0_c1[0] ;
assign	mux1_h_sel_r2[3]  = addr1to0_c1[1] & addr1to0_c1[0] ;
assign	mux1_l_sel_r2 = mux1_h_sel_r2 ;
assign	mux2_sel_r2 = addr7_c1;
assign	rd_en_r2  = ~addr7_px2 & array_rd_en;

// XY = 75 X 50
assign	rd_addr1_r3 = rd_addr1[6:2];
assign	rd_addr2_r3 = rd_addr2[6:2];
assign	rd_addr_sel_r3 = rd_addr_sel ;
assign	wr_addr_r3 = wr_addr_entry ;
assign	word_en_r3 = wr_word_en ;
assign	wr_en_r3c0 = wr_en[3] & wr_en0 ;
assign	wr_en_r3c1 = wr_en[3] & wr_en1 ;
assign	rd_en_r3  = addr7_px2 & array_rd_en;


// Middle Io = 75 X 50

assign	mux_sel[0]  = ~addr9to8_c1[1] & ~addr9to8_c1[0] ;
assign	mux_sel[1]  = ~addr9to8_c1[1] & addr9to8_c1[0] ;
assign	mux_sel[2]  = addr9to8_c1[1] & ~addr9to8_c1[0] ;
assign	mux_sel[3]  = addr9to8_c1[1] & addr9to8_c1[0] ;




// XY = 75 X 50
assign	rd_addr1_r4 = rd_addr1[6:2];
assign	rd_addr2_r4 = rd_addr2[6:2];
assign	rd_addr_sel_r4 = rd_addr_sel ;
assign	wr_addr_r4 = wr_addr_entry ;
assign	word_en_r4 = wr_word_en ;
assign	wr_en_r4c0 = wr_en[4] & wr_en0 ;
assign	wr_en_r4c1 = wr_en[4] & wr_en1 ;
assign	mux1_h_sel_r4[0]  = ~addr1to0_c1[1] & ~addr1to0_c1[0] ;
assign	mux1_h_sel_r4[1]  = ~addr1to0_c1[1] & addr1to0_c1[0] ;
assign	mux1_h_sel_r4[2]  = addr1to0_c1[1] & ~addr1to0_c1[0] ;
assign	mux1_h_sel_r4[3]  = addr1to0_c1[1] & addr1to0_c1[0] ;
assign	mux1_l_sel_r4 = mux1_h_sel_r4 ;
assign	mux2_sel_r4 = addr7_c1;
assign	rd_en_r4  = ~addr7_px2 & array_rd_en;

// XY = 75 X 50
assign	rd_addr1_r5 = rd_addr1[6:2];
assign	rd_addr2_r5 = rd_addr2[6:2];
assign	rd_addr_sel_r5 = rd_addr_sel ;
assign	wr_addr_r5 = wr_addr_entry ;
assign	word_en_r5 = wr_word_en ;
assign	wr_en_r5c0 = wr_en[5] & wr_en0 ;
assign	wr_en_r5c1 = wr_en[5] & wr_en1 ;
assign	rd_en_r5  = addr7_px2 & array_rd_en;

// XY = 75 X 50
assign	rd_addr1_r6 = rd_addr1[6:2];
assign	rd_addr2_r6 = rd_addr2[6:2];
assign	rd_addr_sel_r6 = rd_addr_sel ;
assign	wr_addr_r6 = wr_addr_entry ;
assign	word_en_r6 = wr_word_en ;
assign	wr_en_r6c0 = wr_en[6] & wr_en0 ;
assign	wr_en_r6c1 = wr_en[6] & wr_en1 ;
assign	mux1_h_sel_r6[0]  = ~addr1to0_c1[1] & ~addr1to0_c1[0] ;
assign	mux1_h_sel_r6[1]  = ~addr1to0_c1[1] & addr1to0_c1[0] ;
assign	mux1_h_sel_r6[2]  = addr1to0_c1[1] & ~addr1to0_c1[0] ;
assign	mux1_h_sel_r6[3]  = addr1to0_c1[1] & addr1to0_c1[0] ;
assign	mux1_l_sel_r6 = mux1_h_sel_r6 ;
assign	mux2_sel_r6 = addr7_c1;
assign	rd_en_r6  = ~addr7_px2 & array_rd_en;

// XY = 75 X 50
assign	rd_addr1_r7 = rd_addr1[6:2];
assign	rd_addr2_r7 = rd_addr2[6:2];
assign	rd_addr_sel_r7 = rd_addr_sel ;
assign	wr_addr_r7 = wr_addr_entry ;
assign	word_en_r7 = wr_word_en ;
assign	wr_en_r7c0 = wr_en[7] & wr_en0 ;
assign	wr_en_r7c1 = wr_en[7] & wr_en1 ;
assign	rd_en_r7  = addr7_px2 & array_rd_en ;




endmodule
