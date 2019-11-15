// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_snpdp.v
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
// Change: 6/12/2003
// Read the change description around line 242.
`include	"sctag.h"


module sctag_snpdp (/*AUTOARG*/
   // Outputs
   so, snpq_arbdp_addr_px2, snpq_arbdp_inst_px2, snpq_arbdp_data_px2, 
   snpdp_rq_winv_s1, rdmatag_wr_addr_s2, 
   // Inputs
   rclk, si, se, jbi_req_buf, snp_hdr1_wen0_s0, snp_hdr2_wen0_s1, 
   snp_data1_wen0_s2, snp_data2_wen0_s3, snp_hdr1_wen1_s0, 
   snp_hdr2_wen1_s1, snp_data1_wen1_s2, snp_data2_wen1_s3, 
   snpctl_wr_ptr, snpctl_rd_ptr, rdmad_wr_entry_s2
   );

output	so;

// to the arbiter
output [39:0]			snpq_arbdp_addr_px2;
output [`JBI_HDR_SZ-1:0]	snpq_arbdp_inst_px2; // this bus has grown by 1 bit since 2.0
output [63:0]			snpq_arbdp_data_px2;

// to snpctl
output		snpdp_rq_winv_s1; // to snp ctl;

// to rdmatag
output	[39:6]	rdmatag_wr_addr_s2 ;

input	rclk, si, se;

// from jbi
input	[31:0]	jbi_req_buf;

 // from snpctl
input   snp_hdr1_wen0_s0, snp_hdr2_wen0_s1, snp_data1_wen0_s2, snp_data2_wen0_s3 ;
input   snp_hdr1_wen1_s0, snp_hdr2_wen1_s1, snp_data1_wen1_s2, snp_data2_wen1_s3 ;
input	snpctl_wr_ptr;
input	snpctl_rd_ptr;
input	[1:0]	rdmad_wr_entry_s2;

wire	[`JBI_HDR_SZ-1:0]	instr0; 
wire	[`JBI_HDR_SZ-1:0]	instr1; 
wire	[39:0]	addr0; 
wire	[39:0]	addr1; 
wire	[63:0]	data0;
wire	[63:0]	data1;

wire	snpctl_rd_ptr_d1, snpctl_rd_ptr_d1_1, snpctl_rd_ptr_d1_2, snpctl_rd_ptr_d1_3 ;

wire	snpctl_rd_ptr_d1_4;

//  data path is 92 bits wide.
//  address = 40 bits
//  header  = 20 bits
//  data    = 64 bits/2 

// In cycle 1 write 19 bits of header and 8 bits of address.
// Header = wr64 wr8 rd CTAG<11:0> RSVD SZ<2:0> 
// cycle s1

// dffe   #(`JBI_HDR_SZ-3) ff_instr0    (.din(jbi_req_buf[`JBI_RQ_WR64:`JBI_SZ_LO]), .clk(rclk),
// 			   .en(snp_hdr1_wen0_s0), .q(instr0[`JBI_HDR_SZ-4:0]), 
// 			   .se(se), .si(), .so());
clken_buf  ckbuf_1  (.clk(clk_1), .rclk(rclk), .enb_l(~snp_hdr1_wen0_s0), .tmb_l(~se));
dff_s   #(`JBI_HDR_SZ-3) ff_instr0    (.din(jbi_req_buf[`JBI_RQ_WR64:`JBI_SZ_LO]), .clk(clk_1),
                	.q(instr0[`JBI_HDR_SZ-4:0]), 
			.se(se), .si(), .so());

// dffe   #(2)		ff_instr0_entry ( .din(rdmad_wr_entry_s2[1:0]), .clk(rclk),
// 			   .en(snp_data1_wen0_s2), .q(instr0[`JBI_HDR_SZ-2:`JBI_HDR_SZ-3]),
// 			   .se(se), .si(), .so());
clken_buf  ckbuf_2  (.clk(clk_2), .rclk(rclk), .enb_l(~snp_data1_wen0_s2), .tmb_l(~se));
dff_s   #(2)		ff_instr0_entry ( .din(rdmad_wr_entry_s2[1:0]), .clk(clk_2),
			.q(instr0[`JBI_HDR_SZ-2:`JBI_HDR_SZ-3]),
                        .se(se), .si(), .so());


// dffe   #(1)		ff_instr0_poison ( .din(jbi_req_buf[`JBI_RQ_POISON]), .clk(rclk),
// 			   .en(snp_hdr1_wen0_s0), .q(instr0[`JBI_HDR_SZ-1]),
// 			   .se(se), .si(), .so());
dff_s   #(1)		ff_instr0_poison ( .din(jbi_req_buf[`JBI_RQ_POISON]), .clk(clk_1),
			.q(instr0[`JBI_HDR_SZ-1]),
                        .se(se), .si(), .so());


// dffe   #(8)  ff_addr0_1    (.din(jbi_req_buf[`JBI_ADDR_HI:`JBI_ADDR_LO]), .clk(rclk),
// 			   .en(snp_hdr1_wen0_s0), .q(addr0[39:32]), 
// 			   .se(se), .si(), .so());
dff_s   #(8)  ff_addr0_1    (.din(jbi_req_buf[`JBI_ADDR_HI:`JBI_ADDR_LO]), .clk(clk_1),
                	.q(addr0[39:32]), 
			.se(se), .si(), .so());

// 32 bits of addr <31:0>
// cycle s2
// dffe   #(32) ff_addr0_2    (.din(jbi_req_buf[31:0]), .clk(rclk),
// 			   .en(snp_hdr2_wen0_s1), .q(addr0[31:0]), 
// 			   .se(se), .si(), .so());
clken_buf  ckbuf_4  (.clk(clk_4), .rclk(rclk), .enb_l(~snp_hdr2_wen0_s1), .tmb_l(~se));
dff_s   #(32) ff_addr0_2    (.din(jbi_req_buf[31:0]), .clk(clk_4),
                	.q(addr0[31:0]), 
			.se(se), .si(), .so());

// 32 bits of data <63:32>
// cycle s3
// dffe   #(32) ff_data0_1    (.din(jbi_req_buf[31:0]), .clk(rclk),
// 			   .en(snp_data1_wen0_s2), .q(data0[63:32]), 
// 			   .se(se), .si(), .so());
clken_buf  ckbuf_5  (.clk(clk_5), .rclk(rclk), .enb_l(~snp_data1_wen0_s2), .tmb_l(~se));
dff_s   #(32) ff_data0_1    (.din(jbi_req_buf[31:0]), .clk(clk_5),
                	.q(data0[63:32]), 
			.se(se), .si(), .so());


// 32 bits of data <31:0>
// cycle s4
// dffe   #(32) ff_data0_2    (.din(jbi_req_buf[31:0]), .clk(rclk),
// 			   .en(snp_data2_wen0_s3), .q(data0[31:0]), 
// 			   .se(se), .si(), .so());
clken_buf  ckbuf_6  (.clk(clk_6), .rclk(rclk), .enb_l(~snp_data2_wen0_s3), .tmb_l(~se));
dff_s   #(32) ff_data0_2    (.din(jbi_req_buf[31:0]), .clk(clk_6),
                	.q(data0[31:0]), 
			.se(se), .si(), .so());


// In cycle 1 write 19 bits of header and 8 bits of address.
// Header = wr64 wr8 rd CTAG<11:0> RSVD SZ<2:0> 
// cycle s1

// dffe   #(`JBI_HDR_SZ-3) ff_instr1    (.din(jbi_req_buf[`JBI_RQ_WR64:`JBI_SZ_LO]), .clk(rclk),
// 			   .en(snp_hdr1_wen1_s0), .q(instr1[`JBI_HDR_SZ-4:0]),
// 			   .se(se), .si(), .so());
clken_buf  ckbuf_7  (.clk(clk_7), .rclk(rclk), .enb_l(~snp_hdr1_wen1_s0), .tmb_l(~se));
dff_s   #(`JBI_HDR_SZ-3) ff_instr1    (.din(jbi_req_buf[`JBI_RQ_WR64:`JBI_SZ_LO]), .clk(clk_7),
                	.q(instr1[`JBI_HDR_SZ-4:0]),
			.se(se), .si(), .so());

// dffe   #(2)		ff_instr1_entry ( .din(rdmad_wr_entry_s2[1:0]), .clk(rclk),
// 			   .en(snp_data1_wen1_s2), .q(instr1[`JBI_HDR_SZ-2:`JBI_HDR_SZ-3]),
// 			   .se(se), .si(), .so());
clken_buf  ckbuf_8  (.clk(clk_8), .rclk(rclk), .enb_l(~snp_data1_wen1_s2), .tmb_l(~se));
dff_s   #(2)		ff_instr1_entry ( .din(rdmad_wr_entry_s2[1:0]), .clk(clk_8),
			.q(instr1[`JBI_HDR_SZ-2:`JBI_HDR_SZ-3]),
                        .se(se), .si(), .so());

// dffe   #(1)		ff_instr1_poison ( .din(jbi_req_buf[`JBI_RQ_POISON]), .clk(rclk),
// 			   .en(snp_hdr1_wen1_s0), .q(instr1[`JBI_HDR_SZ-1]),
// 			   .se(se), .si(), .so());
dff_s   #(1)		ff_instr1_poison ( .din(jbi_req_buf[`JBI_RQ_POISON]), .clk(clk_7),
			.q(instr1[`JBI_HDR_SZ-1]),
                        .se(se), .si(), .so());


// dffe   #(8)  ff_addr1_1    (.din(jbi_req_buf[`JBI_ADDR_HI:`JBI_ADDR_LO]), .clk(rclk),
// 			   .en(snp_hdr1_wen1_s0), .q(addr1[39:32]),
// 			   .se(se), .si(), .so());
dff_s   #(8)  ff_addr1_1    (.din(jbi_req_buf[`JBI_ADDR_HI:`JBI_ADDR_LO]), .clk(clk_7),
                	.q(addr1[39:32]),
			.se(se), .si(), .so());

// 32 bits of addr <31:0>
// cycle s2
// dffe   #(32) ff_addr1_2    (.din(jbi_req_buf[31:0]), .clk(rclk),
// 			   .en(snp_hdr2_wen1_s1), .q(addr1[31:0]),
// 			   .se(se), .si(), .so());
clken_buf  ckbuf_10  (.clk(clk_10), .rclk(rclk), .enb_l(~snp_hdr2_wen1_s1), .tmb_l(~se));
dff_s   #(32) ff_addr1_2    (.din(jbi_req_buf[31:0]), .clk(clk_10),
                        .q(addr1[31:0]),
 			.se(se), .si(), .so());

// 32 bits of data <63:32>
// cycle s3
// dffe   #(32) ff_data1_1    (.din(jbi_req_buf[31:0]), .clk(rclk),
// 			   .en(snp_data1_wen1_s2), .q(data1[63:32]),
// 			   .se(se), .si(), .so());
clken_buf  ckbuf_11  (.clk(clk_11), .rclk(rclk), .enb_l(~snp_data1_wen1_s2), .tmb_l(~se));
dff_s   #(32) ff_data1_1    (.din(jbi_req_buf[31:0]), .clk(clk_11),
                        .q(data1[63:32]),
                        .se(se), .si(), .so());

// 32 bits of data <31:0>
// cycle s4
// dffe   #(32) ff_data1_2    (.din(jbi_req_buf[31:0]), .clk(rclk),
// 			   .en(snp_data2_wen1_s3), .q(data1[31:0]),
// 			   .se(se), .si(), .so());
clken_buf  ckbuf_12  (.clk(clk_12), .rclk(rclk), .enb_l(~snp_data2_wen1_s3), .tmb_l(~se));
dff_s   #(32) ff_data1_2    (.din(jbi_req_buf[31:0]), .clk(clk_12),
                        .q(data1[31:0]),
                        .se(se), .si(), .so());




/////////////////////////////////////////////////
// A 34 bit mux is used to mux out the address
// of the request that is being sent from the jbi.
// Hence wr ptr is used for this mux.
// If this request happens to be a WR64, the 
// address is written into the rdma tags.
/////////////////////////////////////////////////


mux2ds  #(34) mux_rdmatag_wr_addr_s2 (.dout (rdmatag_wr_addr_s2[39:6]) ,
                	.in0(addr0[39:6]),  // entry0
			.in1(addr1[39:6]), // entry1
                	.sel0(~snpctl_wr_ptr),  // entry 0 is being written
			.sel1(snpctl_wr_ptr)) ; // entry 1 is being written


mux2ds  #(1) mux_snpdp_rq_winv_s1 (.dout (snpdp_rq_winv_s1) ,
                	.in0(instr0[`JBI_HDR_SZ-4]),  // entry0
                	.in1(instr1[`JBI_HDR_SZ-4]),  // entry0
                	.sel0(~snpctl_wr_ptr),  // entry 0 is being written
			.sel1(snpctl_wr_ptr)) ; // entry 1 is being written

	
/////////////////////////////////////////////////
// The snp q output is a mux between the 
// entry0 and entry1.
//
// rd pointer is updated when arbctl_snpsel_c1 
// 
/////////////////////////////////////////////////



dff_s     #(1)    ff_snpctl_rd_ptr_d1  (.din(snpctl_rd_ptr), .clk(rclk),
                 .q(snpctl_rd_ptr_d1), .se(se), .si(), .so());

mux2ds  #(`JBI_HDR_SZ) mux_instr_px2 (.dout (snpq_arbdp_inst_px2[`JBI_HDR_SZ-1:0]) ,
                	.in0(instr0[`JBI_HDR_SZ-1:0]),  // entry0
                	.in1(instr1[`JBI_HDR_SZ-1:0]),  // entry1
                	.sel0(~snpctl_rd_ptr_d1),  // entry 0 is being written
			.sel1(snpctl_rd_ptr_d1)) ; // entry 1 is being written

dff_s     #(1)    ff_snpctl_rd_ptr_d1_1  (.din(snpctl_rd_ptr), .clk(rclk),
                 .q(snpctl_rd_ptr_d1_1), .se(se), .si(), .so());

dff_s     #(1)    ff_snpctl_rd_ptr_d1_2  (.din(snpctl_rd_ptr), .clk(rclk),
                 .q(snpctl_rd_ptr_d1_2), .se(se), .si(), .so());

// Change 6/13/2003
// 1) use an 8x flop for snpctl_rd_ptr_d1_4, snpctl_rd_ptr_d1_5 
// The above signals can be used for the more critical address bits <17:8>
// transmit the selects close to the affected bits before flopping them so
// as to save time in PX2.
// 2) The 2-1 addr mux ( use a 2x mux) can be performed between ~addr0 and ~addr1.
//    The result can be driven using a 40x buffer 

dff_s     #(1)    ff_snpctl_rd_ptr_d1_4  (.din(snpctl_rd_ptr), .clk(rclk),
                 .q(snpctl_rd_ptr_d1_4), .se(se), .si(), .so());

dff_s     #(1)    ff_snpctl_rd_ptr_d1_5  (.din(snpctl_rd_ptr), .clk(rclk),
                 .q(snpctl_rd_ptr_d1_5), .se(se), .si(), .so());

mux2ds  #(22) mux_addr_px2_39_18 (.dout (snpq_arbdp_addr_px2[39:18]) ,
                	.in0(addr0[39:18]),  // entry0
                	.in1(addr1[39:18]),  // entry1
                	.sel0(~snpctl_rd_ptr_d1_1),  // entry 0 is being read
			.sel1(snpctl_rd_ptr_d1_1)) ; // entry 1 is being read

mux2ds  #(5) mux_addr_px2_17_13 (.dout (snpq_arbdp_addr_px2[17:13]) ,
                	.in0(addr0[17:13]),  // entry0
                	.in1(addr1[17:13]),  // entry1
                	.sel0(~snpctl_rd_ptr_d1_4),  // entry 0 is being read
			.sel1(snpctl_rd_ptr_d1_4)) ; // entry 1 is being read

mux2ds  #(5) mux_addr_px2_12_8 (.dout (snpq_arbdp_addr_px2[12:8]) ,
                	.in0(addr0[12:8]),  // entry0
                	.in1(addr1[12:8]),  // entry1
                	.sel0(~snpctl_rd_ptr_d1_5),  // entry 0 is being read
			.sel1(snpctl_rd_ptr_d1_5)) ; // entry 1 is being read

mux2ds  #(8) mux_addr_px2_7_0 (.dout (snpq_arbdp_addr_px2[7:0]) ,
                	.in0(addr0[7:0]),  // entry0
                	.in1(addr1[7:0]),  // entry1
                	.sel0(~snpctl_rd_ptr_d1_1),  // entry 0 is being read
			.sel1(snpctl_rd_ptr_d1_1)) ; // entry 1 is being read




mux2ds  #(32) mux_data_px2_0 (.dout (snpq_arbdp_data_px2[31:0]) ,
                	.in0(data0[31:0]),  // entry0
                	.in1(data1[31:0]),  // entry1
                	.sel0(~snpctl_rd_ptr_d1_2),  // entry 0 is being written
			.sel1(snpctl_rd_ptr_d1_2)) ; // entry 1 is being written

dff_s     #(1)    ff_snpctl_rd_ptr_d1_3  (.din(snpctl_rd_ptr), .clk(rclk),
                 .q(snpctl_rd_ptr_d1_3), .se(se), .si(), .so());

mux2ds  #(32) mux_data_px2_1 (.dout (snpq_arbdp_data_px2[63:32]) ,
                	.in0(data0[63:32]),  // entry0
                	.in1(data1[63:32]),  // entry1
                	.sel0(~snpctl_rd_ptr_d1_3),  // entry 0 is being written
			.sel1(snpctl_rd_ptr_d1_3)) ; // entry 1 is being written

endmodule

