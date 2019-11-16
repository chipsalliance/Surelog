// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_snpctl.v
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
`include "sctag.h"



module sctag_snpctl (/*AUTOARG*/
   // Outputs
   sctag_jbi_por_req, so, sctag_jbi_iq_dequeue, snpq_arbctl_vld_px1, 
   snp_hdr1_wen0_s0, snp_hdr2_wen0_s1, snp_data1_wen0_s2, 
   snp_data2_wen0_s3, snp_hdr1_wen1_s0, snp_hdr2_wen1_s1, 
   snp_data1_wen1_s2, snp_data2_wen1_s3, snpctl_wr_ptr, 
   snpctl_rd_ptr, rdmad_wr_entry_s2, rdmatag_wr_en_s2, 
   sctag_scbuf_rdma_wren_s2, sctag_scbuf_rdma_wrwl_s2, 
   // Inputs
   jbi_req_vld_buf, arbctl_snpsel_c1, snpdp_rq_winv_s1, 
   rdmat_wr_entry_s1, sctag_por_req, rclk, si, se, arst_l, grst_l
   );

input	jbi_req_vld_buf; // primary input.
input	arbctl_snpsel_c1; // This signal is used to advance the rd ptr.
input	snpdp_rq_winv_s1; // from snoop sp. Request type bit indicating winv.
input	[1:0]	rdmat_wr_entry_s1; // encoded from rdma tag ctl.
input	sctag_por_req; // POST_4.2 pin in the BOTTOM


input	rclk;
input	si,se;
input	arst_l;
input	grst_l;

output	sctag_jbi_por_req ; // POST_4.2 pin on TOP. USe a 30x Buffer
output	so;
// to jbi
output	sctag_jbi_iq_dequeue ;
// to arbctl.
output 	snpq_arbctl_vld_px1;
// to snpdp.
output	snp_hdr1_wen0_s0, snp_hdr2_wen0_s1, snp_data1_wen0_s2, snp_data2_wen0_s3 ;
output	snp_hdr1_wen1_s0, snp_hdr2_wen1_s1, snp_data1_wen1_s2, snp_data2_wen1_s3 ;
output	snpctl_wr_ptr;
output	snpctl_rd_ptr;
output	[1:0]	rdmad_wr_entry_s2;
// to rdmatag.
output	rdmatag_wr_en_s2;
// to scbuf
output	[15:0]	sctag_scbuf_rdma_wren_s2;
output	[1:0]	sctag_scbuf_rdma_wrwl_s2;

wire	jbi_req_vld_s0;
wire	wr_ptr_in, wr_ptr;
wire	rd_ptr_in, rd_ptr ;

wire	winv_reset, winv_en ;
wire	winv_rq_active_s2, winv_rq_active_s2_1;
wire	sel_snpiq_cnt_reset, snpiq_cnt_en, sel_snpiq_cnt_plus0, snpiq_cnt_rst ;
wire	[4:0]	snpiq_cnt_plus0, snpiq_cnt_in, snpiq_cnt ;
wire	[1:0]	snpq_valid_in, snpq_valid ;
wire	[15:0]	rdmadata_wen_s1, rdmadata_wen_s2 ;
wire	[1:0]	rdmad_wr_entry_s2_d1, rdmad_wr_wl_s2;

wire            dbb_rst_l;

assign	sctag_jbi_por_req = sctag_por_req ;

///////////////////////////////////////////////////////////////////
 // Reset flop
 ///////////////////////////////////////////////////////////////////

 dffrl_async    #(1)    reset_flop      (.q(dbb_rst_l),
                                        .clk(rclk),
                                        .rst_l(arst_l),
                                        .din(grst_l),
                                        .se(se), .si(), .so());







////////////////////////////////////////////////////////////////////////////////////////////////////////////
// requests from JBI to issue pipeline.
// WR8s and Reads are separated by 5 cycles.
// Wr64 is a 19 cycle instruction so no new 
// request can be issued within 19 cycles or a WR64
////////////////////////////////////////////////////////////////////////////////////////////////////////////
//	INstA		S0		S1		S2		S3		S4		S5
////////////////////////////////////////////////////////////////////////////////////////////////////////////
//-----------------------------------------------------------------------------------------------------------
//	req_vld		hdr1		hdr2		data1		data2		
//	A											
//											
//-----------------------------------------------------------------------------------------------------------
//											
//					cnt=1		2		3		
//											set vld=1	
//											
//-----------------------------------------------------------------------------------------------------------
//							winv_rq_active_s2
//							set if
//							hdr1 indicates
//							WR64				
//
//-----------------------------------------------------------------------------------------------------------
//							wrptr_p =
//							~wrptr.				non WR64 PX1	PX2
//
//-----------------------------------------------------------------------------------------------------------
//											
//			writehdr1	writehdr2	writedata1	writedata2
//					
//-----------------------------------------------------------------------------------------------------------
//					
//					send entry to	mux		write rdmat	
//					snpqctl from	out		set rdmatctl vld
//					rdmatctl	addr from
//							written
//							entry
//
//-----------------------------------------------------------------------------------------------------------
//							xmit wr_wen
//							& wl for
//							rdmad write
//											INST B
//-----------------------------------------------------------------------------------------------------------
//
//	In this block of code, the enables for writing into the hdr addr and data flops are 
//	generated. Since the snp IQ is 2 deep, there are a total of 8 mux selects that 
//	are generated here.
//	The mux selects are a cross product of the IQ entry and IQ field that is written.
//
//
// - winv_rq_active_s2 is maintained high from the S2 of a WR64 instruction 
// till the S2 of a following instruction that is not a WR64.
// - counter is reset when count is 3 or count is 17. The resetting of the counter
//   indicates that the Wr pointer needs to be toggled.Also, one cycle after the
//   counter expires,  vld_px1 is turned on to the arbiter.
//
// - The wenables for writing into the rdma Wr Buffer data assume that the 64Bytes of
//   data arrive in the order 0,4,...60
// - valid bit for an entry in the snp IQ is set when the request counter is reset.
// - rd pointer is toggled when an instruction is issued down the pipe.
// - entry in the rdma Wr Buffer to write into is determined in S1 based on the 
//   valid bits in rdmat.
// 
// 
////////////////////////////////////////////////////////////////////////////////////////////////////////////


dff_s     #(1)    ff_jbi_req_vld_s0     (.din(jbi_req_vld_buf), .clk(rclk),
                 .q(jbi_req_vld_s0), .se(se), .si(), .so());

assign 	winv_reset = ~dbb_rst_l ;
assign 	winv_en = ( snpiq_cnt == 5'd1);

dffre_s   #(1)  ff_winv_rq_active_s2  (.din(snpdp_rq_winv_s1),
                 .en(winv_en), .clk(rclk), .rst(winv_reset),
                 .q(winv_rq_active_s2), .se(se), .si(), .so());

assign	sel_snpiq_cnt_reset = (( snpiq_cnt == 5'd17) & winv_rq_active_s2)  |
			(( snpiq_cnt == 5'd3) &  ~winv_rq_active_s2 ) ;

assign	sel_snpiq_cnt_plus0 = ( |(snpiq_cnt)   | jbi_req_vld_s0 ) ;
assign	snpiq_cnt_plus0 = snpiq_cnt + 5'd1;
assign	snpiq_cnt_en = sel_snpiq_cnt_plus0 | sel_snpiq_cnt_reset ;
assign	snpiq_cnt_rst = ~dbb_rst_l ;

mux2ds #(5)  mux_snpiq_cnt (.dout (snpiq_cnt_in[4:0]),
               	.in0  (snpiq_cnt_plus0[4:0]),     .in1  (5'b0),  
		.sel0 (~sel_snpiq_cnt_reset), .sel1 (sel_snpiq_cnt_reset)) ;

dffre_s   #(5)  ff_snpiq_cnt  (.din(snpiq_cnt_in[4:0]),
               	.en(snpiq_cnt_en), .clk(rclk), .rst(snpiq_cnt_rst),
               	.q(snpiq_cnt[4:0]), .se(se), .si(), .so());



///////////////////////////////////////////////////////////////////
// Instruction WR pointer logic. 
// Wr pointer is initialized at 1 and toggles between
// 0 and 1 everytime a req is written into the 
// snp IQ. A request is considered to be written when the
// request counter is reset to 0.
///////////////////////////////////////////////////////////////////

assign	wr_ptr_in = (( ~wr_ptr & sel_snpiq_cnt_reset ) | wr_ptr ) & // set condition
		~( wr_ptr & sel_snpiq_cnt_reset ) ; // reset condition.
		    

dffrl_s #(1)  ff_wr_ptr (.q(wr_ptr), .din (wr_ptr_in),
              .clk (rclk),  .rst_l(dbb_rst_l), .se(se), .si  (), .so  ()
             ) ;

assign	snpctl_wr_ptr = wr_ptr ;



///////////////////////////
// Wenable generation into 
// the snpIQ
///////////////////////////

assign	snp_hdr1_wen0_s0 = ~wr_ptr & (snpiq_cnt==5'd0)  & jbi_req_vld_s0 ;
assign	snp_hdr2_wen0_s1 = ~wr_ptr & (snpiq_cnt==5'd1) ;
assign	snp_data1_wen0_s2 = ~wr_ptr & (snpiq_cnt==5'd2) ;
assign	snp_data2_wen0_s3 = ~wr_ptr & (snpiq_cnt==5'd3) ;

assign	snp_hdr1_wen1_s0 = wr_ptr & (snpiq_cnt==5'd0)  & jbi_req_vld_s0;
assign	snp_hdr2_wen1_s1 = wr_ptr & (snpiq_cnt==5'd1) ;
assign	snp_data1_wen1_s2 = wr_ptr & (snpiq_cnt==5'd2) ;
assign	snp_data2_wen1_s3 = wr_ptr & (snpiq_cnt==5'd3) ;

  
///////////////////////////
// Wenable generation into 
// rdmatag cam2
///////////////////////////

assign	rdmatag_wr_en_s2 = winv_rq_active_s2 & ( snpiq_cnt==5'd2 ) ;

///////////////////////////
// Wenable generation into 
// rdmadata 
// This signal is calculated
// in S1 and then staged.
// data write happens starting in s4 all the way upto
//
///////////////////////////

assign	rdmadata_wen_s1[0] = ( snpiq_cnt==5'd1) ;
assign	rdmadata_wen_s1[1] = ( snpiq_cnt==5'd2) ;
assign	rdmadata_wen_s1[2] = ( snpiq_cnt==5'd3) ;
assign	rdmadata_wen_s1[3] = ( snpiq_cnt==5'd4) ;
assign	rdmadata_wen_s1[4] = ( snpiq_cnt==5'd5) ;
assign	rdmadata_wen_s1[5] = ( snpiq_cnt==5'd6) ;
assign	rdmadata_wen_s1[6] = ( snpiq_cnt==5'd7) ;
assign	rdmadata_wen_s1[7] = ( snpiq_cnt==5'd8) ;
assign	rdmadata_wen_s1[8] = ( snpiq_cnt==5'd9) ;
assign	rdmadata_wen_s1[9] = ( snpiq_cnt==5'd10) ;
assign	rdmadata_wen_s1[10] = ( snpiq_cnt==5'd11) ;
assign	rdmadata_wen_s1[11] = ( snpiq_cnt==5'd12) ;
assign	rdmadata_wen_s1[12] = ( snpiq_cnt==5'd13) ;
assign	rdmadata_wen_s1[13] = ( snpiq_cnt==5'd14) ;
assign	rdmadata_wen_s1[14] = ( snpiq_cnt==5'd15) ;
assign	rdmadata_wen_s1[15] = ( snpiq_cnt==5'd16) ;


dff_s     #(16)    ff_rdmadata_wen_s2     (.din(rdmadata_wen_s1[15:0]), .clk(rclk),
                 .q(rdmadata_wen_s2[15:0]), .se(se), .si(), .so());

dffre_s   #(1)  ff_winv_rq_active_s2_1  (.din(snpdp_rq_winv_s1),
                 .en(winv_en), .clk(rclk), .rst(winv_reset),
                 .q(winv_rq_active_s2_1), .se(se), .si(), .so());

assign	sctag_scbuf_rdma_wren_s2 = rdmadata_wen_s2 & 
					{16{winv_rq_active_s2_1}} ;

///////////////////////////
// Write Wline generation
///////////////////////////



dff_s     #(2)    ff_rdmad_wr_entry_s2     (.din(rdmat_wr_entry_s1[1:0]), .clk(rclk),
                 .q(rdmad_wr_entry_s2[1:0]), .se(se), .si(), .so());

mux2ds  #(2)    mux_rdmad_wr_entry_s2 (.dout (rdmad_wr_wl_s2[1:0]) ,
                        .in0(rdmad_wr_entry_s2[1:0]),  // new entry
                        .in1(rdmad_wr_entry_s2_d1[1:0]), // old entry
                        .sel0(rdmatag_wr_en_s2),  //  wr64 in s2
                        .sel1(~rdmatag_wr_en_s2)) ; // ~wr64 in S2

assign	sctag_scbuf_rdma_wrwl_s2 = rdmad_wr_wl_s2;

dffrl_s     #(2)    ff_rdmad_wr_entry_s2_d1     (.din(rdmad_wr_wl_s2[1:0]), .clk(rclk),
		 .rst_l(dbb_rst_l),
                 .q(rdmad_wr_entry_s2_d1[1:0]), .se(se), .si(), .so());

///////////////////////////
// Valid bit generation in the
// SNPIQ
// set when an instruction in written
// into the snp IQ.i.e. in the S3 or S17 cycles.
// reset when an instruction is issued
// down the pipe.
///////////////////////////

// Removed '[0]' at the end of sel_snpiq_cnt_reset for synthesis
// - connie 1/16/2003

assign	snpq_valid_in[0]  = ( snpq_valid[0] | ( ~wr_ptr & sel_snpiq_cnt_reset ) ) &
				~( ~rd_ptr & arbctl_snpsel_c1 ) ;
	
assign	snpq_valid_in[1]  = ( snpq_valid[1] | ( wr_ptr & sel_snpiq_cnt_reset ) ) &
				~( rd_ptr & arbctl_snpsel_c1 ) ;

dffrl_s #(2)  ff_snp_valid (.q(snpq_valid[1:0]), .din (snpq_valid_in[1:0]),
              .clk (rclk),  .rst_l(dbb_rst_l), .se(se), .si  (), .so  ()) ;

assign	snpq_arbctl_vld_px1 = |( snpq_valid ) ;

// assign	snpq_arbctl_vld_px1 = 0;


/////////////////////////////////////////////////////////////////////
// Instruction RD pointer logic.
// Read pointer is used for select the requests in FIFO order
// Rd pointer is initialized at 1 and toggles between
// 0 and 1 everytime a req is issued down the pipe from the snpIQ
/////////////////////////////////////////////////////////////////////

assign  rd_ptr_in = (( ~rd_ptr & arbctl_snpsel_c1 ) | rd_ptr ) & // set condition
                        ~( rd_ptr & arbctl_snpsel_c1 ) ; // reset condition.
                    

dffrl_s #(1)  ff_rd_ptr (.q(rd_ptr), .din (rd_ptr_in),
              .clk (rclk),  .rst_l(dbb_rst_l), .se(se), .si  (), .so  ()) ;


assign	snpctl_rd_ptr = rd_ptr;

assign	sctag_jbi_iq_dequeue = arbctl_snpsel_c1 ;



endmodule

