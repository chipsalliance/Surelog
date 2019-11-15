// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_tagdp.v
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

//%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
// Description:
//		Final 4-1 mux for evicted address.
//		lkup tag and wr data tag logic.
//		diagnostic read pipe
//		CTL logic for generating the

// Changes:
//	- lkup_tag_c1[`TAG_WIDTH-1:6] replaces wrdata_tag_c1;
//	- removed all bist related signals, since the bist mux has been moved inside
//	 the tag.
//%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



`include 	"iop.h"
`include 	"sctag.h"

module sctag_tagdp( /*AUTOARG*/
   // Outputs
   tagdp_evict_tag_c4, tagdp_diag_data_c7, tagdp_lkup_addr_c4, 
   lkup_row_addr_dcd_c3, lkup_row_addr_icd_c3, tagdp_lkup_addr11_c4, 
   mbdata_inst_tecc_c8, so, lkup_tag_c1, arbdp_tag_idx_px2_buf, 
   mbist_l2t_index_buf, arbctl_tag_way_px2_buf, 
   mbist_l2t_dec_way_buf, arbctl_tag_rd_px2_buf, mbist_l2t_read_buf, 
   arbctl_tag_wr_px2_buf, mbist_l2t_write_buf, tag_wrdata_px2_buf, 
   mbist_write_data_buf, 
   // Inputs
   dir_cam_addr_c3, arbaddr_idx_c3, arbdp_tagdata_px2, tag_triad0_c3, 
   tag_triad1_c3, tag_triad2_c3, tag_triad3_c3, tag_quad_muxsel_c3, 
   arbdp_tag_idx_px2, mbist_l2t_index, arbctl_tag_way_px2, 
   mbist_l2t_dec_way, arbctl_tag_rd_px2, mbist_l2t_read, 
   arbctl_tag_wr_px2, mbist_l2t_write, tag_wrdata_px2, 
   mbist_write_data, arbctl_evict_c3, rclk, si, se, sehold
   );

input	[39:8] dir_cam_addr_c3; // from arbaddr
input	[9:0] 	arbaddr_idx_c3; // from arbaddr
input	[`TAG_WIDTH-1:6] arbdp_tagdata_px2 ; // write data for tag.

input  [`TAG_WIDTH-1:0] tag_triad0_c3;
input  [`TAG_WIDTH-1:0] tag_triad1_c3;
input  [`TAG_WIDTH-1:0] tag_triad2_c3;
input  [`TAG_WIDTH-1:0] tag_triad3_c3;

input	 [3:0]   tag_quad_muxsel_c3 ; // to tagdp

output	[`TAG_WIDTH-1:0] tagdp_evict_tag_c4; // to wbdata. 
output	[`TAG_WIDTH-1:0] tagdp_diag_data_c7; // to oqdp

output	[39:10]	tagdp_lkup_addr_c4;	// to the directory
output	[2:0]	lkup_row_addr_dcd_c3, lkup_row_addr_icd_c3;
output		tagdp_lkup_addr11_c4; // to dirrep. // NEW_PIN POST_4.2


output	[5:0]	mbdata_inst_tecc_c8; // to miss buffer data.
output		so;

// lkup_tag_c1[`TAG_WIDTH-1:6] replaces wrdata_tag_c1;

output	[`TAG_WIDTH-1:1] lkup_tag_c1; // to tag.

input	[9:0]	arbdp_tag_idx_px2;
input	[9:0]	mbist_l2t_index;

input	[11:0]	arbctl_tag_way_px2;
input	[11:0]	mbist_l2t_dec_way;

input		arbctl_tag_rd_px2;
input		mbist_l2t_read;

input		arbctl_tag_wr_px2;
input		mbist_l2t_write;

input	[27:0]	tag_wrdata_px2;
input	[7:0]	mbist_write_data;

output   [9:0]   arbdp_tag_idx_px2_buf;
output   [9:0]   mbist_l2t_index_buf;

output   [11:0]  arbctl_tag_way_px2_buf;
output   [11:0]  mbist_l2t_dec_way_buf;        

output           arbctl_tag_rd_px2_buf;
output           mbist_l2t_read_buf;

output           arbctl_tag_wr_px2_buf;
output           mbist_l2t_write_buf;

output   [27:0]  tag_wrdata_px2_buf;
output   [7:0]   mbist_write_data_buf;
input	        arbctl_evict_c3;
input		rclk;
input		si,se;
input		sehold; // POST_4.1


wire	[29:6]	tmp_lkup_tag_c1 ;
wire	[5:0]		parity_c1;

wire	[5:0]	tag_acc_ecc_c1, tag_acc_ecc_c2, tag_acc_ecc_c3;
wire	[5:0]	tag_acc_ecc_c4, tag_acc_ecc_c5, tag_acc_ecc_c6;
wire	[5:0]	tag_acc_ecc_c7;

wire	[`TAG_WIDTH-1:0] tagdp_evict_tag_c3, tagdp_diag_data_c6; // to oqdp
wire	[39:8]  evict_addr_c3;
wire	[39:8]	lkup_addr_c3;
wire	[39:10] tagdp_lkup_addr_c3;
wire	[`TAG_WIDTH-1:6] wrdata_tag_c1;






// New functionality POST_4.1
// sehold will make ff_wrdata_tag_c1 non-transparent.

wire	clk_1;

clken_buf  clk_buf  (.clk(clk_1), .rclk(rclk), .enb_l(sehold), .tmb_l(~se));


// reduced the width of this flop.
dff_s     #(`TAG_WIDTH-6)  ff_wrdata_tag_c1  	
		(.din(arbdp_tagdata_px2[`TAG_WIDTH-1:6]), .clk(clk_1),
               .q(wrdata_tag_c1[`TAG_WIDTH-1:6]), .se(se), .si(), .so());

zzecc_sctag_24b_gen     tagecc0 (.din({2'b0,wrdata_tag_c1[`TAG_WIDTH-1:6]}),
                 .dout(tmp_lkup_tag_c1[29:6]),
                 .parity(parity_c1[5:0]));

assign  tag_acc_ecc_c1 = { parity_c1[4:0], parity_c1[5] } ;


/////////////////////////////////////////////////////////
// To prevent the tag_acc_ecc_c1 bits from being
// part of the critical path in the tag compare operation,
// the overall parity bit P is not compared 
//
// The check bits in tag_acc_ecc_c1 take 4 levels of XOR
// to compute whereas the overall parity P takes 5 levels.
//
// Not comparing P means that a hit could be signalled
// inspite of an error in the P bit. This requires the
// parity computation in C2 to account for this case
// and not cause any Miss Buffer insertions.
/////////////////////////////////////////////////////////

assign  lkup_tag_c1[`TAG_WIDTH-1:6] =   wrdata_tag_c1[`TAG_WIDTH-1:6] ;
assign  lkup_tag_c1[5:1] =   tag_acc_ecc_c1[5:1]  ; 


/////////////////////////////////////////////
// Directory lkup address
/////////////////////////////////////////////

assign	evict_addr_c3[39:8] = { tagdp_evict_tag_c3[`TAG_WIDTH-1:6], 
				arbaddr_idx_c3[9:0] } ;

mux2ds #(32) mux_cam_addr_c3 ( .dout (lkup_addr_c3[39:8]),
              .in0(dir_cam_addr_c3[39:8]), .in1(evict_addr_c3[39:8]),
              .sel0(~arbctl_evict_c3), .sel1(arbctl_evict_c3));

assign  tagdp_lkup_addr_c3[39:10] = lkup_addr_c3[39:10] ;


dff_s  #(30)  ff_tagdp_lkup_addr_c4  (.din(tagdp_lkup_addr_c3[39:10]), .clk(rclk),
              .q(tagdp_lkup_addr_c4[39:10]), .se(se), .si(), .so());


/////////////////////////////////////////////
// LRU mux.
/////////////////////////////////////////////

mux4ds	#(`TAG_WIDTH)	mux_lru_tag (.dout (tagdp_evict_tag_c3[`TAG_WIDTH-1:0]),
                             .in0(tag_triad0_c3[`TAG_WIDTH-1:0]),
                             .in1(tag_triad1_c3[`TAG_WIDTH-1:0]),
                             .in2(tag_triad2_c3[`TAG_WIDTH-1:0]),
                             .in3(tag_triad3_c3[`TAG_WIDTH-1:0]),
                             .sel0(tag_quad_muxsel_c3[0]),
                             .sel1(tag_quad_muxsel_c3[1]),
                             .sel2(tag_quad_muxsel_c3[2]),
                             .sel3(tag_quad_muxsel_c3[3]));

//////////////////////////////////////////////////////////////////////////////////////////////
// Tag Diagnostic data pipeline
//------------------------------------------------------------------------------------------
//	C1	C2	C3	C4	C5	C6	C7	C8	C9
//------------------------------------------------------------------------------------------
//	diag	px2	rd tag	prepare mux	flop 	flop  	mux	data ret.
// 	decode  idx mux		way mux out tag			with
//				sels	and flop		other
//								diag data
//------------------------------------------------------------------------------------------
//////////////////////////////////////////////////////////////////////////////////////////////

dff_s  #(`TAG_WIDTH)  ff_tagdp_evict_tag_c4  (.din(tagdp_evict_tag_c3[`TAG_WIDTH-1:0]), .clk(rclk),
                   .q(tagdp_evict_tag_c4[`TAG_WIDTH-1:0]), .se(se), .si(), .so());

dff_s  #(`TAG_WIDTH)  ff_tagdp_diag_data_c6  (.din(tagdp_evict_tag_c4[`TAG_WIDTH-1:0]), .clk(rclk),
                   .q(tagdp_diag_data_c6[`TAG_WIDTH-1:0]), .se(se), .si(), .so());

dff_s  #(`TAG_WIDTH)  ff_tagdp_diag_data_c7  (.din(tagdp_diag_data_c6[`TAG_WIDTH-1:0]), .clk(rclk),
                   .q(tagdp_diag_data_c7[`TAG_WIDTH-1:0]), .se(se), .si(), .so());


/////////////////////////////////////////////
// DP is 32 bits wide. The following
// logic and flops are pushed to one side.
/////////////////////////////////////////////

dff_s     #(6)    ff_ecc_c2     (.din(tag_acc_ecc_c1[5:0]), .clk(rclk),
             .q(tag_acc_ecc_c2[5:0]), .se(se), .si(), .so());

dff_s     #(6)    ff_ecc_c3     (.din(tag_acc_ecc_c2[5:0]), .clk(rclk),
             .q(tag_acc_ecc_c3[5:0]), .se(se), .si(), .so());

dff_s     #(6)    ff_ecc_c4     (.din(tag_acc_ecc_c3[5:0]), .clk(rclk),
             .q(tag_acc_ecc_c4[5:0]), .se(se), .si(), .so());

dff_s     #(6)    ff_ecc_c5     (.din(tag_acc_ecc_c4[5:0]), .clk(rclk),
             .q(tag_acc_ecc_c5[5:0]), .se(se), .si(), .so());

dff_s     #(6)    ff_ecc_c6     (.din(tag_acc_ecc_c5[5:0]), .clk(rclk),
             .q(tag_acc_ecc_c6[5:0]), .se(se), .si(), .so());

dff_s     #(6)    ff_ecc_c7     (.din(tag_acc_ecc_c6[5:0]), .clk(rclk),
             .q(tag_acc_ecc_c7[5:0]), .se(se), .si(), .so());

dff_s     #(6)    ff_ecc_c8     (.din(tag_acc_ecc_c7[5:0]), .clk(rclk),
             .q(mbdata_inst_tecc_c8[5:0]), .se(se), .si(), .so());


assign	lkup_row_addr_dcd_c3[2:0] = lkup_addr_c3[10:8];
assign	lkup_row_addr_icd_c3[2:0] = lkup_addr_c3[10:8];

dff_s  #(1)  ff_addr11_c4  (.din(lkup_addr_c3[11]), .clk(rclk),
		  .q(tagdp_lkup_addr11_c4), .se(se), .si(), .so());


////////////////////////////////////////////////////////////
// The following signals need to be bufferred before
// the tag.
// INput pins are arranged on the top.
// Try to align with the data path cell placement information
// provided below.
////////////////////////////////////////////////////////////

// repeater row1 ( 24 bits wide ) arranged as follows from left to right.
// index [0 ..... 9]
// way [11 .... 0 ]
// rd 
// wr 

assign	 arbdp_tag_idx_px2_buf[9:0]	= arbdp_tag_idx_px2[9:0] ;
assign	arbctl_tag_way_px2_buf[11:0]	= arbctl_tag_way_px2[11:0] ;

assign	arbctl_tag_rd_px2_buf	= 	arbctl_tag_rd_px2;
assign	arbctl_tag_wr_px2_buf	= 	arbctl_tag_wr_px2;

// repeater row2 ( 24 bits wide ) arranged as follows from left to right.
// index [0 ..... 9]
// way [11 .... 0 ]
// rd 
// wr 
assign	 mbist_l2t_index_buf[9:0]	=  mbist_l2t_index[9:0] ;
assign	 mbist_l2t_dec_way_buf[11:0]    = mbist_l2t_dec_way[11:0] ;
assign	 mbist_l2t_read_buf		= mbist_l2t_read;
assign	mbist_l2t_write_buf		= mbist_l2t_write;

// repeater row 3 ( 28 bits wide ) arranged as follows from left to right.
// wr_data [0 .. 27]

assign	tag_wrdata_px2_buf = 	tag_wrdata_px2 ;

// repeater row 4  ( 8 bits wide ) arranged as follows from left to right.

assign	mbist_write_data_buf = mbist_write_data;


endmodule

