// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_arbaddrdp.v
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
//%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
// Description: This file contains the following logic
//	* Tag repair for TECC instructions
//	* Flops for mb,wb and fb addresses.
//	* Arbiter logic. ( index, and non-index bits of address )
//	* Comparators for mb bypass.
//	* CAM/wr address for the directory.
//	* address for errors.
//	* Address to DRAM
// Change 4/7/2003 : -Change bist_vuad_idx to bist_vuad_idx_px1;
//     		     -Added a flop instance, bist_vuad_idx_px2
// 		     -Removed instances mux_vuad_idx_px2, ff_vuad_idx_c1
// 		      ff_vuad_idx_c2 and ff_vuad_idx_c3 ;
//		     - added idx compare c1toc5.
// Change 6/12/2003 : Change arbdp_word_addr_c7 output moved to C6 
//		      under the new name arbdp_byte_addr_c6
//%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%





////////////////////////////////////////////////////////////////////////
// Global header file includes
////////////////////////////////////////////////////////////////////////
                                        // time scale definition

`include 	"iop.h"
`include 	"sctag.h"

// comments. requires about 20 tracks per bit pitch in the 
// vertical direction.

////////////////////////////////////////////////////////////////////////
// Local header file includes / local define
////////////////////////////////////////////////////////////////////////

module sctag_arbaddrdp( /*AUTOARG*/
   // Outputs
   tagdp_evict_tag_c4_buf, so, arbdp_tag_idx_px2, 
   arbdp_vuad_idx1_px2, arbdp_vuad_idx2_px2, arbdp_tagdata_px2, 
   arbdp_cam_addr_px2, arbdp_new_addr5to4_px2, 
   arbdp_addr_c1c2comp_c1, arbdp_addr_c1c3comp_c1, idx_c1c2comp_c1, 
   idx_c1c3comp_c1, idx_c1c4comp_c1, idx_c1c5comp_c1, 
   arbdp_word_addr_c1, arbdp_ioaddr_c1, arbdp_addr5to4_c1, 
   arbdp_addr3to2_c1, arbdp_diag_wr_way_c2, sctag_scdata_set_c2, 
   arbaddr_addr22_c2, arbdp_addr5to4_c2, arbdp_addr_start_c2, 
   arbaddr_idx_c3, dir_cam_addr_c3, arbdp_dir_wr_par_c3, 
   arbdp_addr11to8_c3, arbdp_addr5to4_c3, arbdp_dbg_addr_c3, 
   c1_addr_eq_wb_c4, arbdp_rdmatctl_addr_c6, arbdp_waddr_c6, 
   arbdp_word_addr_c6, arbdp_byte_addr_c6, arbdp_addr22_c7, 
   arbdp_csr_addr_c9, rdmard_addr_c12, arbdp_line_addr_c7, 
   arbdp_inst_byte_addr_c7, arbdp_oqdp_l1_index_c7, 
   arbaddrdp_addr2_c8, data_ecc_idx, tag_wrdata_px2, 
   // Inputs
   iq_arbdp_addr_px2, snpq_arbdp_addr_px2, evicttag_addr_px2, 
   arbdata_wr_data_c2, tagdp_evict_tag_c4, csr_wr_dirpinj_en, 
   mux2_snpsel_px2, mux3_bufsel_px2, mux4_c1sel_px2, 
   inc_tag_ecc_cnt_c3_n, data_ecc_idx_reset, data_ecc_idx_en, 
   sel_vuad_bist_px2, sel_decc_or_bist_idx, sel_diag_addr_px2, 
   sel_tecc_addr_px2, sel_decc_addr_px2, sel_diag_tag_addr_px2, 
   sel_lkup_stalled_tag_px2, arbctl_imiss_hit_c10, 
   tagctl_rd64_complete_c11, arbctl_imiss_hit_c4, 
   sel_c2_stall_idx_c1, bist_data_set_c1, bist_data_enable_c1, 
   bist_vuad_idx_px1, rclk, si, se, diag_or_tecc_write_px2, 
   sel_way_px2
   );

// data to the L2 arbiter

input	[39:0]	iq_arbdp_addr_px2; // IQ instruction
input	[39:0]	snpq_arbdp_addr_px2; // PX2 instruction.
input	[39:0]	evicttag_addr_px2; // mb fb addr mux output.
input	[27:0]	arbdata_wr_data_c2; // for diagnostic tag writes. from arbdata // pin on the left
input	[`TAG_WIDTH-1:0] tagdp_evict_tag_c4 ; // read tag.	TOP

output	[`TAG_WIDTH-1:6] tagdp_evict_tag_c4_buf ;  // Place pins on the right.

input		csr_wr_dirpinj_en ; // parity injection into directory is enabled.


input		mux2_snpsel_px2; // snp,mb and fb
input		mux3_bufsel_px2; // snp,mb,fb or IQ
input		mux4_c1sel_px2; // snp,mb,fb,iq or C1

input		inc_tag_ecc_cnt_c3_n; // from arbctl.
input		data_ecc_idx_reset; // decc scrub idx = 0 from arbctl
input		data_ecc_idx_en; // decc scrub idx increment. from arbctl

input		sel_vuad_bist_px2; // NEW_PIN
input	 	sel_decc_or_bist_idx; // NEW_PIN
// input		sel_stall_vuad_idx ; // NEW_PIN from arbctl

input		sel_diag_addr_px2; // diag tag idx sel
input		sel_tecc_addr_px2; // tecc idx sel.
input		sel_decc_addr_px2; // decc idx sel.
input		sel_diag_tag_addr_px2; // diag or tecc or decc only
input		sel_lkup_stalled_tag_px2; // sel stalled address.


input		arbctl_imiss_hit_c10; // select to pick address
		     // for a csr write. NEW_PIN replaces OLD_PIN arbctl_imiss_hit_c8

input		tagctl_rd64_complete_c11; // NEW_PIN 
input		arbctl_imiss_hit_c4; // select to pick an address for camming the dir


input		sel_c2_stall_idx_c1; // sel from arbctl 
input	[9:0]	bist_data_set_c1; // from data bist
input		bist_data_enable_c1; // from databist
input	[9:0]	bist_vuad_idx_px1 ; // POST_3.0 pin

input		rclk;	
input		si,se;

output		so;

// PX2 outputs
output	[9:0]	arbdp_tag_idx_px2 ; // addr<17:8> going to tag 
output	[9:0]	arbdp_vuad_idx1_px2 ; // addr<17:8> going to vuad .
output	[9:0]	arbdp_vuad_idx2_px2 ; // addr<17:8> going to vuad .

// wr data to tagdp
output	[27:6]	arbdp_tagdata_px2; // lkup data for the tag.
output	[39:0]	arbdp_cam_addr_px2 ; // Address to cam MBF.
output	[1:0]	arbdp_new_addr5to4_px2; // to arbctl for col offset stall calculation ( does not include
					// the output of the stall mux .


// C1 outputs
output	arbdp_addr_c1c2comp_c1;	// to mbctl via arbctl
output	arbdp_addr_c1c3comp_c1;	// to mbctl via arbctl

output	idx_c1c2comp_c1 ; // to vuad dp via arbctl
output	idx_c1c3comp_c1 ; // to vuad dp via arbctl
output	idx_c1c4comp_c1 ; // to vuad dp via arbctl
output	idx_c1c5comp_c1; // to vuad dp via arbctl

output	[1:0]	arbdp_word_addr_c1; // to arbdec for pst decode logic
output	[39:32]	arbdp_ioaddr_c1; // bits 39-32 are used to determine if the
                                 // address space is DRAM or diagnostic.
output	[1:0]	arbdp_addr5to4_c1; // to arbctl foroffset stall calculation
output	[1:0]	arbdp_addr3to2_c1 ; // output to tagctl.

// C2 outputs
output	[3:0]	arbdp_diag_wr_way_c2; // bit of the diagnostic access address indicate way.
output	[9:0]	sctag_scdata_set_c2; // 2X wire going to scdata.
output		arbaddr_addr22_c2; // used by vuad dp for muxing diagnostic read data.
output	[1:0]	arbdp_addr5to4_c2 ; // output to arbctl  for col offset logic
output	arbdp_addr_start_c2;  // NEW_PIN to sctag_arbdec.


// C3 outputs
// output	[9:0]	vuad_idx_c3; // NEW_PIN to vuad array
output	[9:0]   arbaddr_idx_c3; // sent to tagdp.
output	[39:8]	dir_cam_addr_c3; // output to tagdp.
output		arbdp_dir_wr_par_c3 ; // wr data for i and d directories.
output	[7:4]	arbdp_addr11to8_c3; // output to arbctl  for dir cam logic
output	[1:0]	arbdp_addr5to4_c3 ; // output to arbctl  for dir cam logic
output	[5:2]	arbdp_dbg_addr_c3 ; // output to dbgdp.


output	c1_addr_eq_wb_c4; //output to wbctl.

//output	[5:2] 	arbdp_tagctl_addr_c6; // to tagctl
output	[5:2] 	arbdp_rdmatctl_addr_c6; // to scbuf_rep NEW_PIN
output	[1:0] 	arbdp_waddr_c6; // word addr to deccdp
output	[2:0]	arbdp_word_addr_c6 ; // address of a Byte to csr_ctl. NEW_PIN

output	[1:0]	arbdp_byte_addr_c6; // to arbdec for pst decode logic
output		arbdp_addr22_c7 ; // diagnostic  data word addr
output	[39:4]	arbdp_csr_addr_c9; // NEW _PIN replaces OLD_PIN arbdp_csr_addr_c7
output	[39:6]  	rdmard_addr_c12; // NEW_PIN
output	[5:4]	arbdp_line_addr_c7 ; // to oqdp.
output	[2:0]	arbdp_inst_byte_addr_c7 ; // to arbctl for dword mask generation.
output	[11:6]	arbdp_oqdp_l1_index_c7; // l1 index.

output		arbaddrdp_addr2_c8 ; // to arbctl for cas compare.


output	[9:0]	data_ecc_idx; //  output to the CSR block.


input	diag_or_tecc_write_px2; // new input. Left
input	sel_way_px2; // Left
output	[27:0]	tag_wrdata_px2 ; // interleave with pins arbdp_tagdata_px2
				 // at the bottom.





wire	[39:0]	tag_diag_wr_data_c2; // diagnostic wr data after processing.
wire	[29:0] 	err_tag_c4 ; // read tag.
wire		cbit_err;
wire	[29:0] 	tecc_corr_tag_c1; // corrected tag in  the tagecc pipeline.
wire	[27:0] 	tecc_corr_tag_c2; // corrected tag in  the tagecc pipeline.
wire		par_err_tag_c4; // par err.
wire	[9:0]	tag_ecc_idx;

wire	[39:0]	mux2_addr_px2; // snoop/mbf and fbf address.
wire	[39:0]	mux3_addr_px2; // snoop/mbf/fbf and Iq address.
wire	[39:0]	mux4_addr_px2; // snoop/mbf/fbf Iq address.

wire	[9:0]	data_ecc_idx_plus1; 

wire	[9:0]	tag_acc_idx_px2;
wire	[9:0]	mux_idx2_px2;
wire	[27:0]	tag_acc_data_px2;
wire	[27:0]	mux2_tagdata_px2;



wire	[4:0]	corr_bit;


wire	[39:0]	arbdp_addr_c1;
wire	[39:0]	arbdp_addr_c2;
wire	[39:0]	arbdp_addr_c3;
wire	[39:0]	arbdp_addr_c4;
wire	[39:0]	arbdp_addr_c5;
wire	[39:0]	arbdp_addr_c6;
wire	[39:0]	arbdp_addr_c7;
wire	[39:0]	arbdp_addr_c8;
wire	[39:0]	arbdp_addr_c9;
wire	[39:0]	arbdp_addr_c10;
wire	[39:0]	arbdp_addr_c11;


wire	[9:0]	data_idx_px2;
wire	[9:0]	data_idx_c1, data_bist_idx_c2, data_bist_idx_c1;
wire	[9:0]	stall_idx_c1;
wire	[39:8] evict_addr_c4 ;

wire	[9:0]	vuad_acc_idx_px2;
wire	[9:0]	vuad_idx2_px2;
wire	[9:0]	bist_vuad_idx;

/////////////////////////////////////////////////////////////
// dp is 30 bits wide eventhough tag is only 28 bits wide.
// ECC Correction and Generation for writing into the tag array.
// 30 bit wide dp eventhough, the tag is only 28 bits wide.
/////////////////////////////////////////////////////////////

assign	err_tag_c4 = {2'b0,tagdp_evict_tag_c4[`TAG_WIDTH-1:0]};

zzecc_sctag_30b_cor	ecc_corr(.din({err_tag_c4[29:6]}),
				 .parity(err_tag_c4[5:1]),
				 .dout(tecc_corr_tag_c1[29:6]),
				 .corrected_bit(corr_bit[4:0]));


assign	tecc_corr_tag_c1[5] = err_tag_c4[5] ^ ( corr_bit[4:0] == 5'd16) ;
assign	tecc_corr_tag_c1[4] = err_tag_c4[4] ^ ( corr_bit[4:0] == 5'd8) ;
assign	tecc_corr_tag_c1[3] = err_tag_c4[3] ^ ( corr_bit[4:0] == 5'd4) ;
assign	tecc_corr_tag_c1[2] = err_tag_c4[2] ^ ( corr_bit[4:0] == 5'd2) ;
assign	tecc_corr_tag_c1[1] = err_tag_c4[1] ^ ( corr_bit[4:0] == 5'd1) ;

assign	cbit_err	= |(corr_bit[4:0]);

zzpar32	par_bit	(.z(par_err_tag_c4), .d({err_tag_c4[29:0],2'b0}));

assign	tecc_corr_tag_c1[0] = ( par_err_tag_c4 & ~cbit_err ) ^ err_tag_c4[0] ;

dff_s     #(28) ff_tecc_corr_tag_c2   (.din(tecc_corr_tag_c1[27:0]), .clk(rclk),
                   .q(tecc_corr_tag_c2[27:0]), .se(se), .si(), .so());


/////////////////////////////////////////////////////////////////////////
// 1st level of ARB muxes 
// 1) Mux between Fb and MB addr	(in evicttag)
// 2) Mux between Mux1 and SNp data
// 3) Mux between Mux2 and IQ data
/////////////////////////////////////////////////////////////////////////


mux2ds	#(40) mux_mux2_instr_px2(.dout (mux2_addr_px2[39:0]) ,
		.in0(snpq_arbdp_addr_px2[39:0]), .in1(evicttag_addr_px2[39:0]),
		.sel0(mux2_snpsel_px2), .sel1(~mux2_snpsel_px2)); 

mux2ds	#(40) mux_mux3_instr_px2(.dout (mux3_addr_px2[39:0]) ,
		.in0(mux2_addr_px2[39:0]), .in1(iq_arbdp_addr_px2[39:0]),
		.sel0(mux3_bufsel_px2), .sel1(~mux3_bufsel_px2)); 

mux2ds	#(40) mux_mux4_instr_px2(.dout (mux4_addr_px2[39:0]) ,
		.in0(mux3_addr_px2[39:0]), .in1(arbdp_addr_c1[39:0]),
		.sel0(~mux4_c1sel_px2), .sel1(mux4_c1sel_px2)); 


assign	arbdp_new_addr5to4_px2 = mux3_addr_px2[5:4]; // column offset 
assign	arbdp_cam_addr_px2 =  mux4_addr_px2[39:0] ; // miss buffer cam address.

////////////////////////////////////////////////////////////////////////
// INDEX BITS TO THE VUAD.
////////////////////////////////////////////////////////////////////////


// data ecc index manipulation.
assign	data_ecc_idx_plus1 = data_ecc_idx + 10'b1 ;

//dffre   #(10)  ff_data_ecc_idx  (.din(data_ecc_idx_plus1[9:0]),
//                 .en(data_ecc_idx_en), .clk(rclk), .rst(data_ecc_idx_reset),
//                 .q(data_ecc_idx[9:0]), .se(se), .si(), .so());

clken_buf  ckbuf_data_ecc_idx
            (.clk   (clk_data_ecc_idx),   .rclk  (rclk),
             .enb_l (~data_ecc_idx_en),   .tmb_l (~se)
            ) ;
dffr_s    #(10)  ff_data_ecc_idx  (.din(data_ecc_idx_plus1[9:0]),
                 .clk(clk_data_ecc_idx), .rst(data_ecc_idx_reset),
                 .q(data_ecc_idx[9:0]), .se(se), .si(), .so());

// THIS FLOP IS NEW 
dff_s    #(10)  ff_bist_vuad_idx_px2  (.din(bist_vuad_idx_px1[9:0]),
                 	.clk(rclk), 
                 	.q(bist_vuad_idx[9:0]), .se(se), .si(), .so());


mux2ds	#(10) 	mux_vuad_acc_idx_px2(.dout ( vuad_acc_idx_px2[9:0] ) ,
			.in0(data_ecc_idx[9:0]),  // decc idx
			.in1(bist_vuad_idx[9:0]), // tecc idx
			.sel0(~sel_vuad_bist_px2), //  sel decc
			.sel1(sel_vuad_bist_px2)); // sel tecc

mux2ds	#(10) mux_vuad_idx2_px2(.dout (vuad_idx2_px2[9:0] ) ,
			.in0(vuad_acc_idx_px2[9:0]), // bist or decc idx
			.in1(arbdp_addr_c1[17:8]), // stalled addr
			.sel0(sel_decc_or_bist_idx),  // select diag/bist addr
			.sel1(~sel_decc_or_bist_idx)); // ~select diag/bist addr

assign	arbdp_vuad_idx1_px2 = mux3_addr_px2[17:8] ; // index for unstalled operations.

assign	arbdp_vuad_idx2_px2 = vuad_idx2_px2[9:0] ; // index for stalled operations.

//mux2ds #(10) mux_vuad_idx_px2(.dout (vuad_idx_px2[9:0] ) ,
			//.in0(vuad_idx2_px2[9:0]), 
			//.in1(mux3_addr_px2[17:8]), 
			//.sel0(sel_stall_vuad_idx),  
			//.sel1(~sel_stall_vuad_idx)); 

//dff    #(10) ff_vuad_idx_c1   (.din(vuad_idx_px2[9:0]), .clk(rclk), 
		//.q(vuad_idx_c1[9:0]), .se(se), .si(), .so());
//
//dff    #(10) ff_vuad_idx_c2   (.din(vuad_idx_c1[9:0]), .clk(rclk), 
		//.q(vuad_idx_c2[9:0]), .se(se), .si(), .so());
//
//dff    #(10) ff_vuad_idx_c3   (.din(vuad_idx_c2[9:0]), .clk(rclk), 
		//.q(vuad_idx_c3[9:0]), .se(se), .si(), .so());


////////////////////////////////////////////////////////////////////////
// INDEX BITS TO THE TAG.
// The index of a C1 stalled instruction is muxed with the following
// components to generate the address for accessing tag/vuad arrays
// tag_ecc addr.
// data_ecc_addr.
// tag diagnostic addr.
// ( The tag BIST mux is located inside the tag array )
//
// two separate addresses are sent to the tag array/vuad array.
// these arrays select between the new address or the address of the 
// stalled instruction. The select signal is generated in arbctl.v
////////////////////////////////////////////////////////////////////////
//dffe    #(10)    ff_idx_hold_c2   (.din(arbdp_addr_c2[17:8]),
//		       .en(inc_tag_ecc_cnt_c3_n), .clk(rclk),
//                       .q(tag_ecc_idx[9:0]), .se(se), .si(), .so());

clken_buf  ckbuf_idx_hold
            (.clk   (clk_idx_hold),            .rclk  (rclk),
             .enb_l (~inc_tag_ecc_cnt_c3_n),   .tmb_l (~se)
            ) ;
dff_s     #(10)    ff_idx_hold_c2   (.din(arbdp_addr_c2[17:8]), .clk(clk_idx_hold),
                       .q(tag_ecc_idx[9:0]), .se(se), .si(), .so());


mux3ds	#(10) 	mux_tag_idx_px(.dout ( tag_acc_idx_px2[9:0] ) ,
			.in0(data_ecc_idx[9:0]),  // decc idx
			.in1(tag_ecc_idx[9:0]), // tecc idx
			.in2(arbdp_addr_c2[17:8]), // diagnostic wr.
			.sel0(sel_decc_addr_px2), //  sel decc
			.sel1(sel_tecc_addr_px2), // sel tecc
			.sel2(sel_diag_addr_px2)); // sel diag wr.

mux2ds	#(10) mux_mux_idx2_px2(.dout (mux_idx2_px2[9:0] ) ,
			.in0(tag_acc_idx_px2[9:0]), // tecc, decc and diag write.
			.in1(arbdp_addr_c1[17:8]), // stalled addr
			.sel0(sel_diag_tag_addr_px2),  // select diag/tecc/decc addr
			.sel1(~sel_diag_tag_addr_px2)); // sel stalled addr.

mux2ds	#(10) mux_data_idx_px2(.dout (data_idx_px2[9:0] ) ,
			.in0(mux_idx2_px2[9:0]), // C1 or modified index
			.in1(mux3_addr_px2[17:8]), // instruction Px2 addr
			.sel0(sel_lkup_stalled_tag_px2),  // select diag/tecc/decc addr
			.sel1(~sel_lkup_stalled_tag_px2)); // sel stalled addr.

assign	arbdp_tag_idx_px2 =  data_idx_px2[9:0]; // index for tag access.

///////////////////////////////////////////////////////////////////////////
// sctag_scdata_set_c2
//	If an operation is stalled in C1, the C1 and C2 indices are
//	maintained until the stall is deasserted.
// 
//	The set calculation is done with 3 2:1 muxes as follows
//	mux1: select between a stalled C1 addr ( from C1 op, decc idx, 
//		tecc idx, diagnostic idx ) and a PX2 operation.
//	mux2(c2 stall mux): select between the FLOPPED mux1 output C2 idx.
//
//	mux3(bust mux flop): select between bist idx and the output of mux2
//	
//	Notice that the C1 and C2 indices are stalled.
///////////////////////////////////////////////////////////////////////////

// use a mux flop here to reduce setup.
dff_s    #(10) ff_scdata_idx_c1   (.din(data_idx_px2[9:0]), .clk(rclk), 
		.q(data_idx_c1[9:0]), .se(se), .si(), .so());

mux2ds	#(10) mux_c2stall(.dout (stall_idx_c1[9:0] ) ,
			.in0(data_idx_c1[9:0]),  // idx of C1 instruction
			.in1(data_bist_idx_c2[9:0]), // BIST set
			.sel0(~sel_c2_stall_idx_c1),   // stalled c2 address is NOT selected
			.sel1(sel_c2_stall_idx_c1));  // stalled c2 address is selected 

// C2 address stall mux.
// If a stall is asserted, the C2 address needs to be
// retained. THis is 

mux2ds	#(10) mux_data_idx_c1(.dout (data_bist_idx_c1[9:0] ) ,
			.in0(stall_idx_c1[9:0]),  // idx of C1 instruction
			.in1(bist_data_set_c1[9:0]), // BIST set
			.sel0(~bist_data_enable_c1),  
			.sel1(bist_data_enable_c1)); 

// use a mux flop here to reduce setup.
dff_s    #(10) ff_scdata_idx_c2   (.din(data_bist_idx_c1[9:0]), .clk(rclk), 
		.q(data_bist_idx_c2[9:0]), .se(se), .si(), .so());

assign	sctag_scdata_set_c2 = data_bist_idx_c2 ;


///////////////////////////////////////////////////////////////////////
// other bits of the tag.
///////////////////////////////////////////////////////////////////////

// diagnostic wr data 
assign	tag_diag_wr_data_c2[39:18] = arbdata_wr_data_c2[27:6] ; // c2 data.
assign	tag_diag_wr_data_c2[5:0] =   arbdata_wr_data_c2[5:0]; // tag ecc bits.

mux2ds	 #(28) 	mux_tag_acc_data_px2(	
			.dout(tag_acc_data_px2[27:0]) ,
			.in0(tecc_corr_tag_c2[27:0]), // corr tecc tag.
			.in1({tag_diag_wr_data_c2[39:18],tag_diag_wr_data_c2[5:0]}), // diagnostic write tag.
			.sel0(~inc_tag_ecc_cnt_c3_n), // tecc active
			.sel1(inc_tag_ecc_cnt_c3_n)); // tecc not active

//*******************************************************************
// Changes start here.
// changed sel0 and sel1 ;
mux2ds	 #(28) 	mux_tag_stalled_data(	
			.dout(mux2_tagdata_px2[27:0]) ,
			.in0(tag_acc_data_px2[27:0]), // corr tecc tag or diag data
			.in1({arbdp_addr_c1[39:18],arbdp_addr_c1[5:0]}), // c1 tag
			.sel0(diag_or_tecc_write_px2), // diag ortecc or decc active
			.sel1(~diag_or_tecc_write_px2)); // no diag or tecc access.

//Added this mux 
mux2ds	 #(28) 	mux_tag_wrdata_px2(	
			.dout(tag_wrdata_px2[27:0]) ,
			.in0(mux2_tagdata_px2[27:0]), // corr tecc tag or diag data
			.in1({evicttag_addr_px2[39:18],evicttag_addr_px2[5:0]}), // px2 fill tag
			.sel0(~sel_way_px2), // diag ortecc or decc active
			.sel1(sel_way_px2)); // no diag or tecc access.

// LKUP addr.
// changed in0
mux2ds	 #(22) 	mux_arbdp_tagdata_px2(	
			.dout(arbdp_tagdata_px2[27:6]) ,
			.in0(arbdp_addr_c1[39:18]), // c1 tag
			.in1(mux3_addr_px2[39:18]), // tag from other srcs
			.sel0(sel_lkup_stalled_tag_px2), // stalled tag sel.
			.sel1(~sel_lkup_stalled_tag_px2)); // new tag sel

// Changes end here.
//*******************************************************************

// the whole tag for CAMMIng the miss buffer.
dff_s    #(40) ff_inst_addr_c1   (.din(mux4_addr_px2[39:0]), .clk(rclk), 
		.q(arbdp_addr_c1[39:0]), .se(se), .si(), .so());

assign	arbdp_addr5to4_c1 = arbdp_addr_c1[5:4] ; // to arbctl for col offset stall calculation.
assign	arbdp_addr3to2_c1 = arbdp_addr_c1[3:2] ;
assign	arbdp_ioaddr_c1 = arbdp_addr_c1[39:32] ; // to arbctl for diag acc decode
assign	arbdp_word_addr_c1 = arbdp_addr_c1[1:0] ; // pst decode in arbdec

dff_s     #(40)    ff_addr_c2   (.din(arbdp_addr_c1[39:0]), .clk(rclk),
                .q(arbdp_addr_c2[39:0]), .se(se), .si(), .so());


assign	arbaddr_addr22_c2 =  arbdp_addr_c2[22] ; 

assign	arbdp_addr5to4_c2 = arbdp_addr_c2[5:4] ;
assign	arbdp_diag_wr_way_c2 = arbdp_addr_c2[21:18] ;// diag wr way

// The following signal indicates that the access is issued to 
// addr0 of a cacheline.


assign	arbdp_addr_start_c2 = ( arbdp_addr_c2[5:0] == 6'b0 ) ;


dff_s     #(40)    ff_addr_c3   (.din(arbdp_addr_c2[39:0]), .clk(rclk),
              	.q(arbdp_addr_c3[39:0]), .se(se), .si(), .so());

assign	arbdp_addr5to4_c3 = arbdp_addr_c3[5:4] ; // used in arbctl for dir cam

assign	arbaddr_idx_c3 = arbdp_addr_c3[17:8] ; // for  vuad array writes.

//////	POST_4.1
//assign	arbdp_addr11to4_c3 =  arbdp_addr_c3[11:4] ;
assign	arbdp_addr11to8_c3[7:4] =  arbdp_addr_c3[11:8] ;
//////


assign	arbdp_dbg_addr_c3 = {arbdp_addr_c3[5:2] };

dff_s     #(40)    ff_addr_c4   (.din(arbdp_addr_c3[39:0]), .clk(rclk),
                .q(arbdp_addr_c4[39:0]), .se(se), .si(), .so());

// address for CAMMing the directory. i.e. lkup key
// wr data into the directory.
// The evict addr is muxed into this value in tagdp.

mux2ds #(32) mux_tmp_cam_addr_c3 ( .dout (dir_cam_addr_c3[39:8]),
             .in0(arbdp_addr_c3[39:8]), .in1(arbdp_addr_c4[39:8]),
             .sel0(~arbctl_imiss_hit_c4), .sel1(arbctl_imiss_hit_c4));

assign	arbdp_dir_wr_par_c3 = ^(arbdp_addr_c3[39:10]) ^ csr_wr_dirpinj_en ;



dff_s     #(40)    ff_addr_c5   (.din(arbdp_addr_c4[39:0]), .clk(rclk),
                .q(arbdp_addr_c5[39:0]), .se(se), .si(), .so());

dff_s     #(40)    ff_addr_c6   (.din(arbdp_addr_c5[39:0]), .clk(rclk),
                .q(arbdp_addr_c6[39:0]), .se(se), .si(), .so());

assign	arbdp_word_addr_c6 = arbdp_addr_c6[34:32] ;// word address to csr ctl.
assign	arbdp_waddr_c6  = arbdp_addr_c6[3:2] ; // word address tpo 
assign	arbdp_rdmatctl_addr_c6 = arbdp_addr_c6[5:2] ; // requrired in rdma state logic.
assign	arbdp_oqdp_l1_index_c7[11:6] = arbdp_addr_c7[11:6] ; // idx bits to oqdp
assign	arbdp_byte_addr_c6 = arbdp_addr_c6[1:0] ; // to arbdec for ctag generation

dff_s     #(40)    ff_addr_c7   (.din(arbdp_addr_c6[39:0]), .clk(rclk),
                .q(arbdp_addr_c7[39:0]), .se(se), .si(), .so());

assign	arbdp_inst_byte_addr_c7 = arbdp_addr_c7[2:0] ; // byte address	to arbctl.
assign	arbdp_addr22_c7 = arbdp_addr_c7[22] ; // diagnostic data word addr.
assign	arbdp_line_addr_c7[5:4] = arbdp_addr_c7[5:4] ;// required by oqdp   but pipe stage may change



dff_s     #(40)    ff_addr_c8   (.din(arbdp_addr_c7[39:0]), .clk(rclk),
                .q(arbdp_addr_c8[39:0]), .se(se), .si(), .so());

assign	arbaddrdp_addr2_c8 = arbdp_addr_c8[2] ; // for cas compare.

dff_s     #(40)    ff_addr_c9   (.din(arbdp_addr_c8[39:0]), .clk(rclk),
                .q(arbdp_addr_c9[39:0]), .se(se), .si(), .so());

dff_s     #(40)    ff_addr_c10   (.din(arbdp_addr_c9[39:0]), .clk(rclk),
                .q(arbdp_addr_c10[39:0]), .se(se), .si(), .so());

dff_s     #(40)    ff_addr_c11   (.din(arbdp_addr_c10[39:0]), .clk(rclk),
                .q(arbdp_addr_c11[39:0]), .se(se), .si(), .so());

///////////////////////////////////////////////////
// Addr to csr block is the address of a ld in C9
// or an imiss in C10
///////////////////////////////////////////////////

mux2ds #(36) mux_arbdp_csr_addr_c9 ( .dout (arbdp_csr_addr_c9[39:4]),
              .in0(arbdp_addr_c9[39:4]), .in1(arbdp_addr_c10[39:4]),
              .sel0(~arbctl_imiss_hit_c10), .sel1(arbctl_imiss_hit_c10));


///////////////////////////////////////////////////
// Addr of an ld64 instruction  is staged till C11
///////////////////////////////////////////////////

//dffe   #(34)  ff_arbdp_addr_c12    (.din(arbdp_addr_c11[39:6]), .clk(rclk),
//               .en(tagctl_rd64_complete_c11),
//               .q(rdmard_addr_c12[39:6]), .se(se), .si(), .so());

clken_buf  ckbuf_addr_c12
            (.clk   (clk_addr_c12),                .rclk  (rclk),
             .enb_l (~tagctl_rd64_complete_c11),   .tmb_l (~se)
            ) ;
dff_s   #(34)  ff_arbdp_addr_c12    (.din(arbdp_addr_c11[39:6]), .clk(clk_addr_c12),
               .q(rdmard_addr_c12[39:6]), .se(se), .si(), .so());





 
// ADDR  COMPARATORS for mbf bypass 
assign	arbdp_addr_c1c2comp_c1 = 
		( arbdp_addr_c1[39:8] == arbdp_addr_c2[39:8] ) ;
assign	arbdp_addr_c1c3comp_c1 = 
		( arbdp_addr_c1[39:8] == arbdp_addr_c3[39:8] ) ;

// INDEX COMPARATORS for VUAD bypass

assign	idx_c1c2comp_c1 = ( arbdp_addr_c1[17:8] == arbdp_addr_c2[17:8] ) ;
assign	idx_c1c3comp_c1 = ( arbdp_addr_c1[17:8] == arbdp_addr_c3[17:8] ) ;
assign	idx_c1c4comp_c1 = ( arbdp_addr_c1[17:8] == arbdp_addr_c4[17:8] ) ;
assign	idx_c1c5comp_c1 = ( arbdp_addr_c1[17:8] == arbdp_addr_c5[17:8] ) ;


///////////////////////////////////////////////
// bypassing of wb_write_data
// required for generation
// of wb hit.
// evicted tag is written into the WBB in C5.
// The operation in C2 in that cycle will have
// to see the effect of the wb write. Hence the
// C4 address being written into the tag is compared
// with the address of the instruction in C1.
//////////////////////////////////////////////

assign  evict_addr_c4[39:18] = tagdp_evict_tag_c4[`TAG_WIDTH-1:6] ;
assign  evict_addr_c4[17:8] = arbdp_addr_c4[17:8] ;

assign  c1_addr_eq_wb_c4 = (evict_addr_c4[39:8] == arbdp_addr_c1[39:8]);


//////////////////////////////////////////////
// Added a buffer for tagdp_evict_tag_c4
// tagdp_evict_tag_c4_buf output pins are placed on
// the right. Any pin order from top-bottom should
// be okay.
//////////////////////////////////////////////

assign	tagdp_evict_tag_c4_buf[`TAG_WIDTH-1:6] = tagdp_evict_tag_c4[`TAG_WIDTH-1:6];



endmodule


