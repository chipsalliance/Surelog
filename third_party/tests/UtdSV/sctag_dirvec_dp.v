// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_dirvec_dp.v
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
/*
//  Module Name: dirvec_dp.v
*/
////////////////////////////////////////////////////////////////////////

module sctag_dirvec_dp( /*AUTOARG*/
   // Outputs
   dirdp_req_vec_c6, dirdp_way_info_c7, dirdp_inval_pckt_c7, so, 
   // Inputs
   se, si, ic_cam_hit, dc_cam_hit, tagdp_lkup_addr11_c5, sel_mux1_c6, 
   sel_mux2_c6, sel_mux3_c6, mux_vec_sel_c6, rclk
   ) ;

input	se, si;
input   [127:0]  ic_cam_hit;
input   [127:0]  dc_cam_hit;

input            tagdp_lkup_addr11_c5;

input   [  3:0]  sel_mux1_c6;
input   [  3:0]  sel_mux2_c6;
input            sel_mux3_c6;

input   [  3:0]  mux_vec_sel_c6;

input            rclk;

output  [  7:0]  dirdp_req_vec_c6;

output  [  2:0]  dirdp_way_info_c7;
output  [111:0]  dirdp_inval_pckt_c7;
output	so;

wire    [127:0]  dc_cam_hit_c6;
wire    [127:0]  ic_cam_hit_c6;
wire    [127:0]  dc_cam_hit_c5;
wire    [ 63:0]  ic_cam_hit_c5;

wire    [111:0]  dirdp_inval_pckt_c6;
wire    [  2:0]  dirvecdp_way_info_c6;
wire    [111:0]  dirdp_inval_pckt_c7;
wire    [  2:0]  dirvecdp_way_info_c7;



//************************************************************************************
// FLOP INVAL PCKT TILL C6
//************************************************************************************


dff_s   #(112)  ff_dirdp_inval_pckt_c7    (.din(dirdp_inval_pckt_c6[111:0]),
                              .clk(rclk),
                              .q(dirdp_inval_pckt_c7[111:0]),
                              .se(se),
                              .si(),
                              .so());


//************************************************************************************
// FLOP way INFO PCKT TILL C6
//************************************************************************************

dff_s   #(3)  ff_dirvecdp_way_info_c7    (.din(dirvecdp_way_info_c6[2:0]),
                              .clk(rclk),
                              .q(dirvecdp_way_info_c7[2:0]),
                              .se(se),
                              .si(),
                              .so());

assign	dirdp_way_info_c7 = dirvecdp_way_info_c7 ;

//*****************************************************************************
// PIPELINE FOR DIR VEC GENERATION
// DC cam hit has to be 128 b.
// IC cam hit is 64b and the 128b output of icdir needs to be muxed.
//*****************************************************************************

assign	dc_cam_hit_c5	= 	dc_cam_hit ;

dff_s   #(128)  ff_dc_cam_hit_c6    ( .din(dc_cam_hit_c5[127:0]),
                              .clk(rclk),
                              .q(dc_cam_hit_c6[127:0]),
                              .se(se),
                              .si(),
                              .so());


mux2ds #(32) mux1_cam_hit_c5 ( .dout(ic_cam_hit_c5[31:0]),
                              .in0(ic_cam_hit[31:0]),
                              .in1(ic_cam_hit[63:32]),
                              .sel0(~tagdp_lkup_addr11_c5),
                              .sel1(tagdp_lkup_addr11_c5));

mux2ds #(32) mux2_cam_hit_c5 ( .dout(ic_cam_hit_c5[63:32]),
                              .in0(ic_cam_hit[95:64]),
                              .in1(ic_cam_hit[127:96]),
                              .sel0(~tagdp_lkup_addr11_c5),
                              .sel1(tagdp_lkup_addr11_c5));

dff_s   #(32)  ff_dc1_cam_hit_c6    ( .din(ic_cam_hit_c5[31:0]),
                              .clk(rclk),
                              .q(ic_cam_hit_c6[31:0]),
                              .se(se),
                              .si(),
                              .so());

dff_s   #(32)  ff_dc2_cam_hit_c6    ( .din(ic_cam_hit_c5[63:32]),
                              .clk(rclk),
                              .q(ic_cam_hit_c6[95:64]),
                              .se(se),
                              .si(),
                              .so());


//*****************************************************************************
// FORM THE 112b PACKET in C4 ( step 1)
// Get the request vect to be sent to oq_dp 
// Get the I$ and D$ invalidation way for L1 load misses.
// DC cam hit has to be 128 b.
// IC cam hit is 64b and the 128b output of icdir needs to be muxed.
//*****************************************************************************



// BITS 0 - 31 CORRESPOND to INDEX <5:4> = 00 for D$
//				INDEX <5>=0 for I$

// GENERATED CODE


		/***************** START wire declarations FOR 0-31 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b0 
		wire    dc_dir_vec0_c6;
		wire    ic_dir_vec0_c6;

		wire	dir_hit_vec0_c6 ;
		wire    [1:0]   enc_dc_vec0_way_c6;
		wire    [1:0]   enc_ic_vec0_way_c6;

		wire    [1:0]   enc_c_vec0_way_c6;

		wire	[2:0]	way_way_vld0_c6 ;
		/***************** END wire declarations FOR 0-31 ******************/
		
		/***************** START wire declarations FOR 0-31 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b0 
		wire    dc_dir_vec4_c6;
		wire    ic_dir_vec4_c6;

		wire	dir_hit_vec4_c6 ;
		wire    [1:0]   enc_dc_vec4_way_c6;
		wire    [1:0]   enc_ic_vec4_way_c6;

		wire    [1:0]   enc_c_vec4_way_c6;

		wire	[2:0]	way_way_vld4_c6 ;
		/***************** END wire declarations FOR 0-31 ******************/
		
		/***************** START wire declarations FOR 0-31 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b0 
		wire    dc_dir_vec8_c6;
		wire    ic_dir_vec8_c6;

		wire	dir_hit_vec8_c6 ;
		wire    [1:0]   enc_dc_vec8_way_c6;
		wire    [1:0]   enc_ic_vec8_way_c6;

		wire    [1:0]   enc_c_vec8_way_c6;

		wire	[2:0]	way_way_vld8_c6 ;
		/***************** END wire declarations FOR 0-31 ******************/
		
		/***************** START wire declarations FOR 0-31 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b0 
		wire    dc_dir_vec12_c6;
		wire    ic_dir_vec12_c6;

		wire	dir_hit_vec12_c6 ;
		wire    [1:0]   enc_dc_vec12_way_c6;
		wire    [1:0]   enc_ic_vec12_way_c6;

		wire    [1:0]   enc_c_vec12_way_c6;

		wire	[2:0]	way_way_vld12_c6 ;
		/***************** END wire declarations FOR 0-31 ******************/
		
		/***************** START wire declarations FOR 0-31 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b0 
		wire    dc_dir_vec16_c6;
		wire    ic_dir_vec16_c6;

		wire	dir_hit_vec16_c6 ;
		wire    [1:0]   enc_dc_vec16_way_c6;
		wire    [1:0]   enc_ic_vec16_way_c6;

		wire    [1:0]   enc_c_vec16_way_c6;

		wire	[2:0]	way_way_vld16_c6 ;
		/***************** END wire declarations FOR 0-31 ******************/
		
		/***************** START wire declarations FOR 0-31 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b0 
		wire    dc_dir_vec20_c6;
		wire    ic_dir_vec20_c6;

		wire	dir_hit_vec20_c6 ;
		wire    [1:0]   enc_dc_vec20_way_c6;
		wire    [1:0]   enc_ic_vec20_way_c6;

		wire    [1:0]   enc_c_vec20_way_c6;

		wire	[2:0]	way_way_vld20_c6 ;
		/***************** END wire declarations FOR 0-31 ******************/
		
		/***************** START wire declarations FOR 0-31 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b0 
		wire    dc_dir_vec24_c6;
		wire    ic_dir_vec24_c6;

		wire	dir_hit_vec24_c6 ;
		wire    [1:0]   enc_dc_vec24_way_c6;
		wire    [1:0]   enc_ic_vec24_way_c6;

		wire    [1:0]   enc_c_vec24_way_c6;

		wire	[2:0]	way_way_vld24_c6 ;
		/***************** END wire declarations FOR 0-31 ******************/
		
		/***************** START wire declarations FOR 0-31 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b0 
		wire    dc_dir_vec28_c6;
		wire    ic_dir_vec28_c6;

		wire	dir_hit_vec28_c6 ;
		wire    [1:0]   enc_dc_vec28_way_c6;
		wire    [1:0]   enc_ic_vec28_way_c6;

		wire    [1:0]   enc_c_vec28_way_c6;

		wire	[2:0]	way_way_vld28_c6 ;
		/***************** END wire declarations FOR 0-31 ******************/
		
		/***************** START code for generating return pckt. ******************/
		// indicates whether D
		assign  dc_dir_vec0_c6 = ( dc_cam_hit_c6[0] | dc_cam_hit_c6[1] |
                                dc_cam_hit_c6[2] | dc_cam_hit_c6[3] ) ;

		// indicates whether I
		assign  ic_dir_vec0_c6 = ( ic_cam_hit_c6[0] | ic_cam_hit_c6[1] |
                                ic_cam_hit_c6[2] | ic_cam_hit_c6[3] ) ;

		// indicates whether hit
		assign	dir_hit_vec0_c6 =  dc_dir_vec0_c6 | ic_dir_vec0_c6 ;

		//  hit way in D
		assign  enc_dc_vec0_way_c6[0]  = dc_cam_hit_c6[1] | dc_cam_hit_c6[3] ;
		assign  enc_dc_vec0_way_c6[1]  = dc_cam_hit_c6[2] | dc_cam_hit_c6[3] ;

		//  hit way in I
		assign  enc_ic_vec0_way_c6[0]  = ic_cam_hit_c6[1] | ic_cam_hit_c6[3] ;
		assign  enc_ic_vec0_way_c6[1]  = ic_cam_hit_c6[2] | ic_cam_hit_c6[3] ;


		mux2ds #(2) mux2_c_vec0_way  ( .dout(enc_c_vec0_way_c6[1:0]),
                              .in0(enc_dc_vec0_way_c6[1:0]),
                              .in1(enc_ic_vec0_way_c6[1:0]),
                              .sel0(~ic_dir_vec0_c6),
                              .sel1(ic_dir_vec0_c6)); 


		assign	way_way_vld0_c6[0] = enc_c_vec0_way_c6[0] ;
		assign	way_way_vld0_c6[1] = enc_c_vec0_way_c6[1] ;
		assign	way_way_vld0_c6[2] = dir_hit_vec0_c6 ;
		/***************** END code for generating return pckt. ******************/

	
		/***************** START code for generating return pckt. ******************/
		// indicates whether D
		assign  dc_dir_vec4_c6 = ( dc_cam_hit_c6[4] | dc_cam_hit_c6[5] |
                                dc_cam_hit_c6[6] | dc_cam_hit_c6[7] ) ;

		// indicates whether I
		assign  ic_dir_vec4_c6 = ( ic_cam_hit_c6[4] | ic_cam_hit_c6[5] |
                                ic_cam_hit_c6[6] | ic_cam_hit_c6[7] ) ;

		// indicates whether hit
		assign	dir_hit_vec4_c6 =  dc_dir_vec4_c6 | ic_dir_vec4_c6 ;

		//  hit way in D
		assign  enc_dc_vec4_way_c6[0]  = dc_cam_hit_c6[5] | dc_cam_hit_c6[7] ;
		assign  enc_dc_vec4_way_c6[1]  = dc_cam_hit_c6[6] | dc_cam_hit_c6[7] ;

		//  hit way in I
		assign  enc_ic_vec4_way_c6[0]  = ic_cam_hit_c6[5] | ic_cam_hit_c6[7] ;
		assign  enc_ic_vec4_way_c6[1]  = ic_cam_hit_c6[6] | ic_cam_hit_c6[7] ;


		mux2ds #(2) mux2_c_vec4_way  ( .dout(enc_c_vec4_way_c6[1:0]),
                              .in0(enc_dc_vec4_way_c6[1:0]),
                              .in1(enc_ic_vec4_way_c6[1:0]),
                              .sel0(~ic_dir_vec4_c6),
                              .sel1(ic_dir_vec4_c6)); 


		assign	way_way_vld4_c6[0] = enc_c_vec4_way_c6[0] ;
		assign	way_way_vld4_c6[1] = enc_c_vec4_way_c6[1] ;
		assign	way_way_vld4_c6[2] = dir_hit_vec4_c6 ;
		/***************** END code for generating return pckt. ******************/

	
		/***************** START code for generating return pckt. ******************/
		// indicates whether D
		assign  dc_dir_vec8_c6 = ( dc_cam_hit_c6[8] | dc_cam_hit_c6[9] |
                                dc_cam_hit_c6[10] | dc_cam_hit_c6[11] ) ;

		// indicates whether I
		assign  ic_dir_vec8_c6 = ( ic_cam_hit_c6[8] | ic_cam_hit_c6[9] |
                                ic_cam_hit_c6[10] | ic_cam_hit_c6[11] ) ;

		// indicates whether hit
		assign	dir_hit_vec8_c6 =  dc_dir_vec8_c6 | ic_dir_vec8_c6 ;

		//  hit way in D
		assign  enc_dc_vec8_way_c6[0]  = dc_cam_hit_c6[9] | dc_cam_hit_c6[11] ;
		assign  enc_dc_vec8_way_c6[1]  = dc_cam_hit_c6[10] | dc_cam_hit_c6[11] ;

		//  hit way in I
		assign  enc_ic_vec8_way_c6[0]  = ic_cam_hit_c6[9] | ic_cam_hit_c6[11] ;
		assign  enc_ic_vec8_way_c6[1]  = ic_cam_hit_c6[10] | ic_cam_hit_c6[11] ;


		mux2ds #(2) mux2_c_vec8_way  ( .dout(enc_c_vec8_way_c6[1:0]),
                              .in0(enc_dc_vec8_way_c6[1:0]),
                              .in1(enc_ic_vec8_way_c6[1:0]),
                              .sel0(~ic_dir_vec8_c6),
                              .sel1(ic_dir_vec8_c6)); 


		assign	way_way_vld8_c6[0] = enc_c_vec8_way_c6[0] ;
		assign	way_way_vld8_c6[1] = enc_c_vec8_way_c6[1] ;
		assign	way_way_vld8_c6[2] = dir_hit_vec8_c6 ;
		/***************** END code for generating return pckt. ******************/

	
		/***************** START code for generating return pckt. ******************/
		// indicates whether D
		assign  dc_dir_vec12_c6 = ( dc_cam_hit_c6[12] | dc_cam_hit_c6[13] |
                                dc_cam_hit_c6[14] | dc_cam_hit_c6[15] ) ;

		// indicates whether I
		assign  ic_dir_vec12_c6 = ( ic_cam_hit_c6[12] | ic_cam_hit_c6[13] |
                                ic_cam_hit_c6[14] | ic_cam_hit_c6[15] ) ;

		// indicates whether hit
		assign	dir_hit_vec12_c6 =  dc_dir_vec12_c6 | ic_dir_vec12_c6 ;

		//  hit way in D
		assign  enc_dc_vec12_way_c6[0]  = dc_cam_hit_c6[13] | dc_cam_hit_c6[15] ;
		assign  enc_dc_vec12_way_c6[1]  = dc_cam_hit_c6[14] | dc_cam_hit_c6[15] ;

		//  hit way in I
		assign  enc_ic_vec12_way_c6[0]  = ic_cam_hit_c6[13] | ic_cam_hit_c6[15] ;
		assign  enc_ic_vec12_way_c6[1]  = ic_cam_hit_c6[14] | ic_cam_hit_c6[15] ;


		mux2ds #(2) mux2_c_vec12_way  ( .dout(enc_c_vec12_way_c6[1:0]),
                              .in0(enc_dc_vec12_way_c6[1:0]),
                              .in1(enc_ic_vec12_way_c6[1:0]),
                              .sel0(~ic_dir_vec12_c6),
                              .sel1(ic_dir_vec12_c6)); 


		assign	way_way_vld12_c6[0] = enc_c_vec12_way_c6[0] ;
		assign	way_way_vld12_c6[1] = enc_c_vec12_way_c6[1] ;
		assign	way_way_vld12_c6[2] = dir_hit_vec12_c6 ;
		/***************** END code for generating return pckt. ******************/

	
		/***************** START code for generating return pckt. ******************/
		// indicates whether D
		assign  dc_dir_vec16_c6 = ( dc_cam_hit_c6[16] | dc_cam_hit_c6[17] |
                                dc_cam_hit_c6[18] | dc_cam_hit_c6[19] ) ;

		// indicates whether I
		assign  ic_dir_vec16_c6 = ( ic_cam_hit_c6[16] | ic_cam_hit_c6[17] |
                                ic_cam_hit_c6[18] | ic_cam_hit_c6[19] ) ;

		// indicates whether hit
		assign	dir_hit_vec16_c6 =  dc_dir_vec16_c6 | ic_dir_vec16_c6 ;

		//  hit way in D
		assign  enc_dc_vec16_way_c6[0]  = dc_cam_hit_c6[17] | dc_cam_hit_c6[19] ;
		assign  enc_dc_vec16_way_c6[1]  = dc_cam_hit_c6[18] | dc_cam_hit_c6[19] ;

		//  hit way in I
		assign  enc_ic_vec16_way_c6[0]  = ic_cam_hit_c6[17] | ic_cam_hit_c6[19] ;
		assign  enc_ic_vec16_way_c6[1]  = ic_cam_hit_c6[18] | ic_cam_hit_c6[19] ;


		mux2ds #(2) mux2_c_vec16_way  ( .dout(enc_c_vec16_way_c6[1:0]),
                              .in0(enc_dc_vec16_way_c6[1:0]),
                              .in1(enc_ic_vec16_way_c6[1:0]),
                              .sel0(~ic_dir_vec16_c6),
                              .sel1(ic_dir_vec16_c6)); 


		assign	way_way_vld16_c6[0] = enc_c_vec16_way_c6[0] ;
		assign	way_way_vld16_c6[1] = enc_c_vec16_way_c6[1] ;
		assign	way_way_vld16_c6[2] = dir_hit_vec16_c6 ;
		/***************** END code for generating return pckt. ******************/

	
		/***************** START code for generating return pckt. ******************/
		// indicates whether D
		assign  dc_dir_vec20_c6 = ( dc_cam_hit_c6[20] | dc_cam_hit_c6[21] |
                                dc_cam_hit_c6[22] | dc_cam_hit_c6[23] ) ;

		// indicates whether I
		assign  ic_dir_vec20_c6 = ( ic_cam_hit_c6[20] | ic_cam_hit_c6[21] |
                                ic_cam_hit_c6[22] | ic_cam_hit_c6[23] ) ;

		// indicates whether hit
		assign	dir_hit_vec20_c6 =  dc_dir_vec20_c6 | ic_dir_vec20_c6 ;

		//  hit way in D
		assign  enc_dc_vec20_way_c6[0]  = dc_cam_hit_c6[21] | dc_cam_hit_c6[23] ;
		assign  enc_dc_vec20_way_c6[1]  = dc_cam_hit_c6[22] | dc_cam_hit_c6[23] ;

		//  hit way in I
		assign  enc_ic_vec20_way_c6[0]  = ic_cam_hit_c6[21] | ic_cam_hit_c6[23] ;
		assign  enc_ic_vec20_way_c6[1]  = ic_cam_hit_c6[22] | ic_cam_hit_c6[23] ;


		mux2ds #(2) mux2_c_vec20_way  ( .dout(enc_c_vec20_way_c6[1:0]),
                              .in0(enc_dc_vec20_way_c6[1:0]),
                              .in1(enc_ic_vec20_way_c6[1:0]),
                              .sel0(~ic_dir_vec20_c6),
                              .sel1(ic_dir_vec20_c6)); 


		assign	way_way_vld20_c6[0] = enc_c_vec20_way_c6[0] ;
		assign	way_way_vld20_c6[1] = enc_c_vec20_way_c6[1] ;
		assign	way_way_vld20_c6[2] = dir_hit_vec20_c6 ;
		/***************** END code for generating return pckt. ******************/

	
		/***************** START code for generating return pckt. ******************/
		// indicates whether D
		assign  dc_dir_vec24_c6 = ( dc_cam_hit_c6[24] | dc_cam_hit_c6[25] |
                                dc_cam_hit_c6[26] | dc_cam_hit_c6[27] ) ;

		// indicates whether I
		assign  ic_dir_vec24_c6 = ( ic_cam_hit_c6[24] | ic_cam_hit_c6[25] |
                                ic_cam_hit_c6[26] | ic_cam_hit_c6[27] ) ;

		// indicates whether hit
		assign	dir_hit_vec24_c6 =  dc_dir_vec24_c6 | ic_dir_vec24_c6 ;

		//  hit way in D
		assign  enc_dc_vec24_way_c6[0]  = dc_cam_hit_c6[25] | dc_cam_hit_c6[27] ;
		assign  enc_dc_vec24_way_c6[1]  = dc_cam_hit_c6[26] | dc_cam_hit_c6[27] ;

		//  hit way in I
		assign  enc_ic_vec24_way_c6[0]  = ic_cam_hit_c6[25] | ic_cam_hit_c6[27] ;
		assign  enc_ic_vec24_way_c6[1]  = ic_cam_hit_c6[26] | ic_cam_hit_c6[27] ;


		mux2ds #(2) mux2_c_vec24_way  ( .dout(enc_c_vec24_way_c6[1:0]),
                              .in0(enc_dc_vec24_way_c6[1:0]),
                              .in1(enc_ic_vec24_way_c6[1:0]),
                              .sel0(~ic_dir_vec24_c6),
                              .sel1(ic_dir_vec24_c6)); 


		assign	way_way_vld24_c6[0] = enc_c_vec24_way_c6[0] ;
		assign	way_way_vld24_c6[1] = enc_c_vec24_way_c6[1] ;
		assign	way_way_vld24_c6[2] = dir_hit_vec24_c6 ;
		/***************** END code for generating return pckt. ******************/

	
		/***************** START code for generating return pckt. ******************/
		// indicates whether D
		assign  dc_dir_vec28_c6 = ( dc_cam_hit_c6[28] | dc_cam_hit_c6[29] |
                                dc_cam_hit_c6[30] | dc_cam_hit_c6[31] ) ;

		// indicates whether I
		assign  ic_dir_vec28_c6 = ( ic_cam_hit_c6[28] | ic_cam_hit_c6[29] |
                                ic_cam_hit_c6[30] | ic_cam_hit_c6[31] ) ;

		// indicates whether hit
		assign	dir_hit_vec28_c6 =  dc_dir_vec28_c6 | ic_dir_vec28_c6 ;

		//  hit way in D
		assign  enc_dc_vec28_way_c6[0]  = dc_cam_hit_c6[29] | dc_cam_hit_c6[31] ;
		assign  enc_dc_vec28_way_c6[1]  = dc_cam_hit_c6[30] | dc_cam_hit_c6[31] ;

		//  hit way in I
		assign  enc_ic_vec28_way_c6[0]  = ic_cam_hit_c6[29] | ic_cam_hit_c6[31] ;
		assign  enc_ic_vec28_way_c6[1]  = ic_cam_hit_c6[30] | ic_cam_hit_c6[31] ;


		mux2ds #(2) mux2_c_vec28_way  ( .dout(enc_c_vec28_way_c6[1:0]),
                              .in0(enc_dc_vec28_way_c6[1:0]),
                              .in1(enc_ic_vec28_way_c6[1:0]),
                              .sel0(~ic_dir_vec28_c6),
                              .sel1(ic_dir_vec28_c6)); 


		assign	way_way_vld28_c6[0] = enc_c_vec28_way_c6[0] ;
		assign	way_way_vld28_c6[1] = enc_c_vec28_way_c6[1] ;
		assign	way_way_vld28_c6[2] = dir_hit_vec28_c6 ;
		/***************** END code for generating return pckt. ******************/

	 

		/***************** START code for generating way wayvld00  ******************/
		wire	[2:0]	way_wayvld00_mux1_c6;
		wire	[2:0]	way_wayvld00_mux2_c6;
		wire	[2:0]	way_wayvld00_mux3_c6;

		mux4ds #(3) mux1_way_way_wayvld00_c6  ( .dout(way_wayvld00_mux1_c6[2:0]),
                              	.in0(way_way_vld0_c6[2:0]),
                              	.in1(way_way_vld4_c6[2:0]),
                              	.in2(way_way_vld8_c6[2:0]),
                              	.in3(way_way_vld12_c6[2:0]),
                              	.sel0(sel_mux1_c6[0]),
                              	.sel1(sel_mux1_c6[1]),
                              	.sel2(sel_mux1_c6[2]),
                              	.sel3(sel_mux1_c6[3]));

		mux4ds #(3) mux2_way_way_wayvld00_c6  ( .dout(way_wayvld00_mux2_c6[2:0]),
                                .in0(way_way_vld16_c6[2:0]),
                                .in1(way_way_vld20_c6[2:0]),
                                .in2(way_way_vld24_c6[2:0]),
                                .in3(way_way_vld28_c6[2:0]),
                                .sel0(sel_mux2_c6[0]),
                                .sel1(sel_mux2_c6[1]),
                                .sel2(sel_mux2_c6[2]),
                                .sel3(sel_mux2_c6[3]));

		mux2ds #(3) mux3_way_way_wayvld00_c6  ( .dout(way_wayvld00_mux3_c6[2:0]),
                                .in0(way_wayvld00_mux1_c6[2:0]),
                                .in1(way_wayvld00_mux2_c6[2:0]),
                                .sel0(sel_mux3_c6),
                                .sel1(~sel_mux3_c6));
		/***************** END code for generating way wayvld00  ******************/

		
		/***************** START wire declarations FOR 32-63 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b1 
		wire    dc_dir_vec32_c6;
		wire	dir_hit_vec32_c6 ;
		wire    [1:0]   enc_dc_vec32_way_c6;

		wire    [1:0]   enc_c_vec32_way_c6;
		wire    [2:0]   way_way_vld32_c6 ;
		/***************** START wire declarations FOR 32-63 ******************/

		
		/***************** START wire declarations FOR 32-63 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b1 
		wire    dc_dir_vec36_c6;
		wire	dir_hit_vec36_c6 ;
		wire    [1:0]   enc_dc_vec36_way_c6;

		wire    [1:0]   enc_c_vec36_way_c6;
		wire    [2:0]   way_way_vld36_c6 ;
		/***************** START wire declarations FOR 32-63 ******************/

		
		/***************** START wire declarations FOR 32-63 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b1 
		wire    dc_dir_vec40_c6;
		wire	dir_hit_vec40_c6 ;
		wire    [1:0]   enc_dc_vec40_way_c6;

		wire    [1:0]   enc_c_vec40_way_c6;
		wire    [2:0]   way_way_vld40_c6 ;
		/***************** START wire declarations FOR 32-63 ******************/

		
		/***************** START wire declarations FOR 32-63 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b1 
		wire    dc_dir_vec44_c6;
		wire	dir_hit_vec44_c6 ;
		wire    [1:0]   enc_dc_vec44_way_c6;

		wire    [1:0]   enc_c_vec44_way_c6;
		wire    [2:0]   way_way_vld44_c6 ;
		/***************** START wire declarations FOR 32-63 ******************/

		
		/***************** START wire declarations FOR 32-63 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b1 
		wire    dc_dir_vec48_c6;
		wire	dir_hit_vec48_c6 ;
		wire    [1:0]   enc_dc_vec48_way_c6;

		wire    [1:0]   enc_c_vec48_way_c6;
		wire    [2:0]   way_way_vld48_c6 ;
		/***************** START wire declarations FOR 32-63 ******************/

		
		/***************** START wire declarations FOR 32-63 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b1 
		wire    dc_dir_vec52_c6;
		wire	dir_hit_vec52_c6 ;
		wire    [1:0]   enc_dc_vec52_way_c6;

		wire    [1:0]   enc_c_vec52_way_c6;
		wire    [2:0]   way_way_vld52_c6 ;
		/***************** START wire declarations FOR 32-63 ******************/

		
		/***************** START wire declarations FOR 32-63 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b1 
		wire    dc_dir_vec56_c6;
		wire	dir_hit_vec56_c6 ;
		wire    [1:0]   enc_dc_vec56_way_c6;

		wire    [1:0]   enc_c_vec56_way_c6;
		wire    [2:0]   way_way_vld56_c6 ;
		/***************** START wire declarations FOR 32-63 ******************/

		
		/***************** START wire declarations FOR 32-63 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b1 
		wire    dc_dir_vec60_c6;
		wire	dir_hit_vec60_c6 ;
		wire    [1:0]   enc_dc_vec60_way_c6;

		wire    [1:0]   enc_c_vec60_way_c6;
		wire    [2:0]   way_way_vld60_c6 ;
		/***************** START wire declarations FOR 32-63 ******************/

		
		/***************** START code for generating return pckt. ******************/
		// indicates whether D
                assign  dc_dir_vec32_c6 = ( dc_cam_hit_c6[32] | dc_cam_hit_c6[33] |
                                dc_cam_hit_c6[34] | dc_cam_hit_c6[35] ) ;


		// hit way in D
                assign  enc_dc_vec32_way_c6[0]  = dc_cam_hit_c6[33] | dc_cam_hit_c6[35] ; 
                assign  enc_dc_vec32_way_c6[1]  = dc_cam_hit_c6[34] | dc_cam_hit_c6[35] ; 

		assign	dir_hit_vec32_c6 =  dc_dir_vec32_c6 ;

		assign	enc_c_vec32_way_c6[1:0] = enc_dc_vec32_way_c6[1:0] ;

                assign  way_way_vld32_c6[0] = enc_c_vec32_way_c6[0] ;
                assign  way_way_vld32_c6[1] = enc_c_vec32_way_c6[1] ;
		assign  way_way_vld32_c6[2] = dir_hit_vec32_c6 ;

		/***************** END code for generating return pckt. ******************/
	
		/***************** START code for generating return pckt. ******************/
		// indicates whether D
                assign  dc_dir_vec36_c6 = ( dc_cam_hit_c6[36] | dc_cam_hit_c6[37] |
                                dc_cam_hit_c6[38] | dc_cam_hit_c6[39] ) ;


		// hit way in D
                assign  enc_dc_vec36_way_c6[0]  = dc_cam_hit_c6[37] | dc_cam_hit_c6[39] ; 
                assign  enc_dc_vec36_way_c6[1]  = dc_cam_hit_c6[38] | dc_cam_hit_c6[39] ; 

		assign	dir_hit_vec36_c6 =  dc_dir_vec36_c6 ;

		assign	enc_c_vec36_way_c6[1:0] = enc_dc_vec36_way_c6[1:0] ;

                assign  way_way_vld36_c6[0] = enc_c_vec36_way_c6[0] ;
                assign  way_way_vld36_c6[1] = enc_c_vec36_way_c6[1] ;
		assign  way_way_vld36_c6[2] = dir_hit_vec36_c6 ;

		/***************** END code for generating return pckt. ******************/
	
		/***************** START code for generating return pckt. ******************/
		// indicates whether D
                assign  dc_dir_vec40_c6 = ( dc_cam_hit_c6[40] | dc_cam_hit_c6[41] |
                                dc_cam_hit_c6[42] | dc_cam_hit_c6[43] ) ;


		// hit way in D
                assign  enc_dc_vec40_way_c6[0]  = dc_cam_hit_c6[41] | dc_cam_hit_c6[43] ; 
                assign  enc_dc_vec40_way_c6[1]  = dc_cam_hit_c6[42] | dc_cam_hit_c6[43] ; 

		assign	dir_hit_vec40_c6 =  dc_dir_vec40_c6 ;

		assign	enc_c_vec40_way_c6[1:0] = enc_dc_vec40_way_c6[1:0] ;

                assign  way_way_vld40_c6[0] = enc_c_vec40_way_c6[0] ;
                assign  way_way_vld40_c6[1] = enc_c_vec40_way_c6[1] ;
		assign  way_way_vld40_c6[2] = dir_hit_vec40_c6 ;

		/***************** END code for generating return pckt. ******************/
	
		/***************** START code for generating return pckt. ******************/
		// indicates whether D
                assign  dc_dir_vec44_c6 = ( dc_cam_hit_c6[44] | dc_cam_hit_c6[45] |
                                dc_cam_hit_c6[46] | dc_cam_hit_c6[47] ) ;


		// hit way in D
                assign  enc_dc_vec44_way_c6[0]  = dc_cam_hit_c6[45] | dc_cam_hit_c6[47] ; 
                assign  enc_dc_vec44_way_c6[1]  = dc_cam_hit_c6[46] | dc_cam_hit_c6[47] ; 

		assign	dir_hit_vec44_c6 =  dc_dir_vec44_c6 ;

		assign	enc_c_vec44_way_c6[1:0] = enc_dc_vec44_way_c6[1:0] ;

                assign  way_way_vld44_c6[0] = enc_c_vec44_way_c6[0] ;
                assign  way_way_vld44_c6[1] = enc_c_vec44_way_c6[1] ;
		assign  way_way_vld44_c6[2] = dir_hit_vec44_c6 ;

		/***************** END code for generating return pckt. ******************/
	
		/***************** START code for generating return pckt. ******************/
		// indicates whether D
                assign  dc_dir_vec48_c6 = ( dc_cam_hit_c6[48] | dc_cam_hit_c6[49] |
                                dc_cam_hit_c6[50] | dc_cam_hit_c6[51] ) ;


		// hit way in D
                assign  enc_dc_vec48_way_c6[0]  = dc_cam_hit_c6[49] | dc_cam_hit_c6[51] ; 
                assign  enc_dc_vec48_way_c6[1]  = dc_cam_hit_c6[50] | dc_cam_hit_c6[51] ; 

		assign	dir_hit_vec48_c6 =  dc_dir_vec48_c6 ;

		assign	enc_c_vec48_way_c6[1:0] = enc_dc_vec48_way_c6[1:0] ;

                assign  way_way_vld48_c6[0] = enc_c_vec48_way_c6[0] ;
                assign  way_way_vld48_c6[1] = enc_c_vec48_way_c6[1] ;
		assign  way_way_vld48_c6[2] = dir_hit_vec48_c6 ;

		/***************** END code for generating return pckt. ******************/
	
		/***************** START code for generating return pckt. ******************/
		// indicates whether D
                assign  dc_dir_vec52_c6 = ( dc_cam_hit_c6[52] | dc_cam_hit_c6[53] |
                                dc_cam_hit_c6[54] | dc_cam_hit_c6[55] ) ;


		// hit way in D
                assign  enc_dc_vec52_way_c6[0]  = dc_cam_hit_c6[53] | dc_cam_hit_c6[55] ; 
                assign  enc_dc_vec52_way_c6[1]  = dc_cam_hit_c6[54] | dc_cam_hit_c6[55] ; 

		assign	dir_hit_vec52_c6 =  dc_dir_vec52_c6 ;

		assign	enc_c_vec52_way_c6[1:0] = enc_dc_vec52_way_c6[1:0] ;

                assign  way_way_vld52_c6[0] = enc_c_vec52_way_c6[0] ;
                assign  way_way_vld52_c6[1] = enc_c_vec52_way_c6[1] ;
		assign  way_way_vld52_c6[2] = dir_hit_vec52_c6 ;

		/***************** END code for generating return pckt. ******************/
	
		/***************** START code for generating return pckt. ******************/
		// indicates whether D
                assign  dc_dir_vec56_c6 = ( dc_cam_hit_c6[56] | dc_cam_hit_c6[57] |
                                dc_cam_hit_c6[58] | dc_cam_hit_c6[59] ) ;


		// hit way in D
                assign  enc_dc_vec56_way_c6[0]  = dc_cam_hit_c6[57] | dc_cam_hit_c6[59] ; 
                assign  enc_dc_vec56_way_c6[1]  = dc_cam_hit_c6[58] | dc_cam_hit_c6[59] ; 

		assign	dir_hit_vec56_c6 =  dc_dir_vec56_c6 ;

		assign	enc_c_vec56_way_c6[1:0] = enc_dc_vec56_way_c6[1:0] ;

                assign  way_way_vld56_c6[0] = enc_c_vec56_way_c6[0] ;
                assign  way_way_vld56_c6[1] = enc_c_vec56_way_c6[1] ;
		assign  way_way_vld56_c6[2] = dir_hit_vec56_c6 ;

		/***************** END code for generating return pckt. ******************/
	
		/***************** START code for generating return pckt. ******************/
		// indicates whether D
                assign  dc_dir_vec60_c6 = ( dc_cam_hit_c6[60] | dc_cam_hit_c6[61] |
                                dc_cam_hit_c6[62] | dc_cam_hit_c6[63] ) ;


		// hit way in D
                assign  enc_dc_vec60_way_c6[0]  = dc_cam_hit_c6[61] | dc_cam_hit_c6[63] ; 
                assign  enc_dc_vec60_way_c6[1]  = dc_cam_hit_c6[62] | dc_cam_hit_c6[63] ; 

		assign	dir_hit_vec60_c6 =  dc_dir_vec60_c6 ;

		assign	enc_c_vec60_way_c6[1:0] = enc_dc_vec60_way_c6[1:0] ;

                assign  way_way_vld60_c6[0] = enc_c_vec60_way_c6[0] ;
                assign  way_way_vld60_c6[1] = enc_c_vec60_way_c6[1] ;
		assign  way_way_vld60_c6[2] = dir_hit_vec60_c6 ;

		/***************** END code for generating return pckt. ******************/
	

                wire    [2:0]   way_wayvld01_mux1_c6;
                wire    [2:0]   way_wayvld01_mux2_c6;
                wire    [2:0]   way_wayvld01_mux3_c6;

                mux4ds #(3) mux1_way_way_wayvld01_c6  ( .dout(way_wayvld01_mux1_c6[2:0]),
                                .in0(way_way_vld32_c6[2:0]),
                                .in1(way_way_vld36_c6[2:0]),
                                .in2(way_way_vld40_c6[2:0]),
                                .in3(way_way_vld44_c6[2:0]),
                                .sel0(sel_mux1_c6[0]),
                                .sel1(sel_mux1_c6[1]),
                                .sel2(sel_mux1_c6[2]),
                                .sel3(sel_mux1_c6[3]));

                mux4ds #(3) mux2_way_way_wayvld01_c6  ( .dout(way_wayvld01_mux2_c6[2:0]),
                                .in0(way_way_vld48_c6[2:0]),
                                .in1(way_way_vld52_c6[2:0]),
                                .in2(way_way_vld56_c6[2:0]),
                                .in3(way_way_vld60_c6[2:0]),
                                .sel0(sel_mux2_c6[0]),
                                .sel1(sel_mux2_c6[1]),
                                .sel2(sel_mux2_c6[2]),
                                .sel3(sel_mux2_c6[3]));

                mux2ds #(3) mux3_way_way_wayvld01_c6  ( .dout(way_wayvld01_mux3_c6[2:0]),
                                .in0(way_wayvld01_mux1_c6[2:0]),
                                .in1(way_wayvld01_mux2_c6[2:0]),
                                .sel0(sel_mux3_c6),
                                .sel1(~sel_mux3_c6));

                
		/***************** START wire declarations FOR 64-96 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b2 
		wire    dc_dir_vec64_c6;
		wire    ic_dir_vec64_c6;
		wire	dir_hit_vec64_c6 ;
		wire    [1:0]   enc_dc_vec64_way_c6;
		wire    [1:0]   enc_ic_vec64_way_c6;

		wire    [1:0]   enc_c_vec64_way_c6;

		wire    [2:0]   way_way_vld64_c6 ;
		/***************** END wire declarations FOR 64-96 ******************/
		
		/***************** START wire declarations FOR 64-96 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b2 
		wire    dc_dir_vec68_c6;
		wire    ic_dir_vec68_c6;
		wire	dir_hit_vec68_c6 ;
		wire    [1:0]   enc_dc_vec68_way_c6;
		wire    [1:0]   enc_ic_vec68_way_c6;

		wire    [1:0]   enc_c_vec68_way_c6;

		wire    [2:0]   way_way_vld68_c6 ;
		/***************** END wire declarations FOR 64-96 ******************/
		
		/***************** START wire declarations FOR 64-96 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b2 
		wire    dc_dir_vec72_c6;
		wire    ic_dir_vec72_c6;
		wire	dir_hit_vec72_c6 ;
		wire    [1:0]   enc_dc_vec72_way_c6;
		wire    [1:0]   enc_ic_vec72_way_c6;

		wire    [1:0]   enc_c_vec72_way_c6;

		wire    [2:0]   way_way_vld72_c6 ;
		/***************** END wire declarations FOR 64-96 ******************/
		
		/***************** START wire declarations FOR 64-96 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b2 
		wire    dc_dir_vec76_c6;
		wire    ic_dir_vec76_c6;
		wire	dir_hit_vec76_c6 ;
		wire    [1:0]   enc_dc_vec76_way_c6;
		wire    [1:0]   enc_ic_vec76_way_c6;

		wire    [1:0]   enc_c_vec76_way_c6;

		wire    [2:0]   way_way_vld76_c6 ;
		/***************** END wire declarations FOR 64-96 ******************/
		
		/***************** START wire declarations FOR 64-96 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b2 
		wire    dc_dir_vec80_c6;
		wire    ic_dir_vec80_c6;
		wire	dir_hit_vec80_c6 ;
		wire    [1:0]   enc_dc_vec80_way_c6;
		wire    [1:0]   enc_ic_vec80_way_c6;

		wire    [1:0]   enc_c_vec80_way_c6;

		wire    [2:0]   way_way_vld80_c6 ;
		/***************** END wire declarations FOR 64-96 ******************/
		
		/***************** START wire declarations FOR 64-96 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b2 
		wire    dc_dir_vec84_c6;
		wire    ic_dir_vec84_c6;
		wire	dir_hit_vec84_c6 ;
		wire    [1:0]   enc_dc_vec84_way_c6;
		wire    [1:0]   enc_ic_vec84_way_c6;

		wire    [1:0]   enc_c_vec84_way_c6;

		wire    [2:0]   way_way_vld84_c6 ;
		/***************** END wire declarations FOR 64-96 ******************/
		
		/***************** START wire declarations FOR 64-96 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b2 
		wire    dc_dir_vec88_c6;
		wire    ic_dir_vec88_c6;
		wire	dir_hit_vec88_c6 ;
		wire    [1:0]   enc_dc_vec88_way_c6;
		wire    [1:0]   enc_ic_vec88_way_c6;

		wire    [1:0]   enc_c_vec88_way_c6;

		wire    [2:0]   way_way_vld88_c6 ;
		/***************** END wire declarations FOR 64-96 ******************/
		
		/***************** START wire declarations FOR 64-96 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b2 
		wire    dc_dir_vec92_c6;
		wire    ic_dir_vec92_c6;
		wire	dir_hit_vec92_c6 ;
		wire    [1:0]   enc_dc_vec92_way_c6;
		wire    [1:0]   enc_ic_vec92_way_c6;

		wire    [1:0]   enc_c_vec92_way_c6;

		wire    [2:0]   way_way_vld92_c6 ;
		/***************** END wire declarations FOR 64-96 ******************/
		
		/***************** START code for generating return pckt. ******************/
		// indicates whether D
                assign  dc_dir_vec64_c6 = ( dc_cam_hit_c6[64] | dc_cam_hit_c6[65] |
                                dc_cam_hit_c6[66] | dc_cam_hit_c6[67] ) ;

		// indicates whether I hit
                assign  ic_dir_vec64_c6 = ( ic_cam_hit_c6[64] | ic_cam_hit_c6[65] |
                                ic_cam_hit_c6[66] | ic_cam_hit_c6[67] ) ;

		// indicates whether hit
		assign	dir_hit_vec64_c6 =  dc_dir_vec64_c6 | ic_dir_vec64_c6 ;

		// D hit way
                assign  enc_dc_vec64_way_c6[0]  = dc_cam_hit_c6[65] | dc_cam_hit_c6[67] ; 
                assign  enc_dc_vec64_way_c6[1]  = dc_cam_hit_c6[66] | dc_cam_hit_c6[67] ; 

		// I hit way
                assign  enc_ic_vec64_way_c6[0]  = ic_cam_hit_c6[65] | ic_cam_hit_c6[67] ; 
                assign  enc_ic_vec64_way_c6[1]  = ic_cam_hit_c6[66] | ic_cam_hit_c6[67] ; 


                mux2ds #(2) mux2_c_vec64_way  ( .dout(enc_c_vec64_way_c6[1:0]),
                              .in0(enc_dc_vec64_way_c6[1:0]),
                              .in1(enc_ic_vec64_way_c6[1:0]),
                              .sel0(~ic_dir_vec64_c6),
                              .sel1(ic_dir_vec64_c6)); 

                assign  way_way_vld64_c6[0] = enc_c_vec64_way_c6[0] ;
                assign  way_way_vld64_c6[1] = enc_c_vec64_way_c6[1] ;
		assign  way_way_vld64_c6[2] = dir_hit_vec64_c6 ;
		/***************** END code for generating return pckt. ******************/
        
		/***************** START code for generating return pckt. ******************/
		// indicates whether D
                assign  dc_dir_vec68_c6 = ( dc_cam_hit_c6[68] | dc_cam_hit_c6[69] |
                                dc_cam_hit_c6[70] | dc_cam_hit_c6[71] ) ;

		// indicates whether I hit
                assign  ic_dir_vec68_c6 = ( ic_cam_hit_c6[68] | ic_cam_hit_c6[69] |
                                ic_cam_hit_c6[70] | ic_cam_hit_c6[71] ) ;

		// indicates whether hit
		assign	dir_hit_vec68_c6 =  dc_dir_vec68_c6 | ic_dir_vec68_c6 ;

		// D hit way
                assign  enc_dc_vec68_way_c6[0]  = dc_cam_hit_c6[69] | dc_cam_hit_c6[71] ; 
                assign  enc_dc_vec68_way_c6[1]  = dc_cam_hit_c6[70] | dc_cam_hit_c6[71] ; 

		// I hit way
                assign  enc_ic_vec68_way_c6[0]  = ic_cam_hit_c6[69] | ic_cam_hit_c6[71] ; 
                assign  enc_ic_vec68_way_c6[1]  = ic_cam_hit_c6[70] | ic_cam_hit_c6[71] ; 


                mux2ds #(2) mux2_c_vec68_way  ( .dout(enc_c_vec68_way_c6[1:0]),
                              .in0(enc_dc_vec68_way_c6[1:0]),
                              .in1(enc_ic_vec68_way_c6[1:0]),
                              .sel0(~ic_dir_vec68_c6),
                              .sel1(ic_dir_vec68_c6)); 

                assign  way_way_vld68_c6[0] = enc_c_vec68_way_c6[0] ;
                assign  way_way_vld68_c6[1] = enc_c_vec68_way_c6[1] ;
		assign  way_way_vld68_c6[2] = dir_hit_vec68_c6 ;
		/***************** END code for generating return pckt. ******************/
        
		/***************** START code for generating return pckt. ******************/
		// indicates whether D
                assign  dc_dir_vec72_c6 = ( dc_cam_hit_c6[72] | dc_cam_hit_c6[73] |
                                dc_cam_hit_c6[74] | dc_cam_hit_c6[75] ) ;

		// indicates whether I hit
                assign  ic_dir_vec72_c6 = ( ic_cam_hit_c6[72] | ic_cam_hit_c6[73] |
                                ic_cam_hit_c6[74] | ic_cam_hit_c6[75] ) ;

		// indicates whether hit
		assign	dir_hit_vec72_c6 =  dc_dir_vec72_c6 | ic_dir_vec72_c6 ;

		// D hit way
                assign  enc_dc_vec72_way_c6[0]  = dc_cam_hit_c6[73] | dc_cam_hit_c6[75] ; 
                assign  enc_dc_vec72_way_c6[1]  = dc_cam_hit_c6[74] | dc_cam_hit_c6[75] ; 

		// I hit way
                assign  enc_ic_vec72_way_c6[0]  = ic_cam_hit_c6[73] | ic_cam_hit_c6[75] ; 
                assign  enc_ic_vec72_way_c6[1]  = ic_cam_hit_c6[74] | ic_cam_hit_c6[75] ; 


                mux2ds #(2) mux2_c_vec72_way  ( .dout(enc_c_vec72_way_c6[1:0]),
                              .in0(enc_dc_vec72_way_c6[1:0]),
                              .in1(enc_ic_vec72_way_c6[1:0]),
                              .sel0(~ic_dir_vec72_c6),
                              .sel1(ic_dir_vec72_c6)); 

                assign  way_way_vld72_c6[0] = enc_c_vec72_way_c6[0] ;
                assign  way_way_vld72_c6[1] = enc_c_vec72_way_c6[1] ;
		assign  way_way_vld72_c6[2] = dir_hit_vec72_c6 ;
		/***************** END code for generating return pckt. ******************/
        
		/***************** START code for generating return pckt. ******************/
		// indicates whether D
                assign  dc_dir_vec76_c6 = ( dc_cam_hit_c6[76] | dc_cam_hit_c6[77] |
                                dc_cam_hit_c6[78] | dc_cam_hit_c6[79] ) ;

		// indicates whether I hit
                assign  ic_dir_vec76_c6 = ( ic_cam_hit_c6[76] | ic_cam_hit_c6[77] |
                                ic_cam_hit_c6[78] | ic_cam_hit_c6[79] ) ;

		// indicates whether hit
		assign	dir_hit_vec76_c6 =  dc_dir_vec76_c6 | ic_dir_vec76_c6 ;

		// D hit way
                assign  enc_dc_vec76_way_c6[0]  = dc_cam_hit_c6[77] | dc_cam_hit_c6[79] ; 
                assign  enc_dc_vec76_way_c6[1]  = dc_cam_hit_c6[78] | dc_cam_hit_c6[79] ; 

		// I hit way
                assign  enc_ic_vec76_way_c6[0]  = ic_cam_hit_c6[77] | ic_cam_hit_c6[79] ; 
                assign  enc_ic_vec76_way_c6[1]  = ic_cam_hit_c6[78] | ic_cam_hit_c6[79] ; 


                mux2ds #(2) mux2_c_vec76_way  ( .dout(enc_c_vec76_way_c6[1:0]),
                              .in0(enc_dc_vec76_way_c6[1:0]),
                              .in1(enc_ic_vec76_way_c6[1:0]),
                              .sel0(~ic_dir_vec76_c6),
                              .sel1(ic_dir_vec76_c6)); 

                assign  way_way_vld76_c6[0] = enc_c_vec76_way_c6[0] ;
                assign  way_way_vld76_c6[1] = enc_c_vec76_way_c6[1] ;
		assign  way_way_vld76_c6[2] = dir_hit_vec76_c6 ;
		/***************** END code for generating return pckt. ******************/
        
		/***************** START code for generating return pckt. ******************/
		// indicates whether D
                assign  dc_dir_vec80_c6 = ( dc_cam_hit_c6[80] | dc_cam_hit_c6[81] |
                                dc_cam_hit_c6[82] | dc_cam_hit_c6[83] ) ;

		// indicates whether I hit
                assign  ic_dir_vec80_c6 = ( ic_cam_hit_c6[80] | ic_cam_hit_c6[81] |
                                ic_cam_hit_c6[82] | ic_cam_hit_c6[83] ) ;

		// indicates whether hit
		assign	dir_hit_vec80_c6 =  dc_dir_vec80_c6 | ic_dir_vec80_c6 ;

		// D hit way
                assign  enc_dc_vec80_way_c6[0]  = dc_cam_hit_c6[81] | dc_cam_hit_c6[83] ; 
                assign  enc_dc_vec80_way_c6[1]  = dc_cam_hit_c6[82] | dc_cam_hit_c6[83] ; 

		// I hit way
                assign  enc_ic_vec80_way_c6[0]  = ic_cam_hit_c6[81] | ic_cam_hit_c6[83] ; 
                assign  enc_ic_vec80_way_c6[1]  = ic_cam_hit_c6[82] | ic_cam_hit_c6[83] ; 


                mux2ds #(2) mux2_c_vec80_way  ( .dout(enc_c_vec80_way_c6[1:0]),
                              .in0(enc_dc_vec80_way_c6[1:0]),
                              .in1(enc_ic_vec80_way_c6[1:0]),
                              .sel0(~ic_dir_vec80_c6),
                              .sel1(ic_dir_vec80_c6)); 

                assign  way_way_vld80_c6[0] = enc_c_vec80_way_c6[0] ;
                assign  way_way_vld80_c6[1] = enc_c_vec80_way_c6[1] ;
		assign  way_way_vld80_c6[2] = dir_hit_vec80_c6 ;
		/***************** END code for generating return pckt. ******************/
        
		/***************** START code for generating return pckt. ******************/
		// indicates whether D
                assign  dc_dir_vec84_c6 = ( dc_cam_hit_c6[84] | dc_cam_hit_c6[85] |
                                dc_cam_hit_c6[86] | dc_cam_hit_c6[87] ) ;

		// indicates whether I hit
                assign  ic_dir_vec84_c6 = ( ic_cam_hit_c6[84] | ic_cam_hit_c6[85] |
                                ic_cam_hit_c6[86] | ic_cam_hit_c6[87] ) ;

		// indicates whether hit
		assign	dir_hit_vec84_c6 =  dc_dir_vec84_c6 | ic_dir_vec84_c6 ;

		// D hit way
                assign  enc_dc_vec84_way_c6[0]  = dc_cam_hit_c6[85] | dc_cam_hit_c6[87] ; 
                assign  enc_dc_vec84_way_c6[1]  = dc_cam_hit_c6[86] | dc_cam_hit_c6[87] ; 

		// I hit way
                assign  enc_ic_vec84_way_c6[0]  = ic_cam_hit_c6[85] | ic_cam_hit_c6[87] ; 
                assign  enc_ic_vec84_way_c6[1]  = ic_cam_hit_c6[86] | ic_cam_hit_c6[87] ; 


                mux2ds #(2) mux2_c_vec84_way  ( .dout(enc_c_vec84_way_c6[1:0]),
                              .in0(enc_dc_vec84_way_c6[1:0]),
                              .in1(enc_ic_vec84_way_c6[1:0]),
                              .sel0(~ic_dir_vec84_c6),
                              .sel1(ic_dir_vec84_c6)); 

                assign  way_way_vld84_c6[0] = enc_c_vec84_way_c6[0] ;
                assign  way_way_vld84_c6[1] = enc_c_vec84_way_c6[1] ;
		assign  way_way_vld84_c6[2] = dir_hit_vec84_c6 ;
		/***************** END code for generating return pckt. ******************/
        
		/***************** START code for generating return pckt. ******************/
		// indicates whether D
                assign  dc_dir_vec88_c6 = ( dc_cam_hit_c6[88] | dc_cam_hit_c6[89] |
                                dc_cam_hit_c6[90] | dc_cam_hit_c6[91] ) ;

		// indicates whether I hit
                assign  ic_dir_vec88_c6 = ( ic_cam_hit_c6[88] | ic_cam_hit_c6[89] |
                                ic_cam_hit_c6[90] | ic_cam_hit_c6[91] ) ;

		// indicates whether hit
		assign	dir_hit_vec88_c6 =  dc_dir_vec88_c6 | ic_dir_vec88_c6 ;

		// D hit way
                assign  enc_dc_vec88_way_c6[0]  = dc_cam_hit_c6[89] | dc_cam_hit_c6[91] ; 
                assign  enc_dc_vec88_way_c6[1]  = dc_cam_hit_c6[90] | dc_cam_hit_c6[91] ; 

		// I hit way
                assign  enc_ic_vec88_way_c6[0]  = ic_cam_hit_c6[89] | ic_cam_hit_c6[91] ; 
                assign  enc_ic_vec88_way_c6[1]  = ic_cam_hit_c6[90] | ic_cam_hit_c6[91] ; 


                mux2ds #(2) mux2_c_vec88_way  ( .dout(enc_c_vec88_way_c6[1:0]),
                              .in0(enc_dc_vec88_way_c6[1:0]),
                              .in1(enc_ic_vec88_way_c6[1:0]),
                              .sel0(~ic_dir_vec88_c6),
                              .sel1(ic_dir_vec88_c6)); 

                assign  way_way_vld88_c6[0] = enc_c_vec88_way_c6[0] ;
                assign  way_way_vld88_c6[1] = enc_c_vec88_way_c6[1] ;
		assign  way_way_vld88_c6[2] = dir_hit_vec88_c6 ;
		/***************** END code for generating return pckt. ******************/
        
		/***************** START code for generating return pckt. ******************/
		// indicates whether D
                assign  dc_dir_vec92_c6 = ( dc_cam_hit_c6[92] | dc_cam_hit_c6[93] |
                                dc_cam_hit_c6[94] | dc_cam_hit_c6[95] ) ;

		// indicates whether I hit
                assign  ic_dir_vec92_c6 = ( ic_cam_hit_c6[92] | ic_cam_hit_c6[93] |
                                ic_cam_hit_c6[94] | ic_cam_hit_c6[95] ) ;

		// indicates whether hit
		assign	dir_hit_vec92_c6 =  dc_dir_vec92_c6 | ic_dir_vec92_c6 ;

		// D hit way
                assign  enc_dc_vec92_way_c6[0]  = dc_cam_hit_c6[93] | dc_cam_hit_c6[95] ; 
                assign  enc_dc_vec92_way_c6[1]  = dc_cam_hit_c6[94] | dc_cam_hit_c6[95] ; 

		// I hit way
                assign  enc_ic_vec92_way_c6[0]  = ic_cam_hit_c6[93] | ic_cam_hit_c6[95] ; 
                assign  enc_ic_vec92_way_c6[1]  = ic_cam_hit_c6[94] | ic_cam_hit_c6[95] ; 


                mux2ds #(2) mux2_c_vec92_way  ( .dout(enc_c_vec92_way_c6[1:0]),
                              .in0(enc_dc_vec92_way_c6[1:0]),
                              .in1(enc_ic_vec92_way_c6[1:0]),
                              .sel0(~ic_dir_vec92_c6),
                              .sel1(ic_dir_vec92_c6)); 

                assign  way_way_vld92_c6[0] = enc_c_vec92_way_c6[0] ;
                assign  way_way_vld92_c6[1] = enc_c_vec92_way_c6[1] ;
		assign  way_way_vld92_c6[2] = dir_hit_vec92_c6 ;
		/***************** END code for generating return pckt. ******************/
        

                wire    [2:0]   way_wayvld10_mux1_c6;
                wire    [2:0]   way_wayvld10_mux2_c6;
                wire    [2:0]   way_wayvld10_mux3_c6;

                mux4ds #(3) mux1_way_way_wayvld10_c6  ( .dout(way_wayvld10_mux1_c6[2:0]),
                                .in0(way_way_vld64_c6[2:0]),
                                .in1(way_way_vld68_c6[2:0]),
                                .in2(way_way_vld72_c6[2:0]),
                                .in3(way_way_vld76_c6[2:0]),
                                .sel0(sel_mux1_c6[0]),
                                .sel1(sel_mux1_c6[1]),
                                .sel2(sel_mux1_c6[2]),
                                .sel3(sel_mux1_c6[3]));

                mux4ds #(3) mux2_way_way_wayvld10_c6  ( .dout(way_wayvld10_mux2_c6[2:0]),
                                .in0(way_way_vld80_c6[2:0]),
                                .in1(way_way_vld84_c6[2:0]),
                                .in2(way_way_vld88_c6[2:0]),
                                .in3(way_way_vld92_c6[2:0]),
                                .sel0(sel_mux2_c6[0]),
                                .sel1(sel_mux2_c6[1]),
                                .sel2(sel_mux2_c6[2]),
                                .sel3(sel_mux2_c6[3]));

                mux2ds #(3) mux3_way_way_wayvld10_c6  ( .dout(way_wayvld10_mux3_c6[2:0]),
                                .in0(way_wayvld10_mux1_c6[2:0]),
                                .in1(way_wayvld10_mux2_c6[2:0]),
                                .sel0(sel_mux3_c6),
                                .sel1(~sel_mux3_c6));

                
		/***************** START wire declarations FOR 96-128 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b1 
		wire    dc_dir_vec96_c6;
		wire	dir_hit_vec96_c6 ;
		wire    [1:0]   enc_dc_vec96_way_c6;

		wire    [1:0]   enc_c_vec96_way_c6;
		wire    [2:0]   way_way_vld96_c6 ;
		/***************** END wire declarations FOR 96-128 ******************/
		
		/***************** START wire declarations FOR 96-128 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b1 
		wire    dc_dir_vec100_c6;
		wire	dir_hit_vec100_c6 ;
		wire    [1:0]   enc_dc_vec100_way_c6;

		wire    [1:0]   enc_c_vec100_way_c6;
		wire    [2:0]   way_way_vld100_c6 ;
		/***************** END wire declarations FOR 96-128 ******************/
		
		/***************** START wire declarations FOR 96-128 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b1 
		wire    dc_dir_vec104_c6;
		wire	dir_hit_vec104_c6 ;
		wire    [1:0]   enc_dc_vec104_way_c6;

		wire    [1:0]   enc_c_vec104_way_c6;
		wire    [2:0]   way_way_vld104_c6 ;
		/***************** END wire declarations FOR 96-128 ******************/
		
		/***************** START wire declarations FOR 96-128 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b1 
		wire    dc_dir_vec108_c6;
		wire	dir_hit_vec108_c6 ;
		wire    [1:0]   enc_dc_vec108_way_c6;

		wire    [1:0]   enc_c_vec108_way_c6;
		wire    [2:0]   way_way_vld108_c6 ;
		/***************** END wire declarations FOR 96-128 ******************/
		
		/***************** START wire declarations FOR 96-128 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b1 
		wire    dc_dir_vec112_c6;
		wire	dir_hit_vec112_c6 ;
		wire    [1:0]   enc_dc_vec112_way_c6;

		wire    [1:0]   enc_c_vec112_way_c6;
		wire    [2:0]   way_way_vld112_c6 ;
		/***************** END wire declarations FOR 96-128 ******************/
		
		/***************** START wire declarations FOR 96-128 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b1 
		wire    dc_dir_vec116_c6;
		wire	dir_hit_vec116_c6 ;
		wire    [1:0]   enc_dc_vec116_way_c6;

		wire    [1:0]   enc_c_vec116_way_c6;
		wire    [2:0]   way_way_vld116_c6 ;
		/***************** END wire declarations FOR 96-128 ******************/
		
		/***************** START wire declarations FOR 96-128 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b1 
		wire    dc_dir_vec120_c6;
		wire	dir_hit_vec120_c6 ;
		wire    [1:0]   enc_dc_vec120_way_c6;

		wire    [1:0]   enc_c_vec120_way_c6;
		wire    [2:0]   way_way_vld120_c6 ;
		/***************** END wire declarations FOR 96-128 ******************/
		
		/***************** START wire declarations FOR 96-128 ******************/
		// Variables needed for hit  Addr<5:4> = 2'b1 
		wire    dc_dir_vec124_c6;
		wire	dir_hit_vec124_c6 ;
		wire    [1:0]   enc_dc_vec124_way_c6;

		wire    [1:0]   enc_c_vec124_way_c6;
		wire    [2:0]   way_way_vld124_c6 ;
		/***************** END wire declarations FOR 96-128 ******************/
		
		/***************** START code for generating return pckt. ******************/
		// indicates whether D hit.
                assign  dc_dir_vec96_c6 = ( dc_cam_hit_c6[96] | dc_cam_hit_c6[97] |
                                dc_cam_hit_c6[98] | dc_cam_hit_c6[99] ) ;

		// D hit way

		assign	dir_hit_vec96_c6 =  dc_dir_vec96_c6 ;

		//  hit way
                assign  enc_dc_vec96_way_c6[0]  = dc_cam_hit_c6[97] | dc_cam_hit_c6[99] ; 
                assign  enc_dc_vec96_way_c6[1]  = dc_cam_hit_c6[98] | dc_cam_hit_c6[99] ; 


                assign	enc_c_vec96_way_c6[1:0] = enc_dc_vec96_way_c6[1:0] ;

                assign  way_way_vld96_c6[0] = enc_c_vec96_way_c6[0] ;
                assign  way_way_vld96_c6[1] = enc_c_vec96_way_c6[1] ;
		assign  way_way_vld96_c6[2] = dir_hit_vec96_c6 ;
		/***************** END code for generating return pckt. ******************/
        
		/***************** START code for generating return pckt. ******************/
		// indicates whether D hit.
                assign  dc_dir_vec100_c6 = ( dc_cam_hit_c6[100] | dc_cam_hit_c6[101] |
                                dc_cam_hit_c6[102] | dc_cam_hit_c6[103] ) ;

		// D hit way

		assign	dir_hit_vec100_c6 =  dc_dir_vec100_c6 ;

		//  hit way
                assign  enc_dc_vec100_way_c6[0]  = dc_cam_hit_c6[101] | dc_cam_hit_c6[103] ; 
                assign  enc_dc_vec100_way_c6[1]  = dc_cam_hit_c6[102] | dc_cam_hit_c6[103] ; 


                assign	enc_c_vec100_way_c6[1:0] = enc_dc_vec100_way_c6[1:0] ;

                assign  way_way_vld100_c6[0] = enc_c_vec100_way_c6[0] ;
                assign  way_way_vld100_c6[1] = enc_c_vec100_way_c6[1] ;
		assign  way_way_vld100_c6[2] = dir_hit_vec100_c6 ;
		/***************** END code for generating return pckt. ******************/
        
		/***************** START code for generating return pckt. ******************/
		// indicates whether D hit.
                assign  dc_dir_vec104_c6 = ( dc_cam_hit_c6[104] | dc_cam_hit_c6[105] |
                                dc_cam_hit_c6[106] | dc_cam_hit_c6[107] ) ;

		// D hit way

		assign	dir_hit_vec104_c6 =  dc_dir_vec104_c6 ;

		//  hit way
                assign  enc_dc_vec104_way_c6[0]  = dc_cam_hit_c6[105] | dc_cam_hit_c6[107] ; 
                assign  enc_dc_vec104_way_c6[1]  = dc_cam_hit_c6[106] | dc_cam_hit_c6[107] ; 


                assign	enc_c_vec104_way_c6[1:0] = enc_dc_vec104_way_c6[1:0] ;

                assign  way_way_vld104_c6[0] = enc_c_vec104_way_c6[0] ;
                assign  way_way_vld104_c6[1] = enc_c_vec104_way_c6[1] ;
		assign  way_way_vld104_c6[2] = dir_hit_vec104_c6 ;
		/***************** END code for generating return pckt. ******************/
        
		/***************** START code for generating return pckt. ******************/
		// indicates whether D hit.
                assign  dc_dir_vec108_c6 = ( dc_cam_hit_c6[108] | dc_cam_hit_c6[109] |
                                dc_cam_hit_c6[110] | dc_cam_hit_c6[111] ) ;

		// D hit way

		assign	dir_hit_vec108_c6 =  dc_dir_vec108_c6 ;

		//  hit way
                assign  enc_dc_vec108_way_c6[0]  = dc_cam_hit_c6[109] | dc_cam_hit_c6[111] ; 
                assign  enc_dc_vec108_way_c6[1]  = dc_cam_hit_c6[110] | dc_cam_hit_c6[111] ; 


                assign	enc_c_vec108_way_c6[1:0] = enc_dc_vec108_way_c6[1:0] ;

                assign  way_way_vld108_c6[0] = enc_c_vec108_way_c6[0] ;
                assign  way_way_vld108_c6[1] = enc_c_vec108_way_c6[1] ;
		assign  way_way_vld108_c6[2] = dir_hit_vec108_c6 ;
		/***************** END code for generating return pckt. ******************/
        
		/***************** START code for generating return pckt. ******************/
		// indicates whether D hit.
                assign  dc_dir_vec112_c6 = ( dc_cam_hit_c6[112] | dc_cam_hit_c6[113] |
                                dc_cam_hit_c6[114] | dc_cam_hit_c6[115] ) ;

		// D hit way

		assign	dir_hit_vec112_c6 =  dc_dir_vec112_c6 ;

		//  hit way
                assign  enc_dc_vec112_way_c6[0]  = dc_cam_hit_c6[113] | dc_cam_hit_c6[115] ; 
                assign  enc_dc_vec112_way_c6[1]  = dc_cam_hit_c6[114] | dc_cam_hit_c6[115] ; 


                assign	enc_c_vec112_way_c6[1:0] = enc_dc_vec112_way_c6[1:0] ;

                assign  way_way_vld112_c6[0] = enc_c_vec112_way_c6[0] ;
                assign  way_way_vld112_c6[1] = enc_c_vec112_way_c6[1] ;
		assign  way_way_vld112_c6[2] = dir_hit_vec112_c6 ;
		/***************** END code for generating return pckt. ******************/
        
		/***************** START code for generating return pckt. ******************/
		// indicates whether D hit.
                assign  dc_dir_vec116_c6 = ( dc_cam_hit_c6[116] | dc_cam_hit_c6[117] |
                                dc_cam_hit_c6[118] | dc_cam_hit_c6[119] ) ;

		// D hit way

		assign	dir_hit_vec116_c6 =  dc_dir_vec116_c6 ;

		//  hit way
                assign  enc_dc_vec116_way_c6[0]  = dc_cam_hit_c6[117] | dc_cam_hit_c6[119] ; 
                assign  enc_dc_vec116_way_c6[1]  = dc_cam_hit_c6[118] | dc_cam_hit_c6[119] ; 


                assign	enc_c_vec116_way_c6[1:0] = enc_dc_vec116_way_c6[1:0] ;

                assign  way_way_vld116_c6[0] = enc_c_vec116_way_c6[0] ;
                assign  way_way_vld116_c6[1] = enc_c_vec116_way_c6[1] ;
		assign  way_way_vld116_c6[2] = dir_hit_vec116_c6 ;
		/***************** END code for generating return pckt. ******************/
        
		/***************** START code for generating return pckt. ******************/
		// indicates whether D hit.
                assign  dc_dir_vec120_c6 = ( dc_cam_hit_c6[120] | dc_cam_hit_c6[121] |
                                dc_cam_hit_c6[122] | dc_cam_hit_c6[123] ) ;

		// D hit way

		assign	dir_hit_vec120_c6 =  dc_dir_vec120_c6 ;

		//  hit way
                assign  enc_dc_vec120_way_c6[0]  = dc_cam_hit_c6[121] | dc_cam_hit_c6[123] ; 
                assign  enc_dc_vec120_way_c6[1]  = dc_cam_hit_c6[122] | dc_cam_hit_c6[123] ; 


                assign	enc_c_vec120_way_c6[1:0] = enc_dc_vec120_way_c6[1:0] ;

                assign  way_way_vld120_c6[0] = enc_c_vec120_way_c6[0] ;
                assign  way_way_vld120_c6[1] = enc_c_vec120_way_c6[1] ;
		assign  way_way_vld120_c6[2] = dir_hit_vec120_c6 ;
		/***************** END code for generating return pckt. ******************/
        
		/***************** START code for generating return pckt. ******************/
		// indicates whether D hit.
                assign  dc_dir_vec124_c6 = ( dc_cam_hit_c6[124] | dc_cam_hit_c6[125] |
                                dc_cam_hit_c6[126] | dc_cam_hit_c6[127] ) ;

		// D hit way

		assign	dir_hit_vec124_c6 =  dc_dir_vec124_c6 ;

		//  hit way
                assign  enc_dc_vec124_way_c6[0]  = dc_cam_hit_c6[125] | dc_cam_hit_c6[127] ; 
                assign  enc_dc_vec124_way_c6[1]  = dc_cam_hit_c6[126] | dc_cam_hit_c6[127] ; 


                assign	enc_c_vec124_way_c6[1:0] = enc_dc_vec124_way_c6[1:0] ;

                assign  way_way_vld124_c6[0] = enc_c_vec124_way_c6[0] ;
                assign  way_way_vld124_c6[1] = enc_c_vec124_way_c6[1] ;
		assign  way_way_vld124_c6[2] = dir_hit_vec124_c6 ;
		/***************** END code for generating return pckt. ******************/
        

                wire    [2:0]   way_wayvld11_mux1_c6;
                wire    [2:0]   way_wayvld11_mux2_c6;
                wire    [2:0]   way_wayvld11_mux3_c6;

                mux4ds #(3) mux1_way_way_wayvld11_c6  ( .dout(way_wayvld11_mux1_c6[2:0]),
                                .in0(way_way_vld96_c6[2:0]),
                                .in1(way_way_vld100_c6[2:0]),
                                .in2(way_way_vld104_c6[2:0]),
                                .in3(way_way_vld108_c6[2:0]),
                                .sel0(sel_mux1_c6[0]),
                                .sel1(sel_mux1_c6[1]),
                                .sel2(sel_mux1_c6[2]),
                                .sel3(sel_mux1_c6[3]));

                mux4ds #(3) mux2_way_way_wayvld11_c6  ( .dout(way_wayvld11_mux2_c6[2:0]),
                                .in0(way_way_vld112_c6[2:0]),
                                .in1(way_way_vld116_c6[2:0]),
                                .in2(way_way_vld120_c6[2:0]),
                                .in3(way_way_vld124_c6[2:0]),
                                .sel0(sel_mux2_c6[0]),
                                .sel1(sel_mux2_c6[1]),
                                .sel2(sel_mux2_c6[2]),
                                .sel3(sel_mux2_c6[3]));

                mux2ds #(3) mux3_way_way_wayvld11_c6  ( .dout(way_wayvld11_mux3_c6[2:0]),
                                .in0(way_wayvld11_mux1_c6[2:0]),
                                .in1(way_wayvld11_mux2_c6[2:0]),
                                .sel0(sel_mux3_c6),
                                .sel1(~sel_mux3_c6));

                

//*******************************************************************************************
// REQUEST VEC FORMATION
//*******************************************************************************************



assign	dirdp_req_vec_c6[0] = dir_hit_vec0_c6 | dir_hit_vec32_c6 | dir_hit_vec64_c6 | dir_hit_vec96_c6 ;
assign	dirdp_req_vec_c6[1] = dir_hit_vec4_c6 | dir_hit_vec36_c6 | dir_hit_vec68_c6 | dir_hit_vec100_c6 ;
assign	dirdp_req_vec_c6[2] = dir_hit_vec8_c6 | dir_hit_vec40_c6 | dir_hit_vec72_c6 | dir_hit_vec104_c6 ;
assign	dirdp_req_vec_c6[3] = dir_hit_vec12_c6 | dir_hit_vec44_c6 | dir_hit_vec76_c6 | dir_hit_vec108_c6 ;
assign	dirdp_req_vec_c6[4] = dir_hit_vec16_c6 | dir_hit_vec48_c6 | dir_hit_vec80_c6 | dir_hit_vec112_c6 ;
assign	dirdp_req_vec_c6[5] = dir_hit_vec20_c6 | dir_hit_vec52_c6 | dir_hit_vec84_c6 | dir_hit_vec116_c6 ;
assign	dirdp_req_vec_c6[6] = dir_hit_vec24_c6 | dir_hit_vec56_c6 | dir_hit_vec88_c6 | dir_hit_vec120_c6 ;
assign	dirdp_req_vec_c6[7] = dir_hit_vec28_c6 | dir_hit_vec60_c6 | dir_hit_vec92_c6 | dir_hit_vec124_c6 ;

	 
//*******************************************************************************************
// INVALIDATE PACKET FORMATION
//*******************************************************************************************
// 32 bit dir vec.
assign	dirdp_inval_pckt_c6[31:0] = { enc_c_vec28_way_c6, ic_dir_vec28_c6, dc_dir_vec28_c6,
					enc_c_vec24_way_c6, ic_dir_vec24_c6, dc_dir_vec24_c6,
					enc_c_vec20_way_c6, ic_dir_vec20_c6, dc_dir_vec20_c6,
					enc_c_vec16_way_c6, ic_dir_vec16_c6, dc_dir_vec16_c6,
					enc_c_vec12_way_c6, ic_dir_vec12_c6, dc_dir_vec12_c6,
					enc_c_vec8_way_c6, ic_dir_vec8_c6, dc_dir_vec8_c6,
					enc_c_vec4_way_c6, ic_dir_vec4_c6, dc_dir_vec4_c6,
					enc_c_vec0_way_c6, ic_dir_vec0_c6, dc_dir_vec0_c6 
				   } ; 
	 
// 32 bit dir vec.
assign	dirdp_inval_pckt_c6[55:32] = { enc_c_vec60_way_c6,  dc_dir_vec60_c6,
					enc_c_vec56_way_c6, dc_dir_vec56_c6,
					enc_c_vec52_way_c6, dc_dir_vec52_c6,
					enc_c_vec48_way_c6, dc_dir_vec48_c6,
					enc_c_vec44_way_c6, dc_dir_vec44_c6,
					enc_c_vec40_way_c6, dc_dir_vec40_c6,
					enc_c_vec36_way_c6, dc_dir_vec36_c6,
					enc_c_vec32_way_c6, dc_dir_vec32_c6 
				   } ;
		 
assign	dirdp_inval_pckt_c6[87:56] = { enc_c_vec92_way_c6, ic_dir_vec92_c6, dc_dir_vec92_c6,
					enc_c_vec88_way_c6, ic_dir_vec88_c6, dc_dir_vec88_c6,
					enc_c_vec84_way_c6, ic_dir_vec84_c6, dc_dir_vec84_c6,
					enc_c_vec80_way_c6, ic_dir_vec80_c6, dc_dir_vec80_c6,
					enc_c_vec76_way_c6, ic_dir_vec76_c6, dc_dir_vec76_c6,
					enc_c_vec72_way_c6, ic_dir_vec72_c6, dc_dir_vec72_c6,
					enc_c_vec68_way_c6, ic_dir_vec68_c6, dc_dir_vec68_c6,
					enc_c_vec64_way_c6, ic_dir_vec64_c6, dc_dir_vec64_c6 
				   } ; 
		
// 32 bit dir vec.
assign    dirdp_inval_pckt_c6[111:88] = { enc_c_vec124_way_c6, dc_dir_vec124_c6,
                                          enc_c_vec120_way_c6, dc_dir_vec120_c6,
                                          enc_c_vec116_way_c6, dc_dir_vec116_c6,
                                          enc_c_vec112_way_c6, dc_dir_vec112_c6,
                                          enc_c_vec108_way_c6, dc_dir_vec108_c6,
                                          enc_c_vec104_way_c6, dc_dir_vec104_c6,
                                          enc_c_vec100_way_c6, dc_dir_vec100_c6,
                                          enc_c_vec96_way_c6, dc_dir_vec96_c6
                                        } ;
                
//*******************************************************************************************
// GENERATION OR WAY AND WAYVLD FOR THE CPX RETURN 
//*******************************************************************************************




               mux4ds #(3) mux_way_waywayvld_c6  ( .dout(dirvecdp_way_info_c6[2:0]),
                                .in0(way_wayvld00_mux3_c6[2:0]),
                                .in1(way_wayvld01_mux3_c6[2:0]),
                                .in2(way_wayvld10_mux3_c6[2:0]),
                                .in3(way_wayvld11_mux3_c6[2:0]),
                                .sel0(mux_vec_sel_c6[0]),
                                .sel1(mux_vec_sel_c6[1]),
                                .sel2(mux_vec_sel_c6[2]),
                                .sel3(mux_vec_sel_c6[3]));


endmodule
