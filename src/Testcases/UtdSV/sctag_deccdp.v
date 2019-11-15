// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_deccdp.v
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
// This module has the following functionality :-
// 1. Perform the ECC correction on the 155 bit data readd out from
//    the L2 array and convert it into the 128 bit corrected data
// 2. Mux 64 bit out of the 128 bit corrected data for the following
//    2 operations :-
//     a. Partial Store.
//     b. L2 Data Scrub.
// 3. Mux 39 bit out of the 155 bit uncorrected data for the following
//    3 operations :-
//     a. Diagnostic accesses to l2data
//     b. TAP reads to DRAM addresses.
//     c. BIST accesses to l2data.

// Change ( 4/7/2003)
// Changed the input dword_sel_c8 to dword_sel_c7
// Keep the pin in the same place. Setup of
// dword_sel_c7 should be between 50-70ps.

// Added  a 1 bit flop for dword_sel_c7.

module sctag_deccdp(/*AUTOARG*/
   // Outputs
   retdp_data_c8, deccdp_arbdp_data_c8, retdp_diag_data_c7, 
   lda_syndrome_c9, check0_c7, check1_c7, check2_c7, check3_c7, 
   parity0_c7, parity1_c7, parity2_c7, parity3_c7, so, 
   // Inputs
   sel_higher_word_c7, sel_higher_dword_c7, dword_sel_c7, 
   retdp_data_c7, retdp_ecc_c7, rclk, si, se
   );

output	[127:0]	retdp_data_c8;     // data to oqdp
output	[63:0]	deccdp_arbdp_data_c8; // data to arbdatadp
output	[38:0]	retdp_diag_data_c7 ; // diagnostic data
output	[27:0]	lda_syndrome_c9;     // to csr block


// from and to decc_ctl
input	sel_higher_word_c7;
input	sel_higher_dword_c7;
input	dword_sel_c7;
output	[5:0]	check0_c7 ;
output	[5:0]	check1_c7 ;
output	[5:0]	check2_c7 ;
output	[5:0]	check3_c7 ;
output		parity0_c7;
output		parity1_c7;
output		parity2_c7;
output		parity3_c7;

input	[127:0]	retdp_data_c7;
input	[27:0]	retdp_ecc_c7;

input		rclk;
input		si, se;
output		so;


wire	[127:0]	corr_data_c7;
wire	[38:0]	data_word0_c7;
wire	[38:0]	data_word1_c7;
wire	[38:0]	data_word2_c7;
wire	[38:0]	data_word3_c7;

wire	[38:0]	left_diag_out_c7;
wire	[38:0]	rgt_diag_out_c7;


wire	[127:0]	retdp_data_c8; // data to oqdp

wire	[27:0]	error_synd_c7;
wire	[27:0]	error_synd_c8;

wire	dword_sel_c8;

zzecc_sctag_ecc39  bit117_155
 (.dout(corr_data_c7[127:96]),
  .cflag(check3_c7[5:0]),
  .pflag(parity3_c7),
  .parity(retdp_ecc_c7[27:21]),
  .din(retdp_data_c7[127:96])
  ) ;

// msb to the left
dff_s   #(32) ff_data_rtn_c8_127_96		// arrange this flop in 4 rows.
              (.q   (retdp_data_c8[127:96]),	// interleave the bits
               .din (corr_data_c7[127:96]),	// For example, 96,100,104 .. belong to the same row
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

zzecc_sctag_ecc39  bit78_116
 (.dout(corr_data_c7[95:64]),
  .cflag(check2_c7[5:0]),
  .pflag(parity2_c7),
  .parity(retdp_ecc_c7[20:14]),
  .din(retdp_data_c7[95:64])
  ) ;

// msb to the left
dff_s   #(32) ff_data_rtn_c8_95_64		// arrange this flop in 4 rows.
              (.q   (retdp_data_c8[95:64]),	// interleave the bits
               .din (corr_data_c7[95:64]),	// For example, 64,68,8 .. belong to the same row
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

zzecc_sctag_ecc39  bit39_77
 (.dout(corr_data_c7[63:32]),
  .cflag(check1_c7[5:0]),
  .pflag(parity1_c7),
  .parity(retdp_ecc_c7[13:7]),
  .din(retdp_data_c7[63:32])
  ) ;

// msb to the left
dff_s   #(32) ff_data_rtn_c8_63_32		// arrange this flop in 4 rows.
              (.q   (retdp_data_c8[63:32]),	// interleave the bits
               .din (corr_data_c7[63:32]),	// For example, 32,36,40 .. belong to the same row
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

zzecc_sctag_ecc39  bit0_38
 (.dout   (corr_data_c7[31:0]),
  .cflag  (check0_c7[5:0]),
  .pflag  (parity0_c7),
  .parity (retdp_ecc_c7[6:0]),
  .din    (retdp_data_c7[31:0])
  ) ;

// msb to the left
dff_s   #(32) ff_data_rtn_c8_31_0		// arrange this flop in 4 rows.
              (.q   (retdp_data_c8[31:0]),	// interleave the bits
               .din (corr_data_c7[31:0]),	// For example, 32,36,40 .. belong to the same row
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;



//////////////////////////
// SYNDROME to csr_ctl.
//////////////////////////
assign  error_synd_c7 = {parity3_c7,check3_c7[5:0],
                         parity2_c7,check2_c7[5:0],		
                         parity1_c7,check1_c7[5:0],
                         parity0_c7,check0_c7[5:0]} ;

dff_s   #(28)   ff_error_synd_c8
              (.q   (error_synd_c8[27:0]),
               .din (error_synd_c7[27:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

dff_s   #(28)   ff_lda_syndrome_c9
              (.q   (lda_syndrome_c9[27:0]),
               .din (error_synd_c8[27:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


dff_s   #(1)   ff_dword_sel_c8
              (.q   (dword_sel_c8),
               .din (dword_sel_c7),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

mux2ds #(64)  ret_mux
              (.dout (deccdp_arbdp_data_c8[63:0]),
               .in0  (retdp_data_c8[127:64]),  .sel0 (~dword_sel_c8),
               .in1  (retdp_data_c8[63:0]),    .sel1 (dword_sel_c8)
              ) ;

assign data_word1_c7 = {retdp_data_c7[95:64], retdp_ecc_c7[20:14]} ;
assign data_word0_c7 = {retdp_data_c7[127:96],retdp_ecc_c7[27:21]} ;


mux2ds #(39)  mux_left_diag_out
              (.dout (left_diag_out_c7[38:0]),
               .in0  (data_word0_c7[38:0]),  .sel0 (~sel_higher_word_c7),
               .in1  (data_word1_c7[38:0]),  .sel1 (sel_higher_word_c7)
              ) ;

assign data_word3_c7 = {retdp_data_c7[31:0],  retdp_ecc_c7[6:0]} ;
assign data_word2_c7 = {retdp_data_c7[63:32], retdp_ecc_c7[13:7]} ;

mux2ds #(39)  mux_rgt_diag_out
              (.dout (rgt_diag_out_c7[38:0]),
               .in0  (data_word2_c7[38:0]),  .sel0 (~sel_higher_word_c7),
               .in1  (data_word3_c7[38:0]),  .sel1 (sel_higher_word_c7)
              ) ;

mux2ds #(39)  mux_diag_out
              (.dout (retdp_diag_data_c7[38:0]),
               .in0  (left_diag_out_c7[38:0]),  .sel0 (~sel_higher_dword_c7),
               .in1  (rgt_diag_out_c7[38:0]),   .sel1 (sel_higher_dword_c7)
              ) ;



endmodule
