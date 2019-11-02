// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_vuad_dpm.v
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
module sctag_vuad_dpm
 (/*AUTOARG*/
   // Outputs
   so, bistordiag_ua_data, bistordiag_vd_data, vuad_dp_diag_data_c7, 
   vuad_syndrome_c9, parity_c4, 
   // Inputs
   rclk, si, se, diag_rd_ua_out, diag_rd_vd_out, arbctl_acc_ua_c2, 
   valid_rd_parity_c2, dirty_rd_parity_c2, used_rd_parity_c2, 
   alloc_rd_parity_c2, arbdata_wr_data_c2, bist_vuad_data_in, 
   sel_diag1_data_wr_c3, sel_diag0_data_wr_c3
   ) ;



input   rclk;


input	si, se;
output  so;

output	[25:0]	bistordiag_ua_data; // Left
output	[25:0]	bistordiag_vd_data; // Right

input	[25:0]	diag_rd_ua_out ; // Left
input	[25:0]	diag_rd_vd_out ; // Right
input		arbctl_acc_ua_c2; // TOP

output   [25:0] vuad_dp_diag_data_c7;
output	 [3:0]	vuad_syndrome_c9; // Bottom
output	 [3:0]	parity_c4; // Top

input		valid_rd_parity_c2; // Right
input		dirty_rd_parity_c2; // Right
input		used_rd_parity_c2; // Left
input		alloc_rd_parity_c2; // Left

input	 [25:0]	arbdata_wr_data_c2; // Top
input	 [7:0]	bist_vuad_data_in; // Top
input		sel_diag1_data_wr_c3; // Top
input		sel_diag0_data_wr_c3; // Top

wire    [25:0]  diag_out_c2;
wire    [25:0]  diag_out_c3;
wire    [25:0]  diag_out_c4;
wire    [25:0]  diag_out_c5;
wire    [25:0]  diag_out_c6;
wire    [25:0]  diag_out_c7;
wire    [25:0]  diag_out_c8;

wire	[3:0]	parity_c3;
wire	[3:0]	parity_c5;
wire	[3:0]	parity_c6;
wire	[3:0]	vuad_syndrome_c7;
wire	[3:0]	vuad_syndrome_c8;

wire	[25:0]	bist_data_c3;
wire	[25:0]	arbdata_wr_data_c3;
wire	[25:0]	bistordiag_ua_data_in, bistordiag_vd_data_in;


//////////////////////////////
// This is a 32 bit datapath
//////////////////////////////

//////////////////////////////
// Use the 26 lfetmost dp pitches for this
//////////////////////////////

// Use a 2-1 mux flop to reduce the setup on arbctl_acc_ua_c2
mux2ds #(26)  mux_diag_out_c2
 	(	.dout (diag_out_c2[25:0]),
  		.in0(diag_rd_ua_out[25:0]),
  		.in1(diag_rd_vd_out[25:0]),
  		.sel0(arbctl_acc_ua_c2),
  		.sel1(~arbctl_acc_ua_c2)
	);
dff_s   #(26)   ff_diag_out_c3
              (.q   (diag_out_c3[25:0]),
               .din (diag_out_c2[25:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

dff_s   #(26)   ff_diag_out_c4
              (.q   (diag_out_c4[25:0]),
               .din (diag_out_c3[25:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

dff_s   #(26)   ff_diag_out_c5
              (.q   (diag_out_c5[25:0]),
               .din (diag_out_c4[25:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

dff_s   #(26)   ff_diag_out_c6
              (.q   (diag_out_c6[25:0]),
               .din (diag_out_c5[25:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

dff_s   #(26)   ff_diag_out_c7
              (.q   (diag_out_c7[25:0]),
               .din (diag_out_c6[25:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

dff_s   #(26)   ff_diag_out_c8
              (.q   (diag_out_c8[25:0]),
               .din (diag_out_c7[25:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


// eventhough the suffix says c7 this is actually c8 data
// sent to deccdp. THis data gets muxed with other diagnostic
// data and inval data in C8 and is transmitted to the
// requesting sparc in the next cycle.

assign  vuad_dp_diag_data_c7 = diag_out_c8 ;



//////////////////////////////
// Use the 4 rightmost dp pitches for this
//////////////////////////////

dff_s   #(4)    ff_parity_c3
              (.q   (parity_c3[3:0]),
               .din ({valid_rd_parity_c2, dirty_rd_parity_c2,
			used_rd_parity_c2,  alloc_rd_parity_c2}),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

dff_s   #(4)    ff_parity_c4
              (.q   (parity_c4[3:0]),
               .din (parity_c3[3:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

dff_s   #(4)    ff_parity_c5
              (.q   (parity_c5[3:0]),
               .din (parity_c4[3:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

dff_s   #(4)    ff_parity_c6
              (.q   (parity_c6[3:0]),
               .din (parity_c5[3:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

dff_s   #(4)    ff_vuad_syndrome_c7
              (.q   (vuad_syndrome_c7[3:0]),
               .din (parity_c6[3:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

dff_s   #(4)    ff_vuad_syndrome_c8
              (.q   (vuad_syndrome_c8[3:0]),
               .din (vuad_syndrome_c7[3:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

dff_s   #(4)    ff_vuad_syndrome_c9
              (.q   (vuad_syndrome_c9[3:0]),
               .din (vuad_syndrome_c8[3:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;



// Bist data flops


// 26 bits from 8 bits.
assign  bist_data_c3 = { bist_vuad_data_in[1:0],
                {3{bist_vuad_data_in[7:0]}}};


//Diagnostic WR data mux
dff_s   #(26)   ff_arbdata_wr_data_c3
              (.q   (arbdata_wr_data_c3[25:0]),
               .din (arbdata_wr_data_c2[25:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;



// Use a 2-1 mux flop for bistordiag_ua_data
mux2ds #(26)  mux_lhs_bistordiag_data
              (.dout (bistordiag_ua_data_in[25:0]),
               .in0  ({arbdata_wr_data_c3[25], arbdata_wr_data_c3[23:12],
                        arbdata_wr_data_c3[24], arbdata_wr_data_c3[11:0]}),
                .sel0 (sel_diag1_data_wr_c3),
               .in1  ({bist_data_c3[25], bist_data_c3[23:12],
                        bist_data_c3[24], bist_data_c3[11:0]}),
                .sel1 (~sel_diag1_data_wr_c3)
              ) ;

dff_s   #(26)   ff_bistordiag_ua_data
              (.q   (bistordiag_ua_data[25:0]),
               .din (bistordiag_ua_data_in[25:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


// Use a 2-1 mux flop for bistordiag_vd_data
mux2ds #(26)  mux_rhs_bistordiag_data
              (.dout (bistordiag_vd_data_in[25:0]),
               .in0  ({arbdata_wr_data_c3[25], arbdata_wr_data_c3[23:12],
                        arbdata_wr_data_c3[24], arbdata_wr_data_c3[11:0]}),
                .sel0 (sel_diag0_data_wr_c3),
               .in1  ({bist_data_c3[25], bist_data_c3[23:12],
                        bist_data_c3[24], bist_data_c3[11:0]}),
                .sel1 (~sel_diag0_data_wr_c3)
              ) ;

dff_s   #(26)   ff_bistordiag_vd_data
              (.q   (bistordiag_vd_data[25:0]),
               .din (bistordiag_vd_data_in[25:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()

              ) ;

endmodule

