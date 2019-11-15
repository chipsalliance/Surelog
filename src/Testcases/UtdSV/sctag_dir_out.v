// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_dir_out.v
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
module sctag_dir_out(/*AUTOARG*/
   // Outputs
   parity_vld_out, so, parity_vld, 
   // Inputs
   rddata_out_c6_top, rddata_out_c6_bottom, rd_data_sel_c6_top, 
   rd_data_sel_c6_bottom, parity_vld_in, rclk, si, se
   );


input	[31:0]	rddata_out_c6_top; // Top
input	[31:0]	rddata_out_c6_bottom; // Bottom

input		rd_data_sel_c6_top; // Top
input		rd_data_sel_c6_bottom; // Bottom

input	[2:0]	parity_vld_in; //  Right
output	[2:0]	parity_vld_out; // Left

output		so;
input		rclk;
input		si, se;
output		parity_vld;


wire	[31:0]	rddata_out_c6;
wire	row1_parity;
wire	row2_parity;
wire	parity_vld_prev;

// This is a 16 wide dp
// bits {0,1} {2,3} occupy the same bit pitches.

mux2ds  #(32) mux_rddata_out_c6(.dout (rddata_out_c6[31:0]) ,
                	.in0(rddata_out_c6_top[31:0]), 
			.in1(rddata_out_c6_bottom[31:0]),
                	.sel0(rd_data_sel_c6_top), 
			.sel1(~rd_data_sel_c6_top));

zzpar16 par_row1_parity   ( .z(row1_parity),
                        .d({1'b0,rddata_out_c6[30],rddata_out_c6[28],rddata_out_c6[26],
			rddata_out_c6[24],rddata_out_c6[22],rddata_out_c6[20],
			rddata_out_c6[18],rddata_out_c6[16],rddata_out_c6[14],
			rddata_out_c6[12],rddata_out_c6[10],rddata_out_c6[8],
			rddata_out_c6[6],rddata_out_c6[4],rddata_out_c6[2]}));

zzpar16 par_row2_parity   ( .z(row2_parity),
                        .d({rddata_out_c6[31],rddata_out_c6[29],rddata_out_c6[27],
                        rddata_out_c6[25],rddata_out_c6[23],rddata_out_c6[21],
                        rddata_out_c6[19],rddata_out_c6[17],rddata_out_c6[15],
                        rddata_out_c6[13],rddata_out_c6[11],rddata_out_c6[9],
                        rddata_out_c6[7],rddata_out_c6[5],rddata_out_c6[3],rddata_out_c6[1]}));

assign	parity_vld_prev = (row1_parity ^ row2_parity) 
			& rddata_out_c6[0]  &
			( rd_data_sel_c6_top | rd_data_sel_c6_bottom);


dff_s   #(1) ff_parity_vld
              (.q   (parity_vld),
               .din (parity_vld_prev),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;



assign	parity_vld_out = parity_vld_in ; // use a 30X buffer.

endmodule
