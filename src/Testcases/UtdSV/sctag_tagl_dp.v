// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_tagl_dp.v
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

// This module is instanced twice, one for
// each half of what used to be tagdp.
// Pin positions. ( DP size is 

`include 	"iop.h"
`include 	"sctag.h"

module sctag_tagl_dp( /*AUTOARG*/
   // Outputs
   so, parity_c2, tag_triad0_c3, tag_triad1_c3, 
   // Inputs
   way0_tag_c2, way1_tag_c2, way2_tag_c2, way3_tag_c2, way4_tag_c2, 
   way5_tag_c2, rclk, si, se, triad0_muxsel_c3, triad1_muxsel_c3
   );


input	[`TAG_WIDTH-1:0] way0_tag_c2; // tag rd
input	[`TAG_WIDTH-1:0] way1_tag_c2;// tag rd
input	[`TAG_WIDTH-1:0] way2_tag_c2;// tag rd
input	[`TAG_WIDTH-1:0] way3_tag_c2;// tag rd
input	[`TAG_WIDTH-1:0] way4_tag_c2;// tag rd
input	[`TAG_WIDTH-1:0] way5_tag_c2;// tag rd


input		rclk;
input		si,se;

output		so;

output	[5:0]	parity_c2;
output 	[`TAG_WIDTH-1:0] tag_triad0_c3;
output 	[`TAG_WIDTH-1:0] tag_triad1_c3;


input	[2:0]	triad0_muxsel_c3;
input	[2:0]	triad1_muxsel_c3;



// All tag bits are staged into C3

wire	[`TAG_WIDTH-1:0] way0_tag_c3;
wire	[`TAG_WIDTH-1:0] way1_tag_c3;
wire	[`TAG_WIDTH-1:0] way2_tag_c3;
wire	[`TAG_WIDTH-1:0] way3_tag_c3;
wire	[`TAG_WIDTH-1:0] way4_tag_c3;
wire	[`TAG_WIDTH-1:0] way5_tag_c3;



// This data path is 32 bits wide/



zzpar32 p0_way0         ( .z(parity_c2[0]), .d({4'b0,way0_tag_c2[`TAG_WIDTH-1:0]}));

dff_s  #(`TAG_WIDTH)  ff_tag_way0_c3  (.din(way0_tag_c2[`TAG_WIDTH-1:0]), .clk(rclk),
	                    .q(way0_tag_c3[`TAG_WIDTH-1:0]), .se(se), .si(), .so());

zzpar32 p0_way1         ( .z(parity_c2[1]), .d({4'b0,way1_tag_c2[`TAG_WIDTH-1:0]}));

dff_s  #(`TAG_WIDTH)  ff_tag_way1_c3  (.din(way1_tag_c2[`TAG_WIDTH-1:0]), .clk(rclk),
	                    .q(way1_tag_c3[`TAG_WIDTH-1:0]), .se(se), .si(), .so());

zzpar32 p0_way2         ( .z(parity_c2[2]), .d({4'b0,way2_tag_c2[`TAG_WIDTH-1:0]}));

dff_s  #(`TAG_WIDTH)  ff_tag_way2_c3  (.din(way2_tag_c2[`TAG_WIDTH-1:0]), .clk(rclk),
	                    .q(way2_tag_c3[`TAG_WIDTH-1:0]), .se(se), .si(), .so());


mux3ds	#(`TAG_WIDTH)	mux_tag_triad0 (.dout (tag_triad0_c3[`TAG_WIDTH-1:0]),
                             .in0(way0_tag_c3[`TAG_WIDTH-1:0]),
                             .in1(way1_tag_c3[`TAG_WIDTH-1:0]),
                             .in2(way2_tag_c3[`TAG_WIDTH-1:0]),
                             .sel0(triad0_muxsel_c3[0]),
                             .sel1(triad0_muxsel_c3[1]),
                             .sel2(triad0_muxsel_c3[2]));

mux3ds	#(`TAG_WIDTH)	mux_tag_triad1 (.dout (tag_triad1_c3[`TAG_WIDTH-1:0]),
                             .in0(way3_tag_c3[`TAG_WIDTH-1:0]),
                             .in1(way4_tag_c3[`TAG_WIDTH-1:0]),
                             .in2(way5_tag_c3[`TAG_WIDTH-1:0]),
                             .sel0(triad1_muxsel_c3[0]),
                             .sel1(triad1_muxsel_c3[1]),
                             .sel2(triad1_muxsel_c3[2]));


zzpar32 p0_way3         ( .z(parity_c2[3]), .d({4'b0,way3_tag_c2[`TAG_WIDTH-1:0]}));

dff_s  #(`TAG_WIDTH)  ff_tag_way3_c3  (.din(way3_tag_c2[`TAG_WIDTH-1:0]), .clk(rclk),
	                    .q(way3_tag_c3[`TAG_WIDTH-1:0]), .se(se), .si(), .so());

zzpar32 p0_way4         ( .z(parity_c2[4]), .d({4'b0,way4_tag_c2[`TAG_WIDTH-1:0]}));

dff_s  #(`TAG_WIDTH)  ff_tag_way4_c3  (.din(way4_tag_c2[`TAG_WIDTH-1:0]), .clk(rclk),
	                    .q(way4_tag_c3[`TAG_WIDTH-1:0]), .se(se), .si(), .so());

zzpar32 p0_way5         ( .z(parity_c2[5]), .d({4'b0,way5_tag_c2[`TAG_WIDTH-1:0]}));

dff_s  #(`TAG_WIDTH)  ff_tag_way5_c3  (.din(way5_tag_c2[`TAG_WIDTH-1:0]), .clk(rclk),
	                    .q(way5_tag_c3[`TAG_WIDTH-1:0]), .se(se), .si(), .so());



endmodule
