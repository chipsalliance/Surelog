// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_vuadcol_dp.v
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

module sctag_vuadcol_dp
 (/*AUTOARG*/
   // Outputs
   data_out_col, 
   // Inputs
   data_in_l, mux1_h_sel, mux1_l_sel, mux2_sel, data_in_h
   ) ;


// every 4th dp pitch has empty.
input	[103:0]	 data_in_l; // TOP 4 pins per  dp pitch. ( from the array below )
input	[103:0]	 data_in_h; // BOTTOM 4 pins per dp pitch. ( from the array above )

input	[3:0]	 mux1_h_sel; // logically the same as mux1_l_sel ( addr bits <9:8> )
input	[3:0]	 mux1_l_sel; // logically the same as mux1_h_sel
input		 mux2_sel; // ( addr bit <10>)

output	[25:0]	 data_out_col; // to vuad_io_dp.



wire	[25:0]	hi_4to1;
wire	[25:0]	lo_4to1;

wire	[25:0]	hi_4to1_0;
wire	[25:0]	hi_4to1_1;
wire	[25:0]	hi_4to1_2;
wire	[25:0]	hi_4to1_3;

wire	[25:0]	lo_4to1_0;
wire	[25:0]	lo_4to1_1;
wire	[25:0]	lo_4to1_2;
wire	[25:0]	lo_4to1_3;


assign	hi_4to1_0 = { data_in_h[100], data_in_h[96], data_in_h[92],
		data_in_h[88], data_in_h[84], data_in_h[80],	
		data_in_h[76], data_in_h[72], data_in_h[68],
		data_in_h[64], data_in_h[60], data_in_h[56],
		data_in_h[52], data_in_h[48], data_in_h[44],
		data_in_h[40], data_in_h[36], data_in_h[32],
		data_in_h[28], data_in_h[24], data_in_h[20],
		data_in_h[16], data_in_h[12], data_in_h[8],
		data_in_h[4], data_in_h[0]};

assign	hi_4to1_1 = { data_in_h[101], data_in_h[97], data_in_h[93],
		data_in_h[89], data_in_h[85], data_in_h[81],	
		data_in_h[77], data_in_h[73], data_in_h[69],
		data_in_h[65], data_in_h[61], data_in_h[57],
		data_in_h[53], data_in_h[49], data_in_h[45],
		data_in_h[41], data_in_h[37], data_in_h[33],
		data_in_h[29], data_in_h[25], data_in_h[21],
		data_in_h[17], data_in_h[13], data_in_h[9],
		data_in_h[5], data_in_h[1]};

assign	hi_4to1_2 = { data_in_h[102], data_in_h[98], data_in_h[94],
		data_in_h[90], data_in_h[86], data_in_h[82],	
		data_in_h[78], data_in_h[74], data_in_h[70],
		data_in_h[66], data_in_h[62], data_in_h[58],
		data_in_h[54], data_in_h[50], data_in_h[46],
		data_in_h[42], data_in_h[38], data_in_h[34],
		data_in_h[30], data_in_h[26], data_in_h[22],
		data_in_h[18], data_in_h[14], data_in_h[10],
		data_in_h[6], data_in_h[2]};

assign	hi_4to1_3 = { data_in_h[103], data_in_h[99], data_in_h[95],
		data_in_h[91], data_in_h[87], data_in_h[83],	
		data_in_h[79], data_in_h[75], data_in_h[71],
		data_in_h[67], data_in_h[63], data_in_h[59],
		data_in_h[55], data_in_h[51], data_in_h[47],
		data_in_h[43], data_in_h[39], data_in_h[35],
		data_in_h[31], data_in_h[27], data_in_h[23],
		data_in_h[19], data_in_h[15], data_in_h[11],
		data_in_h[7], data_in_h[3]};

mux4ds  #(26)   mux_h_4to1 (.dout (hi_4to1[25:0]),
                             .in0(hi_4to1_0[25:0]),
                             .in1(hi_4to1_1[25:0]),
                             .in2(hi_4to1_2[25:0]),
                             .in3(hi_4to1_3[25:0]),
                             .sel0(mux1_h_sel[0]),
                             .sel1(mux1_h_sel[1]),
                             .sel2(mux1_h_sel[2]),
                             .sel3(mux1_h_sel[3]));

assign	lo_4to1_0 = { data_in_l[100], data_in_l[96], data_in_l[92],
		data_in_l[88], data_in_l[84], data_in_l[80],	
		data_in_l[76], data_in_l[72], data_in_l[68],
		data_in_l[64], data_in_l[60], data_in_l[56],
		data_in_l[52], data_in_l[48], data_in_l[44],
		data_in_l[40], data_in_l[36], data_in_l[32],
		data_in_l[28], data_in_l[24], data_in_l[20],
		data_in_l[16], data_in_l[12], data_in_l[8],
		data_in_l[4], data_in_l[0]};

assign	lo_4to1_1 = { data_in_l[101], data_in_l[97], data_in_l[93],
		data_in_l[89], data_in_l[85], data_in_l[81],	
		data_in_l[77], data_in_l[73], data_in_l[69],
		data_in_l[65], data_in_l[61], data_in_l[57],
		data_in_l[53], data_in_l[49], data_in_l[45],
		data_in_l[41], data_in_l[37], data_in_l[33],
		data_in_l[29], data_in_l[25], data_in_l[21],
		data_in_l[17], data_in_l[13], data_in_l[9],
		data_in_l[5], data_in_l[1]};

assign	lo_4to1_2 = { data_in_l[102], data_in_l[98], data_in_l[94],
		data_in_l[90], data_in_l[86], data_in_l[82],	
		data_in_l[78], data_in_l[74], data_in_l[70],
		data_in_l[66], data_in_l[62], data_in_l[58],
		data_in_l[54], data_in_l[50], data_in_l[46],
		data_in_l[42], data_in_l[38], data_in_l[34],
		data_in_l[30], data_in_l[26], data_in_l[22],
		data_in_l[18], data_in_l[14], data_in_l[10],
		data_in_l[6], data_in_l[2]};

assign	lo_4to1_3 = { data_in_l[103], data_in_l[99], data_in_l[95],
		data_in_l[91], data_in_l[87], data_in_l[83],	
		data_in_l[79], data_in_l[75], data_in_l[71],
		data_in_l[67], data_in_l[63], data_in_l[59],
		data_in_l[55], data_in_l[51], data_in_l[47],
		data_in_l[43], data_in_l[39], data_in_l[35],
		data_in_l[31], data_in_l[27], data_in_l[23],
		data_in_l[19], data_in_l[15], data_in_l[11],
		data_in_l[7], data_in_l[3]};


mux4ds  #(26)   mux_l_4to1 (.dout (lo_4to1[25:0]),
                             .in0(lo_4to1_0[25:0]),
                             .in1(lo_4to1_1[25:0]),
                             .in2(lo_4to1_2[25:0]),
                             .in3(lo_4to1_3[25:0]),
                             .sel0(mux1_l_sel[0]),
                             .sel1(mux1_l_sel[1]),
                             .sel2(mux1_l_sel[2]),
                             .sel3(mux1_l_sel[3]));

mux2ds  #(26)   mux_2to1 (.dout (data_out_col[25:0]),
                             .in0(hi_4to1[25:0]),
                             .in1(lo_4to1[25:0]),
                             .sel0(~mux2_sel),
                             .sel1(mux2_sel));


endmodule


