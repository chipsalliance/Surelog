// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: ff_dram_sc_bank2.v
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
//////////////////////////////////////////////////////////////////////
// Flop repeater for L2<->  dram controller signals. 
// This repeter block has 
// 8 row of data flops and 4 rows of ctl/addr flops.
// The 8 data rows are placed in one column ( 39 bits wide )
// the 4 addr/ctl rows are placed in one column ( 13 bits wide )
//////////////////////////////////////////////////////////////////////

module ff_dram_sc_bank2(/*AUTOARG*/
   // Outputs
   dram_scbuf_data_r2_d1, dram_scbuf_ecc_r2_d1, 
   scbuf_dram_wr_data_r5_d1, scbuf_dram_data_vld_r5_d1, 
   scbuf_dram_data_mecc_r5_d1, sctag_dram_rd_req_d1, 
   sctag_dram_rd_dummy_req_d1, sctag_dram_rd_req_id_d1, 
   sctag_dram_addr_d1, sctag_dram_wr_req_d1, dram_sctag_rd_ack_d1, 
   dram_sctag_wr_ack_d1, dram_sctag_chunk_id_r0_d1, 
   dram_sctag_data_vld_r0_d1, dram_sctag_rd_req_id_r0_d1, 
   dram_sctag_secc_err_r2_d1, dram_sctag_mecc_err_r2_d1, 
   dram_sctag_scb_mecc_err_d1, dram_sctag_scb_secc_err_d1, so, 
   // Inputs
   dram_scbuf_data_r2, dram_scbuf_ecc_r2, scbuf_dram_wr_data_r5, 
   scbuf_dram_data_vld_r5, scbuf_dram_data_mecc_r5, 
   sctag_dram_rd_req, sctag_dram_rd_dummy_req, sctag_dram_rd_req_id, 
   sctag_dram_addr, sctag_dram_wr_req, dram_sctag_rd_ack, 
   dram_sctag_wr_ack, dram_sctag_chunk_id_r0, dram_sctag_data_vld_r0, 
   dram_sctag_rd_req_id_r0, dram_sctag_secc_err_r2, 
   dram_sctag_mecc_err_r2, dram_sctag_scb_mecc_err, 
   dram_sctag_scb_secc_err, rclk, si, se
   );


   // dram-scbuf TOP
   input [127:0]        dram_scbuf_data_r2;
   input [27:0]        	dram_scbuf_ecc_r2;        
   // BOTTOM
   output [127:0]       dram_scbuf_data_r2_d1;
   output [27:0]        dram_scbuf_ecc_r2_d1;        


   


   // scbuf to dram BOTTOM
   input [63:0]		scbuf_dram_wr_data_r5;
   input		scbuf_dram_data_vld_r5;
   input		scbuf_dram_data_mecc_r5;
   // TOP
   output [63:0]	scbuf_dram_wr_data_r5_d1;
   output		scbuf_dram_data_vld_r5_d1;
   output		scbuf_dram_data_mecc_r5_d1;



   // sctag_dram-sctag signals INputs
   // @ the bottom.
   // Outputs @ the top.
   input	sctag_dram_rd_req;
   input	sctag_dram_rd_dummy_req;
   input [2:0]	sctag_dram_rd_req_id;
   input [39:5]	sctag_dram_addr;
   input	sctag_dram_wr_req;	
   //
   output	sctag_dram_rd_req_d1;
   output	sctag_dram_rd_dummy_req_d1;
   output [2:0]	sctag_dram_rd_req_id_d1;
   output [39:5]	sctag_dram_addr_d1;
   output	sctag_dram_wr_req_d1;	


// dram-sctag signals. Outputs @ bottom
// and Input pins on top.
input                   dram_sctag_rd_ack;
input                   dram_sctag_wr_ack;
input  [1:0]            dram_sctag_chunk_id_r0;
input                   dram_sctag_data_vld_r0;
input  [2:0]            dram_sctag_rd_req_id_r0;
input                   dram_sctag_secc_err_r2 ;
input                   dram_sctag_mecc_err_r2 ;
input                   dram_sctag_scb_mecc_err;
input                   dram_sctag_scb_secc_err;
//
output                   dram_sctag_rd_ack_d1;
output                   dram_sctag_wr_ack_d1;
output  [1:0]            dram_sctag_chunk_id_r0_d1;
output                   dram_sctag_data_vld_r0_d1;
output  [2:0]            dram_sctag_rd_req_id_r0_d1;
output                   dram_sctag_secc_err_r2_d1 ;
output                   dram_sctag_mecc_err_r2_d1 ;
output                   dram_sctag_scb_mecc_err_d1;
output                   dram_sctag_scb_secc_err_d1;
			



   input		rclk;
   input		si, se;
   
   output		so;



  // dram-scbuf signals. 8 rows of flops.
  // Input at the top and output at the bottom.

 
	dff_s  #(39)   ff_flop_bank0_row_0      (.q({dram_scbuf_data_r2_d1[127],
				dram_scbuf_data_r2_d1[123],
				dram_scbuf_data_r2_d1[119],
				dram_scbuf_data_r2_d1[115],
				dram_scbuf_data_r2_d1[111],
				dram_scbuf_data_r2_d1[107],
				dram_scbuf_data_r2_d1[103],
				dram_scbuf_data_r2_d1[99],
				dram_scbuf_data_r2_d1[95],
				dram_scbuf_data_r2_d1[91],
				dram_scbuf_data_r2_d1[87],
				dram_scbuf_data_r2_d1[83],
				dram_scbuf_data_r2_d1[79],
				dram_scbuf_data_r2_d1[75],
				dram_scbuf_data_r2_d1[71],
				dram_scbuf_data_r2_d1[67],
				dram_scbuf_data_r2_d1[63],
                                dram_scbuf_data_r2_d1[59],
                                dram_scbuf_data_r2_d1[55],
                                dram_scbuf_data_r2_d1[51],
                                dram_scbuf_data_r2_d1[47],
                                dram_scbuf_data_r2_d1[43],
                                dram_scbuf_data_r2_d1[39],
                                dram_scbuf_data_r2_d1[35],
                                dram_scbuf_data_r2_d1[31],
                                dram_scbuf_data_r2_d1[27],
                                dram_scbuf_data_r2_d1[23],
                                dram_scbuf_data_r2_d1[19],
                                dram_scbuf_data_r2_d1[15],
                                dram_scbuf_data_r2_d1[11],
                                dram_scbuf_data_r2_d1[7],
                                dram_scbuf_data_r2_d1[3],
				dram_scbuf_ecc_r2_d1[27],
				dram_scbuf_ecc_r2_d1[23],
				dram_scbuf_ecc_r2_d1[19],
				dram_scbuf_ecc_r2_d1[15],
				dram_scbuf_ecc_r2_d1[11],
				dram_scbuf_ecc_r2_d1[7],
				dram_scbuf_ecc_r2_d1[3] }),
                                 .din({dram_scbuf_data_r2[127],
				dram_scbuf_data_r2[123],
				dram_scbuf_data_r2[119],
				dram_scbuf_data_r2[115],
				dram_scbuf_data_r2[111],
				dram_scbuf_data_r2[107],
				dram_scbuf_data_r2[103],
				dram_scbuf_data_r2[99],
				dram_scbuf_data_r2[95],
				dram_scbuf_data_r2[91],
				dram_scbuf_data_r2[87],
				dram_scbuf_data_r2[83],
				dram_scbuf_data_r2[79],
				dram_scbuf_data_r2[75],
				dram_scbuf_data_r2[71],
				dram_scbuf_data_r2[67],
				dram_scbuf_data_r2[63],
                                dram_scbuf_data_r2[59],
                                dram_scbuf_data_r2[55],
                                dram_scbuf_data_r2[51],
                                dram_scbuf_data_r2[47],
                                dram_scbuf_data_r2[43],
                                dram_scbuf_data_r2[39],
                                dram_scbuf_data_r2[35],
                                dram_scbuf_data_r2[31],
                                dram_scbuf_data_r2[27],
                                dram_scbuf_data_r2[23],
                                dram_scbuf_data_r2[19],
                                dram_scbuf_data_r2[15],
                                dram_scbuf_data_r2[11],
                                dram_scbuf_data_r2[7],
                                dram_scbuf_data_r2[3],
				dram_scbuf_ecc_r2[27],
				dram_scbuf_ecc_r2[23],
				dram_scbuf_ecc_r2[19],
				dram_scbuf_ecc_r2[15],
				dram_scbuf_ecc_r2[11],
				dram_scbuf_ecc_r2[7],
				dram_scbuf_ecc_r2[3]}),
                                 .clk(rclk), .se(1'b0), .si(), .so() );

	   
	dff_s  #(39)   ff_flop_bank0_row_1      (.q({dram_scbuf_data_r2_d1[126],
				dram_scbuf_data_r2_d1[122],
				dram_scbuf_data_r2_d1[118],
				dram_scbuf_data_r2_d1[114],
				dram_scbuf_data_r2_d1[110],
				dram_scbuf_data_r2_d1[106],
				dram_scbuf_data_r2_d1[102],
				dram_scbuf_data_r2_d1[98],
				dram_scbuf_data_r2_d1[94],
				dram_scbuf_data_r2_d1[90],
				dram_scbuf_data_r2_d1[86],
				dram_scbuf_data_r2_d1[82],
				dram_scbuf_data_r2_d1[78],
				dram_scbuf_data_r2_d1[74],
				dram_scbuf_data_r2_d1[70],
				dram_scbuf_data_r2_d1[66],
				dram_scbuf_data_r2_d1[62],
                                dram_scbuf_data_r2_d1[58],
                                dram_scbuf_data_r2_d1[54],
                                dram_scbuf_data_r2_d1[50],
                                dram_scbuf_data_r2_d1[46],
                                dram_scbuf_data_r2_d1[42],
                                dram_scbuf_data_r2_d1[38],
                                dram_scbuf_data_r2_d1[34],
                                dram_scbuf_data_r2_d1[30],
                                dram_scbuf_data_r2_d1[26],
                                dram_scbuf_data_r2_d1[22],
                                dram_scbuf_data_r2_d1[18],
                                dram_scbuf_data_r2_d1[14],
                                dram_scbuf_data_r2_d1[10],
                                dram_scbuf_data_r2_d1[6],
                                dram_scbuf_data_r2_d1[2],
				dram_scbuf_ecc_r2_d1[26],
				dram_scbuf_ecc_r2_d1[22],
				dram_scbuf_ecc_r2_d1[18],
				dram_scbuf_ecc_r2_d1[14],
				dram_scbuf_ecc_r2_d1[10],
				dram_scbuf_ecc_r2_d1[6],
				dram_scbuf_ecc_r2_d1[2] }),
                                 .din({dram_scbuf_data_r2[126],
				dram_scbuf_data_r2[122],
				dram_scbuf_data_r2[118],
				dram_scbuf_data_r2[114],
				dram_scbuf_data_r2[110],
				dram_scbuf_data_r2[106],
				dram_scbuf_data_r2[102],
				dram_scbuf_data_r2[98],
				dram_scbuf_data_r2[94],
				dram_scbuf_data_r2[90],
				dram_scbuf_data_r2[86],
				dram_scbuf_data_r2[82],
				dram_scbuf_data_r2[78],
				dram_scbuf_data_r2[74],
				dram_scbuf_data_r2[70],
				dram_scbuf_data_r2[66],
				dram_scbuf_data_r2[62],
                                dram_scbuf_data_r2[58],
                                dram_scbuf_data_r2[54],
                                dram_scbuf_data_r2[50],
                                dram_scbuf_data_r2[46],
                                dram_scbuf_data_r2[42],
                                dram_scbuf_data_r2[38],
                                dram_scbuf_data_r2[34],
                                dram_scbuf_data_r2[30],
                                dram_scbuf_data_r2[26],
                                dram_scbuf_data_r2[22],
                                dram_scbuf_data_r2[18],
                                dram_scbuf_data_r2[14],
                                dram_scbuf_data_r2[10],
                                dram_scbuf_data_r2[6],
                                dram_scbuf_data_r2[2],
				dram_scbuf_ecc_r2[26],
				dram_scbuf_ecc_r2[22],
				dram_scbuf_ecc_r2[18],
				dram_scbuf_ecc_r2[14],
				dram_scbuf_ecc_r2[10],
				dram_scbuf_ecc_r2[6],
				dram_scbuf_ecc_r2[2]}),
                                 .clk(rclk), .se(1'b0), .si(), .so() );

	   
	dff_s  #(39)   ff_flop_bank0_row_2      (.q({dram_scbuf_data_r2_d1[125],
				dram_scbuf_data_r2_d1[121],
				dram_scbuf_data_r2_d1[117],
				dram_scbuf_data_r2_d1[113],
				dram_scbuf_data_r2_d1[109],
				dram_scbuf_data_r2_d1[105],
				dram_scbuf_data_r2_d1[101],
				dram_scbuf_data_r2_d1[97],
				dram_scbuf_data_r2_d1[93],
				dram_scbuf_data_r2_d1[89],
				dram_scbuf_data_r2_d1[85],
				dram_scbuf_data_r2_d1[81],
				dram_scbuf_data_r2_d1[77],
				dram_scbuf_data_r2_d1[73],
				dram_scbuf_data_r2_d1[69],
				dram_scbuf_data_r2_d1[65],
				dram_scbuf_data_r2_d1[61],
                                dram_scbuf_data_r2_d1[57],
                                dram_scbuf_data_r2_d1[53],
                                dram_scbuf_data_r2_d1[49],
                                dram_scbuf_data_r2_d1[45],
                                dram_scbuf_data_r2_d1[41],
                                dram_scbuf_data_r2_d1[37],
                                dram_scbuf_data_r2_d1[33],
                                dram_scbuf_data_r2_d1[29],
                                dram_scbuf_data_r2_d1[25],
                                dram_scbuf_data_r2_d1[21],
                                dram_scbuf_data_r2_d1[17],
                                dram_scbuf_data_r2_d1[13],
                                dram_scbuf_data_r2_d1[9],
                                dram_scbuf_data_r2_d1[5],
                                dram_scbuf_data_r2_d1[1],
				dram_scbuf_ecc_r2_d1[25],
				dram_scbuf_ecc_r2_d1[21],
				dram_scbuf_ecc_r2_d1[17],
				dram_scbuf_ecc_r2_d1[13],
				dram_scbuf_ecc_r2_d1[9],
				dram_scbuf_ecc_r2_d1[5],
				dram_scbuf_ecc_r2_d1[1] }),
                                 .din({dram_scbuf_data_r2[125],
				dram_scbuf_data_r2[121],
				dram_scbuf_data_r2[117],
				dram_scbuf_data_r2[113],
				dram_scbuf_data_r2[109],
				dram_scbuf_data_r2[105],
				dram_scbuf_data_r2[101],
				dram_scbuf_data_r2[97],
				dram_scbuf_data_r2[93],
				dram_scbuf_data_r2[89],
				dram_scbuf_data_r2[85],
				dram_scbuf_data_r2[81],
				dram_scbuf_data_r2[77],
				dram_scbuf_data_r2[73],
				dram_scbuf_data_r2[69],
				dram_scbuf_data_r2[65],
				dram_scbuf_data_r2[61],
                                dram_scbuf_data_r2[57],
                                dram_scbuf_data_r2[53],
                                dram_scbuf_data_r2[49],
                                dram_scbuf_data_r2[45],
                                dram_scbuf_data_r2[41],
                                dram_scbuf_data_r2[37],
                                dram_scbuf_data_r2[33],
                                dram_scbuf_data_r2[29],
                                dram_scbuf_data_r2[25],
                                dram_scbuf_data_r2[21],
                                dram_scbuf_data_r2[17],
                                dram_scbuf_data_r2[13],
                                dram_scbuf_data_r2[9],
                                dram_scbuf_data_r2[5],
                                dram_scbuf_data_r2[1],
				dram_scbuf_ecc_r2[25],
				dram_scbuf_ecc_r2[21],
				dram_scbuf_ecc_r2[17],
				dram_scbuf_ecc_r2[13],
				dram_scbuf_ecc_r2[9],
				dram_scbuf_ecc_r2[5],
				dram_scbuf_ecc_r2[1]}),
                                 .clk(rclk), .se(1'b0), .si(), .so() );

	   
	dff_s  #(39)   ff_flop_bank0_row_3      (.q({dram_scbuf_data_r2_d1[124],
				dram_scbuf_data_r2_d1[120],
				dram_scbuf_data_r2_d1[116],
				dram_scbuf_data_r2_d1[112],
				dram_scbuf_data_r2_d1[108],
				dram_scbuf_data_r2_d1[104],
				dram_scbuf_data_r2_d1[100],
				dram_scbuf_data_r2_d1[96],
				dram_scbuf_data_r2_d1[92],
				dram_scbuf_data_r2_d1[88],
				dram_scbuf_data_r2_d1[84],
				dram_scbuf_data_r2_d1[80],
				dram_scbuf_data_r2_d1[76],
				dram_scbuf_data_r2_d1[72],
				dram_scbuf_data_r2_d1[68],
				dram_scbuf_data_r2_d1[64],
				dram_scbuf_data_r2_d1[60],
                                dram_scbuf_data_r2_d1[56],
                                dram_scbuf_data_r2_d1[52],
                                dram_scbuf_data_r2_d1[48],
                                dram_scbuf_data_r2_d1[44],
                                dram_scbuf_data_r2_d1[40],
                                dram_scbuf_data_r2_d1[36],
                                dram_scbuf_data_r2_d1[32],
                                dram_scbuf_data_r2_d1[28],
                                dram_scbuf_data_r2_d1[24],
                                dram_scbuf_data_r2_d1[20],
                                dram_scbuf_data_r2_d1[16],
                                dram_scbuf_data_r2_d1[12],
                                dram_scbuf_data_r2_d1[8],
                                dram_scbuf_data_r2_d1[4],
                                dram_scbuf_data_r2_d1[0],
				dram_scbuf_ecc_r2_d1[24],
				dram_scbuf_ecc_r2_d1[20],
				dram_scbuf_ecc_r2_d1[16],
				dram_scbuf_ecc_r2_d1[12],
				dram_scbuf_ecc_r2_d1[8],
				dram_scbuf_ecc_r2_d1[4],
				dram_scbuf_ecc_r2_d1[0] }),
                                 .din({dram_scbuf_data_r2[124],
				dram_scbuf_data_r2[120],
				dram_scbuf_data_r2[116],
				dram_scbuf_data_r2[112],
				dram_scbuf_data_r2[108],
				dram_scbuf_data_r2[104],
				dram_scbuf_data_r2[100],
				dram_scbuf_data_r2[96],
				dram_scbuf_data_r2[92],
				dram_scbuf_data_r2[88],
				dram_scbuf_data_r2[84],
				dram_scbuf_data_r2[80],
				dram_scbuf_data_r2[76],
				dram_scbuf_data_r2[72],
				dram_scbuf_data_r2[68],
				dram_scbuf_data_r2[64],
				dram_scbuf_data_r2[60],
                                dram_scbuf_data_r2[56],
                                dram_scbuf_data_r2[52],
                                dram_scbuf_data_r2[48],
                                dram_scbuf_data_r2[44],
                                dram_scbuf_data_r2[40],
                                dram_scbuf_data_r2[36],
                                dram_scbuf_data_r2[32],
                                dram_scbuf_data_r2[28],
                                dram_scbuf_data_r2[24],
                                dram_scbuf_data_r2[20],
                                dram_scbuf_data_r2[16],
                                dram_scbuf_data_r2[12],
                                dram_scbuf_data_r2[8],
                                dram_scbuf_data_r2[4],
                                dram_scbuf_data_r2[0],
				dram_scbuf_ecc_r2[24],
				dram_scbuf_ecc_r2[20],
				dram_scbuf_ecc_r2[16],
				dram_scbuf_ecc_r2[12],
				dram_scbuf_ecc_r2[8],
				dram_scbuf_ecc_r2[4],
				dram_scbuf_ecc_r2[0]}),
                                 .clk(rclk), .se(1'b0), .si(), .so() );


	dff_s  #(32)   ff_bank0_row_4      (.q({scbuf_dram_wr_data_r5_d1[63],
				scbuf_dram_wr_data_r5_d1[61],
				scbuf_dram_wr_data_r5_d1[59],
				scbuf_dram_wr_data_r5_d1[57],
				scbuf_dram_wr_data_r5_d1[55],
				scbuf_dram_wr_data_r5_d1[53],
				scbuf_dram_wr_data_r5_d1[51],
				scbuf_dram_wr_data_r5_d1[49],
				scbuf_dram_wr_data_r5_d1[47],
				scbuf_dram_wr_data_r5_d1[45],
				scbuf_dram_wr_data_r5_d1[43],
				scbuf_dram_wr_data_r5_d1[41],
				scbuf_dram_wr_data_r5_d1[39],
				scbuf_dram_wr_data_r5_d1[37],
				scbuf_dram_wr_data_r5_d1[35],
				scbuf_dram_wr_data_r5_d1[33],
				scbuf_dram_wr_data_r5_d1[31],
                                scbuf_dram_wr_data_r5_d1[29],
                                scbuf_dram_wr_data_r5_d1[27],
                                scbuf_dram_wr_data_r5_d1[25],
                                scbuf_dram_wr_data_r5_d1[23],
                                scbuf_dram_wr_data_r5_d1[21],
                                scbuf_dram_wr_data_r5_d1[19],
                                scbuf_dram_wr_data_r5_d1[17],
                                scbuf_dram_wr_data_r5_d1[15],
                                scbuf_dram_wr_data_r5_d1[13],
                                scbuf_dram_wr_data_r5_d1[11],
                                scbuf_dram_wr_data_r5_d1[9],
                                scbuf_dram_wr_data_r5_d1[7],
                                scbuf_dram_wr_data_r5_d1[5],
                                scbuf_dram_wr_data_r5_d1[3],
                                scbuf_dram_wr_data_r5_d1[1]} ),
                                 .din({scbuf_dram_wr_data_r5[63],
				scbuf_dram_wr_data_r5[61],
				scbuf_dram_wr_data_r5[59],
				scbuf_dram_wr_data_r5[57],
				scbuf_dram_wr_data_r5[55],
				scbuf_dram_wr_data_r5[53],
				scbuf_dram_wr_data_r5[51],
				scbuf_dram_wr_data_r5[49],
				scbuf_dram_wr_data_r5[47],
				scbuf_dram_wr_data_r5[45],
				scbuf_dram_wr_data_r5[43],
				scbuf_dram_wr_data_r5[41],
				scbuf_dram_wr_data_r5[39],
				scbuf_dram_wr_data_r5[37],
				scbuf_dram_wr_data_r5[35],
				scbuf_dram_wr_data_r5[33],
				scbuf_dram_wr_data_r5[31],
                                scbuf_dram_wr_data_r5[29],
                                scbuf_dram_wr_data_r5[27],
                                scbuf_dram_wr_data_r5[25],
                                scbuf_dram_wr_data_r5[23],
                                scbuf_dram_wr_data_r5[21],
                                scbuf_dram_wr_data_r5[19],
                                scbuf_dram_wr_data_r5[17],
                                scbuf_dram_wr_data_r5[15],
                                scbuf_dram_wr_data_r5[13],
                                scbuf_dram_wr_data_r5[11],
                                scbuf_dram_wr_data_r5[9],
                                scbuf_dram_wr_data_r5[7],
                                scbuf_dram_wr_data_r5[5],
                                scbuf_dram_wr_data_r5[3],
                                scbuf_dram_wr_data_r5[1]} ),
                                 .clk(rclk), .se(1'b0), .si(), .so() );

	   
	dff_s  #(34)   ff_bank0_row_5      (.q({scbuf_dram_wr_data_r5_d1[62],
				scbuf_dram_wr_data_r5_d1[60],
				scbuf_dram_wr_data_r5_d1[58],
				scbuf_dram_wr_data_r5_d1[56],
				scbuf_dram_wr_data_r5_d1[54],
				scbuf_dram_wr_data_r5_d1[52],
				scbuf_dram_wr_data_r5_d1[50],
				scbuf_dram_wr_data_r5_d1[48],
				scbuf_dram_wr_data_r5_d1[46],
				scbuf_dram_wr_data_r5_d1[44],
				scbuf_dram_wr_data_r5_d1[42],
				scbuf_dram_wr_data_r5_d1[40],
				scbuf_dram_wr_data_r5_d1[38],
				scbuf_dram_wr_data_r5_d1[36],
				scbuf_dram_wr_data_r5_d1[34],
				scbuf_dram_wr_data_r5_d1[32],
				scbuf_dram_wr_data_r5_d1[30],
                                scbuf_dram_wr_data_r5_d1[28],
                                scbuf_dram_wr_data_r5_d1[26],
                                scbuf_dram_wr_data_r5_d1[24],
                                scbuf_dram_wr_data_r5_d1[22],
                                scbuf_dram_wr_data_r5_d1[20],
                                scbuf_dram_wr_data_r5_d1[18],
                                scbuf_dram_wr_data_r5_d1[16],
                                scbuf_dram_wr_data_r5_d1[14],
                                scbuf_dram_wr_data_r5_d1[12],
                                scbuf_dram_wr_data_r5_d1[10],
                                scbuf_dram_wr_data_r5_d1[8],
                                scbuf_dram_wr_data_r5_d1[6],
                                scbuf_dram_wr_data_r5_d1[4],
                                scbuf_dram_wr_data_r5_d1[2],
                                scbuf_dram_wr_data_r5_d1[0],
				scbuf_dram_data_mecc_r5_d1,
				scbuf_dram_data_vld_r5_d1
				} ),
                                 .din({scbuf_dram_wr_data_r5[62],
				scbuf_dram_wr_data_r5[60],
				scbuf_dram_wr_data_r5[58],
				scbuf_dram_wr_data_r5[56],
				scbuf_dram_wr_data_r5[54],
				scbuf_dram_wr_data_r5[52],
				scbuf_dram_wr_data_r5[50],
				scbuf_dram_wr_data_r5[48],
				scbuf_dram_wr_data_r5[46],
				scbuf_dram_wr_data_r5[44],
				scbuf_dram_wr_data_r5[42],
				scbuf_dram_wr_data_r5[40],
				scbuf_dram_wr_data_r5[38],
				scbuf_dram_wr_data_r5[36],
				scbuf_dram_wr_data_r5[34],
				scbuf_dram_wr_data_r5[32],
				scbuf_dram_wr_data_r5[30],
                                scbuf_dram_wr_data_r5[28],
                                scbuf_dram_wr_data_r5[26],
                                scbuf_dram_wr_data_r5[24],
                                scbuf_dram_wr_data_r5[22],
                                scbuf_dram_wr_data_r5[20],
                                scbuf_dram_wr_data_r5[18],
                                scbuf_dram_wr_data_r5[16],
                                scbuf_dram_wr_data_r5[14],
                                scbuf_dram_wr_data_r5[12],
                                scbuf_dram_wr_data_r5[10],
                                scbuf_dram_wr_data_r5[8],
                                scbuf_dram_wr_data_r5[6],
                                scbuf_dram_wr_data_r5[4],
                                scbuf_dram_wr_data_r5[2],
                                scbuf_dram_wr_data_r5[0],
				scbuf_dram_data_mecc_r5,
				scbuf_dram_data_vld_r5 }),
                                 .clk(rclk), .se(1'b0), .si(), .so() );


dff_s  #(41)   ff_flop_bank0_col1_row012      (.q({sctag_dram_addr_d1[39:5],
					sctag_dram_rd_req_id_d1[2:0],
					sctag_dram_wr_req_d1,
					sctag_dram_rd_dummy_req_d1,
					sctag_dram_rd_req_d1}),
					.din({sctag_dram_addr[39:5],
                                        sctag_dram_rd_req_id[2:0],
                                        sctag_dram_wr_req,
                                        sctag_dram_rd_dummy_req,
                                        sctag_dram_rd_req}),
                                 .clk(rclk), .se(1'b0), .si(), .so() );
	  

dff_s  #(12)   ff_flop_bank0_col1_row3      (.q({dram_sctag_rd_ack_d1,
					dram_sctag_wr_ack_d1,
					dram_sctag_chunk_id_r0_d1[1:0],
					dram_sctag_data_vld_r0_d1,
					dram_sctag_rd_req_id_r0_d1[2:0],
					dram_sctag_secc_err_r2_d1,
					dram_sctag_mecc_err_r2_d1,
					dram_sctag_scb_mecc_err_d1,
					dram_sctag_scb_secc_err_d1}),	
					.din({dram_sctag_rd_ack,
                                        dram_sctag_wr_ack,
                                        dram_sctag_chunk_id_r0[1:0], 
                                        dram_sctag_data_vld_r0,     
                                        dram_sctag_rd_req_id_r0[2:0],       
                                        dram_sctag_secc_err_r2,     
                                        dram_sctag_mecc_err_r2,     
                                        dram_sctag_scb_mecc_err,    
                                        dram_sctag_scb_secc_err}),
                                 .clk(rclk), .se(1'b0), .si(), .so() );




endmodule

	  
 
