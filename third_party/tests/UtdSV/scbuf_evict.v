// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: scbuf_evict.v
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
`include   "iop.h"


module scbuf_evict
 (/*AUTOARG*/
   // Outputs
   so, scbuf_dram_wr_data_r5_pb, scbuf_dram_data_vld_r5_pb, 
   scbuf_dram_data_mecc_r5_pb, scbuf_sctag_ev_uerr_r5_pb, 
   scbuf_sctag_ev_cerr_r5_pb, sctag_scbuf_wbrd_en_r1_v1, 
   sctag_scbuf_wbrd_en_r1_v2, sctag_scbuf_wbrd_en_r1_v3, 
   sctag_scbuf_wbrd_en_r1_v4, sctag_scbuf_wbrd_wl_r1_v1, 
   sctag_scbuf_wbrd_wl_r1_v2, sctag_scbuf_wbrd_wl_r1_v3, 
   sctag_scbuf_wbrd_wl_r1_v4, sctag_scbuf_wbwr_wen_c8_v1, 
   sctag_scbuf_wbwr_wen_c8_v2, sctag_scbuf_wbwr_wen_c8_v3, 
   sctag_scbuf_wbwr_wen_c8_v4, sctag_scbuf_wbwr_wl_c8_v1, 
   sctag_scbuf_wbwr_wl_c8_v2, sctag_scbuf_wbwr_wl_c8_v3, 
   sctag_scbuf_wbwr_wl_c8_v4, sctag_scbuf_rdma_rden_r1_v1, 
   sctag_scbuf_rdma_rden_r1_v2, sctag_scbuf_rdma_rden_r1_v3, 
   sctag_scbuf_rdma_rden_r1_v4, sctag_scbuf_rdma_rdwl_r1_v1, 
   sctag_scbuf_rdma_rdwl_r1_v2, sctag_scbuf_rdma_rdwl_r1_v3, 
   sctag_scbuf_rdma_rdwl_r1_v4, sctag_scbuf_rdma_wren_s3, 
   sctag_scbuf_rdma_wren_s3_v4, sctag_scbuf_rdma_wren_s3_v3, 
   sctag_scbuf_rdma_wren_s3_v2, sctag_scbuf_rdma_wren_s3_v1, 
   sctag_scbuf_rdma_wrwl_s3_v1, sctag_scbuf_rdma_wrwl_s3_v2, 
   sctag_scbuf_rdma_wrwl_s3_v3, sctag_scbuf_rdma_wrwl_s3_v4, 
   rdma_array_din, 
   // Inputs
   rclk, arst_l, grst_l, se, sehold, si, sctag_scbuf_wbrd_en_r0, 
   wb_array_dout, sctag_scbuf_evict_en_r0, sctag_scbuf_ev_dword_r0, 
   sctag_scbuf_rdma_rden_r0, rdma_array_dout, sctag_scbuf_wbrd_wl_r0, 
   sctag_scbuf_wbwr_wen_c6, sctag_scbuf_wbwr_wl_c6, 
   sctag_scbuf_rdma_rdwl_r0, sctag_scbuf_rdma_wren_s2, 
   sctag_scbuf_rdma_wrwl_s2, jbi_sctag_req, jbi_scbuf_ecc
   ) ;


// Inputs
input            rclk;
input            arst_l;
input            grst_l;
input            se, sehold, si;
input            sctag_scbuf_wbrd_en_r0;
input   [623:0]  wb_array_dout;
input            sctag_scbuf_evict_en_r0;
input   [2:0]    sctag_scbuf_ev_dword_r0;
input            sctag_scbuf_rdma_rden_r0;
input   [623:0]  rdma_array_dout;

input   [2:0]    sctag_scbuf_wbrd_wl_r0;
input            sctag_scbuf_wbwr_wen_c6;
input   [2:0]    sctag_scbuf_wbwr_wl_c6;
input   [1:0]    sctag_scbuf_rdma_rdwl_r0;
input   [15:0]   sctag_scbuf_rdma_wren_s2;
input   [1:0]    sctag_scbuf_rdma_wrwl_s2;


input	[31:0]	 jbi_sctag_req ;
input	[6:0]	 jbi_scbuf_ecc ;

// Outputs
output           so;
output  [63:0]   scbuf_dram_wr_data_r5_pb;
output           scbuf_dram_data_vld_r5_pb;
output           scbuf_dram_data_mecc_r5_pb;
output           scbuf_sctag_ev_uerr_r5_pb;
output           scbuf_sctag_ev_cerr_r5_pb;

output           sctag_scbuf_wbrd_en_r1_v1;
output           sctag_scbuf_wbrd_en_r1_v2;
output           sctag_scbuf_wbrd_en_r1_v3;
output           sctag_scbuf_wbrd_en_r1_v4;
output  [2:0]    sctag_scbuf_wbrd_wl_r1_v1;
output  [2:0]    sctag_scbuf_wbrd_wl_r1_v2;
output  [2:0]    sctag_scbuf_wbrd_wl_r1_v3;
output  [2:0]    sctag_scbuf_wbrd_wl_r1_v4;
output           sctag_scbuf_wbwr_wen_c8_v1;
output           sctag_scbuf_wbwr_wen_c8_v2;
output           sctag_scbuf_wbwr_wen_c8_v3;
output           sctag_scbuf_wbwr_wen_c8_v4;
output  [2:0]    sctag_scbuf_wbwr_wl_c8_v1;
output  [2:0]    sctag_scbuf_wbwr_wl_c8_v2;
output  [2:0]    sctag_scbuf_wbwr_wl_c8_v3;
output  [2:0]    sctag_scbuf_wbwr_wl_c8_v4;

output           sctag_scbuf_rdma_rden_r1_v1;
output           sctag_scbuf_rdma_rden_r1_v2;
output           sctag_scbuf_rdma_rden_r1_v3;
output           sctag_scbuf_rdma_rden_r1_v4;
output  [1:0]    sctag_scbuf_rdma_rdwl_r1_v1;
output  [1:0]    sctag_scbuf_rdma_rdwl_r1_v2;
output  [1:0]    sctag_scbuf_rdma_rdwl_r1_v3;
output  [1:0]    sctag_scbuf_rdma_rdwl_r1_v4;
output  [15:0]   sctag_scbuf_rdma_wren_s3;
output           sctag_scbuf_rdma_wren_s3_v4 ;
output           sctag_scbuf_rdma_wren_s3_v3 ;
output           sctag_scbuf_rdma_wren_s3_v2 ;
output           sctag_scbuf_rdma_wren_s3_v1 ;
output  [1:0]    sctag_scbuf_rdma_wrwl_s3_v1;
output  [1:0]    sctag_scbuf_rdma_wrwl_s3_v2;
output  [1:0]    sctag_scbuf_rdma_wrwl_s3_v3;
output  [1:0]    sctag_scbuf_rdma_wrwl_s3_v4;

output	[623:0]	 rdma_array_din ;



////////////////////////////////////////////////////////////////////////////////
wire             sctag_scbuf_wbrd_en_r2;
wire             sctag_scbuf_rdma_rden_r1;
wire             sctag_scbuf_rdma_rden_r2;
wire             wb_or_rdma_rden_r2;
wire    [623:0]  wb_rdma_mux_out;
wire    [623:0]  wb_array_dout_r3;
wire    [ 77:0]  wb_array_dout_r4;
wire    [ 63:0]  wb_array_dout_r5;

wire    [  2:0]  sctag_scbuf_ev_dword_r1;
wire    [  2:0]  sctag_scbuf_ev_dword_r2;
wire    [  2:0]  sctag_scbuf_ev_dword_r3;
wire             sel_in0;
wire             sel_in1;
wire             sel_in2;
wire             sel_in3;
wire    [155:0]  wb_array_dout_r3_4t1;
wire    [ 77:0]  wb_array_dout_r3_8t1;

wire    [ 63:0]  wb_array_dout_ecc_r4;
wire    [  5:0]  check0_r4;
wire    [  5:0]  check1_r4;
wire             evict_uncorr_err_r4;
wire             evict_corr_err_r4;

wire             sctag_scbuf_wbwr_wen_c7;
wire    [  2:0]  sctag_scbuf_wbwr_wl_c7;

wire	[38:0]	jbi_sctag_req_ecc_s2 ;
wire	[38:0]  jbi_sctag_req_ecc_s3;

wire    [2:0]    sctag_scbuf_wbrd_wl_r1;
wire             sctag_scbuf_wbwr_wen_c8;
wire    [2:0]    sctag_scbuf_wbwr_wl_c8;
wire    [1:0]    sctag_scbuf_rdma_rdwl_r1;
wire    [1:0]    sctag_scbuf_rdma_wrwl_s3;

wire             sctag_scbuf_evict_en_r3;
wire             evict_uncorr_err_unqual_r4;
wire             error_qual_in;
wire             error_qual;



dffrl_async  #(1)  reset_flop
                    (.q     (dbb_rst_l),
                     .clk   (rclk),
                     .rst_l (arst_l),
                     .din   (grst_l),
                     .se    (se), .si(), .so());


////////////////////////////////////////////////////////////////////////////////
// Data arriving from jbus is flopped and fanned out to 624 bits here.
////////////////////////////////////////////////////////////////////////////////
assign	jbi_sctag_req_ecc_s2 = {jbi_sctag_req[31:0], jbi_scbuf_ecc[6:0]} ;


dff_s   #(39)  ff_jbi_sctag_req_ecc_s3    (.din(jbi_sctag_req_ecc_s2[38:0]), 
			.clk(rclk),
                     .q(jbi_sctag_req_ecc_s3[38:0]), .se(1'b0), .si(), .so());


assign	rdma_array_din = {16{jbi_sctag_req_ecc_s3[38:0]}} ;

////////////////////////////////////////////////////////////////////////////////
dff_s   #(1)   ff_sctag_scbuf_wbwr_wen_c7
              (.q   (sctag_scbuf_wbwr_wen_c7),
               .din (sctag_scbuf_wbwr_wen_c6),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()) ;
dff_s   #(1)   ff_sctag_scbuf_wbwr_wen_c8
              (.q   (sctag_scbuf_wbwr_wen_c8),
               .din (sctag_scbuf_wbwr_wen_c7),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()) ;
assign  sctag_scbuf_wbwr_wen_c8_v1 = sctag_scbuf_wbwr_wen_c8 ;
assign  sctag_scbuf_wbwr_wen_c8_v2 = sctag_scbuf_wbwr_wen_c8 ;
assign  sctag_scbuf_wbwr_wen_c8_v3 = sctag_scbuf_wbwr_wen_c8 ;
assign  sctag_scbuf_wbwr_wen_c8_v4 = sctag_scbuf_wbwr_wen_c8 ;

dff_s   #(3)   ff_sctag_scbuf_wbwr_wl_c7
              (.q   (sctag_scbuf_wbwr_wl_c7[2:0]),
               .din (sctag_scbuf_wbwr_wl_c6[2:0]),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()) ;
dff_s   #(3)   ff_sctag_scbuf_wbwr_wl_c8
              (.q   (sctag_scbuf_wbwr_wl_c8[2:0]),
               .din (sctag_scbuf_wbwr_wl_c7[2:0]),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()) ;
assign  sctag_scbuf_wbwr_wl_c8_v1[2:0] = sctag_scbuf_wbwr_wl_c8[2:0] ;
assign  sctag_scbuf_wbwr_wl_c8_v2[2:0] = sctag_scbuf_wbwr_wl_c8[2:0] ;
assign  sctag_scbuf_wbwr_wl_c8_v3[2:0] = sctag_scbuf_wbwr_wl_c8[2:0] ;
assign  sctag_scbuf_wbwr_wl_c8_v4[2:0] = sctag_scbuf_wbwr_wl_c8[2:0] ;


dff_s   #(3)   ff_sctag_scbuf_wbrd_wl_r1
              (.q   (sctag_scbuf_wbrd_wl_r1[2:0]),
               .din (sctag_scbuf_wbrd_wl_r0[2:0]),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()) ;
assign  sctag_scbuf_wbrd_wl_r1_v1[2:0] = sctag_scbuf_wbrd_wl_r1[2:0] ;
assign  sctag_scbuf_wbrd_wl_r1_v2[2:0] = sctag_scbuf_wbrd_wl_r1[2:0] ;
assign  sctag_scbuf_wbrd_wl_r1_v3[2:0] = sctag_scbuf_wbrd_wl_r1[2:0] ;
assign  sctag_scbuf_wbrd_wl_r1_v4[2:0] = sctag_scbuf_wbrd_wl_r1[2:0] ;



dff_s   #(2)   ff_sctag_scbuf_rdma_rdwl_r1
              (.q   (sctag_scbuf_rdma_rdwl_r1[1:0]),
               .din (sctag_scbuf_rdma_rdwl_r0[1:0]),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()) ;
assign  sctag_scbuf_rdma_rdwl_r1_v1[1:0] = sctag_scbuf_rdma_rdwl_r1[1:0] ;
assign  sctag_scbuf_rdma_rdwl_r1_v2[1:0] = sctag_scbuf_rdma_rdwl_r1[1:0] ;
assign  sctag_scbuf_rdma_rdwl_r1_v3[1:0] = sctag_scbuf_rdma_rdwl_r1[1:0] ;
assign  sctag_scbuf_rdma_rdwl_r1_v4[1:0] = sctag_scbuf_rdma_rdwl_r1[1:0] ;

dff_s   #(16)  ff_sctag_scbuf_rdma_wren_s3
              (.q   (sctag_scbuf_rdma_wren_s3[15:0]),
               .din (sctag_scbuf_rdma_wren_s2[15:0]),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()) ;
assign sctag_scbuf_rdma_wren_s3_v4 = (sctag_scbuf_rdma_wren_s3[6] |
                                      sctag_scbuf_rdma_wren_s3[4] |
                                      sctag_scbuf_rdma_wren_s3[2] |
                                      sctag_scbuf_rdma_wren_s3[0]) ;
assign sctag_scbuf_rdma_wren_s3_v3 = (sctag_scbuf_rdma_wren_s3[7] |
                                      sctag_scbuf_rdma_wren_s3[5] |
                                      sctag_scbuf_rdma_wren_s3[3] |
                                      sctag_scbuf_rdma_wren_s3[1]) ;
assign sctag_scbuf_rdma_wren_s3_v2 = (sctag_scbuf_rdma_wren_s3[14] |
                                      sctag_scbuf_rdma_wren_s3[12] |
                                      sctag_scbuf_rdma_wren_s3[10] |
                                      sctag_scbuf_rdma_wren_s3[8]) ;
assign sctag_scbuf_rdma_wren_s3_v1 = (sctag_scbuf_rdma_wren_s3[15] |
                                      sctag_scbuf_rdma_wren_s3[13] |
                                      sctag_scbuf_rdma_wren_s3[11] |
                                      sctag_scbuf_rdma_wren_s3[9]) ;


dff_s   #(2)   ff_sctag_scbuf_rdma_wrwl_s3
              (.q   (sctag_scbuf_rdma_wrwl_s3[1:0]),
               .din (sctag_scbuf_rdma_wrwl_s2[1:0]),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()) ;
assign  sctag_scbuf_rdma_wrwl_s3_v1[1:0] = sctag_scbuf_rdma_wrwl_s3[1:0] ;
assign  sctag_scbuf_rdma_wrwl_s3_v2[1:0] = sctag_scbuf_rdma_wrwl_s3[1:0] ;
assign  sctag_scbuf_rdma_wrwl_s3_v3[1:0] = sctag_scbuf_rdma_wrwl_s3[1:0] ;
assign  sctag_scbuf_rdma_wrwl_s3_v4[1:0] = sctag_scbuf_rdma_wrwl_s3[1:0] ;


////////////////////////////////////////////////////////////////////////////////

dff_s   #(1)   ff_sctag_scbuf_wbrd_en_r1
              (.q   (sctag_scbuf_wbrd_en_r1),
               .din (sctag_scbuf_wbrd_en_r0),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()) ;
assign  sctag_scbuf_wbrd_en_r1_v1 = sctag_scbuf_wbrd_en_r1 ;
assign  sctag_scbuf_wbrd_en_r1_v2 = sctag_scbuf_wbrd_en_r1 ;
assign  sctag_scbuf_wbrd_en_r1_v3 = sctag_scbuf_wbrd_en_r1 ;
assign  sctag_scbuf_wbrd_en_r1_v4 = sctag_scbuf_wbrd_en_r1 ;

mux2ds #(1)  mux_wbrd_en_r1_in
               (.dout (sctag_scbuf_wbrd_en_r1_in),
                .in0  (sctag_scbuf_wbrd_en_r1),  .sel0 (~sehold),
                .in1  (sctag_scbuf_wbrd_en_r2),  .sel1 (sehold)) ;
dff_s   #(1)   ff_sctag_scbuf_wbrd_en_r2
              (.q   (sctag_scbuf_wbrd_en_r2),
               .din (sctag_scbuf_wbrd_en_r1_in),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()) ;

dff_s   #(1)   ff_sctag_scbuf_rdma_rden_r1
              (.q   (sctag_scbuf_rdma_rden_r1),
               .din (sctag_scbuf_rdma_rden_r0),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()) ;
assign  sctag_scbuf_rdma_rden_r1_v1 = sctag_scbuf_rdma_rden_r1 ;
assign  sctag_scbuf_rdma_rden_r1_v2 = sctag_scbuf_rdma_rden_r1 ;
assign  sctag_scbuf_rdma_rden_r1_v3 = sctag_scbuf_rdma_rden_r1 ;
assign  sctag_scbuf_rdma_rden_r1_v4 = sctag_scbuf_rdma_rden_r1 ;

dff_s   #(1)   ff_sctag_scbuf_rdma_rden_r2
              (.q   (sctag_scbuf_rdma_rden_r2),
               .din (sctag_scbuf_rdma_rden_r1),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()) ;
dff_s   #(1)   ff_sctag_scbuf_rdma_rden_r3
              (.q   (sctag_scbuf_rdma_rden_r3),
               .din (sctag_scbuf_rdma_rden_r2),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()) ;
assign error_qual_in = sctag_scbuf_rdma_rden_r3 | (error_qual & sctag_scbuf_evict_en_r3) ;
dffrl_s #(1)  ff_array_rd_ptr
             (.q   (error_qual),
              .din (error_qual_in),
              .clk (rclk),  .rst_l  (dbb_rst_l),
              .se  (se), .si  (), .so  ()) ;


assign  wb_or_rdma_rden_r2 = (sctag_scbuf_wbrd_en_r2 | sctag_scbuf_rdma_rden_r2) | sehold ;

clken_buf  clk_buf_r2  (.clk(en_clk_r2),                   .rclk(rclk),
                        .enb_l(~wb_or_rdma_rden_r2),       .tmb_l(~se));
clken_buf  clk_buf_r3  (.clk(en_clk_r3),                   .rclk(rclk),
                        .enb_l(~sctag_scbuf_evict_en_r3),  .tmb_l(~se));

mux2ds #(624) mux_wb_rdma_mux_out
               (.dout (wb_rdma_mux_out[623:0]),
                .in0  (wb_array_dout[623:0]),    .sel0 (sctag_scbuf_wbrd_en_r2),
                .in1  (rdma_array_dout[623:0]),  .sel1 (~sctag_scbuf_wbrd_en_r2)) ;
dff_s   #(624) ff_wb_array_dout_r3
              (.q   (wb_array_dout_r3[623:0]),
               .din (wb_rdma_mux_out[623:0]),
               .clk (en_clk_r2),
               .se  (1'b0), .si  (), .so  ()) ;



////////////////////////////////////////////////////////////////////////////////
dff_s   #(1)   ff_sctag_scbuf_evict_en_r1
              (.q   (sctag_scbuf_evict_en_r1),
               .din (sctag_scbuf_evict_en_r0),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()) ;
dff_s   #(1)   ff_sctag_scbuf_evict_en_r2
              (.q   (sctag_scbuf_evict_en_r2),
               .din (sctag_scbuf_evict_en_r1),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()) ;
dff_s   #(1)   ff_sctag_scbuf_evict_en_r3
              (.q   (sctag_scbuf_evict_en_r3),
               .din (sctag_scbuf_evict_en_r2),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()) ;
dff_s   #(1)   ff_sctag_scbuf_evict_en_r4
              (.q   (sctag_scbuf_evict_en_r4),
               .din (sctag_scbuf_evict_en_r3),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()) ;
dff_s   #(1)   ff_sctag_scbuf_evict_en_r5
              (.q   (sctag_scbuf_evict_en_r5),
               .din (sctag_scbuf_evict_en_r4),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()) ;


dff_s   #(3)   ff_ev_dword_r1
              (.q   (sctag_scbuf_ev_dword_r1[2:0]),
               .din (sctag_scbuf_ev_dword_r0[2:0]),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()) ;
dff_s   #(3)   ff_ev_dword_r2
              (.q   (sctag_scbuf_ev_dword_r2[2:0]),
               .din (sctag_scbuf_ev_dword_r1[2:0]),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()) ;
dff_s   #(3)   ff_ev_dword_r3
              (.q   (sctag_scbuf_ev_dword_r3[2:0]),
               .din (sctag_scbuf_ev_dword_r2[2:0]),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()) ;

assign  sel_in0 =  (sctag_scbuf_ev_dword_r3[1:0] == 2'b00) ;
assign  sel_in1 =  (sctag_scbuf_ev_dword_r3[1:0] == 2'b01) ;
assign  sel_in2 =  (sctag_scbuf_ev_dword_r3[1:0] == 2'b10) ;
assign  sel_in3 = ~(sel_in0 | sel_in1 | sel_in2) ;

mux4ds #(78) mux_wb_array_dout_1
              (.dout (wb_array_dout_r3_4t1[77:0]),
               .in0  (wb_array_dout_r3[ 77:  0]),  .sel0 (sel_in3),
               .in1  (wb_array_dout_r3[155: 78]),  .sel1 (sel_in2),
               .in2  (wb_array_dout_r3[233:156]),  .sel2 (sel_in1),
               .in3  (wb_array_dout_r3[311:234]),  .sel3 (sel_in0)) ;

mux4ds #(78) mux_wb_array_dout_2
              (.dout (wb_array_dout_r3_4t1[155:78]),
               .in0  (wb_array_dout_r3[389:312]),  .sel0 (sel_in3),
               .in1  (wb_array_dout_r3[467:390]),  .sel1 (sel_in2),
               .in2  (wb_array_dout_r3[545:468]),  .sel2 (sel_in1),
               .in3  (wb_array_dout_r3[623:546]),  .sel3 (sel_in0)) ;

mux2ds #(78) mux_wb_array_dout_8t1
              (.dout (wb_array_dout_r3_8t1[77:0]),
               .in0  (wb_array_dout_r3_4t1[ 77: 0]),  .sel0 (sctag_scbuf_ev_dword_r3[2]),
               .in1  (wb_array_dout_r3_4t1[155:78]),  .sel1 (~sctag_scbuf_ev_dword_r3[2])) ;

dff_s   #(78)  ff_wb_array_dout_r4
              (.q   (wb_array_dout_r4[77:0]),
               .din (wb_array_dout_r3_8t1[77:0]),
               .clk (en_clk_r3),
               .se  (1'b0), .si  (), .so  ()) ;


////////////////////////////////////////////////////////////////////////////////

zzecc_sctag_ecc39 u_ecctree_39b_1
  (.dout   (wb_array_dout_ecc_r4[31:0]),
   .cflag  (check0_r4[5:0]),
   .pflag  (parity0_r4),

   .parity (wb_array_dout_r4[6:0]),
   .din    (wb_array_dout_r4[38:7])) ;

zzecc_sctag_ecc39 u_ecctree_39b_2
  (.dout   (wb_array_dout_ecc_r4[63:32]),
   .cflag  (check1_r4[5:0]),
   .pflag  (parity1_r4),

   .parity (wb_array_dout_r4[45:39]),
   .din    (wb_array_dout_r4[77:46])) ;


assign evict_uncorr_err_r4 = (sctag_scbuf_evict_en_r4 & !error_qual) &
                             (((|check0_r4[5:0]) & ~parity0_r4) |
                              ((|check1_r4[5:0]) & ~parity1_r4)) ;
assign evict_uncorr_err_unqual_r4 = sctag_scbuf_evict_en_r4 &
                                    (((|check0_r4[5:0]) & ~parity0_r4) |
                                     ((|check1_r4[5:0]) & ~parity1_r4)) ;

assign evict_corr_err_r4   = (sctag_scbuf_evict_en_r4 & !error_qual) &
                             (parity0_r4 | parity1_r4) ;


dff_s   #(64)  ff_wb_array_dout_r5
              (.q   (wb_array_dout_r5[63:0]),
               .din (wb_array_dout_ecc_r4[63:0]),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()) ;

dff_s   #(1)   ff_evict_uncorr_err_r5
              (.q   (evict_uncorr_err_r5),
               .din (evict_uncorr_err_r4),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()) ;

dff_s   #(1)   ff_evict_uncorr_err_unqual_r5
              (.q   (evict_uncorr_err_unqual_r5),
               .din (evict_uncorr_err_unqual_r4),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()) ;

dff_s   #(1)   ff_evict_corr_err_r5
              (.q   (evict_corr_err_r5),
               .din (evict_corr_err_r4),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()) ;


////////////////////////////////////////////////////////////////////////////////
assign  scbuf_dram_wr_data_r5_pb   = wb_array_dout_r5[63:0] ;
assign  scbuf_dram_data_vld_r5_pb  = sctag_scbuf_evict_en_r5 ;
assign  scbuf_dram_data_mecc_r5_pb = evict_uncorr_err_unqual_r5 ;
assign  scbuf_sctag_ev_uerr_r5_pb  = evict_uncorr_err_r5 ;
assign  scbuf_sctag_ev_cerr_r5_pb  = evict_corr_err_r5 ;

////////////////////////////////////////////////////////////////////////////////


endmodule
