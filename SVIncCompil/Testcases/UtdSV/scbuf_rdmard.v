// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: scbuf_rdmard.v
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


module scbuf_rdmard (/*AUTOARG*/
   // Outputs
   so, scdata_scbuf_decc_out_c7_buf, scbuf_jbi_ctag_vld, 
   scbuf_jbi_data, scbuf_jbi_ue_err, scbuf_sctag_rdma_uerr_c10, 
   scbuf_sctag_rdma_cerr_c10, 
   // Inputs
   rclk, se, si, sctag_scbuf_ctag_en_c7, sctag_scbuf_ctag_c7, 
   sctag_scbuf_req_en_c7, scdata_scbuf_decc_out_c7, 
   sctag_scbuf_word_c7, sctag_scbuf_word_vld_c7
   ) ;

input            rclk;
input            se, si;
input            sctag_scbuf_ctag_en_c7;
input   [14:0]   sctag_scbuf_ctag_c7;
input            sctag_scbuf_req_en_c7;
input   [623:0]  scdata_scbuf_decc_out_c7;
input   [3:0]    sctag_scbuf_word_c7;
input            sctag_scbuf_word_vld_c7;

output           so;
output  [623:0]  scdata_scbuf_decc_out_c7_buf;
output           scbuf_jbi_ctag_vld;
output  [31:0]   scbuf_jbi_data;
output           scbuf_jbi_ue_err;
output           scbuf_sctag_rdma_uerr_c10;
output           scbuf_sctag_rdma_cerr_c10;


////////////////////////////////////////////////////////////////////////////////
wire             en_clk_ctag;
wire             sctag_scbuf_req_en_c8;
wire             sctag_scbuf_req_en_c9;
wire             sctag_scbuf_req_en_c10;
wire    [14:0]   sctag_scbuf_ctag_c8;
wire    [14:0]   sctag_scbuf_ctag_c9;
wire             io_read_c8;
wire             sctag_scbuf_we_c8;
wire             en_clk_data;
wire    [623:0]  scdata_scbuf_decc_out_c7_buf;
wire    [623:0]  scdata_scbuf_decc_out_c8;
wire    [623:0]  scdata_scbuf_decc_out_c9;
wire    [38:0]   scdata_scbuf_decc_out_c10;
wire    [31:0]   scdata_scbuf_dat_out_c10;
wire    [31:0]   data_ctag_mux_out_c9;
wire    [31:0]   data_ctag_mux_out_c10;
wire    [3:0]    sctag_scbuf_word_c8;
wire    [3:0]    sctag_scbuf_word_c9;
wire             sctag_scbuf_word_vld_c8;
wire             sctag_scbuf_word_vld_c9;
wire             sctag_scbuf_word_vld_c10;

wire             sel_in0;
wire             sel_in1;
wire             sel_in2;
wire             sel_in3;
wire             sel_in4;
wire             sel_in5;
wire             sel_in6;
wire             sel_in7;
wire    [155:0]  scdata_scbuf_decc_out_c9_4t1;
wire    [38:0]   scdata_scbuf_decc_out_c9_16t1;

wire    [5:0]    check0_c10;
wire             parity0_c10;
wire             rdmard_uncorr_err_c10;
wire             rdmard_uncorr_err_c11;
wire             rdmard_corr_err_c10;
wire             rdmard_corr_err_c11;
wire	[1:0]	 word_c9;


////////////////////////////////////////////////////////////////////////////////
clken_buf  clk_buf_ctag  (.clk(en_clk_ctag),                .rclk(rclk),
                          .enb_l(~sctag_scbuf_ctag_en_c7),  .tmb_l(~se));


dff_s   #(15)  ff_sctag_scbuf_ctag_c8
              (.q   (sctag_scbuf_ctag_c8[14:0]),
               .din (sctag_scbuf_ctag_c7[14:0]),
               .clk (en_clk_ctag),
               .se  (1'b0), .si  (), .so  ()
              ) ;
dff_s   #(15)  ff_sctag_scbuf_ctag_c9
              (.q   (sctag_scbuf_ctag_c9[14:0]),
               .din (sctag_scbuf_ctag_c8[14:0]),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()
              ) ;


assign  io_read_c8        = sctag_scbuf_ctag_c8[12] ;
assign  sctag_scbuf_we_c8 = io_read_c8 & sctag_scbuf_req_en_c8 ;

clken_buf  clk_buf_data (.clk  (en_clk_data),         .rclk (rclk),
                         .enb_l(~sctag_scbuf_we_c8),  .tmb_l(~se));

dff_s   #(1)   ff_sctag_scbuf_req_en_c8
              (.q   (sctag_scbuf_req_en_c8),
               .din (sctag_scbuf_req_en_c7),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ());
dff_s   #(1)   ff_sctag_scbuf_req_en_c9
              (.q   (sctag_scbuf_req_en_c9),
               .din (sctag_scbuf_req_en_c8),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ());
dff_s   #(1)   ff_sctag_scbuf_req_en_c10
              (.q   (sctag_scbuf_req_en_c10),
               .din (sctag_scbuf_req_en_c9),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ());


dff_s   #(1)   ff_sctag_scbuf_word_vld_c8
              (.q   (sctag_scbuf_word_vld_c8),
               .din (sctag_scbuf_word_vld_c7),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ());
dff_s   #(1)   ff_sctag_scbuf_word_vld_c9
              (.q   (sctag_scbuf_word_vld_c9),
               .din (sctag_scbuf_word_vld_c8),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ());
dff_s   #(1)   ff_sctag_scbuf_word_vld_c10
              (.q   (sctag_scbuf_word_vld_c10),
               .din (sctag_scbuf_word_vld_c9),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ());


assign  scdata_scbuf_decc_out_c7_buf[623:0] = scdata_scbuf_decc_out_c7[623:0];
assign  scdata_scbuf_decc_out_c8[623:0]     = scdata_scbuf_decc_out_c7[623:0];
dff_s   #(624) ff_scdata_scbuf_decc_out_c9
              (.q   (scdata_scbuf_decc_out_c9[623:0]),
               .din (scdata_scbuf_decc_out_c8[623:0]),
               .clk (en_clk_data),
               .se  (1'b0), .si  (), .so  ());



dff_s   #(4)   ff_sctag_scbuf_word_c8
              (.q   (sctag_scbuf_word_c8[3:0]),
               .din (sctag_scbuf_word_c7[3:0]),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ());
dff_s   #(4)   ff_sctag_scbuf_word_c9
              (.q   (sctag_scbuf_word_c9[3:0]),
               .din (sctag_scbuf_word_c8[3:0]),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ());


////////////////////////////////////////////////////////////////////////////////

// DWORD selection is based on addr<4:3>
assign  sel_in0 =  (sctag_scbuf_word_c9[2:1] == 2'b00) ;
assign  sel_in1 =  (sctag_scbuf_word_c9[2:1] == 2'b01) ;
assign  sel_in2 =  (sctag_scbuf_word_c9[2:1] == 2'b10) ;
assign  sel_in3 = ~(sel_in0 | sel_in1 | sel_in2) ;


assign	word_c9 = { sctag_scbuf_word_c9[3], sctag_scbuf_word_c9[0] } ;

assign  sel_in4 =  (word_c9 == 2'b00) ;
assign  sel_in5 =  (word_c9 == 2'b01) ;
assign  sel_in6 =  (word_c9 == 2'b10) ;
assign  sel_in7 = ~(sel_in4 | sel_in5 | sel_in6) ;


mux4ds #(78) mux_scdata_scbuf_decc_out_r
              (.dout (scdata_scbuf_decc_out_c9_4t1[77:0]),
               .in0  (scdata_scbuf_decc_out_c9[ 77:  0]),  .sel0 (sel_in3),
               .in1  (scdata_scbuf_decc_out_c9[155: 78]),  .sel1 (sel_in2),
               .in2  (scdata_scbuf_decc_out_c9[233:156]),  .sel2 (sel_in1),
               .in3  (scdata_scbuf_decc_out_c9[311:234]),  .sel3 (sel_in0)
              ) ;
mux4ds #(78) mux_scdata_scbuf_decc_out_l
              (.dout (scdata_scbuf_decc_out_c9_4t1[155:78]),
               .in0  (scdata_scbuf_decc_out_c9[389:312]),  .sel0 (sel_in3),
               .in1  (scdata_scbuf_decc_out_c9[467:390]),  .sel1 (sel_in2),
               .in2  (scdata_scbuf_decc_out_c9[545:468]),  .sel2 (sel_in1),
               .in3  (scdata_scbuf_decc_out_c9[623:546]),  .sel3 (sel_in0)
              ) ;


mux4ds #(39) mux_scdata_scbuf_decc_out
              (.dout (scdata_scbuf_decc_out_c9_16t1[38:0]),
               .in0  (scdata_scbuf_decc_out_c9_4t1[ 38:  0]),  .sel0 (sel_in7),
               .in1  (scdata_scbuf_decc_out_c9_4t1[ 77: 39]),  .sel1 (sel_in6),
               .in2  (scdata_scbuf_decc_out_c9_4t1[116: 78]),  .sel2 (sel_in5),
               .in3  (scdata_scbuf_decc_out_c9_4t1[155:117]),  .sel3 (sel_in4)
              ) ;

dff_s   #(39)  ff_scdata_scbuf_decc_out_c10
              (.q   (scdata_scbuf_decc_out_c10[38:0]),
               .din (scdata_scbuf_decc_out_c9_16t1[38:0]),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()
              ) ;


////////////////////////////////////////////////////////////////////////////////

zzecc_sctag_ecc39 u_ecctree_39b
  (.dout   (scdata_scbuf_dat_out_c10[31:0]),
   .cflag  (check0_c10[5:0]),
   .pflag  (parity0_c10),

   .parity (scdata_scbuf_decc_out_c10[6:0]),
   .din    (scdata_scbuf_decc_out_c10[38:7])
  ) ;

assign  rdmard_uncorr_err_c10 = sctag_scbuf_word_vld_c10 &
                                ((|check0_c10[5:0]) & ~parity0_c10) ;
assign  rdmard_corr_err_c10   = sctag_scbuf_word_vld_c10 & parity0_c10 ;


mux2ds #(32) mux_data_ctag_c9
              (.dout (data_ctag_mux_out_c9[31:0]),
               .in0  (scdata_scbuf_dat_out_c10[31:0]),      .sel0 (~sctag_scbuf_req_en_c9),
               .in1  ({17'b0, sctag_scbuf_ctag_c9[14:0]}),  .sel1 (sctag_scbuf_req_en_c9)
              ) ;
dff_s   #(32)  ff_data_ctag_mux_out_c10
              (.q   (data_ctag_mux_out_c10[31:0]),
               .din (data_ctag_mux_out_c9[31:0]),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()
              ) ;
dff_s   #(1)   ff_rdmard_uncorr_err_c11
              (.q   (rdmard_uncorr_err_c11),
               .din (rdmard_uncorr_err_c10),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()
              ) ;
dff_s   #(1)   ff_rdmard_corr_err_c11
              (.q   (rdmard_corr_err_c11),
               .din (rdmard_corr_err_c10),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()
              ) ;


////////////////////////////////////////////////////////////////////////////////
assign  scbuf_jbi_ctag_vld        = sctag_scbuf_req_en_c10 ;
assign  scbuf_jbi_data            = data_ctag_mux_out_c10[31:0] ;
assign  scbuf_jbi_ue_err          = rdmard_uncorr_err_c11 ;
assign  scbuf_sctag_rdma_uerr_c10 = rdmard_uncorr_err_c11 ;
assign  scbuf_sctag_rdma_cerr_c10 = rdmard_corr_err_c11 ;


endmodule
