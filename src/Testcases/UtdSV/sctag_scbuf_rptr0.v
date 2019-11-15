// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_scbuf_rptr0.v
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
module sctag_scbuf_rptr0 (/*AUTOARG*/
   // Outputs
   sctag_scbuf_fbrd_en_c3_buf, sctag_scbuf_fbrd_wl_c3_buf, 
   sctag_scbuf_fbwr_wen_r2_buf, sctag_scbuf_fbwr_wl_r2_buf, 
   sctag_scbuf_fbd_stdatasel_c3_buf, sctag_scbuf_stdecc_c3_buf, 
   sctag_scbuf_ev_dword_r0_buf, sctag_scbuf_evict_en_r0_buf, 
   sctag_scbuf_wbwr_wen_c6_buf, sctag_scbuf_wbwr_wl_c6_buf, 
   sctag_scbuf_wbrd_en_r0_buf, sctag_scbuf_wbrd_wl_r0_buf, 
   sctag_scbuf_rdma_wren_s2_buf, sctag_scbuf_rdma_wrwl_s2_buf, 
   sctag_scbuf_rdma_rden_r0_buf, sctag_scbuf_rdma_rdwl_r0_buf, 
   sctag_scbuf_ctag_en_c7_buf, sctag_scbuf_ctag_c7_buf, 
   sctag_scbuf_req_en_c7_buf, sctag_scbuf_word_c7_buf, 
   sctag_scbuf_word_vld_c7_buf, scbuf_sctag_ev_uerr_r5_buf, 
   scbuf_sctag_ev_cerr_r5_buf, scbuf_sctag_rdma_uerr_c10_buf, 
   scbuf_sctag_rdma_cerr_c10_buf, 
   // Inputs
   sctag_scbuf_fbrd_en_c3, sctag_scbuf_fbrd_wl_c3, 
   sctag_scbuf_fbwr_wen_r2, sctag_scbuf_fbwr_wl_r2, 
   sctag_scbuf_fbd_stdatasel_c3, sctag_scbuf_stdecc_c3, 
   sctag_scbuf_ev_dword_r0, sctag_scbuf_evict_en_r0, 
   sctag_scbuf_wbwr_wen_c6, sctag_scbuf_wbwr_wl_c6, 
   sctag_scbuf_wbrd_en_r0, sctag_scbuf_wbrd_wl_r0, 
   sctag_scbuf_rdma_wren_s2, sctag_scbuf_rdma_wrwl_s2, 
   sctag_scbuf_rdma_rden_r0, sctag_scbuf_rdma_rdwl_r0, 
   sctag_scbuf_ctag_en_c7, sctag_scbuf_ctag_c7, 
   sctag_scbuf_req_en_c7, sctag_scbuf_word_c7, 
   sctag_scbuf_word_vld_c7, scbuf_sctag_ev_uerr_r5, 
   scbuf_sctag_ev_cerr_r5, scbuf_sctag_rdma_uerr_c10, 
   scbuf_sctag_rdma_cerr_c10
   );


//////////////////////////////////////////////////////////////////////////////
input           sctag_scbuf_fbrd_en_c3;
input   [2:0]   sctag_scbuf_fbrd_wl_c3 ;
input   [15:0]  sctag_scbuf_fbwr_wen_r2 ;
input   [2:0]   sctag_scbuf_fbwr_wl_r2 ;
input           sctag_scbuf_fbd_stdatasel_c3;
input   [77:0]  sctag_scbuf_stdecc_c3;
input   [2:0]   sctag_scbuf_ev_dword_r0;
input           sctag_scbuf_evict_en_r0;
input   [3:0]   sctag_scbuf_wbwr_wen_c6;
input   [2:0]   sctag_scbuf_wbwr_wl_c6;
input           sctag_scbuf_wbrd_en_r0;
input   [2:0]   sctag_scbuf_wbrd_wl_r0;
input   [15:0]  sctag_scbuf_rdma_wren_s2;
input   [1:0]   sctag_scbuf_rdma_wrwl_s2;
input           sctag_scbuf_rdma_rden_r0;
input   [1:0]   sctag_scbuf_rdma_rdwl_r0;
input           sctag_scbuf_ctag_en_c7;
input   [14:0]  sctag_scbuf_ctag_c7;
input           sctag_scbuf_req_en_c7;
input   [3:0]   sctag_scbuf_word_c7;
input           sctag_scbuf_word_vld_c7;

output          sctag_scbuf_fbrd_en_c3_buf;
output  [2:0]   sctag_scbuf_fbrd_wl_c3_buf;
output  [15:0]  sctag_scbuf_fbwr_wen_r2_buf;
output  [2:0]   sctag_scbuf_fbwr_wl_r2_buf;
output          sctag_scbuf_fbd_stdatasel_c3_buf;
output  [77:0]  sctag_scbuf_stdecc_c3_buf;
output  [2:0]   sctag_scbuf_ev_dword_r0_buf;
output          sctag_scbuf_evict_en_r0_buf;
output  [3:0]   sctag_scbuf_wbwr_wen_c6_buf;
output  [2:0]   sctag_scbuf_wbwr_wl_c6_buf;
output          sctag_scbuf_wbrd_en_r0_buf;
output  [2:0]   sctag_scbuf_wbrd_wl_r0_buf;
output  [15:0]  sctag_scbuf_rdma_wren_s2_buf;
output  [1:0]   sctag_scbuf_rdma_wrwl_s2_buf;
output          sctag_scbuf_rdma_rden_r0_buf;
output  [1:0]   sctag_scbuf_rdma_rdwl_r0_buf;
output          sctag_scbuf_ctag_en_c7_buf;
output  [14:0]  sctag_scbuf_ctag_c7_buf;
output          sctag_scbuf_req_en_c7_buf;
output  [3:0]   sctag_scbuf_word_c7_buf;
output          sctag_scbuf_word_vld_c7_buf;



input           scbuf_sctag_ev_uerr_r5;
input           scbuf_sctag_ev_cerr_r5;
input           scbuf_sctag_rdma_uerr_c10;
input           scbuf_sctag_rdma_cerr_c10;

output          scbuf_sctag_ev_uerr_r5_buf;
output          scbuf_sctag_ev_cerr_r5_buf;
output          scbuf_sctag_rdma_uerr_c10_buf;
output          scbuf_sctag_rdma_cerr_c10_buf;


//////////////////////////////////////////////////////////////////////////////
wire            sctag_scbuf_fbrd_en_c3_buf;
wire    [2:0]   sctag_scbuf_fbrd_wl_c3_buf;
wire    [15:0]  sctag_scbuf_fbwr_wen_r2_buf;
wire    [2:0]   sctag_scbuf_fbwr_wl_r2_buf;
wire            sctag_scbuf_fbd_stdatasel_c3_buf;
wire    [77:0]  sctag_scbuf_stdecc_c3_buf;
wire    [2:0]   sctag_scbuf_ev_dword_r0_buf;
wire            sctag_scbuf_evict_en_r0_buf;
wire    [3:0]   sctag_scbuf_wbwr_wen_c6_buf;
wire    [2:0]   sctag_scbuf_wbwr_wl_c6_buf;
wire            sctag_scbuf_wbrd_en_r0_buf;
wire    [2:0]   sctag_scbuf_wbrd_wl_r0_buf;
wire    [15:0]  sctag_scbuf_rdma_wren_s2_buf;
wire    [1:0]   sctag_scbuf_rdma_wrwl_s2_buf;
wire            sctag_scbuf_rdma_rden_r0_buf;
wire    [1:0]   sctag_scbuf_rdma_rdwl_r0_buf;
wire            sctag_scbuf_ctag_en_c7_buf;
wire    [14:0]  sctag_scbuf_ctag_c7_buf;
wire            sctag_scbuf_req_en_c7_buf;
wire    [3:0]   sctag_scbuf_word_c7_buf;
wire            sctag_scbuf_word_vld_c7_buf;
wire            scbuf_sctag_ev_uerr_r5_buf;
wire            scbuf_sctag_ev_cerr_r5_buf;
wire            scbuf_sctag_rdma_uerr_c10_buf;
wire            scbuf_sctag_rdma_cerr_c10_buf;


//////////////////////////////////////////////////////////////////////////////
assign  sctag_scbuf_fbrd_en_c3_buf       = sctag_scbuf_fbrd_en_c3;
assign  sctag_scbuf_fbrd_wl_c3_buf       = sctag_scbuf_fbrd_wl_c3;
assign  sctag_scbuf_fbwr_wen_r2_buf      = sctag_scbuf_fbwr_wen_r2;
assign  sctag_scbuf_fbwr_wl_r2_buf       = sctag_scbuf_fbwr_wl_r2;
assign  sctag_scbuf_fbd_stdatasel_c3_buf = sctag_scbuf_fbd_stdatasel_c3;
assign  sctag_scbuf_stdecc_c3_buf        = sctag_scbuf_stdecc_c3;
assign  sctag_scbuf_ev_dword_r0_buf      = sctag_scbuf_ev_dword_r0;
assign  sctag_scbuf_evict_en_r0_buf      = sctag_scbuf_evict_en_r0;
assign  sctag_scbuf_wbwr_wen_c6_buf      = sctag_scbuf_wbwr_wen_c6;
assign  sctag_scbuf_wbwr_wl_c6_buf       = sctag_scbuf_wbwr_wl_c6;
assign  sctag_scbuf_wbrd_en_r0_buf       = sctag_scbuf_wbrd_en_r0;
assign  sctag_scbuf_wbrd_wl_r0_buf       = sctag_scbuf_wbrd_wl_r0;
assign  sctag_scbuf_rdma_wren_s2_buf     = sctag_scbuf_rdma_wren_s2;
assign  sctag_scbuf_rdma_wrwl_s2_buf     = sctag_scbuf_rdma_wrwl_s2;
assign  sctag_scbuf_rdma_rden_r0_buf     = sctag_scbuf_rdma_rden_r0;
assign  sctag_scbuf_rdma_rdwl_r0_buf     = sctag_scbuf_rdma_rdwl_r0;
assign  sctag_scbuf_ctag_en_c7_buf       = sctag_scbuf_ctag_en_c7;
assign  sctag_scbuf_ctag_c7_buf          = sctag_scbuf_ctag_c7;
assign  sctag_scbuf_req_en_c7_buf        = sctag_scbuf_req_en_c7;
assign  sctag_scbuf_word_c7_buf          = sctag_scbuf_word_c7;
assign  sctag_scbuf_word_vld_c7_buf      = sctag_scbuf_word_vld_c7;

assign  scbuf_sctag_ev_uerr_r5_buf       = scbuf_sctag_ev_uerr_r5;
assign  scbuf_sctag_ev_cerr_r5_buf       = scbuf_sctag_ev_cerr_r5;
assign  scbuf_sctag_rdma_uerr_c10_buf    = scbuf_sctag_rdma_uerr_c10;
assign  scbuf_sctag_rdma_cerr_c10_buf    = scbuf_sctag_rdma_cerr_c10;

endmodule
