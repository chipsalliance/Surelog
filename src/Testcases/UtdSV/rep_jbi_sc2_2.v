// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: rep_jbi_sc2_2.v
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
module rep_jbi_sc2_2(/*AUTOARG*/
   // Outputs
   jbi_sctag_req_buf, scbuf_jbi_data_buf, jbi_scbuf_ecc_buf, 
   jbi_sctag_req_vld_buf, scbuf_jbi_ctag_vld_buf, 
   scbuf_jbi_ue_err_buf, sctag_jbi_iq_dequeue_buf, 
   sctag_jbi_wib_dequeue_buf, sctag_jbi_por_req_buf, 
   // Inputs
   jbi_sctag_req, scbuf_jbi_data, jbi_scbuf_ecc, jbi_sctag_req_vld, 
   scbuf_jbi_ctag_vld, scbuf_jbi_ue_err, sctag_jbi_iq_dequeue, 
   sctag_jbi_wib_dequeue, sctag_jbi_por_req
   );

   output [31:0]        jbi_sctag_req_buf;         
   output [31:0]        scbuf_jbi_data_buf;        
   output [6:0]         jbi_scbuf_ecc_buf;         
   output               jbi_sctag_req_vld_buf;     
   output               scbuf_jbi_ctag_vld_buf;
   output               scbuf_jbi_ue_err_buf;      
   output		sctag_jbi_iq_dequeue_buf;
   output		sctag_jbi_wib_dequeue_buf;
   output		sctag_jbi_por_req_buf;

   input [31:0]        jbi_sctag_req;         
   input [31:0]        scbuf_jbi_data;        
   input [6:0]         jbi_scbuf_ecc;         
   input               jbi_sctag_req_vld;     
   input               scbuf_jbi_ctag_vld;
   input               scbuf_jbi_ue_err;      
   input	       sctag_jbi_iq_dequeue;
   input	       sctag_jbi_wib_dequeue;
   input	       sctag_jbi_por_req;

// This repeater bank is a row of flops 
// There are a maximum of 10 flops per row.


assign		jbi_sctag_req_buf = jbi_sctag_req ;
assign		scbuf_jbi_data_buf = scbuf_jbi_data ;
assign		jbi_scbuf_ecc_buf[6:0] = jbi_scbuf_ecc[6:0] ;
assign		jbi_sctag_req_vld_buf = jbi_sctag_req_vld ;
assign		scbuf_jbi_ctag_vld_buf = scbuf_jbi_ctag_vld ;
assign		scbuf_jbi_ue_err_buf = scbuf_jbi_ue_err ;
assign		sctag_jbi_iq_dequeue_buf = sctag_jbi_iq_dequeue ;
assign		sctag_jbi_wib_dequeue_buf =  sctag_jbi_wib_dequeue;
assign		sctag_jbi_por_req_buf = sctag_jbi_por_req ;

endmodule

