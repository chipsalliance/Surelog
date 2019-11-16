// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: ff_jbi_sc3_2.v
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
module ff_jbi_sc3_2(/*AUTOARG*/
   // Outputs
   jbi_sctag_req_d1, scbuf_jbi_data_d1, jbi_scbuf_ecc_d1, 
   jbi_sctag_req_vld_d1, scbuf_jbi_ctag_vld_d1, scbuf_jbi_ue_err_d1, 
   sctag_jbi_iq_dequeue_d1, sctag_jbi_wib_dequeue_d1, 
   sctag_jbi_por_req_d1, so, 
   // Inputs
   jbi_sctag_req, scbuf_jbi_data, jbi_scbuf_ecc, jbi_sctag_req_vld, 
   scbuf_jbi_ctag_vld, scbuf_jbi_ue_err, sctag_jbi_iq_dequeue, 
   sctag_jbi_wib_dequeue, sctag_jbi_por_req, rclk, si, se
   );

   output [31:0]        jbi_sctag_req_d1;         
   output [31:0]        scbuf_jbi_data_d1;        
   output [6:0]         jbi_scbuf_ecc_d1;         
   output               jbi_sctag_req_vld_d1;     
   output               scbuf_jbi_ctag_vld_d1;
   output               scbuf_jbi_ue_err_d1;      
   output		sctag_jbi_iq_dequeue_d1;
   output		sctag_jbi_wib_dequeue_d1;
   output		sctag_jbi_por_req_d1;

   input [31:0]        jbi_sctag_req;         
   input [31:0]        scbuf_jbi_data;        
   input [6:0]         jbi_scbuf_ecc;         
   input               jbi_sctag_req_vld;     
   input               scbuf_jbi_ctag_vld;
   input               scbuf_jbi_ue_err;      
   input	       sctag_jbi_iq_dequeue;
   input	       sctag_jbi_wib_dequeue;
   input	       sctag_jbi_por_req;

   input		rclk;
   input		si, se;

   output		so;

   wire	int_scanout;

   // connect scanout of the last flop to int_scanout.
   // The output of the lockup latch is
   // the scanout of this dbb (so)

   bw_u1_scanlg_2x so_lockup(.so(so), .sd(int_scanout), .ck(rclk), .se(se));



   dff_s	#(32)	ff_flop_row0	(.q(jbi_sctag_req_d1[31:0]),
				 .din(jbi_sctag_req[31:0]),
				 .clk(rclk), .se(1'b0), .si(), .so() );

   dff_s	#(32)	ff_flop_row1	(.q(scbuf_jbi_data_d1[31:0]),
				 .din(scbuf_jbi_data[31:0]),
				 .clk(rclk), .se(1'b0), .si(), .so() );

   dff_s	#(13)	ff_flop_row2	(.q({  	jbi_scbuf_ecc_d1[6:0],
					jbi_sctag_req_vld_d1, 
					scbuf_jbi_ctag_vld_d1,
					scbuf_jbi_ue_err_d1,
					sctag_jbi_iq_dequeue_d1,
					sctag_jbi_wib_dequeue_d1,
					sctag_jbi_por_req_d1}),
				 .din({ jbi_scbuf_ecc[6:0],
					jbi_sctag_req_vld, 
					scbuf_jbi_ctag_vld,
					scbuf_jbi_ue_err,
					sctag_jbi_iq_dequeue,
					sctag_jbi_wib_dequeue,
					sctag_jbi_por_req}),
				 .clk(rclk), .se(1'b0), .si(), .so() );


endmodule
