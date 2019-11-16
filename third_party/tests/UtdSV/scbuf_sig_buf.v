// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: scbuf_sig_buf.v
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
module scbuf_sig_buf (/*AUTOARG*/
   // Outputs
   scbuf_scdata_fbdecc_c4, scbuf_dram_wr_data_r5, 
   scbuf_dram_data_vld_r5, scbuf_dram_data_mecc_r5, 
   scbuf_sctag_ev_uerr_r5, scbuf_sctag_ev_cerr_r5, 
   // Inputs
   scbuf_scdata_fbdecc_c4_pb, scbuf_dram_wr_data_r5_pb, 
   scbuf_dram_data_vld_r5_pb, scbuf_dram_data_mecc_r5_pb, 
   scbuf_sctag_ev_uerr_r5_pb, scbuf_sctag_ev_cerr_r5_pb
   );


output  [623:0]  scbuf_scdata_fbdecc_c4;
output  [63:0]   scbuf_dram_wr_data_r5;
output           scbuf_dram_data_vld_r5;
output           scbuf_dram_data_mecc_r5;
output           scbuf_sctag_ev_uerr_r5;
output           scbuf_sctag_ev_cerr_r5;

input   [623:0]  scbuf_scdata_fbdecc_c4_pb;
input   [63:0]   scbuf_dram_wr_data_r5_pb;
input            scbuf_dram_data_vld_r5_pb;
input            scbuf_dram_data_mecc_r5_pb;
input            scbuf_sctag_ev_uerr_r5_pb;
input            scbuf_sctag_ev_cerr_r5_pb;



assign scbuf_scdata_fbdecc_c4[623:0] = scbuf_scdata_fbdecc_c4_pb[623:0];
assign scbuf_dram_wr_data_r5[63:0]   = scbuf_dram_wr_data_r5_pb[63:0];
assign scbuf_dram_data_vld_r5        = scbuf_dram_data_vld_r5_pb;
assign scbuf_dram_data_mecc_r5       = scbuf_dram_data_mecc_r5_pb;
assign scbuf_sctag_ev_uerr_r5        = scbuf_sctag_ev_uerr_r5_pb;
assign scbuf_sctag_ev_cerr_r5        = scbuf_sctag_ev_cerr_r5_pb;

endmodule
