// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_cpx_rptr_0.v
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
module sctag_cpx_rptr_0 (/*AUTOARG*/
   // Outputs
   sig_buf, 
   // Inputs
   sig
   );

// this repeater has 164 bits

output	[163:0]	sig_buf;
input	[163:0]	sig;


assign	sig_buf  = sig;

//output [7:0]             sctag_cpx_req_cq_buf;   // sctag to processor request
//output                   sctag_cpx_atom_cq_buf;
//output [`CPX_WIDTH-1:0]  sctag_cpx_data_ca_buf;  // sctag to cpx data pkt
//output [7:0]             cpx_sctag_grant_cx_buf; 

//input [7:0]             sctag_cpx_req_cq;   // sctag to processor request
//input                   sctag_cpx_atom_cq;
//input [`CPX_WIDTH-1:0]  sctag_cpx_data_ca;  // sctag to cpx data pkt
//input [7:0]             cpx_sctag_grant_cx; 


//assign	sctag_cpx_atom_cq_buf = sctag_cpx_atom_cq; 
//assign	sctag_cpx_data_ca_buf = sctag_cpx_data_ca;
//assign	cpx_sctag_grant_cx_buf = cpx_sctag_grant_cx;
//assign	sctag_cpx_req_cq_buf = sctag_cpx_req_cq;

endmodule
