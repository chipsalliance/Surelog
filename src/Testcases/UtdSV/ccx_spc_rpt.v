// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: ccx_spc_rpt.v
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
`include "sys.h"
`include "iop.h"

module ccx_spc_rpt (/*AUTOARG*/
   // Outputs
   spc_pcx_req_pq_buf, spc_pcx_atom_pq_buf, spc_pcx_data_pa_buf, 
   pcx_spc_grant_px_buf, cpx_spc_data_cx2_buf, 
   cpx_spc_data_rdy_cx2_buf, 
   // Inputs
   spc_pcx_req_pq, spc_pcx_atom_pq, spc_pcx_data_pa, 
   pcx_spc_grant_px, cpx_spc_data_cx2, cpx_spc_data_rdy_cx2
   );


input  [4:0]            spc_pcx_req_pq;
input                   spc_pcx_atom_pq;
input  [`PCX_WIDTH-1:0] spc_pcx_data_pa;
input  [4:0]            pcx_spc_grant_px;
   
input  [`CPX_WIDTH-1:0] cpx_spc_data_cx2;      
input                   cpx_spc_data_rdy_cx2;

output [4:0]            spc_pcx_req_pq_buf;
output                  spc_pcx_atom_pq_buf;
output [`PCX_WIDTH-1:0] spc_pcx_data_pa_buf;
output  [4:0]            pcx_spc_grant_px_buf;
   
output [`CPX_WIDTH-1:0] cpx_spc_data_cx2_buf;
output                  cpx_spc_data_rdy_cx2_buf;    

   
assign  spc_pcx_req_pq_buf  =  spc_pcx_req_pq;
assign  spc_pcx_atom_pq_buf  =  spc_pcx_atom_pq;
assign  spc_pcx_data_pa_buf   =  spc_pcx_data_pa;
assign  pcx_spc_grant_px_buf  =  pcx_spc_grant_px;
assign  cpx_spc_data_cx2_buf  =  cpx_spc_data_cx2;
assign  cpx_spc_data_rdy_cx2_buf  =  cpx_spc_data_rdy_cx2;


endmodule   
