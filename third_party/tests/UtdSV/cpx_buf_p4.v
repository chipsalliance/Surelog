// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: cpx_buf_p4.v
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
/*
//
//	Description:	datapath portion of CPX
*/
////////////////////////////////////////////////////////////////////////
// Global header file includes
////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////
// Local header file includes / local defines
////////////////////////////////////////////////////////////////////////

`include	"sys.h"
`include	"iop.h"
module cpx_buf_p4(/*AUTOARG*/
   // Outputs
   scache3_cpx_req_bufp4_cq, scache3_cpx_atom_bufp4_cq, 
   io_cpx_req_bufp4_cq, cpx_scache3_grant_bufp4_ca, 
   cpx_spc7_data_rdy_bufp4_cx, 
   // Inputs
   scache3_cpx_req_bufpt_cq_l, scache3_cpx_atom_bufpt_cq_l, 
   io_cpx_req_bufpt_cq_l, cpx_scache3_grant_bufp3_ca_l, 
   cpx_spc7_data_rdy_bufp3_cx
   );
   

   output [7:0]		scache3_cpx_req_bufp4_cq;	
   output 		scache3_cpx_atom_bufp4_cq;	
   output [7:0]		io_cpx_req_bufp4_cq;
   output [7:0]		cpx_scache3_grant_bufp4_ca;
   output     		cpx_spc7_data_rdy_bufp4_cx;
   
   
   input [7:0]		scache3_cpx_req_bufpt_cq_l;	
   input 		scache3_cpx_atom_bufpt_cq_l;	
   input [7:0]		io_cpx_req_bufpt_cq_l;
   input [7:0]		cpx_scache3_grant_bufp3_ca_l;
   input     		cpx_spc7_data_rdy_bufp3_cx;

   assign 		scache3_cpx_req_bufp4_cq[7:0]		=        ~scache3_cpx_req_bufpt_cq_l[7:0];
   assign 		scache3_cpx_atom_bufp4_cq		=        ~scache3_cpx_atom_bufpt_cq_l;
   assign 		io_cpx_req_bufp4_cq[7:0]		=        ~io_cpx_req_bufpt_cq_l[7:0];
   assign               cpx_scache3_grant_bufp4_ca              =        ~cpx_scache3_grant_bufp3_ca_l;
   assign     		cpx_spc7_data_rdy_bufp4_cx              =         cpx_spc7_data_rdy_bufp3_cx;
								

endmodule 
