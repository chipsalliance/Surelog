// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: cpx_buf_p0.v
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
//  Module Name: cpx_buf_p0
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
module cpx_buf_p0(/*AUTOARG*/
   // Outputs
   scache0_cpx_req_bufp0_cq, scache0_cpx_atom_bufp0_cq, 
   cpx_scache0_grant_bufp0_ca, cpx_spc0_data_rdy_bufp0_cx, 
   // Inputs
   scache0_cpx_req_bufpt_cq_l, scache0_cpx_atom_bufpt_cq_l, 
   cpx_scache0_grant_bufp1_ca_l, cpx_spc0_data_rdy_bufp1_cx
   );
   
   
   output [7:0]		scache0_cpx_req_bufp0_cq;	
   output 		scache0_cpx_atom_bufp0_cq;	
   output [7:0]		cpx_scache0_grant_bufp0_ca;
   output 		cpx_spc0_data_rdy_bufp0_cx;
   
   
   input [7:0]		scache0_cpx_req_bufpt_cq_l;	
   input 		scache0_cpx_atom_bufpt_cq_l;	
   input [7:0]		cpx_scache0_grant_bufp1_ca_l;
   input 		cpx_spc0_data_rdy_bufp1_cx;


   assign 		scache0_cpx_req_bufp0_cq[7:0]		=        ~scache0_cpx_req_bufpt_cq_l[7:0];
   assign 		scache0_cpx_atom_bufp0_cq		=        ~scache0_cpx_atom_bufpt_cq_l;
   assign               cpx_scache0_grant_bufp0_ca              =        ~cpx_scache0_grant_bufp1_ca_l;
   assign     		cpx_spc0_data_rdy_bufp0_cx              =	 cpx_spc0_data_rdy_bufp1_cx;
								

endmodule 
