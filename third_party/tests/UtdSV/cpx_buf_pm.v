// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: cpx_buf_pm.v
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

module cpx_buf_pm(/*AUTOARG*/
   // Outputs
   cpx_scache_grant_bufpm_ca, scache_cpx_req_bufpm_cq, 
   scache_cpx_atom_bufpm_cq, 
   // Inputs
   cpx_scache_grant_ca, scache_cpx_req_bufpt_cq_l, 
   scache_cpx_atom_bufpt_cq_l
   );
   output [7:0]         cpx_scache_grant_bufpm_ca;
   output [7:0]		scache_cpx_req_bufpm_cq		        ;	
   output 		scache_cpx_atom_bufpm_cq		        ;	

   

   input [7:0]          cpx_scache_grant_ca;
   input [7:0]		scache_cpx_req_bufpt_cq_l;	
   input 		scache_cpx_atom_bufpt_cq_l;	

   
   assign               cpx_scache_grant_bufpm_ca      =                  cpx_scache_grant_ca;
   assign		scache_cpx_req_bufpm_cq[7:0]		=        ~scache_cpx_req_bufpt_cq_l[7:0];
   assign 		scache_cpx_atom_bufpm_cq		=        ~scache_cpx_atom_bufpt_cq_l;


endmodule 

