// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: pcx_buf_p4.v
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

module pcx_buf_p4(/*AUTOARG*/
   // Outputs
   pcx_spc7_grant_bufp4_pa, spc6_pcx_req_bufp4_pq, 
   spc6_pcx_atom_bufp4_pq, spc7_pcx_req_bufp4_pq, 
   spc7_pcx_atom_bufp4_pq, 
   // Inputs
   spc6_pcx_req_bufpt_pq_l, spc6_pcx_atom_bufpt_pq_l, 
   spc7_pcx_req_bufpt_pq_l, spc7_pcx_atom_bufpt_pq_l, 
   pcx_spc7_grant_bufp3_pa_l
   );
   
   output [4:0]		pcx_spc7_grant_bufp4_pa;
   output [4:0]		spc6_pcx_req_bufp4_pq;	
   output 		spc6_pcx_atom_bufp4_pq;	
   output [4:0]		spc7_pcx_req_bufp4_pq;	
   output 		spc7_pcx_atom_bufp4_pq;	


   input [4:0]		spc6_pcx_req_bufpt_pq_l;	
   input 		spc6_pcx_atom_bufpt_pq_l;	
   input [4:0]		spc7_pcx_req_bufpt_pq_l;	
   input 		spc7_pcx_atom_bufpt_pq_l;	
   input [4:0]		pcx_spc7_grant_bufp3_pa_l;


   assign               pcx_spc7_grant_bufp4_pa                 =        ~pcx_spc7_grant_bufp3_pa_l;
   assign        	spc6_pcx_req_bufp4_pq[4:0]		=        ~spc6_pcx_req_bufpt_pq_l[4:0];
   assign 		spc6_pcx_atom_bufp4_pq			=        ~spc6_pcx_atom_bufpt_pq_l;
   assign        	spc7_pcx_req_bufp4_pq[4:0]		=        ~spc7_pcx_req_bufpt_pq_l[4:0];
   assign 		spc7_pcx_atom_bufp4_pq			=        ~spc7_pcx_atom_bufpt_pq_l;

								                                    
   
endmodule 
