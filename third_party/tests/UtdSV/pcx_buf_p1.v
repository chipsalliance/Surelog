// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: pcx_buf_p1.v
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

module pcx_buf_p1(/*AUTOARG*/
   // Outputs
   scache0_pcx_stall_bufp1_pq, spc0_pcx_req_bufp1_pq, 
   spc0_pcx_atom_bufp1_pq, spc1_pcx_req_bufp1_pq, 
   spc1_pcx_atom_bufp1_pq, spc2_pcx_req_bufp1_pq, 
   spc2_pcx_atom_bufp1_pq, spc3_pcx_req_bufp1_pq, 
   spc3_pcx_atom_bufp1_pq, spc4_pcx_req_bufp1_pq, 
   spc4_pcx_atom_bufp1_pq, pcx_spc0_grant_bufp1_pa_l, 
   pcx_spc1_grant_bufp1_pa_l, pcx_spc2_grant_bufp1_pa_l, 
   arbpc0_pcxdp_grant_bufp1_pa_l, arbpc0_pcxdp_q0_hold_bufp1_pa, 
   arbpc0_pcxdp_qsel0_bufp1_pa_l, arbpc0_pcxdp_qsel1_bufp1_pa, 
   arbpc0_pcxdp_shift_bufp1_px_l, arbpc1_pcxdp_grant_bufp1_pa_l, 
   arbpc1_pcxdp_q0_hold_bufp1_pa, arbpc1_pcxdp_qsel0_bufp1_pa_l, 
   arbpc1_pcxdp_qsel1_bufp1_pa, arbpc1_pcxdp_shift_bufp1_px_l, 
   arbpc2_pcxdp_grant_bufp1_pa_l, arbpc2_pcxdp_q0_hold_bufp1_pa, 
   arbpc2_pcxdp_qsel0_bufp1_pa_l, arbpc2_pcxdp_qsel1_bufp1_pa, 
   arbpc2_pcxdp_shift_bufp1_px_l, arbpc3_pcxdp_grant_bufp1_pa_l, 
   arbpc3_pcxdp_q0_hold_bufp1_pa, arbpc3_pcxdp_qsel0_bufp1_pa_l, 
   arbpc3_pcxdp_qsel1_bufp1_pa, arbpc3_pcxdp_shift_bufp1_px_l, 
   arbpc4_pcxdp_grant_bufp1_pa_l, arbpc4_pcxdp_q0_hold_bufp1_pa, 
   arbpc4_pcxdp_qsel0_bufp1_pa_l, arbpc4_pcxdp_qsel1_bufp1_pa, 
   arbpc4_pcxdp_shift_bufp1_px_l, sctag1_pcx_stall_bufp1_pq, 
   // Inputs
   scache0_pcx_stall_bufp0even_pq, spc0_pcx_req_bufp0_pq, 
   spc0_pcx_atom_bufp0_pq, spc1_pcx_req_bufp0_pq, 
   spc1_pcx_atom_bufp0_pq, spc2_pcx_req_bufpt_pq_l, 
   spc2_pcx_atom_bufpt_pq_l, spc3_pcx_req_bufpt1_pq, 
   spc3_pcx_atom_bufpt1_pq, spc4_pcx_req_bufpt1_pq, 
   spc4_pcx_atom_bufpt1_pq, pcx_spc0_grant_pa, pcx_spc1_grant_pa, 
   pcx_spc2_grant_pa, arbpc0_pcxdp_grant_arbbf_pa, 
   arbpc0_pcxdp_q0_hold_arbbf_pa_l, arbpc0_pcxdp_qsel0_arbbf_pa, 
   arbpc0_pcxdp_qsel1_arbbf_pa_l, arbpc0_pcxdp_shift_arbbf_px, 
   arbpc1_pcxdp_grant_arbbf_pa, arbpc1_pcxdp_q0_hold_arbbf_pa_l, 
   arbpc1_pcxdp_qsel0_arbbf_pa, arbpc1_pcxdp_qsel1_arbbf_pa_l, 
   arbpc1_pcxdp_shift_arbbf_px, arbpc2_pcxdp_grant_arbbf_pa, 
   arbpc2_pcxdp_q0_hold_arbbf_pa_l, arbpc2_pcxdp_qsel0_arbbf_pa, 
   arbpc2_pcxdp_qsel1_arbbf_pa_l, arbpc2_pcxdp_shift_arbbf_px, 
   arbpc3_pcxdp_grant_arbbf_pa, arbpc3_pcxdp_q0_hold_arbbf_pa_l, 
   arbpc3_pcxdp_qsel0_arbbf_pa, arbpc3_pcxdp_qsel1_arbbf_pa_l, 
   arbpc3_pcxdp_shift_arbbf_px, arbpc4_pcxdp_grant_arbbf_pa, 
   arbpc4_pcxdp_q0_hold_arbbf_pa_l, arbpc4_pcxdp_qsel0_arbbf_pa, 
   arbpc4_pcxdp_qsel1_arbbf_pa_l, arbpc4_pcxdp_shift_arbbf_px, 
   sctag1_pcx_stall_bufp0odd_pq
   );
   
   output               scache0_pcx_stall_bufp1_pq		; 
   output [4:0]		spc0_pcx_req_bufp1_pq		        ;	
   output 		spc0_pcx_atom_bufp1_pq		        ;	
   output [4:0]		spc1_pcx_req_bufp1_pq		        ;	
   output 		spc1_pcx_atom_bufp1_pq		        ;	
   output [4:0]		spc2_pcx_req_bufp1_pq		        ;	
   output 		spc2_pcx_atom_bufp1_pq		        ;	
   output [4:0]		spc3_pcx_req_bufp1_pq		        ;	
   output 		spc3_pcx_atom_bufp1_pq		        ;	
   output [4:0]		spc4_pcx_req_bufp1_pq		        ;	
   output 		spc4_pcx_atom_bufp1_pq		        ;	
   output [4:0] 	pcx_spc0_grant_bufp1_pa_l;
   output [4:0] 	pcx_spc1_grant_bufp1_pa_l;
   output [4:0] 	pcx_spc2_grant_bufp1_pa_l;
   
   

   output [2:0] 		arbpc0_pcxdp_grant_bufp1_pa_l;	
   output [2:0] 		arbpc0_pcxdp_q0_hold_bufp1_pa;
   output [2:0] 		arbpc0_pcxdp_qsel0_bufp1_pa_l;	
   output [2:0] 		arbpc0_pcxdp_qsel1_bufp1_pa;	
   output [2:0] 		arbpc0_pcxdp_shift_bufp1_px_l;	
							     
   output [2:0] 		arbpc1_pcxdp_grant_bufp1_pa_l;	
   output [2:0] 		arbpc1_pcxdp_q0_hold_bufp1_pa;
   output [2:0] 		arbpc1_pcxdp_qsel0_bufp1_pa_l;	
   output [2:0] 		arbpc1_pcxdp_qsel1_bufp1_pa;	
   output [2:0] 		arbpc1_pcxdp_shift_bufp1_px_l;	
							     
   output [2:0] 		arbpc2_pcxdp_grant_bufp1_pa_l;	
   output [2:0] 		arbpc2_pcxdp_q0_hold_bufp1_pa;
   output [2:0] 		arbpc2_pcxdp_qsel0_bufp1_pa_l;	
   output [2:0] 		arbpc2_pcxdp_qsel1_bufp1_pa;	
   output [2:0] 		arbpc2_pcxdp_shift_bufp1_px_l;	
							     
   output [2:0] 		arbpc3_pcxdp_grant_bufp1_pa_l;	
   output [2:0] 		arbpc3_pcxdp_q0_hold_bufp1_pa;
   output [2:0] 		arbpc3_pcxdp_qsel0_bufp1_pa_l;	
   output [2:0] 		arbpc3_pcxdp_qsel1_bufp1_pa;	
   output [2:0] 		arbpc3_pcxdp_shift_bufp1_px_l;	
							     
   output [2:0] 		arbpc4_pcxdp_grant_bufp1_pa_l;	
   output [2:0] 		arbpc4_pcxdp_q0_hold_bufp1_pa;
   output [2:0] 		arbpc4_pcxdp_qsel0_bufp1_pa_l;	
   output [2:0] 		arbpc4_pcxdp_qsel1_bufp1_pa;	
   output [2:0] 		arbpc4_pcxdp_shift_bufp1_px_l;	
							     
   output 		        sctag1_pcx_stall_bufp1_pq;	
   

   input                scache0_pcx_stall_bufp0even_pq ; 
   input [4:0]		spc0_pcx_req_bufp0_pq;	
   input 		spc0_pcx_atom_bufp0_pq;	
   input [4:0]		spc1_pcx_req_bufp0_pq;	
   input 		spc1_pcx_atom_bufp0_pq;	
   input [4:0]		spc2_pcx_req_bufpt_pq_l;	
   input 		spc2_pcx_atom_bufpt_pq_l;	
   input [4:0]		spc3_pcx_req_bufpt1_pq;	
   input 		spc3_pcx_atom_bufpt1_pq;	
   input [4:0]		spc4_pcx_req_bufpt1_pq;	
   input 		spc4_pcx_atom_bufpt1_pq;	
   input [4:0] 		pcx_spc0_grant_pa;
   input [4:0] 		pcx_spc1_grant_pa;
   input [4:0] 		pcx_spc2_grant_pa;

   
   input [2:0]		arbpc0_pcxdp_grant_arbbf_pa;	
   input [2:0]		arbpc0_pcxdp_q0_hold_arbbf_pa_l;
   input [2:0]		arbpc0_pcxdp_qsel0_arbbf_pa;	
   input [2:0]		arbpc0_pcxdp_qsel1_arbbf_pa_l;	
   input [2:0]		arbpc0_pcxdp_shift_arbbf_px;	

   input [2:0]		arbpc1_pcxdp_grant_arbbf_pa;	
   input [2:0]		arbpc1_pcxdp_q0_hold_arbbf_pa_l;
   input [2:0]		arbpc1_pcxdp_qsel0_arbbf_pa;	
   input [2:0]		arbpc1_pcxdp_qsel1_arbbf_pa_l;	
   input [2:0]		arbpc1_pcxdp_shift_arbbf_px;	

   input [2:0]		arbpc2_pcxdp_grant_arbbf_pa;	
   input [2:0]		arbpc2_pcxdp_q0_hold_arbbf_pa_l;
   input [2:0]		arbpc2_pcxdp_qsel0_arbbf_pa;	
   input [2:0]		arbpc2_pcxdp_qsel1_arbbf_pa_l;	
   input [2:0]		arbpc2_pcxdp_shift_arbbf_px;	

   input [2:0]		arbpc3_pcxdp_grant_arbbf_pa;	
   input [2:0]		arbpc3_pcxdp_q0_hold_arbbf_pa_l;
   input [2:0]		arbpc3_pcxdp_qsel0_arbbf_pa;	
   input [2:0]		arbpc3_pcxdp_qsel1_arbbf_pa_l;	
   input [2:0]		arbpc3_pcxdp_shift_arbbf_px;	

   input [2:0]		arbpc4_pcxdp_grant_arbbf_pa;	
   input [2:0]		arbpc4_pcxdp_q0_hold_arbbf_pa_l;
   input [2:0]		arbpc4_pcxdp_qsel0_arbbf_pa;	
   input [2:0]		arbpc4_pcxdp_qsel1_arbbf_pa_l;	
   input [2:0]		arbpc4_pcxdp_shift_arbbf_px;	

   input 		sctag1_pcx_stall_bufp0odd_pq;	

   


   assign		sctag1_pcx_stall_bufp1_pq		=        sctag1_pcx_stall_bufp0odd_pq;

   assign		scache0_pcx_stall_bufp1_pq		=        scache0_pcx_stall_bufp0even_pq;
   assign		spc0_pcx_req_bufp1_pq[4:0]		=        spc0_pcx_req_bufp0_pq[4:0];
   assign 		spc0_pcx_atom_bufp1_pq			=        spc0_pcx_atom_bufp0_pq;
   assign		spc1_pcx_req_bufp1_pq[4:0]		=        spc1_pcx_req_bufp0_pq[4:0];
   assign 		spc1_pcx_atom_bufp1_pq			=        spc1_pcx_atom_bufp0_pq;
   assign		spc2_pcx_req_bufp1_pq[4:0]		=        ~spc2_pcx_req_bufpt_pq_l[4:0];
   assign 		spc2_pcx_atom_bufp1_pq			=        ~spc2_pcx_atom_bufpt_pq_l;
   assign		spc3_pcx_req_bufp1_pq[4:0]		=        spc3_pcx_req_bufpt1_pq[4:0];
   assign 		spc3_pcx_atom_bufp1_pq			=        spc3_pcx_atom_bufpt1_pq;
   assign		spc4_pcx_req_bufp1_pq[4:0]		=        spc4_pcx_req_bufpt1_pq[4:0];
   assign 		spc4_pcx_atom_bufp1_pq			=        spc4_pcx_atom_bufpt1_pq;
   assign               pcx_spc0_grant_bufp1_pa_l[4:0]          =        ~pcx_spc0_grant_pa[4:0];
   assign               pcx_spc1_grant_bufp1_pa_l[4:0]          =        ~pcx_spc1_grant_pa[4:0];
   assign               pcx_spc2_grant_bufp1_pa_l[4:0]          =        ~pcx_spc2_grant_pa[4:0];
   
								
   assign		arbpc0_pcxdp_grant_bufp1_pa_l	   =       ~arbpc0_pcxdp_grant_arbbf_pa;      	
   assign		arbpc0_pcxdp_q0_hold_bufp1_pa	   =       ~arbpc0_pcxdp_q0_hold_arbbf_pa_l;  
   assign		arbpc0_pcxdp_qsel0_bufp1_pa_l	   =       ~arbpc0_pcxdp_qsel0_arbbf_pa;      
   assign		arbpc0_pcxdp_qsel1_bufp1_pa	   =       ~arbpc0_pcxdp_qsel1_arbbf_pa_l;    
   assign		arbpc0_pcxdp_shift_bufp1_px_l	   =       ~arbpc0_pcxdp_shift_arbbf_px;      
								                                                  
   assign		arbpc1_pcxdp_grant_bufp1_pa_l	   =       ~arbpc1_pcxdp_grant_arbbf_pa;      	
   assign		arbpc1_pcxdp_q0_hold_bufp1_pa	   =       ~arbpc1_pcxdp_q0_hold_arbbf_pa_l;  
   assign		arbpc1_pcxdp_qsel0_bufp1_pa_l	   =       ~arbpc1_pcxdp_qsel0_arbbf_pa;      
   assign		arbpc1_pcxdp_qsel1_bufp1_pa	   =       ~arbpc1_pcxdp_qsel1_arbbf_pa_l;    
   assign		arbpc1_pcxdp_shift_bufp1_px_l	   =       ~arbpc1_pcxdp_shift_arbbf_px;      
								                                                  
   assign		arbpc2_pcxdp_grant_bufp1_pa_l	   =       ~arbpc2_pcxdp_grant_arbbf_pa;      	
   assign		arbpc2_pcxdp_q0_hold_bufp1_pa	   =       ~arbpc2_pcxdp_q0_hold_arbbf_pa_l;  
   assign		arbpc2_pcxdp_qsel0_bufp1_pa_l	   =       ~arbpc2_pcxdp_qsel0_arbbf_pa;      
   assign		arbpc2_pcxdp_qsel1_bufp1_pa	   =       ~arbpc2_pcxdp_qsel1_arbbf_pa_l;    
   assign		arbpc2_pcxdp_shift_bufp1_px_l	   =       ~arbpc2_pcxdp_shift_arbbf_px;      
								                                                  
   assign		arbpc3_pcxdp_grant_bufp1_pa_l	   =       ~arbpc3_pcxdp_grant_arbbf_pa;      	
   assign		arbpc3_pcxdp_q0_hold_bufp1_pa	   =       ~arbpc3_pcxdp_q0_hold_arbbf_pa_l;  
   assign		arbpc3_pcxdp_qsel0_bufp1_pa_l	   =       ~arbpc3_pcxdp_qsel0_arbbf_pa;      
   assign		arbpc3_pcxdp_qsel1_bufp1_pa	   =       ~arbpc3_pcxdp_qsel1_arbbf_pa_l;    
   assign		arbpc3_pcxdp_shift_bufp1_px_l	   =       ~arbpc3_pcxdp_shift_arbbf_px;      
								                                                  
   assign		arbpc4_pcxdp_grant_bufp1_pa_l	   =       ~arbpc4_pcxdp_grant_arbbf_pa;      	
   assign		arbpc4_pcxdp_q0_hold_bufp1_pa	   =       ~arbpc4_pcxdp_q0_hold_arbbf_pa_l;  
   assign		arbpc4_pcxdp_qsel0_bufp1_pa_l	   =       ~arbpc4_pcxdp_qsel0_arbbf_pa;      
   assign		arbpc4_pcxdp_qsel1_bufp1_pa	   =       ~arbpc4_pcxdp_qsel1_arbbf_pa_l;    
   assign		arbpc4_pcxdp_shift_bufp1_px_l	   =       ~arbpc4_pcxdp_shift_arbbf_px;      
								                                                  

        
   

endmodule // pcx_grant_ff

