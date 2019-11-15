// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: pcx_buf_p3.v
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

module pcx_buf_p3(/*AUTOARG*/
   // Outputs
   scache3_pcx_stall_bufp3_pq, spc7_pcx_req_bufp3_pq, 
   spc7_pcx_atom_bufp3_pq, spc6_pcx_req_bufp3_pq, 
   spc6_pcx_atom_bufp3_pq, spc5_pcx_req_bufp3_pq, 
   spc5_pcx_atom_bufp3_pq, pcx_spc5_grant_bufp3_pa_l, 
   pcx_spc6_grant_bufp3_pa_l, pcx_spc7_grant_bufp3_pa_l, 
   arbpc0_pcxdp_grant_bufp3_pa_l, arbpc0_pcxdp_q0_hold_bufp3_pa, 
   arbpc0_pcxdp_qsel0_bufp3_pa_l, arbpc0_pcxdp_qsel1_bufp3_pa, 
   arbpc0_pcxdp_shift_bufp3_px_l, arbpc1_pcxdp_grant_bufp3_pa_l, 
   arbpc1_pcxdp_q0_hold_bufp3_pa, arbpc1_pcxdp_qsel0_bufp3_pa_l, 
   arbpc1_pcxdp_qsel1_bufp3_pa, arbpc1_pcxdp_shift_bufp3_px_l, 
   arbpc2_pcxdp_grant_bufp3_pa_l, arbpc2_pcxdp_q0_hold_bufp3_pa, 
   arbpc2_pcxdp_qsel0_bufp3_pa_l, arbpc2_pcxdp_qsel1_bufp3_pa, 
   arbpc2_pcxdp_shift_bufp3_px_l, arbpc3_pcxdp_grant_bufp3_pa_l, 
   arbpc3_pcxdp_q0_hold_bufp3_pa, arbpc3_pcxdp_qsel0_bufp3_pa_l, 
   arbpc3_pcxdp_qsel1_bufp3_pa, arbpc3_pcxdp_shift_bufp3_px_l, 
   arbpc4_pcxdp_grant_bufp3_pa_l, arbpc4_pcxdp_q0_hold_bufp3_pa, 
   arbpc4_pcxdp_qsel0_bufp3_pa_l, arbpc4_pcxdp_qsel1_bufp3_pa, 
   arbpc4_pcxdp_shift_bufp3_px_l, 
   // Inputs
   scache3_pcx_stall_pq, spc7_pcx_req_bufp4_pq, 
   spc7_pcx_atom_bufp4_pq, spc6_pcx_req_bufp4_pq, 
   spc6_pcx_atom_bufp4_pq, spc5_pcx_req_bufpt_pq_l, 
   spc5_pcx_atom_bufpt_pq_l, pcx_spc5_grant_pa, pcx_spc6_grant_pa, 
   pcx_spc7_grant_pa, arbpc0_pcxdp_grant_arbbf_pa, 
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
   arbpc4_pcxdp_qsel1_arbbf_pa_l, arbpc4_pcxdp_shift_arbbf_px
   );
   
   output               scache3_pcx_stall_bufp3_pq		; 
   output [4:0]		spc7_pcx_req_bufp3_pq		        ;	
   output 		spc7_pcx_atom_bufp3_pq		        ;	
   output [4:0]		spc6_pcx_req_bufp3_pq		        ;	
   output 		spc6_pcx_atom_bufp3_pq		        ;	
   output [4:0]		spc5_pcx_req_bufp3_pq		        ;	
   output 		spc5_pcx_atom_bufp3_pq		        ;	
   output [4:0] 	pcx_spc5_grant_bufp3_pa_l;
   output [4:0] 	pcx_spc6_grant_bufp3_pa_l;
   output [4:0] 	pcx_spc7_grant_bufp3_pa_l;


   output [7:5] 		arbpc0_pcxdp_grant_bufp3_pa_l		;	
   output [7:5] 		arbpc0_pcxdp_q0_hold_bufp3_pa		;
   output [7:5] 		arbpc0_pcxdp_qsel0_bufp3_pa_l		;	
   output [7:5] 		arbpc0_pcxdp_qsel1_bufp3_pa		;	
   output [7:5] 		arbpc0_pcxdp_shift_bufp3_px_l		;	

   output [7:5] 		arbpc1_pcxdp_grant_bufp3_pa_l		;	
   output [7:5] 		arbpc1_pcxdp_q0_hold_bufp3_pa		;
   output [7:5] 		arbpc1_pcxdp_qsel0_bufp3_pa_l		;	
   output [7:5] 		arbpc1_pcxdp_qsel1_bufp3_pa		;	
   output [7:5] 		arbpc1_pcxdp_shift_bufp3_px_l		;	

   output [7:5] 		arbpc2_pcxdp_grant_bufp3_pa_l		;	
   output [7:5] 		arbpc2_pcxdp_q0_hold_bufp3_pa		;
   output [7:5] 		arbpc2_pcxdp_qsel0_bufp3_pa_l		;	
   output [7:5] 		arbpc2_pcxdp_qsel1_bufp3_pa		;	
   output [7:5] 		arbpc2_pcxdp_shift_bufp3_px_l		;	

   output [7:5] 		arbpc3_pcxdp_grant_bufp3_pa_l		;	
   output [7:5] 		arbpc3_pcxdp_q0_hold_bufp3_pa		;
   output [7:5] 		arbpc3_pcxdp_qsel0_bufp3_pa_l		;	
   output [7:5] 		arbpc3_pcxdp_qsel1_bufp3_pa		;	
   output [7:5] 		arbpc3_pcxdp_shift_bufp3_px_l		;	

   output [7:5] 		arbpc4_pcxdp_grant_bufp3_pa_l		;	
   output [7:5] 		arbpc4_pcxdp_q0_hold_bufp3_pa		;
   output [7:5] 		arbpc4_pcxdp_qsel0_bufp3_pa_l		;	
   output [7:5] 		arbpc4_pcxdp_qsel1_bufp3_pa		;	
   output [7:5] 		arbpc4_pcxdp_shift_bufp3_px_l		;	


   input                scache3_pcx_stall_pq ; 
   input [4:0]		spc7_pcx_req_bufp4_pq;	
   input 		spc7_pcx_atom_bufp4_pq;	
   input [4:0]		spc6_pcx_req_bufp4_pq;	
   input 		spc6_pcx_atom_bufp4_pq;	
   input [4:0]		spc5_pcx_req_bufpt_pq_l;	
   input 		spc5_pcx_atom_bufpt_pq_l;	
   input [4:0] 		pcx_spc5_grant_pa;
   input [4:0] 		pcx_spc6_grant_pa;
   input [4:0] 		pcx_spc7_grant_pa;

   
   input [7:5]		arbpc0_pcxdp_grant_arbbf_pa;	
   input [7:5]		arbpc0_pcxdp_q0_hold_arbbf_pa_l;
   input [7:5]		arbpc0_pcxdp_qsel0_arbbf_pa;	
   input [7:5]		arbpc0_pcxdp_qsel1_arbbf_pa_l;	
   input [7:5]		arbpc0_pcxdp_shift_arbbf_px;	

   input [7:5]		arbpc1_pcxdp_grant_arbbf_pa;	
   input [7:5]		arbpc1_pcxdp_q0_hold_arbbf_pa_l;
   input [7:5]		arbpc1_pcxdp_qsel0_arbbf_pa;	
   input [7:5]		arbpc1_pcxdp_qsel1_arbbf_pa_l;	
   input [7:5]		arbpc1_pcxdp_shift_arbbf_px;	

   input [7:5]		arbpc2_pcxdp_grant_arbbf_pa;	
   input [7:5]		arbpc2_pcxdp_q0_hold_arbbf_pa_l;
   input [7:5]		arbpc2_pcxdp_qsel0_arbbf_pa;	
   input [7:5]		arbpc2_pcxdp_qsel1_arbbf_pa_l;	
   input [7:5]		arbpc2_pcxdp_shift_arbbf_px;	

   input [7:5]		arbpc3_pcxdp_grant_arbbf_pa;	
   input [7:5]		arbpc3_pcxdp_q0_hold_arbbf_pa_l;
   input [7:5]		arbpc3_pcxdp_qsel0_arbbf_pa;	
   input [7:5]		arbpc3_pcxdp_qsel1_arbbf_pa_l;	
   input [7:5]		arbpc3_pcxdp_shift_arbbf_px;	

   input [7:5]		arbpc4_pcxdp_grant_arbbf_pa;	
   input [7:5]		arbpc4_pcxdp_q0_hold_arbbf_pa_l;
   input [7:5]		arbpc4_pcxdp_qsel0_arbbf_pa;	
   input [7:5]		arbpc4_pcxdp_qsel1_arbbf_pa_l;	
   input [7:5]		arbpc4_pcxdp_shift_arbbf_px;	

   


   assign		scache3_pcx_stall_bufp3_pq		=        scache3_pcx_stall_pq;
   assign		spc7_pcx_req_bufp3_pq[4:0]		=        spc7_pcx_req_bufp4_pq[4:0];
   assign 		spc7_pcx_atom_bufp3_pq			=        spc7_pcx_atom_bufp4_pq;
   assign		spc6_pcx_req_bufp3_pq[4:0]		=        spc6_pcx_req_bufp4_pq[4:0];
   assign 		spc6_pcx_atom_bufp3_pq			=        spc6_pcx_atom_bufp4_pq;
   assign		spc5_pcx_req_bufp3_pq[4:0]		=        ~spc5_pcx_req_bufpt_pq_l[4:0];
   assign 		spc5_pcx_atom_bufp3_pq			=        ~spc5_pcx_atom_bufpt_pq_l;
   assign               pcx_spc5_grant_bufp3_pa_l[4:0]          =        ~pcx_spc5_grant_pa[4:0];
   assign               pcx_spc6_grant_bufp3_pa_l[4:0]          =        ~pcx_spc6_grant_pa[4:0];
   assign               pcx_spc7_grant_bufp3_pa_l[4:0]          =        ~pcx_spc7_grant_pa[4:0];

								
   assign		arbpc0_pcxdp_grant_bufp3_pa_l	   =       ~arbpc0_pcxdp_grant_arbbf_pa; 
   assign		arbpc0_pcxdp_q0_hold_bufp3_pa	   =       ~arbpc0_pcxdp_q0_hold_arbbf_pa_l;  
   assign		arbpc0_pcxdp_qsel0_bufp3_pa_l	   =       ~arbpc0_pcxdp_qsel0_arbbf_pa;      
   assign		arbpc0_pcxdp_qsel1_bufp3_pa	   =       ~arbpc0_pcxdp_qsel1_arbbf_pa_l;    
   assign		arbpc0_pcxdp_shift_bufp3_px_l	   =       ~arbpc0_pcxdp_shift_arbbf_px;      
								                                                  
   assign		arbpc1_pcxdp_grant_bufp3_pa_l	   =       ~arbpc1_pcxdp_grant_arbbf_pa;  
   assign		arbpc1_pcxdp_q0_hold_bufp3_pa	   =       ~arbpc1_pcxdp_q0_hold_arbbf_pa_l;  
   assign		arbpc1_pcxdp_qsel0_bufp3_pa_l	   =       ~arbpc1_pcxdp_qsel0_arbbf_pa;      
   assign		arbpc1_pcxdp_qsel1_bufp3_pa	   =       ~arbpc1_pcxdp_qsel1_arbbf_pa_l;    
   assign		arbpc1_pcxdp_shift_bufp3_px_l	   =       ~arbpc1_pcxdp_shift_arbbf_px;      
								                                                  
   assign		arbpc2_pcxdp_grant_bufp3_pa_l	   =       ~arbpc2_pcxdp_grant_arbbf_pa; 
   assign		arbpc2_pcxdp_q0_hold_bufp3_pa	   =       ~arbpc2_pcxdp_q0_hold_arbbf_pa_l;  
   assign		arbpc2_pcxdp_qsel0_bufp3_pa_l	   =       ~arbpc2_pcxdp_qsel0_arbbf_pa;      
   assign		arbpc2_pcxdp_qsel1_bufp3_pa	   =       ~arbpc2_pcxdp_qsel1_arbbf_pa_l;    
   assign		arbpc2_pcxdp_shift_bufp3_px_l	   =       ~arbpc2_pcxdp_shift_arbbf_px;      
								                                                  
   assign		arbpc3_pcxdp_grant_bufp3_pa_l	   =       ~arbpc3_pcxdp_grant_arbbf_pa; 
   assign		arbpc3_pcxdp_q0_hold_bufp3_pa	   =       ~arbpc3_pcxdp_q0_hold_arbbf_pa_l;  
   assign		arbpc3_pcxdp_qsel0_bufp3_pa_l	   =       ~arbpc3_pcxdp_qsel0_arbbf_pa;      
   assign		arbpc3_pcxdp_qsel1_bufp3_pa	   =       ~arbpc3_pcxdp_qsel1_arbbf_pa_l;    
   assign		arbpc3_pcxdp_shift_bufp3_px_l	   =       ~arbpc3_pcxdp_shift_arbbf_px;      
								                                                  
   assign		arbpc4_pcxdp_grant_bufp3_pa_l	   =       ~arbpc4_pcxdp_grant_arbbf_pa; 
   assign		arbpc4_pcxdp_q0_hold_bufp3_pa	   =       ~arbpc4_pcxdp_q0_hold_arbbf_pa_l;  
   assign		arbpc4_pcxdp_qsel0_bufp3_pa_l	   =       ~arbpc4_pcxdp_qsel0_arbbf_pa;      
   assign		arbpc4_pcxdp_qsel1_bufp3_pa	   =       ~arbpc4_pcxdp_qsel1_arbbf_pa_l;    
   assign		arbpc4_pcxdp_shift_bufp3_px_l	   =       ~arbpc4_pcxdp_shift_arbbf_px;      
								                                                  




endmodule // pcx_grant_ff





