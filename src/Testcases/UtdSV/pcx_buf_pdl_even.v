// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: pcx_buf_pdl_even.v
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

module pcx_buf_pdl_even(/*AUTOARG*/
   // Outputs
   arbpc0_pcxdp_grant_pa, arbpc0_pcxdp_q0_hold_pa_l, 
   arbpc0_pcxdp_qsel0_pa, arbpc0_pcxdp_qsel1_pa_l, 
   arbpc0_pcxdp_shift_px, arbpc2_pcxdp_grant_pa, 
   arbpc2_pcxdp_q0_hold_pa_l, arbpc2_pcxdp_qsel0_pa, 
   arbpc2_pcxdp_qsel1_pa_l, arbpc2_pcxdp_shift_px, 
   // Inputs
   arbpc0_pcxdp_grant_bufp1_pa_l, arbpc0_pcxdp_q0_hold_bufp1_pa, 
   arbpc0_pcxdp_qsel0_bufp1_pa_l, arbpc0_pcxdp_qsel1_bufp1_pa, 
   arbpc0_pcxdp_shift_bufp1_px_l, arbpc2_pcxdp_grant_bufp1_pa_l, 
   arbpc2_pcxdp_q0_hold_bufp1_pa, arbpc2_pcxdp_qsel0_bufp1_pa_l, 
   arbpc2_pcxdp_qsel1_bufp1_pa, arbpc2_pcxdp_shift_bufp1_px_l
   );


   output 		arbpc0_pcxdp_grant_pa		;	
   output 		arbpc0_pcxdp_q0_hold_pa_l		;
   output 		arbpc0_pcxdp_qsel0_pa		;	
   output 		arbpc0_pcxdp_qsel1_pa_l		;	
   output 		arbpc0_pcxdp_shift_px		;	

   output 		arbpc2_pcxdp_grant_pa		;	
   output 		arbpc2_pcxdp_q0_hold_pa_l		;
   output 		arbpc2_pcxdp_qsel0_pa		;	
   output 		arbpc2_pcxdp_qsel1_pa_l		;	
   output 		arbpc2_pcxdp_shift_px		;	

   
   input 		arbpc0_pcxdp_grant_bufp1_pa_l;	
   input 		arbpc0_pcxdp_q0_hold_bufp1_pa;
   input 		arbpc0_pcxdp_qsel0_bufp1_pa_l;	
   input 		arbpc0_pcxdp_qsel1_bufp1_pa;	
   input 		arbpc0_pcxdp_shift_bufp1_px_l;	

   input 		arbpc2_pcxdp_grant_bufp1_pa_l;	
   input 		arbpc2_pcxdp_q0_hold_bufp1_pa;
   input 		arbpc2_pcxdp_qsel0_bufp1_pa_l;	
   input 		arbpc2_pcxdp_qsel1_bufp1_pa;	
   input 		arbpc2_pcxdp_shift_bufp1_px_l;	


   assign		arbpc0_pcxdp_grant_pa	   =        ~arbpc0_pcxdp_grant_bufp1_pa_l;           
   assign		arbpc0_pcxdp_q0_hold_pa_l  =        ~arbpc0_pcxdp_q0_hold_bufp1_pa;  
   assign		arbpc0_pcxdp_qsel0_pa	   =        ~arbpc0_pcxdp_qsel0_bufp1_pa_l;      
   assign		arbpc0_pcxdp_qsel1_pa_l	   =        ~arbpc0_pcxdp_qsel1_bufp1_pa;    
   assign		arbpc0_pcxdp_shift_px	   =        ~arbpc0_pcxdp_shift_bufp1_px_l;      
								                                                   
								                                                   
   assign		arbpc2_pcxdp_grant_pa	   =        ~arbpc2_pcxdp_grant_bufp1_pa_l;      	
   assign		arbpc2_pcxdp_q0_hold_pa_l  =        ~arbpc2_pcxdp_q0_hold_bufp1_pa;  
   assign		arbpc2_pcxdp_qsel0_pa	   =        ~arbpc2_pcxdp_qsel0_bufp1_pa_l;      
   assign		arbpc2_pcxdp_qsel1_pa_l	   =        ~arbpc2_pcxdp_qsel1_bufp1_pa;    
   assign		arbpc2_pcxdp_shift_px	   =        ~arbpc2_pcxdp_shift_bufp1_px_l;      
								                                                   
   

endmodule 

