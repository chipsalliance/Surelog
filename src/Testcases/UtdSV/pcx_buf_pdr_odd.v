// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: pcx_buf_pdr_odd.v
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

module pcx_buf_pdr_odd(/*AUTOARG*/
   // Outputs
   arbpc1_pcxdp_grant_pa, arbpc1_pcxdp_q0_hold_pa_l, 
   arbpc1_pcxdp_qsel0_pa, arbpc1_pcxdp_qsel1_pa_l, 
   arbpc1_pcxdp_shift_px, arbpc3_pcxdp_grant_pa, 
   arbpc3_pcxdp_q0_hold_pa_l, arbpc3_pcxdp_qsel0_pa, 
   arbpc3_pcxdp_qsel1_pa_l, arbpc3_pcxdp_shift_px, 
   arbpc4_pcxdp_grant_pa, arbpc4_pcxdp_q0_hold_pa_l, 
   arbpc4_pcxdp_qsel0_pa, arbpc4_pcxdp_qsel1_pa_l, 
   arbpc4_pcxdp_shift_px, 
   // Inputs
   arbpc1_pcxdp_grant_bufp3_pa_l, arbpc1_pcxdp_q0_hold_bufp3_pa, 
   arbpc1_pcxdp_qsel0_bufp3_pa_l, arbpc1_pcxdp_qsel1_bufp3_pa, 
   arbpc1_pcxdp_shift_bufp3_px_l, arbpc3_pcxdp_grant_bufp3_pa_l, 
   arbpc3_pcxdp_q0_hold_bufp3_pa, arbpc3_pcxdp_qsel0_bufp3_pa_l, 
   arbpc3_pcxdp_qsel1_bufp3_pa, arbpc3_pcxdp_shift_bufp3_px_l, 
   arbpc4_pcxdp_grant_bufp3_pa_l, arbpc4_pcxdp_q0_hold_bufp3_pa, 
   arbpc4_pcxdp_qsel0_bufp3_pa_l, arbpc4_pcxdp_qsel1_bufp3_pa, 
   arbpc4_pcxdp_shift_bufp3_px_l
   );

   
   output 		arbpc1_pcxdp_grant_pa		;	
   output 		arbpc1_pcxdp_q0_hold_pa_l		;
   output 		arbpc1_pcxdp_qsel0_pa		;	
   output 		arbpc1_pcxdp_qsel1_pa_l		;	
   output 		arbpc1_pcxdp_shift_px		;	

   output 		arbpc3_pcxdp_grant_pa		;	
   output 		arbpc3_pcxdp_q0_hold_pa_l		;
   output 		arbpc3_pcxdp_qsel0_pa		;	
   output 		arbpc3_pcxdp_qsel1_pa_l		;	
   output 		arbpc3_pcxdp_shift_px		;	

   output 		arbpc4_pcxdp_grant_pa		;	
   output 		arbpc4_pcxdp_q0_hold_pa_l		;
   output 		arbpc4_pcxdp_qsel0_pa		;	
   output 		arbpc4_pcxdp_qsel1_pa_l		;	
   output 		arbpc4_pcxdp_shift_px		;	



   input 		arbpc1_pcxdp_grant_bufp3_pa_l;	
   input 		arbpc1_pcxdp_q0_hold_bufp3_pa;
   input 		arbpc1_pcxdp_qsel0_bufp3_pa_l;	
   input 		arbpc1_pcxdp_qsel1_bufp3_pa;	
   input 		arbpc1_pcxdp_shift_bufp3_px_l;	

   input 		arbpc3_pcxdp_grant_bufp3_pa_l;	
   input 		arbpc3_pcxdp_q0_hold_bufp3_pa;
   input 		arbpc3_pcxdp_qsel0_bufp3_pa_l;	
   input 		arbpc3_pcxdp_qsel1_bufp3_pa;	
   input 		arbpc3_pcxdp_shift_bufp3_px_l;	

   input 		arbpc4_pcxdp_grant_bufp3_pa_l;	
   input 		arbpc4_pcxdp_q0_hold_bufp3_pa;
   input 		arbpc4_pcxdp_qsel0_bufp3_pa_l;	
   input 		arbpc4_pcxdp_qsel1_bufp3_pa;	
   input 		arbpc4_pcxdp_shift_bufp3_px_l;	

   

								                                                   
   assign		arbpc1_pcxdp_grant_pa	   =        ~arbpc1_pcxdp_grant_bufp3_pa_l;      	
   assign		arbpc1_pcxdp_q0_hold_pa_l  =        ~arbpc1_pcxdp_q0_hold_bufp3_pa;  
   assign		arbpc1_pcxdp_qsel0_pa	   =        ~arbpc1_pcxdp_qsel0_bufp3_pa_l;      
   assign		arbpc1_pcxdp_qsel1_pa_l	   =        ~arbpc1_pcxdp_qsel1_bufp3_pa;    
   assign		arbpc1_pcxdp_shift_px	   =        ~arbpc1_pcxdp_shift_bufp3_px_l;      
								                                                   
   assign		arbpc3_pcxdp_grant_pa	   =        ~arbpc3_pcxdp_grant_bufp3_pa_l;      	
   assign		arbpc3_pcxdp_q0_hold_pa_l  =        ~arbpc3_pcxdp_q0_hold_bufp3_pa;  
   assign		arbpc3_pcxdp_qsel0_pa	   =        ~arbpc3_pcxdp_qsel0_bufp3_pa_l;      
   assign		arbpc3_pcxdp_qsel1_pa_l	   =        ~arbpc3_pcxdp_qsel1_bufp3_pa;    
   assign		arbpc3_pcxdp_shift_px	   =        ~arbpc3_pcxdp_shift_bufp3_px_l;      
								                                                   
   assign		arbpc4_pcxdp_grant_pa	   =        ~arbpc4_pcxdp_grant_bufp3_pa_l;      	
   assign		arbpc4_pcxdp_q0_hold_pa_l  =        ~arbpc4_pcxdp_q0_hold_bufp3_pa;  
   assign		arbpc4_pcxdp_qsel0_pa	   =        ~arbpc4_pcxdp_qsel0_bufp3_pa_l;      
   assign		arbpc4_pcxdp_qsel1_pa_l	   =        ~arbpc4_pcxdp_qsel1_bufp3_pa;    
   assign		arbpc4_pcxdp_shift_px	   =        ~arbpc4_pcxdp_shift_bufp3_px_l;      
								                                                   


   

endmodule 
