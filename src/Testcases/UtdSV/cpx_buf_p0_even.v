// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: cpx_buf_p0_even.v
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
//  Module Name:
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
module cpx_buf_p0_even(/*AUTOARG*/
   // Outputs
   arbcp0_cpxdp_grant_ca, arbcp0_cpxdp_q0_hold_ca_l, 
   arbcp0_cpxdp_qsel0_ca, arbcp0_cpxdp_qsel1_ca_l, 
   arbcp0_cpxdp_shift_cx, arbcp2_cpxdp_grant_ca, 
   arbcp2_cpxdp_q0_hold_ca_l, arbcp2_cpxdp_qsel0_ca, 
   arbcp2_cpxdp_qsel1_ca_l, arbcp2_cpxdp_shift_cx, 
   arbcp4_cpxdp_grant_ca, arbcp4_cpxdp_q0_hold_ca_l, 
   arbcp4_cpxdp_qsel0_ca, arbcp4_cpxdp_qsel1_ca_l, 
   arbcp4_cpxdp_shift_cx, arbcp6_cpxdp_grant_ca, 
   arbcp6_cpxdp_q0_hold_ca_l, arbcp6_cpxdp_qsel0_ca, 
   arbcp6_cpxdp_qsel1_ca_l, arbcp6_cpxdp_shift_cx, 
   // Inputs
   arbcp0_cpxdp_grant_bufp1_ca_l, arbcp0_cpxdp_q0_hold_bufp1_ca, 
   arbcp0_cpxdp_qsel0_bufp1_ca_l, arbcp0_cpxdp_qsel1_bufp1_ca, 
   arbcp0_cpxdp_shift_bufp1_cx_l, arbcp2_cpxdp_grant_bufp1_ca_l, 
   arbcp2_cpxdp_q0_hold_bufp1_ca, arbcp2_cpxdp_qsel0_bufp1_ca_l, 
   arbcp2_cpxdp_qsel1_bufp1_ca, arbcp2_cpxdp_shift_bufp1_cx_l, 
   arbcp4_cpxdp_grant_bufp1_ca_l, arbcp4_cpxdp_q0_hold_bufp1_ca, 
   arbcp4_cpxdp_qsel0_bufp1_ca_l, arbcp4_cpxdp_qsel1_bufp1_ca, 
   arbcp4_cpxdp_shift_bufp1_cx_l, arbcp6_cpxdp_grant_bufp1_ca_l, 
   arbcp6_cpxdp_q0_hold_bufp1_ca, arbcp6_cpxdp_qsel0_bufp1_ca_l, 
   arbcp6_cpxdp_qsel1_bufp1_ca, arbcp6_cpxdp_shift_bufp1_cx_l
   );
   
   
   output 		arbcp0_cpxdp_grant_ca;	
   output 		arbcp0_cpxdp_q0_hold_ca_l;
   output 		arbcp0_cpxdp_qsel0_ca;	
   output 		arbcp0_cpxdp_qsel1_ca_l;	
   output 		arbcp0_cpxdp_shift_cx;	
	  
   output 		arbcp2_cpxdp_grant_ca;	
   output 		arbcp2_cpxdp_q0_hold_ca_l;
   output 		arbcp2_cpxdp_qsel0_ca;	
   output 		arbcp2_cpxdp_qsel1_ca_l;	
   output 		arbcp2_cpxdp_shift_cx;	
	  
   output 		arbcp4_cpxdp_grant_ca;	
   output 		arbcp4_cpxdp_q0_hold_ca_l;
   output 		arbcp4_cpxdp_qsel0_ca;	
   output 		arbcp4_cpxdp_qsel1_ca_l;	
   output 		arbcp4_cpxdp_shift_cx;	
	  
   output 		arbcp6_cpxdp_grant_ca;	
   output 		arbcp6_cpxdp_q0_hold_ca_l;
   output 		arbcp6_cpxdp_qsel0_ca;	
   output 		arbcp6_cpxdp_qsel1_ca_l;	
   output 		arbcp6_cpxdp_shift_cx;	


   input		arbcp0_cpxdp_grant_bufp1_ca_l;	
   input		arbcp0_cpxdp_q0_hold_bufp1_ca;
   input		arbcp0_cpxdp_qsel0_bufp1_ca_l;	
   input		arbcp0_cpxdp_qsel1_bufp1_ca;	
   input		arbcp0_cpxdp_shift_bufp1_cx_l;	

   input		arbcp2_cpxdp_grant_bufp1_ca_l;	
   input		arbcp2_cpxdp_q0_hold_bufp1_ca;
   input		arbcp2_cpxdp_qsel0_bufp1_ca_l;	
   input		arbcp2_cpxdp_qsel1_bufp1_ca;	
   input		arbcp2_cpxdp_shift_bufp1_cx_l;	

   input		arbcp4_cpxdp_grant_bufp1_ca_l;	
   input		arbcp4_cpxdp_q0_hold_bufp1_ca;
   input		arbcp4_cpxdp_qsel0_bufp1_ca_l;	
   input		arbcp4_cpxdp_qsel1_bufp1_ca;	
   input		arbcp4_cpxdp_shift_bufp1_cx_l;	

   input		arbcp6_cpxdp_grant_bufp1_ca_l;	
   input		arbcp6_cpxdp_q0_hold_bufp1_ca;
   input		arbcp6_cpxdp_qsel0_bufp1_ca_l;	
   input		arbcp6_cpxdp_qsel1_bufp1_ca;	
   input		arbcp6_cpxdp_shift_bufp1_cx_l;	

   assign		arbcp0_cpxdp_grant_ca		   =    ~  arbcp0_cpxdp_grant_bufp1_ca_l;      	
   assign		arbcp0_cpxdp_q0_hold_ca_l	   =    ~ arbcp0_cpxdp_q0_hold_bufp1_ca;
   assign		arbcp0_cpxdp_qsel0_ca		   =    ~ arbcp0_cpxdp_qsel0_bufp1_ca_l;
   assign		arbcp0_cpxdp_qsel1_ca_l		   =    ~ arbcp0_cpxdp_qsel1_bufp1_ca;
   assign		arbcp0_cpxdp_shift_cx		   =    ~ arbcp0_cpxdp_shift_bufp1_cx_l;
								                                         
   assign		arbcp2_cpxdp_grant_ca		   =    ~  arbcp2_cpxdp_grant_bufp1_ca_l;      	
   assign		arbcp2_cpxdp_q0_hold_ca_l	   =    ~ arbcp2_cpxdp_q0_hold_bufp1_ca;
   assign		arbcp2_cpxdp_qsel0_ca		   =    ~ arbcp2_cpxdp_qsel0_bufp1_ca_l;
   assign		arbcp2_cpxdp_qsel1_ca_l		   =    ~ arbcp2_cpxdp_qsel1_bufp1_ca;
   assign		arbcp2_cpxdp_shift_cx		   =    ~ arbcp2_cpxdp_shift_bufp1_cx_l;
								                                     
   assign		arbcp4_cpxdp_grant_ca		   =    ~  arbcp4_cpxdp_grant_bufp1_ca_l;      	
   assign		arbcp4_cpxdp_q0_hold_ca_l	   =    ~ arbcp4_cpxdp_q0_hold_bufp1_ca;
   assign		arbcp4_cpxdp_qsel0_ca		   =    ~ arbcp4_cpxdp_qsel0_bufp1_ca_l;
   assign		arbcp4_cpxdp_qsel1_ca_l		   =    ~ arbcp4_cpxdp_qsel1_bufp1_ca;
   assign		arbcp4_cpxdp_shift_cx		   =    ~ arbcp4_cpxdp_shift_bufp1_cx_l;
								                                     
   assign		arbcp6_cpxdp_grant_ca		   =    ~  arbcp6_cpxdp_grant_bufp1_ca_l;      	
   assign		arbcp6_cpxdp_q0_hold_ca_l	   =    ~ arbcp6_cpxdp_q0_hold_bufp1_ca;
   assign		arbcp6_cpxdp_qsel0_ca		   =    ~ arbcp6_cpxdp_qsel0_bufp1_ca_l;
   assign		arbcp6_cpxdp_qsel1_ca_l		   =    ~ arbcp6_cpxdp_qsel1_bufp1_ca;
   assign		arbcp6_cpxdp_shift_cx		   =    ~ arbcp6_cpxdp_shift_bufp1_cx_l;
								                                     

endmodule 


















