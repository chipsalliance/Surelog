// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: cpx_buf_p1.v
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

module cpx_buf_p1(/*AUTOARG*/
   // Outputs
   scache0_cpx_req_bufp1_cq, scache0_cpx_atom_bufp1_cq, 
   cpx_scache0_grant_bufp1_ca_l, cpx_spc0_data_rdy_bufp1_cx, 
   cpx_spc1_data_rdy_bufp1_cx, cpx_spc2_data_rdy_bufp1_cx, 
   arbcp0_cpxdp_grant_bufp1_ca_l_0, arbcp0_cpxdp_q0_hold_bufp1_ca_0, 
   arbcp0_cpxdp_qsel0_bufp1_ca_l_0, arbcp0_cpxdp_qsel1_bufp1_ca_0, 
   arbcp0_cpxdp_shift_bufp1_cx_l_0, arbcp1_cpxdp_grant_bufp1_ca_l_0, 
   arbcp1_cpxdp_q0_hold_bufp1_ca_0, arbcp1_cpxdp_qsel0_bufp1_ca_l_0, 
   arbcp1_cpxdp_qsel1_bufp1_ca_0, arbcp1_cpxdp_shift_bufp1_cx_l_0, 
   arbcp2_cpxdp_grant_bufp1_ca_l_0, arbcp2_cpxdp_q0_hold_bufp1_ca_0, 
   arbcp2_cpxdp_qsel0_bufp1_ca_l_0, arbcp2_cpxdp_qsel1_bufp1_ca_0, 
   arbcp2_cpxdp_shift_bufp1_cx_l_0, arbcp3_cpxdp_grant_bufp1_ca_l_0, 
   arbcp3_cpxdp_q0_hold_bufp1_ca_0, arbcp3_cpxdp_qsel0_bufp1_ca_l_0, 
   arbcp3_cpxdp_qsel1_bufp1_ca_0, arbcp3_cpxdp_shift_bufp1_cx_l_0, 
   arbcp4_cpxdp_grant_bufp1_ca_l_0, arbcp4_cpxdp_q0_hold_bufp1_ca_0, 
   arbcp4_cpxdp_qsel0_bufp1_ca_l_0, arbcp4_cpxdp_qsel1_bufp1_ca_0, 
   arbcp4_cpxdp_shift_bufp1_cx_l_0, arbcp5_cpxdp_grant_bufp1_ca_l_0, 
   arbcp5_cpxdp_q0_hold_bufp1_ca_0, arbcp5_cpxdp_qsel0_bufp1_ca_l_0, 
   arbcp5_cpxdp_qsel1_bufp1_ca_0, arbcp5_cpxdp_shift_bufp1_cx_l_0, 
   arbcp6_cpxdp_grant_bufp1_ca_l_0, arbcp6_cpxdp_q0_hold_bufp1_ca_0, 
   arbcp6_cpxdp_qsel0_bufp1_ca_l_0, arbcp6_cpxdp_qsel1_bufp1_ca_0, 
   arbcp6_cpxdp_shift_bufp1_cx_l_0, arbcp7_cpxdp_grant_bufp1_ca_l_0, 
   arbcp7_cpxdp_q0_hold_bufp1_ca_0, arbcp7_cpxdp_qsel0_bufp1_ca_l_0, 
   arbcp7_cpxdp_qsel1_bufp1_ca_0, arbcp7_cpxdp_shift_bufp1_cx_l_0, 
   arbcp0_cpxdp_grant_bufp1_ca_l_1, arbcp0_cpxdp_q0_hold_bufp1_ca_1, 
   arbcp0_cpxdp_qsel0_bufp1_ca_l_1, arbcp0_cpxdp_qsel1_bufp1_ca_1, 
   arbcp0_cpxdp_shift_bufp1_cx_l_1, arbcp1_cpxdp_grant_bufp1_ca_l_1, 
   arbcp1_cpxdp_q0_hold_bufp1_ca_1, arbcp1_cpxdp_qsel0_bufp1_ca_l_1, 
   arbcp1_cpxdp_qsel1_bufp1_ca_1, arbcp1_cpxdp_shift_bufp1_cx_l_1, 
   arbcp2_cpxdp_grant_bufp1_ca_l_1, arbcp2_cpxdp_q0_hold_bufp1_ca_1, 
   arbcp2_cpxdp_qsel0_bufp1_ca_l_1, arbcp2_cpxdp_qsel1_bufp1_ca_1, 
   arbcp2_cpxdp_shift_bufp1_cx_l_1, arbcp3_cpxdp_grant_bufp1_ca_l_1, 
   arbcp3_cpxdp_q0_hold_bufp1_ca_1, arbcp3_cpxdp_qsel0_bufp1_ca_l_1, 
   arbcp3_cpxdp_qsel1_bufp1_ca_1, arbcp3_cpxdp_shift_bufp1_cx_l_1, 
   arbcp4_cpxdp_grant_bufp1_ca_l_1, arbcp4_cpxdp_q0_hold_bufp1_ca_1, 
   arbcp4_cpxdp_qsel0_bufp1_ca_l_1, arbcp4_cpxdp_qsel1_bufp1_ca_1, 
   arbcp4_cpxdp_shift_bufp1_cx_l_1, arbcp5_cpxdp_grant_bufp1_ca_l_1, 
   arbcp5_cpxdp_q0_hold_bufp1_ca_1, arbcp5_cpxdp_qsel0_bufp1_ca_l_1, 
   arbcp5_cpxdp_qsel1_bufp1_ca_1, arbcp5_cpxdp_shift_bufp1_cx_l_1, 
   arbcp6_cpxdp_grant_bufp1_ca_l_1, arbcp6_cpxdp_q0_hold_bufp1_ca_1, 
   arbcp6_cpxdp_qsel0_bufp1_ca_l_1, arbcp6_cpxdp_qsel1_bufp1_ca_1, 
   arbcp6_cpxdp_shift_bufp1_cx_l_1, arbcp7_cpxdp_grant_bufp1_ca_l_1, 
   arbcp7_cpxdp_q0_hold_bufp1_ca_1, arbcp7_cpxdp_qsel0_bufp1_ca_l_1, 
   arbcp7_cpxdp_qsel1_bufp1_ca_1, arbcp7_cpxdp_shift_bufp1_cx_l_1, 
   // Inputs
   scache0_cpx_req_bufp0_cq, scache0_cpx_atom_bufp0_cq, 
   cpx_scache0_grant_ca, cpx_spc0_data_rdy_cx, cpx_spc1_data_rdy_cx, 
   cpx_spc2_data_rdy_cx, arbcp0_cpxdp_grant_arbbf_ca_0, 
   arbcp0_cpxdp_q0_hold_arbbf_ca_l_0, arbcp0_cpxdp_qsel0_arbbf_ca_0, 
   arbcp0_cpxdp_qsel1_arbbf_ca_l_0, arbcp0_cpxdp_shift_arbbf_cx_0, 
   arbcp1_cpxdp_grant_arbbf_ca_0, arbcp1_cpxdp_q0_hold_arbbf_ca_l_0, 
   arbcp1_cpxdp_qsel0_arbbf_ca_0, arbcp1_cpxdp_qsel1_arbbf_ca_l_0, 
   arbcp1_cpxdp_shift_arbbf_cx_0, arbcp2_cpxdp_grant_arbbf_ca_0, 
   arbcp2_cpxdp_q0_hold_arbbf_ca_l_0, arbcp2_cpxdp_qsel0_arbbf_ca_0, 
   arbcp2_cpxdp_qsel1_arbbf_ca_l_0, arbcp2_cpxdp_shift_arbbf_cx_0, 
   arbcp3_cpxdp_grant_arbbf_ca_0, arbcp3_cpxdp_q0_hold_arbbf_ca_l_0, 
   arbcp3_cpxdp_qsel0_arbbf_ca_0, arbcp3_cpxdp_qsel1_arbbf_ca_l_0, 
   arbcp3_cpxdp_shift_arbbf_cx_0, arbcp4_cpxdp_grant_arbbf_ca_0, 
   arbcp4_cpxdp_q0_hold_arbbf_ca_l_0, arbcp4_cpxdp_qsel0_arbbf_ca_0, 
   arbcp4_cpxdp_qsel1_arbbf_ca_l_0, arbcp4_cpxdp_shift_arbbf_cx_0, 
   arbcp5_cpxdp_grant_arbbf_ca_0, arbcp5_cpxdp_q0_hold_arbbf_ca_l_0, 
   arbcp5_cpxdp_qsel0_arbbf_ca_0, arbcp5_cpxdp_qsel1_arbbf_ca_l_0, 
   arbcp5_cpxdp_shift_arbbf_cx_0, arbcp6_cpxdp_grant_arbbf_ca_0, 
   arbcp6_cpxdp_q0_hold_arbbf_ca_l_0, arbcp6_cpxdp_qsel0_arbbf_ca_0, 
   arbcp6_cpxdp_qsel1_arbbf_ca_l_0, arbcp6_cpxdp_shift_arbbf_cx_0, 
   arbcp7_cpxdp_grant_arbbf_ca_0, arbcp7_cpxdp_q0_hold_arbbf_ca_l_0, 
   arbcp7_cpxdp_qsel0_arbbf_ca_0, arbcp7_cpxdp_qsel1_arbbf_ca_l_0, 
   arbcp7_cpxdp_shift_arbbf_cx_0, arbcp0_cpxdp_grant_arbbf_ca_1, 
   arbcp0_cpxdp_q0_hold_arbbf_ca_l_1, arbcp0_cpxdp_qsel0_arbbf_ca_1, 
   arbcp0_cpxdp_qsel1_arbbf_ca_l_1, arbcp0_cpxdp_shift_arbbf_cx_1, 
   arbcp1_cpxdp_grant_arbbf_ca_1, arbcp1_cpxdp_q0_hold_arbbf_ca_l_1, 
   arbcp1_cpxdp_qsel0_arbbf_ca_1, arbcp1_cpxdp_qsel1_arbbf_ca_l_1, 
   arbcp1_cpxdp_shift_arbbf_cx_1, arbcp2_cpxdp_grant_arbbf_ca_1, 
   arbcp2_cpxdp_q0_hold_arbbf_ca_l_1, arbcp2_cpxdp_qsel0_arbbf_ca_1, 
   arbcp2_cpxdp_qsel1_arbbf_ca_l_1, arbcp2_cpxdp_shift_arbbf_cx_1, 
   arbcp3_cpxdp_grant_arbbf_ca_1, arbcp3_cpxdp_q0_hold_arbbf_ca_l_1, 
   arbcp3_cpxdp_qsel0_arbbf_ca_1, arbcp3_cpxdp_qsel1_arbbf_ca_l_1, 
   arbcp3_cpxdp_shift_arbbf_cx_1, arbcp4_cpxdp_grant_arbbf_ca_1, 
   arbcp4_cpxdp_q0_hold_arbbf_ca_l_1, arbcp4_cpxdp_qsel0_arbbf_ca_1, 
   arbcp4_cpxdp_qsel1_arbbf_ca_l_1, arbcp4_cpxdp_shift_arbbf_cx_1, 
   arbcp5_cpxdp_grant_arbbf_ca_1, arbcp5_cpxdp_q0_hold_arbbf_ca_l_1, 
   arbcp5_cpxdp_qsel0_arbbf_ca_1, arbcp5_cpxdp_qsel1_arbbf_ca_l_1, 
   arbcp5_cpxdp_shift_arbbf_cx_1, arbcp6_cpxdp_grant_arbbf_ca_1, 
   arbcp6_cpxdp_q0_hold_arbbf_ca_l_1, arbcp6_cpxdp_qsel0_arbbf_ca_1, 
   arbcp6_cpxdp_qsel1_arbbf_ca_l_1, arbcp6_cpxdp_shift_arbbf_cx_1, 
   arbcp7_cpxdp_grant_arbbf_ca_1, arbcp7_cpxdp_q0_hold_arbbf_ca_l_1, 
   arbcp7_cpxdp_qsel0_arbbf_ca_1, arbcp7_cpxdp_qsel1_arbbf_ca_l_1, 
   arbcp7_cpxdp_shift_arbbf_cx_1
   );
   
   output [7:0]		scache0_cpx_req_bufp1_cq		        ;	
   output 		scache0_cpx_atom_bufp1_cq		        ;	
   output [7:0] 	cpx_scache0_grant_bufp1_ca_l;
   output     		cpx_spc0_data_rdy_bufp1_cx;
   output     		cpx_spc1_data_rdy_bufp1_cx;
   output     		cpx_spc2_data_rdy_bufp1_cx;
   
   output 		arbcp0_cpxdp_grant_bufp1_ca_l_0		;	
   output 		arbcp0_cpxdp_q0_hold_bufp1_ca_0		;
   output 		arbcp0_cpxdp_qsel0_bufp1_ca_l_0		;	
   output 		arbcp0_cpxdp_qsel1_bufp1_ca_0		;	
   output 		arbcp0_cpxdp_shift_bufp1_cx_l_0		;	

   output 		arbcp1_cpxdp_grant_bufp1_ca_l_0		;	
   output 		arbcp1_cpxdp_q0_hold_bufp1_ca_0		;
   output 		arbcp1_cpxdp_qsel0_bufp1_ca_l_0		;	
   output 		arbcp1_cpxdp_qsel1_bufp1_ca_0		;	
   output 		arbcp1_cpxdp_shift_bufp1_cx_l_0		;	

   output 		arbcp2_cpxdp_grant_bufp1_ca_l_0		;	
   output 		arbcp2_cpxdp_q0_hold_bufp1_ca_0		;
   output 		arbcp2_cpxdp_qsel0_bufp1_ca_l_0		;	
   output 		arbcp2_cpxdp_qsel1_bufp1_ca_0		;	
   output 		arbcp2_cpxdp_shift_bufp1_cx_l_0		;	

   output 		arbcp3_cpxdp_grant_bufp1_ca_l_0		;	
   output 		arbcp3_cpxdp_q0_hold_bufp1_ca_0		;
   output 		arbcp3_cpxdp_qsel0_bufp1_ca_l_0		;	
   output 		arbcp3_cpxdp_qsel1_bufp1_ca_0		;	
   output 		arbcp3_cpxdp_shift_bufp1_cx_l_0		;	

   output 		arbcp4_cpxdp_grant_bufp1_ca_l_0		;	
   output 		arbcp4_cpxdp_q0_hold_bufp1_ca_0		;
   output 		arbcp4_cpxdp_qsel0_bufp1_ca_l_0		;	
   output 		arbcp4_cpxdp_qsel1_bufp1_ca_0		;	
   output 		arbcp4_cpxdp_shift_bufp1_cx_l_0		;	

   output 		arbcp5_cpxdp_grant_bufp1_ca_l_0		;	
   output 		arbcp5_cpxdp_q0_hold_bufp1_ca_0		;
   output 		arbcp5_cpxdp_qsel0_bufp1_ca_l_0		;	
   output 		arbcp5_cpxdp_qsel1_bufp1_ca_0		;	
   output 		arbcp5_cpxdp_shift_bufp1_cx_l_0		;	

   output 		arbcp6_cpxdp_grant_bufp1_ca_l_0		;	
   output 		arbcp6_cpxdp_q0_hold_bufp1_ca_0		;
   output 		arbcp6_cpxdp_qsel0_bufp1_ca_l_0		;	
   output 		arbcp6_cpxdp_qsel1_bufp1_ca_0		;	
   output 		arbcp6_cpxdp_shift_bufp1_cx_l_0		;	

   output 		arbcp7_cpxdp_grant_bufp1_ca_l_0		;	
   output 		arbcp7_cpxdp_q0_hold_bufp1_ca_0		;
   output 		arbcp7_cpxdp_qsel0_bufp1_ca_l_0		;	
   output 		arbcp7_cpxdp_qsel1_bufp1_ca_0		;	
   output 		arbcp7_cpxdp_shift_bufp1_cx_l_0		;	


   input [7:0]		scache0_cpx_req_bufp0_cq;	
   input 		scache0_cpx_atom_bufp0_cq;	
   input [7:0] 	        cpx_scache0_grant_ca;
   input     		cpx_spc0_data_rdy_cx;
   input     		cpx_spc1_data_rdy_cx;
   input     		cpx_spc2_data_rdy_cx;
   
   
   input 		arbcp0_cpxdp_grant_arbbf_ca_0;	
   input 		arbcp0_cpxdp_q0_hold_arbbf_ca_l_0;
   input 		arbcp0_cpxdp_qsel0_arbbf_ca_0;	
   input 		arbcp0_cpxdp_qsel1_arbbf_ca_l_0;	
   input 		arbcp0_cpxdp_shift_arbbf_cx_0;	

   input 		arbcp1_cpxdp_grant_arbbf_ca_0;	
   input 		arbcp1_cpxdp_q0_hold_arbbf_ca_l_0;
   input 		arbcp1_cpxdp_qsel0_arbbf_ca_0;	
   input 		arbcp1_cpxdp_qsel1_arbbf_ca_l_0;	
   input 		arbcp1_cpxdp_shift_arbbf_cx_0;	

   input 		arbcp2_cpxdp_grant_arbbf_ca_0;	
   input 		arbcp2_cpxdp_q0_hold_arbbf_ca_l_0;
   input 		arbcp2_cpxdp_qsel0_arbbf_ca_0;	
   input 		arbcp2_cpxdp_qsel1_arbbf_ca_l_0;	
   input 		arbcp2_cpxdp_shift_arbbf_cx_0;	

   input 		arbcp3_cpxdp_grant_arbbf_ca_0;	
   input 		arbcp3_cpxdp_q0_hold_arbbf_ca_l_0;
   input 		arbcp3_cpxdp_qsel0_arbbf_ca_0;	
   input 		arbcp3_cpxdp_qsel1_arbbf_ca_l_0;	
   input 		arbcp3_cpxdp_shift_arbbf_cx_0;	

   input 		arbcp4_cpxdp_grant_arbbf_ca_0;	
   input 		arbcp4_cpxdp_q0_hold_arbbf_ca_l_0;
   input 		arbcp4_cpxdp_qsel0_arbbf_ca_0;	
   input 		arbcp4_cpxdp_qsel1_arbbf_ca_l_0;	
   input 		arbcp4_cpxdp_shift_arbbf_cx_0;	

   input 		arbcp5_cpxdp_grant_arbbf_ca_0;	
   input 		arbcp5_cpxdp_q0_hold_arbbf_ca_l_0;
   input 		arbcp5_cpxdp_qsel0_arbbf_ca_0;	
   input 		arbcp5_cpxdp_qsel1_arbbf_ca_l_0;	
   input 		arbcp5_cpxdp_shift_arbbf_cx_0;	

   input 		arbcp6_cpxdp_grant_arbbf_ca_0;	
   input 		arbcp6_cpxdp_q0_hold_arbbf_ca_l_0;
   input 		arbcp6_cpxdp_qsel0_arbbf_ca_0;	
   input 		arbcp6_cpxdp_qsel1_arbbf_ca_l_0;	
   input 		arbcp6_cpxdp_shift_arbbf_cx_0;	

   input 		arbcp7_cpxdp_grant_arbbf_ca_0;	
   input 		arbcp7_cpxdp_q0_hold_arbbf_ca_l_0;
   input 		arbcp7_cpxdp_qsel0_arbbf_ca_0;	
   input 		arbcp7_cpxdp_qsel1_arbbf_ca_l_0;	
   input 		arbcp7_cpxdp_shift_arbbf_cx_0;	
   

   output 		arbcp0_cpxdp_grant_bufp1_ca_l_1		;	
   output 		arbcp0_cpxdp_q0_hold_bufp1_ca_1		;
   output 		arbcp0_cpxdp_qsel0_bufp1_ca_l_1		;	
   output 		arbcp0_cpxdp_qsel1_bufp1_ca_1		;	
   output 		arbcp0_cpxdp_shift_bufp1_cx_l_1		;	

   output 		arbcp1_cpxdp_grant_bufp1_ca_l_1		;	
   output 		arbcp1_cpxdp_q0_hold_bufp1_ca_1		;
   output 		arbcp1_cpxdp_qsel0_bufp1_ca_l_1		;	
   output 		arbcp1_cpxdp_qsel1_bufp1_ca_1		;	
   output 		arbcp1_cpxdp_shift_bufp1_cx_l_1		;	

   output 		arbcp2_cpxdp_grant_bufp1_ca_l_1		;	
   output 		arbcp2_cpxdp_q0_hold_bufp1_ca_1		;
   output 		arbcp2_cpxdp_qsel0_bufp1_ca_l_1		;	
   output 		arbcp2_cpxdp_qsel1_bufp1_ca_1		;	
   output 		arbcp2_cpxdp_shift_bufp1_cx_l_1		;	

   output 		arbcp3_cpxdp_grant_bufp1_ca_l_1		;	
   output 		arbcp3_cpxdp_q0_hold_bufp1_ca_1		;
   output 		arbcp3_cpxdp_qsel0_bufp1_ca_l_1		;	
   output 		arbcp3_cpxdp_qsel1_bufp1_ca_1		;	
   output 		arbcp3_cpxdp_shift_bufp1_cx_l_1		;	

   output 		arbcp4_cpxdp_grant_bufp1_ca_l_1		;	
   output 		arbcp4_cpxdp_q0_hold_bufp1_ca_1		;
   output 		arbcp4_cpxdp_qsel0_bufp1_ca_l_1		;	
   output 		arbcp4_cpxdp_qsel1_bufp1_ca_1		;	
   output 		arbcp4_cpxdp_shift_bufp1_cx_l_1		;	

   output 		arbcp5_cpxdp_grant_bufp1_ca_l_1		;	
   output 		arbcp5_cpxdp_q0_hold_bufp1_ca_1		;
   output 		arbcp5_cpxdp_qsel0_bufp1_ca_l_1		;	
   output 		arbcp5_cpxdp_qsel1_bufp1_ca_1		;	
   output 		arbcp5_cpxdp_shift_bufp1_cx_l_1		;	

   output 		arbcp6_cpxdp_grant_bufp1_ca_l_1		;	
   output 		arbcp6_cpxdp_q0_hold_bufp1_ca_1		;
   output 		arbcp6_cpxdp_qsel0_bufp1_ca_l_1		;	
   output 		arbcp6_cpxdp_qsel1_bufp1_ca_1		;	
   output 		arbcp6_cpxdp_shift_bufp1_cx_l_1		;	

   output 		arbcp7_cpxdp_grant_bufp1_ca_l_1		;	
   output 		arbcp7_cpxdp_q0_hold_bufp1_ca_1		;
   output 		arbcp7_cpxdp_qsel0_bufp1_ca_l_1		;	
   output 		arbcp7_cpxdp_qsel1_bufp1_ca_1		;	
   output 		arbcp7_cpxdp_shift_bufp1_cx_l_1		;	


   input 		arbcp0_cpxdp_grant_arbbf_ca_1;	
   input 		arbcp0_cpxdp_q0_hold_arbbf_ca_l_1;
   input 		arbcp0_cpxdp_qsel0_arbbf_ca_1;	
   input 		arbcp0_cpxdp_qsel1_arbbf_ca_l_1;	
   input 		arbcp0_cpxdp_shift_arbbf_cx_1;	

   input 		arbcp1_cpxdp_grant_arbbf_ca_1;	
   input 		arbcp1_cpxdp_q0_hold_arbbf_ca_l_1;
   input 		arbcp1_cpxdp_qsel0_arbbf_ca_1;	
   input 		arbcp1_cpxdp_qsel1_arbbf_ca_l_1;	
   input 		arbcp1_cpxdp_shift_arbbf_cx_1;	

   input 		arbcp2_cpxdp_grant_arbbf_ca_1;	
   input 		arbcp2_cpxdp_q0_hold_arbbf_ca_l_1;
   input 		arbcp2_cpxdp_qsel0_arbbf_ca_1;	
   input 		arbcp2_cpxdp_qsel1_arbbf_ca_l_1;	
   input 		arbcp2_cpxdp_shift_arbbf_cx_1;	

   input 		arbcp3_cpxdp_grant_arbbf_ca_1;	
   input 		arbcp3_cpxdp_q0_hold_arbbf_ca_l_1;
   input 		arbcp3_cpxdp_qsel0_arbbf_ca_1;	
   input 		arbcp3_cpxdp_qsel1_arbbf_ca_l_1;	
   input 		arbcp3_cpxdp_shift_arbbf_cx_1;	

   input 		arbcp4_cpxdp_grant_arbbf_ca_1;	
   input 		arbcp4_cpxdp_q0_hold_arbbf_ca_l_1;
   input 		arbcp4_cpxdp_qsel0_arbbf_ca_1;	
   input 		arbcp4_cpxdp_qsel1_arbbf_ca_l_1;	
   input 		arbcp4_cpxdp_shift_arbbf_cx_1;	

   input 		arbcp5_cpxdp_grant_arbbf_ca_1;	
   input 		arbcp5_cpxdp_q0_hold_arbbf_ca_l_1;
   input 		arbcp5_cpxdp_qsel0_arbbf_ca_1;	
   input 		arbcp5_cpxdp_qsel1_arbbf_ca_l_1;	
   input 		arbcp5_cpxdp_shift_arbbf_cx_1;	

   input 		arbcp6_cpxdp_grant_arbbf_ca_1;	
   input 		arbcp6_cpxdp_q0_hold_arbbf_ca_l_1;
   input 		arbcp6_cpxdp_qsel0_arbbf_ca_1;	
   input 		arbcp6_cpxdp_qsel1_arbbf_ca_l_1;	
   input 		arbcp6_cpxdp_shift_arbbf_cx_1;	

   input 		arbcp7_cpxdp_grant_arbbf_ca_1;	
   input 		arbcp7_cpxdp_q0_hold_arbbf_ca_l_1;
   input 		arbcp7_cpxdp_qsel0_arbbf_ca_1;	
   input 		arbcp7_cpxdp_qsel1_arbbf_ca_l_1;	
   input 		arbcp7_cpxdp_shift_arbbf_cx_1;	
   


   assign		scache0_cpx_req_bufp1_cq[7:0]		=        scache0_cpx_req_bufp0_cq[7:0];
   assign 		scache0_cpx_atom_bufp1_cq			=        scache0_cpx_atom_bufp0_cq;
   assign 	        cpx_scache0_grant_bufp1_ca_l            =  ~cpx_scache0_grant_ca;
   assign     		cpx_spc0_data_rdy_bufp1_cx              =  cpx_spc0_data_rdy_cx;
   assign     		cpx_spc1_data_rdy_bufp1_cx              =  cpx_spc1_data_rdy_cx;
   assign     		cpx_spc2_data_rdy_bufp1_cx              =  cpx_spc2_data_rdy_cx;

								
   assign		arbcp0_cpxdp_grant_bufp1_ca_l_0	   =       ~  arbcp0_cpxdp_grant_arbbf_ca_0;      	
   assign		arbcp0_cpxdp_q0_hold_bufp1_ca_0	   =       ~ arbcp0_cpxdp_q0_hold_arbbf_ca_l_0;  
   assign		arbcp0_cpxdp_qsel0_bufp1_ca_l_0	   =       ~ arbcp0_cpxdp_qsel0_arbbf_ca_0;      
   assign		arbcp0_cpxdp_qsel1_bufp1_ca_0	   =       ~ arbcp0_cpxdp_qsel1_arbbf_ca_l_0;    
   assign		arbcp0_cpxdp_shift_bufp1_cx_l_0	   =       ~ arbcp0_cpxdp_shift_arbbf_cx_0;      
								                                                    
   assign		arbcp1_cpxdp_grant_bufp1_ca_l_0	   =       ~  arbcp1_cpxdp_grant_arbbf_ca_0;      	
   assign		arbcp1_cpxdp_q0_hold_bufp1_ca_0	   =       ~ arbcp1_cpxdp_q0_hold_arbbf_ca_l_0;  
   assign		arbcp1_cpxdp_qsel0_bufp1_ca_l_0	   =       ~ arbcp1_cpxdp_qsel0_arbbf_ca_0;      
   assign		arbcp1_cpxdp_qsel1_bufp1_ca_0	   =       ~ arbcp1_cpxdp_qsel1_arbbf_ca_l_0;    
   assign		arbcp1_cpxdp_shift_bufp1_cx_l_0	   =       ~ arbcp1_cpxdp_shift_arbbf_cx_0;      
								                                                    
   assign		arbcp2_cpxdp_grant_bufp1_ca_l_0	   =       ~  arbcp2_cpxdp_grant_arbbf_ca_0;      	
   assign		arbcp2_cpxdp_q0_hold_bufp1_ca_0	   =       ~ arbcp2_cpxdp_q0_hold_arbbf_ca_l_0;  
   assign		arbcp2_cpxdp_qsel0_bufp1_ca_l_0	   =       ~ arbcp2_cpxdp_qsel0_arbbf_ca_0;      
   assign		arbcp2_cpxdp_qsel1_bufp1_ca_0	   =       ~ arbcp2_cpxdp_qsel1_arbbf_ca_l_0;    
   assign		arbcp2_cpxdp_shift_bufp1_cx_l_0	   =       ~ arbcp2_cpxdp_shift_arbbf_cx_0;      
								                                                    
   assign		arbcp3_cpxdp_grant_bufp1_ca_l_0	   =       ~  arbcp3_cpxdp_grant_arbbf_ca_0;      	
   assign		arbcp3_cpxdp_q0_hold_bufp1_ca_0	   =       ~ arbcp3_cpxdp_q0_hold_arbbf_ca_l_0;  
   assign		arbcp3_cpxdp_qsel0_bufp1_ca_l_0	   =       ~ arbcp3_cpxdp_qsel0_arbbf_ca_0;      
   assign		arbcp3_cpxdp_qsel1_bufp1_ca_0	   =       ~ arbcp3_cpxdp_qsel1_arbbf_ca_l_0;    
   assign		arbcp3_cpxdp_shift_bufp1_cx_l_0	   =       ~ arbcp3_cpxdp_shift_arbbf_cx_0;      
								                                                    
   assign		arbcp4_cpxdp_grant_bufp1_ca_l_0	   =       ~  arbcp4_cpxdp_grant_arbbf_ca_0;      	
   assign		arbcp4_cpxdp_q0_hold_bufp1_ca_0	   =       ~ arbcp4_cpxdp_q0_hold_arbbf_ca_l_0;  
   assign		arbcp4_cpxdp_qsel0_bufp1_ca_l_0	   =       ~ arbcp4_cpxdp_qsel0_arbbf_ca_0;      
   assign		arbcp4_cpxdp_qsel1_bufp1_ca_0	   =       ~ arbcp4_cpxdp_qsel1_arbbf_ca_l_0;    
   assign		arbcp4_cpxdp_shift_bufp1_cx_l_0	   =       ~ arbcp4_cpxdp_shift_arbbf_cx_0;      
								                                                    
   assign		arbcp5_cpxdp_grant_bufp1_ca_l_0	   =       ~  arbcp5_cpxdp_grant_arbbf_ca_0;      	
   assign		arbcp5_cpxdp_q0_hold_bufp1_ca_0	   =       ~ arbcp5_cpxdp_q0_hold_arbbf_ca_l_0;  
   assign		arbcp5_cpxdp_qsel0_bufp1_ca_l_0	   =       ~ arbcp5_cpxdp_qsel0_arbbf_ca_0;      
   assign		arbcp5_cpxdp_qsel1_bufp1_ca_0	   =       ~ arbcp5_cpxdp_qsel1_arbbf_ca_l_0;    
   assign		arbcp5_cpxdp_shift_bufp1_cx_l_0	   =       ~ arbcp5_cpxdp_shift_arbbf_cx_0;         
								                                                    
   assign		arbcp6_cpxdp_grant_bufp1_ca_l_0	   =       ~  arbcp6_cpxdp_grant_arbbf_ca_0;      	
   assign		arbcp6_cpxdp_q0_hold_bufp1_ca_0	   =       ~ arbcp6_cpxdp_q0_hold_arbbf_ca_l_0;  
   assign		arbcp6_cpxdp_qsel0_bufp1_ca_l_0	   =       ~ arbcp6_cpxdp_qsel0_arbbf_ca_0;      
   assign		arbcp6_cpxdp_qsel1_bufp1_ca_0	   =       ~ arbcp6_cpxdp_qsel1_arbbf_ca_l_0;    
   assign		arbcp6_cpxdp_shift_bufp1_cx_l_0	   =       ~ arbcp6_cpxdp_shift_arbbf_cx_0;         
								                                                    
   assign		arbcp7_cpxdp_grant_bufp1_ca_l_0	   =       ~  arbcp7_cpxdp_grant_arbbf_ca_0;      	
   assign		arbcp7_cpxdp_q0_hold_bufp1_ca_0	   =       ~ arbcp7_cpxdp_q0_hold_arbbf_ca_l_0;  
   assign		arbcp7_cpxdp_qsel0_bufp1_ca_l_0	   =       ~ arbcp7_cpxdp_qsel0_arbbf_ca_0;      
   assign		arbcp7_cpxdp_qsel1_bufp1_ca_0	   =       ~ arbcp7_cpxdp_qsel1_arbbf_ca_l_0;    
   assign		arbcp7_cpxdp_shift_bufp1_cx_l_0	   =       ~ arbcp7_cpxdp_shift_arbbf_cx_0;         

   								
   assign		arbcp0_cpxdp_grant_bufp1_ca_l_1	   =       ~  arbcp0_cpxdp_grant_arbbf_ca_1;      	
   assign		arbcp0_cpxdp_q0_hold_bufp1_ca_1	   =       ~ arbcp0_cpxdp_q0_hold_arbbf_ca_l_1;  
   assign		arbcp0_cpxdp_qsel0_bufp1_ca_l_1	   =       ~ arbcp0_cpxdp_qsel0_arbbf_ca_1;      
   assign		arbcp0_cpxdp_qsel1_bufp1_ca_1	   =       ~ arbcp0_cpxdp_qsel1_arbbf_ca_l_1;    
   assign		arbcp0_cpxdp_shift_bufp1_cx_l_1	   =       ~ arbcp0_cpxdp_shift_arbbf_cx_1;      
								                                                    
   assign		arbcp1_cpxdp_grant_bufp1_ca_l_1	   =       ~  arbcp1_cpxdp_grant_arbbf_ca_1;      	
   assign		arbcp1_cpxdp_q0_hold_bufp1_ca_1	   =       ~ arbcp1_cpxdp_q0_hold_arbbf_ca_l_1;  
   assign		arbcp1_cpxdp_qsel0_bufp1_ca_l_1	   =       ~ arbcp1_cpxdp_qsel0_arbbf_ca_1;      
   assign		arbcp1_cpxdp_qsel1_bufp1_ca_1	   =       ~ arbcp1_cpxdp_qsel1_arbbf_ca_l_1;    
   assign		arbcp1_cpxdp_shift_bufp1_cx_l_1	   =       ~ arbcp1_cpxdp_shift_arbbf_cx_1;      
								                                                    
   assign		arbcp2_cpxdp_grant_bufp1_ca_l_1	   =       ~  arbcp2_cpxdp_grant_arbbf_ca_1;      	
   assign		arbcp2_cpxdp_q0_hold_bufp1_ca_1	   =       ~ arbcp2_cpxdp_q0_hold_arbbf_ca_l_1;  
   assign		arbcp2_cpxdp_qsel0_bufp1_ca_l_1	   =       ~ arbcp2_cpxdp_qsel0_arbbf_ca_1;      
   assign		arbcp2_cpxdp_qsel1_bufp1_ca_1	   =       ~ arbcp2_cpxdp_qsel1_arbbf_ca_l_1;    
   assign		arbcp2_cpxdp_shift_bufp1_cx_l_1	   =       ~ arbcp2_cpxdp_shift_arbbf_cx_1;      
								                                                    
   assign		arbcp3_cpxdp_grant_bufp1_ca_l_1	   =       ~  arbcp3_cpxdp_grant_arbbf_ca_1;      	
   assign		arbcp3_cpxdp_q0_hold_bufp1_ca_1	   =       ~ arbcp3_cpxdp_q0_hold_arbbf_ca_l_1;  
   assign		arbcp3_cpxdp_qsel0_bufp1_ca_l_1	   =       ~ arbcp3_cpxdp_qsel0_arbbf_ca_1;      
   assign		arbcp3_cpxdp_qsel1_bufp1_ca_1	   =       ~ arbcp3_cpxdp_qsel1_arbbf_ca_l_1;    
   assign		arbcp3_cpxdp_shift_bufp1_cx_l_1	   =       ~ arbcp3_cpxdp_shift_arbbf_cx_1;      
								                                                    
   assign		arbcp4_cpxdp_grant_bufp1_ca_l_1	   =       ~  arbcp4_cpxdp_grant_arbbf_ca_1;      	
   assign		arbcp4_cpxdp_q0_hold_bufp1_ca_1	   =       ~ arbcp4_cpxdp_q0_hold_arbbf_ca_l_1;  
   assign		arbcp4_cpxdp_qsel0_bufp1_ca_l_1	   =       ~ arbcp4_cpxdp_qsel0_arbbf_ca_1;      
   assign		arbcp4_cpxdp_qsel1_bufp1_ca_1	   =       ~ arbcp4_cpxdp_qsel1_arbbf_ca_l_1;    
   assign		arbcp4_cpxdp_shift_bufp1_cx_l_1	   =       ~ arbcp4_cpxdp_shift_arbbf_cx_1;      
								                                                    
   assign		arbcp5_cpxdp_grant_bufp1_ca_l_1	   =       ~  arbcp5_cpxdp_grant_arbbf_ca_1;      	
   assign		arbcp5_cpxdp_q0_hold_bufp1_ca_1	   =       ~ arbcp5_cpxdp_q0_hold_arbbf_ca_l_1;  
   assign		arbcp5_cpxdp_qsel0_bufp1_ca_l_1	   =       ~ arbcp5_cpxdp_qsel0_arbbf_ca_1;      
   assign		arbcp5_cpxdp_qsel1_bufp1_ca_1	   =       ~ arbcp5_cpxdp_qsel1_arbbf_ca_l_1;    
   assign		arbcp5_cpxdp_shift_bufp1_cx_l_1	   =       ~ arbcp5_cpxdp_shift_arbbf_cx_1;         
								                                                    
   assign		arbcp6_cpxdp_grant_bufp1_ca_l_1	   =       ~  arbcp6_cpxdp_grant_arbbf_ca_1;      	
   assign		arbcp6_cpxdp_q0_hold_bufp1_ca_1	   =       ~ arbcp6_cpxdp_q0_hold_arbbf_ca_l_1;  
   assign		arbcp6_cpxdp_qsel0_bufp1_ca_l_1	   =       ~ arbcp6_cpxdp_qsel0_arbbf_ca_1;      
   assign		arbcp6_cpxdp_qsel1_bufp1_ca_1	   =       ~ arbcp6_cpxdp_qsel1_arbbf_ca_l_1;    
   assign		arbcp6_cpxdp_shift_bufp1_cx_l_1	   =       ~ arbcp6_cpxdp_shift_arbbf_cx_1;         
								                                                    
   assign		arbcp7_cpxdp_grant_bufp1_ca_l_1	   =       ~  arbcp7_cpxdp_grant_arbbf_ca_1;      	
   assign		arbcp7_cpxdp_q0_hold_bufp1_ca_1	   =       ~ arbcp7_cpxdp_q0_hold_arbbf_ca_l_1;  
   assign		arbcp7_cpxdp_qsel0_bufp1_ca_l_1	   =       ~ arbcp7_cpxdp_qsel0_arbbf_ca_1;      
   assign		arbcp7_cpxdp_qsel1_bufp1_ca_1	   =       ~ arbcp7_cpxdp_qsel1_arbbf_ca_l_1;    
   assign		arbcp7_cpxdp_shift_bufp1_cx_l_1	   =       ~ arbcp7_cpxdp_shift_arbbf_cx_1;         

   								
endmodule 
