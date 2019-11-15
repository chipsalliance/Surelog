// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: cpx_buf_p3.v
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

module cpx_buf_p3(/*AUTOARG*/
   // Outputs
   scache3_cpx_req_bufp3_cq, scache3_cpx_atom_bufp3_cq, 
   io_cpx_req_bufp3_cq, cpx_scache3_grant_bufp3_ca_l, 
   cpx_spc5_data_rdy_bufp3_cx, cpx_spc6_data_rdy_bufp3_cx, 
   cpx_spc7_data_rdy_bufp3_cx, arbcp0_cpxdp_grant_bufp3_ca_l_5, 
   arbcp0_cpxdp_q0_hold_bufp3_ca_5, arbcp0_cpxdp_qsel0_bufp3_ca_l_5, 
   arbcp0_cpxdp_qsel1_bufp3_ca_5, arbcp0_cpxdp_shift_bufp3_cx_l_5, 
   arbcp1_cpxdp_grant_bufp3_ca_l_5, arbcp1_cpxdp_q0_hold_bufp3_ca_5, 
   arbcp1_cpxdp_qsel0_bufp3_ca_l_5, arbcp1_cpxdp_qsel1_bufp3_ca_5, 
   arbcp1_cpxdp_shift_bufp3_cx_l_5, arbcp2_cpxdp_grant_bufp3_ca_l_5, 
   arbcp2_cpxdp_q0_hold_bufp3_ca_5, arbcp2_cpxdp_qsel0_bufp3_ca_l_5, 
   arbcp2_cpxdp_qsel1_bufp3_ca_5, arbcp2_cpxdp_shift_bufp3_cx_l_5, 
   arbcp3_cpxdp_grant_bufp3_ca_l_5, arbcp3_cpxdp_q0_hold_bufp3_ca_5, 
   arbcp3_cpxdp_qsel0_bufp3_ca_l_5, arbcp3_cpxdp_qsel1_bufp3_ca_5, 
   arbcp3_cpxdp_shift_bufp3_cx_l_5, arbcp4_cpxdp_grant_bufp3_ca_l_5, 
   arbcp4_cpxdp_q0_hold_bufp3_ca_5, arbcp4_cpxdp_qsel0_bufp3_ca_l_5, 
   arbcp4_cpxdp_qsel1_bufp3_ca_5, arbcp4_cpxdp_shift_bufp3_cx_l_5, 
   arbcp5_cpxdp_grant_bufp3_ca_l_5, arbcp5_cpxdp_q0_hold_bufp3_ca_5, 
   arbcp5_cpxdp_qsel0_bufp3_ca_l_5, arbcp5_cpxdp_qsel1_bufp3_ca_5, 
   arbcp5_cpxdp_shift_bufp3_cx_l_5, arbcp6_cpxdp_grant_bufp3_ca_l_5, 
   arbcp6_cpxdp_q0_hold_bufp3_ca_5, arbcp6_cpxdp_qsel0_bufp3_ca_l_5, 
   arbcp6_cpxdp_qsel1_bufp3_ca_5, arbcp6_cpxdp_shift_bufp3_cx_l_5, 
   arbcp7_cpxdp_grant_bufp3_ca_l_5, arbcp7_cpxdp_q0_hold_bufp3_ca_5, 
   arbcp7_cpxdp_qsel0_bufp3_ca_l_5, arbcp7_cpxdp_qsel1_bufp3_ca_5, 
   arbcp7_cpxdp_shift_bufp3_cx_l_5, arbcp0_cpxdp_grant_bufp3_ca_l_2, 
   arbcp0_cpxdp_q0_hold_bufp3_ca_2, arbcp0_cpxdp_qsel0_bufp3_ca_l_2, 
   arbcp0_cpxdp_qsel1_bufp3_ca_2, arbcp0_cpxdp_shift_bufp3_cx_l_2, 
   arbcp1_cpxdp_grant_bufp3_ca_l_2, arbcp1_cpxdp_q0_hold_bufp3_ca_2, 
   arbcp1_cpxdp_qsel0_bufp3_ca_l_2, arbcp1_cpxdp_qsel1_bufp3_ca_2, 
   arbcp1_cpxdp_shift_bufp3_cx_l_2, arbcp2_cpxdp_grant_bufp3_ca_l_2, 
   arbcp2_cpxdp_q0_hold_bufp3_ca_2, arbcp2_cpxdp_qsel0_bufp3_ca_l_2, 
   arbcp2_cpxdp_qsel1_bufp3_ca_2, arbcp2_cpxdp_shift_bufp3_cx_l_2, 
   arbcp3_cpxdp_grant_bufp3_ca_l_2, arbcp3_cpxdp_q0_hold_bufp3_ca_2, 
   arbcp3_cpxdp_qsel0_bufp3_ca_l_2, arbcp3_cpxdp_qsel1_bufp3_ca_2, 
   arbcp3_cpxdp_shift_bufp3_cx_l_2, arbcp4_cpxdp_grant_bufp3_ca_l_2, 
   arbcp4_cpxdp_q0_hold_bufp3_ca_2, arbcp4_cpxdp_qsel0_bufp3_ca_l_2, 
   arbcp4_cpxdp_qsel1_bufp3_ca_2, arbcp4_cpxdp_shift_bufp3_cx_l_2, 
   arbcp5_cpxdp_grant_bufp3_ca_l_2, arbcp5_cpxdp_q0_hold_bufp3_ca_2, 
   arbcp5_cpxdp_qsel0_bufp3_ca_l_2, arbcp5_cpxdp_qsel1_bufp3_ca_2, 
   arbcp5_cpxdp_shift_bufp3_cx_l_2, arbcp6_cpxdp_grant_bufp3_ca_l_2, 
   arbcp6_cpxdp_q0_hold_bufp3_ca_2, arbcp6_cpxdp_qsel0_bufp3_ca_l_2, 
   arbcp6_cpxdp_qsel1_bufp3_ca_2, arbcp6_cpxdp_shift_bufp3_cx_l_2, 
   arbcp7_cpxdp_grant_bufp3_ca_l_2, arbcp7_cpxdp_q0_hold_bufp3_ca_2, 
   arbcp7_cpxdp_qsel0_bufp3_ca_l_2, arbcp7_cpxdp_qsel1_bufp3_ca_2, 
   arbcp7_cpxdp_shift_bufp3_cx_l_2, 
   // Inputs
   scache3_cpx_req_bufp4_cq, scache3_cpx_atom_bufp4_cq, 
   io_cpx_req_bufp4_cq, cpx_scache3_grant_ca, cpx_spc5_data_rdy_cx, 
   cpx_spc6_data_rdy_cx, cpx_spc7_data_rdy_cx, 
   arbcp0_cpxdp_grant_arbbf_ca_5, arbcp0_cpxdp_q0_hold_arbbf_ca_l_5, 
   arbcp0_cpxdp_qsel0_arbbf_ca_5, arbcp0_cpxdp_qsel1_arbbf_ca_l_5, 
   arbcp0_cpxdp_shift_arbbf_cx_5, arbcp1_cpxdp_grant_arbbf_ca_5, 
   arbcp1_cpxdp_q0_hold_arbbf_ca_l_5, arbcp1_cpxdp_qsel0_arbbf_ca_5, 
   arbcp1_cpxdp_qsel1_arbbf_ca_l_5, arbcp1_cpxdp_shift_arbbf_cx_5, 
   arbcp2_cpxdp_grant_arbbf_ca_5, arbcp2_cpxdp_q0_hold_arbbf_ca_l_5, 
   arbcp2_cpxdp_qsel0_arbbf_ca_5, arbcp2_cpxdp_qsel1_arbbf_ca_l_5, 
   arbcp2_cpxdp_shift_arbbf_cx_5, arbcp3_cpxdp_grant_arbbf_ca_5, 
   arbcp3_cpxdp_q0_hold_arbbf_ca_l_5, arbcp3_cpxdp_qsel0_arbbf_ca_5, 
   arbcp3_cpxdp_qsel1_arbbf_ca_l_5, arbcp3_cpxdp_shift_arbbf_cx_5, 
   arbcp4_cpxdp_grant_arbbf_ca_5, arbcp4_cpxdp_q0_hold_arbbf_ca_l_5, 
   arbcp4_cpxdp_qsel0_arbbf_ca_5, arbcp4_cpxdp_qsel1_arbbf_ca_l_5, 
   arbcp4_cpxdp_shift_arbbf_cx_5, arbcp5_cpxdp_grant_arbbf_ca_5, 
   arbcp5_cpxdp_q0_hold_arbbf_ca_l_5, arbcp5_cpxdp_qsel0_arbbf_ca_5, 
   arbcp5_cpxdp_qsel1_arbbf_ca_l_5, arbcp5_cpxdp_shift_arbbf_cx_5, 
   arbcp6_cpxdp_grant_arbbf_ca_5, arbcp6_cpxdp_q0_hold_arbbf_ca_l_5, 
   arbcp6_cpxdp_qsel0_arbbf_ca_5, arbcp6_cpxdp_qsel1_arbbf_ca_l_5, 
   arbcp6_cpxdp_shift_arbbf_cx_5, arbcp7_cpxdp_grant_arbbf_ca_5, 
   arbcp7_cpxdp_q0_hold_arbbf_ca_l_5, arbcp7_cpxdp_qsel0_arbbf_ca_5, 
   arbcp7_cpxdp_qsel1_arbbf_ca_l_5, arbcp7_cpxdp_shift_arbbf_cx_5, 
   arbcp0_cpxdp_grant_arbbf_ca_2, arbcp0_cpxdp_q0_hold_arbbf_ca_l_2, 
   arbcp0_cpxdp_qsel0_arbbf_ca_2, arbcp0_cpxdp_qsel1_arbbf_ca_l_2, 
   arbcp0_cpxdp_shift_arbbf_cx_2, arbcp1_cpxdp_grant_arbbf_ca_2, 
   arbcp1_cpxdp_q0_hold_arbbf_ca_l_2, arbcp1_cpxdp_qsel0_arbbf_ca_2, 
   arbcp1_cpxdp_qsel1_arbbf_ca_l_2, arbcp1_cpxdp_shift_arbbf_cx_2, 
   arbcp2_cpxdp_grant_arbbf_ca_2, arbcp2_cpxdp_q0_hold_arbbf_ca_l_2, 
   arbcp2_cpxdp_qsel0_arbbf_ca_2, arbcp2_cpxdp_qsel1_arbbf_ca_l_2, 
   arbcp2_cpxdp_shift_arbbf_cx_2, arbcp3_cpxdp_grant_arbbf_ca_2, 
   arbcp3_cpxdp_q0_hold_arbbf_ca_l_2, arbcp3_cpxdp_qsel0_arbbf_ca_2, 
   arbcp3_cpxdp_qsel1_arbbf_ca_l_2, arbcp3_cpxdp_shift_arbbf_cx_2, 
   arbcp4_cpxdp_grant_arbbf_ca_2, arbcp4_cpxdp_q0_hold_arbbf_ca_l_2, 
   arbcp4_cpxdp_qsel0_arbbf_ca_2, arbcp4_cpxdp_qsel1_arbbf_ca_l_2, 
   arbcp4_cpxdp_shift_arbbf_cx_2, arbcp5_cpxdp_grant_arbbf_ca_2, 
   arbcp5_cpxdp_q0_hold_arbbf_ca_l_2, arbcp5_cpxdp_qsel0_arbbf_ca_2, 
   arbcp5_cpxdp_qsel1_arbbf_ca_l_2, arbcp5_cpxdp_shift_arbbf_cx_2, 
   arbcp6_cpxdp_grant_arbbf_ca_2, arbcp6_cpxdp_q0_hold_arbbf_ca_l_2, 
   arbcp6_cpxdp_qsel0_arbbf_ca_2, arbcp6_cpxdp_qsel1_arbbf_ca_l_2, 
   arbcp6_cpxdp_shift_arbbf_cx_2, arbcp7_cpxdp_grant_arbbf_ca_2, 
   arbcp7_cpxdp_q0_hold_arbbf_ca_l_2, arbcp7_cpxdp_qsel0_arbbf_ca_2, 
   arbcp7_cpxdp_qsel1_arbbf_ca_l_2, arbcp7_cpxdp_shift_arbbf_cx_2
   );
   
   output [7:0]		scache3_cpx_req_bufp3_cq		        ;	
   output 		scache3_cpx_atom_bufp3_cq		        ;	
   output [7:0]		io_cpx_req_bufp3_cq		        ;	
   output [7:0]		cpx_scache3_grant_bufp3_ca_l;
   output     		cpx_spc5_data_rdy_bufp3_cx;
   output     		cpx_spc6_data_rdy_bufp3_cx;
   output     		cpx_spc7_data_rdy_bufp3_cx;

   output 		arbcp0_cpxdp_grant_bufp3_ca_l_5		;	
   output 		arbcp0_cpxdp_q0_hold_bufp3_ca_5		;
   output 		arbcp0_cpxdp_qsel0_bufp3_ca_l_5		;	
   output 		arbcp0_cpxdp_qsel1_bufp3_ca_5		;	
   output 		arbcp0_cpxdp_shift_bufp3_cx_l_5		;	

   output 		arbcp1_cpxdp_grant_bufp3_ca_l_5		;	
   output 		arbcp1_cpxdp_q0_hold_bufp3_ca_5		;
   output 		arbcp1_cpxdp_qsel0_bufp3_ca_l_5		;	
   output 		arbcp1_cpxdp_qsel1_bufp3_ca_5		;	
   output 		arbcp1_cpxdp_shift_bufp3_cx_l_5		;	

   output 		arbcp2_cpxdp_grant_bufp3_ca_l_5		;	
   output 		arbcp2_cpxdp_q0_hold_bufp3_ca_5		;
   output 		arbcp2_cpxdp_qsel0_bufp3_ca_l_5		;	
   output 		arbcp2_cpxdp_qsel1_bufp3_ca_5		;	
   output 		arbcp2_cpxdp_shift_bufp3_cx_l_5		;	

   output 		arbcp3_cpxdp_grant_bufp3_ca_l_5		;	
   output 		arbcp3_cpxdp_q0_hold_bufp3_ca_5		;
   output 		arbcp3_cpxdp_qsel0_bufp3_ca_l_5		;	
   output 		arbcp3_cpxdp_qsel1_bufp3_ca_5		;	
   output 		arbcp3_cpxdp_shift_bufp3_cx_l_5		;	

   output 		arbcp4_cpxdp_grant_bufp3_ca_l_5		;	
   output 		arbcp4_cpxdp_q0_hold_bufp3_ca_5		;
   output 		arbcp4_cpxdp_qsel0_bufp3_ca_l_5		;	
   output 		arbcp4_cpxdp_qsel1_bufp3_ca_5		;	
   output 		arbcp4_cpxdp_shift_bufp3_cx_l_5		;	

   output 		arbcp5_cpxdp_grant_bufp3_ca_l_5		;	
   output 		arbcp5_cpxdp_q0_hold_bufp3_ca_5		;
   output 		arbcp5_cpxdp_qsel0_bufp3_ca_l_5		;	
   output 		arbcp5_cpxdp_qsel1_bufp3_ca_5		;	
   output 		arbcp5_cpxdp_shift_bufp3_cx_l_5		;	

   output 		arbcp6_cpxdp_grant_bufp3_ca_l_5		;	
   output 		arbcp6_cpxdp_q0_hold_bufp3_ca_5		;
   output 		arbcp6_cpxdp_qsel0_bufp3_ca_l_5		;	
   output 		arbcp6_cpxdp_qsel1_bufp3_ca_5		;	
   output 		arbcp6_cpxdp_shift_bufp3_cx_l_5		;	

   output 		arbcp7_cpxdp_grant_bufp3_ca_l_5		;	
   output 		arbcp7_cpxdp_q0_hold_bufp3_ca_5		;
   output 		arbcp7_cpxdp_qsel0_bufp3_ca_l_5		;	
   output 		arbcp7_cpxdp_qsel1_bufp3_ca_5		;	
   output 		arbcp7_cpxdp_shift_bufp3_cx_l_5		;	
   
   


   input [7:0]		scache3_cpx_req_bufp4_cq;	
   input 		scache3_cpx_atom_bufp4_cq;	
   input [7:0]		io_cpx_req_bufp4_cq;	
   input [7:0]		cpx_scache3_grant_ca;
   input     		cpx_spc5_data_rdy_cx;
   input     		cpx_spc6_data_rdy_cx;
   input     		cpx_spc7_data_rdy_cx;

   
   input 		arbcp0_cpxdp_grant_arbbf_ca_5;	
   input 		arbcp0_cpxdp_q0_hold_arbbf_ca_l_5;
   input 		arbcp0_cpxdp_qsel0_arbbf_ca_5;	
   input 		arbcp0_cpxdp_qsel1_arbbf_ca_l_5;	
   input 		arbcp0_cpxdp_shift_arbbf_cx_5;	

   input 		arbcp1_cpxdp_grant_arbbf_ca_5;	
   input 		arbcp1_cpxdp_q0_hold_arbbf_ca_l_5;
   input 		arbcp1_cpxdp_qsel0_arbbf_ca_5;	
   input 		arbcp1_cpxdp_qsel1_arbbf_ca_l_5;	
   input 		arbcp1_cpxdp_shift_arbbf_cx_5;	

   input 		arbcp2_cpxdp_grant_arbbf_ca_5;	
   input 		arbcp2_cpxdp_q0_hold_arbbf_ca_l_5;
   input 		arbcp2_cpxdp_qsel0_arbbf_ca_5;	
   input 		arbcp2_cpxdp_qsel1_arbbf_ca_l_5;	
   input 		arbcp2_cpxdp_shift_arbbf_cx_5;	

   input 		arbcp3_cpxdp_grant_arbbf_ca_5;	
   input 		arbcp3_cpxdp_q0_hold_arbbf_ca_l_5;
   input 		arbcp3_cpxdp_qsel0_arbbf_ca_5;	
   input 		arbcp3_cpxdp_qsel1_arbbf_ca_l_5;	
   input 		arbcp3_cpxdp_shift_arbbf_cx_5;	

   input 		arbcp4_cpxdp_grant_arbbf_ca_5;	
   input 		arbcp4_cpxdp_q0_hold_arbbf_ca_l_5;
   input 		arbcp4_cpxdp_qsel0_arbbf_ca_5;	
   input 		arbcp4_cpxdp_qsel1_arbbf_ca_l_5;	
   input 		arbcp4_cpxdp_shift_arbbf_cx_5;	

   input 		arbcp5_cpxdp_grant_arbbf_ca_5;	
   input 		arbcp5_cpxdp_q0_hold_arbbf_ca_l_5;
   input 		arbcp5_cpxdp_qsel0_arbbf_ca_5;	
   input 		arbcp5_cpxdp_qsel1_arbbf_ca_l_5;	
   input 		arbcp5_cpxdp_shift_arbbf_cx_5;	

   input 		arbcp6_cpxdp_grant_arbbf_ca_5;	
   input 		arbcp6_cpxdp_q0_hold_arbbf_ca_l_5;
   input 		arbcp6_cpxdp_qsel0_arbbf_ca_5;	
   input 		arbcp6_cpxdp_qsel1_arbbf_ca_l_5;	
   input 		arbcp6_cpxdp_shift_arbbf_cx_5;	

   input 		arbcp7_cpxdp_grant_arbbf_ca_5;	
   input 		arbcp7_cpxdp_q0_hold_arbbf_ca_l_5;
   input 		arbcp7_cpxdp_qsel0_arbbf_ca_5;	
   input 		arbcp7_cpxdp_qsel1_arbbf_ca_l_5;	
   input 		arbcp7_cpxdp_shift_arbbf_cx_5;	
   

   output 		arbcp0_cpxdp_grant_bufp3_ca_l_2		;	
   output 		arbcp0_cpxdp_q0_hold_bufp3_ca_2		;
   output 		arbcp0_cpxdp_qsel0_bufp3_ca_l_2		;	
   output 		arbcp0_cpxdp_qsel1_bufp3_ca_2		;	
   output 		arbcp0_cpxdp_shift_bufp3_cx_l_2		;	

   output 		arbcp1_cpxdp_grant_bufp3_ca_l_2		;	
   output 		arbcp1_cpxdp_q0_hold_bufp3_ca_2		;
   output 		arbcp1_cpxdp_qsel0_bufp3_ca_l_2		;	
   output 		arbcp1_cpxdp_qsel1_bufp3_ca_2		;	
   output 		arbcp1_cpxdp_shift_bufp3_cx_l_2		;	

   output 		arbcp2_cpxdp_grant_bufp3_ca_l_2		;	
   output 		arbcp2_cpxdp_q0_hold_bufp3_ca_2		;
   output 		arbcp2_cpxdp_qsel0_bufp3_ca_l_2		;	
   output 		arbcp2_cpxdp_qsel1_bufp3_ca_2		;	
   output 		arbcp2_cpxdp_shift_bufp3_cx_l_2		;	

   output 		arbcp3_cpxdp_grant_bufp3_ca_l_2		;	
   output 		arbcp3_cpxdp_q0_hold_bufp3_ca_2		;
   output 		arbcp3_cpxdp_qsel0_bufp3_ca_l_2		;	
   output 		arbcp3_cpxdp_qsel1_bufp3_ca_2		;	
   output 		arbcp3_cpxdp_shift_bufp3_cx_l_2		;	

   output 		arbcp4_cpxdp_grant_bufp3_ca_l_2		;	
   output 		arbcp4_cpxdp_q0_hold_bufp3_ca_2		;
   output 		arbcp4_cpxdp_qsel0_bufp3_ca_l_2		;	
   output 		arbcp4_cpxdp_qsel1_bufp3_ca_2		;	
   output 		arbcp4_cpxdp_shift_bufp3_cx_l_2		;	

   output 		arbcp5_cpxdp_grant_bufp3_ca_l_2		;	
   output 		arbcp5_cpxdp_q0_hold_bufp3_ca_2		;
   output 		arbcp5_cpxdp_qsel0_bufp3_ca_l_2		;	
   output 		arbcp5_cpxdp_qsel1_bufp3_ca_2		;	
   output 		arbcp5_cpxdp_shift_bufp3_cx_l_2		;	

   output 		arbcp6_cpxdp_grant_bufp3_ca_l_2		;	
   output 		arbcp6_cpxdp_q0_hold_bufp3_ca_2		;
   output 		arbcp6_cpxdp_qsel0_bufp3_ca_l_2		;	
   output 		arbcp6_cpxdp_qsel1_bufp3_ca_2		;	
   output 		arbcp6_cpxdp_shift_bufp3_cx_l_2		;	

   output 		arbcp7_cpxdp_grant_bufp3_ca_l_2		;	
   output 		arbcp7_cpxdp_q0_hold_bufp3_ca_2		;
   output 		arbcp7_cpxdp_qsel0_bufp3_ca_l_2		;	
   output 		arbcp7_cpxdp_qsel1_bufp3_ca_2		;	
   output 		arbcp7_cpxdp_shift_bufp3_cx_l_2		;	
   
   
   input 		arbcp0_cpxdp_grant_arbbf_ca_2;	
   input 		arbcp0_cpxdp_q0_hold_arbbf_ca_l_2;
   input 		arbcp0_cpxdp_qsel0_arbbf_ca_2;	
   input 		arbcp0_cpxdp_qsel1_arbbf_ca_l_2;	
   input 		arbcp0_cpxdp_shift_arbbf_cx_2;	

   input 		arbcp1_cpxdp_grant_arbbf_ca_2;	
   input 		arbcp1_cpxdp_q0_hold_arbbf_ca_l_2;
   input 		arbcp1_cpxdp_qsel0_arbbf_ca_2;	
   input 		arbcp1_cpxdp_qsel1_arbbf_ca_l_2;	
   input 		arbcp1_cpxdp_shift_arbbf_cx_2;	

   input 		arbcp2_cpxdp_grant_arbbf_ca_2;	
   input 		arbcp2_cpxdp_q0_hold_arbbf_ca_l_2;
   input 		arbcp2_cpxdp_qsel0_arbbf_ca_2;	
   input 		arbcp2_cpxdp_qsel1_arbbf_ca_l_2;	
   input 		arbcp2_cpxdp_shift_arbbf_cx_2;	

   input 		arbcp3_cpxdp_grant_arbbf_ca_2;	
   input 		arbcp3_cpxdp_q0_hold_arbbf_ca_l_2;
   input 		arbcp3_cpxdp_qsel0_arbbf_ca_2;	
   input 		arbcp3_cpxdp_qsel1_arbbf_ca_l_2;	
   input 		arbcp3_cpxdp_shift_arbbf_cx_2;	

   input 		arbcp4_cpxdp_grant_arbbf_ca_2;	
   input 		arbcp4_cpxdp_q0_hold_arbbf_ca_l_2;
   input 		arbcp4_cpxdp_qsel0_arbbf_ca_2;	
   input 		arbcp4_cpxdp_qsel1_arbbf_ca_l_2;	
   input 		arbcp4_cpxdp_shift_arbbf_cx_2;	

   input 		arbcp5_cpxdp_grant_arbbf_ca_2;	
   input 		arbcp5_cpxdp_q0_hold_arbbf_ca_l_2;
   input 		arbcp5_cpxdp_qsel0_arbbf_ca_2;	
   input 		arbcp5_cpxdp_qsel1_arbbf_ca_l_2;	
   input 		arbcp5_cpxdp_shift_arbbf_cx_2;	

   input 		arbcp6_cpxdp_grant_arbbf_ca_2;	
   input 		arbcp6_cpxdp_q0_hold_arbbf_ca_l_2;
   input 		arbcp6_cpxdp_qsel0_arbbf_ca_2;	
   input 		arbcp6_cpxdp_qsel1_arbbf_ca_l_2;	
   input 		arbcp6_cpxdp_shift_arbbf_cx_2;	

   input 		arbcp7_cpxdp_grant_arbbf_ca_2;	
   input 		arbcp7_cpxdp_q0_hold_arbbf_ca_l_2;
   input 		arbcp7_cpxdp_qsel0_arbbf_ca_2;	
   input 		arbcp7_cpxdp_qsel1_arbbf_ca_l_2;	
   input 		arbcp7_cpxdp_shift_arbbf_cx_2;	
   

   assign		scache3_cpx_req_bufp3_cq[7:0]		=        scache3_cpx_req_bufp4_cq[7:0];
   assign 		scache3_cpx_atom_bufp3_cq		=        scache3_cpx_atom_bufp4_cq;
   assign		io_cpx_req_bufp3_cq[7:0]		=        io_cpx_req_bufp4_cq[7:0];
   assign               cpx_scache3_grant_bufp3_ca_l =                   ~cpx_scache3_grant_ca;
   assign     		cpx_spc5_data_rdy_bufp3_cx              =         cpx_spc5_data_rdy_cx;
   assign     		cpx_spc6_data_rdy_bufp3_cx              =         cpx_spc6_data_rdy_cx;
   assign     		cpx_spc7_data_rdy_bufp3_cx              =         cpx_spc7_data_rdy_cx;
   
								
   assign		arbcp0_cpxdp_grant_bufp3_ca_l_5	   =       ~  arbcp0_cpxdp_grant_arbbf_ca_5;      	
   assign		arbcp0_cpxdp_q0_hold_bufp3_ca_5	   =       ~ arbcp0_cpxdp_q0_hold_arbbf_ca_l_5;  
   assign		arbcp0_cpxdp_qsel0_bufp3_ca_l_5	   =       ~ arbcp0_cpxdp_qsel0_arbbf_ca_5;      
   assign		arbcp0_cpxdp_qsel1_bufp3_ca_5	   =       ~ arbcp0_cpxdp_qsel1_arbbf_ca_l_5;    
   assign		arbcp0_cpxdp_shift_bufp3_cx_l_5	   =       ~ arbcp0_cpxdp_shift_arbbf_cx_5;      
								                                                    
   assign		arbcp1_cpxdp_grant_bufp3_ca_l_5	   =       ~  arbcp1_cpxdp_grant_arbbf_ca_5;      	
   assign		arbcp1_cpxdp_q0_hold_bufp3_ca_5	   =       ~ arbcp1_cpxdp_q0_hold_arbbf_ca_l_5;  
   assign		arbcp1_cpxdp_qsel0_bufp3_ca_l_5	   =       ~ arbcp1_cpxdp_qsel0_arbbf_ca_5;      
   assign		arbcp1_cpxdp_qsel1_bufp3_ca_5	   =       ~ arbcp1_cpxdp_qsel1_arbbf_ca_l_5;    
   assign		arbcp1_cpxdp_shift_bufp3_cx_l_5	   =       ~ arbcp1_cpxdp_shift_arbbf_cx_5;      
								                                                    
   assign		arbcp2_cpxdp_grant_bufp3_ca_l_5	   =       ~  arbcp2_cpxdp_grant_arbbf_ca_5;      	
   assign		arbcp2_cpxdp_q0_hold_bufp3_ca_5	   =       ~ arbcp2_cpxdp_q0_hold_arbbf_ca_l_5;  
   assign		arbcp2_cpxdp_qsel0_bufp3_ca_l_5	   =       ~ arbcp2_cpxdp_qsel0_arbbf_ca_5;      
   assign		arbcp2_cpxdp_qsel1_bufp3_ca_5	   =       ~ arbcp2_cpxdp_qsel1_arbbf_ca_l_5;    
   assign		arbcp2_cpxdp_shift_bufp3_cx_l_5	   =       ~ arbcp2_cpxdp_shift_arbbf_cx_5;      
								                                                    
   assign		arbcp3_cpxdp_grant_bufp3_ca_l_5	   =       ~  arbcp3_cpxdp_grant_arbbf_ca_5;      	
   assign		arbcp3_cpxdp_q0_hold_bufp3_ca_5	   =       ~ arbcp3_cpxdp_q0_hold_arbbf_ca_l_5;  
   assign		arbcp3_cpxdp_qsel0_bufp3_ca_l_5	   =       ~ arbcp3_cpxdp_qsel0_arbbf_ca_5;      
   assign		arbcp3_cpxdp_qsel1_bufp3_ca_5	   =       ~ arbcp3_cpxdp_qsel1_arbbf_ca_l_5;    
   assign		arbcp3_cpxdp_shift_bufp3_cx_l_5	   =       ~ arbcp3_cpxdp_shift_arbbf_cx_5;      
								                                                    
   assign		arbcp4_cpxdp_grant_bufp3_ca_l_5	   =       ~  arbcp4_cpxdp_grant_arbbf_ca_5;      	
   assign		arbcp4_cpxdp_q0_hold_bufp3_ca_5	   =       ~ arbcp4_cpxdp_q0_hold_arbbf_ca_l_5;  
   assign		arbcp4_cpxdp_qsel0_bufp3_ca_l_5	   =       ~ arbcp4_cpxdp_qsel0_arbbf_ca_5;      
   assign		arbcp4_cpxdp_qsel1_bufp3_ca_5	   =       ~ arbcp4_cpxdp_qsel1_arbbf_ca_l_5;    
   assign		arbcp4_cpxdp_shift_bufp3_cx_l_5	   =       ~ arbcp4_cpxdp_shift_arbbf_cx_5;      
								                                                    
   assign		arbcp5_cpxdp_grant_bufp3_ca_l_5	   =       ~  arbcp5_cpxdp_grant_arbbf_ca_5;      	
   assign		arbcp5_cpxdp_q0_hold_bufp3_ca_5	   =       ~ arbcp5_cpxdp_q0_hold_arbbf_ca_l_5;  
   assign		arbcp5_cpxdp_qsel0_bufp3_ca_l_5	   =       ~ arbcp5_cpxdp_qsel0_arbbf_ca_5;      
   assign		arbcp5_cpxdp_qsel1_bufp3_ca_5	   =       ~ arbcp5_cpxdp_qsel1_arbbf_ca_l_5;    
   assign		arbcp5_cpxdp_shift_bufp3_cx_l_5	   =       ~ arbcp5_cpxdp_shift_arbbf_cx_5;         
								                                                    
   assign		arbcp6_cpxdp_grant_bufp3_ca_l_5	   =       ~  arbcp6_cpxdp_grant_arbbf_ca_5;      	
   assign		arbcp6_cpxdp_q0_hold_bufp3_ca_5	   =       ~ arbcp6_cpxdp_q0_hold_arbbf_ca_l_5;  
   assign		arbcp6_cpxdp_qsel0_bufp3_ca_l_5	   =       ~ arbcp6_cpxdp_qsel0_arbbf_ca_5;      
   assign		arbcp6_cpxdp_qsel1_bufp3_ca_5	   =       ~ arbcp6_cpxdp_qsel1_arbbf_ca_l_5;    
   assign		arbcp6_cpxdp_shift_bufp3_cx_l_5	   =       ~ arbcp6_cpxdp_shift_arbbf_cx_5;         
								                                                    
   assign		arbcp7_cpxdp_grant_bufp3_ca_l_5	   =       ~  arbcp7_cpxdp_grant_arbbf_ca_5;      	
   assign		arbcp7_cpxdp_q0_hold_bufp3_ca_5	   =       ~ arbcp7_cpxdp_q0_hold_arbbf_ca_l_5;  
   assign		arbcp7_cpxdp_qsel0_bufp3_ca_l_5	   =       ~ arbcp7_cpxdp_qsel0_arbbf_ca_5;      
   assign		arbcp7_cpxdp_qsel1_bufp3_ca_5	   =       ~ arbcp7_cpxdp_qsel1_arbbf_ca_l_5;    
   assign		arbcp7_cpxdp_shift_bufp3_cx_l_5	   =       ~ arbcp7_cpxdp_shift_arbbf_cx_5;         

   assign               arbcp0_cpxdp_grant_bufp3_ca_l_2    =       ~  arbcp0_cpxdp_grant_arbbf_ca_2;
   assign               arbcp0_cpxdp_q0_hold_bufp3_ca_2    =       ~ arbcp0_cpxdp_q0_hold_arbbf_ca_l_2;
   assign               arbcp0_cpxdp_qsel0_bufp3_ca_l_2    =       ~ arbcp0_cpxdp_qsel0_arbbf_ca_2;
   assign               arbcp0_cpxdp_qsel1_bufp3_ca_2      =       ~ arbcp0_cpxdp_qsel1_arbbf_ca_l_2;
   assign               arbcp0_cpxdp_shift_bufp3_cx_l_2    =       ~ arbcp0_cpxdp_shift_arbbf_cx_2;
                                                       
   assign               arbcp1_cpxdp_grant_bufp3_ca_l_2    =       ~  arbcp1_cpxdp_grant_arbbf_ca_2;
   assign               arbcp1_cpxdp_q0_hold_bufp3_ca_2    =       ~ arbcp1_cpxdp_q0_hold_arbbf_ca_l_2;
   assign               arbcp1_cpxdp_qsel0_bufp3_ca_l_2    =       ~ arbcp1_cpxdp_qsel0_arbbf_ca_2;
   assign               arbcp1_cpxdp_qsel1_bufp3_ca_2      =       ~ arbcp1_cpxdp_qsel1_arbbf_ca_l_2;
   assign               arbcp1_cpxdp_shift_bufp3_cx_l_2    =       ~ arbcp1_cpxdp_shift_arbbf_cx_2;
                                                       
   assign               arbcp2_cpxdp_grant_bufp3_ca_l_2    =       ~  arbcp2_cpxdp_grant_arbbf_ca_2;
   assign               arbcp2_cpxdp_q0_hold_bufp3_ca_2    =       ~ arbcp2_cpxdp_q0_hold_arbbf_ca_l_2;
   assign               arbcp2_cpxdp_qsel0_bufp3_ca_l_2    =       ~ arbcp2_cpxdp_qsel0_arbbf_ca_2;
   assign               arbcp2_cpxdp_qsel1_bufp3_ca_2      =       ~ arbcp2_cpxdp_qsel1_arbbf_ca_l_2;
   assign               arbcp2_cpxdp_shift_bufp3_cx_l_2    =       ~ arbcp2_cpxdp_shift_arbbf_cx_2;
                                                       
   assign               arbcp3_cpxdp_grant_bufp3_ca_l_2    =       ~  arbcp3_cpxdp_grant_arbbf_ca_2;
   assign               arbcp3_cpxdp_q0_hold_bufp3_ca_2    =       ~ arbcp3_cpxdp_q0_hold_arbbf_ca_l_2;
   assign               arbcp3_cpxdp_qsel0_bufp3_ca_l_2    =       ~ arbcp3_cpxdp_qsel0_arbbf_ca_2;
   assign               arbcp3_cpxdp_qsel1_bufp3_ca_2      =       ~ arbcp3_cpxdp_qsel1_arbbf_ca_l_2;
   assign               arbcp3_cpxdp_shift_bufp3_cx_l_2    =       ~ arbcp3_cpxdp_shift_arbbf_cx_2;
                                                       
   assign               arbcp4_cpxdp_grant_bufp3_ca_l_2    =       ~  arbcp4_cpxdp_grant_arbbf_ca_2;
   assign               arbcp4_cpxdp_q0_hold_bufp3_ca_2    =       ~ arbcp4_cpxdp_q0_hold_arbbf_ca_l_2;
   assign               arbcp4_cpxdp_qsel0_bufp3_ca_l_2    =       ~ arbcp4_cpxdp_qsel0_arbbf_ca_2;
   assign               arbcp4_cpxdp_qsel1_bufp3_ca_2      =       ~ arbcp4_cpxdp_qsel1_arbbf_ca_l_2;
   assign               arbcp4_cpxdp_shift_bufp3_cx_l_2    =       ~ arbcp4_cpxdp_shift_arbbf_cx_2;
                                                       
   assign               arbcp5_cpxdp_grant_bufp3_ca_l_2    =       ~  arbcp5_cpxdp_grant_arbbf_ca_2;
   assign               arbcp5_cpxdp_q0_hold_bufp3_ca_2    =       ~ arbcp5_cpxdp_q0_hold_arbbf_ca_l_2;
   assign               arbcp5_cpxdp_qsel0_bufp3_ca_l_2    =       ~ arbcp5_cpxdp_qsel0_arbbf_ca_2;
   assign               arbcp5_cpxdp_qsel1_bufp3_ca_2      =       ~ arbcp5_cpxdp_qsel1_arbbf_ca_l_2;
   assign               arbcp5_cpxdp_shift_bufp3_cx_l_2    =       ~ arbcp5_cpxdp_shift_arbbf_cx_2;
                                                       
   assign               arbcp6_cpxdp_grant_bufp3_ca_l_2    =       ~  arbcp6_cpxdp_grant_arbbf_ca_2;
   assign               arbcp6_cpxdp_q0_hold_bufp3_ca_2    =       ~ arbcp6_cpxdp_q0_hold_arbbf_ca_l_2;
   assign               arbcp6_cpxdp_qsel0_bufp3_ca_l_2    =       ~ arbcp6_cpxdp_qsel0_arbbf_ca_2;
   assign               arbcp6_cpxdp_qsel1_bufp3_ca_2      =       ~ arbcp6_cpxdp_qsel1_arbbf_ca_l_2;
   assign               arbcp6_cpxdp_shift_bufp3_cx_l_2    =       ~ arbcp6_cpxdp_shift_arbbf_cx_2;
                                                       
   assign               arbcp7_cpxdp_grant_bufp3_ca_l_2    =       ~  arbcp7_cpxdp_grant_arbbf_ca_2;
   assign               arbcp7_cpxdp_q0_hold_bufp3_ca_2    =       ~ arbcp7_cpxdp_q0_hold_arbbf_ca_l_2;
   assign               arbcp7_cpxdp_qsel0_bufp3_ca_l_2    =       ~ arbcp7_cpxdp_qsel0_arbbf_ca_2;
   assign               arbcp7_cpxdp_qsel1_bufp3_ca_2      =       ~ arbcp7_cpxdp_qsel1_arbbf_ca_l_2;    
   assign               arbcp7_cpxdp_shift_bufp3_cx_l_2    =       ~ arbcp7_cpxdp_shift_arbbf_cx_2;


   

endmodule // cpx_grant_ff








