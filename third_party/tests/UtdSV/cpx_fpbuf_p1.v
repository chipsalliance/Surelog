// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: cpx_fpbuf_p1.v
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
module cpx_fpbuf_p1(/*AUTOARG*/
   // Outputs
   fp_cpx_req_bufp1_cq, arbcp0_cpxdp_grant_bufp1_ca_l_1, 
   arbcp0_cpxdp_q0_hold_bufp1_ca_1, arbcp0_cpxdp_qsel0_bufp1_ca_l_1, 
   arbcp0_cpxdp_qsel1_bufp1_ca_1, arbcp0_cpxdp_shift_bufp1_cx_l_1, 
   arbcp1_cpxdp_grant_bufp1_ca_l_1, arbcp1_cpxdp_q0_hold_bufp1_ca_1, 
   arbcp1_cpxdp_qsel0_bufp1_ca_l_1, arbcp1_cpxdp_qsel1_bufp1_ca_1, 
   arbcp1_cpxdp_shift_bufp1_cx_l_1, arbcp2_cpxdp_grant_bufp1_ca_l_1, 
   arbcp2_cpxdp_q0_hold_bufp1_ca_1, arbcp2_cpxdp_qsel0_bufp1_ca_l_1, 
   arbcp2_cpxdp_qsel1_bufp1_ca_1, arbcp2_cpxdp_shift_bufp1_cx_l_1, 
   arbcp3_cpxdp_grant_bufp1_ca_l_1, arbcp3_cpxdp_q0_hold_bufp1_ca_1, 
   arbcp3_cpxdp_qsel0_bufp1_ca_l_1, arbcp3_cpxdp_qsel1_bufp1_ca_1, 
   arbcp3_cpxdp_shift_bufp1_cx_l_1, arbcp4_cpxdp_grant_bufp1_ca_l_1, 
   arbcp4_cpxdp_q0_hold_bufp1_ca_1, arbcp4_cpxdp_qsel0_bufp1_ca_l_1, 
   arbcp4_cpxdp_qsel1_bufp1_ca_1, arbcp4_cpxdp_shift_bufp1_cx_l_1, 
   arbcp5_cpxdp_grant_bufp1_ca_l_1, arbcp5_cpxdp_q0_hold_bufp1_ca_1, 
   arbcp5_cpxdp_qsel0_bufp1_ca_l_1, arbcp5_cpxdp_qsel1_bufp1_ca_1, 
   arbcp5_cpxdp_shift_bufp1_cx_l_1, arbcp6_cpxdp_grant_bufp1_ca_l_1, 
   arbcp6_cpxdp_q0_hold_bufp1_ca_1, arbcp6_cpxdp_qsel0_bufp1_ca_l_1, 
   arbcp6_cpxdp_qsel1_bufp1_ca_1, arbcp6_cpxdp_shift_bufp1_cx_l_1, 
   arbcp7_cpxdp_grant_bufp1_ca_l_1, arbcp7_cpxdp_q0_hold_bufp1_ca_1, 
   arbcp7_cpxdp_qsel0_bufp1_ca_l_1, arbcp7_cpxdp_qsel1_bufp1_ca_1, 
   arbcp7_cpxdp_shift_bufp1_cx_l_1, 
   // Inputs
   fp_cpx_req_bufp0_cq, arbcp0_cpxdp_grant_arbbf_ca_1, 
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


output	[7:0]	fp_cpx_req_bufp1_cq;

input	[7:0]	fp_cpx_req_bufp0_cq;

   output               arbcp0_cpxdp_grant_bufp1_ca_l_1         ;
   output               arbcp0_cpxdp_q0_hold_bufp1_ca_1         ;
   output               arbcp0_cpxdp_qsel0_bufp1_ca_l_1         ;
   output               arbcp0_cpxdp_qsel1_bufp1_ca_1           ;
   output               arbcp0_cpxdp_shift_bufp1_cx_l_1         ;

   output               arbcp1_cpxdp_grant_bufp1_ca_l_1         ;
   output               arbcp1_cpxdp_q0_hold_bufp1_ca_1         ;
   output               arbcp1_cpxdp_qsel0_bufp1_ca_l_1         ;
   output               arbcp1_cpxdp_qsel1_bufp1_ca_1           ;
   output               arbcp1_cpxdp_shift_bufp1_cx_l_1         ;

   output               arbcp2_cpxdp_grant_bufp1_ca_l_1         ;
   output               arbcp2_cpxdp_q0_hold_bufp1_ca_1         ;
   output               arbcp2_cpxdp_qsel0_bufp1_ca_l_1         ;
   output               arbcp2_cpxdp_qsel1_bufp1_ca_1           ;
   output               arbcp2_cpxdp_shift_bufp1_cx_l_1         ;

   output               arbcp3_cpxdp_grant_bufp1_ca_l_1         ;
   output               arbcp3_cpxdp_q0_hold_bufp1_ca_1         ;
   output               arbcp3_cpxdp_qsel0_bufp1_ca_l_1         ;
   output               arbcp3_cpxdp_qsel1_bufp1_ca_1           ;
   output               arbcp3_cpxdp_shift_bufp1_cx_l_1         ;

   output               arbcp4_cpxdp_grant_bufp1_ca_l_1         ;
   output               arbcp4_cpxdp_q0_hold_bufp1_ca_1         ;
   output               arbcp4_cpxdp_qsel0_bufp1_ca_l_1         ;
   output               arbcp4_cpxdp_qsel1_bufp1_ca_1           ;
   output               arbcp4_cpxdp_shift_bufp1_cx_l_1         ;

   output               arbcp5_cpxdp_grant_bufp1_ca_l_1         ;
   output               arbcp5_cpxdp_q0_hold_bufp1_ca_1         ;
   output               arbcp5_cpxdp_qsel0_bufp1_ca_l_1         ;
   output               arbcp5_cpxdp_qsel1_bufp1_ca_1           ;
   output               arbcp5_cpxdp_shift_bufp1_cx_l_1         ;

   output               arbcp6_cpxdp_grant_bufp1_ca_l_1         ;
   output               arbcp6_cpxdp_q0_hold_bufp1_ca_1         ;
   output               arbcp6_cpxdp_qsel0_bufp1_ca_l_1         ;
   output               arbcp6_cpxdp_qsel1_bufp1_ca_1           ;
   output               arbcp6_cpxdp_shift_bufp1_cx_l_1         ;

   output               arbcp7_cpxdp_grant_bufp1_ca_l_1         ;
   output               arbcp7_cpxdp_q0_hold_bufp1_ca_1         ;
   output               arbcp7_cpxdp_qsel0_bufp1_ca_l_1         ;
   output               arbcp7_cpxdp_qsel1_bufp1_ca_1           ;
   output               arbcp7_cpxdp_shift_bufp1_cx_l_1         ;

   input                arbcp0_cpxdp_grant_arbbf_ca_1;
   input                arbcp0_cpxdp_q0_hold_arbbf_ca_l_1;
   input                arbcp0_cpxdp_qsel0_arbbf_ca_1;
   input                arbcp0_cpxdp_qsel1_arbbf_ca_l_1;
   input                arbcp0_cpxdp_shift_arbbf_cx_1;

   input                arbcp1_cpxdp_grant_arbbf_ca_1;
   input                arbcp1_cpxdp_q0_hold_arbbf_ca_l_1;
   input                arbcp1_cpxdp_qsel0_arbbf_ca_1;
   input                arbcp1_cpxdp_qsel1_arbbf_ca_l_1;
   input                arbcp1_cpxdp_shift_arbbf_cx_1;

   input                arbcp2_cpxdp_grant_arbbf_ca_1;
   input                arbcp2_cpxdp_q0_hold_arbbf_ca_l_1;
   input                arbcp2_cpxdp_qsel0_arbbf_ca_1;
   input                arbcp2_cpxdp_qsel1_arbbf_ca_l_1;
   input                arbcp2_cpxdp_shift_arbbf_cx_1;

   input                arbcp3_cpxdp_grant_arbbf_ca_1;
   input                arbcp3_cpxdp_q0_hold_arbbf_ca_l_1;
   input                arbcp3_cpxdp_qsel0_arbbf_ca_1;
   input                arbcp3_cpxdp_qsel1_arbbf_ca_l_1;
   input                arbcp3_cpxdp_shift_arbbf_cx_1;

   input                arbcp4_cpxdp_grant_arbbf_ca_1;
   input                arbcp4_cpxdp_q0_hold_arbbf_ca_l_1;
   input                arbcp4_cpxdp_qsel0_arbbf_ca_1;
   input                arbcp4_cpxdp_qsel1_arbbf_ca_l_1;
   input                arbcp4_cpxdp_shift_arbbf_cx_1;

   input                arbcp5_cpxdp_grant_arbbf_ca_1;
   input                arbcp5_cpxdp_q0_hold_arbbf_ca_l_1;
   input                arbcp5_cpxdp_qsel0_arbbf_ca_1;
   input                arbcp5_cpxdp_qsel1_arbbf_ca_l_1;
   input                arbcp5_cpxdp_shift_arbbf_cx_1;

   input                arbcp6_cpxdp_grant_arbbf_ca_1;
   input                arbcp6_cpxdp_q0_hold_arbbf_ca_l_1;
   input                arbcp6_cpxdp_qsel0_arbbf_ca_1;
   input                arbcp6_cpxdp_qsel1_arbbf_ca_l_1;
   input                arbcp6_cpxdp_shift_arbbf_cx_1;

   input                arbcp7_cpxdp_grant_arbbf_ca_1;
   input                arbcp7_cpxdp_q0_hold_arbbf_ca_l_1;
   input                arbcp7_cpxdp_qsel0_arbbf_ca_1;
   input                arbcp7_cpxdp_qsel1_arbbf_ca_l_1;
   input                arbcp7_cpxdp_shift_arbbf_cx_1;


assign               fp_cpx_req_bufp1_cq[7:0]                =   fp_cpx_req_bufp0_cq[7:0];



   assign               arbcp0_cpxdp_grant_bufp1_ca_l_1    =       ~  arbcp0_cpxdp_grant_arbbf_ca_1;
   assign               arbcp0_cpxdp_q0_hold_bufp1_ca_1    =       ~ arbcp0_cpxdp_q0_hold_arbbf_ca_l_1;
   assign               arbcp0_cpxdp_qsel0_bufp1_ca_l_1    =       ~ arbcp0_cpxdp_qsel0_arbbf_ca_1;
   assign               arbcp0_cpxdp_qsel1_bufp1_ca_1      =       ~ arbcp0_cpxdp_qsel1_arbbf_ca_l_1;
   assign               arbcp0_cpxdp_shift_bufp1_cx_l_1    =       ~ arbcp0_cpxdp_shift_arbbf_cx_1;

   assign               arbcp1_cpxdp_grant_bufp1_ca_l_1    =       ~  arbcp1_cpxdp_grant_arbbf_ca_1;
   assign               arbcp1_cpxdp_q0_hold_bufp1_ca_1    =       ~ arbcp1_cpxdp_q0_hold_arbbf_ca_l_1;
   assign               arbcp1_cpxdp_qsel0_bufp1_ca_l_1    =       ~ arbcp1_cpxdp_qsel0_arbbf_ca_1;
   assign               arbcp1_cpxdp_qsel1_bufp1_ca_1      =       ~ arbcp1_cpxdp_qsel1_arbbf_ca_l_1;
   assign               arbcp1_cpxdp_shift_bufp1_cx_l_1    =       ~ arbcp1_cpxdp_shift_arbbf_cx_1;

   assign               arbcp2_cpxdp_grant_bufp1_ca_l_1    =       ~  arbcp2_cpxdp_grant_arbbf_ca_1;
   assign               arbcp2_cpxdp_q0_hold_bufp1_ca_1    =       ~ arbcp2_cpxdp_q0_hold_arbbf_ca_l_1;
   assign               arbcp2_cpxdp_qsel0_bufp1_ca_l_1    =       ~ arbcp2_cpxdp_qsel0_arbbf_ca_1;
   assign               arbcp2_cpxdp_qsel1_bufp1_ca_1      =       ~ arbcp2_cpxdp_qsel1_arbbf_ca_l_1;
   assign               arbcp2_cpxdp_shift_bufp1_cx_l_1    =       ~ arbcp2_cpxdp_shift_arbbf_cx_1;

   assign               arbcp3_cpxdp_grant_bufp1_ca_l_1    =       ~  arbcp3_cpxdp_grant_arbbf_ca_1;
   assign               arbcp3_cpxdp_q0_hold_bufp1_ca_1    =       ~ arbcp3_cpxdp_q0_hold_arbbf_ca_l_1;
   assign               arbcp3_cpxdp_qsel0_bufp1_ca_l_1    =       ~ arbcp3_cpxdp_qsel0_arbbf_ca_1;
   assign               arbcp3_cpxdp_qsel1_bufp1_ca_1      =       ~ arbcp3_cpxdp_qsel1_arbbf_ca_l_1;
   assign               arbcp3_cpxdp_shift_bufp1_cx_l_1    =       ~ arbcp3_cpxdp_shift_arbbf_cx_1;

   assign               arbcp4_cpxdp_grant_bufp1_ca_l_1    =       ~  arbcp4_cpxdp_grant_arbbf_ca_1;
   assign               arbcp4_cpxdp_q0_hold_bufp1_ca_1    =       ~ arbcp4_cpxdp_q0_hold_arbbf_ca_l_1;
   assign               arbcp4_cpxdp_qsel0_bufp1_ca_l_1    =       ~ arbcp4_cpxdp_qsel0_arbbf_ca_1;
   assign               arbcp4_cpxdp_qsel1_bufp1_ca_1      =       ~ arbcp4_cpxdp_qsel1_arbbf_ca_l_1;
   assign               arbcp4_cpxdp_shift_bufp1_cx_l_1    =       ~ arbcp4_cpxdp_shift_arbbf_cx_1;

   assign               arbcp5_cpxdp_grant_bufp1_ca_l_1    =       ~  arbcp5_cpxdp_grant_arbbf_ca_1;
   assign               arbcp5_cpxdp_q0_hold_bufp1_ca_1    =       ~ arbcp5_cpxdp_q0_hold_arbbf_ca_l_1;
   assign               arbcp5_cpxdp_qsel0_bufp1_ca_l_1    =       ~ arbcp5_cpxdp_qsel0_arbbf_ca_1;
   assign               arbcp5_cpxdp_qsel1_bufp1_ca_1      =       ~ arbcp5_cpxdp_qsel1_arbbf_ca_l_1;
   assign               arbcp5_cpxdp_shift_bufp1_cx_l_1    =       ~ arbcp5_cpxdp_shift_arbbf_cx_1;

   assign               arbcp6_cpxdp_grant_bufp1_ca_l_1    =       ~  arbcp6_cpxdp_grant_arbbf_ca_1;
   assign               arbcp6_cpxdp_q0_hold_bufp1_ca_1    =       ~ arbcp6_cpxdp_q0_hold_arbbf_ca_l_1;
   assign               arbcp6_cpxdp_qsel0_bufp1_ca_l_1    =       ~ arbcp6_cpxdp_qsel0_arbbf_ca_1;
   assign               arbcp6_cpxdp_qsel1_bufp1_ca_1      =       ~ arbcp6_cpxdp_qsel1_arbbf_ca_l_1;
   assign               arbcp6_cpxdp_shift_bufp1_cx_l_1    =       ~ arbcp6_cpxdp_shift_arbbf_cx_1;

   assign               arbcp7_cpxdp_grant_bufp1_ca_l_1    =       ~  arbcp7_cpxdp_grant_arbbf_ca_1;
   assign               arbcp7_cpxdp_q0_hold_bufp1_ca_1    =       ~ arbcp7_cpxdp_q0_hold_arbbf_ca_l_1;
   assign               arbcp7_cpxdp_qsel0_bufp1_ca_l_1    =       ~ arbcp7_cpxdp_qsel0_arbbf_ca_1;
   assign               arbcp7_cpxdp_qsel1_bufp1_ca_1      =       ~ arbcp7_cpxdp_qsel1_arbbf_ca_l_1;
   assign               arbcp7_cpxdp_shift_bufp1_cx_l_1    =       ~ arbcp7_cpxdp_shift_arbbf_cx_1;

endmodule
