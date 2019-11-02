// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: cpx_buf_top.v
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
/////////////////////////////////////////////////////////////////////////
/*
//  Module Name: pcx_buf_top
//	Description:	file containing all buffering and flopping in the 
//    pcx. 
 //  
*/
////////////////////////////////////////////////////////////////////////
// Global header file includes
////////////////////////////////////////////////////////////////////////

`include	"sys.h" // system level definition file which contains the 
			// time scale definition

`include "iop.h"


////////////////////////////////////////////////////////////////////////
// Local header file includes / local defines
////////////////////////////////////////////////////////////////////////


  module cpx_buf_top(/*AUTOARG*/
   // Outputs
   sctag3_cpx_data_buf_ca, sctag2_cpx_data_buf_ca, 
   sctag1_cpx_data_buf_ca, sctag0_cpx_data_buf_ca, 
   scache3_cpx_req_bufp3_cq, scache3_cpx_atom_bufp3_cq, 
   scache2_cpx_req_bufpm_cq, scache2_cpx_atom_bufpm_cq, 
   scache1_cpx_req_bufpm_cq, scache1_cpx_atom_bufpm_cq, 
   scache0_cpx_req_bufp1_cq, scache0_cpx_atom_bufp1_cq, pt1_so_1, 
   io_cpx_req_bufp3_cq, io_cpx_req_buf1_io_cq, io_cpx_data_buf1_ca2, 
   fp_cpx_req_bufp1_cq, fp_cpx_data_buf_ca, cpx_spc7_data_rdy_cx2, 
   cpx_spc7_data_cx2, cpx_spc6_data_rdy_cx2, cpx_spc6_data_cx2, 
   cpx_spc5_data_rdy_cx2, cpx_spc5_data_cx2, cpx_spc4_data_rdy_cx2, 
   cpx_spc4_data_cx2, cpx_spc3_data_rdy_cx2, cpx_spc3_data_cx2, 
   cpx_spc2_data_rdy_cx2, cpx_spc2_data_cx2, cpx_spc1_data_rdy_cx2, 
   cpx_spc1_data_cx2, cpx_spc0_data_rdy_cx2, cpx_spc0_data_cx2, 
   cpx_scache3_grant_cx, cpx_scache2_grant_cx, cpx_scache1_grant_cx, 
   cpx_scache0_grant_cx, cpx_io_grant_cx2, cpx_buf_top_pt0_so_1, 
   arbcp7_cpxdp_shift_cx, arbcp7_cpxdp_qsel1_ca_l, 
   arbcp7_cpxdp_qsel0_ca, arbcp7_cpxdp_q0_hold_ca_l, 
   arbcp7_cpxdp_grant_ca, arbcp6_cpxdp_shift_cx, 
   arbcp6_cpxdp_qsel1_ca_l, arbcp6_cpxdp_qsel0_ca, 
   arbcp6_cpxdp_q0_hold_ca_l, arbcp6_cpxdp_grant_ca, 
   arbcp5_cpxdp_shift_cx, arbcp5_cpxdp_qsel1_ca_l, 
   arbcp5_cpxdp_qsel0_ca, arbcp5_cpxdp_q0_hold_ca_l, 
   arbcp5_cpxdp_grant_ca, arbcp4_cpxdp_shift_cx, 
   arbcp4_cpxdp_qsel1_ca_l, arbcp4_cpxdp_qsel0_ca, 
   arbcp4_cpxdp_q0_hold_ca_l, arbcp4_cpxdp_grant_ca, 
   arbcp3_cpxdp_shift_cx, arbcp3_cpxdp_qsel1_ca_l, 
   arbcp3_cpxdp_qsel0_ca, arbcp3_cpxdp_q0_hold_ca_l, 
   arbcp3_cpxdp_grant_ca, arbcp2_cpxdp_shift_cx, 
   arbcp2_cpxdp_qsel1_ca_l, arbcp2_cpxdp_qsel0_ca, 
   arbcp2_cpxdp_q0_hold_ca_l, arbcp2_cpxdp_grant_ca, 
   arbcp1_cpxdp_shift_cx, arbcp1_cpxdp_qsel1_ca_l, 
   arbcp1_cpxdp_qsel0_ca, arbcp1_cpxdp_q0_hold_ca_l, 
   arbcp1_cpxdp_grant_ca, arbcp0_cpxdp_shift_cx, 
   arbcp0_cpxdp_qsel1_ca_l, arbcp0_cpxdp_qsel0_ca, 
   arbcp0_cpxdp_q0_hold_ca_l, arbcp0_cpxdp_grant_ca, 
   // Inputs
   si_1, se_buf4_top, se_buf4_bottom, se_buf3_top, se_buf2_top, 
   se_buf2_bottom, se_buf0_middle, sctag3_cpx_data_ca, 
   sctag2_cpx_data_ca, sctag1_cpx_data_ca, sctag0_cpx_data_ca, 
   scache3_cpx_req_cq, scache3_cpx_atom_cq, scache2_cpx_req_cq, 
   scache2_cpx_atom_cq, scache1_cpx_req_cq, scache1_cpx_atom_cq, 
   scache0_cpx_req_cq, scache0_cpx_atom_cq, rclk, 
   pcx_scache2_dat_px2_so_1, io_cpx_req_cq, io_cpx_data_ca, 
   fp_cpx_req_cq, fp_cpx_data_ca, cpx_spc7_data_rdy_cx, 
   cpx_spc7_data_cx_l, cpx_spc6_data_rdy_cx, cpx_spc6_data_cx_l, 
   cpx_spc5_data_rdy_cx, cpx_spc5_data_cx_l, cpx_spc4_data_rdy_cx, 
   cpx_spc4_data_cx_l, cpx_spc3_data_rdy_cx, cpx_spc3_data_cx_l, 
   cpx_spc2_data_rdy_cx, cpx_spc2_data_cx_l, cpx_spc1_data_rdy_cx, 
   cpx_spc1_data_cx_l, cpx_spc0_data_rdy_cx, cpx_spc0_data_cx_l, 
   cpx_scache3_grant_ca, cpx_scache2_grant_ca, cpx_scache1_grant_ca, 
   cpx_scache0_grant_ca, cpx_io_grant_ca, 
   arbcp7_cpxdp_shift_arbbf_cx, arbcp7_cpxdp_qsel1_arbbf_ca_l, 
   arbcp7_cpxdp_qsel0_arbbf_ca, arbcp7_cpxdp_q0_hold_arbbf_ca_l, 
   arbcp7_cpxdp_grant_arbbf_ca, arbcp6_cpxdp_shift_arbbf_cx, 
   arbcp6_cpxdp_qsel1_arbbf_ca_l, arbcp6_cpxdp_qsel0_arbbf_ca, 
   arbcp6_cpxdp_q0_hold_arbbf_ca_l, arbcp6_cpxdp_grant_arbbf_ca, 
   arbcp5_cpxdp_shift_arbbf_cx, arbcp5_cpxdp_qsel1_arbbf_ca_l, 
   arbcp5_cpxdp_qsel0_arbbf_ca, arbcp5_cpxdp_q0_hold_arbbf_ca_l, 
   arbcp5_cpxdp_grant_arbbf_ca, arbcp4_cpxdp_shift_arbbf_cx, 
   arbcp4_cpxdp_qsel1_arbbf_ca_l, arbcp4_cpxdp_qsel0_arbbf_ca, 
   arbcp4_cpxdp_q0_hold_arbbf_ca_l, arbcp4_cpxdp_grant_arbbf_ca, 
   arbcp3_cpxdp_shift_arbbf_cx, arbcp3_cpxdp_qsel1_arbbf_ca_l, 
   arbcp3_cpxdp_qsel0_arbbf_ca, arbcp3_cpxdp_q0_hold_arbbf_ca_l, 
   arbcp3_cpxdp_grant_arbbf_ca, arbcp2_cpxdp_shift_arbbf_cx, 
   arbcp2_cpxdp_qsel1_arbbf_ca_l, arbcp2_cpxdp_qsel0_arbbf_ca, 
   arbcp2_cpxdp_q0_hold_arbbf_ca_l, arbcp2_cpxdp_grant_arbbf_ca, 
   arbcp1_cpxdp_shift_arbbf_cx, arbcp1_cpxdp_qsel1_arbbf_ca_l, 
   arbcp1_cpxdp_qsel0_arbbf_ca, arbcp1_cpxdp_q0_hold_arbbf_ca_l, 
   arbcp1_cpxdp_grant_arbbf_ca, arbcp0_cpxdp_shift_arbbf_cx, 
   arbcp0_cpxdp_qsel1_arbbf_ca_l, arbcp0_cpxdp_qsel0_arbbf_ca, 
   arbcp0_cpxdp_q0_hold_arbbf_ca_l, arbcp0_cpxdp_grant_arbbf_ca
   );

   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output [5:0]		arbcp0_cpxdp_grant_ca;	// From pm1_even of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp0_cpxdp_q0_hold_ca_l;// From pm1_even of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp0_cpxdp_qsel0_ca;	// From pm1_even of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp0_cpxdp_qsel1_ca_l;// From pm1_even of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp0_cpxdp_shift_cx;	// From pm1_even of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp1_cpxdp_grant_ca;	// From pm1_odd of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp1_cpxdp_q0_hold_ca_l;// From pm1_odd of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp1_cpxdp_qsel0_ca;	// From pm1_odd of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp1_cpxdp_qsel1_ca_l;// From pm1_odd of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp1_cpxdp_shift_cx;	// From pm1_odd of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp2_cpxdp_grant_ca;	// From pm1_even of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp2_cpxdp_q0_hold_ca_l;// From pm1_even of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp2_cpxdp_qsel0_ca;	// From pm1_even of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp2_cpxdp_qsel1_ca_l;// From pm1_even of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp2_cpxdp_shift_cx;	// From pm1_even of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp3_cpxdp_grant_ca;	// From pm1_odd of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp3_cpxdp_q0_hold_ca_l;// From pm1_odd of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp3_cpxdp_qsel0_ca;	// From pm1_odd of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp3_cpxdp_qsel1_ca_l;// From pm1_odd of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp3_cpxdp_shift_cx;	// From pm1_odd of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp4_cpxdp_grant_ca;	// From pm1_even of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp4_cpxdp_q0_hold_ca_l;// From pm1_even of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp4_cpxdp_qsel0_ca;	// From pm1_even of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp4_cpxdp_qsel1_ca_l;// From pm1_even of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp4_cpxdp_shift_cx;	// From pm1_even of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp5_cpxdp_grant_ca;	// From pm1_odd of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp5_cpxdp_q0_hold_ca_l;// From pm1_odd of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp5_cpxdp_qsel0_ca;	// From pm1_odd of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp5_cpxdp_qsel1_ca_l;// From pm1_odd of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp5_cpxdp_shift_cx;	// From pm1_odd of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp6_cpxdp_grant_ca;	// From pm1_even of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp6_cpxdp_q0_hold_ca_l;// From pm1_even of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp6_cpxdp_qsel0_ca;	// From pm1_even of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp6_cpxdp_qsel1_ca_l;// From pm1_even of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp6_cpxdp_shift_cx;	// From pm1_even of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp7_cpxdp_grant_ca;	// From pm1_odd of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp7_cpxdp_q0_hold_ca_l;// From pm1_odd of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp7_cpxdp_qsel0_ca;	// From pm1_odd of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp7_cpxdp_qsel1_ca_l;// From pm1_odd of cpx_buf_pm_even.v, ...
   output [5:0]		arbcp7_cpxdp_shift_cx;	// From pm1_odd of cpx_buf_pm_even.v, ...
   output		cpx_buf_top_pt0_so_1;	// From pt0 of cpx_buf_pt.v
   output [7:0]		cpx_io_grant_cx2;	// From ff_io_grant of cpx_io_grant_ff.v
   output [7:0]		cpx_scache0_grant_cx;	// From pt0 of cpx_buf_pt.v
   output [7:0]		cpx_scache1_grant_cx;	// From pt1 of cpx_buf_pt.v
   output [7:0]		cpx_scache2_grant_cx;	// From pt2 of cpx_buf_pt.v
   output [7:0]		cpx_scache3_grant_cx;	// From pt3 of cpx_buf_pt.v
   output [`CPX_WIDTH-1:0]cpx_spc0_data_cx2;	// From ff0 of cpx_datacx2_ff.v
   output		cpx_spc0_data_rdy_cx2;	// From ff0 of cpx_datacx2_ff.v
   output [`CPX_WIDTH-1:0]cpx_spc1_data_cx2;	// From ff1 of cpx_datacx2_ff.v
   output		cpx_spc1_data_rdy_cx2;	// From ff1 of cpx_datacx2_ff.v
   output [`CPX_WIDTH-1:0]cpx_spc2_data_cx2;	// From ff2 of cpx_datacx2_ff.v
   output		cpx_spc2_data_rdy_cx2;	// From ff2 of cpx_datacx2_ff.v
   output [`CPX_WIDTH-1:0]cpx_spc3_data_cx2;	// From ff3 of cpx_datacx2_ff.v
   output		cpx_spc3_data_rdy_cx2;	// From ff3 of cpx_datacx2_ff.v
   output [`CPX_WIDTH-1:0]cpx_spc4_data_cx2;	// From ff4 of cpx_datacx2_ff.v
   output		cpx_spc4_data_rdy_cx2;	// From ff4 of cpx_datacx2_ff.v
   output [`CPX_WIDTH-1:0]cpx_spc5_data_cx2;	// From ff5 of cpx_datacx2_ff.v
   output		cpx_spc5_data_rdy_cx2;	// From ff5 of cpx_datacx2_ff.v
   output [`CPX_WIDTH-1:0]cpx_spc6_data_cx2;	// From ff6 of cpx_datacx2_ff.v
   output		cpx_spc6_data_rdy_cx2;	// From ff6 of cpx_datacx2_ff.v
   output [`CPX_WIDTH-1:0]cpx_spc7_data_cx2;	// From ff7 of cpx_datacx2_ff.v
   output		cpx_spc7_data_rdy_cx2;	// From ff7 of cpx_datacx2_ff.v
   output [`CPX_WIDTH-1:0]fp_cpx_data_buf_ca;	// From buf_fp_cpx_data of cpx_databuf_ca.v
   output [7:0]		fp_cpx_req_bufp1_cq;	// From fpbuf_p1 of cpx_fpbuf_p1.v
   output [`CPX_WIDTH-1:0]io_cpx_data_buf1_ca2;	// From buf1_io_cpx_data of cpx_databuf_ca.v
   output [7:0]		io_cpx_req_buf1_io_cq;	// From buf1_io of cpx_buf_io.v
   output [7:0]		io_cpx_req_bufp3_cq;	// From p3 of cpx_buf_p3.v
   output		pt1_so_1;		// From pt1 of cpx_buf_pt.v
   output		scache0_cpx_atom_bufp1_cq;// From p1 of cpx_buf_p1.v
   output [7:0]		scache0_cpx_req_bufp1_cq;// From p1 of cpx_buf_p1.v
   output		scache1_cpx_atom_bufpm_cq;// From pm1 of cpx_buf_pm.v
   output [7:0]		scache1_cpx_req_bufpm_cq;// From pm1 of cpx_buf_pm.v
   output		scache2_cpx_atom_bufpm_cq;// From pm2 of cpx_buf_pm.v
   output [7:0]		scache2_cpx_req_bufpm_cq;// From pm2 of cpx_buf_pm.v
   output		scache3_cpx_atom_bufp3_cq;// From p3 of cpx_buf_p3.v
   output [7:0]		scache3_cpx_req_bufp3_cq;// From p3 of cpx_buf_p3.v
   output [`CPX_WIDTH-1:0]sctag0_cpx_data_buf_ca;// From buf_sctag0_cpx_data of cpx_databuf_ca.v
   output [`CPX_WIDTH-1:0]sctag1_cpx_data_buf_ca;// From buf_sctag1_cpx_data of cpx_databuf_ca.v
   output [`CPX_WIDTH-1:0]sctag2_cpx_data_buf_ca;// From buf_sctag2_cpx_data of cpx_databuf_ca.v
   output [`CPX_WIDTH-1:0]sctag3_cpx_data_buf_ca;// From buf_sctag3_cpx_data of cpx_databuf_ca.v
   // End of automatics

   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input [5:0]		arbcp0_cpxdp_grant_arbbf_ca;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp0_cpxdp_q0_hold_arbbf_ca_l;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp0_cpxdp_qsel0_arbbf_ca;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp0_cpxdp_qsel1_arbbf_ca_l;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp0_cpxdp_shift_arbbf_cx;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp1_cpxdp_grant_arbbf_ca;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp1_cpxdp_q0_hold_arbbf_ca_l;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp1_cpxdp_qsel0_arbbf_ca;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp1_cpxdp_qsel1_arbbf_ca_l;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp1_cpxdp_shift_arbbf_cx;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp2_cpxdp_grant_arbbf_ca;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp2_cpxdp_q0_hold_arbbf_ca_l;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp2_cpxdp_qsel0_arbbf_ca;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp2_cpxdp_qsel1_arbbf_ca_l;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp2_cpxdp_shift_arbbf_cx;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp3_cpxdp_grant_arbbf_ca;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp3_cpxdp_q0_hold_arbbf_ca_l;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp3_cpxdp_qsel0_arbbf_ca;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp3_cpxdp_qsel1_arbbf_ca_l;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp3_cpxdp_shift_arbbf_cx;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp4_cpxdp_grant_arbbf_ca;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp4_cpxdp_q0_hold_arbbf_ca_l;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp4_cpxdp_qsel0_arbbf_ca;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp4_cpxdp_qsel1_arbbf_ca_l;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp4_cpxdp_shift_arbbf_cx;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp5_cpxdp_grant_arbbf_ca;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp5_cpxdp_q0_hold_arbbf_ca_l;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp5_cpxdp_qsel0_arbbf_ca;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp5_cpxdp_qsel1_arbbf_ca_l;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp5_cpxdp_shift_arbbf_cx;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp6_cpxdp_grant_arbbf_ca;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp6_cpxdp_q0_hold_arbbf_ca_l;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp6_cpxdp_qsel0_arbbf_ca;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp6_cpxdp_qsel1_arbbf_ca_l;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp6_cpxdp_shift_arbbf_cx;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp7_cpxdp_grant_arbbf_ca;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp7_cpxdp_q0_hold_arbbf_ca_l;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp7_cpxdp_qsel0_arbbf_ca;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp7_cpxdp_qsel1_arbbf_ca_l;// To p1 of cpx_buf_p1.v, ...
   input [5:0]		arbcp7_cpxdp_shift_arbbf_cx;// To p1 of cpx_buf_p1.v, ...
   input [7:0]		cpx_io_grant_ca;	// To buf1_io of cpx_buf_io.v
   input [7:0]		cpx_scache0_grant_ca;	// To p1 of cpx_buf_p1.v
   input [7:0]		cpx_scache1_grant_ca;	// To pm1 of cpx_buf_pm.v
   input [7:0]		cpx_scache2_grant_ca;	// To pm2 of cpx_buf_pm.v
   input [7:0]		cpx_scache3_grant_ca;	// To p3 of cpx_buf_p3.v
   input [`CPX_WIDTH-1:0]cpx_spc0_data_cx_l;	// To ff0 of cpx_datacx2_ff.v
   input		cpx_spc0_data_rdy_cx;	// To p1 of cpx_buf_p1.v
   input [`CPX_WIDTH-1:0]cpx_spc1_data_cx_l;	// To ff1 of cpx_datacx2_ff.v
   input		cpx_spc1_data_rdy_cx;	// To p1 of cpx_buf_p1.v
   input [`CPX_WIDTH-1:0]cpx_spc2_data_cx_l;	// To ff2 of cpx_datacx2_ff.v
   input		cpx_spc2_data_rdy_cx;	// To p1 of cpx_buf_p1.v
   input [`CPX_WIDTH-1:0]cpx_spc3_data_cx_l;	// To ff3 of cpx_datacx2_ff.v
   input		cpx_spc3_data_rdy_cx;	// To ff3 of cpx_datacx2_ff.v
   input [`CPX_WIDTH-1:0]cpx_spc4_data_cx_l;	// To ff4 of cpx_datacx2_ff.v
   input		cpx_spc4_data_rdy_cx;	// To ff4 of cpx_datacx2_ff.v
   input [`CPX_WIDTH-1:0]cpx_spc5_data_cx_l;	// To ff5 of cpx_datacx2_ff.v
   input		cpx_spc5_data_rdy_cx;	// To p3 of cpx_buf_p3.v
   input [`CPX_WIDTH-1:0]cpx_spc6_data_cx_l;	// To ff6 of cpx_datacx2_ff.v
   input		cpx_spc6_data_rdy_cx;	// To p3 of cpx_buf_p3.v
   input [`CPX_WIDTH-1:0]cpx_spc7_data_cx_l;	// To ff7 of cpx_datacx2_ff.v
   input		cpx_spc7_data_rdy_cx;	// To p3 of cpx_buf_p3.v
   input [`CPX_WIDTH-1:0]fp_cpx_data_ca;	// To buf2_fp_cpx_data of cpx_databuf_ca2.v
   input [7:0]		fp_cpx_req_cq;		// To fp of cpx_buf_pt.v
   input [`CPX_WIDTH-1:0]io_cpx_data_ca;	// To ff_io of io_cpx_reqdata_ff.v
   input [7:0]		io_cpx_req_cq;		// To ff_io of io_cpx_reqdata_ff.v
   input		pcx_scache2_dat_px2_so_1;// To pt2 of cpx_buf_pt.v
   input		rclk;			// To pt0 of cpx_buf_pt.v, ...
   input		scache0_cpx_atom_cq;	// To pt0 of cpx_buf_pt.v
   input [7:0]		scache0_cpx_req_cq;	// To pt0 of cpx_buf_pt.v
   input		scache1_cpx_atom_cq;	// To pt1 of cpx_buf_pt.v
   input [7:0]		scache1_cpx_req_cq;	// To pt1 of cpx_buf_pt.v
   input		scache2_cpx_atom_cq;	// To pt2 of cpx_buf_pt.v
   input [7:0]		scache2_cpx_req_cq;	// To pt2 of cpx_buf_pt.v
   input		scache3_cpx_atom_cq;	// To pt3 of cpx_buf_pt.v
   input [7:0]		scache3_cpx_req_cq;	// To pt3 of cpx_buf_pt.v
   input [`CPX_WIDTH-1:0]sctag0_cpx_data_ca;	// To buf_sctag0_cpx_data of cpx_databuf_ca.v
   input [`CPX_WIDTH-1:0]sctag1_cpx_data_ca;	// To buf_sctag1_cpx_data of cpx_databuf_ca.v
   input [`CPX_WIDTH-1:0]sctag2_cpx_data_ca;	// To buf_sctag2_cpx_data of cpx_databuf_ca.v
   input [`CPX_WIDTH-1:0]sctag3_cpx_data_ca;	// To buf_sctag3_cpx_data of cpx_databuf_ca.v
   input		se_buf0_middle;		// To fp of cpx_buf_pt.v
   input		se_buf2_bottom;		// To pt3 of cpx_buf_pt.v, ...
   input		se_buf2_top;		// To pt2 of cpx_buf_pt.v, ...
   input		se_buf3_top;		// To io of cpx_buf_pt.v, ...
   input		se_buf4_bottom;		// To pt1 of cpx_buf_pt.v, ...
   input		se_buf4_top;		// To pt0 of cpx_buf_pt.v, ...
   input		si_1;			// To ff7 of cpx_datacx2_ff.v
   // End of automatics

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [3:0]		arbcp0_cpxdp_grant_bufp1_ca_l;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp0_cpxdp_grant_bufp3_ca_l;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp0_cpxdp_q0_hold_bufp1_ca;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp0_cpxdp_q0_hold_bufp3_ca;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp0_cpxdp_qsel0_bufp1_ca_l;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp0_cpxdp_qsel0_bufp3_ca_l;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp0_cpxdp_qsel1_bufp1_ca;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp0_cpxdp_qsel1_bufp3_ca;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp0_cpxdp_shift_bufp1_cx_l;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp0_cpxdp_shift_bufp3_cx_l;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp1_cpxdp_grant_bufp1_ca_l;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp1_cpxdp_grant_bufp3_ca_l;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp1_cpxdp_q0_hold_bufp1_ca;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp1_cpxdp_q0_hold_bufp3_ca;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp1_cpxdp_qsel0_bufp1_ca_l;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp1_cpxdp_qsel0_bufp3_ca_l;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp1_cpxdp_qsel1_bufp1_ca;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp1_cpxdp_qsel1_bufp3_ca;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp1_cpxdp_shift_bufp1_cx_l;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp1_cpxdp_shift_bufp3_cx_l;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp2_cpxdp_grant_bufp1_ca_l;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp2_cpxdp_grant_bufp3_ca_l;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp2_cpxdp_q0_hold_bufp1_ca;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp2_cpxdp_q0_hold_bufp3_ca;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp2_cpxdp_qsel0_bufp1_ca_l;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp2_cpxdp_qsel0_bufp3_ca_l;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp2_cpxdp_qsel1_bufp1_ca;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp2_cpxdp_qsel1_bufp3_ca;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp2_cpxdp_shift_bufp1_cx_l;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp2_cpxdp_shift_bufp3_cx_l;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp3_cpxdp_grant_bufp1_ca_l;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp3_cpxdp_grant_bufp3_ca_l;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp3_cpxdp_q0_hold_bufp1_ca;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp3_cpxdp_q0_hold_bufp3_ca;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp3_cpxdp_qsel0_bufp1_ca_l;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp3_cpxdp_qsel0_bufp3_ca_l;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp3_cpxdp_qsel1_bufp1_ca;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp3_cpxdp_qsel1_bufp3_ca;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp3_cpxdp_shift_bufp1_cx_l;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp3_cpxdp_shift_bufp3_cx_l;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp4_cpxdp_grant_bufp1_ca_l;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp4_cpxdp_grant_bufp3_ca_l;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp4_cpxdp_q0_hold_bufp1_ca;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp4_cpxdp_q0_hold_bufp3_ca;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp4_cpxdp_qsel0_bufp1_ca_l;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp4_cpxdp_qsel0_bufp3_ca_l;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp4_cpxdp_qsel1_bufp1_ca;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp4_cpxdp_qsel1_bufp3_ca;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp4_cpxdp_shift_bufp1_cx_l;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp4_cpxdp_shift_bufp3_cx_l;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp5_cpxdp_grant_bufp1_ca_l;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp5_cpxdp_grant_bufp3_ca_l;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp5_cpxdp_q0_hold_bufp1_ca;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp5_cpxdp_q0_hold_bufp3_ca;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp5_cpxdp_qsel0_bufp1_ca_l;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp5_cpxdp_qsel0_bufp3_ca_l;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp5_cpxdp_qsel1_bufp1_ca;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp5_cpxdp_qsel1_bufp3_ca;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp5_cpxdp_shift_bufp1_cx_l;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp5_cpxdp_shift_bufp3_cx_l;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp6_cpxdp_grant_bufp1_ca_l;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp6_cpxdp_grant_bufp3_ca_l;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp6_cpxdp_q0_hold_bufp1_ca;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp6_cpxdp_q0_hold_bufp3_ca;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp6_cpxdp_qsel0_bufp1_ca_l;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp6_cpxdp_qsel0_bufp3_ca_l;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp6_cpxdp_qsel1_bufp1_ca;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp6_cpxdp_qsel1_bufp3_ca;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp6_cpxdp_shift_bufp1_cx_l;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp6_cpxdp_shift_bufp3_cx_l;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp7_cpxdp_grant_bufp1_ca_l;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp7_cpxdp_grant_bufp3_ca_l;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp7_cpxdp_q0_hold_bufp1_ca;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp7_cpxdp_q0_hold_bufp3_ca;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp7_cpxdp_qsel0_bufp1_ca_l;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp7_cpxdp_qsel0_bufp3_ca_l;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp7_cpxdp_qsel1_bufp1_ca;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp7_cpxdp_qsel1_bufp3_ca;// From p3 of cpx_buf_p3.v, ...
   wire [3:0]		arbcp7_cpxdp_shift_bufp1_cx_l;// From p1 of cpx_buf_p1.v, ...
   wire [5:2]		arbcp7_cpxdp_shift_bufp3_cx_l;// From p3 of cpx_buf_p3.v, ...
   wire [7:0]		cpx_io_grant_buf1_io_ca;// From buf1_io of cpx_buf_io.v
   wire [7:0]		cpx_io_grant_cx;	// From io of cpx_buf_pt.v
   wire [7:0]		cpx_scache0_grant_bufp0_ca;// From p0 of cpx_buf_p0.v
   wire [7:0]		cpx_scache0_grant_bufp1_ca_l;// From p1 of cpx_buf_p1.v
   wire [7:0]		cpx_scache1_grant_bufpm_ca;// From pm1 of cpx_buf_pm.v
   wire [7:0]		cpx_scache2_grant_bufpm_ca;// From pm2 of cpx_buf_pm.v
   wire [7:0]		cpx_scache3_grant_bufp3_ca_l;// From p3 of cpx_buf_p3.v
   wire [7:0]		cpx_scache3_grant_bufp4_ca;// From p4 of cpx_buf_p4.v
   wire			cpx_spc0_data_rdy_bufp0_cx;// From p0 of cpx_buf_p0.v
   wire			cpx_spc0_data_rdy_bufp1_cx;// From p1 of cpx_buf_p1.v
   wire			cpx_spc1_data_rdy_bufp1_cx;// From p1 of cpx_buf_p1.v
   wire			cpx_spc2_data_rdy_bufp1_cx;// From p1 of cpx_buf_p1.v
   wire			cpx_spc5_data_rdy_bufp3_cx;// From p3 of cpx_buf_p3.v
   wire			cpx_spc6_data_rdy_bufp3_cx;// From p3 of cpx_buf_p3.v
   wire			cpx_spc7_data_rdy_bufp3_cx;// From p3 of cpx_buf_p3.v
   wire			cpx_spc7_data_rdy_bufp4_cx;// From p4 of cpx_buf_p4.v
   wire			ff0_so_1;		// From ff0 of cpx_datacx2_ff.v
   wire			ff1_so_1;		// From ff1 of cpx_datacx2_ff.v
   wire			ff2_so_1;		// From ff2 of cpx_datacx2_ff.v
   wire			ff3_so_1;		// From ff3 of cpx_datacx2_ff.v
   wire			ff4_so_1;		// From ff4 of cpx_datacx2_ff.v
   wire			ff5_so_1;		// From ff5 of cpx_datacx2_ff.v
   wire			ff6_so_1;		// From ff6 of cpx_datacx2_ff.v
   wire			ff7_so_1;		// From ff7 of cpx_datacx2_ff.v
   wire			ff_io_grant_so_1;	// From ff_io_grant of cpx_io_grant_ff.v
   wire [`CPX_WIDTH-1:0]fp_cpx_data_buf1_ca;	// From buf2_fp_cpx_data of cpx_databuf_ca2.v
   wire [7:0]		fp_cpx_req_bufp0_cq;	// From fpbuf_p0 of cpx_fpbuf_p0.v
   wire [7:0]		fp_cpx_req_bufpt_cq_l;	// From fp of cpx_buf_pt.v
   wire			fp_so_1;		// From fp of cpx_buf_pt.v
   wire [`CPX_WIDTH-1:0]io_cpx_data_ca2;	// From ff_io of io_cpx_reqdata_ff.v
   wire [7:0]		io_cpx_req_bufp4_cq;	// From p4 of cpx_buf_p4.v
   wire [7:0]		io_cpx_req_bufpt_cq_l;	// From io of cpx_buf_pt.v
   wire [7:0]		io_cpx_req_cq2;		// From ff_io of io_cpx_reqdata_ff.v
   wire			io_cpx_reqdata_ff_so_1;	// From ff_io of io_cpx_reqdata_ff.v
   wire			io_so_1;		// From io of cpx_buf_pt.v
   wire			pt2_so_1;		// From pt2 of cpx_buf_pt.v
   wire			pt3_so_1;		// From pt3 of cpx_buf_pt.v
   wire			scache0_cpx_atom_bufp0_cq;// From p0 of cpx_buf_p0.v
   wire			scache0_cpx_atom_bufpt_cq_l;// From pt0 of cpx_buf_pt.v
   wire [7:0]		scache0_cpx_req_bufp0_cq;// From p0 of cpx_buf_p0.v
   wire [7:0]		scache0_cpx_req_bufpt_cq_l;// From pt0 of cpx_buf_pt.v
   wire			scache1_cpx_atom_bufpt_cq_l;// From pt1 of cpx_buf_pt.v
   wire [7:0]		scache1_cpx_req_bufpt_cq_l;// From pt1 of cpx_buf_pt.v
   wire			scache2_cpx_atom_bufpt_cq_l;// From pt2 of cpx_buf_pt.v
   wire [7:0]		scache2_cpx_req_bufpt_cq_l;// From pt2 of cpx_buf_pt.v
   wire			scache3_cpx_atom_bufp4_cq;// From p4 of cpx_buf_p4.v
   wire			scache3_cpx_atom_bufpt_cq_l;// From pt3 of cpx_buf_pt.v
   wire [7:0]		scache3_cpx_req_bufp4_cq;// From p4 of cpx_buf_p4.v
   wire [7:0]		scache3_cpx_req_bufpt_cq_l;// From pt3 of cpx_buf_pt.v
   // End of automatics




   /* cpx_buf_pm AUTO_TEMPLATE(
		  // Outputs
		  .cpx_scache_grant_bufpm_ca(cpx_scache@_grant_bufpm_ca[7:0]),
		  .scache_cpx_req_bufpm_cq(scache@_cpx_req_bufpm_cq[7:0]),
                  .scache_cpx_atom_bufpm_cq(scache@_cpx_atom_bufpm_cq),
		  // Inputs
		  .cpx_scache_grant_ca	(cpx_scache@_grant_ca[7:0]),
		  .scache_cpx_req_bufpt_cq_l(scache@_cpx_req_bufpt_cq_l[7:0]),
		  .scache_cpx_atom_bufpt_cq_l(scache@_cpx_atom_bufpt_cq_l));
  */

  cpx_buf_pm pm1(/*AUTOINST*/
		 // Outputs
		 .cpx_scache_grant_bufpm_ca(cpx_scache1_grant_bufpm_ca[7:0]), // Templated
		 .scache_cpx_req_bufpm_cq(scache1_cpx_req_bufpm_cq[7:0]), // Templated
		 .scache_cpx_atom_bufpm_cq(scache1_cpx_atom_bufpm_cq), // Templated
		 // Inputs
		 .cpx_scache_grant_ca	(cpx_scache1_grant_ca[7:0]), // Templated
		 .scache_cpx_req_bufpt_cq_l(scache1_cpx_req_bufpt_cq_l[7:0]), // Templated
		 .scache_cpx_atom_bufpt_cq_l(scache1_cpx_atom_bufpt_cq_l)); // Templated
  cpx_buf_pm pm2(/*AUTOINST*/
		 // Outputs
		 .cpx_scache_grant_bufpm_ca(cpx_scache2_grant_bufpm_ca[7:0]), // Templated
		 .scache_cpx_req_bufpm_cq(scache2_cpx_req_bufpm_cq[7:0]), // Templated
		 .scache_cpx_atom_bufpm_cq(scache2_cpx_atom_bufpm_cq), // Templated
		 // Inputs
		 .cpx_scache_grant_ca	(cpx_scache2_grant_ca[7:0]), // Templated
		 .scache_cpx_req_bufpt_cq_l(scache2_cpx_req_bufpt_cq_l[7:0]), // Templated
		 .scache_cpx_atom_bufpt_cq_l(scache2_cpx_atom_bufpt_cq_l)); // Templated
   /* cpx_buf_pm_even AUTO_TEMPLATE(
		  // Outputs
		  .arbcp0_cpxdp_grant_ca(arbcp0_cpxdp_grant_ca[@]),
		  .arbcp0_cpxdp_q0_hold_ca_l(arbcp0_cpxdp_q0_hold_ca_l[@]),
		  .arbcp0_cpxdp_qsel0_ca(arbcp0_cpxdp_qsel0_ca[@]),
		  .arbcp0_cpxdp_qsel1_ca_l(arbcp0_cpxdp_qsel1_ca_l[@]),
		  .arbcp0_cpxdp_shift_cx(arbcp0_cpxdp_shift_cx[@]),
		  .arbcp2_cpxdp_grant_ca(arbcp2_cpxdp_grant_ca[@]),
		  .arbcp2_cpxdp_q0_hold_ca_l(arbcp2_cpxdp_q0_hold_ca_l[@]),
		  .arbcp2_cpxdp_qsel0_ca(arbcp2_cpxdp_qsel0_ca[@]),
		  .arbcp2_cpxdp_qsel1_ca_l(arbcp2_cpxdp_qsel1_ca_l[@]),
		  .arbcp2_cpxdp_shift_cx(arbcp2_cpxdp_shift_cx[@]),
		  .arbcp4_cpxdp_grant_ca(arbcp4_cpxdp_grant_ca[@]),
		  .arbcp4_cpxdp_q0_hold_ca_l(arbcp4_cpxdp_q0_hold_ca_l[@]),
		  .arbcp4_cpxdp_qsel0_ca(arbcp4_cpxdp_qsel0_ca[@]),
		  .arbcp4_cpxdp_qsel1_ca_l(arbcp4_cpxdp_qsel1_ca_l[@]),
		  .arbcp4_cpxdp_shift_cx(arbcp4_cpxdp_shift_cx[@]),
		  .arbcp6_cpxdp_grant_ca(arbcp6_cpxdp_grant_ca[@]),
		  .arbcp6_cpxdp_q0_hold_ca_l(arbcp6_cpxdp_q0_hold_ca_l[@]),
		  .arbcp6_cpxdp_qsel0_ca(arbcp6_cpxdp_qsel0_ca[@]),
		  .arbcp6_cpxdp_qsel1_ca_l(arbcp6_cpxdp_qsel1_ca_l[@]),
		  .arbcp6_cpxdp_shift_cx(arbcp6_cpxdp_shift_cx[@]),
		  // Inputs
		  .arbcp0_cpxdp_grant_arbbf_ca_l(arbcp0_cpxdp_grant_bufp1_ca_l[@]),
		  .arbcp0_cpxdp_q0_hold_arbbf_ca(arbcp0_cpxdp_q0_hold_bufp1_ca[@]),
		  .arbcp0_cpxdp_qsel0_arbbf_ca_l(arbcp0_cpxdp_qsel0_bufp1_ca_l[@]),
		  .arbcp0_cpxdp_qsel1_arbbf_ca(arbcp0_cpxdp_qsel1_bufp1_ca[@]),
		  .arbcp0_cpxdp_shift_arbbf_cx_l(arbcp0_cpxdp_shift_bufp1_cx_l[@]),
		  .arbcp2_cpxdp_grant_arbbf_ca_l(arbcp2_cpxdp_grant_bufp1_ca_l[@]),
		  .arbcp2_cpxdp_q0_hold_arbbf_ca(arbcp2_cpxdp_q0_hold_bufp1_ca[@]),
		  .arbcp2_cpxdp_qsel0_arbbf_ca_l(arbcp2_cpxdp_qsel0_bufp1_ca_l[@]),
		  .arbcp2_cpxdp_qsel1_arbbf_ca(arbcp2_cpxdp_qsel1_bufp1_ca[@]),
		  .arbcp2_cpxdp_shift_arbbf_cx_l(arbcp2_cpxdp_shift_bufp1_cx_l[@]),
		  .arbcp4_cpxdp_grant_arbbf_ca_l(arbcp4_cpxdp_grant_bufp1_ca_l[@]),
		  .arbcp4_cpxdp_q0_hold_arbbf_ca(arbcp4_cpxdp_q0_hold_bufp1_ca[@]),
		  .arbcp4_cpxdp_qsel0_arbbf_ca_l(arbcp4_cpxdp_qsel0_bufp1_ca_l[@]),
		  .arbcp4_cpxdp_qsel1_arbbf_ca(arbcp4_cpxdp_qsel1_bufp1_ca[@]),
		  .arbcp4_cpxdp_shift_arbbf_cx_l(arbcp4_cpxdp_shift_bufp1_cx_l[@]),
		  .arbcp6_cpxdp_grant_arbbf_ca_l(arbcp6_cpxdp_grant_bufp1_ca_l[@]),
		  .arbcp6_cpxdp_q0_hold_arbbf_ca(arbcp6_cpxdp_q0_hold_bufp1_ca[@]),
		  .arbcp6_cpxdp_qsel0_arbbf_ca_l(arbcp6_cpxdp_qsel0_bufp1_ca_l[@]),
		  .arbcp6_cpxdp_qsel1_arbbf_ca(arbcp6_cpxdp_qsel1_bufp1_ca[@]),
		  .arbcp6_cpxdp_shift_arbbf_cx_l(arbcp6_cpxdp_shift_bufp1_cx_l[@]));
   */

   cpx_buf_pm_even pm1_even(/*AUTOINST*/
			    // Outputs
			    .arbcp0_cpxdp_grant_ca(arbcp0_cpxdp_grant_ca[1]), // Templated
			    .arbcp0_cpxdp_q0_hold_ca_l(arbcp0_cpxdp_q0_hold_ca_l[1]), // Templated
			    .arbcp0_cpxdp_qsel0_ca(arbcp0_cpxdp_qsel0_ca[1]), // Templated
			    .arbcp0_cpxdp_qsel1_ca_l(arbcp0_cpxdp_qsel1_ca_l[1]), // Templated
			    .arbcp0_cpxdp_shift_cx(arbcp0_cpxdp_shift_cx[1]), // Templated
			    .arbcp2_cpxdp_grant_ca(arbcp2_cpxdp_grant_ca[1]), // Templated
			    .arbcp2_cpxdp_q0_hold_ca_l(arbcp2_cpxdp_q0_hold_ca_l[1]), // Templated
			    .arbcp2_cpxdp_qsel0_ca(arbcp2_cpxdp_qsel0_ca[1]), // Templated
			    .arbcp2_cpxdp_qsel1_ca_l(arbcp2_cpxdp_qsel1_ca_l[1]), // Templated
			    .arbcp2_cpxdp_shift_cx(arbcp2_cpxdp_shift_cx[1]), // Templated
			    .arbcp4_cpxdp_grant_ca(arbcp4_cpxdp_grant_ca[1]), // Templated
			    .arbcp4_cpxdp_q0_hold_ca_l(arbcp4_cpxdp_q0_hold_ca_l[1]), // Templated
			    .arbcp4_cpxdp_qsel0_ca(arbcp4_cpxdp_qsel0_ca[1]), // Templated
			    .arbcp4_cpxdp_qsel1_ca_l(arbcp4_cpxdp_qsel1_ca_l[1]), // Templated
			    .arbcp4_cpxdp_shift_cx(arbcp4_cpxdp_shift_cx[1]), // Templated
			    .arbcp6_cpxdp_grant_ca(arbcp6_cpxdp_grant_ca[1]), // Templated
			    .arbcp6_cpxdp_q0_hold_ca_l(arbcp6_cpxdp_q0_hold_ca_l[1]), // Templated
			    .arbcp6_cpxdp_qsel0_ca(arbcp6_cpxdp_qsel0_ca[1]), // Templated
			    .arbcp6_cpxdp_qsel1_ca_l(arbcp6_cpxdp_qsel1_ca_l[1]), // Templated
			    .arbcp6_cpxdp_shift_cx(arbcp6_cpxdp_shift_cx[1]), // Templated
			    // Inputs
			    .arbcp0_cpxdp_grant_arbbf_ca_l(arbcp0_cpxdp_grant_bufp1_ca_l[1]), // Templated
			    .arbcp0_cpxdp_q0_hold_arbbf_ca(arbcp0_cpxdp_q0_hold_bufp1_ca[1]), // Templated
			    .arbcp0_cpxdp_qsel0_arbbf_ca_l(arbcp0_cpxdp_qsel0_bufp1_ca_l[1]), // Templated
			    .arbcp0_cpxdp_qsel1_arbbf_ca(arbcp0_cpxdp_qsel1_bufp1_ca[1]), // Templated
			    .arbcp0_cpxdp_shift_arbbf_cx_l(arbcp0_cpxdp_shift_bufp1_cx_l[1]), // Templated
			    .arbcp2_cpxdp_grant_arbbf_ca_l(arbcp2_cpxdp_grant_bufp1_ca_l[1]), // Templated
			    .arbcp2_cpxdp_q0_hold_arbbf_ca(arbcp2_cpxdp_q0_hold_bufp1_ca[1]), // Templated
			    .arbcp2_cpxdp_qsel0_arbbf_ca_l(arbcp2_cpxdp_qsel0_bufp1_ca_l[1]), // Templated
			    .arbcp2_cpxdp_qsel1_arbbf_ca(arbcp2_cpxdp_qsel1_bufp1_ca[1]), // Templated
			    .arbcp2_cpxdp_shift_arbbf_cx_l(arbcp2_cpxdp_shift_bufp1_cx_l[1]), // Templated
			    .arbcp4_cpxdp_grant_arbbf_ca_l(arbcp4_cpxdp_grant_bufp1_ca_l[1]), // Templated
			    .arbcp4_cpxdp_q0_hold_arbbf_ca(arbcp4_cpxdp_q0_hold_bufp1_ca[1]), // Templated
			    .arbcp4_cpxdp_qsel0_arbbf_ca_l(arbcp4_cpxdp_qsel0_bufp1_ca_l[1]), // Templated
			    .arbcp4_cpxdp_qsel1_arbbf_ca(arbcp4_cpxdp_qsel1_bufp1_ca[1]), // Templated
			    .arbcp4_cpxdp_shift_arbbf_cx_l(arbcp4_cpxdp_shift_bufp1_cx_l[1]), // Templated
			    .arbcp6_cpxdp_grant_arbbf_ca_l(arbcp6_cpxdp_grant_bufp1_ca_l[1]), // Templated
			    .arbcp6_cpxdp_q0_hold_arbbf_ca(arbcp6_cpxdp_q0_hold_bufp1_ca[1]), // Templated
			    .arbcp6_cpxdp_qsel0_arbbf_ca_l(arbcp6_cpxdp_qsel0_bufp1_ca_l[1]), // Templated
			    .arbcp6_cpxdp_qsel1_arbbf_ca(arbcp6_cpxdp_qsel1_bufp1_ca[1]), // Templated
			    .arbcp6_cpxdp_shift_arbbf_cx_l(arbcp6_cpxdp_shift_bufp1_cx_l[1])); // Templated
   /* cpx_buf_pm_even AUTO_TEMPLATE(
                  // Outputs
                  .arbcp0_cpxdp_grant_ca(arbcp0_cpxdp_grant_ca[@]),
                  .arbcp0_cpxdp_q0_hold_ca_l(arbcp0_cpxdp_q0_hold_ca_l[@]),
                  .arbcp0_cpxdp_qsel0_ca(arbcp0_cpxdp_qsel0_ca[@]),
                  .arbcp0_cpxdp_qsel1_ca_l(arbcp0_cpxdp_qsel1_ca_l[@]),
                  .arbcp0_cpxdp_shift_cx(arbcp0_cpxdp_shift_cx[@]),
                  .arbcp2_cpxdp_grant_ca(arbcp2_cpxdp_grant_ca[@]),
                  .arbcp2_cpxdp_q0_hold_ca_l(arbcp2_cpxdp_q0_hold_ca_l[@]),
                  .arbcp2_cpxdp_qsel0_ca(arbcp2_cpxdp_qsel0_ca[@]),
                  .arbcp2_cpxdp_qsel1_ca_l(arbcp2_cpxdp_qsel1_ca_l[@]),
                  .arbcp2_cpxdp_shift_cx(arbcp2_cpxdp_shift_cx[@]),
                  .arbcp4_cpxdp_grant_ca(arbcp4_cpxdp_grant_ca[@]),
                  .arbcp4_cpxdp_q0_hold_ca_l(arbcp4_cpxdp_q0_hold_ca_l[@]),
                  .arbcp4_cpxdp_qsel0_ca(arbcp4_cpxdp_qsel0_ca[@]),
                  .arbcp4_cpxdp_qsel1_ca_l(arbcp4_cpxdp_qsel1_ca_l[@]),
                  .arbcp4_cpxdp_shift_cx(arbcp4_cpxdp_shift_cx[@]),
                  .arbcp6_cpxdp_grant_ca(arbcp6_cpxdp_grant_ca[@]),
                  .arbcp6_cpxdp_q0_hold_ca_l(arbcp6_cpxdp_q0_hold_ca_l[@]),
                  .arbcp6_cpxdp_qsel0_ca(arbcp6_cpxdp_qsel0_ca[@]),
                  .arbcp6_cpxdp_qsel1_ca_l(arbcp6_cpxdp_qsel1_ca_l[@]),
                  .arbcp6_cpxdp_shift_cx(arbcp6_cpxdp_shift_cx[@]),
                  // Inputs
                  .arbcp0_cpxdp_grant_arbbf_ca_l(arbcp0_cpxdp_grant_bufp3_ca_l[@]),
                  .arbcp0_cpxdp_q0_hold_arbbf_ca(arbcp0_cpxdp_q0_hold_bufp3_ca[@]),
                  .arbcp0_cpxdp_qsel0_arbbf_ca_l(arbcp0_cpxdp_qsel0_bufp3_ca_l[@]),
                  .arbcp0_cpxdp_qsel1_arbbf_ca(arbcp0_cpxdp_qsel1_bufp3_ca[@]),
                  .arbcp0_cpxdp_shift_arbbf_cx_l(arbcp0_cpxdp_shift_bufp3_cx_l[@]),
                  .arbcp2_cpxdp_grant_arbbf_ca_l(arbcp2_cpxdp_grant_bufp3_ca_l[@]),
                  .arbcp2_cpxdp_q0_hold_arbbf_ca(arbcp2_cpxdp_q0_hold_bufp3_ca[@]),
                  .arbcp2_cpxdp_qsel0_arbbf_ca_l(arbcp2_cpxdp_qsel0_bufp3_ca_l[@]),
                  .arbcp2_cpxdp_qsel1_arbbf_ca(arbcp2_cpxdp_qsel1_bufp3_ca[@]),
                  .arbcp2_cpxdp_shift_arbbf_cx_l(arbcp2_cpxdp_shift_bufp3_cx_l[@]),
                  .arbcp4_cpxdp_grant_arbbf_ca_l(arbcp4_cpxdp_grant_bufp3_ca_l[@]),
                  .arbcp4_cpxdp_q0_hold_arbbf_ca(arbcp4_cpxdp_q0_hold_bufp3_ca[@]),
                  .arbcp4_cpxdp_qsel0_arbbf_ca_l(arbcp4_cpxdp_qsel0_bufp3_ca_l[@]),
                  .arbcp4_cpxdp_qsel1_arbbf_ca(arbcp4_cpxdp_qsel1_bufp3_ca[@]),
                  .arbcp4_cpxdp_shift_arbbf_cx_l(arbcp4_cpxdp_shift_bufp3_cx_l[@]),
                  .arbcp6_cpxdp_grant_arbbf_ca_l(arbcp6_cpxdp_grant_bufp3_ca_l[@]),
                  .arbcp6_cpxdp_q0_hold_arbbf_ca(arbcp6_cpxdp_q0_hold_bufp3_ca[@]),
                  .arbcp6_cpxdp_qsel0_arbbf_ca_l(arbcp6_cpxdp_qsel0_bufp3_ca_l[@]),
                  .arbcp6_cpxdp_qsel1_arbbf_ca(arbcp6_cpxdp_qsel1_bufp3_ca[@]),
                  .arbcp6_cpxdp_shift_arbbf_cx_l(arbcp6_cpxdp_shift_bufp3_cx_l[@]));
   */


   cpx_buf_pm_even pm2_even(/*AUTOINST*/
			    // Outputs
			    .arbcp0_cpxdp_grant_ca(arbcp0_cpxdp_grant_ca[2]), // Templated
			    .arbcp0_cpxdp_q0_hold_ca_l(arbcp0_cpxdp_q0_hold_ca_l[2]), // Templated
			    .arbcp0_cpxdp_qsel0_ca(arbcp0_cpxdp_qsel0_ca[2]), // Templated
			    .arbcp0_cpxdp_qsel1_ca_l(arbcp0_cpxdp_qsel1_ca_l[2]), // Templated
			    .arbcp0_cpxdp_shift_cx(arbcp0_cpxdp_shift_cx[2]), // Templated
			    .arbcp2_cpxdp_grant_ca(arbcp2_cpxdp_grant_ca[2]), // Templated
			    .arbcp2_cpxdp_q0_hold_ca_l(arbcp2_cpxdp_q0_hold_ca_l[2]), // Templated
			    .arbcp2_cpxdp_qsel0_ca(arbcp2_cpxdp_qsel0_ca[2]), // Templated
			    .arbcp2_cpxdp_qsel1_ca_l(arbcp2_cpxdp_qsel1_ca_l[2]), // Templated
			    .arbcp2_cpxdp_shift_cx(arbcp2_cpxdp_shift_cx[2]), // Templated
			    .arbcp4_cpxdp_grant_ca(arbcp4_cpxdp_grant_ca[2]), // Templated
			    .arbcp4_cpxdp_q0_hold_ca_l(arbcp4_cpxdp_q0_hold_ca_l[2]), // Templated
			    .arbcp4_cpxdp_qsel0_ca(arbcp4_cpxdp_qsel0_ca[2]), // Templated
			    .arbcp4_cpxdp_qsel1_ca_l(arbcp4_cpxdp_qsel1_ca_l[2]), // Templated
			    .arbcp4_cpxdp_shift_cx(arbcp4_cpxdp_shift_cx[2]), // Templated
			    .arbcp6_cpxdp_grant_ca(arbcp6_cpxdp_grant_ca[2]), // Templated
			    .arbcp6_cpxdp_q0_hold_ca_l(arbcp6_cpxdp_q0_hold_ca_l[2]), // Templated
			    .arbcp6_cpxdp_qsel0_ca(arbcp6_cpxdp_qsel0_ca[2]), // Templated
			    .arbcp6_cpxdp_qsel1_ca_l(arbcp6_cpxdp_qsel1_ca_l[2]), // Templated
			    .arbcp6_cpxdp_shift_cx(arbcp6_cpxdp_shift_cx[2]), // Templated
			    // Inputs
			    .arbcp0_cpxdp_grant_arbbf_ca_l(arbcp0_cpxdp_grant_bufp3_ca_l[2]), // Templated
			    .arbcp0_cpxdp_q0_hold_arbbf_ca(arbcp0_cpxdp_q0_hold_bufp3_ca[2]), // Templated
			    .arbcp0_cpxdp_qsel0_arbbf_ca_l(arbcp0_cpxdp_qsel0_bufp3_ca_l[2]), // Templated
			    .arbcp0_cpxdp_qsel1_arbbf_ca(arbcp0_cpxdp_qsel1_bufp3_ca[2]), // Templated
			    .arbcp0_cpxdp_shift_arbbf_cx_l(arbcp0_cpxdp_shift_bufp3_cx_l[2]), // Templated
			    .arbcp2_cpxdp_grant_arbbf_ca_l(arbcp2_cpxdp_grant_bufp3_ca_l[2]), // Templated
			    .arbcp2_cpxdp_q0_hold_arbbf_ca(arbcp2_cpxdp_q0_hold_bufp3_ca[2]), // Templated
			    .arbcp2_cpxdp_qsel0_arbbf_ca_l(arbcp2_cpxdp_qsel0_bufp3_ca_l[2]), // Templated
			    .arbcp2_cpxdp_qsel1_arbbf_ca(arbcp2_cpxdp_qsel1_bufp3_ca[2]), // Templated
			    .arbcp2_cpxdp_shift_arbbf_cx_l(arbcp2_cpxdp_shift_bufp3_cx_l[2]), // Templated
			    .arbcp4_cpxdp_grant_arbbf_ca_l(arbcp4_cpxdp_grant_bufp3_ca_l[2]), // Templated
			    .arbcp4_cpxdp_q0_hold_arbbf_ca(arbcp4_cpxdp_q0_hold_bufp3_ca[2]), // Templated
			    .arbcp4_cpxdp_qsel0_arbbf_ca_l(arbcp4_cpxdp_qsel0_bufp3_ca_l[2]), // Templated
			    .arbcp4_cpxdp_qsel1_arbbf_ca(arbcp4_cpxdp_qsel1_bufp3_ca[2]), // Templated
			    .arbcp4_cpxdp_shift_arbbf_cx_l(arbcp4_cpxdp_shift_bufp3_cx_l[2]), // Templated
			    .arbcp6_cpxdp_grant_arbbf_ca_l(arbcp6_cpxdp_grant_bufp3_ca_l[2]), // Templated
			    .arbcp6_cpxdp_q0_hold_arbbf_ca(arbcp6_cpxdp_q0_hold_bufp3_ca[2]), // Templated
			    .arbcp6_cpxdp_qsel0_arbbf_ca_l(arbcp6_cpxdp_qsel0_bufp3_ca_l[2]), // Templated
			    .arbcp6_cpxdp_qsel1_arbbf_ca(arbcp6_cpxdp_qsel1_bufp3_ca[2]), // Templated
			    .arbcp6_cpxdp_shift_arbbf_cx_l(arbcp6_cpxdp_shift_bufp3_cx_l[2])); // Templated
   /* cpx_buf_pm_even AUTO_TEMPLATE(
		  // Outputs
		  .arbcp0_cpxdp_grant_ca(arbcp1_cpxdp_grant_ca[@]),
		  .arbcp0_cpxdp_q0_hold_ca_l(arbcp1_cpxdp_q0_hold_ca_l[@]),
		  .arbcp0_cpxdp_qsel0_ca(arbcp1_cpxdp_qsel0_ca[@]),
		  .arbcp0_cpxdp_qsel1_ca_l(arbcp1_cpxdp_qsel1_ca_l[@]),
		  .arbcp0_cpxdp_shift_cx(arbcp1_cpxdp_shift_cx[@]),
		  .arbcp2_cpxdp_grant_ca(arbcp3_cpxdp_grant_ca[@]),
		  .arbcp2_cpxdp_q0_hold_ca_l(arbcp3_cpxdp_q0_hold_ca_l[@]),
		  .arbcp2_cpxdp_qsel0_ca(arbcp3_cpxdp_qsel0_ca[@]),
		  .arbcp2_cpxdp_qsel1_ca_l(arbcp3_cpxdp_qsel1_ca_l[@]),
		  .arbcp2_cpxdp_shift_cx(arbcp3_cpxdp_shift_cx[@]),
		  .arbcp4_cpxdp_grant_ca(arbcp5_cpxdp_grant_ca[@]),
		  .arbcp4_cpxdp_q0_hold_ca_l(arbcp5_cpxdp_q0_hold_ca_l[@]),
		  .arbcp4_cpxdp_qsel0_ca(arbcp5_cpxdp_qsel0_ca[@]),
		  .arbcp4_cpxdp_qsel1_ca_l(arbcp5_cpxdp_qsel1_ca_l[@]),
		  .arbcp4_cpxdp_shift_cx(arbcp5_cpxdp_shift_cx[@]),
		  .arbcp6_cpxdp_grant_ca(arbcp7_cpxdp_grant_ca[@]),
		  .arbcp6_cpxdp_q0_hold_ca_l(arbcp7_cpxdp_q0_hold_ca_l[@]),
		  .arbcp6_cpxdp_qsel0_ca(arbcp7_cpxdp_qsel0_ca[@]),
		  .arbcp6_cpxdp_qsel1_ca_l(arbcp7_cpxdp_qsel1_ca_l[@]),
		  .arbcp6_cpxdp_shift_cx(arbcp7_cpxdp_shift_cx[@]),
		  // Inputs
		  .arbcp0_cpxdp_grant_arbbf_ca_l(arbcp1_cpxdp_grant_bufp1_ca_l[@]),
		  .arbcp0_cpxdp_q0_hold_arbbf_ca(arbcp1_cpxdp_q0_hold_bufp1_ca[@]),
		  .arbcp0_cpxdp_qsel0_arbbf_ca_l(arbcp1_cpxdp_qsel0_bufp1_ca_l[@]),
		  .arbcp0_cpxdp_qsel1_arbbf_ca(arbcp1_cpxdp_qsel1_bufp1_ca[@]),
		  .arbcp0_cpxdp_shift_arbbf_cx_l(arbcp1_cpxdp_shift_bufp1_cx_l[@]),
		  .arbcp2_cpxdp_grant_arbbf_ca_l(arbcp3_cpxdp_grant_bufp1_ca_l[@]),
		  .arbcp2_cpxdp_q0_hold_arbbf_ca(arbcp3_cpxdp_q0_hold_bufp1_ca[@]),
		  .arbcp2_cpxdp_qsel0_arbbf_ca_l(arbcp3_cpxdp_qsel0_bufp1_ca_l[@]),
		  .arbcp2_cpxdp_qsel1_arbbf_ca(arbcp3_cpxdp_qsel1_bufp1_ca[@]),
		  .arbcp2_cpxdp_shift_arbbf_cx_l(arbcp3_cpxdp_shift_bufp1_cx_l[@]),
		  .arbcp4_cpxdp_grant_arbbf_ca_l(arbcp5_cpxdp_grant_bufp1_ca_l[@]),
		  .arbcp4_cpxdp_q0_hold_arbbf_ca(arbcp5_cpxdp_q0_hold_bufp1_ca[@]),
		  .arbcp4_cpxdp_qsel0_arbbf_ca_l(arbcp5_cpxdp_qsel0_bufp1_ca_l[@]),
		  .arbcp4_cpxdp_qsel1_arbbf_ca(arbcp5_cpxdp_qsel1_bufp1_ca[@]),
		  .arbcp4_cpxdp_shift_arbbf_cx_l(arbcp5_cpxdp_shift_bufp1_cx_l[@]),
		  .arbcp6_cpxdp_grant_arbbf_ca_l(arbcp7_cpxdp_grant_bufp1_ca_l[@]),
		  .arbcp6_cpxdp_q0_hold_arbbf_ca(arbcp7_cpxdp_q0_hold_bufp1_ca[@]),
		  .arbcp6_cpxdp_qsel0_arbbf_ca_l(arbcp7_cpxdp_qsel0_bufp1_ca_l[@]),
		  .arbcp6_cpxdp_qsel1_arbbf_ca(arbcp7_cpxdp_qsel1_bufp1_ca[@]),
		  .arbcp6_cpxdp_shift_arbbf_cx_l(arbcp7_cpxdp_shift_bufp1_cx_l[@]));
*/

   cpx_buf_pm_even pm1_odd(/*AUTOINST*/
			   // Outputs
			   .arbcp0_cpxdp_grant_ca(arbcp1_cpxdp_grant_ca[1]), // Templated
			   .arbcp0_cpxdp_q0_hold_ca_l(arbcp1_cpxdp_q0_hold_ca_l[1]), // Templated
			   .arbcp0_cpxdp_qsel0_ca(arbcp1_cpxdp_qsel0_ca[1]), // Templated
			   .arbcp0_cpxdp_qsel1_ca_l(arbcp1_cpxdp_qsel1_ca_l[1]), // Templated
			   .arbcp0_cpxdp_shift_cx(arbcp1_cpxdp_shift_cx[1]), // Templated
			   .arbcp2_cpxdp_grant_ca(arbcp3_cpxdp_grant_ca[1]), // Templated
			   .arbcp2_cpxdp_q0_hold_ca_l(arbcp3_cpxdp_q0_hold_ca_l[1]), // Templated
			   .arbcp2_cpxdp_qsel0_ca(arbcp3_cpxdp_qsel0_ca[1]), // Templated
			   .arbcp2_cpxdp_qsel1_ca_l(arbcp3_cpxdp_qsel1_ca_l[1]), // Templated
			   .arbcp2_cpxdp_shift_cx(arbcp3_cpxdp_shift_cx[1]), // Templated
			   .arbcp4_cpxdp_grant_ca(arbcp5_cpxdp_grant_ca[1]), // Templated
			   .arbcp4_cpxdp_q0_hold_ca_l(arbcp5_cpxdp_q0_hold_ca_l[1]), // Templated
			   .arbcp4_cpxdp_qsel0_ca(arbcp5_cpxdp_qsel0_ca[1]), // Templated
			   .arbcp4_cpxdp_qsel1_ca_l(arbcp5_cpxdp_qsel1_ca_l[1]), // Templated
			   .arbcp4_cpxdp_shift_cx(arbcp5_cpxdp_shift_cx[1]), // Templated
			   .arbcp6_cpxdp_grant_ca(arbcp7_cpxdp_grant_ca[1]), // Templated
			   .arbcp6_cpxdp_q0_hold_ca_l(arbcp7_cpxdp_q0_hold_ca_l[1]), // Templated
			   .arbcp6_cpxdp_qsel0_ca(arbcp7_cpxdp_qsel0_ca[1]), // Templated
			   .arbcp6_cpxdp_qsel1_ca_l(arbcp7_cpxdp_qsel1_ca_l[1]), // Templated
			   .arbcp6_cpxdp_shift_cx(arbcp7_cpxdp_shift_cx[1]), // Templated
			   // Inputs
			   .arbcp0_cpxdp_grant_arbbf_ca_l(arbcp1_cpxdp_grant_bufp1_ca_l[1]), // Templated
			   .arbcp0_cpxdp_q0_hold_arbbf_ca(arbcp1_cpxdp_q0_hold_bufp1_ca[1]), // Templated
			   .arbcp0_cpxdp_qsel0_arbbf_ca_l(arbcp1_cpxdp_qsel0_bufp1_ca_l[1]), // Templated
			   .arbcp0_cpxdp_qsel1_arbbf_ca(arbcp1_cpxdp_qsel1_bufp1_ca[1]), // Templated
			   .arbcp0_cpxdp_shift_arbbf_cx_l(arbcp1_cpxdp_shift_bufp1_cx_l[1]), // Templated
			   .arbcp2_cpxdp_grant_arbbf_ca_l(arbcp3_cpxdp_grant_bufp1_ca_l[1]), // Templated
			   .arbcp2_cpxdp_q0_hold_arbbf_ca(arbcp3_cpxdp_q0_hold_bufp1_ca[1]), // Templated
			   .arbcp2_cpxdp_qsel0_arbbf_ca_l(arbcp3_cpxdp_qsel0_bufp1_ca_l[1]), // Templated
			   .arbcp2_cpxdp_qsel1_arbbf_ca(arbcp3_cpxdp_qsel1_bufp1_ca[1]), // Templated
			   .arbcp2_cpxdp_shift_arbbf_cx_l(arbcp3_cpxdp_shift_bufp1_cx_l[1]), // Templated
			   .arbcp4_cpxdp_grant_arbbf_ca_l(arbcp5_cpxdp_grant_bufp1_ca_l[1]), // Templated
			   .arbcp4_cpxdp_q0_hold_arbbf_ca(arbcp5_cpxdp_q0_hold_bufp1_ca[1]), // Templated
			   .arbcp4_cpxdp_qsel0_arbbf_ca_l(arbcp5_cpxdp_qsel0_bufp1_ca_l[1]), // Templated
			   .arbcp4_cpxdp_qsel1_arbbf_ca(arbcp5_cpxdp_qsel1_bufp1_ca[1]), // Templated
			   .arbcp4_cpxdp_shift_arbbf_cx_l(arbcp5_cpxdp_shift_bufp1_cx_l[1]), // Templated
			   .arbcp6_cpxdp_grant_arbbf_ca_l(arbcp7_cpxdp_grant_bufp1_ca_l[1]), // Templated
			   .arbcp6_cpxdp_q0_hold_arbbf_ca(arbcp7_cpxdp_q0_hold_bufp1_ca[1]), // Templated
			   .arbcp6_cpxdp_qsel0_arbbf_ca_l(arbcp7_cpxdp_qsel0_bufp1_ca_l[1]), // Templated
			   .arbcp6_cpxdp_qsel1_arbbf_ca(arbcp7_cpxdp_qsel1_bufp1_ca[1]), // Templated
			   .arbcp6_cpxdp_shift_arbbf_cx_l(arbcp7_cpxdp_shift_bufp1_cx_l[1])); // Templated
   /* cpx_buf_pm_even AUTO_TEMPLATE(
                  // Outputs
                  .arbcp0_cpxdp_grant_ca(arbcp1_cpxdp_grant_ca[@]),
                  .arbcp0_cpxdp_q0_hold_ca_l(arbcp1_cpxdp_q0_hold_ca_l[@]),
                  .arbcp0_cpxdp_qsel0_ca(arbcp1_cpxdp_qsel0_ca[@]),
                  .arbcp0_cpxdp_qsel1_ca_l(arbcp1_cpxdp_qsel1_ca_l[@]),
                  .arbcp0_cpxdp_shift_cx(arbcp1_cpxdp_shift_cx[@]),
                  .arbcp2_cpxdp_grant_ca(arbcp3_cpxdp_grant_ca[@]),
                  .arbcp2_cpxdp_q0_hold_ca_l(arbcp3_cpxdp_q0_hold_ca_l[@]),
                  .arbcp2_cpxdp_qsel0_ca(arbcp3_cpxdp_qsel0_ca[@]),
                  .arbcp2_cpxdp_qsel1_ca_l(arbcp3_cpxdp_qsel1_ca_l[@]),
                  .arbcp2_cpxdp_shift_cx(arbcp3_cpxdp_shift_cx[@]),
                  .arbcp4_cpxdp_grant_ca(arbcp5_cpxdp_grant_ca[@]),
                  .arbcp4_cpxdp_q0_hold_ca_l(arbcp5_cpxdp_q0_hold_ca_l[@]),
                  .arbcp4_cpxdp_qsel0_ca(arbcp5_cpxdp_qsel0_ca[@]),
                  .arbcp4_cpxdp_qsel1_ca_l(arbcp5_cpxdp_qsel1_ca_l[@]),
                  .arbcp4_cpxdp_shift_cx(arbcp5_cpxdp_shift_cx[@]),
                  .arbcp6_cpxdp_grant_ca(arbcp7_cpxdp_grant_ca[@]),
                  .arbcp6_cpxdp_q0_hold_ca_l(arbcp7_cpxdp_q0_hold_ca_l[@]),
                  .arbcp6_cpxdp_qsel0_ca(arbcp7_cpxdp_qsel0_ca[@]),
                  .arbcp6_cpxdp_qsel1_ca_l(arbcp7_cpxdp_qsel1_ca_l[@]),
                  .arbcp6_cpxdp_shift_cx(arbcp7_cpxdp_shift_cx[@]),
                  // Inputs
                  .arbcp0_cpxdp_grant_arbbf_ca_l(arbcp1_cpxdp_grant_bufp3_ca_l[@]),
                  .arbcp0_cpxdp_q0_hold_arbbf_ca(arbcp1_cpxdp_q0_hold_bufp3_ca[@]),
                  .arbcp0_cpxdp_qsel0_arbbf_ca_l(arbcp1_cpxdp_qsel0_bufp3_ca_l[@]),
                  .arbcp0_cpxdp_qsel1_arbbf_ca(arbcp1_cpxdp_qsel1_bufp3_ca[@]),
                  .arbcp0_cpxdp_shift_arbbf_cx_l(arbcp1_cpxdp_shift_bufp3_cx_l[@]),
                  .arbcp2_cpxdp_grant_arbbf_ca_l(arbcp3_cpxdp_grant_bufp3_ca_l[@]),
                  .arbcp2_cpxdp_q0_hold_arbbf_ca(arbcp3_cpxdp_q0_hold_bufp3_ca[@]),
                  .arbcp2_cpxdp_qsel0_arbbf_ca_l(arbcp3_cpxdp_qsel0_bufp3_ca_l[@]),
                  .arbcp2_cpxdp_qsel1_arbbf_ca(arbcp3_cpxdp_qsel1_bufp3_ca[@]),
                  .arbcp2_cpxdp_shift_arbbf_cx_l(arbcp3_cpxdp_shift_bufp3_cx_l[@]),
                  .arbcp4_cpxdp_grant_arbbf_ca_l(arbcp5_cpxdp_grant_bufp3_ca_l[@]),
                  .arbcp4_cpxdp_q0_hold_arbbf_ca(arbcp5_cpxdp_q0_hold_bufp3_ca[@]),
                  .arbcp4_cpxdp_qsel0_arbbf_ca_l(arbcp5_cpxdp_qsel0_bufp3_ca_l[@]),
                  .arbcp4_cpxdp_qsel1_arbbf_ca(arbcp5_cpxdp_qsel1_bufp3_ca[@]),
                  .arbcp4_cpxdp_shift_arbbf_cx_l(arbcp5_cpxdp_shift_bufp3_cx_l[@]),
                  .arbcp6_cpxdp_grant_arbbf_ca_l(arbcp7_cpxdp_grant_bufp3_ca_l[@]),
                  .arbcp6_cpxdp_q0_hold_arbbf_ca(arbcp7_cpxdp_q0_hold_bufp3_ca[@]),
                  .arbcp6_cpxdp_qsel0_arbbf_ca_l(arbcp7_cpxdp_qsel0_bufp3_ca_l[@]),
                  .arbcp6_cpxdp_qsel1_arbbf_ca(arbcp7_cpxdp_qsel1_bufp3_ca[@]),
                  .arbcp6_cpxdp_shift_arbbf_cx_l(arbcp7_cpxdp_shift_bufp3_cx_l[@]));
*/

   cpx_buf_pm_even pm2_odd(/*AUTOINST*/
			   // Outputs
			   .arbcp0_cpxdp_grant_ca(arbcp1_cpxdp_grant_ca[2]), // Templated
			   .arbcp0_cpxdp_q0_hold_ca_l(arbcp1_cpxdp_q0_hold_ca_l[2]), // Templated
			   .arbcp0_cpxdp_qsel0_ca(arbcp1_cpxdp_qsel0_ca[2]), // Templated
			   .arbcp0_cpxdp_qsel1_ca_l(arbcp1_cpxdp_qsel1_ca_l[2]), // Templated
			   .arbcp0_cpxdp_shift_cx(arbcp1_cpxdp_shift_cx[2]), // Templated
			   .arbcp2_cpxdp_grant_ca(arbcp3_cpxdp_grant_ca[2]), // Templated
			   .arbcp2_cpxdp_q0_hold_ca_l(arbcp3_cpxdp_q0_hold_ca_l[2]), // Templated
			   .arbcp2_cpxdp_qsel0_ca(arbcp3_cpxdp_qsel0_ca[2]), // Templated
			   .arbcp2_cpxdp_qsel1_ca_l(arbcp3_cpxdp_qsel1_ca_l[2]), // Templated
			   .arbcp2_cpxdp_shift_cx(arbcp3_cpxdp_shift_cx[2]), // Templated
			   .arbcp4_cpxdp_grant_ca(arbcp5_cpxdp_grant_ca[2]), // Templated
			   .arbcp4_cpxdp_q0_hold_ca_l(arbcp5_cpxdp_q0_hold_ca_l[2]), // Templated
			   .arbcp4_cpxdp_qsel0_ca(arbcp5_cpxdp_qsel0_ca[2]), // Templated
			   .arbcp4_cpxdp_qsel1_ca_l(arbcp5_cpxdp_qsel1_ca_l[2]), // Templated
			   .arbcp4_cpxdp_shift_cx(arbcp5_cpxdp_shift_cx[2]), // Templated
			   .arbcp6_cpxdp_grant_ca(arbcp7_cpxdp_grant_ca[2]), // Templated
			   .arbcp6_cpxdp_q0_hold_ca_l(arbcp7_cpxdp_q0_hold_ca_l[2]), // Templated
			   .arbcp6_cpxdp_qsel0_ca(arbcp7_cpxdp_qsel0_ca[2]), // Templated
			   .arbcp6_cpxdp_qsel1_ca_l(arbcp7_cpxdp_qsel1_ca_l[2]), // Templated
			   .arbcp6_cpxdp_shift_cx(arbcp7_cpxdp_shift_cx[2]), // Templated
			   // Inputs
			   .arbcp0_cpxdp_grant_arbbf_ca_l(arbcp1_cpxdp_grant_bufp3_ca_l[2]), // Templated
			   .arbcp0_cpxdp_q0_hold_arbbf_ca(arbcp1_cpxdp_q0_hold_bufp3_ca[2]), // Templated
			   .arbcp0_cpxdp_qsel0_arbbf_ca_l(arbcp1_cpxdp_qsel0_bufp3_ca_l[2]), // Templated
			   .arbcp0_cpxdp_qsel1_arbbf_ca(arbcp1_cpxdp_qsel1_bufp3_ca[2]), // Templated
			   .arbcp0_cpxdp_shift_arbbf_cx_l(arbcp1_cpxdp_shift_bufp3_cx_l[2]), // Templated
			   .arbcp2_cpxdp_grant_arbbf_ca_l(arbcp3_cpxdp_grant_bufp3_ca_l[2]), // Templated
			   .arbcp2_cpxdp_q0_hold_arbbf_ca(arbcp3_cpxdp_q0_hold_bufp3_ca[2]), // Templated
			   .arbcp2_cpxdp_qsel0_arbbf_ca_l(arbcp3_cpxdp_qsel0_bufp3_ca_l[2]), // Templated
			   .arbcp2_cpxdp_qsel1_arbbf_ca(arbcp3_cpxdp_qsel1_bufp3_ca[2]), // Templated
			   .arbcp2_cpxdp_shift_arbbf_cx_l(arbcp3_cpxdp_shift_bufp3_cx_l[2]), // Templated
			   .arbcp4_cpxdp_grant_arbbf_ca_l(arbcp5_cpxdp_grant_bufp3_ca_l[2]), // Templated
			   .arbcp4_cpxdp_q0_hold_arbbf_ca(arbcp5_cpxdp_q0_hold_bufp3_ca[2]), // Templated
			   .arbcp4_cpxdp_qsel0_arbbf_ca_l(arbcp5_cpxdp_qsel0_bufp3_ca_l[2]), // Templated
			   .arbcp4_cpxdp_qsel1_arbbf_ca(arbcp5_cpxdp_qsel1_bufp3_ca[2]), // Templated
			   .arbcp4_cpxdp_shift_arbbf_cx_l(arbcp5_cpxdp_shift_bufp3_cx_l[2]), // Templated
			   .arbcp6_cpxdp_grant_arbbf_ca_l(arbcp7_cpxdp_grant_bufp3_ca_l[2]), // Templated
			   .arbcp6_cpxdp_q0_hold_arbbf_ca(arbcp7_cpxdp_q0_hold_bufp3_ca[2]), // Templated
			   .arbcp6_cpxdp_qsel0_arbbf_ca_l(arbcp7_cpxdp_qsel0_bufp3_ca_l[2]), // Templated
			   .arbcp6_cpxdp_qsel1_arbbf_ca(arbcp7_cpxdp_qsel1_bufp3_ca[2]), // Templated
			   .arbcp6_cpxdp_shift_arbbf_cx_l(arbcp7_cpxdp_shift_bufp3_cx_l[2])); // Templated
/*
 cpx_buf_pt AUTO_TEMPLATE(
		  // Outputs
		  .out0_l		(scache@_cpx_req_bufpt_cq_l[7:0]),
		  .out1_l		(scache@_cpx_atom_bufpt_cq_l),
		  .cpx_src_grant_cx	(cpx_scache@_grant_cx[7:0]),
		  .so			(cpx_buf_top_pt0_so_1),
		  // Inputs
                  .se                   (se_buf4_top),
		  .in0			(scache@_cpx_req_cq[7:0]),
		  .in1			(scache@_cpx_atom_cq),
		  .cpx_src_grant_ca	(cpx_scache@_grant_bufp0_ca[7:0]),
		  .clk			(clk),
		  .si			(pt2_so_1));

 */

   cpx_buf_pt pt0(/*AUTOINST*/
		  // Outputs
		  .out0_l		(scache0_cpx_req_bufpt_cq_l[7:0]), // Templated
		  .out1_l		(scache0_cpx_atom_bufpt_cq_l), // Templated
		  .cpx_src_grant_cx	(cpx_scache0_grant_cx[7:0]), // Templated
		  .so			(cpx_buf_top_pt0_so_1),	 // Templated
		  // Inputs
		  .in0			(scache0_cpx_req_cq[7:0]), // Templated
		  .in1			(scache0_cpx_atom_cq),	 // Templated
		  .cpx_src_grant_ca	(cpx_scache0_grant_bufp0_ca[7:0]), // Templated
		  .rclk			(rclk),
		  .si			(pt2_so_1),		 // Templated
		  .se			(se_buf4_top));		 // Templated
/*
 cpx_buf_pt AUTO_TEMPLATE(
		  // Outputs
		  .out0_l		(scache@_cpx_req_bufpt_cq_l[7:0]),
		  .out1_l		(scache@_cpx_atom_bufpt_cq_l),
		  .cpx_src_grant_cx	(cpx_scache@_grant_cx[7:0]),
		  .so			(pt3_so_1),
		  // Inputs
                  .se                   (se_buf2_bottom),
		  .in0			(scache@_cpx_req_cq[7:0]),
		  .in1			(scache@_cpx_atom_cq),
		  .cpx_src_grant_ca	(cpx_scache@_grant_bufp4_ca[7:0]),
		  .clk			(clk),
		  .si			(fp_so_1));

 */
   cpx_buf_pt pt3(/*AUTOINST*/
		  // Outputs
		  .out0_l		(scache3_cpx_req_bufpt_cq_l[7:0]), // Templated
		  .out1_l		(scache3_cpx_atom_bufpt_cq_l), // Templated
		  .cpx_src_grant_cx	(cpx_scache3_grant_cx[7:0]), // Templated
		  .so			(pt3_so_1),		 // Templated
		  // Inputs
		  .in0			(scache3_cpx_req_cq[7:0]), // Templated
		  .in1			(scache3_cpx_atom_cq),	 // Templated
		  .cpx_src_grant_ca	(cpx_scache3_grant_bufp4_ca[7:0]), // Templated
		  .rclk			(rclk),
		  .si			(fp_so_1),		 // Templated
		  .se			(se_buf2_bottom));	 // Templated
/*
 cpx_buf_pt AUTO_TEMPLATE(
		  // Outputs
		  .out0_l		(scache@_cpx_req_bufpt_cq_l[7:0]),
		  .out1_l		(scache@_cpx_atom_bufpt_cq_l),
		  .cpx_src_grant_cx	(cpx_scache@_grant_cx[7:0]),
		  .so			(pt1_so_1),
		  // Inputs
                  .se                   (se_buf4_bottom),
		  .in0			(scache@_cpx_req_cq[7:0]),
		  .in1			(scache@_cpx_atom_cq),
		  .cpx_src_grant_ca	(cpx_scache@_grant_bufpm_ca[7:0]),
		  .clk			(clk),
		  .si			(pt3_so_1));

 */
   
   cpx_buf_pt pt1(/*AUTOINST*/
		  // Outputs
		  .out0_l		(scache1_cpx_req_bufpt_cq_l[7:0]), // Templated
		  .out1_l		(scache1_cpx_atom_bufpt_cq_l), // Templated
		  .cpx_src_grant_cx	(cpx_scache1_grant_cx[7:0]), // Templated
		  .so			(pt1_so_1),		 // Templated
		  // Inputs
		  .in0			(scache1_cpx_req_cq[7:0]), // Templated
		  .in1			(scache1_cpx_atom_cq),	 // Templated
		  .cpx_src_grant_ca	(cpx_scache1_grant_bufpm_ca[7:0]), // Templated
		  .rclk			(rclk),
		  .si			(pt3_so_1),		 // Templated
		  .se			(se_buf4_bottom));	 // Templated
/*
 cpx_buf_pt AUTO_TEMPLATE(
		  // Outputs
		  .out0_l		(scache@_cpx_req_bufpt_cq_l[7:0]),
		  .out1_l		(scache@_cpx_atom_bufpt_cq_l),
		  .cpx_src_grant_cx	(cpx_scache@_grant_cx[7:0]),
		  .so			(pt2_so_1),
		  // Inputs
                  .se                   (se_buf2_top),
		  .in0			(scache@_cpx_req_cq[7:0]),
		  .in1			(scache@_cpx_atom_cq),
		  .cpx_src_grant_ca	(cpx_scache@_grant_bufpm_ca[7:0]),
		  .clk			(clk),
		  .si			(pcx_scache2_dat_px2_so_1));
*/
   cpx_buf_pt pt2(/*AUTOINST*/
		  // Outputs
		  .out0_l		(scache2_cpx_req_bufpt_cq_l[7:0]), // Templated
		  .out1_l		(scache2_cpx_atom_bufpt_cq_l), // Templated
		  .cpx_src_grant_cx	(cpx_scache2_grant_cx[7:0]), // Templated
		  .so			(pt2_so_1),		 // Templated
		  // Inputs
		  .in0			(scache2_cpx_req_cq[7:0]), // Templated
		  .in1			(scache2_cpx_atom_cq),	 // Templated
		  .cpx_src_grant_ca	(cpx_scache2_grant_bufpm_ca[7:0]), // Templated
		  .rclk			(rclk),
		  .si			(pcx_scache2_dat_px2_so_1), // Templated
		  .se			(se_buf2_top));		 // Templated
/*
 cpx_buf_pt AUTO_TEMPLATE(
		  // Outputs
		  .out0_l		(fp_cpx_req_bufpt_cq_l[7:0]),
		  .out1_l		(),
		  .cpx_src_grant_cx	(),
		  .so			(fp_so_1),
		  // Inputs
                  .se                   (se_buf0_middle),
		  .in0			(fp_cpx_req_cq[7:0]),
		  .in1			(1'b0),
		  .cpx_src_grant_ca	(8'h0),
		  .clk			(clk),
		  .si			(io_so_1));
 */

   cpx_buf_pt  fp(/*AUTOINST*/
		  // Outputs
		  .out0_l		(fp_cpx_req_bufpt_cq_l[7:0]), // Templated
		  .out1_l		(),			 // Templated
		  .cpx_src_grant_cx	(),			 // Templated
		  .so			(fp_so_1),		 // Templated
		  // Inputs
		  .in0			(fp_cpx_req_cq[7:0]),	 // Templated
		  .in1			(1'b0),			 // Templated
		  .cpx_src_grant_ca	(8'h0),			 // Templated
		  .rclk			(rclk),
		  .si			(io_so_1),		 // Templated
		  .se			(se_buf0_middle));	 // Templated
/*
 cpx_buf_pt AUTO_TEMPLATE(
		  // Outputs
		  .out0_l		(io_cpx_req_bufpt_cq_l[7:0]),
		  .out1_l		(),
		  .cpx_src_grant_cx	(cpx_io_grant_cx[7:0]),
		  .so			(io_so_1),
		  // Inputs
		  .se			(se_buf3_top),
		  .in0			(io_cpx_req_cq2[7:0]),
		  .in1			(1'b0),
		  .cpx_src_grant_ca	(cpx_io_grant_buf1_io_ca[7:0]),
		  .clk			(clk),
		  .si			(io_cpx_reqdata_ff_so_1));
 */
   cpx_buf_pt io(/*AUTOINST*/
		 // Outputs
		 .out0_l		(io_cpx_req_bufpt_cq_l[7:0]), // Templated
		 .out1_l		(),			 // Templated
		 .cpx_src_grant_cx	(cpx_io_grant_cx[7:0]),	 // Templated
		 .so			(io_so_1),		 // Templated
		 // Inputs
		 .in0			(io_cpx_req_cq2[7:0]),	 // Templated
		 .in1			(1'b0),			 // Templated
		 .cpx_src_grant_ca	(cpx_io_grant_buf1_io_ca[7:0]), // Templated
		 .rclk			(rclk),
		 .si			(io_cpx_reqdata_ff_so_1), // Templated
		 .se			(se_buf3_top));		 // Templated
    cpx_buf_p0 p0(/*AUTOINST*/
		  // Outputs
		  .scache0_cpx_req_bufp0_cq(scache0_cpx_req_bufp0_cq[7:0]),
		  .scache0_cpx_atom_bufp0_cq(scache0_cpx_atom_bufp0_cq),
		  .cpx_scache0_grant_bufp0_ca(cpx_scache0_grant_bufp0_ca[7:0]),
		  .cpx_spc0_data_rdy_bufp0_cx(cpx_spc0_data_rdy_bufp0_cx),
		  // Inputs
		  .scache0_cpx_req_bufpt_cq_l(scache0_cpx_req_bufpt_cq_l[7:0]),
		  .scache0_cpx_atom_bufpt_cq_l(scache0_cpx_atom_bufpt_cq_l),
		  .cpx_scache0_grant_bufp1_ca_l(cpx_scache0_grant_bufp1_ca_l[7:0]),
		  .cpx_spc0_data_rdy_bufp1_cx(cpx_spc0_data_rdy_bufp1_cx));

   /* cpx_buf_p0_even AUTO_TEMPLATE(
		 // Outputs
		 .arbcp0_cpxdp_grant_ca	(arbcp0_cpxdp_grant_ca[0]),
		 .arbcp0_cpxdp_q0_hold_ca_l(arbcp0_cpxdp_q0_hold_ca_l[0]),
		 .arbcp0_cpxdp_qsel0_ca	(arbcp0_cpxdp_qsel0_ca[0]),
		 .arbcp0_cpxdp_qsel1_ca_l(arbcp0_cpxdp_qsel1_ca_l[0]),
		 .arbcp0_cpxdp_shift_cx	(arbcp0_cpxdp_shift_cx[0]),
		 .arbcp2_cpxdp_grant_ca	(arbcp2_cpxdp_grant_ca[0]),
		 .arbcp2_cpxdp_q0_hold_ca_l(arbcp2_cpxdp_q0_hold_ca_l[0]),
		 .arbcp2_cpxdp_qsel0_ca	(arbcp2_cpxdp_qsel0_ca[0]),
		 .arbcp2_cpxdp_qsel1_ca_l(arbcp2_cpxdp_qsel1_ca_l[0]),
		 .arbcp2_cpxdp_shift_cx	(arbcp2_cpxdp_shift_cx[0]),
		 .arbcp4_cpxdp_grant_ca	(arbcp4_cpxdp_grant_ca[0]),
		 .arbcp4_cpxdp_q0_hold_ca_l(arbcp4_cpxdp_q0_hold_ca_l[0]),
		 .arbcp4_cpxdp_qsel0_ca	(arbcp4_cpxdp_qsel0_ca[0]),
		 .arbcp4_cpxdp_qsel1_ca_l(arbcp4_cpxdp_qsel1_ca_l[0]),
		 .arbcp4_cpxdp_shift_cx	(arbcp4_cpxdp_shift_cx[0]),
		 .arbcp6_cpxdp_grant_ca	(arbcp6_cpxdp_grant_ca[0]),
		 .arbcp6_cpxdp_q0_hold_ca_l(arbcp6_cpxdp_q0_hold_ca_l[0]),
		 .arbcp6_cpxdp_qsel0_ca	(arbcp6_cpxdp_qsel0_ca[0]),
		 .arbcp6_cpxdp_qsel1_ca_l(arbcp6_cpxdp_qsel1_ca_l[0]),
		 .arbcp6_cpxdp_shift_cx	(arbcp6_cpxdp_shift_cx[0]),
		 // Inputs
    		 .arbcp0_cpxdp_grant_bufp1_ca_l(arbcp0_cpxdp_grant_bufp1_ca_l[0]),
		 .arbcp0_cpxdp_q0_hold_bufp1_ca(arbcp0_cpxdp_q0_hold_bufp1_ca[0]),
		 .arbcp0_cpxdp_qsel0_bufp1_ca_l(arbcp0_cpxdp_qsel0_bufp1_ca_l[0]),
		 .arbcp0_cpxdp_qsel1_bufp1_ca(arbcp0_cpxdp_qsel1_bufp1_ca[0]),
		 .arbcp0_cpxdp_shift_bufp1_cx_l(arbcp0_cpxdp_shift_bufp1_cx_l[0]),
		 .arbcp2_cpxdp_grant_bufp1_ca_l(arbcp2_cpxdp_grant_bufp1_ca_l[0]),
		 .arbcp2_cpxdp_q0_hold_bufp1_ca(arbcp2_cpxdp_q0_hold_bufp1_ca[0]),
		 .arbcp2_cpxdp_qsel0_bufp1_ca_l(arbcp2_cpxdp_qsel0_bufp1_ca_l[0]),
		 .arbcp2_cpxdp_qsel1_bufp1_ca(arbcp2_cpxdp_qsel1_bufp1_ca[0]),
		 .arbcp2_cpxdp_shift_bufp1_cx_l(arbcp2_cpxdp_shift_bufp1_cx_l[0]),
		 .arbcp4_cpxdp_grant_bufp1_ca_l(arbcp4_cpxdp_grant_bufp1_ca_l[0]),
		 .arbcp4_cpxdp_q0_hold_bufp1_ca(arbcp4_cpxdp_q0_hold_bufp1_ca[0]),
		 .arbcp4_cpxdp_qsel0_bufp1_ca_l(arbcp4_cpxdp_qsel0_bufp1_ca_l[0]),
		 .arbcp4_cpxdp_qsel1_bufp1_ca(arbcp4_cpxdp_qsel1_bufp1_ca[0]),
		 .arbcp4_cpxdp_shift_bufp1_cx_l(arbcp4_cpxdp_shift_bufp1_cx_l[0]),
		 .arbcp6_cpxdp_grant_bufp1_ca_l(arbcp6_cpxdp_grant_bufp1_ca_l[0]),
		 .arbcp6_cpxdp_q0_hold_bufp1_ca(arbcp6_cpxdp_q0_hold_bufp1_ca[0]),
		 .arbcp6_cpxdp_qsel0_bufp1_ca_l(arbcp6_cpxdp_qsel0_bufp1_ca_l[0]),
		 .arbcp6_cpxdp_qsel1_bufp1_ca(arbcp6_cpxdp_qsel1_bufp1_ca[0]),
		 .arbcp6_cpxdp_shift_bufp1_cx_l(arbcp6_cpxdp_shift_bufp1_cx_l[0]));
    */

   cpx_buf_p0_even p0_even(/*AUTOINST*/
			   // Outputs
			   .arbcp0_cpxdp_grant_ca(arbcp0_cpxdp_grant_ca[0]), // Templated
			   .arbcp0_cpxdp_q0_hold_ca_l(arbcp0_cpxdp_q0_hold_ca_l[0]), // Templated
			   .arbcp0_cpxdp_qsel0_ca(arbcp0_cpxdp_qsel0_ca[0]), // Templated
			   .arbcp0_cpxdp_qsel1_ca_l(arbcp0_cpxdp_qsel1_ca_l[0]), // Templated
			   .arbcp0_cpxdp_shift_cx(arbcp0_cpxdp_shift_cx[0]), // Templated
			   .arbcp2_cpxdp_grant_ca(arbcp2_cpxdp_grant_ca[0]), // Templated
			   .arbcp2_cpxdp_q0_hold_ca_l(arbcp2_cpxdp_q0_hold_ca_l[0]), // Templated
			   .arbcp2_cpxdp_qsel0_ca(arbcp2_cpxdp_qsel0_ca[0]), // Templated
			   .arbcp2_cpxdp_qsel1_ca_l(arbcp2_cpxdp_qsel1_ca_l[0]), // Templated
			   .arbcp2_cpxdp_shift_cx(arbcp2_cpxdp_shift_cx[0]), // Templated
			   .arbcp4_cpxdp_grant_ca(arbcp4_cpxdp_grant_ca[0]), // Templated
			   .arbcp4_cpxdp_q0_hold_ca_l(arbcp4_cpxdp_q0_hold_ca_l[0]), // Templated
			   .arbcp4_cpxdp_qsel0_ca(arbcp4_cpxdp_qsel0_ca[0]), // Templated
			   .arbcp4_cpxdp_qsel1_ca_l(arbcp4_cpxdp_qsel1_ca_l[0]), // Templated
			   .arbcp4_cpxdp_shift_cx(arbcp4_cpxdp_shift_cx[0]), // Templated
			   .arbcp6_cpxdp_grant_ca(arbcp6_cpxdp_grant_ca[0]), // Templated
			   .arbcp6_cpxdp_q0_hold_ca_l(arbcp6_cpxdp_q0_hold_ca_l[0]), // Templated
			   .arbcp6_cpxdp_qsel0_ca(arbcp6_cpxdp_qsel0_ca[0]), // Templated
			   .arbcp6_cpxdp_qsel1_ca_l(arbcp6_cpxdp_qsel1_ca_l[0]), // Templated
			   .arbcp6_cpxdp_shift_cx(arbcp6_cpxdp_shift_cx[0]), // Templated
			   // Inputs
			   .arbcp0_cpxdp_grant_bufp1_ca_l(arbcp0_cpxdp_grant_bufp1_ca_l[0]), // Templated
			   .arbcp0_cpxdp_q0_hold_bufp1_ca(arbcp0_cpxdp_q0_hold_bufp1_ca[0]), // Templated
			   .arbcp0_cpxdp_qsel0_bufp1_ca_l(arbcp0_cpxdp_qsel0_bufp1_ca_l[0]), // Templated
			   .arbcp0_cpxdp_qsel1_bufp1_ca(arbcp0_cpxdp_qsel1_bufp1_ca[0]), // Templated
			   .arbcp0_cpxdp_shift_bufp1_cx_l(arbcp0_cpxdp_shift_bufp1_cx_l[0]), // Templated
			   .arbcp2_cpxdp_grant_bufp1_ca_l(arbcp2_cpxdp_grant_bufp1_ca_l[0]), // Templated
			   .arbcp2_cpxdp_q0_hold_bufp1_ca(arbcp2_cpxdp_q0_hold_bufp1_ca[0]), // Templated
			   .arbcp2_cpxdp_qsel0_bufp1_ca_l(arbcp2_cpxdp_qsel0_bufp1_ca_l[0]), // Templated
			   .arbcp2_cpxdp_qsel1_bufp1_ca(arbcp2_cpxdp_qsel1_bufp1_ca[0]), // Templated
			   .arbcp2_cpxdp_shift_bufp1_cx_l(arbcp2_cpxdp_shift_bufp1_cx_l[0]), // Templated
			   .arbcp4_cpxdp_grant_bufp1_ca_l(arbcp4_cpxdp_grant_bufp1_ca_l[0]), // Templated
			   .arbcp4_cpxdp_q0_hold_bufp1_ca(arbcp4_cpxdp_q0_hold_bufp1_ca[0]), // Templated
			   .arbcp4_cpxdp_qsel0_bufp1_ca_l(arbcp4_cpxdp_qsel0_bufp1_ca_l[0]), // Templated
			   .arbcp4_cpxdp_qsel1_bufp1_ca(arbcp4_cpxdp_qsel1_bufp1_ca[0]), // Templated
			   .arbcp4_cpxdp_shift_bufp1_cx_l(arbcp4_cpxdp_shift_bufp1_cx_l[0]), // Templated
			   .arbcp6_cpxdp_grant_bufp1_ca_l(arbcp6_cpxdp_grant_bufp1_ca_l[0]), // Templated
			   .arbcp6_cpxdp_q0_hold_bufp1_ca(arbcp6_cpxdp_q0_hold_bufp1_ca[0]), // Templated
			   .arbcp6_cpxdp_qsel0_bufp1_ca_l(arbcp6_cpxdp_qsel0_bufp1_ca_l[0]), // Templated
			   .arbcp6_cpxdp_qsel1_bufp1_ca(arbcp6_cpxdp_qsel1_bufp1_ca[0]), // Templated
			   .arbcp6_cpxdp_shift_bufp1_cx_l(arbcp6_cpxdp_shift_bufp1_cx_l[0])); // Templated
   /* cpx_buf_p0_even AUTO_TEMPLATE(
		 // Outputs
		 .arbcp0_cpxdp_grant_ca	(arbcp1_cpxdp_grant_ca[0]),
		 .arbcp0_cpxdp_q0_hold_ca_l(arbcp1_cpxdp_q0_hold_ca_l[0]),
		 .arbcp0_cpxdp_qsel0_ca	(arbcp1_cpxdp_qsel0_ca[0]),
		 .arbcp0_cpxdp_qsel1_ca_l(arbcp1_cpxdp_qsel1_ca_l[0]),
		 .arbcp0_cpxdp_shift_cx	(arbcp1_cpxdp_shift_cx[0]),
		 .arbcp2_cpxdp_grant_ca	(arbcp3_cpxdp_grant_ca[0]),
		 .arbcp2_cpxdp_q0_hold_ca_l(arbcp3_cpxdp_q0_hold_ca_l[0]),
		 .arbcp2_cpxdp_qsel0_ca	(arbcp3_cpxdp_qsel0_ca[0]),
		 .arbcp2_cpxdp_qsel1_ca_l(arbcp3_cpxdp_qsel1_ca_l[0]),
		 .arbcp2_cpxdp_shift_cx	(arbcp3_cpxdp_shift_cx[0]),
		 .arbcp4_cpxdp_grant_ca	(arbcp5_cpxdp_grant_ca[0]),
		 .arbcp4_cpxdp_q0_hold_ca_l(arbcp5_cpxdp_q0_hold_ca_l[0]),
		 .arbcp4_cpxdp_qsel0_ca	(arbcp5_cpxdp_qsel0_ca[0]),
		 .arbcp4_cpxdp_qsel1_ca_l(arbcp5_cpxdp_qsel1_ca_l[0]),
		 .arbcp4_cpxdp_shift_cx	(arbcp5_cpxdp_shift_cx[0]),
		 .arbcp6_cpxdp_grant_ca	(arbcp7_cpxdp_grant_ca[0]),
		 .arbcp6_cpxdp_q0_hold_ca_l(arbcp7_cpxdp_q0_hold_ca_l[0]),
		 .arbcp6_cpxdp_qsel0_ca	(arbcp7_cpxdp_qsel0_ca[0]),
		 .arbcp6_cpxdp_qsel1_ca_l(arbcp7_cpxdp_qsel1_ca_l[0]),
		 .arbcp6_cpxdp_shift_cx	(arbcp7_cpxdp_shift_cx[0]),
		 // Inputs
		 .arbcp0_cpxdp_grant_bufp1_ca_l(arbcp1_cpxdp_grant_bufp1_ca_l[0]),
		 .arbcp0_cpxdp_q0_hold_bufp1_ca(arbcp1_cpxdp_q0_hold_bufp1_ca[0]),
		 .arbcp0_cpxdp_qsel0_bufp1_ca_l(arbcp1_cpxdp_qsel0_bufp1_ca_l[0]),
		 .arbcp0_cpxdp_qsel1_bufp1_ca(arbcp1_cpxdp_qsel1_bufp1_ca[0]),
		 .arbcp0_cpxdp_shift_bufp1_cx_l(arbcp1_cpxdp_shift_bufp1_cx_l[0]),
		 .arbcp2_cpxdp_grant_bufp1_ca_l(arbcp3_cpxdp_grant_bufp1_ca_l[0]),
		 .arbcp2_cpxdp_q0_hold_bufp1_ca(arbcp3_cpxdp_q0_hold_bufp1_ca[0]),
		 .arbcp2_cpxdp_qsel0_bufp1_ca_l(arbcp3_cpxdp_qsel0_bufp1_ca_l[0]),
		 .arbcp2_cpxdp_qsel1_bufp1_ca(arbcp3_cpxdp_qsel1_bufp1_ca[0]),
		 .arbcp2_cpxdp_shift_bufp1_cx_l(arbcp3_cpxdp_shift_bufp1_cx_l[0]),
		 .arbcp4_cpxdp_grant_bufp1_ca_l(arbcp5_cpxdp_grant_bufp1_ca_l[0]),
		 .arbcp4_cpxdp_q0_hold_bufp1_ca(arbcp5_cpxdp_q0_hold_bufp1_ca[0]),
		 .arbcp4_cpxdp_qsel0_bufp1_ca_l(arbcp5_cpxdp_qsel0_bufp1_ca_l[0]),
		 .arbcp4_cpxdp_qsel1_bufp1_ca(arbcp5_cpxdp_qsel1_bufp1_ca[0]),
		 .arbcp4_cpxdp_shift_bufp1_cx_l(arbcp5_cpxdp_shift_bufp1_cx_l[0]),
		 .arbcp6_cpxdp_grant_bufp1_ca_l(arbcp7_cpxdp_grant_bufp1_ca_l[0]),
		 .arbcp6_cpxdp_q0_hold_bufp1_ca(arbcp7_cpxdp_q0_hold_bufp1_ca[0]),
		 .arbcp6_cpxdp_qsel0_bufp1_ca_l(arbcp7_cpxdp_qsel0_bufp1_ca_l[0]),
		 .arbcp6_cpxdp_qsel1_bufp1_ca(arbcp7_cpxdp_qsel1_bufp1_ca[0]),
		 .arbcp6_cpxdp_shift_bufp1_cx_l(arbcp7_cpxdp_shift_bufp1_cx_l[0]));


   */
   cpx_buf_p0_even p0_odd(/*AUTOINST*/
			  // Outputs
			  .arbcp0_cpxdp_grant_ca(arbcp1_cpxdp_grant_ca[0]), // Templated
			  .arbcp0_cpxdp_q0_hold_ca_l(arbcp1_cpxdp_q0_hold_ca_l[0]), // Templated
			  .arbcp0_cpxdp_qsel0_ca(arbcp1_cpxdp_qsel0_ca[0]), // Templated
			  .arbcp0_cpxdp_qsel1_ca_l(arbcp1_cpxdp_qsel1_ca_l[0]), // Templated
			  .arbcp0_cpxdp_shift_cx(arbcp1_cpxdp_shift_cx[0]), // Templated
			  .arbcp2_cpxdp_grant_ca(arbcp3_cpxdp_grant_ca[0]), // Templated
			  .arbcp2_cpxdp_q0_hold_ca_l(arbcp3_cpxdp_q0_hold_ca_l[0]), // Templated
			  .arbcp2_cpxdp_qsel0_ca(arbcp3_cpxdp_qsel0_ca[0]), // Templated
			  .arbcp2_cpxdp_qsel1_ca_l(arbcp3_cpxdp_qsel1_ca_l[0]), // Templated
			  .arbcp2_cpxdp_shift_cx(arbcp3_cpxdp_shift_cx[0]), // Templated
			  .arbcp4_cpxdp_grant_ca(arbcp5_cpxdp_grant_ca[0]), // Templated
			  .arbcp4_cpxdp_q0_hold_ca_l(arbcp5_cpxdp_q0_hold_ca_l[0]), // Templated
			  .arbcp4_cpxdp_qsel0_ca(arbcp5_cpxdp_qsel0_ca[0]), // Templated
			  .arbcp4_cpxdp_qsel1_ca_l(arbcp5_cpxdp_qsel1_ca_l[0]), // Templated
			  .arbcp4_cpxdp_shift_cx(arbcp5_cpxdp_shift_cx[0]), // Templated
			  .arbcp6_cpxdp_grant_ca(arbcp7_cpxdp_grant_ca[0]), // Templated
			  .arbcp6_cpxdp_q0_hold_ca_l(arbcp7_cpxdp_q0_hold_ca_l[0]), // Templated
			  .arbcp6_cpxdp_qsel0_ca(arbcp7_cpxdp_qsel0_ca[0]), // Templated
			  .arbcp6_cpxdp_qsel1_ca_l(arbcp7_cpxdp_qsel1_ca_l[0]), // Templated
			  .arbcp6_cpxdp_shift_cx(arbcp7_cpxdp_shift_cx[0]), // Templated
			  // Inputs
			  .arbcp0_cpxdp_grant_bufp1_ca_l(arbcp1_cpxdp_grant_bufp1_ca_l[0]), // Templated
			  .arbcp0_cpxdp_q0_hold_bufp1_ca(arbcp1_cpxdp_q0_hold_bufp1_ca[0]), // Templated
			  .arbcp0_cpxdp_qsel0_bufp1_ca_l(arbcp1_cpxdp_qsel0_bufp1_ca_l[0]), // Templated
			  .arbcp0_cpxdp_qsel1_bufp1_ca(arbcp1_cpxdp_qsel1_bufp1_ca[0]), // Templated
			  .arbcp0_cpxdp_shift_bufp1_cx_l(arbcp1_cpxdp_shift_bufp1_cx_l[0]), // Templated
			  .arbcp2_cpxdp_grant_bufp1_ca_l(arbcp3_cpxdp_grant_bufp1_ca_l[0]), // Templated
			  .arbcp2_cpxdp_q0_hold_bufp1_ca(arbcp3_cpxdp_q0_hold_bufp1_ca[0]), // Templated
			  .arbcp2_cpxdp_qsel0_bufp1_ca_l(arbcp3_cpxdp_qsel0_bufp1_ca_l[0]), // Templated
			  .arbcp2_cpxdp_qsel1_bufp1_ca(arbcp3_cpxdp_qsel1_bufp1_ca[0]), // Templated
			  .arbcp2_cpxdp_shift_bufp1_cx_l(arbcp3_cpxdp_shift_bufp1_cx_l[0]), // Templated
			  .arbcp4_cpxdp_grant_bufp1_ca_l(arbcp5_cpxdp_grant_bufp1_ca_l[0]), // Templated
			  .arbcp4_cpxdp_q0_hold_bufp1_ca(arbcp5_cpxdp_q0_hold_bufp1_ca[0]), // Templated
			  .arbcp4_cpxdp_qsel0_bufp1_ca_l(arbcp5_cpxdp_qsel0_bufp1_ca_l[0]), // Templated
			  .arbcp4_cpxdp_qsel1_bufp1_ca(arbcp5_cpxdp_qsel1_bufp1_ca[0]), // Templated
			  .arbcp4_cpxdp_shift_bufp1_cx_l(arbcp5_cpxdp_shift_bufp1_cx_l[0]), // Templated
			  .arbcp6_cpxdp_grant_bufp1_ca_l(arbcp7_cpxdp_grant_bufp1_ca_l[0]), // Templated
			  .arbcp6_cpxdp_q0_hold_bufp1_ca(arbcp7_cpxdp_q0_hold_bufp1_ca[0]), // Templated
			  .arbcp6_cpxdp_qsel0_bufp1_ca_l(arbcp7_cpxdp_qsel0_bufp1_ca_l[0]), // Templated
			  .arbcp6_cpxdp_qsel1_bufp1_ca(arbcp7_cpxdp_qsel1_bufp1_ca[0]), // Templated
			  .arbcp6_cpxdp_shift_bufp1_cx_l(arbcp7_cpxdp_shift_bufp1_cx_l[0])); // Templated
/* cpx_buf_p1 AUTO_TEMPLATE(
		 // Outputs
		 .arbcp0_cpxdp_grant_bufp1_ca_l_0(arbcp0_cpxdp_grant_bufp1_ca_l[0]),
		 .arbcp0_cpxdp_q0_hold_bufp1_ca_0(arbcp0_cpxdp_q0_hold_bufp1_ca[0]),
		 .arbcp0_cpxdp_qsel0_bufp1_ca_l_0(arbcp0_cpxdp_qsel0_bufp1_ca_l[0]),
		 .arbcp0_cpxdp_qsel1_bufp1_ca_0(arbcp0_cpxdp_qsel1_bufp1_ca[0]),
		 .arbcp0_cpxdp_shift_bufp1_cx_l_0(arbcp0_cpxdp_shift_bufp1_cx_l[0]),
		 .arbcp1_cpxdp_grant_bufp1_ca_l_0(arbcp1_cpxdp_grant_bufp1_ca_l[0]),
		 .arbcp1_cpxdp_q0_hold_bufp1_ca_0(arbcp1_cpxdp_q0_hold_bufp1_ca[0]),
		 .arbcp1_cpxdp_qsel0_bufp1_ca_l_0(arbcp1_cpxdp_qsel0_bufp1_ca_l[0]),
		 .arbcp1_cpxdp_qsel1_bufp1_ca_0(arbcp1_cpxdp_qsel1_bufp1_ca[0]),
		 .arbcp1_cpxdp_shift_bufp1_cx_l_0(arbcp1_cpxdp_shift_bufp1_cx_l[0]),
		 .arbcp2_cpxdp_grant_bufp1_ca_l_0(arbcp2_cpxdp_grant_bufp1_ca_l[0]),
		 .arbcp2_cpxdp_q0_hold_bufp1_ca_0(arbcp2_cpxdp_q0_hold_bufp1_ca[0]),
		 .arbcp2_cpxdp_qsel0_bufp1_ca_l_0(arbcp2_cpxdp_qsel0_bufp1_ca_l[0]),
		 .arbcp2_cpxdp_qsel1_bufp1_ca_0(arbcp2_cpxdp_qsel1_bufp1_ca[0]),
		 .arbcp2_cpxdp_shift_bufp1_cx_l_0(arbcp2_cpxdp_shift_bufp1_cx_l[0]),
		 .arbcp3_cpxdp_grant_bufp1_ca_l_0(arbcp3_cpxdp_grant_bufp1_ca_l[0]),
		 .arbcp3_cpxdp_q0_hold_bufp1_ca_0(arbcp3_cpxdp_q0_hold_bufp1_ca[0]),
		 .arbcp3_cpxdp_qsel0_bufp1_ca_l_0(arbcp3_cpxdp_qsel0_bufp1_ca_l[0]),
		 .arbcp3_cpxdp_qsel1_bufp1_ca_0(arbcp3_cpxdp_qsel1_bufp1_ca[0]),
		 .arbcp3_cpxdp_shift_bufp1_cx_l_0(arbcp3_cpxdp_shift_bufp1_cx_l[0]),
		 .arbcp4_cpxdp_grant_bufp1_ca_l_0(arbcp4_cpxdp_grant_bufp1_ca_l[0]),
		 .arbcp4_cpxdp_q0_hold_bufp1_ca_0(arbcp4_cpxdp_q0_hold_bufp1_ca[0]),
		 .arbcp4_cpxdp_qsel0_bufp1_ca_l_0(arbcp4_cpxdp_qsel0_bufp1_ca_l[0]),
		 .arbcp4_cpxdp_qsel1_bufp1_ca_0(arbcp4_cpxdp_qsel1_bufp1_ca[0]),
		 .arbcp4_cpxdp_shift_bufp1_cx_l_0(arbcp4_cpxdp_shift_bufp1_cx_l[0]),
		 .arbcp5_cpxdp_grant_bufp1_ca_l_0(arbcp5_cpxdp_grant_bufp1_ca_l[0]),
		 .arbcp5_cpxdp_q0_hold_bufp1_ca_0(arbcp5_cpxdp_q0_hold_bufp1_ca[0]),
		 .arbcp5_cpxdp_qsel0_bufp1_ca_l_0(arbcp5_cpxdp_qsel0_bufp1_ca_l[0]),
		 .arbcp5_cpxdp_qsel1_bufp1_ca_0(arbcp5_cpxdp_qsel1_bufp1_ca[0]),
		 .arbcp5_cpxdp_shift_bufp1_cx_l_0(arbcp5_cpxdp_shift_bufp1_cx_l[0]),
		 .arbcp6_cpxdp_grant_bufp1_ca_l_0(arbcp6_cpxdp_grant_bufp1_ca_l[0]),
		 .arbcp6_cpxdp_q0_hold_bufp1_ca_0(arbcp6_cpxdp_q0_hold_bufp1_ca[0]),
		 .arbcp6_cpxdp_qsel0_bufp1_ca_l_0(arbcp6_cpxdp_qsel0_bufp1_ca_l[0]),
		 .arbcp6_cpxdp_qsel1_bufp1_ca_0(arbcp6_cpxdp_qsel1_bufp1_ca[0]),
		 .arbcp6_cpxdp_shift_bufp1_cx_l_0(arbcp6_cpxdp_shift_bufp1_cx_l[0]),
		 .arbcp7_cpxdp_grant_bufp1_ca_l_0(arbcp7_cpxdp_grant_bufp1_ca_l[0]),
		 .arbcp7_cpxdp_q0_hold_bufp1_ca_0(arbcp7_cpxdp_q0_hold_bufp1_ca[0]),
		 .arbcp7_cpxdp_qsel0_bufp1_ca_l_0(arbcp7_cpxdp_qsel0_bufp1_ca_l[0]),
		 .arbcp7_cpxdp_qsel1_bufp1_ca_0(arbcp7_cpxdp_qsel1_bufp1_ca[0]),
		 .arbcp7_cpxdp_shift_bufp1_cx_l_0(arbcp7_cpxdp_shift_bufp1_cx_l[0]),
                 .arbcp0_cpxdp_grant_bufp1_ca_l_1(arbcp0_cpxdp_grant_bufp1_ca_l[1]),
                 .arbcp0_cpxdp_q0_hold_bufp1_ca_1(arbcp0_cpxdp_q0_hold_bufp1_ca[1]),
                 .arbcp0_cpxdp_qsel0_bufp1_ca_l_1(arbcp0_cpxdp_qsel0_bufp1_ca_l[1]),
                 .arbcp0_cpxdp_qsel1_bufp1_ca_1(arbcp0_cpxdp_qsel1_bufp1_ca[1]),
                 .arbcp0_cpxdp_shift_bufp1_cx_l_1(arbcp0_cpxdp_shift_bufp1_cx_l[1]),
                 .arbcp1_cpxdp_grant_bufp1_ca_l_1(arbcp1_cpxdp_grant_bufp1_ca_l[1]),
                 .arbcp1_cpxdp_q0_hold_bufp1_ca_1(arbcp1_cpxdp_q0_hold_bufp1_ca[1]),
                 .arbcp1_cpxdp_qsel0_bufp1_ca_l_1(arbcp1_cpxdp_qsel0_bufp1_ca_l[1]),
                 .arbcp1_cpxdp_qsel1_bufp1_ca_1(arbcp1_cpxdp_qsel1_bufp1_ca[1]),
                 .arbcp1_cpxdp_shift_bufp1_cx_l_1(arbcp1_cpxdp_shift_bufp1_cx_l[1]),
                 .arbcp2_cpxdp_grant_bufp1_ca_l_1(arbcp2_cpxdp_grant_bufp1_ca_l[1]),
                 .arbcp2_cpxdp_q0_hold_bufp1_ca_1(arbcp2_cpxdp_q0_hold_bufp1_ca[1]),
                 .arbcp2_cpxdp_qsel0_bufp1_ca_l_1(arbcp2_cpxdp_qsel0_bufp1_ca_l[1]),
                 .arbcp2_cpxdp_qsel1_bufp1_ca_1(arbcp2_cpxdp_qsel1_bufp1_ca[1]),
                 .arbcp2_cpxdp_shift_bufp1_cx_l_1(arbcp2_cpxdp_shift_bufp1_cx_l[1]),
                 .arbcp3_cpxdp_grant_bufp1_ca_l_1(arbcp3_cpxdp_grant_bufp1_ca_l[1]),
                 .arbcp3_cpxdp_q0_hold_bufp1_ca_1(arbcp3_cpxdp_q0_hold_bufp1_ca[1]),
                 .arbcp3_cpxdp_qsel0_bufp1_ca_l_1(arbcp3_cpxdp_qsel0_bufp1_ca_l[1]),
                 .arbcp3_cpxdp_qsel1_bufp1_ca_1(arbcp3_cpxdp_qsel1_bufp1_ca[1]),
                 .arbcp3_cpxdp_shift_bufp1_cx_l_1(arbcp3_cpxdp_shift_bufp1_cx_l[1]),
                 .arbcp4_cpxdp_grant_bufp1_ca_l_1(arbcp4_cpxdp_grant_bufp1_ca_l[1]),
                 .arbcp4_cpxdp_q0_hold_bufp1_ca_1(arbcp4_cpxdp_q0_hold_bufp1_ca[1]),
                 .arbcp4_cpxdp_qsel0_bufp1_ca_l_1(arbcp4_cpxdp_qsel0_bufp1_ca_l[1]),
                 .arbcp4_cpxdp_qsel1_bufp1_ca_1(arbcp4_cpxdp_qsel1_bufp1_ca[1]),
                 .arbcp4_cpxdp_shift_bufp1_cx_l_1(arbcp4_cpxdp_shift_bufp1_cx_l[1]),
                 .arbcp5_cpxdp_grant_bufp1_ca_l_1(arbcp5_cpxdp_grant_bufp1_ca_l[1]),
                 .arbcp5_cpxdp_q0_hold_bufp1_ca_1(arbcp5_cpxdp_q0_hold_bufp1_ca[1]),
                 .arbcp5_cpxdp_qsel0_bufp1_ca_l_1(arbcp5_cpxdp_qsel0_bufp1_ca_l[1]),
                 .arbcp5_cpxdp_qsel1_bufp1_ca_1(arbcp5_cpxdp_qsel1_bufp1_ca[1]),
                 .arbcp5_cpxdp_shift_bufp1_cx_l_1(arbcp5_cpxdp_shift_bufp1_cx_l[1]),
                 .arbcp6_cpxdp_grant_bufp1_ca_l_1(arbcp6_cpxdp_grant_bufp1_ca_l[1]),
                 .arbcp6_cpxdp_q0_hold_bufp1_ca_1(arbcp6_cpxdp_q0_hold_bufp1_ca[1]),
                 .arbcp6_cpxdp_qsel0_bufp1_ca_l_1(arbcp6_cpxdp_qsel0_bufp1_ca_l[1]),
                 .arbcp6_cpxdp_qsel1_bufp1_ca_1(arbcp6_cpxdp_qsel1_bufp1_ca[1]),
                 .arbcp6_cpxdp_shift_bufp1_cx_l_1(arbcp6_cpxdp_shift_bufp1_cx_l[1]),
                 .arbcp7_cpxdp_grant_bufp1_ca_l_1(arbcp7_cpxdp_grant_bufp1_ca_l[1]),
                 .arbcp7_cpxdp_q0_hold_bufp1_ca_1(arbcp7_cpxdp_q0_hold_bufp1_ca[1]),
                 .arbcp7_cpxdp_qsel0_bufp1_ca_l_1(arbcp7_cpxdp_qsel0_bufp1_ca_l[1]),
                 .arbcp7_cpxdp_qsel1_bufp1_ca_1(arbcp7_cpxdp_qsel1_bufp1_ca[1]),
                 .arbcp7_cpxdp_shift_bufp1_cx_l_1(arbcp7_cpxdp_shift_bufp1_cx_l[1]),
		 // Inputs
                 .arbcp0_cpxdp_grant_arbbf_ca_0(arbcp0_cpxdp_grant_arbbf_ca[0]),
		 .arbcp0_cpxdp_q0_hold_arbbf_ca_l_0(arbcp0_cpxdp_q0_hold_arbbf_ca_l[0]),
		 .arbcp0_cpxdp_qsel0_arbbf_ca_0(arbcp0_cpxdp_qsel0_arbbf_ca[0]),
		 .arbcp0_cpxdp_qsel1_arbbf_ca_l_0(arbcp0_cpxdp_qsel1_arbbf_ca_l[0]),
		 .arbcp0_cpxdp_shift_arbbf_cx_0(arbcp0_cpxdp_shift_arbbf_cx[0]),
		 .arbcp1_cpxdp_grant_arbbf_ca_0(arbcp1_cpxdp_grant_arbbf_ca[0]),
		 .arbcp1_cpxdp_q0_hold_arbbf_ca_l_0(arbcp1_cpxdp_q0_hold_arbbf_ca_l[0]),
		 .arbcp1_cpxdp_qsel0_arbbf_ca_0(arbcp1_cpxdp_qsel0_arbbf_ca[0]),
		 .arbcp1_cpxdp_qsel1_arbbf_ca_l_0(arbcp1_cpxdp_qsel1_arbbf_ca_l[0]),
		 .arbcp1_cpxdp_shift_arbbf_cx_0(arbcp1_cpxdp_shift_arbbf_cx[0]),
		 .arbcp2_cpxdp_grant_arbbf_ca_0(arbcp2_cpxdp_grant_arbbf_ca[0]),
		 .arbcp2_cpxdp_q0_hold_arbbf_ca_l_0(arbcp2_cpxdp_q0_hold_arbbf_ca_l[0]),
		 .arbcp2_cpxdp_qsel0_arbbf_ca_0(arbcp2_cpxdp_qsel0_arbbf_ca[0]),
		 .arbcp2_cpxdp_qsel1_arbbf_ca_l_0(arbcp2_cpxdp_qsel1_arbbf_ca_l[0]),
		 .arbcp2_cpxdp_shift_arbbf_cx_0(arbcp2_cpxdp_shift_arbbf_cx[0]),
		 .arbcp3_cpxdp_grant_arbbf_ca_0(arbcp3_cpxdp_grant_arbbf_ca[0]),
		 .arbcp3_cpxdp_q0_hold_arbbf_ca_l_0(arbcp3_cpxdp_q0_hold_arbbf_ca_l[0]),
		 .arbcp3_cpxdp_qsel0_arbbf_ca_0(arbcp3_cpxdp_qsel0_arbbf_ca[0]),
		 .arbcp3_cpxdp_qsel1_arbbf_ca_l_0(arbcp3_cpxdp_qsel1_arbbf_ca_l[0]),
		 .arbcp3_cpxdp_shift_arbbf_cx_0(arbcp3_cpxdp_shift_arbbf_cx[0]),
		 .arbcp4_cpxdp_grant_arbbf_ca_0(arbcp4_cpxdp_grant_arbbf_ca[0]),
		 .arbcp4_cpxdp_q0_hold_arbbf_ca_l_0(arbcp4_cpxdp_q0_hold_arbbf_ca_l[0]),
		 .arbcp4_cpxdp_qsel0_arbbf_ca_0(arbcp4_cpxdp_qsel0_arbbf_ca[0]),
		 .arbcp4_cpxdp_qsel1_arbbf_ca_l_0(arbcp4_cpxdp_qsel1_arbbf_ca_l[0]),
		 .arbcp4_cpxdp_shift_arbbf_cx_0(arbcp4_cpxdp_shift_arbbf_cx[0]),
		 .arbcp5_cpxdp_grant_arbbf_ca_0(arbcp5_cpxdp_grant_arbbf_ca[0]),
		 .arbcp5_cpxdp_q0_hold_arbbf_ca_l_0(arbcp5_cpxdp_q0_hold_arbbf_ca_l[0]),
		 .arbcp5_cpxdp_qsel0_arbbf_ca_0(arbcp5_cpxdp_qsel0_arbbf_ca[0]),
		 .arbcp5_cpxdp_qsel1_arbbf_ca_l_0(arbcp5_cpxdp_qsel1_arbbf_ca_l[0]),
		 .arbcp5_cpxdp_shift_arbbf_cx_0(arbcp5_cpxdp_shift_arbbf_cx[0]),
		 .arbcp6_cpxdp_grant_arbbf_ca_0(arbcp6_cpxdp_grant_arbbf_ca[0]),
		 .arbcp6_cpxdp_q0_hold_arbbf_ca_l_0(arbcp6_cpxdp_q0_hold_arbbf_ca_l[0]),
		 .arbcp6_cpxdp_qsel0_arbbf_ca_0(arbcp6_cpxdp_qsel0_arbbf_ca[0]),
		 .arbcp6_cpxdp_qsel1_arbbf_ca_l_0(arbcp6_cpxdp_qsel1_arbbf_ca_l[0]),
		 .arbcp6_cpxdp_shift_arbbf_cx_0(arbcp6_cpxdp_shift_arbbf_cx[0]),
		 .arbcp7_cpxdp_grant_arbbf_ca_0(arbcp7_cpxdp_grant_arbbf_ca[0]),
		 .arbcp7_cpxdp_q0_hold_arbbf_ca_l_0(arbcp7_cpxdp_q0_hold_arbbf_ca_l[0]),
		 .arbcp7_cpxdp_qsel0_arbbf_ca_0(arbcp7_cpxdp_qsel0_arbbf_ca[0]),
		 .arbcp7_cpxdp_qsel1_arbbf_ca_l_0(arbcp7_cpxdp_qsel1_arbbf_ca_l[0]),
		 .arbcp7_cpxdp_shift_arbbf_cx_0(arbcp7_cpxdp_shift_arbbf_cx[0]), 
                 .arbcp0_cpxdp_grant_arbbf_ca_1(arbcp0_cpxdp_grant_arbbf_ca[1]),
                 .arbcp0_cpxdp_q0_hold_arbbf_ca_l_1(arbcp0_cpxdp_q0_hold_arbbf_ca_l[1]),
                 .arbcp0_cpxdp_qsel0_arbbf_ca_1(arbcp0_cpxdp_qsel0_arbbf_ca[1]),
                 .arbcp0_cpxdp_qsel1_arbbf_ca_l_1(arbcp0_cpxdp_qsel1_arbbf_ca_l[1]),
                 .arbcp0_cpxdp_shift_arbbf_cx_1(arbcp0_cpxdp_shift_arbbf_cx[1]),
                 .arbcp1_cpxdp_grant_arbbf_ca_1(arbcp1_cpxdp_grant_arbbf_ca[1]),
                 .arbcp1_cpxdp_q0_hold_arbbf_ca_l_1(arbcp1_cpxdp_q0_hold_arbbf_ca_l[1]),
                 .arbcp1_cpxdp_qsel0_arbbf_ca_1(arbcp1_cpxdp_qsel0_arbbf_ca[1]),
                 .arbcp1_cpxdp_qsel1_arbbf_ca_l_1(arbcp1_cpxdp_qsel1_arbbf_ca_l[1]),
                 .arbcp1_cpxdp_shift_arbbf_cx_1(arbcp1_cpxdp_shift_arbbf_cx[1]),
                 .arbcp2_cpxdp_grant_arbbf_ca_1(arbcp2_cpxdp_grant_arbbf_ca[1]),
                 .arbcp2_cpxdp_q0_hold_arbbf_ca_l_1(arbcp2_cpxdp_q0_hold_arbbf_ca_l[1]),
                 .arbcp2_cpxdp_qsel0_arbbf_ca_1(arbcp2_cpxdp_qsel0_arbbf_ca[1]),
                 .arbcp2_cpxdp_qsel1_arbbf_ca_l_1(arbcp2_cpxdp_qsel1_arbbf_ca_l[1]),
                 .arbcp2_cpxdp_shift_arbbf_cx_1(arbcp2_cpxdp_shift_arbbf_cx[1]),
                 .arbcp3_cpxdp_grant_arbbf_ca_1(arbcp3_cpxdp_grant_arbbf_ca[1]),
                 .arbcp3_cpxdp_q0_hold_arbbf_ca_l_1(arbcp3_cpxdp_q0_hold_arbbf_ca_l[1]),
                 .arbcp3_cpxdp_qsel0_arbbf_ca_1(arbcp3_cpxdp_qsel0_arbbf_ca[1]),
                 .arbcp3_cpxdp_qsel1_arbbf_ca_l_1(arbcp3_cpxdp_qsel1_arbbf_ca_l[1]),
                 .arbcp3_cpxdp_shift_arbbf_cx_1(arbcp3_cpxdp_shift_arbbf_cx[1]),
                 .arbcp4_cpxdp_grant_arbbf_ca_1(arbcp4_cpxdp_grant_arbbf_ca[1]),
                 .arbcp4_cpxdp_q0_hold_arbbf_ca_l_1(arbcp4_cpxdp_q0_hold_arbbf_ca_l[1]),
                 .arbcp4_cpxdp_qsel0_arbbf_ca_1(arbcp4_cpxdp_qsel0_arbbf_ca[1]),
                 .arbcp4_cpxdp_qsel1_arbbf_ca_l_1(arbcp4_cpxdp_qsel1_arbbf_ca_l[1]),
                 .arbcp4_cpxdp_shift_arbbf_cx_1(arbcp4_cpxdp_shift_arbbf_cx[1]),
                 .arbcp5_cpxdp_grant_arbbf_ca_1(arbcp5_cpxdp_grant_arbbf_ca[1]),
                 .arbcp5_cpxdp_q0_hold_arbbf_ca_l_1(arbcp5_cpxdp_q0_hold_arbbf_ca_l[1]),
                 .arbcp5_cpxdp_qsel0_arbbf_ca_1(arbcp5_cpxdp_qsel0_arbbf_ca[1]),
                 .arbcp5_cpxdp_qsel1_arbbf_ca_l_1(arbcp5_cpxdp_qsel1_arbbf_ca_l[1]),
                 .arbcp5_cpxdp_shift_arbbf_cx_1(arbcp5_cpxdp_shift_arbbf_cx[1]),
                 .arbcp6_cpxdp_grant_arbbf_ca_1(arbcp6_cpxdp_grant_arbbf_ca[1]),
                 .arbcp6_cpxdp_q0_hold_arbbf_ca_l_1(arbcp6_cpxdp_q0_hold_arbbf_ca_l[1]),
                 .arbcp6_cpxdp_qsel0_arbbf_ca_1(arbcp6_cpxdp_qsel0_arbbf_ca[1]),
                 .arbcp6_cpxdp_qsel1_arbbf_ca_l_1(arbcp6_cpxdp_qsel1_arbbf_ca_l[1]),
                 .arbcp6_cpxdp_shift_arbbf_cx_1(arbcp6_cpxdp_shift_arbbf_cx[1]),
                 .arbcp7_cpxdp_grant_arbbf_ca_1(arbcp7_cpxdp_grant_arbbf_ca[1]),
                 .arbcp7_cpxdp_q0_hold_arbbf_ca_l_1(arbcp7_cpxdp_q0_hold_arbbf_ca_l[1]),
                 .arbcp7_cpxdp_qsel0_arbbf_ca_1(arbcp7_cpxdp_qsel0_arbbf_ca[1]),
                 .arbcp7_cpxdp_qsel1_arbbf_ca_l_1(arbcp7_cpxdp_qsel1_arbbf_ca_l[1]),
                 .arbcp7_cpxdp_shift_arbbf_cx_1(arbcp7_cpxdp_shift_arbbf_cx[1]));
*/
   cpx_buf_p1 p1(/*AUTOINST*/
		 // Outputs
		 .scache0_cpx_req_bufp1_cq(scache0_cpx_req_bufp1_cq[7:0]),
		 .scache0_cpx_atom_bufp1_cq(scache0_cpx_atom_bufp1_cq),
		 .cpx_scache0_grant_bufp1_ca_l(cpx_scache0_grant_bufp1_ca_l[7:0]),
		 .cpx_spc0_data_rdy_bufp1_cx(cpx_spc0_data_rdy_bufp1_cx),
		 .cpx_spc1_data_rdy_bufp1_cx(cpx_spc1_data_rdy_bufp1_cx),
		 .cpx_spc2_data_rdy_bufp1_cx(cpx_spc2_data_rdy_bufp1_cx),
		 .arbcp0_cpxdp_grant_bufp1_ca_l_0(arbcp0_cpxdp_grant_bufp1_ca_l[0]), // Templated
		 .arbcp0_cpxdp_q0_hold_bufp1_ca_0(arbcp0_cpxdp_q0_hold_bufp1_ca[0]), // Templated
		 .arbcp0_cpxdp_qsel0_bufp1_ca_l_0(arbcp0_cpxdp_qsel0_bufp1_ca_l[0]), // Templated
		 .arbcp0_cpxdp_qsel1_bufp1_ca_0(arbcp0_cpxdp_qsel1_bufp1_ca[0]), // Templated
		 .arbcp0_cpxdp_shift_bufp1_cx_l_0(arbcp0_cpxdp_shift_bufp1_cx_l[0]), // Templated
		 .arbcp1_cpxdp_grant_bufp1_ca_l_0(arbcp1_cpxdp_grant_bufp1_ca_l[0]), // Templated
		 .arbcp1_cpxdp_q0_hold_bufp1_ca_0(arbcp1_cpxdp_q0_hold_bufp1_ca[0]), // Templated
		 .arbcp1_cpxdp_qsel0_bufp1_ca_l_0(arbcp1_cpxdp_qsel0_bufp1_ca_l[0]), // Templated
		 .arbcp1_cpxdp_qsel1_bufp1_ca_0(arbcp1_cpxdp_qsel1_bufp1_ca[0]), // Templated
		 .arbcp1_cpxdp_shift_bufp1_cx_l_0(arbcp1_cpxdp_shift_bufp1_cx_l[0]), // Templated
		 .arbcp2_cpxdp_grant_bufp1_ca_l_0(arbcp2_cpxdp_grant_bufp1_ca_l[0]), // Templated
		 .arbcp2_cpxdp_q0_hold_bufp1_ca_0(arbcp2_cpxdp_q0_hold_bufp1_ca[0]), // Templated
		 .arbcp2_cpxdp_qsel0_bufp1_ca_l_0(arbcp2_cpxdp_qsel0_bufp1_ca_l[0]), // Templated
		 .arbcp2_cpxdp_qsel1_bufp1_ca_0(arbcp2_cpxdp_qsel1_bufp1_ca[0]), // Templated
		 .arbcp2_cpxdp_shift_bufp1_cx_l_0(arbcp2_cpxdp_shift_bufp1_cx_l[0]), // Templated
		 .arbcp3_cpxdp_grant_bufp1_ca_l_0(arbcp3_cpxdp_grant_bufp1_ca_l[0]), // Templated
		 .arbcp3_cpxdp_q0_hold_bufp1_ca_0(arbcp3_cpxdp_q0_hold_bufp1_ca[0]), // Templated
		 .arbcp3_cpxdp_qsel0_bufp1_ca_l_0(arbcp3_cpxdp_qsel0_bufp1_ca_l[0]), // Templated
		 .arbcp3_cpxdp_qsel1_bufp1_ca_0(arbcp3_cpxdp_qsel1_bufp1_ca[0]), // Templated
		 .arbcp3_cpxdp_shift_bufp1_cx_l_0(arbcp3_cpxdp_shift_bufp1_cx_l[0]), // Templated
		 .arbcp4_cpxdp_grant_bufp1_ca_l_0(arbcp4_cpxdp_grant_bufp1_ca_l[0]), // Templated
		 .arbcp4_cpxdp_q0_hold_bufp1_ca_0(arbcp4_cpxdp_q0_hold_bufp1_ca[0]), // Templated
		 .arbcp4_cpxdp_qsel0_bufp1_ca_l_0(arbcp4_cpxdp_qsel0_bufp1_ca_l[0]), // Templated
		 .arbcp4_cpxdp_qsel1_bufp1_ca_0(arbcp4_cpxdp_qsel1_bufp1_ca[0]), // Templated
		 .arbcp4_cpxdp_shift_bufp1_cx_l_0(arbcp4_cpxdp_shift_bufp1_cx_l[0]), // Templated
		 .arbcp5_cpxdp_grant_bufp1_ca_l_0(arbcp5_cpxdp_grant_bufp1_ca_l[0]), // Templated
		 .arbcp5_cpxdp_q0_hold_bufp1_ca_0(arbcp5_cpxdp_q0_hold_bufp1_ca[0]), // Templated
		 .arbcp5_cpxdp_qsel0_bufp1_ca_l_0(arbcp5_cpxdp_qsel0_bufp1_ca_l[0]), // Templated
		 .arbcp5_cpxdp_qsel1_bufp1_ca_0(arbcp5_cpxdp_qsel1_bufp1_ca[0]), // Templated
		 .arbcp5_cpxdp_shift_bufp1_cx_l_0(arbcp5_cpxdp_shift_bufp1_cx_l[0]), // Templated
		 .arbcp6_cpxdp_grant_bufp1_ca_l_0(arbcp6_cpxdp_grant_bufp1_ca_l[0]), // Templated
		 .arbcp6_cpxdp_q0_hold_bufp1_ca_0(arbcp6_cpxdp_q0_hold_bufp1_ca[0]), // Templated
		 .arbcp6_cpxdp_qsel0_bufp1_ca_l_0(arbcp6_cpxdp_qsel0_bufp1_ca_l[0]), // Templated
		 .arbcp6_cpxdp_qsel1_bufp1_ca_0(arbcp6_cpxdp_qsel1_bufp1_ca[0]), // Templated
		 .arbcp6_cpxdp_shift_bufp1_cx_l_0(arbcp6_cpxdp_shift_bufp1_cx_l[0]), // Templated
		 .arbcp7_cpxdp_grant_bufp1_ca_l_0(arbcp7_cpxdp_grant_bufp1_ca_l[0]), // Templated
		 .arbcp7_cpxdp_q0_hold_bufp1_ca_0(arbcp7_cpxdp_q0_hold_bufp1_ca[0]), // Templated
		 .arbcp7_cpxdp_qsel0_bufp1_ca_l_0(arbcp7_cpxdp_qsel0_bufp1_ca_l[0]), // Templated
		 .arbcp7_cpxdp_qsel1_bufp1_ca_0(arbcp7_cpxdp_qsel1_bufp1_ca[0]), // Templated
		 .arbcp7_cpxdp_shift_bufp1_cx_l_0(arbcp7_cpxdp_shift_bufp1_cx_l[0]), // Templated
		 .arbcp0_cpxdp_grant_bufp1_ca_l_1(arbcp0_cpxdp_grant_bufp1_ca_l[1]), // Templated
		 .arbcp0_cpxdp_q0_hold_bufp1_ca_1(arbcp0_cpxdp_q0_hold_bufp1_ca[1]), // Templated
		 .arbcp0_cpxdp_qsel0_bufp1_ca_l_1(arbcp0_cpxdp_qsel0_bufp1_ca_l[1]), // Templated
		 .arbcp0_cpxdp_qsel1_bufp1_ca_1(arbcp0_cpxdp_qsel1_bufp1_ca[1]), // Templated
		 .arbcp0_cpxdp_shift_bufp1_cx_l_1(arbcp0_cpxdp_shift_bufp1_cx_l[1]), // Templated
		 .arbcp1_cpxdp_grant_bufp1_ca_l_1(arbcp1_cpxdp_grant_bufp1_ca_l[1]), // Templated
		 .arbcp1_cpxdp_q0_hold_bufp1_ca_1(arbcp1_cpxdp_q0_hold_bufp1_ca[1]), // Templated
		 .arbcp1_cpxdp_qsel0_bufp1_ca_l_1(arbcp1_cpxdp_qsel0_bufp1_ca_l[1]), // Templated
		 .arbcp1_cpxdp_qsel1_bufp1_ca_1(arbcp1_cpxdp_qsel1_bufp1_ca[1]), // Templated
		 .arbcp1_cpxdp_shift_bufp1_cx_l_1(arbcp1_cpxdp_shift_bufp1_cx_l[1]), // Templated
		 .arbcp2_cpxdp_grant_bufp1_ca_l_1(arbcp2_cpxdp_grant_bufp1_ca_l[1]), // Templated
		 .arbcp2_cpxdp_q0_hold_bufp1_ca_1(arbcp2_cpxdp_q0_hold_bufp1_ca[1]), // Templated
		 .arbcp2_cpxdp_qsel0_bufp1_ca_l_1(arbcp2_cpxdp_qsel0_bufp1_ca_l[1]), // Templated
		 .arbcp2_cpxdp_qsel1_bufp1_ca_1(arbcp2_cpxdp_qsel1_bufp1_ca[1]), // Templated
		 .arbcp2_cpxdp_shift_bufp1_cx_l_1(arbcp2_cpxdp_shift_bufp1_cx_l[1]), // Templated
		 .arbcp3_cpxdp_grant_bufp1_ca_l_1(arbcp3_cpxdp_grant_bufp1_ca_l[1]), // Templated
		 .arbcp3_cpxdp_q0_hold_bufp1_ca_1(arbcp3_cpxdp_q0_hold_bufp1_ca[1]), // Templated
		 .arbcp3_cpxdp_qsel0_bufp1_ca_l_1(arbcp3_cpxdp_qsel0_bufp1_ca_l[1]), // Templated
		 .arbcp3_cpxdp_qsel1_bufp1_ca_1(arbcp3_cpxdp_qsel1_bufp1_ca[1]), // Templated
		 .arbcp3_cpxdp_shift_bufp1_cx_l_1(arbcp3_cpxdp_shift_bufp1_cx_l[1]), // Templated
		 .arbcp4_cpxdp_grant_bufp1_ca_l_1(arbcp4_cpxdp_grant_bufp1_ca_l[1]), // Templated
		 .arbcp4_cpxdp_q0_hold_bufp1_ca_1(arbcp4_cpxdp_q0_hold_bufp1_ca[1]), // Templated
		 .arbcp4_cpxdp_qsel0_bufp1_ca_l_1(arbcp4_cpxdp_qsel0_bufp1_ca_l[1]), // Templated
		 .arbcp4_cpxdp_qsel1_bufp1_ca_1(arbcp4_cpxdp_qsel1_bufp1_ca[1]), // Templated
		 .arbcp4_cpxdp_shift_bufp1_cx_l_1(arbcp4_cpxdp_shift_bufp1_cx_l[1]), // Templated
		 .arbcp5_cpxdp_grant_bufp1_ca_l_1(arbcp5_cpxdp_grant_bufp1_ca_l[1]), // Templated
		 .arbcp5_cpxdp_q0_hold_bufp1_ca_1(arbcp5_cpxdp_q0_hold_bufp1_ca[1]), // Templated
		 .arbcp5_cpxdp_qsel0_bufp1_ca_l_1(arbcp5_cpxdp_qsel0_bufp1_ca_l[1]), // Templated
		 .arbcp5_cpxdp_qsel1_bufp1_ca_1(arbcp5_cpxdp_qsel1_bufp1_ca[1]), // Templated
		 .arbcp5_cpxdp_shift_bufp1_cx_l_1(arbcp5_cpxdp_shift_bufp1_cx_l[1]), // Templated
		 .arbcp6_cpxdp_grant_bufp1_ca_l_1(arbcp6_cpxdp_grant_bufp1_ca_l[1]), // Templated
		 .arbcp6_cpxdp_q0_hold_bufp1_ca_1(arbcp6_cpxdp_q0_hold_bufp1_ca[1]), // Templated
		 .arbcp6_cpxdp_qsel0_bufp1_ca_l_1(arbcp6_cpxdp_qsel0_bufp1_ca_l[1]), // Templated
		 .arbcp6_cpxdp_qsel1_bufp1_ca_1(arbcp6_cpxdp_qsel1_bufp1_ca[1]), // Templated
		 .arbcp6_cpxdp_shift_bufp1_cx_l_1(arbcp6_cpxdp_shift_bufp1_cx_l[1]), // Templated
		 .arbcp7_cpxdp_grant_bufp1_ca_l_1(arbcp7_cpxdp_grant_bufp1_ca_l[1]), // Templated
		 .arbcp7_cpxdp_q0_hold_bufp1_ca_1(arbcp7_cpxdp_q0_hold_bufp1_ca[1]), // Templated
		 .arbcp7_cpxdp_qsel0_bufp1_ca_l_1(arbcp7_cpxdp_qsel0_bufp1_ca_l[1]), // Templated
		 .arbcp7_cpxdp_qsel1_bufp1_ca_1(arbcp7_cpxdp_qsel1_bufp1_ca[1]), // Templated
		 .arbcp7_cpxdp_shift_bufp1_cx_l_1(arbcp7_cpxdp_shift_bufp1_cx_l[1]), // Templated
		 // Inputs
		 .scache0_cpx_req_bufp0_cq(scache0_cpx_req_bufp0_cq[7:0]),
		 .scache0_cpx_atom_bufp0_cq(scache0_cpx_atom_bufp0_cq),
		 .cpx_scache0_grant_ca	(cpx_scache0_grant_ca[7:0]),
		 .cpx_spc0_data_rdy_cx	(cpx_spc0_data_rdy_cx),
		 .cpx_spc1_data_rdy_cx	(cpx_spc1_data_rdy_cx),
		 .cpx_spc2_data_rdy_cx	(cpx_spc2_data_rdy_cx),
		 .arbcp0_cpxdp_grant_arbbf_ca_0(arbcp0_cpxdp_grant_arbbf_ca[0]), // Templated
		 .arbcp0_cpxdp_q0_hold_arbbf_ca_l_0(arbcp0_cpxdp_q0_hold_arbbf_ca_l[0]), // Templated
		 .arbcp0_cpxdp_qsel0_arbbf_ca_0(arbcp0_cpxdp_qsel0_arbbf_ca[0]), // Templated
		 .arbcp0_cpxdp_qsel1_arbbf_ca_l_0(arbcp0_cpxdp_qsel1_arbbf_ca_l[0]), // Templated
		 .arbcp0_cpxdp_shift_arbbf_cx_0(arbcp0_cpxdp_shift_arbbf_cx[0]), // Templated
		 .arbcp1_cpxdp_grant_arbbf_ca_0(arbcp1_cpxdp_grant_arbbf_ca[0]), // Templated
		 .arbcp1_cpxdp_q0_hold_arbbf_ca_l_0(arbcp1_cpxdp_q0_hold_arbbf_ca_l[0]), // Templated
		 .arbcp1_cpxdp_qsel0_arbbf_ca_0(arbcp1_cpxdp_qsel0_arbbf_ca[0]), // Templated
		 .arbcp1_cpxdp_qsel1_arbbf_ca_l_0(arbcp1_cpxdp_qsel1_arbbf_ca_l[0]), // Templated
		 .arbcp1_cpxdp_shift_arbbf_cx_0(arbcp1_cpxdp_shift_arbbf_cx[0]), // Templated
		 .arbcp2_cpxdp_grant_arbbf_ca_0(arbcp2_cpxdp_grant_arbbf_ca[0]), // Templated
		 .arbcp2_cpxdp_q0_hold_arbbf_ca_l_0(arbcp2_cpxdp_q0_hold_arbbf_ca_l[0]), // Templated
		 .arbcp2_cpxdp_qsel0_arbbf_ca_0(arbcp2_cpxdp_qsel0_arbbf_ca[0]), // Templated
		 .arbcp2_cpxdp_qsel1_arbbf_ca_l_0(arbcp2_cpxdp_qsel1_arbbf_ca_l[0]), // Templated
		 .arbcp2_cpxdp_shift_arbbf_cx_0(arbcp2_cpxdp_shift_arbbf_cx[0]), // Templated
		 .arbcp3_cpxdp_grant_arbbf_ca_0(arbcp3_cpxdp_grant_arbbf_ca[0]), // Templated
		 .arbcp3_cpxdp_q0_hold_arbbf_ca_l_0(arbcp3_cpxdp_q0_hold_arbbf_ca_l[0]), // Templated
		 .arbcp3_cpxdp_qsel0_arbbf_ca_0(arbcp3_cpxdp_qsel0_arbbf_ca[0]), // Templated
		 .arbcp3_cpxdp_qsel1_arbbf_ca_l_0(arbcp3_cpxdp_qsel1_arbbf_ca_l[0]), // Templated
		 .arbcp3_cpxdp_shift_arbbf_cx_0(arbcp3_cpxdp_shift_arbbf_cx[0]), // Templated
		 .arbcp4_cpxdp_grant_arbbf_ca_0(arbcp4_cpxdp_grant_arbbf_ca[0]), // Templated
		 .arbcp4_cpxdp_q0_hold_arbbf_ca_l_0(arbcp4_cpxdp_q0_hold_arbbf_ca_l[0]), // Templated
		 .arbcp4_cpxdp_qsel0_arbbf_ca_0(arbcp4_cpxdp_qsel0_arbbf_ca[0]), // Templated
		 .arbcp4_cpxdp_qsel1_arbbf_ca_l_0(arbcp4_cpxdp_qsel1_arbbf_ca_l[0]), // Templated
		 .arbcp4_cpxdp_shift_arbbf_cx_0(arbcp4_cpxdp_shift_arbbf_cx[0]), // Templated
		 .arbcp5_cpxdp_grant_arbbf_ca_0(arbcp5_cpxdp_grant_arbbf_ca[0]), // Templated
		 .arbcp5_cpxdp_q0_hold_arbbf_ca_l_0(arbcp5_cpxdp_q0_hold_arbbf_ca_l[0]), // Templated
		 .arbcp5_cpxdp_qsel0_arbbf_ca_0(arbcp5_cpxdp_qsel0_arbbf_ca[0]), // Templated
		 .arbcp5_cpxdp_qsel1_arbbf_ca_l_0(arbcp5_cpxdp_qsel1_arbbf_ca_l[0]), // Templated
		 .arbcp5_cpxdp_shift_arbbf_cx_0(arbcp5_cpxdp_shift_arbbf_cx[0]), // Templated
		 .arbcp6_cpxdp_grant_arbbf_ca_0(arbcp6_cpxdp_grant_arbbf_ca[0]), // Templated
		 .arbcp6_cpxdp_q0_hold_arbbf_ca_l_0(arbcp6_cpxdp_q0_hold_arbbf_ca_l[0]), // Templated
		 .arbcp6_cpxdp_qsel0_arbbf_ca_0(arbcp6_cpxdp_qsel0_arbbf_ca[0]), // Templated
		 .arbcp6_cpxdp_qsel1_arbbf_ca_l_0(arbcp6_cpxdp_qsel1_arbbf_ca_l[0]), // Templated
		 .arbcp6_cpxdp_shift_arbbf_cx_0(arbcp6_cpxdp_shift_arbbf_cx[0]), // Templated
		 .arbcp7_cpxdp_grant_arbbf_ca_0(arbcp7_cpxdp_grant_arbbf_ca[0]), // Templated
		 .arbcp7_cpxdp_q0_hold_arbbf_ca_l_0(arbcp7_cpxdp_q0_hold_arbbf_ca_l[0]), // Templated
		 .arbcp7_cpxdp_qsel0_arbbf_ca_0(arbcp7_cpxdp_qsel0_arbbf_ca[0]), // Templated
		 .arbcp7_cpxdp_qsel1_arbbf_ca_l_0(arbcp7_cpxdp_qsel1_arbbf_ca_l[0]), // Templated
		 .arbcp7_cpxdp_shift_arbbf_cx_0(arbcp7_cpxdp_shift_arbbf_cx[0]), // Templated
		 .arbcp0_cpxdp_grant_arbbf_ca_1(arbcp0_cpxdp_grant_arbbf_ca[1]), // Templated
		 .arbcp0_cpxdp_q0_hold_arbbf_ca_l_1(arbcp0_cpxdp_q0_hold_arbbf_ca_l[1]), // Templated
		 .arbcp0_cpxdp_qsel0_arbbf_ca_1(arbcp0_cpxdp_qsel0_arbbf_ca[1]), // Templated
		 .arbcp0_cpxdp_qsel1_arbbf_ca_l_1(arbcp0_cpxdp_qsel1_arbbf_ca_l[1]), // Templated
		 .arbcp0_cpxdp_shift_arbbf_cx_1(arbcp0_cpxdp_shift_arbbf_cx[1]), // Templated
		 .arbcp1_cpxdp_grant_arbbf_ca_1(arbcp1_cpxdp_grant_arbbf_ca[1]), // Templated
		 .arbcp1_cpxdp_q0_hold_arbbf_ca_l_1(arbcp1_cpxdp_q0_hold_arbbf_ca_l[1]), // Templated
		 .arbcp1_cpxdp_qsel0_arbbf_ca_1(arbcp1_cpxdp_qsel0_arbbf_ca[1]), // Templated
		 .arbcp1_cpxdp_qsel1_arbbf_ca_l_1(arbcp1_cpxdp_qsel1_arbbf_ca_l[1]), // Templated
		 .arbcp1_cpxdp_shift_arbbf_cx_1(arbcp1_cpxdp_shift_arbbf_cx[1]), // Templated
		 .arbcp2_cpxdp_grant_arbbf_ca_1(arbcp2_cpxdp_grant_arbbf_ca[1]), // Templated
		 .arbcp2_cpxdp_q0_hold_arbbf_ca_l_1(arbcp2_cpxdp_q0_hold_arbbf_ca_l[1]), // Templated
		 .arbcp2_cpxdp_qsel0_arbbf_ca_1(arbcp2_cpxdp_qsel0_arbbf_ca[1]), // Templated
		 .arbcp2_cpxdp_qsel1_arbbf_ca_l_1(arbcp2_cpxdp_qsel1_arbbf_ca_l[1]), // Templated
		 .arbcp2_cpxdp_shift_arbbf_cx_1(arbcp2_cpxdp_shift_arbbf_cx[1]), // Templated
		 .arbcp3_cpxdp_grant_arbbf_ca_1(arbcp3_cpxdp_grant_arbbf_ca[1]), // Templated
		 .arbcp3_cpxdp_q0_hold_arbbf_ca_l_1(arbcp3_cpxdp_q0_hold_arbbf_ca_l[1]), // Templated
		 .arbcp3_cpxdp_qsel0_arbbf_ca_1(arbcp3_cpxdp_qsel0_arbbf_ca[1]), // Templated
		 .arbcp3_cpxdp_qsel1_arbbf_ca_l_1(arbcp3_cpxdp_qsel1_arbbf_ca_l[1]), // Templated
		 .arbcp3_cpxdp_shift_arbbf_cx_1(arbcp3_cpxdp_shift_arbbf_cx[1]), // Templated
		 .arbcp4_cpxdp_grant_arbbf_ca_1(arbcp4_cpxdp_grant_arbbf_ca[1]), // Templated
		 .arbcp4_cpxdp_q0_hold_arbbf_ca_l_1(arbcp4_cpxdp_q0_hold_arbbf_ca_l[1]), // Templated
		 .arbcp4_cpxdp_qsel0_arbbf_ca_1(arbcp4_cpxdp_qsel0_arbbf_ca[1]), // Templated
		 .arbcp4_cpxdp_qsel1_arbbf_ca_l_1(arbcp4_cpxdp_qsel1_arbbf_ca_l[1]), // Templated
		 .arbcp4_cpxdp_shift_arbbf_cx_1(arbcp4_cpxdp_shift_arbbf_cx[1]), // Templated
		 .arbcp5_cpxdp_grant_arbbf_ca_1(arbcp5_cpxdp_grant_arbbf_ca[1]), // Templated
		 .arbcp5_cpxdp_q0_hold_arbbf_ca_l_1(arbcp5_cpxdp_q0_hold_arbbf_ca_l[1]), // Templated
		 .arbcp5_cpxdp_qsel0_arbbf_ca_1(arbcp5_cpxdp_qsel0_arbbf_ca[1]), // Templated
		 .arbcp5_cpxdp_qsel1_arbbf_ca_l_1(arbcp5_cpxdp_qsel1_arbbf_ca_l[1]), // Templated
		 .arbcp5_cpxdp_shift_arbbf_cx_1(arbcp5_cpxdp_shift_arbbf_cx[1]), // Templated
		 .arbcp6_cpxdp_grant_arbbf_ca_1(arbcp6_cpxdp_grant_arbbf_ca[1]), // Templated
		 .arbcp6_cpxdp_q0_hold_arbbf_ca_l_1(arbcp6_cpxdp_q0_hold_arbbf_ca_l[1]), // Templated
		 .arbcp6_cpxdp_qsel0_arbbf_ca_1(arbcp6_cpxdp_qsel0_arbbf_ca[1]), // Templated
		 .arbcp6_cpxdp_qsel1_arbbf_ca_l_1(arbcp6_cpxdp_qsel1_arbbf_ca_l[1]), // Templated
		 .arbcp6_cpxdp_shift_arbbf_cx_1(arbcp6_cpxdp_shift_arbbf_cx[1]), // Templated
		 .arbcp7_cpxdp_grant_arbbf_ca_1(arbcp7_cpxdp_grant_arbbf_ca[1]), // Templated
		 .arbcp7_cpxdp_q0_hold_arbbf_ca_l_1(arbcp7_cpxdp_q0_hold_arbbf_ca_l[1]), // Templated
		 .arbcp7_cpxdp_qsel0_arbbf_ca_1(arbcp7_cpxdp_qsel0_arbbf_ca[1]), // Templated
		 .arbcp7_cpxdp_qsel1_arbbf_ca_l_1(arbcp7_cpxdp_qsel1_arbbf_ca_l[1]), // Templated
		 .arbcp7_cpxdp_shift_arbbf_cx_1(arbcp7_cpxdp_shift_arbbf_cx[1])); // Templated
   cpx_fpbuf_p0  fpbuf_p0(/*AUTOINST*/
			  // Outputs
			  .fp_cpx_req_bufp0_cq(fp_cpx_req_bufp0_cq[7:0]),
			  // Inputs
			  .fp_cpx_req_bufpt_cq_l(fp_cpx_req_bufpt_cq_l[7:0]));

/*   cpx_fpbuf_p1  AUTO_TEMPLATE(
                 // Outputs
                 .arbcp0_cpxdp_grant_bufp1_ca_l_1(arbcp0_cpxdp_grant_bufp1_ca_l[3]),
                 .arbcp0_cpxdp_q0_hold_bufp1_ca_1(arbcp0_cpxdp_q0_hold_bufp1_ca[3]),
                 .arbcp0_cpxdp_qsel0_bufp1_ca_l_1(arbcp0_cpxdp_qsel0_bufp1_ca_l[3]),
                 .arbcp0_cpxdp_qsel1_bufp1_ca_1(arbcp0_cpxdp_qsel1_bufp1_ca[3]),
                 .arbcp0_cpxdp_shift_bufp1_cx_l_1(arbcp0_cpxdp_shift_bufp1_cx_l[3]),
                 .arbcp1_cpxdp_grant_bufp1_ca_l_1(arbcp1_cpxdp_grant_bufp1_ca_l[3]),
                 .arbcp1_cpxdp_q0_hold_bufp1_ca_1(arbcp1_cpxdp_q0_hold_bufp1_ca[3]),
                 .arbcp1_cpxdp_qsel0_bufp1_ca_l_1(arbcp1_cpxdp_qsel0_bufp1_ca_l[3]),
                 .arbcp1_cpxdp_qsel1_bufp1_ca_1(arbcp1_cpxdp_qsel1_bufp1_ca[3]),
                 .arbcp1_cpxdp_shift_bufp1_cx_l_1(arbcp1_cpxdp_shift_bufp1_cx_l[3]),
                 .arbcp2_cpxdp_grant_bufp1_ca_l_1(arbcp2_cpxdp_grant_bufp1_ca_l[3]),
                 .arbcp2_cpxdp_q0_hold_bufp1_ca_1(arbcp2_cpxdp_q0_hold_bufp1_ca[3]),
                 .arbcp2_cpxdp_qsel0_bufp1_ca_l_1(arbcp2_cpxdp_qsel0_bufp1_ca_l[3]),
                 .arbcp2_cpxdp_qsel1_bufp1_ca_1(arbcp2_cpxdp_qsel1_bufp1_ca[3]),
                 .arbcp2_cpxdp_shift_bufp1_cx_l_1(arbcp2_cpxdp_shift_bufp1_cx_l[3]),
                 .arbcp3_cpxdp_grant_bufp1_ca_l_1(arbcp3_cpxdp_grant_bufp1_ca_l[3]),
                 .arbcp3_cpxdp_q0_hold_bufp1_ca_1(arbcp3_cpxdp_q0_hold_bufp1_ca[3]),
                 .arbcp3_cpxdp_qsel0_bufp1_ca_l_1(arbcp3_cpxdp_qsel0_bufp1_ca_l[3]),
                 .arbcp3_cpxdp_qsel1_bufp1_ca_1(arbcp3_cpxdp_qsel1_bufp1_ca[3]),
                 .arbcp3_cpxdp_shift_bufp1_cx_l_1(arbcp3_cpxdp_shift_bufp1_cx_l[3]),
                 .arbcp4_cpxdp_grant_bufp1_ca_l_1(arbcp4_cpxdp_grant_bufp1_ca_l[3]),
                 .arbcp4_cpxdp_q0_hold_bufp1_ca_1(arbcp4_cpxdp_q0_hold_bufp1_ca[3]),
                 .arbcp4_cpxdp_qsel0_bufp1_ca_l_1(arbcp4_cpxdp_qsel0_bufp1_ca_l[3]),
                 .arbcp4_cpxdp_qsel1_bufp1_ca_1(arbcp4_cpxdp_qsel1_bufp1_ca[3]),
                 .arbcp4_cpxdp_shift_bufp1_cx_l_1(arbcp4_cpxdp_shift_bufp1_cx_l[3]),
                 .arbcp5_cpxdp_grant_bufp1_ca_l_1(arbcp5_cpxdp_grant_bufp1_ca_l[3]),
                 .arbcp5_cpxdp_q0_hold_bufp1_ca_1(arbcp5_cpxdp_q0_hold_bufp1_ca[3]),
                 .arbcp5_cpxdp_qsel0_bufp1_ca_l_1(arbcp5_cpxdp_qsel0_bufp1_ca_l[3]),
                 .arbcp5_cpxdp_qsel1_bufp1_ca_1(arbcp5_cpxdp_qsel1_bufp1_ca[3]),
                 .arbcp5_cpxdp_shift_bufp1_cx_l_1(arbcp5_cpxdp_shift_bufp1_cx_l[3]),
                 .arbcp6_cpxdp_grant_bufp1_ca_l_1(arbcp6_cpxdp_grant_bufp1_ca_l[3]),
                 .arbcp6_cpxdp_q0_hold_bufp1_ca_1(arbcp6_cpxdp_q0_hold_bufp1_ca[3]),
                 .arbcp6_cpxdp_qsel0_bufp1_ca_l_1(arbcp6_cpxdp_qsel0_bufp1_ca_l[3]),
                 .arbcp6_cpxdp_qsel1_bufp1_ca_1(arbcp6_cpxdp_qsel1_bufp1_ca[3]),
                 .arbcp6_cpxdp_shift_bufp1_cx_l_1(arbcp6_cpxdp_shift_bufp1_cx_l[3]),
                 .arbcp7_cpxdp_grant_bufp1_ca_l_1(arbcp7_cpxdp_grant_bufp1_ca_l[3]),
                 .arbcp7_cpxdp_q0_hold_bufp1_ca_1(arbcp7_cpxdp_q0_hold_bufp1_ca[3]),
                 .arbcp7_cpxdp_qsel0_bufp1_ca_l_1(arbcp7_cpxdp_qsel0_bufp1_ca_l[3]),
                 .arbcp7_cpxdp_qsel1_bufp1_ca_1(arbcp7_cpxdp_qsel1_bufp1_ca[3]),
                 .arbcp7_cpxdp_shift_bufp1_cx_l_1(arbcp7_cpxdp_shift_bufp1_cx_l[3]),
                 // Inputs
                 .arbcp0_cpxdp_grant_arbbf_ca_1(arbcp0_cpxdp_grant_arbbf_ca[3]),
                 .arbcp0_cpxdp_q0_hold_arbbf_ca_l_1(arbcp0_cpxdp_q0_hold_arbbf_ca_l[3]),
                 .arbcp0_cpxdp_qsel0_arbbf_ca_1(arbcp0_cpxdp_qsel0_arbbf_ca[3]),
                 .arbcp0_cpxdp_qsel1_arbbf_ca_l_1(arbcp0_cpxdp_qsel1_arbbf_ca_l[3]),
                 .arbcp0_cpxdp_shift_arbbf_cx_1(arbcp0_cpxdp_shift_arbbf_cx[3]),
                 .arbcp1_cpxdp_grant_arbbf_ca_1(arbcp1_cpxdp_grant_arbbf_ca[3]),
                 .arbcp1_cpxdp_q0_hold_arbbf_ca_l_1(arbcp1_cpxdp_q0_hold_arbbf_ca_l[3]),
                 .arbcp1_cpxdp_qsel0_arbbf_ca_1(arbcp1_cpxdp_qsel0_arbbf_ca[3]),
                 .arbcp1_cpxdp_qsel1_arbbf_ca_l_1(arbcp1_cpxdp_qsel1_arbbf_ca_l[3]),
                 .arbcp1_cpxdp_shift_arbbf_cx_1(arbcp1_cpxdp_shift_arbbf_cx[3]),
                 .arbcp2_cpxdp_grant_arbbf_ca_1(arbcp2_cpxdp_grant_arbbf_ca[3]),
                 .arbcp2_cpxdp_q0_hold_arbbf_ca_l_1(arbcp2_cpxdp_q0_hold_arbbf_ca_l[3]),
                 .arbcp2_cpxdp_qsel0_arbbf_ca_1(arbcp2_cpxdp_qsel0_arbbf_ca[3]),
                 .arbcp2_cpxdp_qsel1_arbbf_ca_l_1(arbcp2_cpxdp_qsel1_arbbf_ca_l[3]),
                 .arbcp2_cpxdp_shift_arbbf_cx_1(arbcp2_cpxdp_shift_arbbf_cx[3]),
                 .arbcp3_cpxdp_grant_arbbf_ca_1(arbcp3_cpxdp_grant_arbbf_ca[3]),
                 .arbcp3_cpxdp_q0_hold_arbbf_ca_l_1(arbcp3_cpxdp_q0_hold_arbbf_ca_l[3]),
                 .arbcp3_cpxdp_qsel0_arbbf_ca_1(arbcp3_cpxdp_qsel0_arbbf_ca[3]),
                 .arbcp3_cpxdp_qsel1_arbbf_ca_l_1(arbcp3_cpxdp_qsel1_arbbf_ca_l[3]),
                 .arbcp3_cpxdp_shift_arbbf_cx_1(arbcp3_cpxdp_shift_arbbf_cx[3]),
                 .arbcp4_cpxdp_grant_arbbf_ca_1(arbcp4_cpxdp_grant_arbbf_ca[3]),
                 .arbcp4_cpxdp_q0_hold_arbbf_ca_l_1(arbcp4_cpxdp_q0_hold_arbbf_ca_l[3]),
                 .arbcp4_cpxdp_qsel0_arbbf_ca_1(arbcp4_cpxdp_qsel0_arbbf_ca[3]),
                 .arbcp4_cpxdp_qsel1_arbbf_ca_l_1(arbcp4_cpxdp_qsel1_arbbf_ca_l[3]),
                 .arbcp4_cpxdp_shift_arbbf_cx_1(arbcp4_cpxdp_shift_arbbf_cx[3]),
                 .arbcp5_cpxdp_grant_arbbf_ca_1(arbcp5_cpxdp_grant_arbbf_ca[3]),
                 .arbcp5_cpxdp_q0_hold_arbbf_ca_l_1(arbcp5_cpxdp_q0_hold_arbbf_ca_l[3]),
                 .arbcp5_cpxdp_qsel0_arbbf_ca_1(arbcp5_cpxdp_qsel0_arbbf_ca[3]),
                 .arbcp5_cpxdp_qsel1_arbbf_ca_l_1(arbcp5_cpxdp_qsel1_arbbf_ca_l[3]),
                 .arbcp5_cpxdp_shift_arbbf_cx_1(arbcp5_cpxdp_shift_arbbf_cx[3]),
                 .arbcp6_cpxdp_grant_arbbf_ca_1(arbcp6_cpxdp_grant_arbbf_ca[3]),
                 .arbcp6_cpxdp_q0_hold_arbbf_ca_l_1(arbcp6_cpxdp_q0_hold_arbbf_ca_l[3]),
                 .arbcp6_cpxdp_qsel0_arbbf_ca_1(arbcp6_cpxdp_qsel0_arbbf_ca[3]),
                 .arbcp6_cpxdp_qsel1_arbbf_ca_l_1(arbcp6_cpxdp_qsel1_arbbf_ca_l[3]),
                 .arbcp6_cpxdp_shift_arbbf_cx_1(arbcp6_cpxdp_shift_arbbf_cx[3]),
                 .arbcp7_cpxdp_grant_arbbf_ca_1(arbcp7_cpxdp_grant_arbbf_ca[3]),
                 .arbcp7_cpxdp_q0_hold_arbbf_ca_l_1(arbcp7_cpxdp_q0_hold_arbbf_ca_l[3]),
                 .arbcp7_cpxdp_qsel0_arbbf_ca_1(arbcp7_cpxdp_qsel0_arbbf_ca[3]),
                 .arbcp7_cpxdp_qsel1_arbbf_ca_l_1(arbcp7_cpxdp_qsel1_arbbf_ca_l[3]),
                 .arbcp7_cpxdp_shift_arbbf_cx_1(arbcp7_cpxdp_shift_arbbf_cx[3]));
*/
   cpx_fpbuf_p1  fpbuf_p1(/*AUTOINST*/
			  // Outputs
			  .fp_cpx_req_bufp1_cq(fp_cpx_req_bufp1_cq[7:0]),
			  .arbcp0_cpxdp_grant_bufp1_ca_l_1(arbcp0_cpxdp_grant_bufp1_ca_l[3]), // Templated
			  .arbcp0_cpxdp_q0_hold_bufp1_ca_1(arbcp0_cpxdp_q0_hold_bufp1_ca[3]), // Templated
			  .arbcp0_cpxdp_qsel0_bufp1_ca_l_1(arbcp0_cpxdp_qsel0_bufp1_ca_l[3]), // Templated
			  .arbcp0_cpxdp_qsel1_bufp1_ca_1(arbcp0_cpxdp_qsel1_bufp1_ca[3]), // Templated
			  .arbcp0_cpxdp_shift_bufp1_cx_l_1(arbcp0_cpxdp_shift_bufp1_cx_l[3]), // Templated
			  .arbcp1_cpxdp_grant_bufp1_ca_l_1(arbcp1_cpxdp_grant_bufp1_ca_l[3]), // Templated
			  .arbcp1_cpxdp_q0_hold_bufp1_ca_1(arbcp1_cpxdp_q0_hold_bufp1_ca[3]), // Templated
			  .arbcp1_cpxdp_qsel0_bufp1_ca_l_1(arbcp1_cpxdp_qsel0_bufp1_ca_l[3]), // Templated
			  .arbcp1_cpxdp_qsel1_bufp1_ca_1(arbcp1_cpxdp_qsel1_bufp1_ca[3]), // Templated
			  .arbcp1_cpxdp_shift_bufp1_cx_l_1(arbcp1_cpxdp_shift_bufp1_cx_l[3]), // Templated
			  .arbcp2_cpxdp_grant_bufp1_ca_l_1(arbcp2_cpxdp_grant_bufp1_ca_l[3]), // Templated
			  .arbcp2_cpxdp_q0_hold_bufp1_ca_1(arbcp2_cpxdp_q0_hold_bufp1_ca[3]), // Templated
			  .arbcp2_cpxdp_qsel0_bufp1_ca_l_1(arbcp2_cpxdp_qsel0_bufp1_ca_l[3]), // Templated
			  .arbcp2_cpxdp_qsel1_bufp1_ca_1(arbcp2_cpxdp_qsel1_bufp1_ca[3]), // Templated
			  .arbcp2_cpxdp_shift_bufp1_cx_l_1(arbcp2_cpxdp_shift_bufp1_cx_l[3]), // Templated
			  .arbcp3_cpxdp_grant_bufp1_ca_l_1(arbcp3_cpxdp_grant_bufp1_ca_l[3]), // Templated
			  .arbcp3_cpxdp_q0_hold_bufp1_ca_1(arbcp3_cpxdp_q0_hold_bufp1_ca[3]), // Templated
			  .arbcp3_cpxdp_qsel0_bufp1_ca_l_1(arbcp3_cpxdp_qsel0_bufp1_ca_l[3]), // Templated
			  .arbcp3_cpxdp_qsel1_bufp1_ca_1(arbcp3_cpxdp_qsel1_bufp1_ca[3]), // Templated
			  .arbcp3_cpxdp_shift_bufp1_cx_l_1(arbcp3_cpxdp_shift_bufp1_cx_l[3]), // Templated
			  .arbcp4_cpxdp_grant_bufp1_ca_l_1(arbcp4_cpxdp_grant_bufp1_ca_l[3]), // Templated
			  .arbcp4_cpxdp_q0_hold_bufp1_ca_1(arbcp4_cpxdp_q0_hold_bufp1_ca[3]), // Templated
			  .arbcp4_cpxdp_qsel0_bufp1_ca_l_1(arbcp4_cpxdp_qsel0_bufp1_ca_l[3]), // Templated
			  .arbcp4_cpxdp_qsel1_bufp1_ca_1(arbcp4_cpxdp_qsel1_bufp1_ca[3]), // Templated
			  .arbcp4_cpxdp_shift_bufp1_cx_l_1(arbcp4_cpxdp_shift_bufp1_cx_l[3]), // Templated
			  .arbcp5_cpxdp_grant_bufp1_ca_l_1(arbcp5_cpxdp_grant_bufp1_ca_l[3]), // Templated
			  .arbcp5_cpxdp_q0_hold_bufp1_ca_1(arbcp5_cpxdp_q0_hold_bufp1_ca[3]), // Templated
			  .arbcp5_cpxdp_qsel0_bufp1_ca_l_1(arbcp5_cpxdp_qsel0_bufp1_ca_l[3]), // Templated
			  .arbcp5_cpxdp_qsel1_bufp1_ca_1(arbcp5_cpxdp_qsel1_bufp1_ca[3]), // Templated
			  .arbcp5_cpxdp_shift_bufp1_cx_l_1(arbcp5_cpxdp_shift_bufp1_cx_l[3]), // Templated
			  .arbcp6_cpxdp_grant_bufp1_ca_l_1(arbcp6_cpxdp_grant_bufp1_ca_l[3]), // Templated
			  .arbcp6_cpxdp_q0_hold_bufp1_ca_1(arbcp6_cpxdp_q0_hold_bufp1_ca[3]), // Templated
			  .arbcp6_cpxdp_qsel0_bufp1_ca_l_1(arbcp6_cpxdp_qsel0_bufp1_ca_l[3]), // Templated
			  .arbcp6_cpxdp_qsel1_bufp1_ca_1(arbcp6_cpxdp_qsel1_bufp1_ca[3]), // Templated
			  .arbcp6_cpxdp_shift_bufp1_cx_l_1(arbcp6_cpxdp_shift_bufp1_cx_l[3]), // Templated
			  .arbcp7_cpxdp_grant_bufp1_ca_l_1(arbcp7_cpxdp_grant_bufp1_ca_l[3]), // Templated
			  .arbcp7_cpxdp_q0_hold_bufp1_ca_1(arbcp7_cpxdp_q0_hold_bufp1_ca[3]), // Templated
			  .arbcp7_cpxdp_qsel0_bufp1_ca_l_1(arbcp7_cpxdp_qsel0_bufp1_ca_l[3]), // Templated
			  .arbcp7_cpxdp_qsel1_bufp1_ca_1(arbcp7_cpxdp_qsel1_bufp1_ca[3]), // Templated
			  .arbcp7_cpxdp_shift_bufp1_cx_l_1(arbcp7_cpxdp_shift_bufp1_cx_l[3]), // Templated
			  // Inputs
			  .fp_cpx_req_bufp0_cq(fp_cpx_req_bufp0_cq[7:0]),
			  .arbcp0_cpxdp_grant_arbbf_ca_1(arbcp0_cpxdp_grant_arbbf_ca[3]), // Templated
			  .arbcp0_cpxdp_q0_hold_arbbf_ca_l_1(arbcp0_cpxdp_q0_hold_arbbf_ca_l[3]), // Templated
			  .arbcp0_cpxdp_qsel0_arbbf_ca_1(arbcp0_cpxdp_qsel0_arbbf_ca[3]), // Templated
			  .arbcp0_cpxdp_qsel1_arbbf_ca_l_1(arbcp0_cpxdp_qsel1_arbbf_ca_l[3]), // Templated
			  .arbcp0_cpxdp_shift_arbbf_cx_1(arbcp0_cpxdp_shift_arbbf_cx[3]), // Templated
			  .arbcp1_cpxdp_grant_arbbf_ca_1(arbcp1_cpxdp_grant_arbbf_ca[3]), // Templated
			  .arbcp1_cpxdp_q0_hold_arbbf_ca_l_1(arbcp1_cpxdp_q0_hold_arbbf_ca_l[3]), // Templated
			  .arbcp1_cpxdp_qsel0_arbbf_ca_1(arbcp1_cpxdp_qsel0_arbbf_ca[3]), // Templated
			  .arbcp1_cpxdp_qsel1_arbbf_ca_l_1(arbcp1_cpxdp_qsel1_arbbf_ca_l[3]), // Templated
			  .arbcp1_cpxdp_shift_arbbf_cx_1(arbcp1_cpxdp_shift_arbbf_cx[3]), // Templated
			  .arbcp2_cpxdp_grant_arbbf_ca_1(arbcp2_cpxdp_grant_arbbf_ca[3]), // Templated
			  .arbcp2_cpxdp_q0_hold_arbbf_ca_l_1(arbcp2_cpxdp_q0_hold_arbbf_ca_l[3]), // Templated
			  .arbcp2_cpxdp_qsel0_arbbf_ca_1(arbcp2_cpxdp_qsel0_arbbf_ca[3]), // Templated
			  .arbcp2_cpxdp_qsel1_arbbf_ca_l_1(arbcp2_cpxdp_qsel1_arbbf_ca_l[3]), // Templated
			  .arbcp2_cpxdp_shift_arbbf_cx_1(arbcp2_cpxdp_shift_arbbf_cx[3]), // Templated
			  .arbcp3_cpxdp_grant_arbbf_ca_1(arbcp3_cpxdp_grant_arbbf_ca[3]), // Templated
			  .arbcp3_cpxdp_q0_hold_arbbf_ca_l_1(arbcp3_cpxdp_q0_hold_arbbf_ca_l[3]), // Templated
			  .arbcp3_cpxdp_qsel0_arbbf_ca_1(arbcp3_cpxdp_qsel0_arbbf_ca[3]), // Templated
			  .arbcp3_cpxdp_qsel1_arbbf_ca_l_1(arbcp3_cpxdp_qsel1_arbbf_ca_l[3]), // Templated
			  .arbcp3_cpxdp_shift_arbbf_cx_1(arbcp3_cpxdp_shift_arbbf_cx[3]), // Templated
			  .arbcp4_cpxdp_grant_arbbf_ca_1(arbcp4_cpxdp_grant_arbbf_ca[3]), // Templated
			  .arbcp4_cpxdp_q0_hold_arbbf_ca_l_1(arbcp4_cpxdp_q0_hold_arbbf_ca_l[3]), // Templated
			  .arbcp4_cpxdp_qsel0_arbbf_ca_1(arbcp4_cpxdp_qsel0_arbbf_ca[3]), // Templated
			  .arbcp4_cpxdp_qsel1_arbbf_ca_l_1(arbcp4_cpxdp_qsel1_arbbf_ca_l[3]), // Templated
			  .arbcp4_cpxdp_shift_arbbf_cx_1(arbcp4_cpxdp_shift_arbbf_cx[3]), // Templated
			  .arbcp5_cpxdp_grant_arbbf_ca_1(arbcp5_cpxdp_grant_arbbf_ca[3]), // Templated
			  .arbcp5_cpxdp_q0_hold_arbbf_ca_l_1(arbcp5_cpxdp_q0_hold_arbbf_ca_l[3]), // Templated
			  .arbcp5_cpxdp_qsel0_arbbf_ca_1(arbcp5_cpxdp_qsel0_arbbf_ca[3]), // Templated
			  .arbcp5_cpxdp_qsel1_arbbf_ca_l_1(arbcp5_cpxdp_qsel1_arbbf_ca_l[3]), // Templated
			  .arbcp5_cpxdp_shift_arbbf_cx_1(arbcp5_cpxdp_shift_arbbf_cx[3]), // Templated
			  .arbcp6_cpxdp_grant_arbbf_ca_1(arbcp6_cpxdp_grant_arbbf_ca[3]), // Templated
			  .arbcp6_cpxdp_q0_hold_arbbf_ca_l_1(arbcp6_cpxdp_q0_hold_arbbf_ca_l[3]), // Templated
			  .arbcp6_cpxdp_qsel0_arbbf_ca_1(arbcp6_cpxdp_qsel0_arbbf_ca[3]), // Templated
			  .arbcp6_cpxdp_qsel1_arbbf_ca_l_1(arbcp6_cpxdp_qsel1_arbbf_ca_l[3]), // Templated
			  .arbcp6_cpxdp_shift_arbbf_cx_1(arbcp6_cpxdp_shift_arbbf_cx[3]), // Templated
			  .arbcp7_cpxdp_grant_arbbf_ca_1(arbcp7_cpxdp_grant_arbbf_ca[3]), // Templated
			  .arbcp7_cpxdp_q0_hold_arbbf_ca_l_1(arbcp7_cpxdp_q0_hold_arbbf_ca_l[3]), // Templated
			  .arbcp7_cpxdp_qsel0_arbbf_ca_1(arbcp7_cpxdp_qsel0_arbbf_ca[3]), // Templated
			  .arbcp7_cpxdp_qsel1_arbbf_ca_l_1(arbcp7_cpxdp_qsel1_arbbf_ca_l[3]), // Templated
			  .arbcp7_cpxdp_shift_arbbf_cx_1(arbcp7_cpxdp_shift_arbbf_cx[3])); // Templated
/* cpx_buf_pdl_even AUTO_TEMPLATE(
			   // Outputs
			   .arbcp0_cpxdp_grant_ca(arbcp0_cpxdp_grant_ca[5]),
			   .arbcp0_cpxdp_q0_hold_ca_l(arbcp0_cpxdp_q0_hold_ca_l[5]),
			   .arbcp0_cpxdp_qsel0_ca(arbcp0_cpxdp_qsel0_ca[5]),
			   .arbcp0_cpxdp_qsel1_ca_l(arbcp0_cpxdp_qsel1_ca_l[5]),
			   .arbcp0_cpxdp_shift_cx(arbcp0_cpxdp_shift_cx[5]),
			   .arbcp2_cpxdp_grant_ca(arbcp2_cpxdp_grant_ca[5]),
			   .arbcp2_cpxdp_q0_hold_ca_l(arbcp2_cpxdp_q0_hold_ca_l[5]),
			   .arbcp2_cpxdp_qsel0_ca(arbcp2_cpxdp_qsel0_ca[5]),
			   .arbcp2_cpxdp_qsel1_ca_l(arbcp2_cpxdp_qsel1_ca_l[5]),
			   .arbcp2_cpxdp_shift_cx(arbcp2_cpxdp_shift_cx[5]),
			   .arbcp4_cpxdp_grant_ca(arbcp4_cpxdp_grant_ca[5]),
			   .arbcp4_cpxdp_q0_hold_ca_l(arbcp4_cpxdp_q0_hold_ca_l[5]),
			   .arbcp4_cpxdp_qsel0_ca(arbcp4_cpxdp_qsel0_ca[5]),
			   .arbcp4_cpxdp_qsel1_ca_l(arbcp4_cpxdp_qsel1_ca_l[5]),
			   .arbcp4_cpxdp_shift_cx(arbcp4_cpxdp_shift_cx[5]),
			   .arbcp6_cpxdp_grant_ca(arbcp6_cpxdp_grant_ca[5]),
			   .arbcp6_cpxdp_q0_hold_ca_l(arbcp6_cpxdp_q0_hold_ca_l[5]),
			   .arbcp6_cpxdp_qsel0_ca(arbcp6_cpxdp_qsel0_ca[5]),
			   .arbcp6_cpxdp_qsel1_ca_l(arbcp6_cpxdp_qsel1_ca_l[5]),
			   .arbcp6_cpxdp_shift_cx(arbcp6_cpxdp_shift_cx[5]),
			   // Inputs
			   .arbcp0_cpxdp_grant_bufp1_ca_l(arbcp0_cpxdp_grant_bufp3_ca_l[5]),
			   .arbcp0_cpxdp_q0_hold_bufp1_ca(arbcp0_cpxdp_q0_hold_bufp3_ca[5]),
			   .arbcp0_cpxdp_qsel0_bufp1_ca_l(arbcp0_cpxdp_qsel0_bufp3_ca_l[5]),
			   .arbcp0_cpxdp_qsel1_bufp1_ca(arbcp0_cpxdp_qsel1_bufp3_ca[5]),
			   .arbcp0_cpxdp_shift_bufp1_cx_l(arbcp0_cpxdp_shift_bufp3_cx_l[5]),
			   .arbcp2_cpxdp_grant_bufp1_ca_l(arbcp2_cpxdp_grant_bufp3_ca_l[5]),
			   .arbcp2_cpxdp_q0_hold_bufp1_ca(arbcp2_cpxdp_q0_hold_bufp3_ca[5]),
			   .arbcp2_cpxdp_qsel0_bufp1_ca_l(arbcp2_cpxdp_qsel0_bufp3_ca_l[5]),
			   .arbcp2_cpxdp_qsel1_bufp1_ca(arbcp2_cpxdp_qsel1_bufp3_ca[5]),
			   .arbcp2_cpxdp_shift_bufp1_cx_l(arbcp2_cpxdp_shift_bufp3_cx_l[5]),
			   .arbcp4_cpxdp_grant_bufp1_ca_l(arbcp4_cpxdp_grant_bufp3_ca_l[5]),
			   .arbcp4_cpxdp_q0_hold_bufp1_ca(arbcp4_cpxdp_q0_hold_bufp3_ca[5]),
			   .arbcp4_cpxdp_qsel0_bufp1_ca_l(arbcp4_cpxdp_qsel0_bufp3_ca_l[5]),
			   .arbcp4_cpxdp_qsel1_bufp1_ca(arbcp4_cpxdp_qsel1_bufp3_ca[5]),
			   .arbcp4_cpxdp_shift_bufp1_cx_l(arbcp4_cpxdp_shift_bufp3_cx_l[5]),
			   .arbcp6_cpxdp_grant_bufp1_ca_l(arbcp6_cpxdp_grant_bufp3_ca_l[5]),
			   .arbcp6_cpxdp_q0_hold_bufp1_ca(arbcp6_cpxdp_q0_hold_bufp3_ca[5]),
			   .arbcp6_cpxdp_qsel0_bufp1_ca_l(arbcp6_cpxdp_qsel0_bufp3_ca_l[5]),
			   .arbcp6_cpxdp_qsel1_bufp1_ca(arbcp6_cpxdp_qsel1_bufp3_ca[5]),
			   .arbcp6_cpxdp_shift_bufp1_cx_l(arbcp6_cpxdp_shift_bufp3_cx_l[5]));
  */
   cpx_buf_pdl_even pdl_even(/*AUTOINST*/
			     // Outputs
			     .arbcp0_cpxdp_grant_ca(arbcp0_cpxdp_grant_ca[5]), // Templated
			     .arbcp0_cpxdp_q0_hold_ca_l(arbcp0_cpxdp_q0_hold_ca_l[5]), // Templated
			     .arbcp0_cpxdp_qsel0_ca(arbcp0_cpxdp_qsel0_ca[5]), // Templated
			     .arbcp0_cpxdp_qsel1_ca_l(arbcp0_cpxdp_qsel1_ca_l[5]), // Templated
			     .arbcp0_cpxdp_shift_cx(arbcp0_cpxdp_shift_cx[5]), // Templated
			     .arbcp2_cpxdp_grant_ca(arbcp2_cpxdp_grant_ca[5]), // Templated
			     .arbcp2_cpxdp_q0_hold_ca_l(arbcp2_cpxdp_q0_hold_ca_l[5]), // Templated
			     .arbcp2_cpxdp_qsel0_ca(arbcp2_cpxdp_qsel0_ca[5]), // Templated
			     .arbcp2_cpxdp_qsel1_ca_l(arbcp2_cpxdp_qsel1_ca_l[5]), // Templated
			     .arbcp2_cpxdp_shift_cx(arbcp2_cpxdp_shift_cx[5]), // Templated
			     .arbcp4_cpxdp_grant_ca(arbcp4_cpxdp_grant_ca[5]), // Templated
			     .arbcp4_cpxdp_q0_hold_ca_l(arbcp4_cpxdp_q0_hold_ca_l[5]), // Templated
			     .arbcp4_cpxdp_qsel0_ca(arbcp4_cpxdp_qsel0_ca[5]), // Templated
			     .arbcp4_cpxdp_qsel1_ca_l(arbcp4_cpxdp_qsel1_ca_l[5]), // Templated
			     .arbcp4_cpxdp_shift_cx(arbcp4_cpxdp_shift_cx[5]), // Templated
			     .arbcp6_cpxdp_grant_ca(arbcp6_cpxdp_grant_ca[5]), // Templated
			     .arbcp6_cpxdp_q0_hold_ca_l(arbcp6_cpxdp_q0_hold_ca_l[5]), // Templated
			     .arbcp6_cpxdp_qsel0_ca(arbcp6_cpxdp_qsel0_ca[5]), // Templated
			     .arbcp6_cpxdp_qsel1_ca_l(arbcp6_cpxdp_qsel1_ca_l[5]), // Templated
			     .arbcp6_cpxdp_shift_cx(arbcp6_cpxdp_shift_cx[5]), // Templated
			     // Inputs
			     .arbcp0_cpxdp_grant_bufp1_ca_l(arbcp0_cpxdp_grant_bufp3_ca_l[5]), // Templated
			     .arbcp0_cpxdp_q0_hold_bufp1_ca(arbcp0_cpxdp_q0_hold_bufp3_ca[5]), // Templated
			     .arbcp0_cpxdp_qsel0_bufp1_ca_l(arbcp0_cpxdp_qsel0_bufp3_ca_l[5]), // Templated
			     .arbcp0_cpxdp_qsel1_bufp1_ca(arbcp0_cpxdp_qsel1_bufp3_ca[5]), // Templated
			     .arbcp0_cpxdp_shift_bufp1_cx_l(arbcp0_cpxdp_shift_bufp3_cx_l[5]), // Templated
			     .arbcp2_cpxdp_grant_bufp1_ca_l(arbcp2_cpxdp_grant_bufp3_ca_l[5]), // Templated
			     .arbcp2_cpxdp_q0_hold_bufp1_ca(arbcp2_cpxdp_q0_hold_bufp3_ca[5]), // Templated
			     .arbcp2_cpxdp_qsel0_bufp1_ca_l(arbcp2_cpxdp_qsel0_bufp3_ca_l[5]), // Templated
			     .arbcp2_cpxdp_qsel1_bufp1_ca(arbcp2_cpxdp_qsel1_bufp3_ca[5]), // Templated
			     .arbcp2_cpxdp_shift_bufp1_cx_l(arbcp2_cpxdp_shift_bufp3_cx_l[5]), // Templated
			     .arbcp4_cpxdp_grant_bufp1_ca_l(arbcp4_cpxdp_grant_bufp3_ca_l[5]), // Templated
			     .arbcp4_cpxdp_q0_hold_bufp1_ca(arbcp4_cpxdp_q0_hold_bufp3_ca[5]), // Templated
			     .arbcp4_cpxdp_qsel0_bufp1_ca_l(arbcp4_cpxdp_qsel0_bufp3_ca_l[5]), // Templated
			     .arbcp4_cpxdp_qsel1_bufp1_ca(arbcp4_cpxdp_qsel1_bufp3_ca[5]), // Templated
			     .arbcp4_cpxdp_shift_bufp1_cx_l(arbcp4_cpxdp_shift_bufp3_cx_l[5]), // Templated
			     .arbcp6_cpxdp_grant_bufp1_ca_l(arbcp6_cpxdp_grant_bufp3_ca_l[5]), // Templated
			     .arbcp6_cpxdp_q0_hold_bufp1_ca(arbcp6_cpxdp_q0_hold_bufp3_ca[5]), // Templated
			     .arbcp6_cpxdp_qsel0_bufp1_ca_l(arbcp6_cpxdp_qsel0_bufp3_ca_l[5]), // Templated
			     .arbcp6_cpxdp_qsel1_bufp1_ca(arbcp6_cpxdp_qsel1_bufp3_ca[5]), // Templated
			     .arbcp6_cpxdp_shift_bufp1_cx_l(arbcp6_cpxdp_shift_bufp3_cx_l[5])); // Templated
/* cpx_buf_pdl_even AUTO_TEMPLATE(
			   // Outputs
			   .arbcp0_cpxdp_grant_ca(arbcp1_cpxdp_grant_ca[5]),
			   .arbcp0_cpxdp_q0_hold_ca_l(arbcp1_cpxdp_q0_hold_ca_l[5]),
			   .arbcp0_cpxdp_qsel0_ca(arbcp1_cpxdp_qsel0_ca[5]),
			   .arbcp0_cpxdp_qsel1_ca_l(arbcp1_cpxdp_qsel1_ca_l[5]),
			   .arbcp0_cpxdp_shift_cx(arbcp1_cpxdp_shift_cx[5]),
			   .arbcp2_cpxdp_grant_ca(arbcp3_cpxdp_grant_ca[5]),
			   .arbcp2_cpxdp_q0_hold_ca_l(arbcp3_cpxdp_q0_hold_ca_l[5]),
			   .arbcp2_cpxdp_qsel0_ca(arbcp3_cpxdp_qsel0_ca[5]),
			   .arbcp2_cpxdp_qsel1_ca_l(arbcp3_cpxdp_qsel1_ca_l[5]),
			   .arbcp2_cpxdp_shift_cx(arbcp3_cpxdp_shift_cx[5]),
			   .arbcp4_cpxdp_grant_ca(arbcp5_cpxdp_grant_ca[5]),
			   .arbcp4_cpxdp_q0_hold_ca_l(arbcp5_cpxdp_q0_hold_ca_l[5]),
			   .arbcp4_cpxdp_qsel0_ca(arbcp5_cpxdp_qsel0_ca[5]),
			   .arbcp4_cpxdp_qsel1_ca_l(arbcp5_cpxdp_qsel1_ca_l[5]),
			   .arbcp4_cpxdp_shift_cx(arbcp5_cpxdp_shift_cx[5]),
			   .arbcp6_cpxdp_grant_ca(arbcp7_cpxdp_grant_ca[5]),
			   .arbcp6_cpxdp_q0_hold_ca_l(arbcp7_cpxdp_q0_hold_ca_l[5]),
			   .arbcp6_cpxdp_qsel0_ca(arbcp7_cpxdp_qsel0_ca[5]),
			   .arbcp6_cpxdp_qsel1_ca_l(arbcp7_cpxdp_qsel1_ca_l[5]),
			   .arbcp6_cpxdp_shift_cx(arbcp7_cpxdp_shift_cx[5]),
			   // Inputs
			   .arbcp0_cpxdp_grant_bufp1_ca_l(arbcp1_cpxdp_grant_bufp3_ca_l[5]),
			   .arbcp0_cpxdp_q0_hold_bufp1_ca(arbcp1_cpxdp_q0_hold_bufp3_ca[5]),
			   .arbcp0_cpxdp_qsel0_bufp1_ca_l(arbcp1_cpxdp_qsel0_bufp3_ca_l[5]),
			   .arbcp0_cpxdp_qsel1_bufp1_ca(arbcp1_cpxdp_qsel1_bufp3_ca[5]),
			   .arbcp0_cpxdp_shift_bufp1_cx_l(arbcp1_cpxdp_shift_bufp3_cx_l[5]),
			   .arbcp2_cpxdp_grant_bufp1_ca_l(arbcp3_cpxdp_grant_bufp3_ca_l[5]),
			   .arbcp2_cpxdp_q0_hold_bufp1_ca(arbcp3_cpxdp_q0_hold_bufp3_ca[5]),
			   .arbcp2_cpxdp_qsel0_bufp1_ca_l(arbcp3_cpxdp_qsel0_bufp3_ca_l[5]),
			   .arbcp2_cpxdp_qsel1_bufp1_ca(arbcp3_cpxdp_qsel1_bufp3_ca[5]),
			   .arbcp2_cpxdp_shift_bufp1_cx_l(arbcp3_cpxdp_shift_bufp3_cx_l[5]),
			   .arbcp4_cpxdp_grant_bufp1_ca_l(arbcp5_cpxdp_grant_bufp3_ca_l[5]),
			   .arbcp4_cpxdp_q0_hold_bufp1_ca(arbcp5_cpxdp_q0_hold_bufp3_ca[5]),
			   .arbcp4_cpxdp_qsel0_bufp1_ca_l(arbcp5_cpxdp_qsel0_bufp3_ca_l[5]),
			   .arbcp4_cpxdp_qsel1_bufp1_ca(arbcp5_cpxdp_qsel1_bufp3_ca[5]),
			   .arbcp4_cpxdp_shift_bufp1_cx_l(arbcp5_cpxdp_shift_bufp3_cx_l[5]),
			   .arbcp6_cpxdp_grant_bufp1_ca_l(arbcp7_cpxdp_grant_bufp3_ca_l[5]),
			   .arbcp6_cpxdp_q0_hold_bufp1_ca(arbcp7_cpxdp_q0_hold_bufp3_ca[5]),
			   .arbcp6_cpxdp_qsel0_bufp1_ca_l(arbcp7_cpxdp_qsel0_bufp3_ca_l[5]),
			   .arbcp6_cpxdp_qsel1_bufp1_ca(arbcp7_cpxdp_qsel1_bufp3_ca[5]),
			   .arbcp6_cpxdp_shift_bufp1_cx_l(arbcp7_cpxdp_shift_bufp3_cx_l[5]));
   
 */
   cpx_buf_pdl_even pdl_odd(/*AUTOINST*/
			    // Outputs
			    .arbcp0_cpxdp_grant_ca(arbcp1_cpxdp_grant_ca[5]), // Templated
			    .arbcp0_cpxdp_q0_hold_ca_l(arbcp1_cpxdp_q0_hold_ca_l[5]), // Templated
			    .arbcp0_cpxdp_qsel0_ca(arbcp1_cpxdp_qsel0_ca[5]), // Templated
			    .arbcp0_cpxdp_qsel1_ca_l(arbcp1_cpxdp_qsel1_ca_l[5]), // Templated
			    .arbcp0_cpxdp_shift_cx(arbcp1_cpxdp_shift_cx[5]), // Templated
			    .arbcp2_cpxdp_grant_ca(arbcp3_cpxdp_grant_ca[5]), // Templated
			    .arbcp2_cpxdp_q0_hold_ca_l(arbcp3_cpxdp_q0_hold_ca_l[5]), // Templated
			    .arbcp2_cpxdp_qsel0_ca(arbcp3_cpxdp_qsel0_ca[5]), // Templated
			    .arbcp2_cpxdp_qsel1_ca_l(arbcp3_cpxdp_qsel1_ca_l[5]), // Templated
			    .arbcp2_cpxdp_shift_cx(arbcp3_cpxdp_shift_cx[5]), // Templated
			    .arbcp4_cpxdp_grant_ca(arbcp5_cpxdp_grant_ca[5]), // Templated
			    .arbcp4_cpxdp_q0_hold_ca_l(arbcp5_cpxdp_q0_hold_ca_l[5]), // Templated
			    .arbcp4_cpxdp_qsel0_ca(arbcp5_cpxdp_qsel0_ca[5]), // Templated
			    .arbcp4_cpxdp_qsel1_ca_l(arbcp5_cpxdp_qsel1_ca_l[5]), // Templated
			    .arbcp4_cpxdp_shift_cx(arbcp5_cpxdp_shift_cx[5]), // Templated
			    .arbcp6_cpxdp_grant_ca(arbcp7_cpxdp_grant_ca[5]), // Templated
			    .arbcp6_cpxdp_q0_hold_ca_l(arbcp7_cpxdp_q0_hold_ca_l[5]), // Templated
			    .arbcp6_cpxdp_qsel0_ca(arbcp7_cpxdp_qsel0_ca[5]), // Templated
			    .arbcp6_cpxdp_qsel1_ca_l(arbcp7_cpxdp_qsel1_ca_l[5]), // Templated
			    .arbcp6_cpxdp_shift_cx(arbcp7_cpxdp_shift_cx[5]), // Templated
			    // Inputs
			    .arbcp0_cpxdp_grant_bufp1_ca_l(arbcp1_cpxdp_grant_bufp3_ca_l[5]), // Templated
			    .arbcp0_cpxdp_q0_hold_bufp1_ca(arbcp1_cpxdp_q0_hold_bufp3_ca[5]), // Templated
			    .arbcp0_cpxdp_qsel0_bufp1_ca_l(arbcp1_cpxdp_qsel0_bufp3_ca_l[5]), // Templated
			    .arbcp0_cpxdp_qsel1_bufp1_ca(arbcp1_cpxdp_qsel1_bufp3_ca[5]), // Templated
			    .arbcp0_cpxdp_shift_bufp1_cx_l(arbcp1_cpxdp_shift_bufp3_cx_l[5]), // Templated
			    .arbcp2_cpxdp_grant_bufp1_ca_l(arbcp3_cpxdp_grant_bufp3_ca_l[5]), // Templated
			    .arbcp2_cpxdp_q0_hold_bufp1_ca(arbcp3_cpxdp_q0_hold_bufp3_ca[5]), // Templated
			    .arbcp2_cpxdp_qsel0_bufp1_ca_l(arbcp3_cpxdp_qsel0_bufp3_ca_l[5]), // Templated
			    .arbcp2_cpxdp_qsel1_bufp1_ca(arbcp3_cpxdp_qsel1_bufp3_ca[5]), // Templated
			    .arbcp2_cpxdp_shift_bufp1_cx_l(arbcp3_cpxdp_shift_bufp3_cx_l[5]), // Templated
			    .arbcp4_cpxdp_grant_bufp1_ca_l(arbcp5_cpxdp_grant_bufp3_ca_l[5]), // Templated
			    .arbcp4_cpxdp_q0_hold_bufp1_ca(arbcp5_cpxdp_q0_hold_bufp3_ca[5]), // Templated
			    .arbcp4_cpxdp_qsel0_bufp1_ca_l(arbcp5_cpxdp_qsel0_bufp3_ca_l[5]), // Templated
			    .arbcp4_cpxdp_qsel1_bufp1_ca(arbcp5_cpxdp_qsel1_bufp3_ca[5]), // Templated
			    .arbcp4_cpxdp_shift_bufp1_cx_l(arbcp5_cpxdp_shift_bufp3_cx_l[5]), // Templated
			    .arbcp6_cpxdp_grant_bufp1_ca_l(arbcp7_cpxdp_grant_bufp3_ca_l[5]), // Templated
			    .arbcp6_cpxdp_q0_hold_bufp1_ca(arbcp7_cpxdp_q0_hold_bufp3_ca[5]), // Templated
			    .arbcp6_cpxdp_qsel0_bufp1_ca_l(arbcp7_cpxdp_qsel0_bufp3_ca_l[5]), // Templated
			    .arbcp6_cpxdp_qsel1_bufp1_ca(arbcp7_cpxdp_qsel1_bufp3_ca[5]), // Templated
			    .arbcp6_cpxdp_shift_bufp1_cx_l(arbcp7_cpxdp_shift_bufp3_cx_l[5])); // Templated
/* cpx_buf_p3 AUTO_TEMPLATE(
              //Outputs
              .arbcp0_cpxdp_grant_bufp3_ca_l_5(arbcp0_cpxdp_grant_bufp3_ca_l[5]),
              .arbcp0_cpxdp_q0_hold_bufp3_ca_5(arbcp0_cpxdp_q0_hold_bufp3_ca[5]),
              .arbcp0_cpxdp_qsel0_bufp3_ca_l_5(arbcp0_cpxdp_qsel0_bufp3_ca_l[5]),
              .arbcp0_cpxdp_qsel1_bufp3_ca_5(arbcp0_cpxdp_qsel1_bufp3_ca[5]),
              .arbcp0_cpxdp_shift_bufp3_cx_l_5(arbcp0_cpxdp_shift_bufp3_cx_l[5]),
              .arbcp1_cpxdp_grant_bufp3_ca_l_5(arbcp1_cpxdp_grant_bufp3_ca_l[5]),
              .arbcp1_cpxdp_q0_hold_bufp3_ca_5(arbcp1_cpxdp_q0_hold_bufp3_ca[5]),
              .arbcp1_cpxdp_qsel0_bufp3_ca_l_5(arbcp1_cpxdp_qsel0_bufp3_ca_l[5]),
              .arbcp1_cpxdp_qsel1_bufp3_ca_5(arbcp1_cpxdp_qsel1_bufp3_ca[5]),
              .arbcp1_cpxdp_shift_bufp3_cx_l_5(arbcp1_cpxdp_shift_bufp3_cx_l[5]),
              .arbcp2_cpxdp_grant_bufp3_ca_l_5(arbcp2_cpxdp_grant_bufp3_ca_l[5]),
              .arbcp2_cpxdp_q0_hold_bufp3_ca_5(arbcp2_cpxdp_q0_hold_bufp3_ca[5]),
              .arbcp2_cpxdp_qsel0_bufp3_ca_l_5(arbcp2_cpxdp_qsel0_bufp3_ca_l[5]),
              .arbcp2_cpxdp_qsel1_bufp3_ca_5(arbcp2_cpxdp_qsel1_bufp3_ca[5]),
              .arbcp2_cpxdp_shift_bufp3_cx_l_5(arbcp2_cpxdp_shift_bufp3_cx_l[5]),
              .arbcp3_cpxdp_grant_bufp3_ca_l_5(arbcp3_cpxdp_grant_bufp3_ca_l[5]),
              .arbcp3_cpxdp_q0_hold_bufp3_ca_5(arbcp3_cpxdp_q0_hold_bufp3_ca[5]),
              .arbcp3_cpxdp_qsel0_bufp3_ca_l_5(arbcp3_cpxdp_qsel0_bufp3_ca_l[5]),
              .arbcp3_cpxdp_qsel1_bufp3_ca_5(arbcp3_cpxdp_qsel1_bufp3_ca[5]),
              .arbcp3_cpxdp_shift_bufp3_cx_l_5(arbcp3_cpxdp_shift_bufp3_cx_l[5]),
              .arbcp4_cpxdp_grant_bufp3_ca_l_5(arbcp4_cpxdp_grant_bufp3_ca_l[5]),
              .arbcp4_cpxdp_q0_hold_bufp3_ca_5(arbcp4_cpxdp_q0_hold_bufp3_ca[5]),
              .arbcp4_cpxdp_qsel0_bufp3_ca_l_5(arbcp4_cpxdp_qsel0_bufp3_ca_l[5]),
              .arbcp4_cpxdp_qsel1_bufp3_ca_5(arbcp4_cpxdp_qsel1_bufp3_ca[5]),
              .arbcp4_cpxdp_shift_bufp3_cx_l_5(arbcp4_cpxdp_shift_bufp3_cx_l[5]),
              .arbcp5_cpxdp_grant_bufp3_ca_l_5(arbcp5_cpxdp_grant_bufp3_ca_l[5]),
              .arbcp5_cpxdp_q0_hold_bufp3_ca_5(arbcp5_cpxdp_q0_hold_bufp3_ca[5]),
              .arbcp5_cpxdp_qsel0_bufp3_ca_l_5(arbcp5_cpxdp_qsel0_bufp3_ca_l[5]),
              .arbcp5_cpxdp_qsel1_bufp3_ca_5(arbcp5_cpxdp_qsel1_bufp3_ca[5]),
              .arbcp5_cpxdp_shift_bufp3_cx_l_5(arbcp5_cpxdp_shift_bufp3_cx_l[5]),
              .arbcp6_cpxdp_grant_bufp3_ca_l_5(arbcp6_cpxdp_grant_bufp3_ca_l[5]),
              .arbcp6_cpxdp_q0_hold_bufp3_ca_5(arbcp6_cpxdp_q0_hold_bufp3_ca[5]),
              .arbcp6_cpxdp_qsel0_bufp3_ca_l_5(arbcp6_cpxdp_qsel0_bufp3_ca_l[5]),
              .arbcp6_cpxdp_qsel1_bufp3_ca_5(arbcp6_cpxdp_qsel1_bufp3_ca[5]),
              .arbcp6_cpxdp_shift_bufp3_cx_l_5(arbcp6_cpxdp_shift_bufp3_cx_l[5]),
              .arbcp7_cpxdp_grant_bufp3_ca_l_5(arbcp7_cpxdp_grant_bufp3_ca_l[5]),
              .arbcp7_cpxdp_q0_hold_bufp3_ca_5(arbcp7_cpxdp_q0_hold_bufp3_ca[5]),
              .arbcp7_cpxdp_qsel0_bufp3_ca_l_5(arbcp7_cpxdp_qsel0_bufp3_ca_l[5]),
              .arbcp7_cpxdp_qsel1_bufp3_ca_5(arbcp7_cpxdp_qsel1_bufp3_ca[5]),
              .arbcp7_cpxdp_shift_bufp3_cx_l_5(arbcp7_cpxdp_shift_bufp3_cx_l[5]),
              .arbcp0_cpxdp_grant_bufp3_ca_l_2(arbcp0_cpxdp_grant_bufp3_ca_l[2]),
              .arbcp0_cpxdp_q0_hold_bufp3_ca_2(arbcp0_cpxdp_q0_hold_bufp3_ca[2]),
              .arbcp0_cpxdp_qsel0_bufp3_ca_l_2(arbcp0_cpxdp_qsel0_bufp3_ca_l[2]),
              .arbcp0_cpxdp_qsel1_bufp3_ca_2(arbcp0_cpxdp_qsel1_bufp3_ca[2]),
              .arbcp0_cpxdp_shift_bufp3_cx_l_2(arbcp0_cpxdp_shift_bufp3_cx_l[2]),
              .arbcp1_cpxdp_grant_bufp3_ca_l_2(arbcp1_cpxdp_grant_bufp3_ca_l[2]),
              .arbcp1_cpxdp_q0_hold_bufp3_ca_2(arbcp1_cpxdp_q0_hold_bufp3_ca[2]),
              .arbcp1_cpxdp_qsel0_bufp3_ca_l_2(arbcp1_cpxdp_qsel0_bufp3_ca_l[2]),
              .arbcp1_cpxdp_qsel1_bufp3_ca_2(arbcp1_cpxdp_qsel1_bufp3_ca[2]),
              .arbcp1_cpxdp_shift_bufp3_cx_l_2(arbcp1_cpxdp_shift_bufp3_cx_l[2]),
              .arbcp2_cpxdp_grant_bufp3_ca_l_2(arbcp2_cpxdp_grant_bufp3_ca_l[2]),
              .arbcp2_cpxdp_q0_hold_bufp3_ca_2(arbcp2_cpxdp_q0_hold_bufp3_ca[2]),
              .arbcp2_cpxdp_qsel0_bufp3_ca_l_2(arbcp2_cpxdp_qsel0_bufp3_ca_l[2]),
              .arbcp2_cpxdp_qsel1_bufp3_ca_2(arbcp2_cpxdp_qsel1_bufp3_ca[2]),
              .arbcp2_cpxdp_shift_bufp3_cx_l_2(arbcp2_cpxdp_shift_bufp3_cx_l[2]),
              .arbcp3_cpxdp_grant_bufp3_ca_l_2(arbcp3_cpxdp_grant_bufp3_ca_l[2]),
              .arbcp3_cpxdp_q0_hold_bufp3_ca_2(arbcp3_cpxdp_q0_hold_bufp3_ca[2]),
              .arbcp3_cpxdp_qsel0_bufp3_ca_l_2(arbcp3_cpxdp_qsel0_bufp3_ca_l[2]),
              .arbcp3_cpxdp_qsel1_bufp3_ca_2(arbcp3_cpxdp_qsel1_bufp3_ca[2]),
              .arbcp3_cpxdp_shift_bufp3_cx_l_2(arbcp3_cpxdp_shift_bufp3_cx_l[2]),
              .arbcp4_cpxdp_grant_bufp3_ca_l_2(arbcp4_cpxdp_grant_bufp3_ca_l[2]),
              .arbcp4_cpxdp_q0_hold_bufp3_ca_2(arbcp4_cpxdp_q0_hold_bufp3_ca[2]),
              .arbcp4_cpxdp_qsel0_bufp3_ca_l_2(arbcp4_cpxdp_qsel0_bufp3_ca_l[2]),
              .arbcp4_cpxdp_qsel1_bufp3_ca_2(arbcp4_cpxdp_qsel1_bufp3_ca[2]),
              .arbcp4_cpxdp_shift_bufp3_cx_l_2(arbcp4_cpxdp_shift_bufp3_cx_l[2]),
              .arbcp5_cpxdp_grant_bufp3_ca_l_2(arbcp5_cpxdp_grant_bufp3_ca_l[2]),
              .arbcp5_cpxdp_q0_hold_bufp3_ca_2(arbcp5_cpxdp_q0_hold_bufp3_ca[2]),
              .arbcp5_cpxdp_qsel0_bufp3_ca_l_2(arbcp5_cpxdp_qsel0_bufp3_ca_l[2]),
              .arbcp5_cpxdp_qsel1_bufp3_ca_2(arbcp5_cpxdp_qsel1_bufp3_ca[2]),
              .arbcp5_cpxdp_shift_bufp3_cx_l_2(arbcp5_cpxdp_shift_bufp3_cx_l[2]),
              .arbcp6_cpxdp_grant_bufp3_ca_l_2(arbcp6_cpxdp_grant_bufp3_ca_l[2]),
              .arbcp6_cpxdp_q0_hold_bufp3_ca_2(arbcp6_cpxdp_q0_hold_bufp3_ca[2]),
              .arbcp6_cpxdp_qsel0_bufp3_ca_l_2(arbcp6_cpxdp_qsel0_bufp3_ca_l[2]),
              .arbcp6_cpxdp_qsel1_bufp3_ca_2(arbcp6_cpxdp_qsel1_bufp3_ca[2]),
              .arbcp6_cpxdp_shift_bufp3_cx_l_2(arbcp6_cpxdp_shift_bufp3_cx_l[2]),
              .arbcp7_cpxdp_grant_bufp3_ca_l_2(arbcp7_cpxdp_grant_bufp3_ca_l[2]),
              .arbcp7_cpxdp_q0_hold_bufp3_ca_2(arbcp7_cpxdp_q0_hold_bufp3_ca[2]),
              .arbcp7_cpxdp_qsel0_bufp3_ca_l_2(arbcp7_cpxdp_qsel0_bufp3_ca_l[2]),
              .arbcp7_cpxdp_qsel1_bufp3_ca_2(arbcp7_cpxdp_qsel1_bufp3_ca[2]),
              .arbcp7_cpxdp_shift_bufp3_cx_l_2(arbcp7_cpxdp_shift_bufp3_cx_l[2]),
              //Inputs
              .arbcp0_cpxdp_grant_arbbf_ca_5(arbcp0_cpxdp_grant_arbbf_ca[5]),
              .arbcp0_cpxdp_q0_hold_arbbf_ca_l_5(arbcp0_cpxdp_q0_hold_arbbf_ca_l[5]),
              .arbcp0_cpxdp_qsel0_arbbf_ca_5(arbcp0_cpxdp_qsel0_arbbf_ca[5]),
              .arbcp0_cpxdp_qsel1_arbbf_ca_l_5(arbcp0_cpxdp_qsel1_arbbf_ca_l[5]),
              .arbcp0_cpxdp_shift_arbbf_cx_5(arbcp0_cpxdp_shift_arbbf_cx[5]),
              .arbcp1_cpxdp_grant_arbbf_ca_5(arbcp1_cpxdp_grant_arbbf_ca[5]),
              .arbcp1_cpxdp_q0_hold_arbbf_ca_l_5(arbcp1_cpxdp_q0_hold_arbbf_ca_l[5]),
              .arbcp1_cpxdp_qsel0_arbbf_ca_5(arbcp1_cpxdp_qsel0_arbbf_ca[5]),
              .arbcp1_cpxdp_qsel1_arbbf_ca_l_5(arbcp1_cpxdp_qsel1_arbbf_ca_l[5]),
              .arbcp1_cpxdp_shift_arbbf_cx_5(arbcp1_cpxdp_shift_arbbf_cx[5]),
              .arbcp2_cpxdp_grant_arbbf_ca_5(arbcp2_cpxdp_grant_arbbf_ca[5]),
              .arbcp2_cpxdp_q0_hold_arbbf_ca_l_5(arbcp2_cpxdp_q0_hold_arbbf_ca_l[5]),
              .arbcp2_cpxdp_qsel0_arbbf_ca_5(arbcp2_cpxdp_qsel0_arbbf_ca[5]),
              .arbcp2_cpxdp_qsel1_arbbf_ca_l_5(arbcp2_cpxdp_qsel1_arbbf_ca_l[5]),
              .arbcp2_cpxdp_shift_arbbf_cx_5(arbcp2_cpxdp_shift_arbbf_cx[5]),
              .arbcp3_cpxdp_grant_arbbf_ca_5(arbcp3_cpxdp_grant_arbbf_ca[5]),
              .arbcp3_cpxdp_q0_hold_arbbf_ca_l_5(arbcp3_cpxdp_q0_hold_arbbf_ca_l[5]),
              .arbcp3_cpxdp_qsel0_arbbf_ca_5(arbcp3_cpxdp_qsel0_arbbf_ca[5]),
              .arbcp3_cpxdp_qsel1_arbbf_ca_l_5(arbcp3_cpxdp_qsel1_arbbf_ca_l[5]),
              .arbcp3_cpxdp_shift_arbbf_cx_5(arbcp3_cpxdp_shift_arbbf_cx[5]),
              .arbcp4_cpxdp_grant_arbbf_ca_5(arbcp4_cpxdp_grant_arbbf_ca[5]),
              .arbcp4_cpxdp_q0_hold_arbbf_ca_l_5(arbcp4_cpxdp_q0_hold_arbbf_ca_l[5]),
              .arbcp4_cpxdp_qsel0_arbbf_ca_5(arbcp4_cpxdp_qsel0_arbbf_ca[5]),
              .arbcp4_cpxdp_qsel1_arbbf_ca_l_5(arbcp4_cpxdp_qsel1_arbbf_ca_l[5]),
              .arbcp4_cpxdp_shift_arbbf_cx_5(arbcp4_cpxdp_shift_arbbf_cx[5]),
              .arbcp5_cpxdp_grant_arbbf_ca_5(arbcp5_cpxdp_grant_arbbf_ca[5]),
              .arbcp5_cpxdp_q0_hold_arbbf_ca_l_5(arbcp5_cpxdp_q0_hold_arbbf_ca_l[5]),
              .arbcp5_cpxdp_qsel0_arbbf_ca_5(arbcp5_cpxdp_qsel0_arbbf_ca[5]),
              .arbcp5_cpxdp_qsel1_arbbf_ca_l_5(arbcp5_cpxdp_qsel1_arbbf_ca_l[5]),
              .arbcp5_cpxdp_shift_arbbf_cx_5(arbcp5_cpxdp_shift_arbbf_cx[5]),
              .arbcp6_cpxdp_grant_arbbf_ca_5(arbcp6_cpxdp_grant_arbbf_ca[5]),
              .arbcp6_cpxdp_q0_hold_arbbf_ca_l_5(arbcp6_cpxdp_q0_hold_arbbf_ca_l[5]),
              .arbcp6_cpxdp_qsel0_arbbf_ca_5(arbcp6_cpxdp_qsel0_arbbf_ca[5]),
              .arbcp6_cpxdp_qsel1_arbbf_ca_l_5(arbcp6_cpxdp_qsel1_arbbf_ca_l[5]),
              .arbcp6_cpxdp_shift_arbbf_cx_5(arbcp6_cpxdp_shift_arbbf_cx[5]),
              .arbcp7_cpxdp_grant_arbbf_ca_5(arbcp7_cpxdp_grant_arbbf_ca[5]),
              .arbcp7_cpxdp_q0_hold_arbbf_ca_l_5(arbcp7_cpxdp_q0_hold_arbbf_ca_l[5]),
              .arbcp7_cpxdp_qsel0_arbbf_ca_5(arbcp7_cpxdp_qsel0_arbbf_ca[5]),
              .arbcp7_cpxdp_qsel1_arbbf_ca_l_5(arbcp7_cpxdp_qsel1_arbbf_ca_l[5]),
              .arbcp7_cpxdp_shift_arbbf_cx_5(arbcp7_cpxdp_shift_arbbf_cx[5]),
              .arbcp0_cpxdp_grant_arbbf_ca_2(arbcp0_cpxdp_grant_arbbf_ca[2]),
              .arbcp0_cpxdp_q0_hold_arbbf_ca_l_2(arbcp0_cpxdp_q0_hold_arbbf_ca_l[2]),
              .arbcp0_cpxdp_qsel0_arbbf_ca_2(arbcp0_cpxdp_qsel0_arbbf_ca[2]),
              .arbcp0_cpxdp_qsel1_arbbf_ca_l_2(arbcp0_cpxdp_qsel1_arbbf_ca_l[2]),
              .arbcp0_cpxdp_shift_arbbf_cx_2(arbcp0_cpxdp_shift_arbbf_cx[2]),
              .arbcp1_cpxdp_grant_arbbf_ca_2(arbcp1_cpxdp_grant_arbbf_ca[2]),
              .arbcp1_cpxdp_q0_hold_arbbf_ca_l_2(arbcp1_cpxdp_q0_hold_arbbf_ca_l[2]),
              .arbcp1_cpxdp_qsel0_arbbf_ca_2(arbcp1_cpxdp_qsel0_arbbf_ca[2]),
              .arbcp1_cpxdp_qsel1_arbbf_ca_l_2(arbcp1_cpxdp_qsel1_arbbf_ca_l[2]),
              .arbcp1_cpxdp_shift_arbbf_cx_2(arbcp1_cpxdp_shift_arbbf_cx[2]),
              .arbcp2_cpxdp_grant_arbbf_ca_2(arbcp2_cpxdp_grant_arbbf_ca[2]),
              .arbcp2_cpxdp_q0_hold_arbbf_ca_l_2(arbcp2_cpxdp_q0_hold_arbbf_ca_l[2]),
              .arbcp2_cpxdp_qsel0_arbbf_ca_2(arbcp2_cpxdp_qsel0_arbbf_ca[2]),
              .arbcp2_cpxdp_qsel1_arbbf_ca_l_2(arbcp2_cpxdp_qsel1_arbbf_ca_l[2]),
              .arbcp2_cpxdp_shift_arbbf_cx_2(arbcp2_cpxdp_shift_arbbf_cx[2]),
              .arbcp3_cpxdp_grant_arbbf_ca_2(arbcp3_cpxdp_grant_arbbf_ca[2]),
              .arbcp3_cpxdp_q0_hold_arbbf_ca_l_2(arbcp3_cpxdp_q0_hold_arbbf_ca_l[2]),
              .arbcp3_cpxdp_qsel0_arbbf_ca_2(arbcp3_cpxdp_qsel0_arbbf_ca[2]),
              .arbcp3_cpxdp_qsel1_arbbf_ca_l_2(arbcp3_cpxdp_qsel1_arbbf_ca_l[2]),
              .arbcp3_cpxdp_shift_arbbf_cx_2(arbcp3_cpxdp_shift_arbbf_cx[2]),
              .arbcp4_cpxdp_grant_arbbf_ca_2(arbcp4_cpxdp_grant_arbbf_ca[2]),
              .arbcp4_cpxdp_q0_hold_arbbf_ca_l_2(arbcp4_cpxdp_q0_hold_arbbf_ca_l[2]),
              .arbcp4_cpxdp_qsel0_arbbf_ca_2(arbcp4_cpxdp_qsel0_arbbf_ca[2]),
              .arbcp4_cpxdp_qsel1_arbbf_ca_l_2(arbcp4_cpxdp_qsel1_arbbf_ca_l[2]),
              .arbcp4_cpxdp_shift_arbbf_cx_2(arbcp4_cpxdp_shift_arbbf_cx[2]),
              .arbcp5_cpxdp_grant_arbbf_ca_2(arbcp5_cpxdp_grant_arbbf_ca[2]),
              .arbcp5_cpxdp_q0_hold_arbbf_ca_l_2(arbcp5_cpxdp_q0_hold_arbbf_ca_l[2]),
              .arbcp5_cpxdp_qsel0_arbbf_ca_2(arbcp5_cpxdp_qsel0_arbbf_ca[2]),
              .arbcp5_cpxdp_qsel1_arbbf_ca_l_2(arbcp5_cpxdp_qsel1_arbbf_ca_l[2]),
              .arbcp5_cpxdp_shift_arbbf_cx_2(arbcp5_cpxdp_shift_arbbf_cx[2]),
              .arbcp6_cpxdp_grant_arbbf_ca_2(arbcp6_cpxdp_grant_arbbf_ca[2]),
              .arbcp6_cpxdp_q0_hold_arbbf_ca_l_2(arbcp6_cpxdp_q0_hold_arbbf_ca_l[2]),
              .arbcp6_cpxdp_qsel0_arbbf_ca_2(arbcp6_cpxdp_qsel0_arbbf_ca[2]),
              .arbcp6_cpxdp_qsel1_arbbf_ca_l_2(arbcp6_cpxdp_qsel1_arbbf_ca_l[2]),
              .arbcp6_cpxdp_shift_arbbf_cx_2(arbcp6_cpxdp_shift_arbbf_cx[2]),
              .arbcp7_cpxdp_grant_arbbf_ca_2(arbcp7_cpxdp_grant_arbbf_ca[2]),
              .arbcp7_cpxdp_q0_hold_arbbf_ca_l_2(arbcp7_cpxdp_q0_hold_arbbf_ca_l[2]),
              .arbcp7_cpxdp_qsel0_arbbf_ca_2(arbcp7_cpxdp_qsel0_arbbf_ca[2]),
              .arbcp7_cpxdp_qsel1_arbbf_ca_l_2(arbcp7_cpxdp_qsel1_arbbf_ca_l[2]),
              .arbcp7_cpxdp_shift_arbbf_cx_2(arbcp7_cpxdp_shift_arbbf_cx[2]));
*/
cpx_buf_p3 p3(/*AUTOINST*/
	      // Outputs
	      .scache3_cpx_req_bufp3_cq	(scache3_cpx_req_bufp3_cq[7:0]),
	      .scache3_cpx_atom_bufp3_cq(scache3_cpx_atom_bufp3_cq),
	      .io_cpx_req_bufp3_cq	(io_cpx_req_bufp3_cq[7:0]),
	      .cpx_scache3_grant_bufp3_ca_l(cpx_scache3_grant_bufp3_ca_l[7:0]),
	      .cpx_spc5_data_rdy_bufp3_cx(cpx_spc5_data_rdy_bufp3_cx),
	      .cpx_spc6_data_rdy_bufp3_cx(cpx_spc6_data_rdy_bufp3_cx),
	      .cpx_spc7_data_rdy_bufp3_cx(cpx_spc7_data_rdy_bufp3_cx),
	      .arbcp0_cpxdp_grant_bufp3_ca_l_5(arbcp0_cpxdp_grant_bufp3_ca_l[5]), // Templated
	      .arbcp0_cpxdp_q0_hold_bufp3_ca_5(arbcp0_cpxdp_q0_hold_bufp3_ca[5]), // Templated
	      .arbcp0_cpxdp_qsel0_bufp3_ca_l_5(arbcp0_cpxdp_qsel0_bufp3_ca_l[5]), // Templated
	      .arbcp0_cpxdp_qsel1_bufp3_ca_5(arbcp0_cpxdp_qsel1_bufp3_ca[5]), // Templated
	      .arbcp0_cpxdp_shift_bufp3_cx_l_5(arbcp0_cpxdp_shift_bufp3_cx_l[5]), // Templated
	      .arbcp1_cpxdp_grant_bufp3_ca_l_5(arbcp1_cpxdp_grant_bufp3_ca_l[5]), // Templated
	      .arbcp1_cpxdp_q0_hold_bufp3_ca_5(arbcp1_cpxdp_q0_hold_bufp3_ca[5]), // Templated
	      .arbcp1_cpxdp_qsel0_bufp3_ca_l_5(arbcp1_cpxdp_qsel0_bufp3_ca_l[5]), // Templated
	      .arbcp1_cpxdp_qsel1_bufp3_ca_5(arbcp1_cpxdp_qsel1_bufp3_ca[5]), // Templated
	      .arbcp1_cpxdp_shift_bufp3_cx_l_5(arbcp1_cpxdp_shift_bufp3_cx_l[5]), // Templated
	      .arbcp2_cpxdp_grant_bufp3_ca_l_5(arbcp2_cpxdp_grant_bufp3_ca_l[5]), // Templated
	      .arbcp2_cpxdp_q0_hold_bufp3_ca_5(arbcp2_cpxdp_q0_hold_bufp3_ca[5]), // Templated
	      .arbcp2_cpxdp_qsel0_bufp3_ca_l_5(arbcp2_cpxdp_qsel0_bufp3_ca_l[5]), // Templated
	      .arbcp2_cpxdp_qsel1_bufp3_ca_5(arbcp2_cpxdp_qsel1_bufp3_ca[5]), // Templated
	      .arbcp2_cpxdp_shift_bufp3_cx_l_5(arbcp2_cpxdp_shift_bufp3_cx_l[5]), // Templated
	      .arbcp3_cpxdp_grant_bufp3_ca_l_5(arbcp3_cpxdp_grant_bufp3_ca_l[5]), // Templated
	      .arbcp3_cpxdp_q0_hold_bufp3_ca_5(arbcp3_cpxdp_q0_hold_bufp3_ca[5]), // Templated
	      .arbcp3_cpxdp_qsel0_bufp3_ca_l_5(arbcp3_cpxdp_qsel0_bufp3_ca_l[5]), // Templated
	      .arbcp3_cpxdp_qsel1_bufp3_ca_5(arbcp3_cpxdp_qsel1_bufp3_ca[5]), // Templated
	      .arbcp3_cpxdp_shift_bufp3_cx_l_5(arbcp3_cpxdp_shift_bufp3_cx_l[5]), // Templated
	      .arbcp4_cpxdp_grant_bufp3_ca_l_5(arbcp4_cpxdp_grant_bufp3_ca_l[5]), // Templated
	      .arbcp4_cpxdp_q0_hold_bufp3_ca_5(arbcp4_cpxdp_q0_hold_bufp3_ca[5]), // Templated
	      .arbcp4_cpxdp_qsel0_bufp3_ca_l_5(arbcp4_cpxdp_qsel0_bufp3_ca_l[5]), // Templated
	      .arbcp4_cpxdp_qsel1_bufp3_ca_5(arbcp4_cpxdp_qsel1_bufp3_ca[5]), // Templated
	      .arbcp4_cpxdp_shift_bufp3_cx_l_5(arbcp4_cpxdp_shift_bufp3_cx_l[5]), // Templated
	      .arbcp5_cpxdp_grant_bufp3_ca_l_5(arbcp5_cpxdp_grant_bufp3_ca_l[5]), // Templated
	      .arbcp5_cpxdp_q0_hold_bufp3_ca_5(arbcp5_cpxdp_q0_hold_bufp3_ca[5]), // Templated
	      .arbcp5_cpxdp_qsel0_bufp3_ca_l_5(arbcp5_cpxdp_qsel0_bufp3_ca_l[5]), // Templated
	      .arbcp5_cpxdp_qsel1_bufp3_ca_5(arbcp5_cpxdp_qsel1_bufp3_ca[5]), // Templated
	      .arbcp5_cpxdp_shift_bufp3_cx_l_5(arbcp5_cpxdp_shift_bufp3_cx_l[5]), // Templated
	      .arbcp6_cpxdp_grant_bufp3_ca_l_5(arbcp6_cpxdp_grant_bufp3_ca_l[5]), // Templated
	      .arbcp6_cpxdp_q0_hold_bufp3_ca_5(arbcp6_cpxdp_q0_hold_bufp3_ca[5]), // Templated
	      .arbcp6_cpxdp_qsel0_bufp3_ca_l_5(arbcp6_cpxdp_qsel0_bufp3_ca_l[5]), // Templated
	      .arbcp6_cpxdp_qsel1_bufp3_ca_5(arbcp6_cpxdp_qsel1_bufp3_ca[5]), // Templated
	      .arbcp6_cpxdp_shift_bufp3_cx_l_5(arbcp6_cpxdp_shift_bufp3_cx_l[5]), // Templated
	      .arbcp7_cpxdp_grant_bufp3_ca_l_5(arbcp7_cpxdp_grant_bufp3_ca_l[5]), // Templated
	      .arbcp7_cpxdp_q0_hold_bufp3_ca_5(arbcp7_cpxdp_q0_hold_bufp3_ca[5]), // Templated
	      .arbcp7_cpxdp_qsel0_bufp3_ca_l_5(arbcp7_cpxdp_qsel0_bufp3_ca_l[5]), // Templated
	      .arbcp7_cpxdp_qsel1_bufp3_ca_5(arbcp7_cpxdp_qsel1_bufp3_ca[5]), // Templated
	      .arbcp7_cpxdp_shift_bufp3_cx_l_5(arbcp7_cpxdp_shift_bufp3_cx_l[5]), // Templated
	      .arbcp0_cpxdp_grant_bufp3_ca_l_2(arbcp0_cpxdp_grant_bufp3_ca_l[2]), // Templated
	      .arbcp0_cpxdp_q0_hold_bufp3_ca_2(arbcp0_cpxdp_q0_hold_bufp3_ca[2]), // Templated
	      .arbcp0_cpxdp_qsel0_bufp3_ca_l_2(arbcp0_cpxdp_qsel0_bufp3_ca_l[2]), // Templated
	      .arbcp0_cpxdp_qsel1_bufp3_ca_2(arbcp0_cpxdp_qsel1_bufp3_ca[2]), // Templated
	      .arbcp0_cpxdp_shift_bufp3_cx_l_2(arbcp0_cpxdp_shift_bufp3_cx_l[2]), // Templated
	      .arbcp1_cpxdp_grant_bufp3_ca_l_2(arbcp1_cpxdp_grant_bufp3_ca_l[2]), // Templated
	      .arbcp1_cpxdp_q0_hold_bufp3_ca_2(arbcp1_cpxdp_q0_hold_bufp3_ca[2]), // Templated
	      .arbcp1_cpxdp_qsel0_bufp3_ca_l_2(arbcp1_cpxdp_qsel0_bufp3_ca_l[2]), // Templated
	      .arbcp1_cpxdp_qsel1_bufp3_ca_2(arbcp1_cpxdp_qsel1_bufp3_ca[2]), // Templated
	      .arbcp1_cpxdp_shift_bufp3_cx_l_2(arbcp1_cpxdp_shift_bufp3_cx_l[2]), // Templated
	      .arbcp2_cpxdp_grant_bufp3_ca_l_2(arbcp2_cpxdp_grant_bufp3_ca_l[2]), // Templated
	      .arbcp2_cpxdp_q0_hold_bufp3_ca_2(arbcp2_cpxdp_q0_hold_bufp3_ca[2]), // Templated
	      .arbcp2_cpxdp_qsel0_bufp3_ca_l_2(arbcp2_cpxdp_qsel0_bufp3_ca_l[2]), // Templated
	      .arbcp2_cpxdp_qsel1_bufp3_ca_2(arbcp2_cpxdp_qsel1_bufp3_ca[2]), // Templated
	      .arbcp2_cpxdp_shift_bufp3_cx_l_2(arbcp2_cpxdp_shift_bufp3_cx_l[2]), // Templated
	      .arbcp3_cpxdp_grant_bufp3_ca_l_2(arbcp3_cpxdp_grant_bufp3_ca_l[2]), // Templated
	      .arbcp3_cpxdp_q0_hold_bufp3_ca_2(arbcp3_cpxdp_q0_hold_bufp3_ca[2]), // Templated
	      .arbcp3_cpxdp_qsel0_bufp3_ca_l_2(arbcp3_cpxdp_qsel0_bufp3_ca_l[2]), // Templated
	      .arbcp3_cpxdp_qsel1_bufp3_ca_2(arbcp3_cpxdp_qsel1_bufp3_ca[2]), // Templated
	      .arbcp3_cpxdp_shift_bufp3_cx_l_2(arbcp3_cpxdp_shift_bufp3_cx_l[2]), // Templated
	      .arbcp4_cpxdp_grant_bufp3_ca_l_2(arbcp4_cpxdp_grant_bufp3_ca_l[2]), // Templated
	      .arbcp4_cpxdp_q0_hold_bufp3_ca_2(arbcp4_cpxdp_q0_hold_bufp3_ca[2]), // Templated
	      .arbcp4_cpxdp_qsel0_bufp3_ca_l_2(arbcp4_cpxdp_qsel0_bufp3_ca_l[2]), // Templated
	      .arbcp4_cpxdp_qsel1_bufp3_ca_2(arbcp4_cpxdp_qsel1_bufp3_ca[2]), // Templated
	      .arbcp4_cpxdp_shift_bufp3_cx_l_2(arbcp4_cpxdp_shift_bufp3_cx_l[2]), // Templated
	      .arbcp5_cpxdp_grant_bufp3_ca_l_2(arbcp5_cpxdp_grant_bufp3_ca_l[2]), // Templated
	      .arbcp5_cpxdp_q0_hold_bufp3_ca_2(arbcp5_cpxdp_q0_hold_bufp3_ca[2]), // Templated
	      .arbcp5_cpxdp_qsel0_bufp3_ca_l_2(arbcp5_cpxdp_qsel0_bufp3_ca_l[2]), // Templated
	      .arbcp5_cpxdp_qsel1_bufp3_ca_2(arbcp5_cpxdp_qsel1_bufp3_ca[2]), // Templated
	      .arbcp5_cpxdp_shift_bufp3_cx_l_2(arbcp5_cpxdp_shift_bufp3_cx_l[2]), // Templated
	      .arbcp6_cpxdp_grant_bufp3_ca_l_2(arbcp6_cpxdp_grant_bufp3_ca_l[2]), // Templated
	      .arbcp6_cpxdp_q0_hold_bufp3_ca_2(arbcp6_cpxdp_q0_hold_bufp3_ca[2]), // Templated
	      .arbcp6_cpxdp_qsel0_bufp3_ca_l_2(arbcp6_cpxdp_qsel0_bufp3_ca_l[2]), // Templated
	      .arbcp6_cpxdp_qsel1_bufp3_ca_2(arbcp6_cpxdp_qsel1_bufp3_ca[2]), // Templated
	      .arbcp6_cpxdp_shift_bufp3_cx_l_2(arbcp6_cpxdp_shift_bufp3_cx_l[2]), // Templated
	      .arbcp7_cpxdp_grant_bufp3_ca_l_2(arbcp7_cpxdp_grant_bufp3_ca_l[2]), // Templated
	      .arbcp7_cpxdp_q0_hold_bufp3_ca_2(arbcp7_cpxdp_q0_hold_bufp3_ca[2]), // Templated
	      .arbcp7_cpxdp_qsel0_bufp3_ca_l_2(arbcp7_cpxdp_qsel0_bufp3_ca_l[2]), // Templated
	      .arbcp7_cpxdp_qsel1_bufp3_ca_2(arbcp7_cpxdp_qsel1_bufp3_ca[2]), // Templated
	      .arbcp7_cpxdp_shift_bufp3_cx_l_2(arbcp7_cpxdp_shift_bufp3_cx_l[2]), // Templated
	      // Inputs
	      .scache3_cpx_req_bufp4_cq	(scache3_cpx_req_bufp4_cq[7:0]),
	      .scache3_cpx_atom_bufp4_cq(scache3_cpx_atom_bufp4_cq),
	      .io_cpx_req_bufp4_cq	(io_cpx_req_bufp4_cq[7:0]),
	      .cpx_scache3_grant_ca	(cpx_scache3_grant_ca[7:0]),
	      .cpx_spc5_data_rdy_cx	(cpx_spc5_data_rdy_cx),
	      .cpx_spc6_data_rdy_cx	(cpx_spc6_data_rdy_cx),
	      .cpx_spc7_data_rdy_cx	(cpx_spc7_data_rdy_cx),
	      .arbcp0_cpxdp_grant_arbbf_ca_5(arbcp0_cpxdp_grant_arbbf_ca[5]), // Templated
	      .arbcp0_cpxdp_q0_hold_arbbf_ca_l_5(arbcp0_cpxdp_q0_hold_arbbf_ca_l[5]), // Templated
	      .arbcp0_cpxdp_qsel0_arbbf_ca_5(arbcp0_cpxdp_qsel0_arbbf_ca[5]), // Templated
	      .arbcp0_cpxdp_qsel1_arbbf_ca_l_5(arbcp0_cpxdp_qsel1_arbbf_ca_l[5]), // Templated
	      .arbcp0_cpxdp_shift_arbbf_cx_5(arbcp0_cpxdp_shift_arbbf_cx[5]), // Templated
	      .arbcp1_cpxdp_grant_arbbf_ca_5(arbcp1_cpxdp_grant_arbbf_ca[5]), // Templated
	      .arbcp1_cpxdp_q0_hold_arbbf_ca_l_5(arbcp1_cpxdp_q0_hold_arbbf_ca_l[5]), // Templated
	      .arbcp1_cpxdp_qsel0_arbbf_ca_5(arbcp1_cpxdp_qsel0_arbbf_ca[5]), // Templated
	      .arbcp1_cpxdp_qsel1_arbbf_ca_l_5(arbcp1_cpxdp_qsel1_arbbf_ca_l[5]), // Templated
	      .arbcp1_cpxdp_shift_arbbf_cx_5(arbcp1_cpxdp_shift_arbbf_cx[5]), // Templated
	      .arbcp2_cpxdp_grant_arbbf_ca_5(arbcp2_cpxdp_grant_arbbf_ca[5]), // Templated
	      .arbcp2_cpxdp_q0_hold_arbbf_ca_l_5(arbcp2_cpxdp_q0_hold_arbbf_ca_l[5]), // Templated
	      .arbcp2_cpxdp_qsel0_arbbf_ca_5(arbcp2_cpxdp_qsel0_arbbf_ca[5]), // Templated
	      .arbcp2_cpxdp_qsel1_arbbf_ca_l_5(arbcp2_cpxdp_qsel1_arbbf_ca_l[5]), // Templated
	      .arbcp2_cpxdp_shift_arbbf_cx_5(arbcp2_cpxdp_shift_arbbf_cx[5]), // Templated
	      .arbcp3_cpxdp_grant_arbbf_ca_5(arbcp3_cpxdp_grant_arbbf_ca[5]), // Templated
	      .arbcp3_cpxdp_q0_hold_arbbf_ca_l_5(arbcp3_cpxdp_q0_hold_arbbf_ca_l[5]), // Templated
	      .arbcp3_cpxdp_qsel0_arbbf_ca_5(arbcp3_cpxdp_qsel0_arbbf_ca[5]), // Templated
	      .arbcp3_cpxdp_qsel1_arbbf_ca_l_5(arbcp3_cpxdp_qsel1_arbbf_ca_l[5]), // Templated
	      .arbcp3_cpxdp_shift_arbbf_cx_5(arbcp3_cpxdp_shift_arbbf_cx[5]), // Templated
	      .arbcp4_cpxdp_grant_arbbf_ca_5(arbcp4_cpxdp_grant_arbbf_ca[5]), // Templated
	      .arbcp4_cpxdp_q0_hold_arbbf_ca_l_5(arbcp4_cpxdp_q0_hold_arbbf_ca_l[5]), // Templated
	      .arbcp4_cpxdp_qsel0_arbbf_ca_5(arbcp4_cpxdp_qsel0_arbbf_ca[5]), // Templated
	      .arbcp4_cpxdp_qsel1_arbbf_ca_l_5(arbcp4_cpxdp_qsel1_arbbf_ca_l[5]), // Templated
	      .arbcp4_cpxdp_shift_arbbf_cx_5(arbcp4_cpxdp_shift_arbbf_cx[5]), // Templated
	      .arbcp5_cpxdp_grant_arbbf_ca_5(arbcp5_cpxdp_grant_arbbf_ca[5]), // Templated
	      .arbcp5_cpxdp_q0_hold_arbbf_ca_l_5(arbcp5_cpxdp_q0_hold_arbbf_ca_l[5]), // Templated
	      .arbcp5_cpxdp_qsel0_arbbf_ca_5(arbcp5_cpxdp_qsel0_arbbf_ca[5]), // Templated
	      .arbcp5_cpxdp_qsel1_arbbf_ca_l_5(arbcp5_cpxdp_qsel1_arbbf_ca_l[5]), // Templated
	      .arbcp5_cpxdp_shift_arbbf_cx_5(arbcp5_cpxdp_shift_arbbf_cx[5]), // Templated
	      .arbcp6_cpxdp_grant_arbbf_ca_5(arbcp6_cpxdp_grant_arbbf_ca[5]), // Templated
	      .arbcp6_cpxdp_q0_hold_arbbf_ca_l_5(arbcp6_cpxdp_q0_hold_arbbf_ca_l[5]), // Templated
	      .arbcp6_cpxdp_qsel0_arbbf_ca_5(arbcp6_cpxdp_qsel0_arbbf_ca[5]), // Templated
	      .arbcp6_cpxdp_qsel1_arbbf_ca_l_5(arbcp6_cpxdp_qsel1_arbbf_ca_l[5]), // Templated
	      .arbcp6_cpxdp_shift_arbbf_cx_5(arbcp6_cpxdp_shift_arbbf_cx[5]), // Templated
	      .arbcp7_cpxdp_grant_arbbf_ca_5(arbcp7_cpxdp_grant_arbbf_ca[5]), // Templated
	      .arbcp7_cpxdp_q0_hold_arbbf_ca_l_5(arbcp7_cpxdp_q0_hold_arbbf_ca_l[5]), // Templated
	      .arbcp7_cpxdp_qsel0_arbbf_ca_5(arbcp7_cpxdp_qsel0_arbbf_ca[5]), // Templated
	      .arbcp7_cpxdp_qsel1_arbbf_ca_l_5(arbcp7_cpxdp_qsel1_arbbf_ca_l[5]), // Templated
	      .arbcp7_cpxdp_shift_arbbf_cx_5(arbcp7_cpxdp_shift_arbbf_cx[5]), // Templated
	      .arbcp0_cpxdp_grant_arbbf_ca_2(arbcp0_cpxdp_grant_arbbf_ca[2]), // Templated
	      .arbcp0_cpxdp_q0_hold_arbbf_ca_l_2(arbcp0_cpxdp_q0_hold_arbbf_ca_l[2]), // Templated
	      .arbcp0_cpxdp_qsel0_arbbf_ca_2(arbcp0_cpxdp_qsel0_arbbf_ca[2]), // Templated
	      .arbcp0_cpxdp_qsel1_arbbf_ca_l_2(arbcp0_cpxdp_qsel1_arbbf_ca_l[2]), // Templated
	      .arbcp0_cpxdp_shift_arbbf_cx_2(arbcp0_cpxdp_shift_arbbf_cx[2]), // Templated
	      .arbcp1_cpxdp_grant_arbbf_ca_2(arbcp1_cpxdp_grant_arbbf_ca[2]), // Templated
	      .arbcp1_cpxdp_q0_hold_arbbf_ca_l_2(arbcp1_cpxdp_q0_hold_arbbf_ca_l[2]), // Templated
	      .arbcp1_cpxdp_qsel0_arbbf_ca_2(arbcp1_cpxdp_qsel0_arbbf_ca[2]), // Templated
	      .arbcp1_cpxdp_qsel1_arbbf_ca_l_2(arbcp1_cpxdp_qsel1_arbbf_ca_l[2]), // Templated
	      .arbcp1_cpxdp_shift_arbbf_cx_2(arbcp1_cpxdp_shift_arbbf_cx[2]), // Templated
	      .arbcp2_cpxdp_grant_arbbf_ca_2(arbcp2_cpxdp_grant_arbbf_ca[2]), // Templated
	      .arbcp2_cpxdp_q0_hold_arbbf_ca_l_2(arbcp2_cpxdp_q0_hold_arbbf_ca_l[2]), // Templated
	      .arbcp2_cpxdp_qsel0_arbbf_ca_2(arbcp2_cpxdp_qsel0_arbbf_ca[2]), // Templated
	      .arbcp2_cpxdp_qsel1_arbbf_ca_l_2(arbcp2_cpxdp_qsel1_arbbf_ca_l[2]), // Templated
	      .arbcp2_cpxdp_shift_arbbf_cx_2(arbcp2_cpxdp_shift_arbbf_cx[2]), // Templated
	      .arbcp3_cpxdp_grant_arbbf_ca_2(arbcp3_cpxdp_grant_arbbf_ca[2]), // Templated
	      .arbcp3_cpxdp_q0_hold_arbbf_ca_l_2(arbcp3_cpxdp_q0_hold_arbbf_ca_l[2]), // Templated
	      .arbcp3_cpxdp_qsel0_arbbf_ca_2(arbcp3_cpxdp_qsel0_arbbf_ca[2]), // Templated
	      .arbcp3_cpxdp_qsel1_arbbf_ca_l_2(arbcp3_cpxdp_qsel1_arbbf_ca_l[2]), // Templated
	      .arbcp3_cpxdp_shift_arbbf_cx_2(arbcp3_cpxdp_shift_arbbf_cx[2]), // Templated
	      .arbcp4_cpxdp_grant_arbbf_ca_2(arbcp4_cpxdp_grant_arbbf_ca[2]), // Templated
	      .arbcp4_cpxdp_q0_hold_arbbf_ca_l_2(arbcp4_cpxdp_q0_hold_arbbf_ca_l[2]), // Templated
	      .arbcp4_cpxdp_qsel0_arbbf_ca_2(arbcp4_cpxdp_qsel0_arbbf_ca[2]), // Templated
	      .arbcp4_cpxdp_qsel1_arbbf_ca_l_2(arbcp4_cpxdp_qsel1_arbbf_ca_l[2]), // Templated
	      .arbcp4_cpxdp_shift_arbbf_cx_2(arbcp4_cpxdp_shift_arbbf_cx[2]), // Templated
	      .arbcp5_cpxdp_grant_arbbf_ca_2(arbcp5_cpxdp_grant_arbbf_ca[2]), // Templated
	      .arbcp5_cpxdp_q0_hold_arbbf_ca_l_2(arbcp5_cpxdp_q0_hold_arbbf_ca_l[2]), // Templated
	      .arbcp5_cpxdp_qsel0_arbbf_ca_2(arbcp5_cpxdp_qsel0_arbbf_ca[2]), // Templated
	      .arbcp5_cpxdp_qsel1_arbbf_ca_l_2(arbcp5_cpxdp_qsel1_arbbf_ca_l[2]), // Templated
	      .arbcp5_cpxdp_shift_arbbf_cx_2(arbcp5_cpxdp_shift_arbbf_cx[2]), // Templated
	      .arbcp6_cpxdp_grant_arbbf_ca_2(arbcp6_cpxdp_grant_arbbf_ca[2]), // Templated
	      .arbcp6_cpxdp_q0_hold_arbbf_ca_l_2(arbcp6_cpxdp_q0_hold_arbbf_ca_l[2]), // Templated
	      .arbcp6_cpxdp_qsel0_arbbf_ca_2(arbcp6_cpxdp_qsel0_arbbf_ca[2]), // Templated
	      .arbcp6_cpxdp_qsel1_arbbf_ca_l_2(arbcp6_cpxdp_qsel1_arbbf_ca_l[2]), // Templated
	      .arbcp6_cpxdp_shift_arbbf_cx_2(arbcp6_cpxdp_shift_arbbf_cx[2]), // Templated
	      .arbcp7_cpxdp_grant_arbbf_ca_2(arbcp7_cpxdp_grant_arbbf_ca[2]), // Templated
	      .arbcp7_cpxdp_q0_hold_arbbf_ca_l_2(arbcp7_cpxdp_q0_hold_arbbf_ca_l[2]), // Templated
	      .arbcp7_cpxdp_qsel0_arbbf_ca_2(arbcp7_cpxdp_qsel0_arbbf_ca[2]), // Templated
	      .arbcp7_cpxdp_qsel1_arbbf_ca_l_2(arbcp7_cpxdp_qsel1_arbbf_ca_l[2]), // Templated
	      .arbcp7_cpxdp_shift_arbbf_cx_2(arbcp7_cpxdp_shift_arbbf_cx[2])); // Templated
/* cpx_buf_pdr_even AUTO_TEMPLATE(
		   // Outputs
		   .arbcp0_cpxdp_grant_ca(arbcp0_cpxdp_grant_ca[4]),
		   .arbcp0_cpxdp_q0_hold_ca_l(arbcp0_cpxdp_q0_hold_ca_l[4]),
		   .arbcp0_cpxdp_qsel0_ca(arbcp0_cpxdp_qsel0_ca[4]),
		   .arbcp0_cpxdp_qsel1_ca_l(arbcp0_cpxdp_qsel1_ca_l[4]),
		   .arbcp0_cpxdp_shift_cx(arbcp0_cpxdp_shift_cx[4]),
		   .arbcp2_cpxdp_grant_ca(arbcp2_cpxdp_grant_ca[4]),
		   .arbcp2_cpxdp_q0_hold_ca_l(arbcp2_cpxdp_q0_hold_ca_l[4]),
		   .arbcp2_cpxdp_qsel0_ca(arbcp2_cpxdp_qsel0_ca[4]),
		   .arbcp2_cpxdp_qsel1_ca_l(arbcp2_cpxdp_qsel1_ca_l[4]),
		   .arbcp2_cpxdp_shift_cx(arbcp2_cpxdp_shift_cx[4]),
		   .arbcp4_cpxdp_grant_ca(arbcp4_cpxdp_grant_ca[4]),
		   .arbcp4_cpxdp_q0_hold_ca_l(arbcp4_cpxdp_q0_hold_ca_l[4]),
		   .arbcp4_cpxdp_qsel0_ca(arbcp4_cpxdp_qsel0_ca[4]),
		   .arbcp4_cpxdp_qsel1_ca_l(arbcp4_cpxdp_qsel1_ca_l[4]),
		   .arbcp4_cpxdp_shift_cx(arbcp4_cpxdp_shift_cx[4]),
		   .arbcp6_cpxdp_grant_ca(arbcp6_cpxdp_grant_ca[4]),
		   .arbcp6_cpxdp_q0_hold_ca_l(arbcp6_cpxdp_q0_hold_ca_l[4]),
		   .arbcp6_cpxdp_qsel0_ca(arbcp6_cpxdp_qsel0_ca[4]),
		   .arbcp6_cpxdp_qsel1_ca_l(arbcp6_cpxdp_qsel1_ca_l[4]),
		   .arbcp6_cpxdp_shift_cx(arbcp6_cpxdp_shift_cx[4]),
		   // Inputs
		   .arbcp0_cpxdp_grant_bufp3_ca(arbcp0_cpxdp_grant_arbbf_ca[4]),
		   .arbcp0_cpxdp_q0_hold_bufp3_ca_l(arbcp0_cpxdp_q0_hold_arbbf_ca_l[4]),
		   .arbcp0_cpxdp_qsel0_bufp3_ca(arbcp0_cpxdp_qsel0_arbbf_ca[4]),
		   .arbcp0_cpxdp_qsel1_bufp3_ca_l(arbcp0_cpxdp_qsel1_arbbf_ca_l[4]),
		   .arbcp0_cpxdp_shift_bufp3_cx(arbcp0_cpxdp_shift_arbbf_cx[4]),
		   .arbcp2_cpxdp_grant_bufp3_ca(arbcp2_cpxdp_grant_arbbf_ca[4]),
		   .arbcp2_cpxdp_q0_hold_bufp3_ca_l(arbcp2_cpxdp_q0_hold_arbbf_ca_l[4]),
		   .arbcp2_cpxdp_qsel0_bufp3_ca(arbcp2_cpxdp_qsel0_arbbf_ca[4]),
		   .arbcp2_cpxdp_qsel1_bufp3_ca_l(arbcp2_cpxdp_qsel1_arbbf_ca_l[4]),
		   .arbcp2_cpxdp_shift_bufp3_cx(arbcp2_cpxdp_shift_arbbf_cx[4]),
		   .arbcp4_cpxdp_grant_bufp3_ca(arbcp4_cpxdp_grant_arbbf_ca[4]),
		   .arbcp4_cpxdp_q0_hold_bufp3_ca_l(arbcp4_cpxdp_q0_hold_arbbf_ca_l[4]),
		   .arbcp4_cpxdp_qsel0_bufp3_ca(arbcp4_cpxdp_qsel0_arbbf_ca[4]),
		   .arbcp4_cpxdp_qsel1_bufp3_ca_l(arbcp4_cpxdp_qsel1_arbbf_ca_l[4]),
		   .arbcp4_cpxdp_shift_bufp3_cx(arbcp4_cpxdp_shift_arbbf_cx[4]),
		   .arbcp6_cpxdp_grant_bufp3_ca(arbcp6_cpxdp_grant_arbbf_ca[4]),
		   .arbcp6_cpxdp_q0_hold_bufp3_ca_l(arbcp6_cpxdp_q0_hold_arbbf_ca_l[4]),
		   .arbcp6_cpxdp_qsel0_bufp3_ca(arbcp6_cpxdp_qsel0_arbbf_ca[4]),
		   .arbcp6_cpxdp_qsel1_bufp3_ca_l(arbcp6_cpxdp_qsel1_arbbf_ca_l[4]),
		   .arbcp6_cpxdp_shift_bufp3_cx(arbcp6_cpxdp_shift_arbbf_cx[4]));
*/
   cpx_buf_pdr_even pdr_even(/*AUTOINST*/
			     // Outputs
			     .arbcp0_cpxdp_grant_ca(arbcp0_cpxdp_grant_ca[4]), // Templated
			     .arbcp0_cpxdp_q0_hold_ca_l(arbcp0_cpxdp_q0_hold_ca_l[4]), // Templated
			     .arbcp0_cpxdp_qsel0_ca(arbcp0_cpxdp_qsel0_ca[4]), // Templated
			     .arbcp0_cpxdp_qsel1_ca_l(arbcp0_cpxdp_qsel1_ca_l[4]), // Templated
			     .arbcp0_cpxdp_shift_cx(arbcp0_cpxdp_shift_cx[4]), // Templated
			     .arbcp2_cpxdp_grant_ca(arbcp2_cpxdp_grant_ca[4]), // Templated
			     .arbcp2_cpxdp_q0_hold_ca_l(arbcp2_cpxdp_q0_hold_ca_l[4]), // Templated
			     .arbcp2_cpxdp_qsel0_ca(arbcp2_cpxdp_qsel0_ca[4]), // Templated
			     .arbcp2_cpxdp_qsel1_ca_l(arbcp2_cpxdp_qsel1_ca_l[4]), // Templated
			     .arbcp2_cpxdp_shift_cx(arbcp2_cpxdp_shift_cx[4]), // Templated
			     .arbcp4_cpxdp_grant_ca(arbcp4_cpxdp_grant_ca[4]), // Templated
			     .arbcp4_cpxdp_q0_hold_ca_l(arbcp4_cpxdp_q0_hold_ca_l[4]), // Templated
			     .arbcp4_cpxdp_qsel0_ca(arbcp4_cpxdp_qsel0_ca[4]), // Templated
			     .arbcp4_cpxdp_qsel1_ca_l(arbcp4_cpxdp_qsel1_ca_l[4]), // Templated
			     .arbcp4_cpxdp_shift_cx(arbcp4_cpxdp_shift_cx[4]), // Templated
			     .arbcp6_cpxdp_grant_ca(arbcp6_cpxdp_grant_ca[4]), // Templated
			     .arbcp6_cpxdp_q0_hold_ca_l(arbcp6_cpxdp_q0_hold_ca_l[4]), // Templated
			     .arbcp6_cpxdp_qsel0_ca(arbcp6_cpxdp_qsel0_ca[4]), // Templated
			     .arbcp6_cpxdp_qsel1_ca_l(arbcp6_cpxdp_qsel1_ca_l[4]), // Templated
			     .arbcp6_cpxdp_shift_cx(arbcp6_cpxdp_shift_cx[4]), // Templated
			     // Inputs
			     .arbcp0_cpxdp_grant_bufp3_ca(arbcp0_cpxdp_grant_arbbf_ca[4]), // Templated
			     .arbcp0_cpxdp_q0_hold_bufp3_ca_l(arbcp0_cpxdp_q0_hold_arbbf_ca_l[4]), // Templated
			     .arbcp0_cpxdp_qsel0_bufp3_ca(arbcp0_cpxdp_qsel0_arbbf_ca[4]), // Templated
			     .arbcp0_cpxdp_qsel1_bufp3_ca_l(arbcp0_cpxdp_qsel1_arbbf_ca_l[4]), // Templated
			     .arbcp0_cpxdp_shift_bufp3_cx(arbcp0_cpxdp_shift_arbbf_cx[4]), // Templated
			     .arbcp2_cpxdp_grant_bufp3_ca(arbcp2_cpxdp_grant_arbbf_ca[4]), // Templated
			     .arbcp2_cpxdp_q0_hold_bufp3_ca_l(arbcp2_cpxdp_q0_hold_arbbf_ca_l[4]), // Templated
			     .arbcp2_cpxdp_qsel0_bufp3_ca(arbcp2_cpxdp_qsel0_arbbf_ca[4]), // Templated
			     .arbcp2_cpxdp_qsel1_bufp3_ca_l(arbcp2_cpxdp_qsel1_arbbf_ca_l[4]), // Templated
			     .arbcp2_cpxdp_shift_bufp3_cx(arbcp2_cpxdp_shift_arbbf_cx[4]), // Templated
			     .arbcp4_cpxdp_grant_bufp3_ca(arbcp4_cpxdp_grant_arbbf_ca[4]), // Templated
			     .arbcp4_cpxdp_q0_hold_bufp3_ca_l(arbcp4_cpxdp_q0_hold_arbbf_ca_l[4]), // Templated
			     .arbcp4_cpxdp_qsel0_bufp3_ca(arbcp4_cpxdp_qsel0_arbbf_ca[4]), // Templated
			     .arbcp4_cpxdp_qsel1_bufp3_ca_l(arbcp4_cpxdp_qsel1_arbbf_ca_l[4]), // Templated
			     .arbcp4_cpxdp_shift_bufp3_cx(arbcp4_cpxdp_shift_arbbf_cx[4]), // Templated
			     .arbcp6_cpxdp_grant_bufp3_ca(arbcp6_cpxdp_grant_arbbf_ca[4]), // Templated
			     .arbcp6_cpxdp_q0_hold_bufp3_ca_l(arbcp6_cpxdp_q0_hold_arbbf_ca_l[4]), // Templated
			     .arbcp6_cpxdp_qsel0_bufp3_ca(arbcp6_cpxdp_qsel0_arbbf_ca[4]), // Templated
			     .arbcp6_cpxdp_qsel1_bufp3_ca_l(arbcp6_cpxdp_qsel1_arbbf_ca_l[4]), // Templated
			     .arbcp6_cpxdp_shift_bufp3_cx(arbcp6_cpxdp_shift_arbbf_cx[4])); // Templated
/* cpx_buf_pdr_even AUTO_TEMPLATE(
		   // Outputs
		   .arbcp0_cpxdp_grant_ca(arbcp1_cpxdp_grant_ca[4]),
		   .arbcp0_cpxdp_q0_hold_ca_l(arbcp1_cpxdp_q0_hold_ca_l[4]),
		   .arbcp0_cpxdp_qsel0_ca(arbcp1_cpxdp_qsel0_ca[4]),
		   .arbcp0_cpxdp_qsel1_ca_l(arbcp1_cpxdp_qsel1_ca_l[4]),
		   .arbcp0_cpxdp_shift_cx(arbcp1_cpxdp_shift_cx[4]),
		   .arbcp2_cpxdp_grant_ca(arbcp3_cpxdp_grant_ca[4]),
		   .arbcp2_cpxdp_q0_hold_ca_l(arbcp3_cpxdp_q0_hold_ca_l[4]),
		   .arbcp2_cpxdp_qsel0_ca(arbcp3_cpxdp_qsel0_ca[4]),
		   .arbcp2_cpxdp_qsel1_ca_l(arbcp3_cpxdp_qsel1_ca_l[4]),
		   .arbcp2_cpxdp_shift_cx(arbcp3_cpxdp_shift_cx[4]),
		   .arbcp4_cpxdp_grant_ca(arbcp5_cpxdp_grant_ca[4]),
		   .arbcp4_cpxdp_q0_hold_ca_l(arbcp5_cpxdp_q0_hold_ca_l[4]),
		   .arbcp4_cpxdp_qsel0_ca(arbcp5_cpxdp_qsel0_ca[4]),
		   .arbcp4_cpxdp_qsel1_ca_l(arbcp5_cpxdp_qsel1_ca_l[4]),
		   .arbcp4_cpxdp_shift_cx(arbcp5_cpxdp_shift_cx[4]),
		   .arbcp6_cpxdp_grant_ca(arbcp7_cpxdp_grant_ca[4]),
		   .arbcp6_cpxdp_q0_hold_ca_l(arbcp7_cpxdp_q0_hold_ca_l[4]),
		   .arbcp6_cpxdp_qsel0_ca(arbcp7_cpxdp_qsel0_ca[4]),
		   .arbcp6_cpxdp_qsel1_ca_l(arbcp7_cpxdp_qsel1_ca_l[4]),
		   .arbcp6_cpxdp_shift_cx(arbcp7_cpxdp_shift_cx[4]),
		   // Inputs
		   .arbcp0_cpxdp_grant_bufp3_ca(arbcp1_cpxdp_grant_arbbf_ca[4]),
		   .arbcp0_cpxdp_q0_hold_bufp3_ca_l(arbcp1_cpxdp_q0_hold_arbbf_ca_l[4]),
		   .arbcp0_cpxdp_qsel0_bufp3_ca(arbcp1_cpxdp_qsel0_arbbf_ca[4]),
		   .arbcp0_cpxdp_qsel1_bufp3_ca_l(arbcp1_cpxdp_qsel1_arbbf_ca_l[4]),
		   .arbcp0_cpxdp_shift_bufp3_cx(arbcp1_cpxdp_shift_arbbf_cx[4]),
		   .arbcp2_cpxdp_grant_bufp3_ca(arbcp3_cpxdp_grant_arbbf_ca[4]),
		   .arbcp2_cpxdp_q0_hold_bufp3_ca_l(arbcp3_cpxdp_q0_hold_arbbf_ca_l[4]),
		   .arbcp2_cpxdp_qsel0_bufp3_ca(arbcp3_cpxdp_qsel0_arbbf_ca[4]),
		   .arbcp2_cpxdp_qsel1_bufp3_ca_l(arbcp3_cpxdp_qsel1_arbbf_ca_l[4]),
		   .arbcp2_cpxdp_shift_bufp3_cx(arbcp3_cpxdp_shift_arbbf_cx[4]),
		   .arbcp4_cpxdp_grant_bufp3_ca(arbcp5_cpxdp_grant_arbbf_ca[4]),
		   .arbcp4_cpxdp_q0_hold_bufp3_ca_l(arbcp5_cpxdp_q0_hold_arbbf_ca_l[4]),
		   .arbcp4_cpxdp_qsel0_bufp3_ca(arbcp5_cpxdp_qsel0_arbbf_ca[4]),
		   .arbcp4_cpxdp_qsel1_bufp3_ca_l(arbcp5_cpxdp_qsel1_arbbf_ca_l[4]),
		   .arbcp4_cpxdp_shift_bufp3_cx(arbcp5_cpxdp_shift_arbbf_cx[4]),
		   .arbcp6_cpxdp_grant_bufp3_ca(arbcp7_cpxdp_grant_arbbf_ca[4]),
		   .arbcp6_cpxdp_q0_hold_bufp3_ca_l(arbcp7_cpxdp_q0_hold_arbbf_ca_l[4]),
		   .arbcp6_cpxdp_qsel0_bufp3_ca(arbcp7_cpxdp_qsel0_arbbf_ca[4]),
		   .arbcp6_cpxdp_qsel1_bufp3_ca_l(arbcp7_cpxdp_qsel1_arbbf_ca_l[4]),
		   .arbcp6_cpxdp_shift_bufp3_cx(arbcp7_cpxdp_shift_arbbf_cx[4]));
*/ 
   
   cpx_buf_pdr_even pdr_odd(/*AUTOINST*/
			    // Outputs
			    .arbcp0_cpxdp_grant_ca(arbcp1_cpxdp_grant_ca[4]), // Templated
			    .arbcp0_cpxdp_q0_hold_ca_l(arbcp1_cpxdp_q0_hold_ca_l[4]), // Templated
			    .arbcp0_cpxdp_qsel0_ca(arbcp1_cpxdp_qsel0_ca[4]), // Templated
			    .arbcp0_cpxdp_qsel1_ca_l(arbcp1_cpxdp_qsel1_ca_l[4]), // Templated
			    .arbcp0_cpxdp_shift_cx(arbcp1_cpxdp_shift_cx[4]), // Templated
			    .arbcp2_cpxdp_grant_ca(arbcp3_cpxdp_grant_ca[4]), // Templated
			    .arbcp2_cpxdp_q0_hold_ca_l(arbcp3_cpxdp_q0_hold_ca_l[4]), // Templated
			    .arbcp2_cpxdp_qsel0_ca(arbcp3_cpxdp_qsel0_ca[4]), // Templated
			    .arbcp2_cpxdp_qsel1_ca_l(arbcp3_cpxdp_qsel1_ca_l[4]), // Templated
			    .arbcp2_cpxdp_shift_cx(arbcp3_cpxdp_shift_cx[4]), // Templated
			    .arbcp4_cpxdp_grant_ca(arbcp5_cpxdp_grant_ca[4]), // Templated
			    .arbcp4_cpxdp_q0_hold_ca_l(arbcp5_cpxdp_q0_hold_ca_l[4]), // Templated
			    .arbcp4_cpxdp_qsel0_ca(arbcp5_cpxdp_qsel0_ca[4]), // Templated
			    .arbcp4_cpxdp_qsel1_ca_l(arbcp5_cpxdp_qsel1_ca_l[4]), // Templated
			    .arbcp4_cpxdp_shift_cx(arbcp5_cpxdp_shift_cx[4]), // Templated
			    .arbcp6_cpxdp_grant_ca(arbcp7_cpxdp_grant_ca[4]), // Templated
			    .arbcp6_cpxdp_q0_hold_ca_l(arbcp7_cpxdp_q0_hold_ca_l[4]), // Templated
			    .arbcp6_cpxdp_qsel0_ca(arbcp7_cpxdp_qsel0_ca[4]), // Templated
			    .arbcp6_cpxdp_qsel1_ca_l(arbcp7_cpxdp_qsel1_ca_l[4]), // Templated
			    .arbcp6_cpxdp_shift_cx(arbcp7_cpxdp_shift_cx[4]), // Templated
			    // Inputs
			    .arbcp0_cpxdp_grant_bufp3_ca(arbcp1_cpxdp_grant_arbbf_ca[4]), // Templated
			    .arbcp0_cpxdp_q0_hold_bufp3_ca_l(arbcp1_cpxdp_q0_hold_arbbf_ca_l[4]), // Templated
			    .arbcp0_cpxdp_qsel0_bufp3_ca(arbcp1_cpxdp_qsel0_arbbf_ca[4]), // Templated
			    .arbcp0_cpxdp_qsel1_bufp3_ca_l(arbcp1_cpxdp_qsel1_arbbf_ca_l[4]), // Templated
			    .arbcp0_cpxdp_shift_bufp3_cx(arbcp1_cpxdp_shift_arbbf_cx[4]), // Templated
			    .arbcp2_cpxdp_grant_bufp3_ca(arbcp3_cpxdp_grant_arbbf_ca[4]), // Templated
			    .arbcp2_cpxdp_q0_hold_bufp3_ca_l(arbcp3_cpxdp_q0_hold_arbbf_ca_l[4]), // Templated
			    .arbcp2_cpxdp_qsel0_bufp3_ca(arbcp3_cpxdp_qsel0_arbbf_ca[4]), // Templated
			    .arbcp2_cpxdp_qsel1_bufp3_ca_l(arbcp3_cpxdp_qsel1_arbbf_ca_l[4]), // Templated
			    .arbcp2_cpxdp_shift_bufp3_cx(arbcp3_cpxdp_shift_arbbf_cx[4]), // Templated
			    .arbcp4_cpxdp_grant_bufp3_ca(arbcp5_cpxdp_grant_arbbf_ca[4]), // Templated
			    .arbcp4_cpxdp_q0_hold_bufp3_ca_l(arbcp5_cpxdp_q0_hold_arbbf_ca_l[4]), // Templated
			    .arbcp4_cpxdp_qsel0_bufp3_ca(arbcp5_cpxdp_qsel0_arbbf_ca[4]), // Templated
			    .arbcp4_cpxdp_qsel1_bufp3_ca_l(arbcp5_cpxdp_qsel1_arbbf_ca_l[4]), // Templated
			    .arbcp4_cpxdp_shift_bufp3_cx(arbcp5_cpxdp_shift_arbbf_cx[4]), // Templated
			    .arbcp6_cpxdp_grant_bufp3_ca(arbcp7_cpxdp_grant_arbbf_ca[4]), // Templated
			    .arbcp6_cpxdp_q0_hold_bufp3_ca_l(arbcp7_cpxdp_q0_hold_arbbf_ca_l[4]), // Templated
			    .arbcp6_cpxdp_qsel0_bufp3_ca(arbcp7_cpxdp_qsel0_arbbf_ca[4]), // Templated
			    .arbcp6_cpxdp_qsel1_bufp3_ca_l(arbcp7_cpxdp_qsel1_arbbf_ca_l[4]), // Templated
			    .arbcp6_cpxdp_shift_bufp3_cx(arbcp7_cpxdp_shift_arbbf_cx[4])); // Templated
   cpx_buf_p4 p4(/*AUTOINST*/
		 // Outputs
		 .scache3_cpx_req_bufp4_cq(scache3_cpx_req_bufp4_cq[7:0]),
		 .scache3_cpx_atom_bufp4_cq(scache3_cpx_atom_bufp4_cq),
		 .io_cpx_req_bufp4_cq	(io_cpx_req_bufp4_cq[7:0]),
		 .cpx_scache3_grant_bufp4_ca(cpx_scache3_grant_bufp4_ca[7:0]),
		 .cpx_spc7_data_rdy_bufp4_cx(cpx_spc7_data_rdy_bufp4_cx),
		 // Inputs
		 .scache3_cpx_req_bufpt_cq_l(scache3_cpx_req_bufpt_cq_l[7:0]),
		 .scache3_cpx_atom_bufpt_cq_l(scache3_cpx_atom_bufpt_cq_l),
		 .io_cpx_req_bufpt_cq_l	(io_cpx_req_bufpt_cq_l[7:0]),
		 .cpx_scache3_grant_bufp3_ca_l(cpx_scache3_grant_bufp3_ca_l[7:0]),
		 .cpx_spc7_data_rdy_bufp3_cx(cpx_spc7_data_rdy_bufp3_cx));

/*   cpx_buf_p4_even AUTO_TEMPLATE(
		 // Outputs
		 .arbcp0_cpxdp_grant_ca	(arbcp0_cpxdp_grant_ca[3]),
		 .arbcp0_cpxdp_q0_hold_ca_l(arbcp0_cpxdp_q0_hold_ca_l[3]),
		 .arbcp0_cpxdp_qsel0_ca	(arbcp0_cpxdp_qsel0_ca[3]),
		 .arbcp0_cpxdp_qsel1_ca_l(arbcp0_cpxdp_qsel1_ca_l[3]),
		 .arbcp0_cpxdp_shift_cx	(arbcp0_cpxdp_shift_cx[3]),
		 .arbcp2_cpxdp_grant_ca	(arbcp2_cpxdp_grant_ca[3]),
		 .arbcp2_cpxdp_q0_hold_ca_l(arbcp2_cpxdp_q0_hold_ca_l[3]),
		 .arbcp2_cpxdp_qsel0_ca	(arbcp2_cpxdp_qsel0_ca[3]),
		 .arbcp2_cpxdp_qsel1_ca_l(arbcp2_cpxdp_qsel1_ca_l[3]),
		 .arbcp2_cpxdp_shift_cx	(arbcp2_cpxdp_shift_cx[3]),
		 .arbcp4_cpxdp_grant_ca	(arbcp4_cpxdp_grant_ca[3]),
		 .arbcp4_cpxdp_q0_hold_ca_l(arbcp4_cpxdp_q0_hold_ca_l[3]),
		 .arbcp4_cpxdp_qsel0_ca	(arbcp4_cpxdp_qsel0_ca[3]),
		 .arbcp4_cpxdp_qsel1_ca_l(arbcp4_cpxdp_qsel1_ca_l[3]),
		 .arbcp4_cpxdp_shift_cx	(arbcp4_cpxdp_shift_cx[3]),
		 .arbcp6_cpxdp_grant_ca	(arbcp6_cpxdp_grant_ca[3]),
		 .arbcp6_cpxdp_q0_hold_ca_l(arbcp6_cpxdp_q0_hold_ca_l[3]),
		 .arbcp6_cpxdp_qsel0_ca	(arbcp6_cpxdp_qsel0_ca[3]),
		 .arbcp6_cpxdp_qsel1_ca_l(arbcp6_cpxdp_qsel1_ca_l[3]),
		 .arbcp6_cpxdp_shift_cx	(arbcp6_cpxdp_shift_cx[3]),
                 // Inputs
 	      .arbcp0_cpxdp_grant_bufp3_ca_l(arbcp0_cpxdp_grant_bufp1_ca_l[3]),
	      .arbcp0_cpxdp_q0_hold_bufp3_ca(arbcp0_cpxdp_q0_hold_bufp1_ca[3]),
	      .arbcp0_cpxdp_qsel0_bufp3_ca_l(arbcp0_cpxdp_qsel0_bufp1_ca_l[3]),
	      .arbcp0_cpxdp_qsel1_bufp3_ca(arbcp0_cpxdp_qsel1_bufp1_ca[3]),
	      .arbcp0_cpxdp_shift_bufp3_cx_l(arbcp0_cpxdp_shift_bufp1_cx_l[3]),
	      .arbcp2_cpxdp_grant_bufp3_ca_l(arbcp2_cpxdp_grant_bufp1_ca_l[3]),
	      .arbcp2_cpxdp_q0_hold_bufp3_ca(arbcp2_cpxdp_q0_hold_bufp1_ca[3]),
	      .arbcp2_cpxdp_qsel0_bufp3_ca_l(arbcp2_cpxdp_qsel0_bufp1_ca_l[3]),
	      .arbcp2_cpxdp_qsel1_bufp3_ca(arbcp2_cpxdp_qsel1_bufp1_ca[3]),
	      .arbcp2_cpxdp_shift_bufp3_cx_l(arbcp2_cpxdp_shift_bufp1_cx_l[3]),
	      .arbcp4_cpxdp_grant_bufp3_ca_l(arbcp4_cpxdp_grant_bufp1_ca_l[3]),
	      .arbcp4_cpxdp_q0_hold_bufp3_ca(arbcp4_cpxdp_q0_hold_bufp1_ca[3]),
	      .arbcp4_cpxdp_qsel0_bufp3_ca_l(arbcp4_cpxdp_qsel0_bufp1_ca_l[3]),
	      .arbcp4_cpxdp_qsel1_bufp3_ca(arbcp4_cpxdp_qsel1_bufp1_ca[3]),
	      .arbcp4_cpxdp_shift_bufp3_cx_l(arbcp4_cpxdp_shift_bufp1_cx_l[3]),
	      .arbcp6_cpxdp_grant_bufp3_ca_l(arbcp6_cpxdp_grant_bufp1_ca_l[3]),
	      .arbcp6_cpxdp_q0_hold_bufp3_ca(arbcp6_cpxdp_q0_hold_bufp1_ca[3]),
	      .arbcp6_cpxdp_qsel0_bufp3_ca_l(arbcp6_cpxdp_qsel0_bufp1_ca_l[3]),
	      .arbcp6_cpxdp_qsel1_bufp3_ca(arbcp6_cpxdp_qsel1_bufp1_ca[3]),
	      .arbcp6_cpxdp_shift_bufp3_cx_l(arbcp6_cpxdp_shift_bufp1_cx_l[3]));
*/

  cpx_buf_p4_even p4_even(/*AUTOINST*/
			  // Outputs
			  .arbcp0_cpxdp_grant_ca(arbcp0_cpxdp_grant_ca[3]), // Templated
			  .arbcp0_cpxdp_q0_hold_ca_l(arbcp0_cpxdp_q0_hold_ca_l[3]), // Templated
			  .arbcp0_cpxdp_qsel0_ca(arbcp0_cpxdp_qsel0_ca[3]), // Templated
			  .arbcp0_cpxdp_qsel1_ca_l(arbcp0_cpxdp_qsel1_ca_l[3]), // Templated
			  .arbcp0_cpxdp_shift_cx(arbcp0_cpxdp_shift_cx[3]), // Templated
			  .arbcp2_cpxdp_grant_ca(arbcp2_cpxdp_grant_ca[3]), // Templated
			  .arbcp2_cpxdp_q0_hold_ca_l(arbcp2_cpxdp_q0_hold_ca_l[3]), // Templated
			  .arbcp2_cpxdp_qsel0_ca(arbcp2_cpxdp_qsel0_ca[3]), // Templated
			  .arbcp2_cpxdp_qsel1_ca_l(arbcp2_cpxdp_qsel1_ca_l[3]), // Templated
			  .arbcp2_cpxdp_shift_cx(arbcp2_cpxdp_shift_cx[3]), // Templated
			  .arbcp4_cpxdp_grant_ca(arbcp4_cpxdp_grant_ca[3]), // Templated
			  .arbcp4_cpxdp_q0_hold_ca_l(arbcp4_cpxdp_q0_hold_ca_l[3]), // Templated
			  .arbcp4_cpxdp_qsel0_ca(arbcp4_cpxdp_qsel0_ca[3]), // Templated
			  .arbcp4_cpxdp_qsel1_ca_l(arbcp4_cpxdp_qsel1_ca_l[3]), // Templated
			  .arbcp4_cpxdp_shift_cx(arbcp4_cpxdp_shift_cx[3]), // Templated
			  .arbcp6_cpxdp_grant_ca(arbcp6_cpxdp_grant_ca[3]), // Templated
			  .arbcp6_cpxdp_q0_hold_ca_l(arbcp6_cpxdp_q0_hold_ca_l[3]), // Templated
			  .arbcp6_cpxdp_qsel0_ca(arbcp6_cpxdp_qsel0_ca[3]), // Templated
			  .arbcp6_cpxdp_qsel1_ca_l(arbcp6_cpxdp_qsel1_ca_l[3]), // Templated
			  .arbcp6_cpxdp_shift_cx(arbcp6_cpxdp_shift_cx[3]), // Templated
			  // Inputs
			  .arbcp0_cpxdp_grant_bufp3_ca_l(arbcp0_cpxdp_grant_bufp1_ca_l[3]), // Templated
			  .arbcp0_cpxdp_q0_hold_bufp3_ca(arbcp0_cpxdp_q0_hold_bufp1_ca[3]), // Templated
			  .arbcp0_cpxdp_qsel0_bufp3_ca_l(arbcp0_cpxdp_qsel0_bufp1_ca_l[3]), // Templated
			  .arbcp0_cpxdp_qsel1_bufp3_ca(arbcp0_cpxdp_qsel1_bufp1_ca[3]), // Templated
			  .arbcp0_cpxdp_shift_bufp3_cx_l(arbcp0_cpxdp_shift_bufp1_cx_l[3]), // Templated
			  .arbcp2_cpxdp_grant_bufp3_ca_l(arbcp2_cpxdp_grant_bufp1_ca_l[3]), // Templated
			  .arbcp2_cpxdp_q0_hold_bufp3_ca(arbcp2_cpxdp_q0_hold_bufp1_ca[3]), // Templated
			  .arbcp2_cpxdp_qsel0_bufp3_ca_l(arbcp2_cpxdp_qsel0_bufp1_ca_l[3]), // Templated
			  .arbcp2_cpxdp_qsel1_bufp3_ca(arbcp2_cpxdp_qsel1_bufp1_ca[3]), // Templated
			  .arbcp2_cpxdp_shift_bufp3_cx_l(arbcp2_cpxdp_shift_bufp1_cx_l[3]), // Templated
			  .arbcp4_cpxdp_grant_bufp3_ca_l(arbcp4_cpxdp_grant_bufp1_ca_l[3]), // Templated
			  .arbcp4_cpxdp_q0_hold_bufp3_ca(arbcp4_cpxdp_q0_hold_bufp1_ca[3]), // Templated
			  .arbcp4_cpxdp_qsel0_bufp3_ca_l(arbcp4_cpxdp_qsel0_bufp1_ca_l[3]), // Templated
			  .arbcp4_cpxdp_qsel1_bufp3_ca(arbcp4_cpxdp_qsel1_bufp1_ca[3]), // Templated
			  .arbcp4_cpxdp_shift_bufp3_cx_l(arbcp4_cpxdp_shift_bufp1_cx_l[3]), // Templated
			  .arbcp6_cpxdp_grant_bufp3_ca_l(arbcp6_cpxdp_grant_bufp1_ca_l[3]), // Templated
			  .arbcp6_cpxdp_q0_hold_bufp3_ca(arbcp6_cpxdp_q0_hold_bufp1_ca[3]), // Templated
			  .arbcp6_cpxdp_qsel0_bufp3_ca_l(arbcp6_cpxdp_qsel0_bufp1_ca_l[3]), // Templated
			  .arbcp6_cpxdp_qsel1_bufp3_ca(arbcp6_cpxdp_qsel1_bufp1_ca[3]), // Templated
			  .arbcp6_cpxdp_shift_bufp3_cx_l(arbcp6_cpxdp_shift_bufp1_cx_l[3])); // Templated
/*   cpx_buf_p4_even AUTO_TEMPLATE(
		 // Outputs
		 .arbcp0_cpxdp_grant_ca	(arbcp1_cpxdp_grant_ca[3]),
		 .arbcp0_cpxdp_q0_hold_ca_l(arbcp1_cpxdp_q0_hold_ca_l[3]),
		 .arbcp0_cpxdp_qsel0_ca	(arbcp1_cpxdp_qsel0_ca[3]),
		 .arbcp0_cpxdp_qsel1_ca_l(arbcp1_cpxdp_qsel1_ca_l[3]),
		 .arbcp0_cpxdp_shift_cx	(arbcp1_cpxdp_shift_cx[3]),
		 .arbcp2_cpxdp_grant_ca	(arbcp3_cpxdp_grant_ca[3]),
		 .arbcp2_cpxdp_q0_hold_ca_l(arbcp3_cpxdp_q0_hold_ca_l[3]),
		 .arbcp2_cpxdp_qsel0_ca	(arbcp3_cpxdp_qsel0_ca[3]),
		 .arbcp2_cpxdp_qsel1_ca_l(arbcp3_cpxdp_qsel1_ca_l[3]),
		 .arbcp2_cpxdp_shift_cx	(arbcp3_cpxdp_shift_cx[3]),
		 .arbcp4_cpxdp_grant_ca	(arbcp5_cpxdp_grant_ca[3]),
		 .arbcp4_cpxdp_q0_hold_ca_l(arbcp5_cpxdp_q0_hold_ca_l[3]),
		 .arbcp4_cpxdp_qsel0_ca	(arbcp5_cpxdp_qsel0_ca[3]),
		 .arbcp4_cpxdp_qsel1_ca_l(arbcp5_cpxdp_qsel1_ca_l[3]),
		 .arbcp4_cpxdp_shift_cx	(arbcp5_cpxdp_shift_cx[3]),
		 .arbcp6_cpxdp_grant_ca	(arbcp7_cpxdp_grant_ca[3]),
		 .arbcp6_cpxdp_q0_hold_ca_l(arbcp7_cpxdp_q0_hold_ca_l[3]),
		 .arbcp6_cpxdp_qsel0_ca	(arbcp7_cpxdp_qsel0_ca[3]),
		 .arbcp6_cpxdp_qsel1_ca_l(arbcp7_cpxdp_qsel1_ca_l[3]),
		 .arbcp6_cpxdp_shift_cx	(arbcp7_cpxdp_shift_cx[3]),
                 // Inputs
	      .arbcp0_cpxdp_grant_bufp3_ca_l(arbcp1_cpxdp_grant_bufp1_ca_l[3]),
	      .arbcp0_cpxdp_q0_hold_bufp3_ca(arbcp1_cpxdp_q0_hold_bufp1_ca[3]),
	      .arbcp0_cpxdp_qsel0_bufp3_ca_l(arbcp1_cpxdp_qsel0_bufp1_ca_l[3]),
	      .arbcp0_cpxdp_qsel1_bufp3_ca(arbcp1_cpxdp_qsel1_bufp1_ca[3]),
	      .arbcp0_cpxdp_shift_bufp3_cx_l(arbcp1_cpxdp_shift_bufp1_cx_l[3]),
	      .arbcp2_cpxdp_grant_bufp3_ca_l(arbcp3_cpxdp_grant_bufp1_ca_l[3]),
	      .arbcp2_cpxdp_q0_hold_bufp3_ca(arbcp3_cpxdp_q0_hold_bufp1_ca[3]),
	      .arbcp2_cpxdp_qsel0_bufp3_ca_l(arbcp3_cpxdp_qsel0_bufp1_ca_l[3]),
	      .arbcp2_cpxdp_qsel1_bufp3_ca(arbcp3_cpxdp_qsel1_bufp1_ca[3]),
	      .arbcp2_cpxdp_shift_bufp3_cx_l(arbcp3_cpxdp_shift_bufp1_cx_l[3]),
	      .arbcp4_cpxdp_grant_bufp3_ca_l(arbcp5_cpxdp_grant_bufp1_ca_l[3]),
	      .arbcp4_cpxdp_q0_hold_bufp3_ca(arbcp5_cpxdp_q0_hold_bufp1_ca[3]),
	      .arbcp4_cpxdp_qsel0_bufp3_ca_l(arbcp5_cpxdp_qsel0_bufp1_ca_l[3]),
	      .arbcp4_cpxdp_qsel1_bufp3_ca(arbcp5_cpxdp_qsel1_bufp1_ca[3]),
	      .arbcp4_cpxdp_shift_bufp3_cx_l(arbcp5_cpxdp_shift_bufp1_cx_l[3]),
	      .arbcp6_cpxdp_grant_bufp3_ca_l(arbcp7_cpxdp_grant_bufp1_ca_l[3]),
	      .arbcp6_cpxdp_q0_hold_bufp3_ca(arbcp7_cpxdp_q0_hold_bufp1_ca[3]),
	      .arbcp6_cpxdp_qsel0_bufp3_ca_l(arbcp7_cpxdp_qsel0_bufp1_ca_l[3]),
	      .arbcp6_cpxdp_qsel1_bufp3_ca(arbcp7_cpxdp_qsel1_bufp1_ca[3]),
	      .arbcp6_cpxdp_shift_bufp3_cx_l(arbcp7_cpxdp_shift_bufp1_cx_l[3]));
*/

cpx_buf_p4_even p4_odd(/*AUTOINST*/
		       // Outputs
		       .arbcp0_cpxdp_grant_ca(arbcp1_cpxdp_grant_ca[3]), // Templated
		       .arbcp0_cpxdp_q0_hold_ca_l(arbcp1_cpxdp_q0_hold_ca_l[3]), // Templated
		       .arbcp0_cpxdp_qsel0_ca(arbcp1_cpxdp_qsel0_ca[3]), // Templated
		       .arbcp0_cpxdp_qsel1_ca_l(arbcp1_cpxdp_qsel1_ca_l[3]), // Templated
		       .arbcp0_cpxdp_shift_cx(arbcp1_cpxdp_shift_cx[3]), // Templated
		       .arbcp2_cpxdp_grant_ca(arbcp3_cpxdp_grant_ca[3]), // Templated
		       .arbcp2_cpxdp_q0_hold_ca_l(arbcp3_cpxdp_q0_hold_ca_l[3]), // Templated
		       .arbcp2_cpxdp_qsel0_ca(arbcp3_cpxdp_qsel0_ca[3]), // Templated
		       .arbcp2_cpxdp_qsel1_ca_l(arbcp3_cpxdp_qsel1_ca_l[3]), // Templated
		       .arbcp2_cpxdp_shift_cx(arbcp3_cpxdp_shift_cx[3]), // Templated
		       .arbcp4_cpxdp_grant_ca(arbcp5_cpxdp_grant_ca[3]), // Templated
		       .arbcp4_cpxdp_q0_hold_ca_l(arbcp5_cpxdp_q0_hold_ca_l[3]), // Templated
		       .arbcp4_cpxdp_qsel0_ca(arbcp5_cpxdp_qsel0_ca[3]), // Templated
		       .arbcp4_cpxdp_qsel1_ca_l(arbcp5_cpxdp_qsel1_ca_l[3]), // Templated
		       .arbcp4_cpxdp_shift_cx(arbcp5_cpxdp_shift_cx[3]), // Templated
		       .arbcp6_cpxdp_grant_ca(arbcp7_cpxdp_grant_ca[3]), // Templated
		       .arbcp6_cpxdp_q0_hold_ca_l(arbcp7_cpxdp_q0_hold_ca_l[3]), // Templated
		       .arbcp6_cpxdp_qsel0_ca(arbcp7_cpxdp_qsel0_ca[3]), // Templated
		       .arbcp6_cpxdp_qsel1_ca_l(arbcp7_cpxdp_qsel1_ca_l[3]), // Templated
		       .arbcp6_cpxdp_shift_cx(arbcp7_cpxdp_shift_cx[3]), // Templated
		       // Inputs
		       .arbcp0_cpxdp_grant_bufp3_ca_l(arbcp1_cpxdp_grant_bufp1_ca_l[3]), // Templated
		       .arbcp0_cpxdp_q0_hold_bufp3_ca(arbcp1_cpxdp_q0_hold_bufp1_ca[3]), // Templated
		       .arbcp0_cpxdp_qsel0_bufp3_ca_l(arbcp1_cpxdp_qsel0_bufp1_ca_l[3]), // Templated
		       .arbcp0_cpxdp_qsel1_bufp3_ca(arbcp1_cpxdp_qsel1_bufp1_ca[3]), // Templated
		       .arbcp0_cpxdp_shift_bufp3_cx_l(arbcp1_cpxdp_shift_bufp1_cx_l[3]), // Templated
		       .arbcp2_cpxdp_grant_bufp3_ca_l(arbcp3_cpxdp_grant_bufp1_ca_l[3]), // Templated
		       .arbcp2_cpxdp_q0_hold_bufp3_ca(arbcp3_cpxdp_q0_hold_bufp1_ca[3]), // Templated
		       .arbcp2_cpxdp_qsel0_bufp3_ca_l(arbcp3_cpxdp_qsel0_bufp1_ca_l[3]), // Templated
		       .arbcp2_cpxdp_qsel1_bufp3_ca(arbcp3_cpxdp_qsel1_bufp1_ca[3]), // Templated
		       .arbcp2_cpxdp_shift_bufp3_cx_l(arbcp3_cpxdp_shift_bufp1_cx_l[3]), // Templated
		       .arbcp4_cpxdp_grant_bufp3_ca_l(arbcp5_cpxdp_grant_bufp1_ca_l[3]), // Templated
		       .arbcp4_cpxdp_q0_hold_bufp3_ca(arbcp5_cpxdp_q0_hold_bufp1_ca[3]), // Templated
		       .arbcp4_cpxdp_qsel0_bufp3_ca_l(arbcp5_cpxdp_qsel0_bufp1_ca_l[3]), // Templated
		       .arbcp4_cpxdp_qsel1_bufp3_ca(arbcp5_cpxdp_qsel1_bufp1_ca[3]), // Templated
		       .arbcp4_cpxdp_shift_bufp3_cx_l(arbcp5_cpxdp_shift_bufp1_cx_l[3]), // Templated
		       .arbcp6_cpxdp_grant_bufp3_ca_l(arbcp7_cpxdp_grant_bufp1_ca_l[3]), // Templated
		       .arbcp6_cpxdp_q0_hold_bufp3_ca(arbcp7_cpxdp_q0_hold_bufp1_ca[3]), // Templated
		       .arbcp6_cpxdp_qsel0_bufp3_ca_l(arbcp7_cpxdp_qsel0_bufp1_ca_l[3]), // Templated
		       .arbcp6_cpxdp_qsel1_bufp3_ca(arbcp7_cpxdp_qsel1_bufp1_ca[3]), // Templated
		       .arbcp6_cpxdp_shift_bufp3_cx_l(arbcp7_cpxdp_shift_bufp1_cx_l[3])); // Templated
/*
    cpx_datacx2_ff AUTO_TEMPLATE(
		       // Outputs
		      .cpx_spc_data_cx2	(cpx_spc@_data_cx2[`CPX_WIDTH-1:0]),
		      .cpx_spc_data_rdy_cx2(cpx_spc@_data_rdy_cx2),
		      .so		(ff0_so_1),
		     // Inputs
                      .se(se_buf4_top),
		      .cpx_spc_data_cx_l(cpx_spc@_data_cx_l[`CPX_WIDTH-1:0]),
		      .cpx_spc_data_rdy_cx(cpx_spc@_data_rdy_bufp0_cx),
		      .clk		(clk),
		      .si		(ff1_so_1));

 
 */
   cpx_datacx2_ff ff0(/*AUTOINST*/
		      // Outputs
		      .cpx_spc_data_cx2	(cpx_spc0_data_cx2[`CPX_WIDTH-1:0]), // Templated
		      .cpx_spc_data_rdy_cx2(cpx_spc0_data_rdy_cx2), // Templated
		      .so		(ff0_so_1),		 // Templated
		      // Inputs
		      .cpx_spc_data_cx_l(cpx_spc0_data_cx_l[`CPX_WIDTH-1:0]), // Templated
		      .cpx_spc_data_rdy_cx(cpx_spc0_data_rdy_bufp0_cx), // Templated
		      .rclk		(rclk),
		      .si		(ff1_so_1),		 // Templated
		      .se		(se_buf4_top));		 // Templated
/*
    cpx_datacx2_ff AUTO_TEMPLATE(
		       // Outputs
		      .cpx_spc_data_cx2	(cpx_spc@_data_cx2[`CPX_WIDTH-1:0]),
		      .cpx_spc_data_rdy_cx2(cpx_spc@_data_rdy_cx2),
		      .so		(ff1_so_1),
		     // Inputs
                      .se(se_buf4_bottom),
		      .cpx_spc_data_cx_l(cpx_spc@_data_cx_l[`CPX_WIDTH-1:0]),
		      .cpx_spc_data_rdy_cx(cpx_spc@_data_rdy_bufp1_cx),
		      .clk		(clk),
		      .si		(ff3_so_1));

 
 */
   cpx_datacx2_ff ff1(/*AUTOINST*/
		      // Outputs
		      .cpx_spc_data_cx2	(cpx_spc1_data_cx2[`CPX_WIDTH-1:0]), // Templated
		      .cpx_spc_data_rdy_cx2(cpx_spc1_data_rdy_cx2), // Templated
		      .so		(ff1_so_1),		 // Templated
		      // Inputs
		      .cpx_spc_data_cx_l(cpx_spc1_data_cx_l[`CPX_WIDTH-1:0]), // Templated
		      .cpx_spc_data_rdy_cx(cpx_spc1_data_rdy_bufp1_cx), // Templated
		      .rclk		(rclk),
		      .si		(ff3_so_1),		 // Templated
		      .se		(se_buf4_bottom));	 // Templated
/*
    cpx_datacx2_ff AUTO_TEMPLATE(
		       // Outputs
		      .cpx_spc_data_cx2	(cpx_spc@_data_cx2[`CPX_WIDTH-1:0]),
		      .cpx_spc_data_rdy_cx2(cpx_spc@_data_rdy_cx2),
		      .so		(ff2_so_1),
		     // Inputs
                      .se(se_buf4_top),
		      .cpx_spc_data_cx_l(cpx_spc@_data_cx_l[`CPX_WIDTH-1:0]),
		      .cpx_spc_data_rdy_cx(cpx_spc@_data_rdy_bufp1_cx),
		      .clk		(clk),
		      .si		(ff4_so_1));

 
 */
   cpx_datacx2_ff ff2(/*AUTOINST*/
		      // Outputs
		      .cpx_spc_data_cx2	(cpx_spc2_data_cx2[`CPX_WIDTH-1:0]), // Templated
		      .cpx_spc_data_rdy_cx2(cpx_spc2_data_rdy_cx2), // Templated
		      .so		(ff2_so_1),		 // Templated
		      // Inputs
		      .cpx_spc_data_cx_l(cpx_spc2_data_cx_l[`CPX_WIDTH-1:0]), // Templated
		      .cpx_spc_data_rdy_cx(cpx_spc2_data_rdy_bufp1_cx), // Templated
		      .rclk		(rclk),
		      .si		(ff4_so_1),		 // Templated
		      .se		(se_buf4_top));		 // Templated
/*
    cpx_datacx2_ff AUTO_TEMPLATE(
		       // Outputs
		      .cpx_spc_data_cx2	(cpx_spc@_data_cx2[`CPX_WIDTH-1:0]),
		      .cpx_spc_data_rdy_cx2(cpx_spc@_data_rdy_cx2),
		      .so		(ff3_so_1),
		     // Inputs
                      .se(se_buf4_bottom),
		      .cpx_spc_data_cx_l(cpx_spc@_data_cx_l[`CPX_WIDTH-1:0]),
		      .cpx_spc_data_rdy_cx(cpx_spc@_data_rdy_cx),
		      .clk		(clk),
		      .si		(ff2_so_1));

 
 */
   cpx_datacx2_ff ff3(/*AUTOINST*/
		      // Outputs
		      .cpx_spc_data_cx2	(cpx_spc3_data_cx2[`CPX_WIDTH-1:0]), // Templated
		      .cpx_spc_data_rdy_cx2(cpx_spc3_data_rdy_cx2), // Templated
		      .so		(ff3_so_1),		 // Templated
		      // Inputs
		      .cpx_spc_data_cx_l(cpx_spc3_data_cx_l[`CPX_WIDTH-1:0]), // Templated
		      .cpx_spc_data_rdy_cx(cpx_spc3_data_rdy_cx), // Templated
		      .rclk		(rclk),
		      .si		(ff2_so_1),		 // Templated
		      .se		(se_buf4_bottom));	 // Templated
/*
    cpx_datacx2_ff AUTO_TEMPLATE(
		       // Outputs
		      .cpx_spc_data_cx2	(cpx_spc@_data_cx2[`CPX_WIDTH-1:0]),
		      .cpx_spc_data_rdy_cx2(cpx_spc@_data_rdy_cx2),
		      .so		(ff4_so_1),
		     // Inputs
                      .se(se_buf2_top),
		      .cpx_spc_data_cx_l(cpx_spc@_data_cx_l[`CPX_WIDTH-1:0]),
		      .cpx_spc_data_rdy_cx(cpx_spc@_data_rdy_cx),
		      .clk		(clk),
		      .si		(ff5_so_1));

 
 */
   cpx_datacx2_ff ff4(/*AUTOINST*/
		      // Outputs
		      .cpx_spc_data_cx2	(cpx_spc4_data_cx2[`CPX_WIDTH-1:0]), // Templated
		      .cpx_spc_data_rdy_cx2(cpx_spc4_data_rdy_cx2), // Templated
		      .so		(ff4_so_1),		 // Templated
		      // Inputs
		      .cpx_spc_data_cx_l(cpx_spc4_data_cx_l[`CPX_WIDTH-1:0]), // Templated
		      .cpx_spc_data_rdy_cx(cpx_spc4_data_rdy_cx), // Templated
		      .rclk		(rclk),
		      .si		(ff5_so_1),		 // Templated
		      .se		(se_buf2_top));		 // Templated
/*
    cpx_datacx2_ff AUTO_TEMPLATE(
		       // Outputs
		      .cpx_spc_data_cx2	(cpx_spc@_data_cx2[`CPX_WIDTH-1:0]),
		      .cpx_spc_data_rdy_cx2(cpx_spc@_data_rdy_cx2),
		      .so		(ff5_so_1),
		     // Inputs
                      .se(se_buf2_bottom),
		      .cpx_spc_data_cx_l(cpx_spc@_data_cx_l[`CPX_WIDTH-1:0]),
		      .cpx_spc_data_rdy_cx(cpx_spc@_data_rdy_bufp3_cx),
		      .clk		(clk),
		      .si		(ff6_so_1));

 
 */
   cpx_datacx2_ff ff5(/*AUTOINST*/
		      // Outputs
		      .cpx_spc_data_cx2	(cpx_spc5_data_cx2[`CPX_WIDTH-1:0]), // Templated
		      .cpx_spc_data_rdy_cx2(cpx_spc5_data_rdy_cx2), // Templated
		      .so		(ff5_so_1),		 // Templated
		      // Inputs
		      .cpx_spc_data_cx_l(cpx_spc5_data_cx_l[`CPX_WIDTH-1:0]), // Templated
		      .cpx_spc_data_rdy_cx(cpx_spc5_data_rdy_bufp3_cx), // Templated
		      .rclk		(rclk),
		      .si		(ff6_so_1),		 // Templated
		      .se		(se_buf2_bottom));	 // Templated
/*
    cpx_datacx2_ff AUTO_TEMPLATE(
		       // Outputs
		      .cpx_spc_data_cx2	(cpx_spc@_data_cx2[`CPX_WIDTH-1:0]),
		      .cpx_spc_data_rdy_cx2(cpx_spc@_data_rdy_cx2),
		      .so		(ff6_so_1),
		     // Inputs
                      .se(se_buf2_top),
		      .cpx_spc_data_cx_l(cpx_spc@_data_cx_l[`CPX_WIDTH-1:0]),
		      .cpx_spc_data_rdy_cx(cpx_spc@_data_rdy_bufp3_cx),
		      .clk		(clk),
		      .si		(ff7_so_1));

 
 */
   cpx_datacx2_ff ff6(/*AUTOINST*/
		      // Outputs
		      .cpx_spc_data_cx2	(cpx_spc6_data_cx2[`CPX_WIDTH-1:0]), // Templated
		      .cpx_spc_data_rdy_cx2(cpx_spc6_data_rdy_cx2), // Templated
		      .so		(ff6_so_1),		 // Templated
		      // Inputs
		      .cpx_spc_data_cx_l(cpx_spc6_data_cx_l[`CPX_WIDTH-1:0]), // Templated
		      .cpx_spc_data_rdy_cx(cpx_spc6_data_rdy_bufp3_cx), // Templated
		      .rclk		(rclk),
		      .si		(ff7_so_1),		 // Templated
		      .se		(se_buf2_top));		 // Templated
/*
    cpx_datacx2_ff AUTO_TEMPLATE(
		       // Outputs
		      .cpx_spc_data_cx2	(cpx_spc@_data_cx2[`CPX_WIDTH-1:0]),
		      .cpx_spc_data_rdy_cx2(cpx_spc@_data_rdy_cx2),
		      .so		(ff7_so_1),
		     // Inputs
                      .se(se_buf2_bottom),
		      .cpx_spc_data_cx_l(cpx_spc@_data_cx_l[`CPX_WIDTH-1:0]),
		      .cpx_spc_data_rdy_cx(cpx_spc@_data_rdy_bufp4_cx),
		      .clk		(clk),
		      .si		(si_1));

 
 */
   cpx_datacx2_ff ff7(/*AUTOINST*/
		      // Outputs
		      .cpx_spc_data_cx2	(cpx_spc7_data_cx2[`CPX_WIDTH-1:0]), // Templated
		      .cpx_spc_data_rdy_cx2(cpx_spc7_data_rdy_cx2), // Templated
		      .so		(ff7_so_1),		 // Templated
		      // Inputs
		      .cpx_spc_data_cx_l(cpx_spc7_data_cx_l[`CPX_WIDTH-1:0]), // Templated
		      .cpx_spc_data_rdy_cx(cpx_spc7_data_rdy_bufp4_cx), // Templated
		      .rclk		(rclk),
		      .si		(si_1),			 // Templated
		      .se		(se_buf2_bottom));	 // Templated
/*
    io_cpx_reqdata_ff AUTO_TEMPLATE(
		       // Outputs
		      .scan_out		(io_cpx_reqdata_ff_so_1),
		     // Inputs
                      .se(se_buf3_top),
		      .scan_in		(ff_io_grant_so_1));
 
 */

    io_cpx_reqdata_ff ff_io(/*AUTOINST*/
			    // Outputs
			    .io_cpx_data_ca2(io_cpx_data_ca2[`CPX_WIDTH-1:0]),
			    .io_cpx_req_cq2(io_cpx_req_cq2[7:0]),
			    .scan_out	(io_cpx_reqdata_ff_so_1), // Templated
			    // Inputs
			    .io_cpx_data_ca(io_cpx_data_ca[`CPX_WIDTH-1:0]),
			    .io_cpx_req_cq(io_cpx_req_cq[7:0]),
			    .rclk	(rclk),
			    .scan_in	(ff_io_grant_so_1),	 // Templated
			    .se		(se_buf3_top));		 // Templated
/*
    cpx_io_grant_ff AUTO_TEMPLATE(
		       // Outputs
		      .so		(ff_io_grant_so_1),
		     // Inputs
                      .se(se_buf3_top),
		      .si		(ff0_so_1));
 
 */

   cpx_io_grant_ff ff_io_grant(/*AUTOINST*/
			       // Outputs
			       .cpx_io_grant_cx2(cpx_io_grant_cx2[7:0]),
			       .so	(ff_io_grant_so_1),	 // Templated
			       // Inputs
			       .cpx_io_grant_cx(cpx_io_grant_cx[7:0]),
			       .rclk	(rclk),
			       .si	(ff0_so_1),		 // Templated
			       .se	(se_buf3_top));		 // Templated
/*
   cpx_databuf_ca AUTO_TEMPLATE(
			.sctag_cpx_data_buf_pa(fp_cpx_data_buf_ca[`CPX_WIDTH-1:0]),
			.sctag_cpx_data_pa(fp_cpx_data_buf1_ca[`CPX_WIDTH-1:0]));
*/
   cpx_databuf_ca buf_fp_cpx_data(/*AUTOINST*/
				  // Outputs
				  .sctag_cpx_data_buf_pa(fp_cpx_data_buf_ca[`CPX_WIDTH-1:0]), // Templated
				  // Inputs
				  .sctag_cpx_data_pa(fp_cpx_data_buf1_ca[`CPX_WIDTH-1:0])); // Templated
/*
   cpx_databuf_ca2 AUTO_TEMPLATE(
			.sctag_cpx_data_buf_pa(fp_cpx_data_buf1_ca[`CPX_WIDTH-1:0]),
			.sctag_cpx_data_pa(fp_cpx_data_ca[`CPX_WIDTH-1:0]));
*/
   cpx_databuf_ca2 buf2_fp_cpx_data(/*AUTOINST*/
				    // Outputs
				    .sctag_cpx_data_buf_pa(fp_cpx_data_buf1_ca[`CPX_WIDTH-1:0]), // Templated
				    // Inputs
				    .sctag_cpx_data_pa(fp_cpx_data_ca[`CPX_WIDTH-1:0])); // Templated
/*
   cpx_databuf_ca AUTO_TEMPLATE(
			.sctag_cpx_data_buf_pa(sctag@_cpx_data_buf_ca[`CPX_WIDTH-1:0]),
			.sctag_cpx_data_pa(sctag@_cpx_data_ca[`CPX_WIDTH-1:0]));
*/
   cpx_databuf_ca buf_sctag0_cpx_data(/*AUTOINST*/
				      // Outputs
				      .sctag_cpx_data_buf_pa(sctag0_cpx_data_buf_ca[`CPX_WIDTH-1:0]), // Templated
				      // Inputs
				      .sctag_cpx_data_pa(sctag0_cpx_data_ca[`CPX_WIDTH-1:0])); // Templated
   cpx_databuf_ca buf_sctag1_cpx_data(/*AUTOINST*/
				      // Outputs
				      .sctag_cpx_data_buf_pa(sctag1_cpx_data_buf_ca[`CPX_WIDTH-1:0]), // Templated
				      // Inputs
				      .sctag_cpx_data_pa(sctag1_cpx_data_ca[`CPX_WIDTH-1:0])); // Templated
   cpx_databuf_ca buf_sctag2_cpx_data(/*AUTOINST*/
				      // Outputs
				      .sctag_cpx_data_buf_pa(sctag2_cpx_data_buf_ca[`CPX_WIDTH-1:0]), // Templated
				      // Inputs
				      .sctag_cpx_data_pa(sctag2_cpx_data_ca[`CPX_WIDTH-1:0])); // Templated
   cpx_databuf_ca buf_sctag3_cpx_data(/*AUTOINST*/
				      // Outputs
				      .sctag_cpx_data_buf_pa(sctag3_cpx_data_buf_ca[`CPX_WIDTH-1:0]), // Templated
				      // Inputs
				      .sctag_cpx_data_pa(sctag3_cpx_data_ca[`CPX_WIDTH-1:0])); // Templated
/*
   cpx_databuf_ca AUTO_TEMPLATE(
			.sctag_cpx_data_buf_pa(io_cpx_data_buf1_ca2[`CPX_WIDTH-1:0]),
			.sctag_cpx_data_pa(io_cpx_data_ca2[`CPX_WIDTH-1:0]));
*/
   cpx_databuf_ca buf1_io_cpx_data(/*AUTOINST*/
				   // Outputs
				   .sctag_cpx_data_buf_pa(io_cpx_data_buf1_ca2[`CPX_WIDTH-1:0]), // Templated
				   // Inputs
				   .sctag_cpx_data_pa(io_cpx_data_ca2[`CPX_WIDTH-1:0])); // Templated
   /* cpx_buf_io AUTO_TEMPLATE(
                  // Outputs
                  .cpx_io_grant_bufio_ca(cpx_io_grant_buf1_io_ca[7:0]),
                  .io_cpx_req_bufio_cq_l(io_cpx_req_buf1_io_cq[7:0]),
                  // Inputs
                  .cpx_io_grant_ca(cpx_io_grant_ca[7:0]),
                  .io_cpx_req_cq(io_cpx_req_bufpt_cq_l[7:0]));
  */

      cpx_buf_io  buf1_io(/*AUTOINST*/
			  // Outputs
			  .cpx_io_grant_bufio_ca(cpx_io_grant_buf1_io_ca[7:0]), // Templated
			  .io_cpx_req_bufio_cq_l(io_cpx_req_buf1_io_cq[7:0]), // Templated
			  // Inputs
			  .cpx_io_grant_ca(cpx_io_grant_ca[7:0]), // Templated
			  .io_cpx_req_cq(io_cpx_req_bufpt_cq_l[7:0])); // Templated
endmodule

   
// Local Variables:
// verilog-library-directories:("." "../../../../../common/rtl" "../../common/rtl")
// End:
