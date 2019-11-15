// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: pcx_buf_top.v
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
//
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


  module pcx_buf_top(/*AUTOARG*/
   // Outputs
   spc7_pcx_req_bufp3_pq, spc7_pcx_data_buf_pa, 
   spc7_pcx_atom_bufp3_pq, spc6_pcx_req_bufp3_pq, 
   spc6_pcx_data_buf_pa, spc6_pcx_atom_bufp3_pq, 
   spc5_pcx_req_bufp3_pq, spc5_pcx_data_buf_pa, 
   spc5_pcx_atom_bufp3_pq, spc4_pcx_req_bufp1_pq, 
   spc4_pcx_data_buf_pa, spc4_pcx_atom_bufp1_pq, 
   spc3_pcx_req_bufp1_pq, spc3_pcx_data_buf_pa, 
   spc3_pcx_atom_bufp1_pq, spc2_pcx_req_bufp1_pq, 
   spc2_pcx_data_buf_pa, spc2_pcx_atom_bufp1_pq, 
   spc1_pcx_req_bufp1_pq, spc1_pcx_data_buf_pa, 
   spc1_pcx_atom_bufp1_pq, spc0_pcx_req_bufp1_pq, 
   spc0_pcx_data_buf_pa, spc0_pcx_atom_bufp1_pq, 
   sctag1_pcx_stall_bufp1_pq, scache3_pcx_stall_bufp3_pq, 
   scache0_pcx_stall_bufp1_pq, pcx_spc7_grant_px, pcx_spc6_grant_px, 
   pcx_spc5_grant_px, pcx_spc4_grant_px, pcx_spc3_grant_px, 
   pcx_spc2_grant_px, pcx_spc1_grant_px, pcx_spc0_grant_px, 
   pcx_scache3_data_rdy_px, pcx_scache3_data_px2, 
   pcx_scache3_atom_px1, pcx_scache2_data_rdy_px, 
   pcx_scache2_data_px2, pcx_scache2_dat_px2_so_1, 
   pcx_scache2_atom_px1, pcx_scache1_data_rdy_px, 
   pcx_scache1_data_px2, pcx_scache1_dat_px2_so_1, 
   pcx_scache1_atom_px1, pcx_scache0_data_rdy_px, 
   pcx_scache0_data_px2, pcx_scache0_dat_px2_so_1, 
   pcx_scache0_atom_px1, pcx_iodata_px2_so_1, pcx_io_data_rdy_px2, 
   pcx_io_data_px2, pcx_fpio_data_rdy_px2, pcx_fpio_data_px2, 
   pcx_buf_top_pt0_so_0, io_pcx_stall_bufp3_pq, arst_l_buf_fpio_inff, 
   arbpc4_pcxdp_shift_px, arbpc4_pcxdp_qsel1_pa_l, 
   arbpc4_pcxdp_qsel0_pa, arbpc4_pcxdp_q0_hold_pa_l, 
   arbpc4_pcxdp_grant_pa, arbpc3_pcxdp_shift_px, 
   arbpc3_pcxdp_qsel1_pa_l, arbpc3_pcxdp_qsel0_pa, 
   arbpc3_pcxdp_q0_hold_pa_l, arbpc3_pcxdp_grant_pa, 
   arbpc2_pcxdp_shift_px, arbpc2_pcxdp_qsel1_pa_l, 
   arbpc2_pcxdp_qsel0_pa, arbpc2_pcxdp_q0_hold_pa_l, 
   arbpc2_pcxdp_grant_pa, arbpc1_pcxdp_shift_px, 
   arbpc1_pcxdp_qsel1_pa_l, arbpc1_pcxdp_qsel0_pa, 
   arbpc1_pcxdp_q0_hold_pa_l, arbpc1_pcxdp_grant_pa, 
   arbpc0_pcxdp_shift_px, arbpc0_pcxdp_qsel1_pa_l, 
   arbpc0_pcxdp_qsel0_pa, arbpc0_pcxdp_q0_hold_pa_l, 
   arbpc0_pcxdp_grant_pa, 
   // Inputs
   spc7_pcx_req_pq, spc7_pcx_atom_pq, spc6_pcx_req_pq, 
   spc6_pcx_atom_pq, spc5_pcx_req_pq, spc5_pcx_atom_pq, 
   spc4_pcx_req_pq, spc4_pcx_atom_pq, spc3_pcx_req_pq, 
   spc3_pcx_atom_pq, spc2_pcx_req_pq, spc2_pcx_atom_pq, 
   spc1_pcx_req_pq, spc1_pcx_atom_pq, spc0_pcx_req_pq, 
   spc0_pcx_atom_pq, si_1, si_0, se_buf5_top, se_buf5_bottom, 
   se_buf4_top, se_buf4_bottom, se_buf3_top, se_buf3_middle, 
   se_buf3_bottom, se_buf2_top, se_buf2_bottom, se_buf1_top, 
   se_buf1_bottom, se_buf0_middle, sctag1_pcx_stall_pq, 
   scache3_pcx_stall_pq, scache0_pcx_stall_pq, rclk, pt1_so_1, 
   pcx_spc7_grant_pa, pcx_spc6_grant_pa, pcx_spc5_grant_pa, 
   pcx_spc4_grant_pa, pcx_spc3_grant_pa, pcx_spc2_grant_pa, 
   pcx_spc1_grant_pa, pcx_spc0_grant_pa, pcx_scache3_data_rdy_arb_px, 
   pcx_scache3_data_px_l, pcx_scache3_atom_px, 
   pcx_scache2_data_rdy_arb_px, pcx_scache2_data_px_l, 
   pcx_scache2_atom_px, pcx_scache1_data_rdy_arb_px, 
   pcx_scache1_data_px_l, pcx_scache1_atom_px, 
   pcx_scache0_data_rdy_arb_px, pcx_scache0_data_px_l, 
   pcx_scache0_atom_px, pcx_fpio_data_rdy_arb_px, pcx_fpio_data_px_l, 
   io_pcx_stall_pq, cpx_buf_top_pt0_so_1, cmp_arst_l, 
   ccx_clk_hdr_so_1, arbpc4_pcxdp_shift_arbbf_px, 
   arbpc4_pcxdp_qsel1_arbbf_pa_l, arbpc4_pcxdp_qsel0_arbbf_pa, 
   arbpc4_pcxdp_q0_hold_arbbf_pa_l, arbpc4_pcxdp_grant_arbbf_pa, 
   arbpc3_pcxdp_shift_arbbf_px, arbpc3_pcxdp_qsel1_arbbf_pa_l, 
   arbpc3_pcxdp_qsel0_arbbf_pa, arbpc3_pcxdp_q0_hold_arbbf_pa_l, 
   arbpc3_pcxdp_grant_arbbf_pa, arbpc2_pcxdp_shift_arbbf_px, 
   arbpc2_pcxdp_qsel1_arbbf_pa_l, arbpc2_pcxdp_qsel0_arbbf_pa, 
   arbpc2_pcxdp_q0_hold_arbbf_pa_l, arbpc2_pcxdp_grant_arbbf_pa, 
   arbpc1_pcxdp_shift_arbbf_px, arbpc1_pcxdp_qsel1_arbbf_pa_l, 
   arbpc1_pcxdp_qsel0_arbbf_pa, arbpc1_pcxdp_q0_hold_arbbf_pa_l, 
   arbpc1_pcxdp_grant_arbbf_pa, arbpc0_pcxdp_shift_arbbf_px, 
   arbpc0_pcxdp_qsel1_arbbf_pa_l, arbpc0_pcxdp_qsel0_arbbf_pa, 
   arbpc0_pcxdp_q0_hold_arbbf_pa_l, arbpc0_pcxdp_grant_arbbf_pa, 
   spc1_pcx_data_pa, spc3_pcx_data_pa, spc5_pcx_data_pa, 
   spc7_pcx_data_pa, spc0_pcx_data_pa, spc2_pcx_data_pa, 
   spc4_pcx_data_pa, spc6_pcx_data_pa
   );

   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output [7:0]		arbpc0_pcxdp_grant_pa;	// From pm3_even of pcx_buf_pm_even.v, ...
   output [7:0]		arbpc0_pcxdp_q0_hold_pa_l;// From pm3_even of pcx_buf_pm_even.v, ...
   output [7:0]		arbpc0_pcxdp_qsel0_pa;	// From pm3_even of pcx_buf_pm_even.v, ...
   output [7:0]		arbpc0_pcxdp_qsel1_pa_l;// From pm3_even of pcx_buf_pm_even.v, ...
   output [7:0]		arbpc0_pcxdp_shift_px;	// From pm3_even of pcx_buf_pm_even.v, ...
   output [7:0]		arbpc1_pcxdp_grant_pa;	// From pm3_odd of pcx_buf_pm_odd.v, ...
   output [7:0]		arbpc1_pcxdp_q0_hold_pa_l;// From pm3_odd of pcx_buf_pm_odd.v, ...
   output [7:0]		arbpc1_pcxdp_qsel0_pa;	// From pm3_odd of pcx_buf_pm_odd.v, ...
   output [7:0]		arbpc1_pcxdp_qsel1_pa_l;// From pm3_odd of pcx_buf_pm_odd.v, ...
   output [7:0]		arbpc1_pcxdp_shift_px;	// From pm3_odd of pcx_buf_pm_odd.v, ...
   output [7:0]		arbpc2_pcxdp_grant_pa;	// From pm3_even of pcx_buf_pm_even.v, ...
   output [7:0]		arbpc2_pcxdp_q0_hold_pa_l;// From pm3_even of pcx_buf_pm_even.v, ...
   output [7:0]		arbpc2_pcxdp_qsel0_pa;	// From pm3_even of pcx_buf_pm_even.v, ...
   output [7:0]		arbpc2_pcxdp_qsel1_pa_l;// From pm3_even of pcx_buf_pm_even.v, ...
   output [7:0]		arbpc2_pcxdp_shift_px;	// From pm3_even of pcx_buf_pm_even.v, ...
   output [7:0]		arbpc3_pcxdp_grant_pa;	// From pm3_odd of pcx_buf_pm_odd.v, ...
   output [7:0]		arbpc3_pcxdp_q0_hold_pa_l;// From pm3_odd of pcx_buf_pm_odd.v, ...
   output [7:0]		arbpc3_pcxdp_qsel0_pa;	// From pm3_odd of pcx_buf_pm_odd.v, ...
   output [7:0]		arbpc3_pcxdp_qsel1_pa_l;// From pm3_odd of pcx_buf_pm_odd.v, ...
   output [7:0]		arbpc3_pcxdp_shift_px;	// From pm3_odd of pcx_buf_pm_odd.v, ...
   output [7:0]		arbpc4_pcxdp_grant_pa;	// From pm3_odd of pcx_buf_pm_odd.v, ...
   output [7:0]		arbpc4_pcxdp_q0_hold_pa_l;// From pm3_odd of pcx_buf_pm_odd.v, ...
   output [7:0]		arbpc4_pcxdp_qsel0_pa;	// From pm3_odd of pcx_buf_pm_odd.v, ...
   output [7:0]		arbpc4_pcxdp_qsel1_pa_l;// From pm3_odd of pcx_buf_pm_odd.v, ...
   output [7:0]		arbpc4_pcxdp_shift_px;	// From pm3_odd of pcx_buf_pm_odd.v, ...
   output		arst_l_buf_fpio_inff;	// From buffpio_inff of pcx_buf_fpio.v
   output		io_pcx_stall_bufp3_pq;	// From pm4 of pcx_buf_pm.v
   output		pcx_buf_top_pt0_so_0;	// From pt0 of pcx_buf_pt.v
   output [`PCX_WIDTH-1:0]pcx_fpio_data_px2;	// From buffpio of pcx_buf_fpio.v
   output		pcx_fpio_data_rdy_px2;	// From buffpio of pcx_buf_fpio.v
   output [`PCX_WIDTH-1:0]pcx_io_data_px2;	// From bufio_outff of pcx_databuf_pa.v
   output		pcx_io_data_rdy_px2;	// From bufio_outff of pcx_databuf_pa.v
   output		pcx_iodata_px2_so_1;	// From pcx_iodata_px2 of pcx_data_px2.v
   output		pcx_scache0_atom_px1;	// From buf0_4 of pcx_buf_scache.v
   output		pcx_scache0_dat_px2_so_1;// From pcx_scache0_dat_px2 of pcx_data_px2.v
   output [`PCX_WIDTH-1:0]pcx_scache0_data_px2;	// From pcx_scache0_dat_px2 of pcx_data_px2.v
   output		pcx_scache0_data_rdy_px;// From buf0_3 of pcx_buf_scache.v
   output		pcx_scache1_atom_px1;	// From buf1_4 of pcx_buf_scache.v
   output		pcx_scache1_dat_px2_so_1;// From pcx_scache1_dat_px2 of pcx_data_px2.v
   output [`PCX_WIDTH-1:0]pcx_scache1_data_px2;	// From pcx_scache1_dat_px2 of pcx_data_px2.v
   output		pcx_scache1_data_rdy_px;// From buf1_3 of pcx_buf_scache.v
   output		pcx_scache2_atom_px1;	// From buf2_4 of pcx_buf_scache.v
   output		pcx_scache2_dat_px2_so_1;// From pcx_scache2_dat_px2 of pcx_data_px2.v
   output [`PCX_WIDTH-1:0]pcx_scache2_data_px2;	// From pcx_scache2_dat_px2 of pcx_data_px2.v
   output		pcx_scache2_data_rdy_px;// From buf2_3 of pcx_buf_scache.v
   output		pcx_scache3_atom_px1;	// From buf3_4 of pcx_buf_scache.v
   output [`PCX_WIDTH-1:0]pcx_scache3_data_px2;	// From pcx_scache3_dat_px2 of pcx_data_px2.v
   output		pcx_scache3_data_rdy_px;// From buf3_3 of pcx_buf_scache.v
   output [4:0]		pcx_spc0_grant_px;	// From pt0 of pcx_buf_pt.v
   output [4:0]		pcx_spc1_grant_px;	// From pt1 of pcx_buf_pt.v
   output [4:0]		pcx_spc2_grant_px;	// From pt2 of pcx_buf_pt.v
   output [4:0]		pcx_spc3_grant_px;	// From pt3 of pcx_buf_pt1.v
   output [4:0]		pcx_spc4_grant_px;	// From pt4 of pcx_buf_pt1.v
   output [4:0]		pcx_spc5_grant_px;	// From pt5 of pcx_buf_pt.v
   output [4:0]		pcx_spc6_grant_px;	// From pt6 of pcx_buf_pt.v
   output [4:0]		pcx_spc7_grant_px;	// From pt7 of pcx_buf_pt.v
   output		scache0_pcx_stall_bufp1_pq;// From p1 of pcx_buf_p1.v
   output		scache3_pcx_stall_bufp3_pq;// From p3 of pcx_buf_p3.v
   output		sctag1_pcx_stall_bufp1_pq;// From p1 of pcx_buf_p1.v
   output		spc0_pcx_atom_bufp1_pq;	// From p1 of pcx_buf_p1.v
   output [`PCX_WIDTH-1:0]spc0_pcx_data_buf_pa;	// From pcx_databuf_pa0 of pcx_databuf_pa.v
   output [4:0]		spc0_pcx_req_bufp1_pq;	// From p1 of pcx_buf_p1.v
   output		spc1_pcx_atom_bufp1_pq;	// From p1 of pcx_buf_p1.v
   output [`PCX_WIDTH-1:0]spc1_pcx_data_buf_pa;	// From pcx_databuf_pa1 of pcx_databuf_pa.v
   output [4:0]		spc1_pcx_req_bufp1_pq;	// From p1 of pcx_buf_p1.v
   output		spc2_pcx_atom_bufp1_pq;	// From p1 of pcx_buf_p1.v
   output [`PCX_WIDTH-1:0]spc2_pcx_data_buf_pa;	// From pcx_databuf_pa2 of pcx_databuf_pa.v
   output [4:0]		spc2_pcx_req_bufp1_pq;	// From p1 of pcx_buf_p1.v
   output		spc3_pcx_atom_bufp1_pq;	// From p1 of pcx_buf_p1.v
   output [`PCX_WIDTH-1:0]spc3_pcx_data_buf_pa;	// From pcx_databuf_pa3 of pcx_databuf_pa.v
   output [4:0]		spc3_pcx_req_bufp1_pq;	// From p1 of pcx_buf_p1.v
   output		spc4_pcx_atom_bufp1_pq;	// From p1 of pcx_buf_p1.v
   output [`PCX_WIDTH-1:0]spc4_pcx_data_buf_pa;	// From pcx_databuf_pa4 of pcx_databuf_pa.v
   output [4:0]		spc4_pcx_req_bufp1_pq;	// From p1 of pcx_buf_p1.v
   output		spc5_pcx_atom_bufp3_pq;	// From p3 of pcx_buf_p3.v
   output [`PCX_WIDTH-1:0]spc5_pcx_data_buf_pa;	// From pcx_databuf_pa5 of pcx_databuf_pa.v
   output [4:0]		spc5_pcx_req_bufp3_pq;	// From p3 of pcx_buf_p3.v
   output		spc6_pcx_atom_bufp3_pq;	// From p3 of pcx_buf_p3.v
   output [`PCX_WIDTH-1:0]spc6_pcx_data_buf_pa;	// From pcx_databuf_pa6 of pcx_databuf_pa.v
   output [4:0]		spc6_pcx_req_bufp3_pq;	// From p3 of pcx_buf_p3.v
   output		spc7_pcx_atom_bufp3_pq;	// From p3 of pcx_buf_p3.v
   output [`PCX_WIDTH-1:0]spc7_pcx_data_buf_pa;	// From pcx_databuf_pa7 of pcx_databuf_pa.v
   output [4:0]		spc7_pcx_req_bufp3_pq;	// From p3 of pcx_buf_p3.v
   // End of automatics

   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input [7:0]		arbpc0_pcxdp_grant_arbbf_pa;// To pm3_even of pcx_buf_pm_even.v, ...
   input [7:0]		arbpc0_pcxdp_q0_hold_arbbf_pa_l;// To pm3_even of pcx_buf_pm_even.v, ...
   input [7:0]		arbpc0_pcxdp_qsel0_arbbf_pa;// To pm3_even of pcx_buf_pm_even.v, ...
   input [7:0]		arbpc0_pcxdp_qsel1_arbbf_pa_l;// To pm3_even of pcx_buf_pm_even.v, ...
   input [7:0]		arbpc0_pcxdp_shift_arbbf_px;// To pm3_even of pcx_buf_pm_even.v, ...
   input [7:0]		arbpc1_pcxdp_grant_arbbf_pa;// To pm3_odd of pcx_buf_pm_odd.v, ...
   input [7:0]		arbpc1_pcxdp_q0_hold_arbbf_pa_l;// To pm3_odd of pcx_buf_pm_odd.v, ...
   input [7:0]		arbpc1_pcxdp_qsel0_arbbf_pa;// To pm3_odd of pcx_buf_pm_odd.v, ...
   input [7:0]		arbpc1_pcxdp_qsel1_arbbf_pa_l;// To pm3_odd of pcx_buf_pm_odd.v, ...
   input [7:0]		arbpc1_pcxdp_shift_arbbf_px;// To pm3_odd of pcx_buf_pm_odd.v, ...
   input [7:0]		arbpc2_pcxdp_grant_arbbf_pa;// To pm3_even of pcx_buf_pm_even.v, ...
   input [7:0]		arbpc2_pcxdp_q0_hold_arbbf_pa_l;// To pm3_even of pcx_buf_pm_even.v, ...
   input [7:0]		arbpc2_pcxdp_qsel0_arbbf_pa;// To pm3_even of pcx_buf_pm_even.v, ...
   input [7:0]		arbpc2_pcxdp_qsel1_arbbf_pa_l;// To pm3_even of pcx_buf_pm_even.v, ...
   input [7:0]		arbpc2_pcxdp_shift_arbbf_px;// To pm3_even of pcx_buf_pm_even.v, ...
   input [7:0]		arbpc3_pcxdp_grant_arbbf_pa;// To pm3_odd of pcx_buf_pm_odd.v, ...
   input [7:0]		arbpc3_pcxdp_q0_hold_arbbf_pa_l;// To pm3_odd of pcx_buf_pm_odd.v, ...
   input [7:0]		arbpc3_pcxdp_qsel0_arbbf_pa;// To pm3_odd of pcx_buf_pm_odd.v, ...
   input [7:0]		arbpc3_pcxdp_qsel1_arbbf_pa_l;// To pm3_odd of pcx_buf_pm_odd.v, ...
   input [7:0]		arbpc3_pcxdp_shift_arbbf_px;// To pm3_odd of pcx_buf_pm_odd.v, ...
   input [7:0]		arbpc4_pcxdp_grant_arbbf_pa;// To pm3_odd of pcx_buf_pm_odd.v, ...
   input [7:0]		arbpc4_pcxdp_q0_hold_arbbf_pa_l;// To pm3_odd of pcx_buf_pm_odd.v, ...
   input [7:0]		arbpc4_pcxdp_qsel0_arbbf_pa;// To pm3_odd of pcx_buf_pm_odd.v, ...
   input [7:0]		arbpc4_pcxdp_qsel1_arbbf_pa_l;// To pm3_odd of pcx_buf_pm_odd.v, ...
   input [7:0]		arbpc4_pcxdp_shift_arbbf_px;// To pm3_odd of pcx_buf_pm_odd.v, ...
   input		ccx_clk_hdr_so_1;	// To pcx_iodata_px2 of pcx_data_px2.v
   input		cmp_arst_l;		// To buffpio_inff of pcx_buf_fpio.v
   input		cpx_buf_top_pt0_so_1;	// To pcx_scache0_dat_px2 of pcx_data_px2.v
   input		io_pcx_stall_pq;	// To pcx_iodata_px2 of pcx_data_px2.v
   input [`PCX_WIDTH-1:0]pcx_fpio_data_px_l;	// To buffpio_inff of pcx_buf_fpio.v, ...
   input		pcx_fpio_data_rdy_arb_px;// To pcx_fpiodata_px2 of pcx_data_px2.v, ...
   input		pcx_scache0_atom_px;	// To buf0_2 of pcx_buf_scache.v
   input [`PCX_WIDTH-1:0]pcx_scache0_data_px_l;	// To buf0_1 of pcx_buf_scache.v
   input		pcx_scache0_data_rdy_arb_px;// To buf0_1 of pcx_buf_scache.v
   input		pcx_scache1_atom_px;	// To buf1_2 of pcx_buf_scache.v
   input [`PCX_WIDTH-1:0]pcx_scache1_data_px_l;	// To buf1_1 of pcx_buf_scache.v
   input		pcx_scache1_data_rdy_arb_px;// To buf1_1 of pcx_buf_scache.v
   input		pcx_scache2_atom_px;	// To buf2_4 of pcx_buf_scache.v
   input [`PCX_WIDTH-1:0]pcx_scache2_data_px_l;	// To buf2_1 of pcx_buf_scache.v
   input		pcx_scache2_data_rdy_arb_px;// To buf2_1 of pcx_buf_scache.v
   input		pcx_scache3_atom_px;	// To buf3_4 of pcx_buf_scache.v
   input [`PCX_WIDTH-1:0]pcx_scache3_data_px_l;	// To buf3_1 of pcx_buf_scache.v
   input		pcx_scache3_data_rdy_arb_px;// To buf3_1 of pcx_buf_scache.v
   input [4:0]		pcx_spc0_grant_pa;	// To p1 of pcx_buf_p1.v
   input [4:0]		pcx_spc1_grant_pa;	// To p1 of pcx_buf_p1.v
   input [4:0]		pcx_spc2_grant_pa;	// To p1 of pcx_buf_p1.v
   input [4:0]		pcx_spc3_grant_pa;	// To pm3 of pcx_buf_pm.v
   input [4:0]		pcx_spc4_grant_pa;	// To pm4 of pcx_buf_pm.v
   input [4:0]		pcx_spc5_grant_pa;	// To p3 of pcx_buf_p3.v
   input [4:0]		pcx_spc6_grant_pa;	// To p3 of pcx_buf_p3.v
   input [4:0]		pcx_spc7_grant_pa;	// To p3 of pcx_buf_p3.v
   input		pt1_so_1;		// To pcx_scache1_dat_px2 of pcx_data_px2.v
   input		rclk;			// To pt0 of pcx_buf_pt.v, ...
   input		scache0_pcx_stall_pq;	// To p0_even of pcx_buf_p0_even.v
   input		scache3_pcx_stall_pq;	// To p3 of pcx_buf_p3.v
   input		sctag1_pcx_stall_pq;	// To p0_odd of pcx_buf_p0_odd.v
   input		se_buf0_middle;		// To pcx_fpiodata_px2 of pcx_data_px2.v
   input		se_buf1_bottom;		// To pt7 of pcx_buf_pt.v
   input		se_buf1_top;		// To pt6 of pcx_buf_pt.v
   input		se_buf2_bottom;		// To pcx_scache3_dat_px2 of pcx_data_px2.v
   input		se_buf2_top;		// To pcx_scache2_dat_px2 of pcx_data_px2.v
   input		se_buf3_bottom;		// To pt5 of pcx_buf_pt.v, ...
   input		se_buf3_middle;		// To pcx_iodata_px2 of pcx_data_px2.v
   input		se_buf3_top;		// To pt2 of pcx_buf_pt.v, ...
   input		se_buf4_bottom;		// To pcx_scache1_dat_px2 of pcx_data_px2.v
   input		se_buf4_top;		// To pcx_scache0_dat_px2 of pcx_data_px2.v
   input		se_buf5_bottom;		// To pt1 of pcx_buf_pt.v
   input		se_buf5_top;		// To pt0 of pcx_buf_pt.v
   input		si_0;			// To pt3 of pcx_buf_pt1.v
   input		si_1;			// To pcx_fpiodata_px2 of pcx_data_px2.v
   input		spc0_pcx_atom_pq;	// To pt0 of pcx_buf_pt.v
   input [4:0]		spc0_pcx_req_pq;	// To pt0 of pcx_buf_pt.v
   input		spc1_pcx_atom_pq;	// To pt1 of pcx_buf_pt.v
   input [4:0]		spc1_pcx_req_pq;	// To pt1 of pcx_buf_pt.v
   input		spc2_pcx_atom_pq;	// To pt2 of pcx_buf_pt.v
   input [4:0]		spc2_pcx_req_pq;	// To pt2 of pcx_buf_pt.v
   input		spc3_pcx_atom_pq;	// To pt3 of pcx_buf_pt1.v
   input [4:0]		spc3_pcx_req_pq;	// To pt3 of pcx_buf_pt1.v
   input		spc4_pcx_atom_pq;	// To pt4 of pcx_buf_pt1.v
   input [4:0]		spc4_pcx_req_pq;	// To pt4 of pcx_buf_pt1.v
   input		spc5_pcx_atom_pq;	// To pt5 of pcx_buf_pt.v
   input [4:0]		spc5_pcx_req_pq;	// To pt5 of pcx_buf_pt.v
   input		spc6_pcx_atom_pq;	// To pt6 of pcx_buf_pt.v
   input [4:0]		spc6_pcx_req_pq;	// To pt6 of pcx_buf_pt.v
   input		spc7_pcx_atom_pq;	// To pt7 of pcx_buf_pt.v
   input [4:0]		spc7_pcx_req_pq;	// To pt7 of pcx_buf_pt.v
   // End of automatics

   input [`PCX_WIDTH-1:0] spc1_pcx_data_pa;
   input [`PCX_WIDTH-1:0] spc3_pcx_data_pa;
   input [`PCX_WIDTH-1:0] spc5_pcx_data_pa;
   input [`PCX_WIDTH-1:0] spc7_pcx_data_pa;
   input [`PCX_WIDTH-1:0] spc0_pcx_data_pa;
   input [`PCX_WIDTH-1:0] spc2_pcx_data_pa;
   input [`PCX_WIDTH-1:0] spc4_pcx_data_pa;
   input [`PCX_WIDTH-1:0] spc6_pcx_data_pa;
   
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [2:0]		arbpc0_pcxdp_grant_bufp1_pa_l;// From p1 of pcx_buf_p1.v
   wire [7:5]		arbpc0_pcxdp_grant_bufp3_pa_l;// From p3 of pcx_buf_p3.v
   wire [2:0]		arbpc0_pcxdp_q0_hold_bufp1_pa;// From p1 of pcx_buf_p1.v
   wire [7:5]		arbpc0_pcxdp_q0_hold_bufp3_pa;// From p3 of pcx_buf_p3.v
   wire [2:0]		arbpc0_pcxdp_qsel0_bufp1_pa_l;// From p1 of pcx_buf_p1.v
   wire [7:5]		arbpc0_pcxdp_qsel0_bufp3_pa_l;// From p3 of pcx_buf_p3.v
   wire [2:0]		arbpc0_pcxdp_qsel1_bufp1_pa;// From p1 of pcx_buf_p1.v
   wire [7:5]		arbpc0_pcxdp_qsel1_bufp3_pa;// From p3 of pcx_buf_p3.v
   wire [2:0]		arbpc0_pcxdp_shift_bufp1_px_l;// From p1 of pcx_buf_p1.v
   wire [7:5]		arbpc0_pcxdp_shift_bufp3_px_l;// From p3 of pcx_buf_p3.v
   wire [2:0]		arbpc1_pcxdp_grant_bufp1_pa_l;// From p1 of pcx_buf_p1.v
   wire [7:5]		arbpc1_pcxdp_grant_bufp3_pa_l;// From p3 of pcx_buf_p3.v
   wire [2:0]		arbpc1_pcxdp_q0_hold_bufp1_pa;// From p1 of pcx_buf_p1.v
   wire [7:5]		arbpc1_pcxdp_q0_hold_bufp3_pa;// From p3 of pcx_buf_p3.v
   wire [2:0]		arbpc1_pcxdp_qsel0_bufp1_pa_l;// From p1 of pcx_buf_p1.v
   wire [7:5]		arbpc1_pcxdp_qsel0_bufp3_pa_l;// From p3 of pcx_buf_p3.v
   wire [2:0]		arbpc1_pcxdp_qsel1_bufp1_pa;// From p1 of pcx_buf_p1.v
   wire [7:5]		arbpc1_pcxdp_qsel1_bufp3_pa;// From p3 of pcx_buf_p3.v
   wire [2:0]		arbpc1_pcxdp_shift_bufp1_px_l;// From p1 of pcx_buf_p1.v
   wire [7:5]		arbpc1_pcxdp_shift_bufp3_px_l;// From p3 of pcx_buf_p3.v
   wire [2:0]		arbpc2_pcxdp_grant_bufp1_pa_l;// From p1 of pcx_buf_p1.v
   wire [7:5]		arbpc2_pcxdp_grant_bufp3_pa_l;// From p3 of pcx_buf_p3.v
   wire [2:0]		arbpc2_pcxdp_q0_hold_bufp1_pa;// From p1 of pcx_buf_p1.v
   wire [7:5]		arbpc2_pcxdp_q0_hold_bufp3_pa;// From p3 of pcx_buf_p3.v
   wire [2:0]		arbpc2_pcxdp_qsel0_bufp1_pa_l;// From p1 of pcx_buf_p1.v
   wire [7:5]		arbpc2_pcxdp_qsel0_bufp3_pa_l;// From p3 of pcx_buf_p3.v
   wire [2:0]		arbpc2_pcxdp_qsel1_bufp1_pa;// From p1 of pcx_buf_p1.v
   wire [7:5]		arbpc2_pcxdp_qsel1_bufp3_pa;// From p3 of pcx_buf_p3.v
   wire [2:0]		arbpc2_pcxdp_shift_bufp1_px_l;// From p1 of pcx_buf_p1.v
   wire [7:5]		arbpc2_pcxdp_shift_bufp3_px_l;// From p3 of pcx_buf_p3.v
   wire [2:0]		arbpc3_pcxdp_grant_bufp1_pa_l;// From p1 of pcx_buf_p1.v
   wire [7:5]		arbpc3_pcxdp_grant_bufp3_pa_l;// From p3 of pcx_buf_p3.v
   wire [2:0]		arbpc3_pcxdp_q0_hold_bufp1_pa;// From p1 of pcx_buf_p1.v
   wire [7:5]		arbpc3_pcxdp_q0_hold_bufp3_pa;// From p3 of pcx_buf_p3.v
   wire [2:0]		arbpc3_pcxdp_qsel0_bufp1_pa_l;// From p1 of pcx_buf_p1.v
   wire [7:5]		arbpc3_pcxdp_qsel0_bufp3_pa_l;// From p3 of pcx_buf_p3.v
   wire [2:0]		arbpc3_pcxdp_qsel1_bufp1_pa;// From p1 of pcx_buf_p1.v
   wire [7:5]		arbpc3_pcxdp_qsel1_bufp3_pa;// From p3 of pcx_buf_p3.v
   wire [2:0]		arbpc3_pcxdp_shift_bufp1_px_l;// From p1 of pcx_buf_p1.v
   wire [7:5]		arbpc3_pcxdp_shift_bufp3_px_l;// From p3 of pcx_buf_p3.v
   wire [2:0]		arbpc4_pcxdp_grant_bufp1_pa_l;// From p1 of pcx_buf_p1.v
   wire [7:5]		arbpc4_pcxdp_grant_bufp3_pa_l;// From p3 of pcx_buf_p3.v
   wire [2:0]		arbpc4_pcxdp_q0_hold_bufp1_pa;// From p1 of pcx_buf_p1.v
   wire [7:5]		arbpc4_pcxdp_q0_hold_bufp3_pa;// From p3 of pcx_buf_p3.v
   wire [2:0]		arbpc4_pcxdp_qsel0_bufp1_pa_l;// From p1 of pcx_buf_p1.v
   wire [7:5]		arbpc4_pcxdp_qsel0_bufp3_pa_l;// From p3 of pcx_buf_p3.v
   wire [2:0]		arbpc4_pcxdp_qsel1_bufp1_pa;// From p1 of pcx_buf_p1.v
   wire [7:5]		arbpc4_pcxdp_qsel1_bufp3_pa;// From p3 of pcx_buf_p3.v
   wire [2:0]		arbpc4_pcxdp_shift_bufp1_px_l;// From p1 of pcx_buf_p1.v
   wire [7:5]		arbpc4_pcxdp_shift_bufp3_px_l;// From p3 of pcx_buf_p3.v
   wire			io_pcx_stall_buf1_pq;	// From pcx_iodata_px2 of pcx_data_px2.v
   wire [`PCX_WIDTH-1:0]pcx_fpio_data_ff_px2;	// From pcx_fpiodata_px2 of pcx_data_px2.v
   wire [`PCX_WIDTH-1:0]pcx_fpio_data_px_buf_l;	// From buffpio_inff of pcx_buf_fpio.v
   wire			pcx_fpio_data_rdy_ff_px2;// From pcx_fpiodata_px2 of pcx_data_px2.v
   wire			pcx_fpiodata_px2_so_1;	// From pcx_fpiodata_px2 of pcx_data_px2.v
   wire [`PCX_WIDTH-1:0]pcx_io_data_ff_px2;	// From pcx_iodata_px2 of pcx_data_px2.v
   wire [`PCX_WIDTH-1:0]pcx_io_data_px_buf_l;	// From bufio_inff of pcx_databuf_pa.v
   wire			pcx_io_data_rdy_arb_buf_px;// From bufio_inff of pcx_databuf_pa.v
   wire			pcx_io_data_rdy_ff_px2;	// From pcx_iodata_px2 of pcx_data_px2.v
   wire			pcx_scache0_atom_buf0_2_px1;// From buf0_2 of pcx_buf_scache.v
   wire [`PCX_WIDTH-1:0]pcx_scache0_data_buf2_l;// From buf0_2 of pcx_buf_scache.v
   wire [`PCX_WIDTH-1:0]pcx_scache0_data_px_buf1;// From buf0_1 of pcx_buf_scache.v
   wire [`PCX_WIDTH-1:0]pcx_scache0_data_px_buf3;// From buf0_3 of pcx_buf_scache.v
   wire [`PCX_WIDTH-1:0]pcx_scache0_data_px_buf4_l;// From buf0_4 of pcx_buf_scache.v
   wire			pcx_scache0_data_rdy_buf1_px;// From buf0_1 of pcx_buf_scache.v
   wire			pcx_scache1_atom_buf1_2_px1;// From buf1_2 of pcx_buf_scache.v
   wire [`PCX_WIDTH-1:0]pcx_scache1_data_buf2_l;// From buf1_2 of pcx_buf_scache.v
   wire [`PCX_WIDTH-1:0]pcx_scache1_data_px_buf1;// From buf1_1 of pcx_buf_scache.v
   wire [`PCX_WIDTH-1:0]pcx_scache1_data_px_buf3;// From buf1_3 of pcx_buf_scache.v
   wire [`PCX_WIDTH-1:0]pcx_scache1_data_px_buf4_l;// From buf1_4 of pcx_buf_scache.v
   wire			pcx_scache1_data_rdy_buf1_px;// From buf1_1 of pcx_buf_scache.v
   wire [`PCX_WIDTH-1:0]pcx_scache2_data_buf2_l;// From buf2_2 of pcx_buf_scache.v
   wire [`PCX_WIDTH-1:0]pcx_scache2_data_px_buf1;// From buf2_1 of pcx_buf_scache.v
   wire [`PCX_WIDTH-1:0]pcx_scache2_data_px_buf3;// From buf2_3 of pcx_buf_scache.v
   wire [`PCX_WIDTH-1:0]pcx_scache2_data_px_buf4_l;// From buf2_4 of pcx_buf_scache.v
   wire			pcx_scache2_data_rdy_buf1_px;// From buf2_1 of pcx_buf_scache.v
   wire			pcx_scache3_dat_px2_so_1;// From pcx_scache3_dat_px2 of pcx_data_px2.v
   wire [`PCX_WIDTH-1:0]pcx_scache3_data_buf2_l;// From buf3_2 of pcx_buf_scache.v
   wire [`PCX_WIDTH-1:0]pcx_scache3_data_px_buf1;// From buf3_1 of pcx_buf_scache.v
   wire [`PCX_WIDTH-1:0]pcx_scache3_data_px_buf3;// From buf3_3 of pcx_buf_scache.v
   wire [`PCX_WIDTH-1:0]pcx_scache3_data_px_buf4_l;// From buf3_4 of pcx_buf_scache.v
   wire			pcx_scache3_data_rdy_buf1_px;// From buf3_1 of pcx_buf_scache.v
   wire [4:0]		pcx_spc0_grant_bufp0_pa;// From p0 of pcx_buf_p0.v
   wire [4:0]		pcx_spc0_grant_bufp1_pa_l;// From p1 of pcx_buf_p1.v
   wire [4:0]		pcx_spc1_grant_bufp1_pa_l;// From p1 of pcx_buf_p1.v
   wire [4:0]		pcx_spc1_grant_bufpdl_pa;// From pdl1 of pcx_buf_pdl.v
   wire [4:0]		pcx_spc2_grant_bufp1_pa_l;// From p1 of pcx_buf_p1.v
   wire [4:0]		pcx_spc2_grant_bufpdl_pa;// From pdl2 of pcx_buf_pdl.v
   wire [4:0]		pcx_spc3_grant_bufpm_pa;// From pm3 of pcx_buf_pm.v
   wire [4:0]		pcx_spc4_grant_bufpm_pa;// From pm4 of pcx_buf_pm.v
   wire [4:0]		pcx_spc5_grant_bufp3_pa_l;// From p3 of pcx_buf_p3.v
   wire [4:0]		pcx_spc5_grant_bufpdr_pa;// From pdr5 of pcx_buf_pdr.v
   wire [4:0]		pcx_spc6_grant_bufp3_pa_l;// From p3 of pcx_buf_p3.v
   wire [4:0]		pcx_spc6_grant_bufpdr_pa;// From pdr6 of pcx_buf_pdr.v
   wire [4:0]		pcx_spc7_grant_bufp3_pa_l;// From p3 of pcx_buf_p3.v
   wire [4:0]		pcx_spc7_grant_bufp4_pa;// From p4 of pcx_buf_p4.v
   wire			pt1_so_0;		// From pt1 of pcx_buf_pt.v
   wire			pt2_so_0;		// From pt2 of pcx_buf_pt.v
   wire			pt3_so_0;		// From pt3 of pcx_buf_pt1.v
   wire			pt4_so_0;		// From pt4 of pcx_buf_pt1.v
   wire			pt5_so_0;		// From pt5 of pcx_buf_pt.v
   wire			pt6_so_0;		// From pt6 of pcx_buf_pt.v
   wire			pt7_so_0;		// From pt7 of pcx_buf_pt.v
   wire			scache0_pcx_stall_bufp0even_pq;// From p0_even of pcx_buf_p0_even.v
   wire			sctag1_pcx_stall_bufp0odd_pq;// From p0_odd of pcx_buf_p0_odd.v
   wire			spc0_pcx_atom_bufp0_pq;	// From p0 of pcx_buf_p0.v
   wire			spc0_pcx_atom_bufpt_pq_l;// From pt0 of pcx_buf_pt.v
   wire [4:0]		spc0_pcx_req_bufp0_pq;	// From p0 of pcx_buf_p0.v
   wire [4:0]		spc0_pcx_req_bufpt_pq_l;// From pt0 of pcx_buf_pt.v
   wire			spc1_pcx_atom_bufp0_pq;	// From p0 of pcx_buf_p0.v
   wire			spc1_pcx_atom_bufpt_pq_l;// From pt1 of pcx_buf_pt.v
   wire [4:0]		spc1_pcx_req_bufp0_pq;	// From p0 of pcx_buf_p0.v
   wire [4:0]		spc1_pcx_req_bufpt_pq_l;// From pt1 of pcx_buf_pt.v
   wire			spc2_pcx_atom_bufpt_pq_l;// From pt2 of pcx_buf_pt.v
   wire [4:0]		spc2_pcx_req_bufpt_pq_l;// From pt2 of pcx_buf_pt.v
   wire			spc3_pcx_atom_bufpt1_pq;// From pt3 of pcx_buf_pt1.v
   wire [4:0]		spc3_pcx_req_bufpt1_pq;	// From pt3 of pcx_buf_pt1.v
   wire			spc4_pcx_atom_bufpt1_pq;// From pt4 of pcx_buf_pt1.v
   wire [4:0]		spc4_pcx_req_bufpt1_pq;	// From pt4 of pcx_buf_pt1.v
   wire			spc5_pcx_atom_bufpt_pq_l;// From pt5 of pcx_buf_pt.v
   wire [4:0]		spc5_pcx_req_bufpt_pq_l;// From pt5 of pcx_buf_pt.v
   wire			spc6_pcx_atom_bufp4_pq;	// From p4 of pcx_buf_p4.v
   wire			spc6_pcx_atom_bufpt_pq_l;// From pt6 of pcx_buf_pt.v
   wire [4:0]		spc6_pcx_req_bufp4_pq;	// From p4 of pcx_buf_p4.v
   wire [4:0]		spc6_pcx_req_bufpt_pq_l;// From pt6 of pcx_buf_pt.v
   wire			spc7_pcx_atom_bufp4_pq;	// From p4 of pcx_buf_p4.v
   wire			spc7_pcx_atom_bufpt_pq_l;// From pt7 of pcx_buf_pt.v
   wire [4:0]		spc7_pcx_req_bufp4_pq;	// From p4 of pcx_buf_p4.v
   wire [4:0]		spc7_pcx_req_bufpt_pq_l;// From pt7 of pcx_buf_pt.v
   // End of automatics




   /*
   pcx_buf_pm AUTO_TEMPLATE(
		 // Outputs
		 .pcx_spc_grant_bufpm_pa(pcx_spc@_grant_bufpm_pa[4:0]),
                 .pcx_stall_bufpm_pq(),
		 // Inputs
                 .pcx_stall_pq(1'b0),
		 .pcx_spc_grant_pa	(pcx_spc@_grant_pa[4:0]));
   */

   pcx_buf_pm pm3(/*AUTOINST*/
		  // Outputs
		  .pcx_spc_grant_bufpm_pa(pcx_spc3_grant_bufpm_pa[4:0]), // Templated
		  .pcx_stall_bufpm_pq	(),			 // Templated
		  // Inputs
		  .pcx_spc_grant_pa	(pcx_spc3_grant_pa[4:0]), // Templated
		  .pcx_stall_pq		(1'b0));			 // Templated
   /*
   pcx_buf_pm AUTO_TEMPLATE(
		 // Outputs
		 .pcx_spc_grant_bufpm_pa(pcx_spc@_grant_bufpm_pa[4:0]),
                 .pcx_stall_bufpm_pq(io_pcx_stall_bufp3_pq),
		 // Inputs
                 .pcx_stall_pq(io_pcx_stall_buf1_pq),
		 .pcx_spc_grant_pa	(pcx_spc@_grant_pa[4:0]));
   */
   pcx_buf_pm pm4(/*AUTOINST*/
		  // Outputs
		  .pcx_spc_grant_bufpm_pa(pcx_spc4_grant_bufpm_pa[4:0]), // Templated
		  .pcx_stall_bufpm_pq	(io_pcx_stall_bufp3_pq), // Templated
		  // Inputs
		  .pcx_spc_grant_pa	(pcx_spc4_grant_pa[4:0]), // Templated
		  .pcx_stall_pq		(io_pcx_stall_buf1_pq));	 // Templated
   /*
   pcx_buf_pm_even AUTO_TEMPLATE(
		 // Outputs
		 .arbpc0_pcxdp_grant_pa	(arbpc0_pcxdp_grant_pa[@]),
		 .arbpc0_pcxdp_q0_hold_pa_l(arbpc0_pcxdp_q0_hold_pa_l[@]),
		 .arbpc0_pcxdp_qsel0_pa	(arbpc0_pcxdp_qsel0_pa[@]),
		 .arbpc0_pcxdp_qsel1_pa_l(arbpc0_pcxdp_qsel1_pa_l[@]),
		 .arbpc0_pcxdp_shift_px	(arbpc0_pcxdp_shift_px[@]),
		 .arbpc2_pcxdp_grant_pa	(arbpc2_pcxdp_grant_pa[@]),
		 .arbpc2_pcxdp_q0_hold_pa_l(arbpc2_pcxdp_q0_hold_pa_l[@]),
		 .arbpc2_pcxdp_qsel0_pa	(arbpc2_pcxdp_qsel0_pa[@]),
		 .arbpc2_pcxdp_qsel1_pa_l(arbpc2_pcxdp_qsel1_pa_l[@]),
		 .arbpc2_pcxdp_shift_px	(arbpc2_pcxdp_shift_px[@]),
		 // Inputs
		 .arbpc0_pcxdp_grant_arbbf_pa(arbpc0_pcxdp_grant_arbbf_pa[@]),
		 .arbpc0_pcxdp_q0_hold_arbbf_pa_l(arbpc0_pcxdp_q0_hold_arbbf_pa_l[@]),
		 .arbpc0_pcxdp_qsel0_arbbf_pa(arbpc0_pcxdp_qsel0_arbbf_pa[@]),
		 .arbpc0_pcxdp_qsel1_arbbf_pa_l(arbpc0_pcxdp_qsel1_arbbf_pa_l[@]),
		 .arbpc0_pcxdp_shift_arbbf_px(arbpc0_pcxdp_shift_arbbf_px[@]),
		 .arbpc2_pcxdp_grant_arbbf_pa(arbpc2_pcxdp_grant_arbbf_pa[@]),
		 .arbpc2_pcxdp_q0_hold_arbbf_pa_l(arbpc2_pcxdp_q0_hold_arbbf_pa_l[@]),
		 .arbpc2_pcxdp_qsel0_arbbf_pa(arbpc2_pcxdp_qsel0_arbbf_pa[@]),
		 .arbpc2_pcxdp_qsel1_arbbf_pa_l(arbpc2_pcxdp_qsel1_arbbf_pa_l[@]),
		 .arbpc2_pcxdp_shift_arbbf_px(arbpc2_pcxdp_shift_arbbf_px[@]));
   */

   pcx_buf_pm_even pm3_even(/*AUTOINST*/
			    // Outputs
			    .arbpc0_pcxdp_grant_pa(arbpc0_pcxdp_grant_pa[3]), // Templated
			    .arbpc0_pcxdp_q0_hold_pa_l(arbpc0_pcxdp_q0_hold_pa_l[3]), // Templated
			    .arbpc0_pcxdp_qsel0_pa(arbpc0_pcxdp_qsel0_pa[3]), // Templated
			    .arbpc0_pcxdp_qsel1_pa_l(arbpc0_pcxdp_qsel1_pa_l[3]), // Templated
			    .arbpc0_pcxdp_shift_px(arbpc0_pcxdp_shift_px[3]), // Templated
			    .arbpc2_pcxdp_grant_pa(arbpc2_pcxdp_grant_pa[3]), // Templated
			    .arbpc2_pcxdp_q0_hold_pa_l(arbpc2_pcxdp_q0_hold_pa_l[3]), // Templated
			    .arbpc2_pcxdp_qsel0_pa(arbpc2_pcxdp_qsel0_pa[3]), // Templated
			    .arbpc2_pcxdp_qsel1_pa_l(arbpc2_pcxdp_qsel1_pa_l[3]), // Templated
			    .arbpc2_pcxdp_shift_px(arbpc2_pcxdp_shift_px[3]), // Templated
			    // Inputs
			    .arbpc0_pcxdp_grant_arbbf_pa(arbpc0_pcxdp_grant_arbbf_pa[3]), // Templated
			    .arbpc0_pcxdp_q0_hold_arbbf_pa_l(arbpc0_pcxdp_q0_hold_arbbf_pa_l[3]), // Templated
			    .arbpc0_pcxdp_qsel0_arbbf_pa(arbpc0_pcxdp_qsel0_arbbf_pa[3]), // Templated
			    .arbpc0_pcxdp_qsel1_arbbf_pa_l(arbpc0_pcxdp_qsel1_arbbf_pa_l[3]), // Templated
			    .arbpc0_pcxdp_shift_arbbf_px(arbpc0_pcxdp_shift_arbbf_px[3]), // Templated
			    .arbpc2_pcxdp_grant_arbbf_pa(arbpc2_pcxdp_grant_arbbf_pa[3]), // Templated
			    .arbpc2_pcxdp_q0_hold_arbbf_pa_l(arbpc2_pcxdp_q0_hold_arbbf_pa_l[3]), // Templated
			    .arbpc2_pcxdp_qsel0_arbbf_pa(arbpc2_pcxdp_qsel0_arbbf_pa[3]), // Templated
			    .arbpc2_pcxdp_qsel1_arbbf_pa_l(arbpc2_pcxdp_qsel1_arbbf_pa_l[3]), // Templated
			    .arbpc2_pcxdp_shift_arbbf_px(arbpc2_pcxdp_shift_arbbf_px[3])); // Templated
   pcx_buf_pm_even pm4_even(/*AUTOINST*/
			    // Outputs
			    .arbpc0_pcxdp_grant_pa(arbpc0_pcxdp_grant_pa[4]), // Templated
			    .arbpc0_pcxdp_q0_hold_pa_l(arbpc0_pcxdp_q0_hold_pa_l[4]), // Templated
			    .arbpc0_pcxdp_qsel0_pa(arbpc0_pcxdp_qsel0_pa[4]), // Templated
			    .arbpc0_pcxdp_qsel1_pa_l(arbpc0_pcxdp_qsel1_pa_l[4]), // Templated
			    .arbpc0_pcxdp_shift_px(arbpc0_pcxdp_shift_px[4]), // Templated
			    .arbpc2_pcxdp_grant_pa(arbpc2_pcxdp_grant_pa[4]), // Templated
			    .arbpc2_pcxdp_q0_hold_pa_l(arbpc2_pcxdp_q0_hold_pa_l[4]), // Templated
			    .arbpc2_pcxdp_qsel0_pa(arbpc2_pcxdp_qsel0_pa[4]), // Templated
			    .arbpc2_pcxdp_qsel1_pa_l(arbpc2_pcxdp_qsel1_pa_l[4]), // Templated
			    .arbpc2_pcxdp_shift_px(arbpc2_pcxdp_shift_px[4]), // Templated
			    // Inputs
			    .arbpc0_pcxdp_grant_arbbf_pa(arbpc0_pcxdp_grant_arbbf_pa[4]), // Templated
			    .arbpc0_pcxdp_q0_hold_arbbf_pa_l(arbpc0_pcxdp_q0_hold_arbbf_pa_l[4]), // Templated
			    .arbpc0_pcxdp_qsel0_arbbf_pa(arbpc0_pcxdp_qsel0_arbbf_pa[4]), // Templated
			    .arbpc0_pcxdp_qsel1_arbbf_pa_l(arbpc0_pcxdp_qsel1_arbbf_pa_l[4]), // Templated
			    .arbpc0_pcxdp_shift_arbbf_px(arbpc0_pcxdp_shift_arbbf_px[4]), // Templated
			    .arbpc2_pcxdp_grant_arbbf_pa(arbpc2_pcxdp_grant_arbbf_pa[4]), // Templated
			    .arbpc2_pcxdp_q0_hold_arbbf_pa_l(arbpc2_pcxdp_q0_hold_arbbf_pa_l[4]), // Templated
			    .arbpc2_pcxdp_qsel0_arbbf_pa(arbpc2_pcxdp_qsel0_arbbf_pa[4]), // Templated
			    .arbpc2_pcxdp_qsel1_arbbf_pa_l(arbpc2_pcxdp_qsel1_arbbf_pa_l[4]), // Templated
			    .arbpc2_pcxdp_shift_arbbf_px(arbpc2_pcxdp_shift_arbbf_px[4])); // Templated
   /*
   pcx_buf_pm_odd AUTO_TEMPLATE(
		 // Outputs
		 .arbpc1_pcxdp_grant_pa	(arbpc1_pcxdp_grant_pa[@]),
		 .arbpc1_pcxdp_q0_hold_pa_l(arbpc1_pcxdp_q0_hold_pa_l[@]),
		 .arbpc1_pcxdp_qsel0_pa	(arbpc1_pcxdp_qsel0_pa[@]),
		 .arbpc1_pcxdp_qsel1_pa_l(arbpc1_pcxdp_qsel1_pa_l[@]),
		 .arbpc1_pcxdp_shift_px	(arbpc1_pcxdp_shift_px[@]),
		 .arbpc3_pcxdp_grant_pa	(arbpc3_pcxdp_grant_pa[@]),
		 .arbpc3_pcxdp_q0_hold_pa_l(arbpc3_pcxdp_q0_hold_pa_l[@]),
		 .arbpc3_pcxdp_qsel0_pa	(arbpc3_pcxdp_qsel0_pa[@]),
		 .arbpc3_pcxdp_qsel1_pa_l(arbpc3_pcxdp_qsel1_pa_l[@]),
		 .arbpc3_pcxdp_shift_px	(arbpc3_pcxdp_shift_px[@]),
		 .arbpc4_pcxdp_grant_pa	(arbpc4_pcxdp_grant_pa[@]),
		 .arbpc4_pcxdp_q0_hold_pa_l(arbpc4_pcxdp_q0_hold_pa_l[@]),
		 .arbpc4_pcxdp_qsel0_pa	(arbpc4_pcxdp_qsel0_pa[@]),
		 .arbpc4_pcxdp_qsel1_pa_l(arbpc4_pcxdp_qsel1_pa_l[@]),
		 .arbpc4_pcxdp_shift_px	(arbpc4_pcxdp_shift_px[@]),
		 // Inputs
		 .arbpc1_pcxdp_grant_arbbf_pa(arbpc1_pcxdp_grant_arbbf_pa[@]),
		 .arbpc1_pcxdp_q0_hold_arbbf_pa_l(arbpc1_pcxdp_q0_hold_arbbf_pa_l[@]),
		 .arbpc1_pcxdp_qsel0_arbbf_pa(arbpc1_pcxdp_qsel0_arbbf_pa[@]),
		 .arbpc1_pcxdp_qsel1_arbbf_pa_l(arbpc1_pcxdp_qsel1_arbbf_pa_l[@]),
		 .arbpc1_pcxdp_shift_arbbf_px(arbpc1_pcxdp_shift_arbbf_px[@]),
		 .arbpc3_pcxdp_grant_arbbf_pa(arbpc3_pcxdp_grant_arbbf_pa[@]),
		 .arbpc3_pcxdp_q0_hold_arbbf_pa_l(arbpc3_pcxdp_q0_hold_arbbf_pa_l[@]),
		 .arbpc3_pcxdp_qsel0_arbbf_pa(arbpc3_pcxdp_qsel0_arbbf_pa[@]),
		 .arbpc3_pcxdp_qsel1_arbbf_pa_l(arbpc3_pcxdp_qsel1_arbbf_pa_l[@]),
		 .arbpc3_pcxdp_shift_arbbf_px(arbpc3_pcxdp_shift_arbbf_px[@]),
		 .arbpc4_pcxdp_grant_arbbf_pa(arbpc4_pcxdp_grant_arbbf_pa[@]),
		 .arbpc4_pcxdp_q0_hold_arbbf_pa_l(arbpc4_pcxdp_q0_hold_arbbf_pa_l[@]),
		 .arbpc4_pcxdp_qsel0_arbbf_pa(arbpc4_pcxdp_qsel0_arbbf_pa[@]),
		 .arbpc4_pcxdp_qsel1_arbbf_pa_l(arbpc4_pcxdp_qsel1_arbbf_pa_l[@]),
		 .arbpc4_pcxdp_shift_arbbf_px(arbpc4_pcxdp_shift_arbbf_px[@]));
*/
   pcx_buf_pm_odd pm3_odd(/*AUTOINST*/
			  // Outputs
			  .arbpc1_pcxdp_grant_pa(arbpc1_pcxdp_grant_pa[3]), // Templated
			  .arbpc1_pcxdp_q0_hold_pa_l(arbpc1_pcxdp_q0_hold_pa_l[3]), // Templated
			  .arbpc1_pcxdp_qsel0_pa(arbpc1_pcxdp_qsel0_pa[3]), // Templated
			  .arbpc1_pcxdp_qsel1_pa_l(arbpc1_pcxdp_qsel1_pa_l[3]), // Templated
			  .arbpc1_pcxdp_shift_px(arbpc1_pcxdp_shift_px[3]), // Templated
			  .arbpc3_pcxdp_grant_pa(arbpc3_pcxdp_grant_pa[3]), // Templated
			  .arbpc3_pcxdp_q0_hold_pa_l(arbpc3_pcxdp_q0_hold_pa_l[3]), // Templated
			  .arbpc3_pcxdp_qsel0_pa(arbpc3_pcxdp_qsel0_pa[3]), // Templated
			  .arbpc3_pcxdp_qsel1_pa_l(arbpc3_pcxdp_qsel1_pa_l[3]), // Templated
			  .arbpc3_pcxdp_shift_px(arbpc3_pcxdp_shift_px[3]), // Templated
			  .arbpc4_pcxdp_grant_pa(arbpc4_pcxdp_grant_pa[3]), // Templated
			  .arbpc4_pcxdp_q0_hold_pa_l(arbpc4_pcxdp_q0_hold_pa_l[3]), // Templated
			  .arbpc4_pcxdp_qsel0_pa(arbpc4_pcxdp_qsel0_pa[3]), // Templated
			  .arbpc4_pcxdp_qsel1_pa_l(arbpc4_pcxdp_qsel1_pa_l[3]), // Templated
			  .arbpc4_pcxdp_shift_px(arbpc4_pcxdp_shift_px[3]), // Templated
			  // Inputs
			  .arbpc1_pcxdp_grant_arbbf_pa(arbpc1_pcxdp_grant_arbbf_pa[3]), // Templated
			  .arbpc1_pcxdp_q0_hold_arbbf_pa_l(arbpc1_pcxdp_q0_hold_arbbf_pa_l[3]), // Templated
			  .arbpc1_pcxdp_qsel0_arbbf_pa(arbpc1_pcxdp_qsel0_arbbf_pa[3]), // Templated
			  .arbpc1_pcxdp_qsel1_arbbf_pa_l(arbpc1_pcxdp_qsel1_arbbf_pa_l[3]), // Templated
			  .arbpc1_pcxdp_shift_arbbf_px(arbpc1_pcxdp_shift_arbbf_px[3]), // Templated
			  .arbpc3_pcxdp_grant_arbbf_pa(arbpc3_pcxdp_grant_arbbf_pa[3]), // Templated
			  .arbpc3_pcxdp_q0_hold_arbbf_pa_l(arbpc3_pcxdp_q0_hold_arbbf_pa_l[3]), // Templated
			  .arbpc3_pcxdp_qsel0_arbbf_pa(arbpc3_pcxdp_qsel0_arbbf_pa[3]), // Templated
			  .arbpc3_pcxdp_qsel1_arbbf_pa_l(arbpc3_pcxdp_qsel1_arbbf_pa_l[3]), // Templated
			  .arbpc3_pcxdp_shift_arbbf_px(arbpc3_pcxdp_shift_arbbf_px[3]), // Templated
			  .arbpc4_pcxdp_grant_arbbf_pa(arbpc4_pcxdp_grant_arbbf_pa[3]), // Templated
			  .arbpc4_pcxdp_q0_hold_arbbf_pa_l(arbpc4_pcxdp_q0_hold_arbbf_pa_l[3]), // Templated
			  .arbpc4_pcxdp_qsel0_arbbf_pa(arbpc4_pcxdp_qsel0_arbbf_pa[3]), // Templated
			  .arbpc4_pcxdp_qsel1_arbbf_pa_l(arbpc4_pcxdp_qsel1_arbbf_pa_l[3]), // Templated
			  .arbpc4_pcxdp_shift_arbbf_px(arbpc4_pcxdp_shift_arbbf_px[3])); // Templated
   pcx_buf_pm_odd pm4_odd(/*AUTOINST*/
			  // Outputs
			  .arbpc1_pcxdp_grant_pa(arbpc1_pcxdp_grant_pa[4]), // Templated
			  .arbpc1_pcxdp_q0_hold_pa_l(arbpc1_pcxdp_q0_hold_pa_l[4]), // Templated
			  .arbpc1_pcxdp_qsel0_pa(arbpc1_pcxdp_qsel0_pa[4]), // Templated
			  .arbpc1_pcxdp_qsel1_pa_l(arbpc1_pcxdp_qsel1_pa_l[4]), // Templated
			  .arbpc1_pcxdp_shift_px(arbpc1_pcxdp_shift_px[4]), // Templated
			  .arbpc3_pcxdp_grant_pa(arbpc3_pcxdp_grant_pa[4]), // Templated
			  .arbpc3_pcxdp_q0_hold_pa_l(arbpc3_pcxdp_q0_hold_pa_l[4]), // Templated
			  .arbpc3_pcxdp_qsel0_pa(arbpc3_pcxdp_qsel0_pa[4]), // Templated
			  .arbpc3_pcxdp_qsel1_pa_l(arbpc3_pcxdp_qsel1_pa_l[4]), // Templated
			  .arbpc3_pcxdp_shift_px(arbpc3_pcxdp_shift_px[4]), // Templated
			  .arbpc4_pcxdp_grant_pa(arbpc4_pcxdp_grant_pa[4]), // Templated
			  .arbpc4_pcxdp_q0_hold_pa_l(arbpc4_pcxdp_q0_hold_pa_l[4]), // Templated
			  .arbpc4_pcxdp_qsel0_pa(arbpc4_pcxdp_qsel0_pa[4]), // Templated
			  .arbpc4_pcxdp_qsel1_pa_l(arbpc4_pcxdp_qsel1_pa_l[4]), // Templated
			  .arbpc4_pcxdp_shift_px(arbpc4_pcxdp_shift_px[4]), // Templated
			  // Inputs
			  .arbpc1_pcxdp_grant_arbbf_pa(arbpc1_pcxdp_grant_arbbf_pa[4]), // Templated
			  .arbpc1_pcxdp_q0_hold_arbbf_pa_l(arbpc1_pcxdp_q0_hold_arbbf_pa_l[4]), // Templated
			  .arbpc1_pcxdp_qsel0_arbbf_pa(arbpc1_pcxdp_qsel0_arbbf_pa[4]), // Templated
			  .arbpc1_pcxdp_qsel1_arbbf_pa_l(arbpc1_pcxdp_qsel1_arbbf_pa_l[4]), // Templated
			  .arbpc1_pcxdp_shift_arbbf_px(arbpc1_pcxdp_shift_arbbf_px[4]), // Templated
			  .arbpc3_pcxdp_grant_arbbf_pa(arbpc3_pcxdp_grant_arbbf_pa[4]), // Templated
			  .arbpc3_pcxdp_q0_hold_arbbf_pa_l(arbpc3_pcxdp_q0_hold_arbbf_pa_l[4]), // Templated
			  .arbpc3_pcxdp_qsel0_arbbf_pa(arbpc3_pcxdp_qsel0_arbbf_pa[4]), // Templated
			  .arbpc3_pcxdp_qsel1_arbbf_pa_l(arbpc3_pcxdp_qsel1_arbbf_pa_l[4]), // Templated
			  .arbpc3_pcxdp_shift_arbbf_px(arbpc3_pcxdp_shift_arbbf_px[4]), // Templated
			  .arbpc4_pcxdp_grant_arbbf_pa(arbpc4_pcxdp_grant_arbbf_pa[4]), // Templated
			  .arbpc4_pcxdp_q0_hold_arbbf_pa_l(arbpc4_pcxdp_q0_hold_arbbf_pa_l[4]), // Templated
			  .arbpc4_pcxdp_qsel0_arbbf_pa(arbpc4_pcxdp_qsel0_arbbf_pa[4]), // Templated
			  .arbpc4_pcxdp_qsel1_arbbf_pa_l(arbpc4_pcxdp_qsel1_arbbf_pa_l[4]), // Templated
			  .arbpc4_pcxdp_shift_arbbf_px(arbpc4_pcxdp_shift_arbbf_px[4])); // Templated
/*
 pcx_buf_pt AUTO_TEMPLATE(
		  // Outputs
		  .out0_l		(spc@_pcx_req_bufpt_pq_l[4:0]),
		  .out1_l		(spc@_pcx_atom_bufpt_pq_l),
	          .pcx_spc_grant_px	(pcx_spc@_grant_px[4:0]), 
                  .so                   (pcx_buf_top_pt0_so_0),
		  // Inputs
                  .si                   (pt1_so_0),
                  .se                   (se_buf5_top),
		  .in0			(spc@_pcx_req_pq[4:0]),
		  .in1			(spc@_pcx_atom_pq),
                  .pcx_spc_grant_buf_pa	(pcx_spc@_grant_bufp0_pa[4:0]),);
 */

   pcx_buf_pt pt0(/*AUTOINST*/
		  // Outputs
		  .out0_l		(spc0_pcx_req_bufpt_pq_l[4:0]), // Templated
		  .out1_l		(spc0_pcx_atom_bufpt_pq_l), // Templated
		  .pcx_spc_grant_px	(pcx_spc0_grant_px[4:0]), // Templated
		  .so			(pcx_buf_top_pt0_so_0),	 // Templated
		  // Inputs
		  .in0			(spc0_pcx_req_pq[4:0]),	 // Templated
		  .in1			(spc0_pcx_atom_pq),	 // Templated
		  .pcx_spc_grant_buf_pa	(pcx_spc0_grant_bufp0_pa[4:0]), // Templated
		  .rclk			(rclk),
		  .si			(pt1_so_0),		 // Templated
		  .se			(se_buf5_top));		 // Templated
   /*
 pcx_buf_pt AUTO_TEMPLATE(
		  // Outputs
		  .out0_l		(spc@_pcx_req_bufpt_pq_l[4:0]),
		  .out1_l		(spc@_pcx_atom_bufpt_pq_l),
	          .pcx_spc_grant_px	(pcx_spc@_grant_px[4:0]), 
                  .so                   (pt1_so_0),
		  // Inputs
                  .si                   (pt2_so_0),
                  .se                   (se_buf5_bottom),
		  .in0			(spc@_pcx_req_pq[4:0]),
		  .in1			(spc@_pcx_atom_pq),
                  .pcx_spc_grant_buf_pa	(pcx_spc@_grant_bufpdl_pa[4:0]),);
 */

   pcx_buf_pt pt1(/*AUTOINST*/
		  // Outputs
		  .out0_l		(spc1_pcx_req_bufpt_pq_l[4:0]), // Templated
		  .out1_l		(spc1_pcx_atom_bufpt_pq_l), // Templated
		  .pcx_spc_grant_px	(pcx_spc1_grant_px[4:0]), // Templated
		  .so			(pt1_so_0),		 // Templated
		  // Inputs
		  .in0			(spc1_pcx_req_pq[4:0]),	 // Templated
		  .in1			(spc1_pcx_atom_pq),	 // Templated
		  .pcx_spc_grant_buf_pa	(pcx_spc1_grant_bufpdl_pa[4:0]), // Templated
		  .rclk			(rclk),
		  .si			(pt2_so_0),		 // Templated
		  .se			(se_buf5_bottom));	 // Templated
   /*
 pcx_buf_pt AUTO_TEMPLATE(
		  // Outputs
		  .out0_l		(spc@_pcx_req_bufpt_pq_l[4:0]),
		  .out1_l		(spc@_pcx_atom_bufpt_pq_l),
	          .pcx_spc_grant_px	(pcx_spc@_grant_px[4:0]), 
                  .so                   (pt2_so_0),
		  // Inputs
                  .si                   (pt4_so_0),
                  .se                   (se_buf3_top),
		  .in0			(spc@_pcx_req_pq[4:0]),
		  .in1			(spc@_pcx_atom_pq),
                  .pcx_spc_grant_buf_pa	(pcx_spc@_grant_bufpdl_pa[4:0]),);
 */

   pcx_buf_pt pt2(/*AUTOINST*/
		  // Outputs
		  .out0_l		(spc2_pcx_req_bufpt_pq_l[4:0]), // Templated
		  .out1_l		(spc2_pcx_atom_bufpt_pq_l), // Templated
		  .pcx_spc_grant_px	(pcx_spc2_grant_px[4:0]), // Templated
		  .so			(pt2_so_0),		 // Templated
		  // Inputs
		  .in0			(spc2_pcx_req_pq[4:0]),	 // Templated
		  .in1			(spc2_pcx_atom_pq),	 // Templated
		  .pcx_spc_grant_buf_pa	(pcx_spc2_grant_bufpdl_pa[4:0]), // Templated
		  .rclk			(rclk),
		  .si			(pt4_so_0),		 // Templated
		  .se			(se_buf3_top));		 // Templated
   /*
 pcx_buf_pt AUTO_TEMPLATE(
		  // Outputs
		  .out0_l		(spc@_pcx_req_bufpt_pq_l[4:0]),
		  .out1_l		(spc@_pcx_atom_bufpt_pq_l),
	          .pcx_spc_grant_px	(pcx_spc@_grant_px[4:0]), 
                  .so                   (pt5_so_0),
		  // Inputs
                  .si                   (pt3_so_0),
                  .se                   (se_buf3_bottom),
		  .in0			(spc@_pcx_req_pq[4:0]),
		  .in1			(spc@_pcx_atom_pq),
                  .pcx_spc_grant_buf_pa	(pcx_spc@_grant_bufpdr_pa[4:0]),);
 */

   pcx_buf_pt pt5(/*AUTOINST*/
		  // Outputs
		  .out0_l		(spc5_pcx_req_bufpt_pq_l[4:0]), // Templated
		  .out1_l		(spc5_pcx_atom_bufpt_pq_l), // Templated
		  .pcx_spc_grant_px	(pcx_spc5_grant_px[4:0]), // Templated
		  .so			(pt5_so_0),		 // Templated
		  // Inputs
		  .in0			(spc5_pcx_req_pq[4:0]),	 // Templated
		  .in1			(spc5_pcx_atom_pq),	 // Templated
		  .pcx_spc_grant_buf_pa	(pcx_spc5_grant_bufpdr_pa[4:0]), // Templated
		  .rclk			(rclk),
		  .si			(pt3_so_0),		 // Templated
		  .se			(se_buf3_bottom));	 // Templated
   /*
 pcx_buf_pt AUTO_TEMPLATE(
		  // Outputs
		  .out0_l		(spc@_pcx_req_bufpt_pq_l[4:0]),
		  .out1_l		(spc@_pcx_atom_bufpt_pq_l),
	          .pcx_spc_grant_px	(pcx_spc@_grant_px[4:0]), 
                  .so                   (pt6_so_0),
		  // Inputs
                  .si                   (pt7_so_0),
                  .se                   (se_buf1_top),
		  .in0			(spc@_pcx_req_pq[4:0]),
		  .in1			(spc@_pcx_atom_pq),
                  .pcx_spc_grant_buf_pa	(pcx_spc@_grant_bufpdr_pa[4:0]),);
 */

   pcx_buf_pt pt6(/*AUTOINST*/
		  // Outputs
		  .out0_l		(spc6_pcx_req_bufpt_pq_l[4:0]), // Templated
		  .out1_l		(spc6_pcx_atom_bufpt_pq_l), // Templated
		  .pcx_spc_grant_px	(pcx_spc6_grant_px[4:0]), // Templated
		  .so			(pt6_so_0),		 // Templated
		  // Inputs
		  .in0			(spc6_pcx_req_pq[4:0]),	 // Templated
		  .in1			(spc6_pcx_atom_pq),	 // Templated
		  .pcx_spc_grant_buf_pa	(pcx_spc6_grant_bufpdr_pa[4:0]), // Templated
		  .rclk			(rclk),
		  .si			(pt7_so_0),		 // Templated
		  .se			(se_buf1_top));		 // Templated
   /*
 pcx_buf_pt AUTO_TEMPLATE(
		  // Outputs
		  .out0_l		(spc@_pcx_req_bufpt_pq_l[4:0]),
		  .out1_l		(spc@_pcx_atom_bufpt_pq_l),
	          .pcx_spc_grant_px	(pcx_spc@_grant_px[4:0]), 
                  .so                   (pt7_so_0),
		  // Inputs
                  .si                   (pt5_so_0),
                  .se                   (se_buf1_bottom),
		  .in0			(spc@_pcx_req_pq[4:0]),
		  .in1			(spc@_pcx_atom_pq),
                  .pcx_spc_grant_buf_pa	(pcx_spc@_grant_bufp4_pa[4:0]),);
 */

   pcx_buf_pt pt7(/*AUTOINST*/
		  // Outputs
		  .out0_l		(spc7_pcx_req_bufpt_pq_l[4:0]), // Templated
		  .out1_l		(spc7_pcx_atom_bufpt_pq_l), // Templated
		  .pcx_spc_grant_px	(pcx_spc7_grant_px[4:0]), // Templated
		  .so			(pt7_so_0),		 // Templated
		  // Inputs
		  .in0			(spc7_pcx_req_pq[4:0]),	 // Templated
		  .in1			(spc7_pcx_atom_pq),	 // Templated
		  .pcx_spc_grant_buf_pa	(pcx_spc7_grant_bufp4_pa[4:0]), // Templated
		  .rclk			(rclk),
		  .si			(pt5_so_0),		 // Templated
		  .se			(se_buf1_bottom));	 // Templated
/*
 pcx_buf_pt1 AUTO_TEMPLATE(
		  // Outputs
		  .out0		        (spc@_pcx_req_bufpt1_pq[4:0]),
		  .out1		        (spc@_pcx_atom_bufpt1_pq),
		  .pcx_spc_grant_px	(pcx_spc@_grant_px[4:0]),
                  .so                   (pt3_so_0),
		  // Inputs
                  .si                   (si_0),
                  .se                   (se_buf3_bottom),
		  .in0			(spc@_pcx_req_pq[4:0]),
		  .in1			(spc@_pcx_atom_pq),
		  .pcx_spc_grant_buf_pa (pcx_spc@_grant_bufpm_pa[4:0]));

 */

   pcx_buf_pt1 pt3(/*AUTOINST*/
		   // Outputs
		   .out0		(spc3_pcx_req_bufpt1_pq[4:0]), // Templated
		   .out1		(spc3_pcx_atom_bufpt1_pq), // Templated
		   .pcx_spc_grant_px	(pcx_spc3_grant_px[4:0]), // Templated
		   .so			(pt3_so_0),		 // Templated
		   // Inputs
		   .in0			(spc3_pcx_req_pq[4:0]),	 // Templated
		   .in1			(spc3_pcx_atom_pq),	 // Templated
		   .pcx_spc_grant_buf_pa(pcx_spc3_grant_bufpm_pa[4:0]), // Templated
		   .rclk		(rclk),
		   .si			(si_0),			 // Templated
		   .se			(se_buf3_bottom));	 // Templated
/*
 pcx_buf_pt1 AUTO_TEMPLATE(
		  // Outputs
		  .out0		        (spc@_pcx_req_bufpt1_pq[4:0]),
		  .out1		        (spc@_pcx_atom_bufpt1_pq),
		  .pcx_spc_grant_px	(pcx_spc@_grant_px[4:0]),
                  .so                   (pt4_so_0),
		  // Inputs
                  .si                   (pt6_so_0),
                  .se                   (se_buf3_top),
		  .in0			(spc@_pcx_req_pq[4:0]),
		  .in1			(spc@_pcx_atom_pq),
		  .pcx_spc_grant_buf_pa (pcx_spc@_grant_bufpm_pa[4:0]));

 */
   pcx_buf_pt1 pt4(/*AUTOINST*/
		   // Outputs
		   .out0		(spc4_pcx_req_bufpt1_pq[4:0]), // Templated
		   .out1		(spc4_pcx_atom_bufpt1_pq), // Templated
		   .pcx_spc_grant_px	(pcx_spc4_grant_px[4:0]), // Templated
		   .so			(pt4_so_0),		 // Templated
		   // Inputs
		   .in0			(spc4_pcx_req_pq[4:0]),	 // Templated
		   .in1			(spc4_pcx_atom_pq),	 // Templated
		   .pcx_spc_grant_buf_pa(pcx_spc4_grant_bufpm_pa[4:0]), // Templated
		   .rclk		(rclk),
		   .si			(pt6_so_0),		 // Templated
		   .se			(se_buf3_top));		 // Templated
   pcx_buf_p0 p0(/*AUTOINST*/
		 // Outputs
		 .pcx_spc0_grant_bufp0_pa(pcx_spc0_grant_bufp0_pa[4:0]),
		 .spc0_pcx_req_bufp0_pq	(spc0_pcx_req_bufp0_pq[4:0]),
		 .spc0_pcx_atom_bufp0_pq(spc0_pcx_atom_bufp0_pq),
		 .spc1_pcx_req_bufp0_pq	(spc1_pcx_req_bufp0_pq[4:0]),
		 .spc1_pcx_atom_bufp0_pq(spc1_pcx_atom_bufp0_pq),
		 // Inputs
		 .spc0_pcx_req_bufpt_pq_l(spc0_pcx_req_bufpt_pq_l[4:0]),
		 .spc0_pcx_atom_bufpt_pq_l(spc0_pcx_atom_bufpt_pq_l),
		 .spc1_pcx_req_bufpt_pq_l(spc1_pcx_req_bufpt_pq_l[4:0]),
		 .spc1_pcx_atom_bufpt_pq_l(spc1_pcx_atom_bufpt_pq_l),
		 .pcx_spc0_grant_bufp1_pa_l(pcx_spc0_grant_bufp1_pa_l[4:0]));

  /* pcx_buf_p0_even AUTO_TEMPLATE(
		 // Outputs
		 .arbpc0_pcxdp_grant_pa	(arbpc0_pcxdp_grant_pa[0]),
		 .arbpc0_pcxdp_q0_hold_pa_l(arbpc0_pcxdp_q0_hold_pa_l[0]),
		 .arbpc0_pcxdp_qsel0_pa	(arbpc0_pcxdp_qsel0_pa[0]),
		 .arbpc0_pcxdp_qsel1_pa_l(arbpc0_pcxdp_qsel1_pa_l[0]),
		 .arbpc0_pcxdp_shift_px	(arbpc0_pcxdp_shift_px[0]),
		 .arbpc2_pcxdp_grant_pa	(arbpc2_pcxdp_grant_pa[0]),
		 .arbpc2_pcxdp_q0_hold_pa_l(arbpc2_pcxdp_q0_hold_pa_l[0]),
		 .arbpc2_pcxdp_qsel0_pa	(arbpc2_pcxdp_qsel0_pa[0]),
		 .arbpc2_pcxdp_qsel1_pa_l(arbpc2_pcxdp_qsel1_pa_l[0]),
		 .arbpc2_pcxdp_shift_px	(arbpc2_pcxdp_shift_px[0]),
		 // Inputs
   		 .arbpc0_pcxdp_grant_bufp1_pa_l(arbpc0_pcxdp_grant_bufp1_pa_l[0]),
		 .arbpc0_pcxdp_q0_hold_bufp1_pa(arbpc0_pcxdp_q0_hold_bufp1_pa[0]),
		 .arbpc0_pcxdp_qsel0_bufp1_pa_l(arbpc0_pcxdp_qsel0_bufp1_pa_l[0]),
		 .arbpc0_pcxdp_qsel1_bufp1_pa(arbpc0_pcxdp_qsel1_bufp1_pa[0]),
		 .arbpc0_pcxdp_shift_bufp1_px_l(arbpc0_pcxdp_shift_bufp1_px_l[0]),
		 .arbpc2_pcxdp_grant_bufp1_pa_l(arbpc2_pcxdp_grant_bufp1_pa_l[0]),
		 .arbpc2_pcxdp_q0_hold_bufp1_pa(arbpc2_pcxdp_q0_hold_bufp1_pa[0]),
		 .arbpc2_pcxdp_qsel0_bufp1_pa_l(arbpc2_pcxdp_qsel0_bufp1_pa_l[0]),
		 .arbpc2_pcxdp_qsel1_bufp1_pa(arbpc2_pcxdp_qsel1_bufp1_pa[0]),
		 .arbpc2_pcxdp_shift_bufp1_px_l(arbpc2_pcxdp_shift_bufp1_px_l[0]));
  */

  pcx_buf_p0_even p0_even(/*AUTOINST*/
			  // Outputs
			  .arbpc0_pcxdp_grant_pa(arbpc0_pcxdp_grant_pa[0]), // Templated
			  .arbpc0_pcxdp_q0_hold_pa_l(arbpc0_pcxdp_q0_hold_pa_l[0]), // Templated
			  .arbpc0_pcxdp_qsel0_pa(arbpc0_pcxdp_qsel0_pa[0]), // Templated
			  .arbpc0_pcxdp_qsel1_pa_l(arbpc0_pcxdp_qsel1_pa_l[0]), // Templated
			  .arbpc0_pcxdp_shift_px(arbpc0_pcxdp_shift_px[0]), // Templated
			  .arbpc2_pcxdp_grant_pa(arbpc2_pcxdp_grant_pa[0]), // Templated
			  .arbpc2_pcxdp_q0_hold_pa_l(arbpc2_pcxdp_q0_hold_pa_l[0]), // Templated
			  .arbpc2_pcxdp_qsel0_pa(arbpc2_pcxdp_qsel0_pa[0]), // Templated
			  .arbpc2_pcxdp_qsel1_pa_l(arbpc2_pcxdp_qsel1_pa_l[0]), // Templated
			  .arbpc2_pcxdp_shift_px(arbpc2_pcxdp_shift_px[0]), // Templated
			  .scache0_pcx_stall_bufp0even_pq(scache0_pcx_stall_bufp0even_pq),
			  // Inputs
			  .arbpc0_pcxdp_grant_bufp1_pa_l(arbpc0_pcxdp_grant_bufp1_pa_l[0]), // Templated
			  .arbpc0_pcxdp_q0_hold_bufp1_pa(arbpc0_pcxdp_q0_hold_bufp1_pa[0]), // Templated
			  .arbpc0_pcxdp_qsel0_bufp1_pa_l(arbpc0_pcxdp_qsel0_bufp1_pa_l[0]), // Templated
			  .arbpc0_pcxdp_qsel1_bufp1_pa(arbpc0_pcxdp_qsel1_bufp1_pa[0]), // Templated
			  .arbpc0_pcxdp_shift_bufp1_px_l(arbpc0_pcxdp_shift_bufp1_px_l[0]), // Templated
			  .arbpc2_pcxdp_grant_bufp1_pa_l(arbpc2_pcxdp_grant_bufp1_pa_l[0]), // Templated
			  .arbpc2_pcxdp_q0_hold_bufp1_pa(arbpc2_pcxdp_q0_hold_bufp1_pa[0]), // Templated
			  .arbpc2_pcxdp_qsel0_bufp1_pa_l(arbpc2_pcxdp_qsel0_bufp1_pa_l[0]), // Templated
			  .arbpc2_pcxdp_qsel1_bufp1_pa(arbpc2_pcxdp_qsel1_bufp1_pa[0]), // Templated
			  .arbpc2_pcxdp_shift_bufp1_px_l(arbpc2_pcxdp_shift_bufp1_px_l[0]), // Templated
			  .scache0_pcx_stall_pq(scache0_pcx_stall_pq));
  /* pcx_buf_p0_odd AUTO_TEMPLATE(
		 // Outputs
		 .arbpc1_pcxdp_grant_pa	(arbpc1_pcxdp_grant_pa[0]),
		 .arbpc1_pcxdp_q0_hold_pa_l(arbpc1_pcxdp_q0_hold_pa_l[0]),
		 .arbpc1_pcxdp_qsel0_pa	(arbpc1_pcxdp_qsel0_pa[0]),
		 .arbpc1_pcxdp_qsel1_pa_l(arbpc1_pcxdp_qsel1_pa_l[0]),
		 .arbpc1_pcxdp_shift_px	(arbpc1_pcxdp_shift_px[0]),
		 .arbpc3_pcxdp_grant_pa	(arbpc3_pcxdp_grant_pa[0]),
		 .arbpc3_pcxdp_q0_hold_pa_l(arbpc3_pcxdp_q0_hold_pa_l[0]),
		 .arbpc3_pcxdp_qsel0_pa	(arbpc3_pcxdp_qsel0_pa[0]),
		 .arbpc3_pcxdp_qsel1_pa_l(arbpc3_pcxdp_qsel1_pa_l[0]),
		 .arbpc3_pcxdp_shift_px	(arbpc3_pcxdp_shift_px[0]),
		 .arbpc4_pcxdp_grant_pa	(arbpc4_pcxdp_grant_pa[0]),
		 .arbpc4_pcxdp_q0_hold_pa_l(arbpc4_pcxdp_q0_hold_pa_l[0]),
		 .arbpc4_pcxdp_qsel0_pa	(arbpc4_pcxdp_qsel0_pa[0]),
		 .arbpc4_pcxdp_qsel1_pa_l(arbpc4_pcxdp_qsel1_pa_l[0]),
		 .arbpc4_pcxdp_shift_px	(arbpc4_pcxdp_shift_px[0]),
		 // Inputs
		 .arbpc1_pcxdp_grant_bufp1_pa_l(arbpc1_pcxdp_grant_bufp1_pa_l[0]),
		 .arbpc1_pcxdp_q0_hold_bufp1_pa(arbpc1_pcxdp_q0_hold_bufp1_pa[0]),
		 .arbpc1_pcxdp_qsel0_bufp1_pa_l(arbpc1_pcxdp_qsel0_bufp1_pa_l[0]),
		 .arbpc1_pcxdp_qsel1_bufp1_pa(arbpc1_pcxdp_qsel1_bufp1_pa[0]),
		 .arbpc1_pcxdp_shift_bufp1_px_l(arbpc1_pcxdp_shift_bufp1_px_l[0]),
		 .arbpc3_pcxdp_grant_bufp1_pa_l(arbpc3_pcxdp_grant_bufp1_pa_l[0]),
		 .arbpc3_pcxdp_q0_hold_bufp1_pa(arbpc3_pcxdp_q0_hold_bufp1_pa[0]),
		 .arbpc3_pcxdp_qsel0_bufp1_pa_l(arbpc3_pcxdp_qsel0_bufp1_pa_l[0]),
		 .arbpc3_pcxdp_qsel1_bufp1_pa(arbpc3_pcxdp_qsel1_bufp1_pa[0]),
		 .arbpc3_pcxdp_shift_bufp1_px_l(arbpc3_pcxdp_shift_bufp1_px_l[0]),
		 .arbpc4_pcxdp_grant_bufp1_pa_l(arbpc4_pcxdp_grant_bufp1_pa_l[0]),
		 .arbpc4_pcxdp_q0_hold_bufp1_pa(arbpc4_pcxdp_q0_hold_bufp1_pa[0]),
		 .arbpc4_pcxdp_qsel0_bufp1_pa_l(arbpc4_pcxdp_qsel0_bufp1_pa_l[0]),
		 .arbpc4_pcxdp_qsel1_bufp1_pa(arbpc4_pcxdp_qsel1_bufp1_pa[0]),
		 .arbpc4_pcxdp_shift_bufp1_px_l(arbpc4_pcxdp_shift_bufp1_px_l[0]));
*/
   pcx_buf_p0_odd p0_odd(/*AUTOINST*/
			 // Outputs
			 .arbpc1_pcxdp_grant_pa(arbpc1_pcxdp_grant_pa[0]), // Templated
			 .arbpc1_pcxdp_q0_hold_pa_l(arbpc1_pcxdp_q0_hold_pa_l[0]), // Templated
			 .arbpc1_pcxdp_qsel0_pa(arbpc1_pcxdp_qsel0_pa[0]), // Templated
			 .arbpc1_pcxdp_qsel1_pa_l(arbpc1_pcxdp_qsel1_pa_l[0]), // Templated
			 .arbpc1_pcxdp_shift_px(arbpc1_pcxdp_shift_px[0]), // Templated
			 .arbpc3_pcxdp_grant_pa(arbpc3_pcxdp_grant_pa[0]), // Templated
			 .arbpc3_pcxdp_q0_hold_pa_l(arbpc3_pcxdp_q0_hold_pa_l[0]), // Templated
			 .arbpc3_pcxdp_qsel0_pa(arbpc3_pcxdp_qsel0_pa[0]), // Templated
			 .arbpc3_pcxdp_qsel1_pa_l(arbpc3_pcxdp_qsel1_pa_l[0]), // Templated
			 .arbpc3_pcxdp_shift_px(arbpc3_pcxdp_shift_px[0]), // Templated
			 .arbpc4_pcxdp_grant_pa(arbpc4_pcxdp_grant_pa[0]), // Templated
			 .arbpc4_pcxdp_q0_hold_pa_l(arbpc4_pcxdp_q0_hold_pa_l[0]), // Templated
			 .arbpc4_pcxdp_qsel0_pa(arbpc4_pcxdp_qsel0_pa[0]), // Templated
			 .arbpc4_pcxdp_qsel1_pa_l(arbpc4_pcxdp_qsel1_pa_l[0]), // Templated
			 .arbpc4_pcxdp_shift_px(arbpc4_pcxdp_shift_px[0]), // Templated
			 .sctag1_pcx_stall_bufp0odd_pq(sctag1_pcx_stall_bufp0odd_pq),
			 // Inputs
			 .arbpc1_pcxdp_grant_bufp1_pa_l(arbpc1_pcxdp_grant_bufp1_pa_l[0]), // Templated
			 .arbpc1_pcxdp_q0_hold_bufp1_pa(arbpc1_pcxdp_q0_hold_bufp1_pa[0]), // Templated
			 .arbpc1_pcxdp_qsel0_bufp1_pa_l(arbpc1_pcxdp_qsel0_bufp1_pa_l[0]), // Templated
			 .arbpc1_pcxdp_qsel1_bufp1_pa(arbpc1_pcxdp_qsel1_bufp1_pa[0]), // Templated
			 .arbpc1_pcxdp_shift_bufp1_px_l(arbpc1_pcxdp_shift_bufp1_px_l[0]), // Templated
			 .arbpc3_pcxdp_grant_bufp1_pa_l(arbpc3_pcxdp_grant_bufp1_pa_l[0]), // Templated
			 .arbpc3_pcxdp_q0_hold_bufp1_pa(arbpc3_pcxdp_q0_hold_bufp1_pa[0]), // Templated
			 .arbpc3_pcxdp_qsel0_bufp1_pa_l(arbpc3_pcxdp_qsel0_bufp1_pa_l[0]), // Templated
			 .arbpc3_pcxdp_qsel1_bufp1_pa(arbpc3_pcxdp_qsel1_bufp1_pa[0]), // Templated
			 .arbpc3_pcxdp_shift_bufp1_px_l(arbpc3_pcxdp_shift_bufp1_px_l[0]), // Templated
			 .arbpc4_pcxdp_grant_bufp1_pa_l(arbpc4_pcxdp_grant_bufp1_pa_l[0]), // Templated
			 .arbpc4_pcxdp_q0_hold_bufp1_pa(arbpc4_pcxdp_q0_hold_bufp1_pa[0]), // Templated
			 .arbpc4_pcxdp_qsel0_bufp1_pa_l(arbpc4_pcxdp_qsel0_bufp1_pa_l[0]), // Templated
			 .arbpc4_pcxdp_qsel1_bufp1_pa(arbpc4_pcxdp_qsel1_bufp1_pa[0]), // Templated
			 .arbpc4_pcxdp_shift_bufp1_px_l(arbpc4_pcxdp_shift_bufp1_px_l[0]), // Templated
			 .sctag1_pcx_stall_pq(sctag1_pcx_stall_pq));
   pcx_buf_p1 p1(/*AUTOINST*/
		 // Outputs
		 .scache0_pcx_stall_bufp1_pq(scache0_pcx_stall_bufp1_pq),
		 .spc0_pcx_req_bufp1_pq	(spc0_pcx_req_bufp1_pq[4:0]),
		 .spc0_pcx_atom_bufp1_pq(spc0_pcx_atom_bufp1_pq),
		 .spc1_pcx_req_bufp1_pq	(spc1_pcx_req_bufp1_pq[4:0]),
		 .spc1_pcx_atom_bufp1_pq(spc1_pcx_atom_bufp1_pq),
		 .spc2_pcx_req_bufp1_pq	(spc2_pcx_req_bufp1_pq[4:0]),
		 .spc2_pcx_atom_bufp1_pq(spc2_pcx_atom_bufp1_pq),
		 .spc3_pcx_req_bufp1_pq	(spc3_pcx_req_bufp1_pq[4:0]),
		 .spc3_pcx_atom_bufp1_pq(spc3_pcx_atom_bufp1_pq),
		 .spc4_pcx_req_bufp1_pq	(spc4_pcx_req_bufp1_pq[4:0]),
		 .spc4_pcx_atom_bufp1_pq(spc4_pcx_atom_bufp1_pq),
		 .pcx_spc0_grant_bufp1_pa_l(pcx_spc0_grant_bufp1_pa_l[4:0]),
		 .pcx_spc1_grant_bufp1_pa_l(pcx_spc1_grant_bufp1_pa_l[4:0]),
		 .pcx_spc2_grant_bufp1_pa_l(pcx_spc2_grant_bufp1_pa_l[4:0]),
		 .arbpc0_pcxdp_grant_bufp1_pa_l(arbpc0_pcxdp_grant_bufp1_pa_l[2:0]),
		 .arbpc0_pcxdp_q0_hold_bufp1_pa(arbpc0_pcxdp_q0_hold_bufp1_pa[2:0]),
		 .arbpc0_pcxdp_qsel0_bufp1_pa_l(arbpc0_pcxdp_qsel0_bufp1_pa_l[2:0]),
		 .arbpc0_pcxdp_qsel1_bufp1_pa(arbpc0_pcxdp_qsel1_bufp1_pa[2:0]),
		 .arbpc0_pcxdp_shift_bufp1_px_l(arbpc0_pcxdp_shift_bufp1_px_l[2:0]),
		 .arbpc1_pcxdp_grant_bufp1_pa_l(arbpc1_pcxdp_grant_bufp1_pa_l[2:0]),
		 .arbpc1_pcxdp_q0_hold_bufp1_pa(arbpc1_pcxdp_q0_hold_bufp1_pa[2:0]),
		 .arbpc1_pcxdp_qsel0_bufp1_pa_l(arbpc1_pcxdp_qsel0_bufp1_pa_l[2:0]),
		 .arbpc1_pcxdp_qsel1_bufp1_pa(arbpc1_pcxdp_qsel1_bufp1_pa[2:0]),
		 .arbpc1_pcxdp_shift_bufp1_px_l(arbpc1_pcxdp_shift_bufp1_px_l[2:0]),
		 .arbpc2_pcxdp_grant_bufp1_pa_l(arbpc2_pcxdp_grant_bufp1_pa_l[2:0]),
		 .arbpc2_pcxdp_q0_hold_bufp1_pa(arbpc2_pcxdp_q0_hold_bufp1_pa[2:0]),
		 .arbpc2_pcxdp_qsel0_bufp1_pa_l(arbpc2_pcxdp_qsel0_bufp1_pa_l[2:0]),
		 .arbpc2_pcxdp_qsel1_bufp1_pa(arbpc2_pcxdp_qsel1_bufp1_pa[2:0]),
		 .arbpc2_pcxdp_shift_bufp1_px_l(arbpc2_pcxdp_shift_bufp1_px_l[2:0]),
		 .arbpc3_pcxdp_grant_bufp1_pa_l(arbpc3_pcxdp_grant_bufp1_pa_l[2:0]),
		 .arbpc3_pcxdp_q0_hold_bufp1_pa(arbpc3_pcxdp_q0_hold_bufp1_pa[2:0]),
		 .arbpc3_pcxdp_qsel0_bufp1_pa_l(arbpc3_pcxdp_qsel0_bufp1_pa_l[2:0]),
		 .arbpc3_pcxdp_qsel1_bufp1_pa(arbpc3_pcxdp_qsel1_bufp1_pa[2:0]),
		 .arbpc3_pcxdp_shift_bufp1_px_l(arbpc3_pcxdp_shift_bufp1_px_l[2:0]),
		 .arbpc4_pcxdp_grant_bufp1_pa_l(arbpc4_pcxdp_grant_bufp1_pa_l[2:0]),
		 .arbpc4_pcxdp_q0_hold_bufp1_pa(arbpc4_pcxdp_q0_hold_bufp1_pa[2:0]),
		 .arbpc4_pcxdp_qsel0_bufp1_pa_l(arbpc4_pcxdp_qsel0_bufp1_pa_l[2:0]),
		 .arbpc4_pcxdp_qsel1_bufp1_pa(arbpc4_pcxdp_qsel1_bufp1_pa[2:0]),
		 .arbpc4_pcxdp_shift_bufp1_px_l(arbpc4_pcxdp_shift_bufp1_px_l[2:0]),
		 .sctag1_pcx_stall_bufp1_pq(sctag1_pcx_stall_bufp1_pq),
		 // Inputs
		 .scache0_pcx_stall_bufp0even_pq(scache0_pcx_stall_bufp0even_pq),
		 .spc0_pcx_req_bufp0_pq	(spc0_pcx_req_bufp0_pq[4:0]),
		 .spc0_pcx_atom_bufp0_pq(spc0_pcx_atom_bufp0_pq),
		 .spc1_pcx_req_bufp0_pq	(spc1_pcx_req_bufp0_pq[4:0]),
		 .spc1_pcx_atom_bufp0_pq(spc1_pcx_atom_bufp0_pq),
		 .spc2_pcx_req_bufpt_pq_l(spc2_pcx_req_bufpt_pq_l[4:0]),
		 .spc2_pcx_atom_bufpt_pq_l(spc2_pcx_atom_bufpt_pq_l),
		 .spc3_pcx_req_bufpt1_pq(spc3_pcx_req_bufpt1_pq[4:0]),
		 .spc3_pcx_atom_bufpt1_pq(spc3_pcx_atom_bufpt1_pq),
		 .spc4_pcx_req_bufpt1_pq(spc4_pcx_req_bufpt1_pq[4:0]),
		 .spc4_pcx_atom_bufpt1_pq(spc4_pcx_atom_bufpt1_pq),
		 .pcx_spc0_grant_pa	(pcx_spc0_grant_pa[4:0]),
		 .pcx_spc1_grant_pa	(pcx_spc1_grant_pa[4:0]),
		 .pcx_spc2_grant_pa	(pcx_spc2_grant_pa[4:0]),
		 .arbpc0_pcxdp_grant_arbbf_pa(arbpc0_pcxdp_grant_arbbf_pa[2:0]),
		 .arbpc0_pcxdp_q0_hold_arbbf_pa_l(arbpc0_pcxdp_q0_hold_arbbf_pa_l[2:0]),
		 .arbpc0_pcxdp_qsel0_arbbf_pa(arbpc0_pcxdp_qsel0_arbbf_pa[2:0]),
		 .arbpc0_pcxdp_qsel1_arbbf_pa_l(arbpc0_pcxdp_qsel1_arbbf_pa_l[2:0]),
		 .arbpc0_pcxdp_shift_arbbf_px(arbpc0_pcxdp_shift_arbbf_px[2:0]),
		 .arbpc1_pcxdp_grant_arbbf_pa(arbpc1_pcxdp_grant_arbbf_pa[2:0]),
		 .arbpc1_pcxdp_q0_hold_arbbf_pa_l(arbpc1_pcxdp_q0_hold_arbbf_pa_l[2:0]),
		 .arbpc1_pcxdp_qsel0_arbbf_pa(arbpc1_pcxdp_qsel0_arbbf_pa[2:0]),
		 .arbpc1_pcxdp_qsel1_arbbf_pa_l(arbpc1_pcxdp_qsel1_arbbf_pa_l[2:0]),
		 .arbpc1_pcxdp_shift_arbbf_px(arbpc1_pcxdp_shift_arbbf_px[2:0]),
		 .arbpc2_pcxdp_grant_arbbf_pa(arbpc2_pcxdp_grant_arbbf_pa[2:0]),
		 .arbpc2_pcxdp_q0_hold_arbbf_pa_l(arbpc2_pcxdp_q0_hold_arbbf_pa_l[2:0]),
		 .arbpc2_pcxdp_qsel0_arbbf_pa(arbpc2_pcxdp_qsel0_arbbf_pa[2:0]),
		 .arbpc2_pcxdp_qsel1_arbbf_pa_l(arbpc2_pcxdp_qsel1_arbbf_pa_l[2:0]),
		 .arbpc2_pcxdp_shift_arbbf_px(arbpc2_pcxdp_shift_arbbf_px[2:0]),
		 .arbpc3_pcxdp_grant_arbbf_pa(arbpc3_pcxdp_grant_arbbf_pa[2:0]),
		 .arbpc3_pcxdp_q0_hold_arbbf_pa_l(arbpc3_pcxdp_q0_hold_arbbf_pa_l[2:0]),
		 .arbpc3_pcxdp_qsel0_arbbf_pa(arbpc3_pcxdp_qsel0_arbbf_pa[2:0]),
		 .arbpc3_pcxdp_qsel1_arbbf_pa_l(arbpc3_pcxdp_qsel1_arbbf_pa_l[2:0]),
		 .arbpc3_pcxdp_shift_arbbf_px(arbpc3_pcxdp_shift_arbbf_px[2:0]),
		 .arbpc4_pcxdp_grant_arbbf_pa(arbpc4_pcxdp_grant_arbbf_pa[2:0]),
		 .arbpc4_pcxdp_q0_hold_arbbf_pa_l(arbpc4_pcxdp_q0_hold_arbbf_pa_l[2:0]),
		 .arbpc4_pcxdp_qsel0_arbbf_pa(arbpc4_pcxdp_qsel0_arbbf_pa[2:0]),
		 .arbpc4_pcxdp_qsel1_arbbf_pa_l(arbpc4_pcxdp_qsel1_arbbf_pa_l[2:0]),
		 .arbpc4_pcxdp_shift_arbbf_px(arbpc4_pcxdp_shift_arbbf_px[2:0]),
		 .sctag1_pcx_stall_bufp0odd_pq(sctag1_pcx_stall_bufp0odd_pq)); 

   /* pcx_buf_pdl AUTO_TEMPLATE(
    		  // Outputs
                  .pcx_spc_grant_bufpdl_pa(pcx_spc@_grant_bufpdl_pa[4:0]),
		  // Inputs
         	  .pcx_spc_grant_bufp1_pa_l(pcx_spc@_grant_bufp1_pa_l[4:0]));
  */

   pcx_buf_pdl pdl1(/*AUTOINST*/
		    // Outputs
		    .pcx_spc_grant_bufpdl_pa(pcx_spc1_grant_bufpdl_pa[4:0]), // Templated
		    // Inputs
		    .pcx_spc_grant_bufp1_pa_l(pcx_spc1_grant_bufp1_pa_l[4:0])); // Templated
   pcx_buf_pdl pdl2(/*AUTOINST*/
		    // Outputs
		    .pcx_spc_grant_bufpdl_pa(pcx_spc2_grant_bufpdl_pa[4:0]), // Templated
		    // Inputs
		    .pcx_spc_grant_bufp1_pa_l(pcx_spc2_grant_bufp1_pa_l[4:0])); // Templated
   /* pcx_buf_pdl_even AUTO_TEMPLATE(
    		  // Outputs
    		  .arbpc0_pcxdp_grant_pa(arbpc0_pcxdp_grant_pa[@]),
		  .arbpc0_pcxdp_q0_hold_pa_l(arbpc0_pcxdp_q0_hold_pa_l[@]),
		  .arbpc0_pcxdp_qsel0_pa(arbpc0_pcxdp_qsel0_pa[@]),
		  .arbpc0_pcxdp_qsel1_pa_l(arbpc0_pcxdp_qsel1_pa_l[@]),
		  .arbpc0_pcxdp_shift_px(arbpc0_pcxdp_shift_px[@]),
		  .arbpc2_pcxdp_grant_pa(arbpc2_pcxdp_grant_pa[@]),
		  .arbpc2_pcxdp_q0_hold_pa_l(arbpc2_pcxdp_q0_hold_pa_l[@]),
		  .arbpc2_pcxdp_qsel0_pa(arbpc2_pcxdp_qsel0_pa[@]),
		  .arbpc2_pcxdp_qsel1_pa_l(arbpc2_pcxdp_qsel1_pa_l[@]),
		  .arbpc2_pcxdp_shift_px(arbpc2_pcxdp_shift_px[@]),
		  // Inputs
		  .arbpc0_pcxdp_grant_bufp1_pa_l(arbpc0_pcxdp_grant_bufp1_pa_l[@]),
		  .arbpc0_pcxdp_q0_hold_bufp1_pa(arbpc0_pcxdp_q0_hold_bufp1_pa[@]),
		  .arbpc0_pcxdp_qsel0_bufp1_pa_l(arbpc0_pcxdp_qsel0_bufp1_pa_l[@]),
		  .arbpc0_pcxdp_qsel1_bufp1_pa(arbpc0_pcxdp_qsel1_bufp1_pa[@]),
		  .arbpc0_pcxdp_shift_bufp1_px_l(arbpc0_pcxdp_shift_bufp1_px_l[@]),
		  .arbpc2_pcxdp_grant_bufp1_pa_l(arbpc2_pcxdp_grant_bufp1_pa_l[@]),
		  .arbpc2_pcxdp_q0_hold_bufp1_pa(arbpc2_pcxdp_q0_hold_bufp1_pa[@]),
		  .arbpc2_pcxdp_qsel0_bufp1_pa_l(arbpc2_pcxdp_qsel0_bufp1_pa_l[@]),
		  .arbpc2_pcxdp_qsel1_bufp1_pa(arbpc2_pcxdp_qsel1_bufp1_pa[@]),
		  .arbpc2_pcxdp_shift_bufp1_px_l(arbpc2_pcxdp_shift_bufp1_px_l[@]));
   */

   pcx_buf_pdl_even pdl1_even(/*AUTOINST*/
			      // Outputs
			      .arbpc0_pcxdp_grant_pa(arbpc0_pcxdp_grant_pa[1]), // Templated
			      .arbpc0_pcxdp_q0_hold_pa_l(arbpc0_pcxdp_q0_hold_pa_l[1]), // Templated
			      .arbpc0_pcxdp_qsel0_pa(arbpc0_pcxdp_qsel0_pa[1]), // Templated
			      .arbpc0_pcxdp_qsel1_pa_l(arbpc0_pcxdp_qsel1_pa_l[1]), // Templated
			      .arbpc0_pcxdp_shift_px(arbpc0_pcxdp_shift_px[1]), // Templated
			      .arbpc2_pcxdp_grant_pa(arbpc2_pcxdp_grant_pa[1]), // Templated
			      .arbpc2_pcxdp_q0_hold_pa_l(arbpc2_pcxdp_q0_hold_pa_l[1]), // Templated
			      .arbpc2_pcxdp_qsel0_pa(arbpc2_pcxdp_qsel0_pa[1]), // Templated
			      .arbpc2_pcxdp_qsel1_pa_l(arbpc2_pcxdp_qsel1_pa_l[1]), // Templated
			      .arbpc2_pcxdp_shift_px(arbpc2_pcxdp_shift_px[1]), // Templated
			      // Inputs
			      .arbpc0_pcxdp_grant_bufp1_pa_l(arbpc0_pcxdp_grant_bufp1_pa_l[1]), // Templated
			      .arbpc0_pcxdp_q0_hold_bufp1_pa(arbpc0_pcxdp_q0_hold_bufp1_pa[1]), // Templated
			      .arbpc0_pcxdp_qsel0_bufp1_pa_l(arbpc0_pcxdp_qsel0_bufp1_pa_l[1]), // Templated
			      .arbpc0_pcxdp_qsel1_bufp1_pa(arbpc0_pcxdp_qsel1_bufp1_pa[1]), // Templated
			      .arbpc0_pcxdp_shift_bufp1_px_l(arbpc0_pcxdp_shift_bufp1_px_l[1]), // Templated
			      .arbpc2_pcxdp_grant_bufp1_pa_l(arbpc2_pcxdp_grant_bufp1_pa_l[1]), // Templated
			      .arbpc2_pcxdp_q0_hold_bufp1_pa(arbpc2_pcxdp_q0_hold_bufp1_pa[1]), // Templated
			      .arbpc2_pcxdp_qsel0_bufp1_pa_l(arbpc2_pcxdp_qsel0_bufp1_pa_l[1]), // Templated
			      .arbpc2_pcxdp_qsel1_bufp1_pa(arbpc2_pcxdp_qsel1_bufp1_pa[1]), // Templated
			      .arbpc2_pcxdp_shift_bufp1_px_l(arbpc2_pcxdp_shift_bufp1_px_l[1])); // Templated
   pcx_buf_pdl_even pdl2_even(/*AUTOINST*/
			      // Outputs
			      .arbpc0_pcxdp_grant_pa(arbpc0_pcxdp_grant_pa[2]), // Templated
			      .arbpc0_pcxdp_q0_hold_pa_l(arbpc0_pcxdp_q0_hold_pa_l[2]), // Templated
			      .arbpc0_pcxdp_qsel0_pa(arbpc0_pcxdp_qsel0_pa[2]), // Templated
			      .arbpc0_pcxdp_qsel1_pa_l(arbpc0_pcxdp_qsel1_pa_l[2]), // Templated
			      .arbpc0_pcxdp_shift_px(arbpc0_pcxdp_shift_px[2]), // Templated
			      .arbpc2_pcxdp_grant_pa(arbpc2_pcxdp_grant_pa[2]), // Templated
			      .arbpc2_pcxdp_q0_hold_pa_l(arbpc2_pcxdp_q0_hold_pa_l[2]), // Templated
			      .arbpc2_pcxdp_qsel0_pa(arbpc2_pcxdp_qsel0_pa[2]), // Templated
			      .arbpc2_pcxdp_qsel1_pa_l(arbpc2_pcxdp_qsel1_pa_l[2]), // Templated
			      .arbpc2_pcxdp_shift_px(arbpc2_pcxdp_shift_px[2]), // Templated
			      // Inputs
			      .arbpc0_pcxdp_grant_bufp1_pa_l(arbpc0_pcxdp_grant_bufp1_pa_l[2]), // Templated
			      .arbpc0_pcxdp_q0_hold_bufp1_pa(arbpc0_pcxdp_q0_hold_bufp1_pa[2]), // Templated
			      .arbpc0_pcxdp_qsel0_bufp1_pa_l(arbpc0_pcxdp_qsel0_bufp1_pa_l[2]), // Templated
			      .arbpc0_pcxdp_qsel1_bufp1_pa(arbpc0_pcxdp_qsel1_bufp1_pa[2]), // Templated
			      .arbpc0_pcxdp_shift_bufp1_px_l(arbpc0_pcxdp_shift_bufp1_px_l[2]), // Templated
			      .arbpc2_pcxdp_grant_bufp1_pa_l(arbpc2_pcxdp_grant_bufp1_pa_l[2]), // Templated
			      .arbpc2_pcxdp_q0_hold_bufp1_pa(arbpc2_pcxdp_q0_hold_bufp1_pa[2]), // Templated
			      .arbpc2_pcxdp_qsel0_bufp1_pa_l(arbpc2_pcxdp_qsel0_bufp1_pa_l[2]), // Templated
			      .arbpc2_pcxdp_qsel1_bufp1_pa(arbpc2_pcxdp_qsel1_bufp1_pa[2]), // Templated
			      .arbpc2_pcxdp_shift_bufp1_px_l(arbpc2_pcxdp_shift_bufp1_px_l[2])); // Templated
   /* pcx_buf_pdl_odd AUTO_TEMPLATE(
    		  // Outputs
		  .arbpc1_pcxdp_grant_pa(arbpc1_pcxdp_grant_pa[@]),
		  .arbpc1_pcxdp_q0_hold_pa_l(arbpc1_pcxdp_q0_hold_pa_l[@]),
		  .arbpc1_pcxdp_qsel0_pa(arbpc1_pcxdp_qsel0_pa[@]),
		  .arbpc1_pcxdp_qsel1_pa_l(arbpc1_pcxdp_qsel1_pa_l[@]),
		  .arbpc1_pcxdp_shift_px(arbpc1_pcxdp_shift_px[@]),
		  .arbpc3_pcxdp_grant_pa(arbpc3_pcxdp_grant_pa[@]),
		  .arbpc3_pcxdp_q0_hold_pa_l(arbpc3_pcxdp_q0_hold_pa_l[@]),
		  .arbpc3_pcxdp_qsel0_pa(arbpc3_pcxdp_qsel0_pa[@]),
		  .arbpc3_pcxdp_qsel1_pa_l(arbpc3_pcxdp_qsel1_pa_l[@]),
		  .arbpc3_pcxdp_shift_px(arbpc3_pcxdp_shift_px[@]),
		  .arbpc4_pcxdp_grant_pa(arbpc4_pcxdp_grant_pa[@]),
		  .arbpc4_pcxdp_q0_hold_pa_l(arbpc4_pcxdp_q0_hold_pa_l[@]),
		  .arbpc4_pcxdp_qsel0_pa(arbpc4_pcxdp_qsel0_pa[@]),
		  .arbpc4_pcxdp_qsel1_pa_l(arbpc4_pcxdp_qsel1_pa_l[@]),
		  .arbpc4_pcxdp_shift_px(arbpc4_pcxdp_shift_px[@]),
		  // Inputs
		  .arbpc1_pcxdp_grant_bufp1_pa_l(arbpc1_pcxdp_grant_bufp1_pa_l[@]),
		  .arbpc1_pcxdp_q0_hold_bufp1_pa(arbpc1_pcxdp_q0_hold_bufp1_pa[@]),
		  .arbpc1_pcxdp_qsel0_bufp1_pa_l(arbpc1_pcxdp_qsel0_bufp1_pa_l[@]),
		  .arbpc1_pcxdp_qsel1_bufp1_pa(arbpc1_pcxdp_qsel1_bufp1_pa[@]),
		  .arbpc1_pcxdp_shift_bufp1_px_l(arbpc1_pcxdp_shift_bufp1_px_l[@]),
		  .arbpc3_pcxdp_grant_bufp1_pa_l(arbpc3_pcxdp_grant_bufp1_pa_l[@]),
		  .arbpc3_pcxdp_q0_hold_bufp1_pa(arbpc3_pcxdp_q0_hold_bufp1_pa[@]),
		  .arbpc3_pcxdp_qsel0_bufp1_pa_l(arbpc3_pcxdp_qsel0_bufp1_pa_l[@]),
		  .arbpc3_pcxdp_qsel1_bufp1_pa(arbpc3_pcxdp_qsel1_bufp1_pa[@]),
		  .arbpc3_pcxdp_shift_bufp1_px_l(arbpc3_pcxdp_shift_bufp1_px_l[@]),
		  .arbpc4_pcxdp_grant_bufp1_pa_l(arbpc4_pcxdp_grant_bufp1_pa_l[@]),
		  .arbpc4_pcxdp_q0_hold_bufp1_pa(arbpc4_pcxdp_q0_hold_bufp1_pa[@]),
		  .arbpc4_pcxdp_qsel0_bufp1_pa_l(arbpc4_pcxdp_qsel0_bufp1_pa_l[@]),
		  .arbpc4_pcxdp_qsel1_bufp1_pa(arbpc4_pcxdp_qsel1_bufp1_pa[@]),
		  .arbpc4_pcxdp_shift_bufp1_px_l(arbpc4_pcxdp_shift_bufp1_px_l[@]));
 */


   pcx_buf_pdl_odd pdl1_odd(/*AUTOINST*/
			    // Outputs
			    .arbpc1_pcxdp_grant_pa(arbpc1_pcxdp_grant_pa[1]), // Templated
			    .arbpc1_pcxdp_q0_hold_pa_l(arbpc1_pcxdp_q0_hold_pa_l[1]), // Templated
			    .arbpc1_pcxdp_qsel0_pa(arbpc1_pcxdp_qsel0_pa[1]), // Templated
			    .arbpc1_pcxdp_qsel1_pa_l(arbpc1_pcxdp_qsel1_pa_l[1]), // Templated
			    .arbpc1_pcxdp_shift_px(arbpc1_pcxdp_shift_px[1]), // Templated
			    .arbpc3_pcxdp_grant_pa(arbpc3_pcxdp_grant_pa[1]), // Templated
			    .arbpc3_pcxdp_q0_hold_pa_l(arbpc3_pcxdp_q0_hold_pa_l[1]), // Templated
			    .arbpc3_pcxdp_qsel0_pa(arbpc3_pcxdp_qsel0_pa[1]), // Templated
			    .arbpc3_pcxdp_qsel1_pa_l(arbpc3_pcxdp_qsel1_pa_l[1]), // Templated
			    .arbpc3_pcxdp_shift_px(arbpc3_pcxdp_shift_px[1]), // Templated
			    .arbpc4_pcxdp_grant_pa(arbpc4_pcxdp_grant_pa[1]), // Templated
			    .arbpc4_pcxdp_q0_hold_pa_l(arbpc4_pcxdp_q0_hold_pa_l[1]), // Templated
			    .arbpc4_pcxdp_qsel0_pa(arbpc4_pcxdp_qsel0_pa[1]), // Templated
			    .arbpc4_pcxdp_qsel1_pa_l(arbpc4_pcxdp_qsel1_pa_l[1]), // Templated
			    .arbpc4_pcxdp_shift_px(arbpc4_pcxdp_shift_px[1]), // Templated
			    // Inputs
			    .arbpc1_pcxdp_grant_bufp1_pa_l(arbpc1_pcxdp_grant_bufp1_pa_l[1]), // Templated
			    .arbpc1_pcxdp_q0_hold_bufp1_pa(arbpc1_pcxdp_q0_hold_bufp1_pa[1]), // Templated
			    .arbpc1_pcxdp_qsel0_bufp1_pa_l(arbpc1_pcxdp_qsel0_bufp1_pa_l[1]), // Templated
			    .arbpc1_pcxdp_qsel1_bufp1_pa(arbpc1_pcxdp_qsel1_bufp1_pa[1]), // Templated
			    .arbpc1_pcxdp_shift_bufp1_px_l(arbpc1_pcxdp_shift_bufp1_px_l[1]), // Templated
			    .arbpc3_pcxdp_grant_bufp1_pa_l(arbpc3_pcxdp_grant_bufp1_pa_l[1]), // Templated
			    .arbpc3_pcxdp_q0_hold_bufp1_pa(arbpc3_pcxdp_q0_hold_bufp1_pa[1]), // Templated
			    .arbpc3_pcxdp_qsel0_bufp1_pa_l(arbpc3_pcxdp_qsel0_bufp1_pa_l[1]), // Templated
			    .arbpc3_pcxdp_qsel1_bufp1_pa(arbpc3_pcxdp_qsel1_bufp1_pa[1]), // Templated
			    .arbpc3_pcxdp_shift_bufp1_px_l(arbpc3_pcxdp_shift_bufp1_px_l[1]), // Templated
			    .arbpc4_pcxdp_grant_bufp1_pa_l(arbpc4_pcxdp_grant_bufp1_pa_l[1]), // Templated
			    .arbpc4_pcxdp_q0_hold_bufp1_pa(arbpc4_pcxdp_q0_hold_bufp1_pa[1]), // Templated
			    .arbpc4_pcxdp_qsel0_bufp1_pa_l(arbpc4_pcxdp_qsel0_bufp1_pa_l[1]), // Templated
			    .arbpc4_pcxdp_qsel1_bufp1_pa(arbpc4_pcxdp_qsel1_bufp1_pa[1]), // Templated
			    .arbpc4_pcxdp_shift_bufp1_px_l(arbpc4_pcxdp_shift_bufp1_px_l[1])); // Templated
   pcx_buf_pdl_odd pdl2_odd(/*AUTOINST*/
			    // Outputs
			    .arbpc1_pcxdp_grant_pa(arbpc1_pcxdp_grant_pa[2]), // Templated
			    .arbpc1_pcxdp_q0_hold_pa_l(arbpc1_pcxdp_q0_hold_pa_l[2]), // Templated
			    .arbpc1_pcxdp_qsel0_pa(arbpc1_pcxdp_qsel0_pa[2]), // Templated
			    .arbpc1_pcxdp_qsel1_pa_l(arbpc1_pcxdp_qsel1_pa_l[2]), // Templated
			    .arbpc1_pcxdp_shift_px(arbpc1_pcxdp_shift_px[2]), // Templated
			    .arbpc3_pcxdp_grant_pa(arbpc3_pcxdp_grant_pa[2]), // Templated
			    .arbpc3_pcxdp_q0_hold_pa_l(arbpc3_pcxdp_q0_hold_pa_l[2]), // Templated
			    .arbpc3_pcxdp_qsel0_pa(arbpc3_pcxdp_qsel0_pa[2]), // Templated
			    .arbpc3_pcxdp_qsel1_pa_l(arbpc3_pcxdp_qsel1_pa_l[2]), // Templated
			    .arbpc3_pcxdp_shift_px(arbpc3_pcxdp_shift_px[2]), // Templated
			    .arbpc4_pcxdp_grant_pa(arbpc4_pcxdp_grant_pa[2]), // Templated
			    .arbpc4_pcxdp_q0_hold_pa_l(arbpc4_pcxdp_q0_hold_pa_l[2]), // Templated
			    .arbpc4_pcxdp_qsel0_pa(arbpc4_pcxdp_qsel0_pa[2]), // Templated
			    .arbpc4_pcxdp_qsel1_pa_l(arbpc4_pcxdp_qsel1_pa_l[2]), // Templated
			    .arbpc4_pcxdp_shift_px(arbpc4_pcxdp_shift_px[2]), // Templated
			    // Inputs
			    .arbpc1_pcxdp_grant_bufp1_pa_l(arbpc1_pcxdp_grant_bufp1_pa_l[2]), // Templated
			    .arbpc1_pcxdp_q0_hold_bufp1_pa(arbpc1_pcxdp_q0_hold_bufp1_pa[2]), // Templated
			    .arbpc1_pcxdp_qsel0_bufp1_pa_l(arbpc1_pcxdp_qsel0_bufp1_pa_l[2]), // Templated
			    .arbpc1_pcxdp_qsel1_bufp1_pa(arbpc1_pcxdp_qsel1_bufp1_pa[2]), // Templated
			    .arbpc1_pcxdp_shift_bufp1_px_l(arbpc1_pcxdp_shift_bufp1_px_l[2]), // Templated
			    .arbpc3_pcxdp_grant_bufp1_pa_l(arbpc3_pcxdp_grant_bufp1_pa_l[2]), // Templated
			    .arbpc3_pcxdp_q0_hold_bufp1_pa(arbpc3_pcxdp_q0_hold_bufp1_pa[2]), // Templated
			    .arbpc3_pcxdp_qsel0_bufp1_pa_l(arbpc3_pcxdp_qsel0_bufp1_pa_l[2]), // Templated
			    .arbpc3_pcxdp_qsel1_bufp1_pa(arbpc3_pcxdp_qsel1_bufp1_pa[2]), // Templated
			    .arbpc3_pcxdp_shift_bufp1_px_l(arbpc3_pcxdp_shift_bufp1_px_l[2]), // Templated
			    .arbpc4_pcxdp_grant_bufp1_pa_l(arbpc4_pcxdp_grant_bufp1_pa_l[2]), // Templated
			    .arbpc4_pcxdp_q0_hold_bufp1_pa(arbpc4_pcxdp_q0_hold_bufp1_pa[2]), // Templated
			    .arbpc4_pcxdp_qsel0_bufp1_pa_l(arbpc4_pcxdp_qsel0_bufp1_pa_l[2]), // Templated
			    .arbpc4_pcxdp_qsel1_bufp1_pa(arbpc4_pcxdp_qsel1_bufp1_pa[2]), // Templated
			    .arbpc4_pcxdp_shift_bufp1_px_l(arbpc4_pcxdp_shift_bufp1_px_l[2])); // Templated
   pcx_buf_p3 p3(/*AUTOINST*/
		 // Outputs
		 .scache3_pcx_stall_bufp3_pq(scache3_pcx_stall_bufp3_pq),
		 .spc7_pcx_req_bufp3_pq	(spc7_pcx_req_bufp3_pq[4:0]),
		 .spc7_pcx_atom_bufp3_pq(spc7_pcx_atom_bufp3_pq),
		 .spc6_pcx_req_bufp3_pq	(spc6_pcx_req_bufp3_pq[4:0]),
		 .spc6_pcx_atom_bufp3_pq(spc6_pcx_atom_bufp3_pq),
		 .spc5_pcx_req_bufp3_pq	(spc5_pcx_req_bufp3_pq[4:0]),
		 .spc5_pcx_atom_bufp3_pq(spc5_pcx_atom_bufp3_pq),
		 .pcx_spc5_grant_bufp3_pa_l(pcx_spc5_grant_bufp3_pa_l[4:0]),
		 .pcx_spc6_grant_bufp3_pa_l(pcx_spc6_grant_bufp3_pa_l[4:0]),
		 .pcx_spc7_grant_bufp3_pa_l(pcx_spc7_grant_bufp3_pa_l[4:0]),
		 .arbpc0_pcxdp_grant_bufp3_pa_l(arbpc0_pcxdp_grant_bufp3_pa_l[7:5]),
		 .arbpc0_pcxdp_q0_hold_bufp3_pa(arbpc0_pcxdp_q0_hold_bufp3_pa[7:5]),
		 .arbpc0_pcxdp_qsel0_bufp3_pa_l(arbpc0_pcxdp_qsel0_bufp3_pa_l[7:5]),
		 .arbpc0_pcxdp_qsel1_bufp3_pa(arbpc0_pcxdp_qsel1_bufp3_pa[7:5]),
		 .arbpc0_pcxdp_shift_bufp3_px_l(arbpc0_pcxdp_shift_bufp3_px_l[7:5]),
		 .arbpc1_pcxdp_grant_bufp3_pa_l(arbpc1_pcxdp_grant_bufp3_pa_l[7:5]),
		 .arbpc1_pcxdp_q0_hold_bufp3_pa(arbpc1_pcxdp_q0_hold_bufp3_pa[7:5]),
		 .arbpc1_pcxdp_qsel0_bufp3_pa_l(arbpc1_pcxdp_qsel0_bufp3_pa_l[7:5]),
		 .arbpc1_pcxdp_qsel1_bufp3_pa(arbpc1_pcxdp_qsel1_bufp3_pa[7:5]),
		 .arbpc1_pcxdp_shift_bufp3_px_l(arbpc1_pcxdp_shift_bufp3_px_l[7:5]),
		 .arbpc2_pcxdp_grant_bufp3_pa_l(arbpc2_pcxdp_grant_bufp3_pa_l[7:5]),
		 .arbpc2_pcxdp_q0_hold_bufp3_pa(arbpc2_pcxdp_q0_hold_bufp3_pa[7:5]),
		 .arbpc2_pcxdp_qsel0_bufp3_pa_l(arbpc2_pcxdp_qsel0_bufp3_pa_l[7:5]),
		 .arbpc2_pcxdp_qsel1_bufp3_pa(arbpc2_pcxdp_qsel1_bufp3_pa[7:5]),
		 .arbpc2_pcxdp_shift_bufp3_px_l(arbpc2_pcxdp_shift_bufp3_px_l[7:5]),
		 .arbpc3_pcxdp_grant_bufp3_pa_l(arbpc3_pcxdp_grant_bufp3_pa_l[7:5]),
		 .arbpc3_pcxdp_q0_hold_bufp3_pa(arbpc3_pcxdp_q0_hold_bufp3_pa[7:5]),
		 .arbpc3_pcxdp_qsel0_bufp3_pa_l(arbpc3_pcxdp_qsel0_bufp3_pa_l[7:5]),
		 .arbpc3_pcxdp_qsel1_bufp3_pa(arbpc3_pcxdp_qsel1_bufp3_pa[7:5]),
		 .arbpc3_pcxdp_shift_bufp3_px_l(arbpc3_pcxdp_shift_bufp3_px_l[7:5]),
		 .arbpc4_pcxdp_grant_bufp3_pa_l(arbpc4_pcxdp_grant_bufp3_pa_l[7:5]),
		 .arbpc4_pcxdp_q0_hold_bufp3_pa(arbpc4_pcxdp_q0_hold_bufp3_pa[7:5]),
		 .arbpc4_pcxdp_qsel0_bufp3_pa_l(arbpc4_pcxdp_qsel0_bufp3_pa_l[7:5]),
		 .arbpc4_pcxdp_qsel1_bufp3_pa(arbpc4_pcxdp_qsel1_bufp3_pa[7:5]),
		 .arbpc4_pcxdp_shift_bufp3_px_l(arbpc4_pcxdp_shift_bufp3_px_l[7:5]),
		 // Inputs
		 .scache3_pcx_stall_pq	(scache3_pcx_stall_pq),
		 .spc7_pcx_req_bufp4_pq	(spc7_pcx_req_bufp4_pq[4:0]),
		 .spc7_pcx_atom_bufp4_pq(spc7_pcx_atom_bufp4_pq),
		 .spc6_pcx_req_bufp4_pq	(spc6_pcx_req_bufp4_pq[4:0]),
		 .spc6_pcx_atom_bufp4_pq(spc6_pcx_atom_bufp4_pq),
		 .spc5_pcx_req_bufpt_pq_l(spc5_pcx_req_bufpt_pq_l[4:0]),
		 .spc5_pcx_atom_bufpt_pq_l(spc5_pcx_atom_bufpt_pq_l),
		 .pcx_spc5_grant_pa	(pcx_spc5_grant_pa[4:0]),
		 .pcx_spc6_grant_pa	(pcx_spc6_grant_pa[4:0]),
		 .pcx_spc7_grant_pa	(pcx_spc7_grant_pa[4:0]),
		 .arbpc0_pcxdp_grant_arbbf_pa(arbpc0_pcxdp_grant_arbbf_pa[7:5]),
		 .arbpc0_pcxdp_q0_hold_arbbf_pa_l(arbpc0_pcxdp_q0_hold_arbbf_pa_l[7:5]),
		 .arbpc0_pcxdp_qsel0_arbbf_pa(arbpc0_pcxdp_qsel0_arbbf_pa[7:5]),
		 .arbpc0_pcxdp_qsel1_arbbf_pa_l(arbpc0_pcxdp_qsel1_arbbf_pa_l[7:5]),
		 .arbpc0_pcxdp_shift_arbbf_px(arbpc0_pcxdp_shift_arbbf_px[7:5]),
		 .arbpc1_pcxdp_grant_arbbf_pa(arbpc1_pcxdp_grant_arbbf_pa[7:5]),
		 .arbpc1_pcxdp_q0_hold_arbbf_pa_l(arbpc1_pcxdp_q0_hold_arbbf_pa_l[7:5]),
		 .arbpc1_pcxdp_qsel0_arbbf_pa(arbpc1_pcxdp_qsel0_arbbf_pa[7:5]),
		 .arbpc1_pcxdp_qsel1_arbbf_pa_l(arbpc1_pcxdp_qsel1_arbbf_pa_l[7:5]),
		 .arbpc1_pcxdp_shift_arbbf_px(arbpc1_pcxdp_shift_arbbf_px[7:5]),
		 .arbpc2_pcxdp_grant_arbbf_pa(arbpc2_pcxdp_grant_arbbf_pa[7:5]),
		 .arbpc2_pcxdp_q0_hold_arbbf_pa_l(arbpc2_pcxdp_q0_hold_arbbf_pa_l[7:5]),
		 .arbpc2_pcxdp_qsel0_arbbf_pa(arbpc2_pcxdp_qsel0_arbbf_pa[7:5]),
		 .arbpc2_pcxdp_qsel1_arbbf_pa_l(arbpc2_pcxdp_qsel1_arbbf_pa_l[7:5]),
		 .arbpc2_pcxdp_shift_arbbf_px(arbpc2_pcxdp_shift_arbbf_px[7:5]),
		 .arbpc3_pcxdp_grant_arbbf_pa(arbpc3_pcxdp_grant_arbbf_pa[7:5]),
		 .arbpc3_pcxdp_q0_hold_arbbf_pa_l(arbpc3_pcxdp_q0_hold_arbbf_pa_l[7:5]),
		 .arbpc3_pcxdp_qsel0_arbbf_pa(arbpc3_pcxdp_qsel0_arbbf_pa[7:5]),
		 .arbpc3_pcxdp_qsel1_arbbf_pa_l(arbpc3_pcxdp_qsel1_arbbf_pa_l[7:5]),
		 .arbpc3_pcxdp_shift_arbbf_px(arbpc3_pcxdp_shift_arbbf_px[7:5]),
		 .arbpc4_pcxdp_grant_arbbf_pa(arbpc4_pcxdp_grant_arbbf_pa[7:5]),
		 .arbpc4_pcxdp_q0_hold_arbbf_pa_l(arbpc4_pcxdp_q0_hold_arbbf_pa_l[7:5]),
		 .arbpc4_pcxdp_qsel0_arbbf_pa(arbpc4_pcxdp_qsel0_arbbf_pa[7:5]),
		 .arbpc4_pcxdp_qsel1_arbbf_pa_l(arbpc4_pcxdp_qsel1_arbbf_pa_l[7:5]),
		 .arbpc4_pcxdp_shift_arbbf_px(arbpc4_pcxdp_shift_arbbf_px[7:5]));

/* pcx_buf_pdr AUTO_TEMPLATE(
		    // Outputs
		    .pcx_spc_grant_bufpdr_pa(pcx_spc@_grant_bufpdr_pa[4:0]),
		    // Inputs
		    .pcx_spc_grant_bufp3_pa_l(pcx_spc@_grant_bufp3_pa_l[4:0]));
*/

  pcx_buf_pdr pdr5(/*AUTOINST*/
		   // Outputs
		   .pcx_spc_grant_bufpdr_pa(pcx_spc5_grant_bufpdr_pa[4:0]), // Templated
		   // Inputs
		   .pcx_spc_grant_bufp3_pa_l(pcx_spc5_grant_bufp3_pa_l[4:0])); // Templated
  pcx_buf_pdr pdr6(/*AUTOINST*/
		   // Outputs
		   .pcx_spc_grant_bufpdr_pa(pcx_spc6_grant_bufpdr_pa[4:0]), // Templated
		   // Inputs
		   .pcx_spc_grant_bufp3_pa_l(pcx_spc6_grant_bufp3_pa_l[4:0])); // Templated
/* pcx_buf_pdr_even AUTO_TEMPLATE(
		    // Outputs
		    .arbpc0_pcxdp_grant_pa(arbpc0_pcxdp_grant_pa[@]),
		    .arbpc0_pcxdp_q0_hold_pa_l(arbpc0_pcxdp_q0_hold_pa_l[@]),
		    .arbpc0_pcxdp_qsel0_pa(arbpc0_pcxdp_qsel0_pa[@]),
		    .arbpc0_pcxdp_qsel1_pa_l(arbpc0_pcxdp_qsel1_pa_l[@]),
		    .arbpc0_pcxdp_shift_px(arbpc0_pcxdp_shift_px[@]),
		    .arbpc2_pcxdp_grant_pa(arbpc2_pcxdp_grant_pa[@]),
		    .arbpc2_pcxdp_q0_hold_pa_l(arbpc2_pcxdp_q0_hold_pa_l[@]),
		    .arbpc2_pcxdp_qsel0_pa(arbpc2_pcxdp_qsel0_pa[@]),
		    .arbpc2_pcxdp_qsel1_pa_l(arbpc2_pcxdp_qsel1_pa_l[@]),
		    .arbpc2_pcxdp_shift_px(arbpc2_pcxdp_shift_px[@]),
		    // Inputs
		    .arbpc0_pcxdp_grant_bufp3_pa_l(arbpc0_pcxdp_grant_bufp3_pa_l[@]),
		    .arbpc0_pcxdp_q0_hold_bufp3_pa(arbpc0_pcxdp_q0_hold_bufp3_pa[@]),
		    .arbpc0_pcxdp_qsel0_bufp3_pa_l(arbpc0_pcxdp_qsel0_bufp3_pa_l[@]),
		    .arbpc0_pcxdp_qsel1_bufp3_pa(arbpc0_pcxdp_qsel1_bufp3_pa[@]),
		    .arbpc0_pcxdp_shift_bufp3_px_l(arbpc0_pcxdp_shift_bufp3_px_l[@]),
		    .arbpc2_pcxdp_grant_bufp3_pa_l(arbpc2_pcxdp_grant_bufp3_pa_l[@]),
		    .arbpc2_pcxdp_q0_hold_bufp3_pa(arbpc2_pcxdp_q0_hold_bufp3_pa[@]),
		    .arbpc2_pcxdp_qsel0_bufp3_pa_l(arbpc2_pcxdp_qsel0_bufp3_pa_l[@]),
		    .arbpc2_pcxdp_qsel1_bufp3_pa(arbpc2_pcxdp_qsel1_bufp3_pa[@]),
		    .arbpc2_pcxdp_shift_bufp3_px_l(arbpc2_pcxdp_shift_bufp3_px_l[@]));
*/

  pcx_buf_pdr_even pdr5_even(/*AUTOINST*/
			     // Outputs
			     .arbpc0_pcxdp_grant_pa(arbpc0_pcxdp_grant_pa[5]), // Templated
			     .arbpc0_pcxdp_q0_hold_pa_l(arbpc0_pcxdp_q0_hold_pa_l[5]), // Templated
			     .arbpc0_pcxdp_qsel0_pa(arbpc0_pcxdp_qsel0_pa[5]), // Templated
			     .arbpc0_pcxdp_qsel1_pa_l(arbpc0_pcxdp_qsel1_pa_l[5]), // Templated
			     .arbpc0_pcxdp_shift_px(arbpc0_pcxdp_shift_px[5]), // Templated
			     .arbpc2_pcxdp_grant_pa(arbpc2_pcxdp_grant_pa[5]), // Templated
			     .arbpc2_pcxdp_q0_hold_pa_l(arbpc2_pcxdp_q0_hold_pa_l[5]), // Templated
			     .arbpc2_pcxdp_qsel0_pa(arbpc2_pcxdp_qsel0_pa[5]), // Templated
			     .arbpc2_pcxdp_qsel1_pa_l(arbpc2_pcxdp_qsel1_pa_l[5]), // Templated
			     .arbpc2_pcxdp_shift_px(arbpc2_pcxdp_shift_px[5]), // Templated
			     // Inputs
			     .arbpc0_pcxdp_grant_bufp3_pa_l(arbpc0_pcxdp_grant_bufp3_pa_l[5]), // Templated
			     .arbpc0_pcxdp_q0_hold_bufp3_pa(arbpc0_pcxdp_q0_hold_bufp3_pa[5]), // Templated
			     .arbpc0_pcxdp_qsel0_bufp3_pa_l(arbpc0_pcxdp_qsel0_bufp3_pa_l[5]), // Templated
			     .arbpc0_pcxdp_qsel1_bufp3_pa(arbpc0_pcxdp_qsel1_bufp3_pa[5]), // Templated
			     .arbpc0_pcxdp_shift_bufp3_px_l(arbpc0_pcxdp_shift_bufp3_px_l[5]), // Templated
			     .arbpc2_pcxdp_grant_bufp3_pa_l(arbpc2_pcxdp_grant_bufp3_pa_l[5]), // Templated
			     .arbpc2_pcxdp_q0_hold_bufp3_pa(arbpc2_pcxdp_q0_hold_bufp3_pa[5]), // Templated
			     .arbpc2_pcxdp_qsel0_bufp3_pa_l(arbpc2_pcxdp_qsel0_bufp3_pa_l[5]), // Templated
			     .arbpc2_pcxdp_qsel1_bufp3_pa(arbpc2_pcxdp_qsel1_bufp3_pa[5]), // Templated
			     .arbpc2_pcxdp_shift_bufp3_px_l(arbpc2_pcxdp_shift_bufp3_px_l[5])); // Templated
  pcx_buf_pdr_even pdr6_even(/*AUTOINST*/
			     // Outputs
			     .arbpc0_pcxdp_grant_pa(arbpc0_pcxdp_grant_pa[6]), // Templated
			     .arbpc0_pcxdp_q0_hold_pa_l(arbpc0_pcxdp_q0_hold_pa_l[6]), // Templated
			     .arbpc0_pcxdp_qsel0_pa(arbpc0_pcxdp_qsel0_pa[6]), // Templated
			     .arbpc0_pcxdp_qsel1_pa_l(arbpc0_pcxdp_qsel1_pa_l[6]), // Templated
			     .arbpc0_pcxdp_shift_px(arbpc0_pcxdp_shift_px[6]), // Templated
			     .arbpc2_pcxdp_grant_pa(arbpc2_pcxdp_grant_pa[6]), // Templated
			     .arbpc2_pcxdp_q0_hold_pa_l(arbpc2_pcxdp_q0_hold_pa_l[6]), // Templated
			     .arbpc2_pcxdp_qsel0_pa(arbpc2_pcxdp_qsel0_pa[6]), // Templated
			     .arbpc2_pcxdp_qsel1_pa_l(arbpc2_pcxdp_qsel1_pa_l[6]), // Templated
			     .arbpc2_pcxdp_shift_px(arbpc2_pcxdp_shift_px[6]), // Templated
			     // Inputs
			     .arbpc0_pcxdp_grant_bufp3_pa_l(arbpc0_pcxdp_grant_bufp3_pa_l[6]), // Templated
			     .arbpc0_pcxdp_q0_hold_bufp3_pa(arbpc0_pcxdp_q0_hold_bufp3_pa[6]), // Templated
			     .arbpc0_pcxdp_qsel0_bufp3_pa_l(arbpc0_pcxdp_qsel0_bufp3_pa_l[6]), // Templated
			     .arbpc0_pcxdp_qsel1_bufp3_pa(arbpc0_pcxdp_qsel1_bufp3_pa[6]), // Templated
			     .arbpc0_pcxdp_shift_bufp3_px_l(arbpc0_pcxdp_shift_bufp3_px_l[6]), // Templated
			     .arbpc2_pcxdp_grant_bufp3_pa_l(arbpc2_pcxdp_grant_bufp3_pa_l[6]), // Templated
			     .arbpc2_pcxdp_q0_hold_bufp3_pa(arbpc2_pcxdp_q0_hold_bufp3_pa[6]), // Templated
			     .arbpc2_pcxdp_qsel0_bufp3_pa_l(arbpc2_pcxdp_qsel0_bufp3_pa_l[6]), // Templated
			     .arbpc2_pcxdp_qsel1_bufp3_pa(arbpc2_pcxdp_qsel1_bufp3_pa[6]), // Templated
			     .arbpc2_pcxdp_shift_bufp3_px_l(arbpc2_pcxdp_shift_bufp3_px_l[6])); // Templated
/* pcx_buf_pdr_odd AUTO_TEMPLATE(
		    // Outputs
		    .arbpc1_pcxdp_grant_pa(arbpc1_pcxdp_grant_pa[@]),
		    .arbpc1_pcxdp_q0_hold_pa_l(arbpc1_pcxdp_q0_hold_pa_l[@]),
		    .arbpc1_pcxdp_qsel0_pa(arbpc1_pcxdp_qsel0_pa[@]),
		    .arbpc1_pcxdp_qsel1_pa_l(arbpc1_pcxdp_qsel1_pa_l[@]),
		    .arbpc1_pcxdp_shift_px(arbpc1_pcxdp_shift_px[@]),
		    .arbpc3_pcxdp_grant_pa(arbpc3_pcxdp_grant_pa[@]),
		    .arbpc3_pcxdp_q0_hold_pa_l(arbpc3_pcxdp_q0_hold_pa_l[@]),
		    .arbpc3_pcxdp_qsel0_pa(arbpc3_pcxdp_qsel0_pa[@]),
		    .arbpc3_pcxdp_qsel1_pa_l(arbpc3_pcxdp_qsel1_pa_l[@]),
		    .arbpc3_pcxdp_shift_px(arbpc3_pcxdp_shift_px[@]),
		    .arbpc4_pcxdp_grant_pa(arbpc4_pcxdp_grant_pa[@]),
		    .arbpc4_pcxdp_q0_hold_pa_l(arbpc4_pcxdp_q0_hold_pa_l[@]),
		    .arbpc4_pcxdp_qsel0_pa(arbpc4_pcxdp_qsel0_pa[@]),
		    .arbpc4_pcxdp_qsel1_pa_l(arbpc4_pcxdp_qsel1_pa_l[@]),
		    .arbpc4_pcxdp_shift_px(arbpc4_pcxdp_shift_px[@]),
		    // Inputs
		    .arbpc1_pcxdp_grant_bufp3_pa_l(arbpc1_pcxdp_grant_bufp3_pa_l[@]),
		    .arbpc1_pcxdp_q0_hold_bufp3_pa(arbpc1_pcxdp_q0_hold_bufp3_pa[@]),
		    .arbpc1_pcxdp_qsel0_bufp3_pa_l(arbpc1_pcxdp_qsel0_bufp3_pa_l[@]),
		    .arbpc1_pcxdp_qsel1_bufp3_pa(arbpc1_pcxdp_qsel1_bufp3_pa[@]),
		    .arbpc1_pcxdp_shift_bufp3_px_l(arbpc1_pcxdp_shift_bufp3_px_l[@]),
		    .arbpc3_pcxdp_grant_bufp3_pa_l(arbpc3_pcxdp_grant_bufp3_pa_l[@]),
		    .arbpc3_pcxdp_q0_hold_bufp3_pa(arbpc3_pcxdp_q0_hold_bufp3_pa[@]),
		    .arbpc3_pcxdp_qsel0_bufp3_pa_l(arbpc3_pcxdp_qsel0_bufp3_pa_l[@]),
		    .arbpc3_pcxdp_qsel1_bufp3_pa(arbpc3_pcxdp_qsel1_bufp3_pa[@]),
		    .arbpc3_pcxdp_shift_bufp3_px_l(arbpc3_pcxdp_shift_bufp3_px_l[@]),
		    .arbpc4_pcxdp_grant_bufp3_pa_l(arbpc4_pcxdp_grant_bufp3_pa_l[@]),
		    .arbpc4_pcxdp_q0_hold_bufp3_pa(arbpc4_pcxdp_q0_hold_bufp3_pa[@]),
		    .arbpc4_pcxdp_qsel0_bufp3_pa_l(arbpc4_pcxdp_qsel0_bufp3_pa_l[@]),
		    .arbpc4_pcxdp_qsel1_bufp3_pa(arbpc4_pcxdp_qsel1_bufp3_pa[@]),
		    .arbpc4_pcxdp_shift_bufp3_px_l(arbpc4_pcxdp_shift_bufp3_px_l[@]));
*/   

   pcx_buf_pdr_odd pdr5_odd(/*AUTOINST*/
			    // Outputs
			    .arbpc1_pcxdp_grant_pa(arbpc1_pcxdp_grant_pa[5]), // Templated
			    .arbpc1_pcxdp_q0_hold_pa_l(arbpc1_pcxdp_q0_hold_pa_l[5]), // Templated
			    .arbpc1_pcxdp_qsel0_pa(arbpc1_pcxdp_qsel0_pa[5]), // Templated
			    .arbpc1_pcxdp_qsel1_pa_l(arbpc1_pcxdp_qsel1_pa_l[5]), // Templated
			    .arbpc1_pcxdp_shift_px(arbpc1_pcxdp_shift_px[5]), // Templated
			    .arbpc3_pcxdp_grant_pa(arbpc3_pcxdp_grant_pa[5]), // Templated
			    .arbpc3_pcxdp_q0_hold_pa_l(arbpc3_pcxdp_q0_hold_pa_l[5]), // Templated
			    .arbpc3_pcxdp_qsel0_pa(arbpc3_pcxdp_qsel0_pa[5]), // Templated
			    .arbpc3_pcxdp_qsel1_pa_l(arbpc3_pcxdp_qsel1_pa_l[5]), // Templated
			    .arbpc3_pcxdp_shift_px(arbpc3_pcxdp_shift_px[5]), // Templated
			    .arbpc4_pcxdp_grant_pa(arbpc4_pcxdp_grant_pa[5]), // Templated
			    .arbpc4_pcxdp_q0_hold_pa_l(arbpc4_pcxdp_q0_hold_pa_l[5]), // Templated
			    .arbpc4_pcxdp_qsel0_pa(arbpc4_pcxdp_qsel0_pa[5]), // Templated
			    .arbpc4_pcxdp_qsel1_pa_l(arbpc4_pcxdp_qsel1_pa_l[5]), // Templated
			    .arbpc4_pcxdp_shift_px(arbpc4_pcxdp_shift_px[5]), // Templated
			    // Inputs
			    .arbpc1_pcxdp_grant_bufp3_pa_l(arbpc1_pcxdp_grant_bufp3_pa_l[5]), // Templated
			    .arbpc1_pcxdp_q0_hold_bufp3_pa(arbpc1_pcxdp_q0_hold_bufp3_pa[5]), // Templated
			    .arbpc1_pcxdp_qsel0_bufp3_pa_l(arbpc1_pcxdp_qsel0_bufp3_pa_l[5]), // Templated
			    .arbpc1_pcxdp_qsel1_bufp3_pa(arbpc1_pcxdp_qsel1_bufp3_pa[5]), // Templated
			    .arbpc1_pcxdp_shift_bufp3_px_l(arbpc1_pcxdp_shift_bufp3_px_l[5]), // Templated
			    .arbpc3_pcxdp_grant_bufp3_pa_l(arbpc3_pcxdp_grant_bufp3_pa_l[5]), // Templated
			    .arbpc3_pcxdp_q0_hold_bufp3_pa(arbpc3_pcxdp_q0_hold_bufp3_pa[5]), // Templated
			    .arbpc3_pcxdp_qsel0_bufp3_pa_l(arbpc3_pcxdp_qsel0_bufp3_pa_l[5]), // Templated
			    .arbpc3_pcxdp_qsel1_bufp3_pa(arbpc3_pcxdp_qsel1_bufp3_pa[5]), // Templated
			    .arbpc3_pcxdp_shift_bufp3_px_l(arbpc3_pcxdp_shift_bufp3_px_l[5]), // Templated
			    .arbpc4_pcxdp_grant_bufp3_pa_l(arbpc4_pcxdp_grant_bufp3_pa_l[5]), // Templated
			    .arbpc4_pcxdp_q0_hold_bufp3_pa(arbpc4_pcxdp_q0_hold_bufp3_pa[5]), // Templated
			    .arbpc4_pcxdp_qsel0_bufp3_pa_l(arbpc4_pcxdp_qsel0_bufp3_pa_l[5]), // Templated
			    .arbpc4_pcxdp_qsel1_bufp3_pa(arbpc4_pcxdp_qsel1_bufp3_pa[5]), // Templated
			    .arbpc4_pcxdp_shift_bufp3_px_l(arbpc4_pcxdp_shift_bufp3_px_l[5])); // Templated
   pcx_buf_pdr_odd pdr6_odd(/*AUTOINST*/
			    // Outputs
			    .arbpc1_pcxdp_grant_pa(arbpc1_pcxdp_grant_pa[6]), // Templated
			    .arbpc1_pcxdp_q0_hold_pa_l(arbpc1_pcxdp_q0_hold_pa_l[6]), // Templated
			    .arbpc1_pcxdp_qsel0_pa(arbpc1_pcxdp_qsel0_pa[6]), // Templated
			    .arbpc1_pcxdp_qsel1_pa_l(arbpc1_pcxdp_qsel1_pa_l[6]), // Templated
			    .arbpc1_pcxdp_shift_px(arbpc1_pcxdp_shift_px[6]), // Templated
			    .arbpc3_pcxdp_grant_pa(arbpc3_pcxdp_grant_pa[6]), // Templated
			    .arbpc3_pcxdp_q0_hold_pa_l(arbpc3_pcxdp_q0_hold_pa_l[6]), // Templated
			    .arbpc3_pcxdp_qsel0_pa(arbpc3_pcxdp_qsel0_pa[6]), // Templated
			    .arbpc3_pcxdp_qsel1_pa_l(arbpc3_pcxdp_qsel1_pa_l[6]), // Templated
			    .arbpc3_pcxdp_shift_px(arbpc3_pcxdp_shift_px[6]), // Templated
			    .arbpc4_pcxdp_grant_pa(arbpc4_pcxdp_grant_pa[6]), // Templated
			    .arbpc4_pcxdp_q0_hold_pa_l(arbpc4_pcxdp_q0_hold_pa_l[6]), // Templated
			    .arbpc4_pcxdp_qsel0_pa(arbpc4_pcxdp_qsel0_pa[6]), // Templated
			    .arbpc4_pcxdp_qsel1_pa_l(arbpc4_pcxdp_qsel1_pa_l[6]), // Templated
			    .arbpc4_pcxdp_shift_px(arbpc4_pcxdp_shift_px[6]), // Templated
			    // Inputs
			    .arbpc1_pcxdp_grant_bufp3_pa_l(arbpc1_pcxdp_grant_bufp3_pa_l[6]), // Templated
			    .arbpc1_pcxdp_q0_hold_bufp3_pa(arbpc1_pcxdp_q0_hold_bufp3_pa[6]), // Templated
			    .arbpc1_pcxdp_qsel0_bufp3_pa_l(arbpc1_pcxdp_qsel0_bufp3_pa_l[6]), // Templated
			    .arbpc1_pcxdp_qsel1_bufp3_pa(arbpc1_pcxdp_qsel1_bufp3_pa[6]), // Templated
			    .arbpc1_pcxdp_shift_bufp3_px_l(arbpc1_pcxdp_shift_bufp3_px_l[6]), // Templated
			    .arbpc3_pcxdp_grant_bufp3_pa_l(arbpc3_pcxdp_grant_bufp3_pa_l[6]), // Templated
			    .arbpc3_pcxdp_q0_hold_bufp3_pa(arbpc3_pcxdp_q0_hold_bufp3_pa[6]), // Templated
			    .arbpc3_pcxdp_qsel0_bufp3_pa_l(arbpc3_pcxdp_qsel0_bufp3_pa_l[6]), // Templated
			    .arbpc3_pcxdp_qsel1_bufp3_pa(arbpc3_pcxdp_qsel1_bufp3_pa[6]), // Templated
			    .arbpc3_pcxdp_shift_bufp3_px_l(arbpc3_pcxdp_shift_bufp3_px_l[6]), // Templated
			    .arbpc4_pcxdp_grant_bufp3_pa_l(arbpc4_pcxdp_grant_bufp3_pa_l[6]), // Templated
			    .arbpc4_pcxdp_q0_hold_bufp3_pa(arbpc4_pcxdp_q0_hold_bufp3_pa[6]), // Templated
			    .arbpc4_pcxdp_qsel0_bufp3_pa_l(arbpc4_pcxdp_qsel0_bufp3_pa_l[6]), // Templated
			    .arbpc4_pcxdp_qsel1_bufp3_pa(arbpc4_pcxdp_qsel1_bufp3_pa[6]), // Templated
			    .arbpc4_pcxdp_shift_bufp3_px_l(arbpc4_pcxdp_shift_bufp3_px_l[6])); // Templated
   pcx_buf_p4 p4(/*AUTOINST*/
		 // Outputs
		 .pcx_spc7_grant_bufp4_pa(pcx_spc7_grant_bufp4_pa[4:0]),
		 .spc6_pcx_req_bufp4_pq	(spc6_pcx_req_bufp4_pq[4:0]),
		 .spc6_pcx_atom_bufp4_pq(spc6_pcx_atom_bufp4_pq),
		 .spc7_pcx_req_bufp4_pq	(spc7_pcx_req_bufp4_pq[4:0]),
		 .spc7_pcx_atom_bufp4_pq(spc7_pcx_atom_bufp4_pq),
		 // Inputs
		 .spc6_pcx_req_bufpt_pq_l(spc6_pcx_req_bufpt_pq_l[4:0]),
		 .spc6_pcx_atom_bufpt_pq_l(spc6_pcx_atom_bufpt_pq_l),
		 .spc7_pcx_req_bufpt_pq_l(spc7_pcx_req_bufpt_pq_l[4:0]),
		 .spc7_pcx_atom_bufpt_pq_l(spc7_pcx_atom_bufpt_pq_l),
		 .pcx_spc7_grant_bufp3_pa_l(pcx_spc7_grant_bufp3_pa_l[4:0]));


   /* pcx_buf_p4_even AUTO_TEMPLATE(
		 // Outputs
		 .arbpc0_pcxdp_grant_pa	(arbpc0_pcxdp_grant_pa[7]),
		 .arbpc0_pcxdp_q0_hold_pa_l(arbpc0_pcxdp_q0_hold_pa_l[7]),
		 .arbpc0_pcxdp_qsel0_pa	(arbpc0_pcxdp_qsel0_pa[7]),
		 .arbpc0_pcxdp_qsel1_pa_l(arbpc0_pcxdp_qsel1_pa_l[7]),
		 .arbpc0_pcxdp_shift_px	(arbpc0_pcxdp_shift_px[7]),
		 .arbpc2_pcxdp_grant_pa	(arbpc2_pcxdp_grant_pa[7]),
		 .arbpc2_pcxdp_q0_hold_pa_l(arbpc2_pcxdp_q0_hold_pa_l[7]),
		 .arbpc2_pcxdp_qsel0_pa	(arbpc2_pcxdp_qsel0_pa[7]),
		 .arbpc2_pcxdp_qsel1_pa_l(arbpc2_pcxdp_qsel1_pa_l[7]),
		 .arbpc2_pcxdp_shift_px	(arbpc2_pcxdp_shift_px[7]),
		 // Inputs
    		 .arbpc0_pcxdp_grant_bufp3_pa_l(arbpc0_pcxdp_grant_bufp3_pa_l[7]),
		 .arbpc0_pcxdp_q0_hold_bufp3_pa(arbpc0_pcxdp_q0_hold_bufp3_pa[7]),
		 .arbpc0_pcxdp_qsel0_bufp3_pa_l(arbpc0_pcxdp_qsel0_bufp3_pa_l[7]),
		 .arbpc0_pcxdp_qsel1_bufp3_pa(arbpc0_pcxdp_qsel1_bufp3_pa[7]),
		 .arbpc0_pcxdp_shift_bufp3_px_l(arbpc0_pcxdp_shift_bufp3_px_l[7]),
		 .arbpc2_pcxdp_grant_bufp3_pa_l(arbpc2_pcxdp_grant_bufp3_pa_l[7]),
		 .arbpc2_pcxdp_q0_hold_bufp3_pa(arbpc2_pcxdp_q0_hold_bufp3_pa[7]),
		 .arbpc2_pcxdp_qsel0_bufp3_pa_l(arbpc2_pcxdp_qsel0_bufp3_pa_l[7]),
		 .arbpc2_pcxdp_qsel1_bufp3_pa(arbpc2_pcxdp_qsel1_bufp3_pa[7]),
		 .arbpc2_pcxdp_shift_bufp3_px_l(arbpc2_pcxdp_shift_bufp3_px_l[7]));
   */

  pcx_buf_p4_even p4_even(/*AUTOINST*/
			  // Outputs
			  .arbpc0_pcxdp_grant_pa(arbpc0_pcxdp_grant_pa[7]), // Templated
			  .arbpc0_pcxdp_q0_hold_pa_l(arbpc0_pcxdp_q0_hold_pa_l[7]), // Templated
			  .arbpc0_pcxdp_qsel0_pa(arbpc0_pcxdp_qsel0_pa[7]), // Templated
			  .arbpc0_pcxdp_qsel1_pa_l(arbpc0_pcxdp_qsel1_pa_l[7]), // Templated
			  .arbpc0_pcxdp_shift_px(arbpc0_pcxdp_shift_px[7]), // Templated
			  .arbpc2_pcxdp_grant_pa(arbpc2_pcxdp_grant_pa[7]), // Templated
			  .arbpc2_pcxdp_q0_hold_pa_l(arbpc2_pcxdp_q0_hold_pa_l[7]), // Templated
			  .arbpc2_pcxdp_qsel0_pa(arbpc2_pcxdp_qsel0_pa[7]), // Templated
			  .arbpc2_pcxdp_qsel1_pa_l(arbpc2_pcxdp_qsel1_pa_l[7]), // Templated
			  .arbpc2_pcxdp_shift_px(arbpc2_pcxdp_shift_px[7]), // Templated
			  // Inputs
			  .arbpc0_pcxdp_grant_bufp3_pa_l(arbpc0_pcxdp_grant_bufp3_pa_l[7]), // Templated
			  .arbpc0_pcxdp_q0_hold_bufp3_pa(arbpc0_pcxdp_q0_hold_bufp3_pa[7]), // Templated
			  .arbpc0_pcxdp_qsel0_bufp3_pa_l(arbpc0_pcxdp_qsel0_bufp3_pa_l[7]), // Templated
			  .arbpc0_pcxdp_qsel1_bufp3_pa(arbpc0_pcxdp_qsel1_bufp3_pa[7]), // Templated
			  .arbpc0_pcxdp_shift_bufp3_px_l(arbpc0_pcxdp_shift_bufp3_px_l[7]), // Templated
			  .arbpc2_pcxdp_grant_bufp3_pa_l(arbpc2_pcxdp_grant_bufp3_pa_l[7]), // Templated
			  .arbpc2_pcxdp_q0_hold_bufp3_pa(arbpc2_pcxdp_q0_hold_bufp3_pa[7]), // Templated
			  .arbpc2_pcxdp_qsel0_bufp3_pa_l(arbpc2_pcxdp_qsel0_bufp3_pa_l[7]), // Templated
			  .arbpc2_pcxdp_qsel1_bufp3_pa(arbpc2_pcxdp_qsel1_bufp3_pa[7]), // Templated
			  .arbpc2_pcxdp_shift_bufp3_px_l(arbpc2_pcxdp_shift_bufp3_px_l[7])); // Templated
   /* pcx_buf_p4_odd AUTO_TEMPLATE(
		 // Outputs
		 .arbpc1_pcxdp_grant_pa	(arbpc1_pcxdp_grant_pa[7]),
		 .arbpc1_pcxdp_q0_hold_pa_l(arbpc1_pcxdp_q0_hold_pa_l[7]),
		 .arbpc1_pcxdp_qsel0_pa	(arbpc1_pcxdp_qsel0_pa[7]),
		 .arbpc1_pcxdp_qsel1_pa_l(arbpc1_pcxdp_qsel1_pa_l[7]),
		 .arbpc1_pcxdp_shift_px	(arbpc1_pcxdp_shift_px[7]),
		 .arbpc3_pcxdp_grant_pa	(arbpc3_pcxdp_grant_pa[7]),
		 .arbpc3_pcxdp_q0_hold_pa_l(arbpc3_pcxdp_q0_hold_pa_l[7]),
		 .arbpc3_pcxdp_qsel0_pa	(arbpc3_pcxdp_qsel0_pa[7]),
		 .arbpc3_pcxdp_qsel1_pa_l(arbpc3_pcxdp_qsel1_pa_l[7]),
		 .arbpc3_pcxdp_shift_px	(arbpc3_pcxdp_shift_px[7]),
		 .arbpc4_pcxdp_grant_pa	(arbpc4_pcxdp_grant_pa[7]),
		 .arbpc4_pcxdp_q0_hold_pa_l(arbpc4_pcxdp_q0_hold_pa_l[7]),
		 .arbpc4_pcxdp_qsel0_pa	(arbpc4_pcxdp_qsel0_pa[7]),
		 .arbpc4_pcxdp_qsel1_pa_l(arbpc4_pcxdp_qsel1_pa_l[7]),
		 .arbpc4_pcxdp_shift_px	(arbpc4_pcxdp_shift_px[7]),
		 // Inputs
		 .arbpc1_pcxdp_grant_bufp3_pa_l(arbpc1_pcxdp_grant_bufp3_pa_l[7]),
		 .arbpc1_pcxdp_q0_hold_bufp3_pa(arbpc1_pcxdp_q0_hold_bufp3_pa[7]),
		 .arbpc1_pcxdp_qsel0_bufp3_pa_l(arbpc1_pcxdp_qsel0_bufp3_pa_l[7]),
		 .arbpc1_pcxdp_qsel1_bufp3_pa(arbpc1_pcxdp_qsel1_bufp3_pa[7]),
		 .arbpc1_pcxdp_shift_bufp3_px_l(arbpc1_pcxdp_shift_bufp3_px_l[7]),
		 .arbpc3_pcxdp_grant_bufp3_pa_l(arbpc3_pcxdp_grant_bufp3_pa_l[7]),
		 .arbpc3_pcxdp_q0_hold_bufp3_pa(arbpc3_pcxdp_q0_hold_bufp3_pa[7]),
		 .arbpc3_pcxdp_qsel0_bufp3_pa_l(arbpc3_pcxdp_qsel0_bufp3_pa_l[7]),
		 .arbpc3_pcxdp_qsel1_bufp3_pa(arbpc3_pcxdp_qsel1_bufp3_pa[7]),
		 .arbpc3_pcxdp_shift_bufp3_px_l(arbpc3_pcxdp_shift_bufp3_px_l[7]),
		 .arbpc4_pcxdp_grant_bufp3_pa_l(arbpc4_pcxdp_grant_bufp3_pa_l[7]),
		 .arbpc4_pcxdp_q0_hold_bufp3_pa(arbpc4_pcxdp_q0_hold_bufp3_pa[7]),
		 .arbpc4_pcxdp_qsel0_bufp3_pa_l(arbpc4_pcxdp_qsel0_bufp3_pa_l[7]),
		 .arbpc4_pcxdp_qsel1_bufp3_pa(arbpc4_pcxdp_qsel1_bufp3_pa[7]),
		 .arbpc4_pcxdp_shift_bufp3_px_l(arbpc4_pcxdp_shift_bufp3_px_l[7]));
*/

   pcx_buf_p4_odd p4_odd(/*AUTOINST*/
			 // Outputs
			 .arbpc1_pcxdp_grant_pa(arbpc1_pcxdp_grant_pa[7]), // Templated
			 .arbpc1_pcxdp_q0_hold_pa_l(arbpc1_pcxdp_q0_hold_pa_l[7]), // Templated
			 .arbpc1_pcxdp_qsel0_pa(arbpc1_pcxdp_qsel0_pa[7]), // Templated
			 .arbpc1_pcxdp_qsel1_pa_l(arbpc1_pcxdp_qsel1_pa_l[7]), // Templated
			 .arbpc1_pcxdp_shift_px(arbpc1_pcxdp_shift_px[7]), // Templated
			 .arbpc3_pcxdp_grant_pa(arbpc3_pcxdp_grant_pa[7]), // Templated
			 .arbpc3_pcxdp_q0_hold_pa_l(arbpc3_pcxdp_q0_hold_pa_l[7]), // Templated
			 .arbpc3_pcxdp_qsel0_pa(arbpc3_pcxdp_qsel0_pa[7]), // Templated
			 .arbpc3_pcxdp_qsel1_pa_l(arbpc3_pcxdp_qsel1_pa_l[7]), // Templated
			 .arbpc3_pcxdp_shift_px(arbpc3_pcxdp_shift_px[7]), // Templated
			 .arbpc4_pcxdp_grant_pa(arbpc4_pcxdp_grant_pa[7]), // Templated
			 .arbpc4_pcxdp_q0_hold_pa_l(arbpc4_pcxdp_q0_hold_pa_l[7]), // Templated
			 .arbpc4_pcxdp_qsel0_pa(arbpc4_pcxdp_qsel0_pa[7]), // Templated
			 .arbpc4_pcxdp_qsel1_pa_l(arbpc4_pcxdp_qsel1_pa_l[7]), // Templated
			 .arbpc4_pcxdp_shift_px(arbpc4_pcxdp_shift_px[7]), // Templated
			 // Inputs
			 .arbpc1_pcxdp_grant_bufp3_pa_l(arbpc1_pcxdp_grant_bufp3_pa_l[7]), // Templated
			 .arbpc1_pcxdp_q0_hold_bufp3_pa(arbpc1_pcxdp_q0_hold_bufp3_pa[7]), // Templated
			 .arbpc1_pcxdp_qsel0_bufp3_pa_l(arbpc1_pcxdp_qsel0_bufp3_pa_l[7]), // Templated
			 .arbpc1_pcxdp_qsel1_bufp3_pa(arbpc1_pcxdp_qsel1_bufp3_pa[7]), // Templated
			 .arbpc1_pcxdp_shift_bufp3_px_l(arbpc1_pcxdp_shift_bufp3_px_l[7]), // Templated
			 .arbpc3_pcxdp_grant_bufp3_pa_l(arbpc3_pcxdp_grant_bufp3_pa_l[7]), // Templated
			 .arbpc3_pcxdp_q0_hold_bufp3_pa(arbpc3_pcxdp_q0_hold_bufp3_pa[7]), // Templated
			 .arbpc3_pcxdp_qsel0_bufp3_pa_l(arbpc3_pcxdp_qsel0_bufp3_pa_l[7]), // Templated
			 .arbpc3_pcxdp_qsel1_bufp3_pa(arbpc3_pcxdp_qsel1_bufp3_pa[7]), // Templated
			 .arbpc3_pcxdp_shift_bufp3_px_l(arbpc3_pcxdp_shift_bufp3_px_l[7]), // Templated
			 .arbpc4_pcxdp_grant_bufp3_pa_l(arbpc4_pcxdp_grant_bufp3_pa_l[7]), // Templated
			 .arbpc4_pcxdp_q0_hold_bufp3_pa(arbpc4_pcxdp_q0_hold_bufp3_pa[7]), // Templated
			 .arbpc4_pcxdp_qsel0_bufp3_pa_l(arbpc4_pcxdp_qsel0_bufp3_pa_l[7]), // Templated
			 .arbpc4_pcxdp_qsel1_bufp3_pa(arbpc4_pcxdp_qsel1_bufp3_pa[7]), // Templated
			 .arbpc4_pcxdp_shift_bufp3_px_l(arbpc4_pcxdp_shift_bufp3_px_l[7])); // Templated
// change from: pcx_data -> (macc+inv) + (inv+inv) + (ff+inv) + (inv+inv) -> scache
// to: pcx_data -> (macc+inv) + (inv+inv) + (inv+inv) + (ff+inv) -> scache
   
   /*
   pcx_buf_scache  AUTO_TEMPLATE(
				  // Outputs
				  .pcx_scache_data_px(pcx_scache@_data_px_buf1[`PCX_WIDTH-1:0]),
				  .pcx_scache_data_rdy_px(pcx_scache@_data_rdy_buf1_px),
		  // Inputs
                		  .pcx_scache_data_rdy_arb_px(pcx_scache@_data_rdy_arb_px), 
				  .pcx_scache_data_px_l(pcx_scache@_data_px_l[`PCX_WIDTH-1:0]));
    */
   pcx_buf_scache buf0_1(/*AUTOINST*/
			 // Outputs
			 .pcx_scache_data_px(pcx_scache0_data_px_buf1[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_px(pcx_scache0_data_rdy_buf1_px), // Templated
			 // Inputs
			 .pcx_scache_data_px_l(pcx_scache0_data_px_l[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_arb_px(pcx_scache0_data_rdy_arb_px)); // Templated
   pcx_buf_scache buf1_1(/*AUTOINST*/
			 // Outputs
			 .pcx_scache_data_px(pcx_scache1_data_px_buf1[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_px(pcx_scache1_data_rdy_buf1_px), // Templated
			 // Inputs
			 .pcx_scache_data_px_l(pcx_scache1_data_px_l[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_arb_px(pcx_scache1_data_rdy_arb_px)); // Templated
   pcx_buf_scache buf2_1(/*AUTOINST*/
			 // Outputs
			 .pcx_scache_data_px(pcx_scache2_data_px_buf1[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_px(pcx_scache2_data_rdy_buf1_px), // Templated
			 // Inputs
			 .pcx_scache_data_px_l(pcx_scache2_data_px_l[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_arb_px(pcx_scache2_data_rdy_arb_px)); // Templated
   pcx_buf_scache buf3_1(/*AUTOINST*/
			 // Outputs
			 .pcx_scache_data_px(pcx_scache3_data_px_buf1[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_px(pcx_scache3_data_rdy_buf1_px), // Templated
			 // Inputs
			 .pcx_scache_data_px_l(pcx_scache3_data_px_l[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_arb_px(pcx_scache3_data_rdy_arb_px)); // Templated
   /*
   pcx_buf_scache  AUTO_TEMPLATE(
				  // Outputs
				  .pcx_scache_data_px(pcx_scache@_data_buf2_l[`PCX_WIDTH-1:0]),
				  .pcx_scache_data_rdy_px(pcx_scache0_atom_buf0_2_px1),
		  // Inputs
                		  .pcx_scache_data_rdy_arb_px(pcx_scache0_atom_px), 
				  .pcx_scache_data_px_l(pcx_scache@_data_px_buf1[`PCX_WIDTH-1:0]));
    */
   pcx_buf_scache buf0_2(/*AUTOINST*/
			 // Outputs
			 .pcx_scache_data_px(pcx_scache0_data_buf2_l[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_px(pcx_scache0_atom_buf0_2_px1), // Templated
			 // Inputs
			 .pcx_scache_data_px_l(pcx_scache0_data_px_buf1[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_arb_px(pcx_scache0_atom_px)); // Templated
   /*
   pcx_buf_scache  AUTO_TEMPLATE(
				  // Outputs
				  .pcx_scache_data_px(pcx_scache@_data_buf2_l[`PCX_WIDTH-1:0]),
				  .pcx_scache_data_rdy_px(pcx_scache1_atom_buf1_2_px1),
		  // Inputs
                		  .pcx_scache_data_rdy_arb_px(pcx_scache1_atom_px), 
				  .pcx_scache_data_px_l(pcx_scache@_data_px_buf1[`PCX_WIDTH-1:0]));
   */
   pcx_buf_scache buf1_2(/*AUTOINST*/
			 // Outputs
			 .pcx_scache_data_px(pcx_scache1_data_buf2_l[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_px(pcx_scache1_atom_buf1_2_px1), // Templated
			 // Inputs
			 .pcx_scache_data_px_l(pcx_scache1_data_px_buf1[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_arb_px(pcx_scache1_atom_px)); // Templated
   /*
   pcx_buf_scache  AUTO_TEMPLATE(
				  // Outputs
				  .pcx_scache_data_px(pcx_scache@_data_buf2_l[`PCX_WIDTH-1:0]),
				  .pcx_scache_data_rdy_px(),
		  // Inputs
                		  .pcx_scache_data_rdy_arb_px(1'b0), 
				  .pcx_scache_data_px_l(pcx_scache@_data_px_buf1[`PCX_WIDTH-1:0]));
    */
   pcx_buf_scache buf2_2(/*AUTOINST*/
			 // Outputs
			 .pcx_scache_data_px(pcx_scache2_data_buf2_l[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_px(),		 // Templated
			 // Inputs
			 .pcx_scache_data_px_l(pcx_scache2_data_px_buf1[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_arb_px(1'b0));	 // Templated
   pcx_buf_scache buf3_2(/*AUTOINST*/
			 // Outputs
			 .pcx_scache_data_px(pcx_scache3_data_buf2_l[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_px(),		 // Templated
			 // Inputs
			 .pcx_scache_data_px_l(pcx_scache3_data_px_buf1[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_arb_px(1'b0));	 // Templated
   /*
   pcx_buf_scache  AUTO_TEMPLATE(
                                  // Outputs
                                  .pcx_scache_data_px(pcx_scache@_data_px_buf3[`PCX_WIDTH-1:0]),
                                  .pcx_scache_data_rdy_px(pcx_scache@_data_rdy_px),
                  // Inputs
                                  .pcx_scache_data_rdy_arb_px(pcx_scache@_data_rdy_buf1_px),
                                  .pcx_scache_data_px_l(pcx_scache@_data_buf2_l[`PCX_WIDTH-1:0]));
    */

   pcx_buf_scache buf0_3(/*AUTOINST*/
			 // Outputs
			 .pcx_scache_data_px(pcx_scache0_data_px_buf3[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_px(pcx_scache0_data_rdy_px), // Templated
			 // Inputs
			 .pcx_scache_data_px_l(pcx_scache0_data_buf2_l[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_arb_px(pcx_scache0_data_rdy_buf1_px)); // Templated
   pcx_buf_scache buf1_3(/*AUTOINST*/
			 // Outputs
			 .pcx_scache_data_px(pcx_scache1_data_px_buf3[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_px(pcx_scache1_data_rdy_px), // Templated
			 // Inputs
			 .pcx_scache_data_px_l(pcx_scache1_data_buf2_l[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_arb_px(pcx_scache1_data_rdy_buf1_px)); // Templated
   pcx_buf_scache buf2_3(/*AUTOINST*/
			 // Outputs
			 .pcx_scache_data_px(pcx_scache2_data_px_buf3[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_px(pcx_scache2_data_rdy_px), // Templated
			 // Inputs
			 .pcx_scache_data_px_l(pcx_scache2_data_buf2_l[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_arb_px(pcx_scache2_data_rdy_buf1_px)); // Templated
   pcx_buf_scache buf3_3(/*AUTOINST*/
			 // Outputs
			 .pcx_scache_data_px(pcx_scache3_data_px_buf3[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_px(pcx_scache3_data_rdy_px), // Templated
			 // Inputs
			 .pcx_scache_data_px_l(pcx_scache3_data_buf2_l[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_arb_px(pcx_scache3_data_rdy_buf1_px)); // Templated
   /*
   pcx_buf_scache  AUTO_TEMPLATE(
                                  // Outputs
                                  .pcx_scache_data_px(pcx_scache@_data_px_buf4_l[`PCX_WIDTH-1:0]),
                                  .pcx_scache_data_rdy_px(pcx_scache0_atom_px1),
                                  // Inputs
                                  .pcx_scache_data_rdy_arb_px(pcx_scache0_atom_buf0_2_px1),
                                  .pcx_scache_data_px_l(pcx_scache@_data_px_buf3[`PCX_WIDTH-1:0]));
    */

   pcx_buf_scache buf0_4(/*AUTOINST*/
			 // Outputs
			 .pcx_scache_data_px(pcx_scache0_data_px_buf4_l[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_px(pcx_scache0_atom_px1), // Templated
			 // Inputs
			 .pcx_scache_data_px_l(pcx_scache0_data_px_buf3[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_arb_px(pcx_scache0_atom_buf0_2_px1)); // Templated
   /*
   pcx_buf_scache  AUTO_TEMPLATE(
                                  // Outputs
                                  .pcx_scache_data_px(pcx_scache@_data_px_buf4_l[`PCX_WIDTH-1:0]),
                                  .pcx_scache_data_rdy_px(pcx_scache1_atom_px1),
                  // Inputs
                                  .pcx_scache_data_rdy_arb_px(pcx_scache1_atom_buf1_2_px1),
                                  .pcx_scache_data_px_l(pcx_scache@_data_px_buf3[`PCX_WIDTH-1:0]));
    */
   pcx_buf_scache buf1_4(/*AUTOINST*/
			 // Outputs
			 .pcx_scache_data_px(pcx_scache1_data_px_buf4_l[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_px(pcx_scache1_atom_px1), // Templated
			 // Inputs
			 .pcx_scache_data_px_l(pcx_scache1_data_px_buf3[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_arb_px(pcx_scache1_atom_buf1_2_px1)); // Templated
   /*
   pcx_buf_scache  AUTO_TEMPLATE(
                                  // Outputs
                                  .pcx_scache_data_px(pcx_scache@_data_px_buf4_l[`PCX_WIDTH-1:0]),
                                  .pcx_scache_data_rdy_px(pcx_scache@_atom_px1),
                  // Inputs
                                  .pcx_scache_data_rdy_arb_px(pcx_scache@_atom_px),
                                  .pcx_scache_data_px_l(pcx_scache@_data_px_buf3[`PCX_WIDTH-1:0]));
    */
   pcx_buf_scache buf2_4(/*AUTOINST*/
			 // Outputs
			 .pcx_scache_data_px(pcx_scache2_data_px_buf4_l[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_px(pcx_scache2_atom_px1), // Templated
			 // Inputs
			 .pcx_scache_data_px_l(pcx_scache2_data_px_buf3[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_arb_px(pcx_scache2_atom_px)); // Templated
   pcx_buf_scache buf3_4(/*AUTOINST*/
			 // Outputs
			 .pcx_scache_data_px(pcx_scache3_data_px_buf4_l[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_px(pcx_scache3_atom_px1), // Templated
			 // Inputs
			 .pcx_scache_data_px_l(pcx_scache3_data_px_buf3[`PCX_WIDTH-1:0]), // Templated
			 .pcx_scache_data_rdy_arb_px(pcx_scache3_atom_px)); // Templated
   /*
   pcx_data_px2 AUTO_TEMPLATE( 
				 // Outputs
				 .pcx_data_px2(pcx_scache@_data_px2[`PCX_WIDTH-1:0]),
				 .pcx_data_rdy_px2(),
				 .pcx_stall_pq_buf(),
				 .so(pcx_scache0_dat_px2_so_1),
				 // Inputs
                                 .se(se_buf4_top),
				 .pcx_data_px_l(pcx_scache@_data_px_buf4_l[`PCX_WIDTH-1:0]),
				 .pcx_data_rdy_px(1'b0),
				 .pcx_stall_pq(1'b0),
				 .si(cpx_buf_top_pt0_so_1));
*/

   pcx_data_px2	pcx_scache0_dat_px2(/*AUTOINST*/
				    // Outputs
				    .pcx_data_px2(pcx_scache0_data_px2[`PCX_WIDTH-1:0]), // Templated
				    .pcx_data_rdy_px2(),	 // Templated
				    .pcx_stall_pq_buf(),	 // Templated
				    .so	(pcx_scache0_dat_px2_so_1), // Templated
				    // Inputs
				    .pcx_data_px_l(pcx_scache0_data_px_buf4_l[`PCX_WIDTH-1:0]), // Templated
				    .pcx_data_rdy_px(1'b0),	 // Templated
				    .pcx_stall_pq(1'b0),	 // Templated
				    .rclk(rclk),
				    .si	(cpx_buf_top_pt0_so_1),	 // Templated
				    .se	(se_buf4_top));		 // Templated
   /*
   pcx_data_px2 AUTO_TEMPLATE( 
				 // Outputs
				 .pcx_data_px2(pcx_scache@_data_px2[`PCX_WIDTH-1:0]),
				 .pcx_data_rdy_px2(),
				 .pcx_stall_pq_buf(),
				 .so(pcx_scache1_dat_px2_so_1),
				 // Inputs
                                 .se(se_buf4_bottom),
				 .pcx_data_px_l(pcx_scache@_data_px_buf4_l[`PCX_WIDTH-1:0]),
				 .pcx_data_rdy_px(1'b0),
				 .pcx_stall_pq(1'b0),
				 .si(pt1_so_1));
*/

   pcx_data_px2	pcx_scache1_dat_px2(/*AUTOINST*/
				    // Outputs
				    .pcx_data_px2(pcx_scache1_data_px2[`PCX_WIDTH-1:0]), // Templated
				    .pcx_data_rdy_px2(),	 // Templated
				    .pcx_stall_pq_buf(),	 // Templated
				    .so	(pcx_scache1_dat_px2_so_1), // Templated
				    // Inputs
				    .pcx_data_px_l(pcx_scache1_data_px_buf4_l[`PCX_WIDTH-1:0]), // Templated
				    .pcx_data_rdy_px(1'b0),	 // Templated
				    .pcx_stall_pq(1'b0),	 // Templated
				    .rclk(rclk),
				    .si	(pt1_so_1),		 // Templated
				    .se	(se_buf4_bottom));	 // Templated
   /*
   pcx_data_px2 AUTO_TEMPLATE( 
				 // Outputs
				 .pcx_data_px2(pcx_scache@_data_px2[`PCX_WIDTH-1:0]),
				 .pcx_data_rdy_px2(),
				 .pcx_stall_pq_buf(),
				 .so(pcx_scache2_dat_px2_so_1),
				 // Inputs
                                 .se(se_buf2_top),
				 .pcx_data_px_l(pcx_scache@_data_px_buf4_l[`PCX_WIDTH-1:0]),
				 .pcx_data_rdy_px(1'b0),
				 .pcx_stall_pq(1'b0),
				 .si(pcx_scache3_dat_px2_so_1));
*/

   pcx_data_px2	pcx_scache2_dat_px2(/*AUTOINST*/
				    // Outputs
				    .pcx_data_px2(pcx_scache2_data_px2[`PCX_WIDTH-1:0]), // Templated
				    .pcx_data_rdy_px2(),	 // Templated
				    .pcx_stall_pq_buf(),	 // Templated
				    .so	(pcx_scache2_dat_px2_so_1), // Templated
				    // Inputs
				    .pcx_data_px_l(pcx_scache2_data_px_buf4_l[`PCX_WIDTH-1:0]), // Templated
				    .pcx_data_rdy_px(1'b0),	 // Templated
				    .pcx_stall_pq(1'b0),	 // Templated
				    .rclk(rclk),
				    .si	(pcx_scache3_dat_px2_so_1), // Templated
				    .se	(se_buf2_top));		 // Templated
   /*
   pcx_data_px2 AUTO_TEMPLATE( 
				 // Outputs
				 .pcx_data_px2(pcx_scache@_data_px2[`PCX_WIDTH-1:0]),
				 .pcx_data_rdy_px2(),
				 .pcx_stall_pq_buf(),
				 .so(pcx_scache3_dat_px2_so_1),
				 // Inputs
                                 .se(se_buf2_bottom),
				 .pcx_data_px_l(pcx_scache@_data_px_buf4_l[`PCX_WIDTH-1:0]),
				 .pcx_data_rdy_px(1'b0),
				 .pcx_stall_pq(1'b0),
				 .si(pcx_fpiodata_px2_so_1));
*/

   pcx_data_px2	pcx_scache3_dat_px2(/*AUTOINST*/
				    // Outputs
				    .pcx_data_px2(pcx_scache3_data_px2[`PCX_WIDTH-1:0]), // Templated
				    .pcx_data_rdy_px2(),	 // Templated
				    .pcx_stall_pq_buf(),	 // Templated
				    .so	(pcx_scache3_dat_px2_so_1), // Templated
				    // Inputs
				    .pcx_data_px_l(pcx_scache3_data_px_buf4_l[`PCX_WIDTH-1:0]), // Templated
				    .pcx_data_rdy_px(1'b0),	 // Templated
				    .pcx_stall_pq(1'b0),	 // Templated
				    .rclk(rclk),
				    .si	(pcx_fpiodata_px2_so_1), // Templated
				    .se	(se_buf2_bottom));	 // Templated
   /*
   pcx_buf_fpio  AUTO_TEMPLATE(
				  // Outputs
				  .pcx_fpio_data_px(pcx_fpio_data_px2[`PCX_WIDTH-1:0]),
				  .pcx_fpio_data_rdy_px(pcx_fpio_data_rdy_px2),
		  // Inputs	       
                                  .pcx_fpio_data_rdy_arb_px(pcx_fpio_data_rdy_ff_px2), 
				  .pcx_fpio_data_ff_px(pcx_fpio_data_ff_px2[`PCX_WIDTH-1:0]));
    */
   pcx_buf_fpio buffpio(/*AUTOINST*/
			// Outputs
			.pcx_fpio_data_px(pcx_fpio_data_px2[`PCX_WIDTH-1:0]), // Templated
			.pcx_fpio_data_rdy_px(pcx_fpio_data_rdy_px2), // Templated
			// Inputs
			.pcx_fpio_data_ff_px(pcx_fpio_data_ff_px2[`PCX_WIDTH-1:0]), // Templated
			.pcx_fpio_data_rdy_arb_px(pcx_fpio_data_rdy_ff_px2)); // Templated
   /*
   pcx_data_px2 AUTO_TEMPLATE( 
				 // Outputs
				 .pcx_data_px2(pcx_fpio_data_ff_px2[`PCX_WIDTH-1:0]),
				 .pcx_data_rdy_px2(pcx_fpio_data_rdy_ff_px2),
				 .pcx_stall_pq_buf(),
				 .so(pcx_fpiodata_px2_so_1),
				 // Inputs
                                 .se(se_buf0_middle),
				 .pcx_data_px_l(pcx_fpio_data_px_buf_l[`PCX_WIDTH-1:0]),
				 .pcx_data_rdy_px(pcx_fpio_data_rdy_arb_px),
				 .pcx_stall_pq(1'b0),
				 .si(si_1));
*/
   pcx_data_px2 pcx_fpiodata_px2(/*AUTOINST*/
				 // Outputs
				 .pcx_data_px2(pcx_fpio_data_ff_px2[`PCX_WIDTH-1:0]), // Templated
				 .pcx_data_rdy_px2(pcx_fpio_data_rdy_ff_px2), // Templated
				 .pcx_stall_pq_buf(),		 // Templated
				 .so	(pcx_fpiodata_px2_so_1), // Templated
				 // Inputs
				 .pcx_data_px_l(pcx_fpio_data_px_buf_l[`PCX_WIDTH-1:0]), // Templated
				 .pcx_data_rdy_px(pcx_fpio_data_rdy_arb_px), // Templated
				 .pcx_stall_pq(1'b0),		 // Templated
				 .rclk	(rclk),
				 .si	(si_1),			 // Templated
				 .se	(se_buf0_middle));	 // Templated
   /*
   pcx_buf_fpio  AUTO_TEMPLATE(
				  // Outputs
				  .pcx_fpio_data_px(pcx_fpio_data_px_buf_l[`PCX_WIDTH-1:0]),
				  .pcx_fpio_data_rdy_px(arst_l_buf_fpio_inff),
		                  // Inputs	       
                                  .pcx_fpio_data_rdy_arb_px(cmp_arst_l), 
				  .pcx_fpio_data_ff_px(pcx_fpio_data_px_l[`PCX_WIDTH-1:0]));
    */


  pcx_buf_fpio  buffpio_inff(/*AUTOINST*/
			     // Outputs
			     .pcx_fpio_data_px(pcx_fpio_data_px_buf_l[`PCX_WIDTH-1:0]), // Templated
			     .pcx_fpio_data_rdy_px(arst_l_buf_fpio_inff), // Templated
			     // Inputs
			     .pcx_fpio_data_ff_px(pcx_fpio_data_px_l[`PCX_WIDTH-1:0]), // Templated
			     .pcx_fpio_data_rdy_arb_px(cmp_arst_l)); // Templated
   /*
   pcx_databuf_pa  AUTO_TEMPLATE(
                                  // Outputs
                                  .spc_pcx_data_buf_pa(pcx_io_data_px2[`PCX_WIDTH-1:0]),
                                  .spc_pcx_data_buf_rdy(pcx_io_data_rdy_px2),
                                  // Inputs
                                  .spc_pcx_data_rdy(pcx_io_data_rdy_ff_px2),
                                  .spc_pcx_data_pa(pcx_io_data_ff_px2[`PCX_WIDTH-1:0]));
    */


  pcx_databuf_pa  bufio_outff(/*AUTOINST*/
			      // Outputs
			      .spc_pcx_data_buf_pa(pcx_io_data_px2[`PCX_WIDTH-1:0]), // Templated
			      .spc_pcx_data_buf_rdy(pcx_io_data_rdy_px2), // Templated
			      // Inputs
			      .spc_pcx_data_pa(pcx_io_data_ff_px2[`PCX_WIDTH-1:0]), // Templated
			      .spc_pcx_data_rdy(pcx_io_data_rdy_ff_px2)); // Templated
   /*
   pcx_data_px2 AUTO_TEMPLATE(
                                 // Outputs
                                 .pcx_data_px2(pcx_io_data_ff_px2[`PCX_WIDTH-1:0]),
                                 .pcx_data_rdy_px2(pcx_io_data_rdy_ff_px2),
				 .pcx_stall_pq_buf(io_pcx_stall_buf1_pq),
                                 .so(pcx_iodata_px2_so_1),
                                 // Inputs
                                 .se(se_buf3_middle),
                                 .pcx_data_px_l(pcx_io_data_px_buf_l[`PCX_WIDTH-1:0]),
                                 .pcx_data_rdy_px(pcx_io_data_rdy_arb_buf_px),
				 .pcx_stall_pq(io_pcx_stall_pq),
                                 .si(ccx_clk_hdr_so_1));
*/
   pcx_data_px2 pcx_iodata_px2(/*AUTOINST*/
			       // Outputs
			       .pcx_data_px2(pcx_io_data_ff_px2[`PCX_WIDTH-1:0]), // Templated
			       .pcx_data_rdy_px2(pcx_io_data_rdy_ff_px2), // Templated
			       .pcx_stall_pq_buf(io_pcx_stall_buf1_pq), // Templated
			       .so	(pcx_iodata_px2_so_1),	 // Templated
			       // Inputs
			       .pcx_data_px_l(pcx_io_data_px_buf_l[`PCX_WIDTH-1:0]), // Templated
			       .pcx_data_rdy_px(pcx_io_data_rdy_arb_buf_px), // Templated
			       .pcx_stall_pq(io_pcx_stall_pq),	 // Templated
			       .rclk	(rclk),
			       .si	(ccx_clk_hdr_so_1),	 // Templated
			       .se	(se_buf3_middle));	 // Templated
   /*
   pcx_databuf_pa  AUTO_TEMPLATE(
                                  // Outputs
                                  .spc_pcx_data_buf_pa(pcx_io_data_px_buf_l[`PCX_WIDTH-1:0]),
                                  .spc_pcx_data_buf_rdy(pcx_io_data_rdy_arb_buf_px),
                                  // Inputs
                                  .spc_pcx_data_rdy(pcx_fpio_data_rdy_arb_px),
                                  .spc_pcx_data_pa(pcx_fpio_data_px_l[`PCX_WIDTH-1:0]));
    */


  pcx_databuf_pa  bufio_inff(/*AUTOINST*/
			     // Outputs
			     .spc_pcx_data_buf_pa(pcx_io_data_px_buf_l[`PCX_WIDTH-1:0]), // Templated
			     .spc_pcx_data_buf_rdy(pcx_io_data_rdy_arb_buf_px), // Templated
			     // Inputs
			     .spc_pcx_data_pa(pcx_fpio_data_px_l[`PCX_WIDTH-1:0]), // Templated
			     .spc_pcx_data_rdy(pcx_fpio_data_rdy_arb_px)); // Templated
/*
   pcx_databuf_pa AUTO_TEMPLATE(
				 // Outputs
				 .spc_pcx_data_buf_pa(spc@_pcx_data_buf_pa[`PCX_WIDTH-1:0]),
                                 .spc_pcx_data_buf_rdy(),
				 // Inputs
                                 .spc_pcx_data_rdy(1'b0),
				 .spc_pcx_data_pa(spc@_pcx_data_pa[`PCX_WIDTH-1:0]));
   */

   pcx_databuf_pa pcx_databuf_pa1(/*AUTOINST*/
				  // Outputs
				  .spc_pcx_data_buf_pa(spc1_pcx_data_buf_pa[`PCX_WIDTH-1:0]), // Templated
				  .spc_pcx_data_buf_rdy(),	 // Templated
				  // Inputs
				  .spc_pcx_data_pa(spc1_pcx_data_pa[`PCX_WIDTH-1:0]), // Templated
				  .spc_pcx_data_rdy(1'b0));	 // Templated
   pcx_databuf_pa pcx_databuf_pa3(/*AUTOINST*/
				  // Outputs
				  .spc_pcx_data_buf_pa(spc3_pcx_data_buf_pa[`PCX_WIDTH-1:0]), // Templated
				  .spc_pcx_data_buf_rdy(),	 // Templated
				  // Inputs
				  .spc_pcx_data_pa(spc3_pcx_data_pa[`PCX_WIDTH-1:0]), // Templated
				  .spc_pcx_data_rdy(1'b0));	 // Templated
   pcx_databuf_pa pcx_databuf_pa5(/*AUTOINST*/
				  // Outputs
				  .spc_pcx_data_buf_pa(spc5_pcx_data_buf_pa[`PCX_WIDTH-1:0]), // Templated
				  .spc_pcx_data_buf_rdy(),	 // Templated
				  // Inputs
				  .spc_pcx_data_pa(spc5_pcx_data_pa[`PCX_WIDTH-1:0]), // Templated
				  .spc_pcx_data_rdy(1'b0));	 // Templated
   pcx_databuf_pa pcx_databuf_pa7(/*AUTOINST*/
				  // Outputs
				  .spc_pcx_data_buf_pa(spc7_pcx_data_buf_pa[`PCX_WIDTH-1:0]), // Templated
				  .spc_pcx_data_buf_rdy(),	 // Templated
				  // Inputs
				  .spc_pcx_data_pa(spc7_pcx_data_pa[`PCX_WIDTH-1:0]), // Templated
				  .spc_pcx_data_rdy(1'b0));	 // Templated
   pcx_databuf_pa pcx_databuf_pa0(/*AUTOINST*/
				  // Outputs
				  .spc_pcx_data_buf_pa(spc0_pcx_data_buf_pa[`PCX_WIDTH-1:0]), // Templated
				  .spc_pcx_data_buf_rdy(),	 // Templated
				  // Inputs
				  .spc_pcx_data_pa(spc0_pcx_data_pa[`PCX_WIDTH-1:0]), // Templated
				  .spc_pcx_data_rdy(1'b0));	 // Templated
   pcx_databuf_pa pcx_databuf_pa2(/*AUTOINST*/
				  // Outputs
				  .spc_pcx_data_buf_pa(spc2_pcx_data_buf_pa[`PCX_WIDTH-1:0]), // Templated
				  .spc_pcx_data_buf_rdy(),	 // Templated
				  // Inputs
				  .spc_pcx_data_pa(spc2_pcx_data_pa[`PCX_WIDTH-1:0]), // Templated
				  .spc_pcx_data_rdy(1'b0));	 // Templated
   pcx_databuf_pa pcx_databuf_pa4(/*AUTOINST*/
				  // Outputs
				  .spc_pcx_data_buf_pa(spc4_pcx_data_buf_pa[`PCX_WIDTH-1:0]), // Templated
				  .spc_pcx_data_buf_rdy(),	 // Templated
				  // Inputs
				  .spc_pcx_data_pa(spc4_pcx_data_pa[`PCX_WIDTH-1:0]), // Templated
				  .spc_pcx_data_rdy(1'b0));	 // Templated
   pcx_databuf_pa pcx_databuf_pa6(/*AUTOINST*/
				  // Outputs
				  .spc_pcx_data_buf_pa(spc6_pcx_data_buf_pa[`PCX_WIDTH-1:0]), // Templated
				  .spc_pcx_data_buf_rdy(),	 // Templated
				  // Inputs
				  .spc_pcx_data_pa(spc6_pcx_data_pa[`PCX_WIDTH-1:0]), // Templated
				  .spc_pcx_data_rdy(1'b0));	 // Templated
endmodule

   
// Local Variables:
// verilog-library-directories:("." "../../../../../common/rtl" "../../common/rtl")
// End:
		  
