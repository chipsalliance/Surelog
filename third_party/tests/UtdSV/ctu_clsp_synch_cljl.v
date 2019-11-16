// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: ctu_clsp_synch_cljl.v
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
//
//    Cluster Name:  CTU
//    Unit Name: ctu_clsp_dramif
//
//-----------------------------------------------------------------------------
`include "sys.h"

module ctu_clsp_synch_cljl(/*AUTOARG*/
// Outputs
jbi_ctu_tr_jl, iob_ctu_tr_jl, iob_ctu_l2_tr_jl, dram13_ctu_tr_jl, 
dram02_ctu_tr_jl, ctu_misc_cken_jl, ctu_jbusr_cken_jl, 
ctu_jbusl_cken_jl, ctu_jbi_cken_jl, ctu_iob_cken_jl, ctu_efc_cken_jl, 
ctu_dram13_cken_jl, ctu_dram02_cken_jl, ctu_dbg_cken_jl, 
clsp_ctrl_srarm_jl, 
// Inputs
jbus_clk, jbi_ctu_tr, iob_ctu_tr, iob_ctu_l2_tr, io_pwron_rst_l, 
dram13_ctu_tr, dram02_ctu_tr, ctu_jbi_cken_pre_jl, 
ctu_iob_cken_pre_jl, ctu_efc_cken_pre_jl, ctu_dram13_cken_pre_jl, 
ctu_dram02_cken_pre_jl, clsp_ctrl_srarm_pre_jl, start_clk_jl, 
ctu_jbusl_cken_pre_jl, ctu_jbusr_cken_pre_jl, ctu_misc_cken_pre_jl, 
ctu_dbg_cken_pre_jl
);

/*AUTOINPUT*/
// Beginning of automatic inputs (from unused autoinst inputs)
input			clsp_ctrl_srarm_pre_jl;	// To u_clsp_ctrl_srarm_jl of dffrl_ns.v
input			ctu_dram02_cken_pre_jl;	// To u_ctu_dram02_cken_jl of dffrl_ns.v
input			ctu_dram13_cken_pre_jl;	// To u_ctu_dram13_cken_jl of dffrl_ns.v
input			ctu_efc_cken_pre_jl;	// To u_ctu_efc_cken_jl of dffrl_ns.v
input			ctu_iob_cken_pre_jl;	// To u_ctu_iob_cken_jl of dffrl_ns.v
input			ctu_jbi_cken_pre_jl;	// To u_ctu_jbi_cken_jl of dffrl_ns.v
input			dram02_ctu_tr;		// To u_dram02_ctu_tr_jl of dff_ns.v
input			dram13_ctu_tr;		// To u_dram13_ctu_tr_jl of dff_ns.v
input			io_pwron_rst_l;		// To u_ctu_jbusl_cken_jl of dffsl_async_ns.v, ...
input			iob_ctu_l2_tr;		// To u_iob_ctu_l2_tr_jl of dff_ns.v
input			iob_ctu_tr;		// To u_iob_ctu_tr_jl of dff_ns.v
input			jbi_ctu_tr;		// To u_jbi_ctu_tr_jl of dff_ns.v
input			jbus_clk;		// To u_clsp_ctrl_srarm_jl of dffrl_ns.v, ...
// End of automatics
input                   start_clk_jl;
input 			ctu_jbusl_cken_pre_jl;
input 			ctu_jbusr_cken_pre_jl;
input 			ctu_misc_cken_pre_jl;
input                   ctu_dbg_cken_pre_jl;
/*AUTOOUTPUT*/
// Beginning of automatic outputs (from unused autoinst outputs)
output			clsp_ctrl_srarm_jl;	// From u_clsp_ctrl_srarm_jl of dffrl_ns.v
output			ctu_dbg_cken_jl;	// From u_ctu_dbg_cken_jl of dffsl_async_ns.v
output			ctu_dram02_cken_jl;	// From u_ctu_dram02_cken_jl of dffrl_ns.v
output			ctu_dram13_cken_jl;	// From u_ctu_dram13_cken_jl of dffrl_ns.v
output			ctu_efc_cken_jl;	// From u_ctu_efc_cken_jl of dffrl_ns.v
output			ctu_iob_cken_jl;	// From u_ctu_iob_cken_jl of dffrl_ns.v
output			ctu_jbi_cken_jl;	// From u_ctu_jbi_cken_jl of dffrl_ns.v
output			ctu_jbusl_cken_jl;	// From u_ctu_jbusl_cken_jl of dffsl_async_ns.v
output			ctu_jbusr_cken_jl;	// From u_ctu_jbusr_cken_jl of dffsl_async_ns.v
output			ctu_misc_cken_jl;	// From u_ctu_misc_cken_jl of dffsl_async_ns.v
output			dram02_ctu_tr_jl;	// From u_dram02_ctu_tr_jl of dff_ns.v
output			dram13_ctu_tr_jl;	// From u_dram13_ctu_tr_jl of dff_ns.v
output			iob_ctu_l2_tr_jl;	// From u_iob_ctu_l2_tr_jl of dff_ns.v
output			iob_ctu_tr_jl;		// From u_iob_ctu_tr_jl of dff_ns.v
output			jbi_ctu_tr_jl;		// From u_jbi_ctu_tr_jl of dff_ns.v
// End of automatics
/*AUTOWIRE*/
// Beginning of automatic wires (for undeclared instantiated-module outputs)
// End of automatics
wire ctu_jbusl_cken_jl_nxt;
wire ctu_jbusr_cken_jl_nxt;
wire ctu_misc_cken_jl_nxt;
wire ctu_dbg_cken_jl_nxt;

   /* dffrl_ns AUTO_TEMPLATE (
       .din(clsp_ctrl_srarm_pre_jl),
       .q (clsp_ctrl_srarm_jl),
       .rst_l(start_clk_jl),
       .clk (jbus_clk),
    );
  */
     dffrl_ns u_clsp_ctrl_srarm_jl( .rst_l	(start_clk_jl), /*AUTOINST*/
				   // Outputs
				   .q	(clsp_ctrl_srarm_jl),	 // Templated
				   // Inputs
				   .din	(clsp_ctrl_srarm_pre_jl), // Templated
				   .clk	(jbus_clk));		 // Templated


   /* dffrl_ns AUTO_TEMPLATE (
       .din(ctu_dram@_cken_pre_jl),
       .q (ctu_dram@_cken_jl),
       .rst_l(start_clk_jl),
       .clk (jbus_clk),
    );
  */
     dffrl_ns u_ctu_dram02_cken_jl( .rst_l	(start_clk_jl), /*AUTOINST*/
				   // Outputs
				   .q	(ctu_dram02_cken_jl),	 // Templated
				   // Inputs
				   .din	(ctu_dram02_cken_pre_jl), // Templated
				   .clk	(jbus_clk));		 // Templated
     dffrl_ns u_ctu_dram13_cken_jl( .rst_l	(start_clk_jl), /*AUTOINST*/
				   // Outputs
				   .q	(ctu_dram13_cken_jl),	 // Templated
				   // Inputs
				   .din	(ctu_dram13_cken_pre_jl), // Templated
				   .clk	(jbus_clk));		 // Templated


   /* dffrl_ns AUTO_TEMPLATE (
       .din(ctu_iob_cken_pre_jl),
       .q (ctu_iob_cken_jl),
       .rst_l(start_clk_jl),
       .clk (jbus_clk),
    );
  */
     dffrl_ns u_ctu_iob_cken_jl( .rst_l	(start_clk_jl), /*AUTOINST*/
				// Outputs
				.q	(ctu_iob_cken_jl),	 // Templated
				// Inputs
				.din	(ctu_iob_cken_pre_jl),	 // Templated
				.clk	(jbus_clk));		 // Templated

   /* dffrl_ns AUTO_TEMPLATE (
       .din(ctu_efc_cken_pre_jl),
       .q (ctu_efc_cken_jl),
       .rst_l(start_clk_jl),
       .clk (jbus_clk),
    );
  */
     dffrl_ns u_ctu_efc_cken_jl( .rst_l	(start_clk_jl), /*AUTOINST*/
				// Outputs
				.q	(ctu_efc_cken_jl),	 // Templated
				// Inputs
				.din	(ctu_efc_cken_pre_jl),	 // Templated
				.clk	(jbus_clk));		 // Templated


   /* dffsl_async_ns AUTO_TEMPLATE (
       .din(ctu_jbusl_cken_jl_nxt),
       .q (ctu_jbusl_cken_jl),
       .set_l(io_pwron_rst_l),
       .clk (jbus_clk),
    );
  */
     assign ctu_jbusl_cken_jl_nxt =  start_clk_jl ? ctu_jbusl_cken_pre_jl : 1'b1;
 
     dffsl_async_ns u_ctu_jbusl_cken_jl(
				   .din	(ctu_jbusl_cken_jl_nxt),
                                   /*AUTOINST*/
					// Outputs
					.q(ctu_jbusl_cken_jl),	 // Templated
					// Inputs
					.clk(jbus_clk),		 // Templated
					.set_l(io_pwron_rst_l));	 // Templated

   /* dffsl_async_ns AUTO_TEMPLATE (
       .din(ctu_jbusr_cken_jl_nxt),
       .q (ctu_jbusr_cken_jl),
       .set_l(io_pwron_rst_l),
       .clk (jbus_clk),
    );
  */
     assign ctu_jbusr_cken_jl_nxt =   start_clk_jl ?  ctu_jbusr_cken_pre_jl: 1'b1;

     dffsl_async_ns u_ctu_jbusr_cken_jl( 
				   .din	(ctu_jbusr_cken_jl_nxt),
                                   /*AUTOINST*/
					// Outputs
					.q(ctu_jbusr_cken_jl),	 // Templated
					// Inputs
					.clk(jbus_clk),		 // Templated
					.set_l(io_pwron_rst_l));	 // Templated


   /* dffrl_ns AUTO_TEMPLATE (
       .din(ctu_jbi_cken_pre_jl),
       .q (ctu_jbi_cken_jl),
       .rst_l(start_clk_jl),
       .clk (jbus_clk),
    );
  */
     dffrl_ns u_ctu_jbi_cken_jl( .rst_l	(start_clk_jl), /*AUTOINST*/
				// Outputs
				.q	(ctu_jbi_cken_jl),	 // Templated
				// Inputs
				.din	(ctu_jbi_cken_pre_jl),	 // Templated
				.clk	(jbus_clk));		 // Templated

 /* dffsl_async_ns AUTO_TEMPLATE (
       .din(ctu_dbg_cken_jl_nxt),
       .q (ctu_dbg_cken_jl),
       .set_l(io_pwron_rst_l),
       .clk (jbus_clk),
    );
  */
     assign ctu_dbg_cken_jl_nxt =   start_clk_jl ?  ctu_dbg_cken_pre_jl: 1'b1;


     dffsl_async_ns u_ctu_dbg_cken_jl( .set_l	(io_pwron_rst_l), /*AUTOINST*/
				      // Outputs
				      .q(ctu_dbg_cken_jl),	 // Templated
				      // Inputs
				      .din(ctu_dbg_cken_jl_nxt), // Templated
				      .clk(jbus_clk));		 // Templated

 /* dffsl_async_ns AUTO_TEMPLATE (
       .din(ctu_misc_cken_jl_nxt),
       .q (ctu_misc_cken_jl),
       .set_l(io_pwron_rst_l),
       .clk (jbus_clk),
    );
  */
     assign ctu_misc_cken_jl_nxt =   start_clk_jl ?  ctu_misc_cken_pre_jl: 1'b1;


     dffsl_async_ns u_ctu_misc_cken_jl( .set_l	(io_pwron_rst_l), /*AUTOINST*/
				       // Outputs
				       .q(ctu_misc_cken_jl),	 // Templated
				       // Inputs
				       .din(ctu_misc_cken_jl_nxt), // Templated
				       .clk(jbus_clk));		 // Templated

   /* dff_ns AUTO_TEMPLATE (
       .din(iob_ctu_l2_tr),
       .q (iob_ctu_l2_tr_jl),
       .clk (jbus_clk),
    );
  */
     dff_ns u_iob_ctu_l2_tr_jl(/*AUTOINST*/
			       // Outputs
			       .q	(iob_ctu_l2_tr_jl),	 // Templated
			       // Inputs
			       .din	(iob_ctu_l2_tr),	 // Templated
			       .clk	(jbus_clk));		 // Templated


   /* dff_ns AUTO_TEMPLATE (
       .din(iob_ctu_tr),
       .q (iob_ctu_tr_jl),
       .clk (jbus_clk),
    );
  */
     dff_ns u_iob_ctu_tr_jl(/*AUTOINST*/
			    // Outputs
			    .q		(iob_ctu_tr_jl),	 // Templated
			    // Inputs
			    .din	(iob_ctu_tr),		 // Templated
			    .clk	(jbus_clk));		 // Templated

   /* dff_ns AUTO_TEMPLATE (
       .din(jbi_ctu_tr),
       .q (jbi_ctu_tr_jl),
       .clk (jbus_clk),
    );
  */
     dff_ns u_jbi_ctu_tr_jl(/*AUTOINST*/
			    // Outputs
			    .q		(jbi_ctu_tr_jl),	 // Templated
			    // Inputs
			    .din	(jbi_ctu_tr),		 // Templated
			    .clk	(jbus_clk));		 // Templated

   /* dff_ns AUTO_TEMPLATE (
       .din(dram@_ctu_tr),
       .q (dram@_ctu_tr_jl),
       .clk (jbus_clk),
    );
  */
     dff_ns u_dram02_ctu_tr_jl (/*AUTOINST*/
				// Outputs
				.q	(dram02_ctu_tr_jl),	 // Templated
				// Inputs
				.din	(dram02_ctu_tr),	 // Templated
				.clk	(jbus_clk));		 // Templated
     dff_ns u_dram13_ctu_tr_jl (/*AUTOINST*/
				// Outputs
				.q	(dram13_ctu_tr_jl),	 // Templated
				// Inputs
				.din	(dram13_ctu_tr),	 // Templated
				.clk	(jbus_clk));		 // Templated


endmodule // ctu_clsp_cl_jg


// Local Variables:
// verilog-library-directories:("." "../common/rtl")
// verilog-library-files:("../common/rtl/ctu_lib.v" "../../common/rtl/swrvr_clib.v")
// verilog-auto-sense-defines-constant:t
// End:








