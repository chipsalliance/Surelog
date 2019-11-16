// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: ctu_clsp_synch_jldl.v
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

module ctu_clsp_synch_jldl(/*AUTOARG*/
// Outputs
ctu_dram13_dram_cken_dl, ctu_dram02_dram_cken_dl, ctu_dll3_byp_val, 
ctu_dll3_byp_l, ctu_dll2_byp_val, ctu_dll2_byp_l, ctu_dll1_byp_val, 
ctu_dll1_byp_l, ctu_dll0_byp_val, ctu_dll0_byp_l, 
ctu_ddr3_dram_cken_dl, ctu_ddr3_dll_delayctr, ctu_ddr2_dram_cken_dl, 
ctu_ddr2_dll_delayctr, ctu_ddr1_dram_cken_dl, ctu_ddr1_dll_delayctr, 
ctu_ddr0_dram_cken_dl, ctu_ddr0_dll_delayctr, ctu_ddr0_iodll_rst_l, 
ctu_ddr1_iodll_rst_l, ctu_ddr2_iodll_rst_l, ctu_ddr3_iodll_rst_l, 
start_clk_dl, 
// Inputs
ctu_dram13_cken_cl, ctu_dram02_cken_cl, ctu_dll3_byp_val_jl, 
ctu_dll3_byp_l_jl, ctu_dll2_byp_val_jl, ctu_dll2_byp_l_jl, 
ctu_dll1_byp_val_jl, ctu_dll1_byp_l_jl, ctu_dll0_byp_val_jl, 
ctu_dll0_byp_l_jl, ctu_ddr3_iodll_rst_jl_l, ctu_ddr3_dll_delayctr_jl, 
ctu_ddr3_cken_cl, ctu_ddr2_iodll_rst_jl_l, ctu_ddr2_dll_delayctr_jl, 
ctu_ddr2_cken_cl, ctu_ddr1_iodll_rst_jl_l, ctu_ddr1_dll_delayctr_jl, 
ctu_ddr1_cken_cl, ctu_ddr0_iodll_rst_jl_l, ctu_ddr0_dll_delayctr_jl, 
ctu_ddr0_cken_cl, coin_edge, cmp_clk, jbus_rx_sync, start_clk_cl, 
io_pwron_rst_l, ctu_dram_tx_sync_early
);

/*AUTOINPUT*/
// Beginning of automatic inputs (from unused autoinst inputs)
input			cmp_clk;		// To u_ctu_dram02_dram_cken of ctu_synch_cl_dl.v, ...
input			coin_edge;		// To u_ctu_ddr0_dll_delayctr of ctu_synch_jl_dl.v, ...
input			ctu_ddr0_cken_cl;	// To u_ctu_ddr0_dram_cken of ctu_synch_cl_dl.v
input [2:0]		ctu_ddr0_dll_delayctr_jl;// To u_ctu_ddr0_dll_delayctr of ctu_synch_jl_dl.v
input			ctu_ddr0_iodll_rst_jl_l;// To u_ctu_ddr0_iodll_rst_dl_l of ctu_synch_jl_dl.v
input			ctu_ddr1_cken_cl;	// To u_ctu_ddr1_dram_cken of ctu_synch_cl_dl.v
input [2:0]		ctu_ddr1_dll_delayctr_jl;// To u_ctu_ddr1_dll_delayctr of ctu_synch_jl_dl.v
input			ctu_ddr1_iodll_rst_jl_l;// To u_ctu_ddr1_iodll_rst_dl_l of ctu_synch_jl_dl.v
input			ctu_ddr2_cken_cl;	// To u_ctu_ddr2_dram_cken of ctu_synch_cl_dl.v
input [2:0]		ctu_ddr2_dll_delayctr_jl;// To u_ctu_ddr2_dll_delayctr of ctu_synch_jl_dl.v
input			ctu_ddr2_iodll_rst_jl_l;// To u_ctu_ddr2_iodll_rst_dl_l of ctu_synch_jl_dl.v
input			ctu_ddr3_cken_cl;	// To u_ctu_ddr3_dram_cken of ctu_synch_cl_dl.v
input [2:0]		ctu_ddr3_dll_delayctr_jl;// To u_ctu_ddr3_dll_delayctr of ctu_synch_jl_dl.v
input			ctu_ddr3_iodll_rst_jl_l;// To u_ctu_ddr3_iodll_rst_dl_l of ctu_synch_jl_dl.v
input			ctu_dll0_byp_l_jl;	// To u_ctu_dll0_byp_l of ctu_synch_jl_dl.v
input [4:0]		ctu_dll0_byp_val_jl;	// To u_ctu_dll0_byp_val of ctu_synch_jl_dl.v
input			ctu_dll1_byp_l_jl;	// To u_ctu_dll1_byp_l of ctu_synch_jl_dl.v
input [4:0]		ctu_dll1_byp_val_jl;	// To u_ctu_dll1_byp_val of ctu_synch_jl_dl.v
input			ctu_dll2_byp_l_jl;	// To u_ctu_dll2_byp_l of ctu_synch_jl_dl.v
input [4:0]		ctu_dll2_byp_val_jl;	// To u_ctu_dll2_byp_val of ctu_synch_jl_dl.v
input			ctu_dll3_byp_l_jl;	// To u_ctu_dll3_byp_l of ctu_synch_jl_dl.v
input [4:0]		ctu_dll3_byp_val_jl;	// To u_ctu_dll3_byp_val of ctu_synch_jl_dl.v
input			ctu_dram02_cken_cl;	// To u_ctu_dram02_dram_cken of ctu_synch_cl_dl.v
input			ctu_dram13_cken_cl;	// To u_ctu_dram13_dram_cken of ctu_synch_cl_dl.v
// End of automatics
input			jbus_rx_sync;		// To ctu_dram02_dram_cken of ctu_synch_jl_cl.v, ...
input                   start_clk_cl;
input                   io_pwron_rst_l;
input			ctu_dram_tx_sync_early;	// To u_ctu_dram02_dram_cken of ctu_synch_cl_dg.v, ...
/*AUTOOUTPUT*/
// Beginning of automatic outputs (from unused autoinst outputs)
output [2:0]		ctu_ddr0_dll_delayctr;	// From u_ctu_ddr0_dll_delayctr of ctu_synch_jl_dl.v
output			ctu_ddr0_dram_cken_dl;	// From u_ctu_ddr0_dram_cken of ctu_synch_cl_dl.v
output [2:0]		ctu_ddr1_dll_delayctr;	// From u_ctu_ddr1_dll_delayctr of ctu_synch_jl_dl.v
output			ctu_ddr1_dram_cken_dl;	// From u_ctu_ddr1_dram_cken of ctu_synch_cl_dl.v
output [2:0]		ctu_ddr2_dll_delayctr;	// From u_ctu_ddr2_dll_delayctr of ctu_synch_jl_dl.v
output			ctu_ddr2_dram_cken_dl;	// From u_ctu_ddr2_dram_cken of ctu_synch_cl_dl.v
output [2:0]		ctu_ddr3_dll_delayctr;	// From u_ctu_ddr3_dll_delayctr of ctu_synch_jl_dl.v
output			ctu_ddr3_dram_cken_dl;	// From u_ctu_ddr3_dram_cken of ctu_synch_cl_dl.v
output			ctu_dll0_byp_l;		// From u_ctu_dll0_byp_l of ctu_synch_jl_dl.v
output [4:0]		ctu_dll0_byp_val;	// From u_ctu_dll0_byp_val of ctu_synch_jl_dl.v
output			ctu_dll1_byp_l;		// From u_ctu_dll1_byp_l of ctu_synch_jl_dl.v
output [4:0]		ctu_dll1_byp_val;	// From u_ctu_dll1_byp_val of ctu_synch_jl_dl.v
output			ctu_dll2_byp_l;		// From u_ctu_dll2_byp_l of ctu_synch_jl_dl.v
output [4:0]		ctu_dll2_byp_val;	// From u_ctu_dll2_byp_val of ctu_synch_jl_dl.v
output			ctu_dll3_byp_l;		// From u_ctu_dll3_byp_l of ctu_synch_jl_dl.v
output [4:0]		ctu_dll3_byp_val;	// From u_ctu_dll3_byp_val of ctu_synch_jl_dl.v
output			ctu_dram02_dram_cken_dl;// From u_ctu_dram02_dram_cken of ctu_synch_cl_dl.v
output			ctu_dram13_dram_cken_dl;// From u_ctu_dram13_dram_cken of ctu_synch_cl_dl.v
// End of automatics
output                  ctu_ddr0_iodll_rst_l;
output                  ctu_ddr1_iodll_rst_l;
output                  ctu_ddr2_iodll_rst_l;
output                  ctu_ddr3_iodll_rst_l;
output                  start_clk_dl;
/*AUTOWIRE*/
// Beginning of automatic wires (for undeclared instantiated-module outputs)
// End of automatics
wire           jbus_rx_sync_gated;


    assign  jbus_rx_sync_gated = jbus_rx_sync & start_clk_cl;
    // transimit sync pulses are generated ahead of rx 


    dffrle_ns u_start_clk_dl (
       .din (start_clk_cl),
       .q(start_clk_dl),
       .en (ctu_dram_tx_sync_early ),
       .rst_l(start_clk_cl), 
       .clk (cmp_clk)
    );


   /*  ctu_synch_cl_dl AUTO_TEMPLATE (
       .presyncdata(ctu_dram@_cken_cl),
       .syncdata(ctu_dram@_dram_cken_dl),
       .ctu_dram_tx_sync_early(ctu_dram_tx_sync_early),
    );
  */
    ctu_synch_cl_dl u_ctu_dram02_dram_cken (/*AUTOINST*/
					    // Outputs
					    .syncdata(ctu_dram02_dram_cken_dl), // Templated
					    // Inputs
					    .cmp_clk(cmp_clk),
					    .ctu_dram_tx_sync_early(ctu_dram_tx_sync_early), // Templated
					    .presyncdata(ctu_dram02_cken_cl)); // Templated
    ctu_synch_cl_dl u_ctu_dram13_dram_cken (/*AUTOINST*/
					    // Outputs
					    .syncdata(ctu_dram13_dram_cken_dl), // Templated
					    // Inputs
					    .cmp_clk(cmp_clk),
					    .ctu_dram_tx_sync_early(ctu_dram_tx_sync_early), // Templated
					    .presyncdata(ctu_dram13_cken_cl)); // Templated



    
   /*  ctu_synch_jl_dl AUTO_TEMPLATE (
       .presyncdata (ctu_ddr@_dll_delayctr_jl[2:0]),
       .syncdata(ctu_ddr@_dll_delayctr[2:0]),
       .arst_l(io_pwron_rst_l),
    );
  */
    ctu_synch_jl_dl #(3) u_ctu_ddr0_dll_delayctr(
						 .jbus_rx_sync(jbus_rx_sync_gated),
                                                 /*AUTOINST*/
						 // Outputs
						 .syncdata(ctu_ddr0_dll_delayctr[2:0]), // Templated
						 // Inputs
						 .cmp_clk(cmp_clk),
						 .coin_edge(coin_edge),
						 .arst_l(io_pwron_rst_l), // Templated
						 .presyncdata(ctu_ddr0_dll_delayctr_jl[2:0])); // Templated
    ctu_synch_jl_dl #(3) u_ctu_ddr1_dll_delayctr(
						 .jbus_rx_sync(jbus_rx_sync_gated),
                                                 /*AUTOINST*/
						 // Outputs
						 .syncdata(ctu_ddr1_dll_delayctr[2:0]), // Templated
						 // Inputs
						 .cmp_clk(cmp_clk),
						 .coin_edge(coin_edge),
						 .arst_l(io_pwron_rst_l), // Templated
						 .presyncdata(ctu_ddr1_dll_delayctr_jl[2:0])); // Templated
    ctu_synch_jl_dl #(3) u_ctu_ddr2_dll_delayctr(
						 .jbus_rx_sync(jbus_rx_sync_gated),
                                                 /*AUTOINST*/
						 // Outputs
						 .syncdata(ctu_ddr2_dll_delayctr[2:0]), // Templated
						 // Inputs
						 .cmp_clk(cmp_clk),
						 .coin_edge(coin_edge),
						 .arst_l(io_pwron_rst_l), // Templated
						 .presyncdata(ctu_ddr2_dll_delayctr_jl[2:0])); // Templated
    ctu_synch_jl_dl #(3) u_ctu_ddr3_dll_delayctr(
						 .jbus_rx_sync(jbus_rx_sync_gated),
                                                 /*AUTOINST*/
						 // Outputs
						 .syncdata(ctu_ddr3_dll_delayctr[2:0]), // Templated
						 // Inputs
						 .cmp_clk(cmp_clk),
						 .coin_edge(coin_edge),
						 .arst_l(io_pwron_rst_l), // Templated
						 .presyncdata(ctu_ddr3_dll_delayctr_jl[2:0])); // Templated

 /*  ctu_synch_jl_dl AUTO_TEMPLATE (
       .presyncdata(ctu_dll@_byp_l_jl),
       .syncdata (ctu_dll@_byp_l),
       .ctu_dram_tx_sync_early(ctu_dram_tx_sync_early),
       .arst_l(io_pwron_rst_l), 
    );
  */

    ctu_synch_jl_dl u_ctu_dll0_byp_l(
				     .jbus_rx_sync(jbus_rx_sync_gated), 
                                     /*AUTOINST*/
				     // Outputs
				     .syncdata(ctu_dll0_byp_l),	 // Templated
				     // Inputs
				     .cmp_clk(cmp_clk),
				     .coin_edge(coin_edge),
				     .arst_l(io_pwron_rst_l),	 // Templated
				     .presyncdata(ctu_dll0_byp_l_jl)); // Templated
    ctu_synch_jl_dl u_ctu_dll1_byp_l(
				     .jbus_rx_sync(jbus_rx_sync_gated), 
                                     /*AUTOINST*/
				     // Outputs
				     .syncdata(ctu_dll1_byp_l),	 // Templated
				     // Inputs
				     .cmp_clk(cmp_clk),
				     .coin_edge(coin_edge),
				     .arst_l(io_pwron_rst_l),	 // Templated
				     .presyncdata(ctu_dll1_byp_l_jl)); // Templated
    ctu_synch_jl_dl u_ctu_dll2_byp_l(
				     .jbus_rx_sync(jbus_rx_sync_gated), 
                                     /*AUTOINST*/
				     // Outputs
				     .syncdata(ctu_dll2_byp_l),	 // Templated
				     // Inputs
				     .cmp_clk(cmp_clk),
				     .coin_edge(coin_edge),
				     .arst_l(io_pwron_rst_l),	 // Templated
				     .presyncdata(ctu_dll2_byp_l_jl)); // Templated
    ctu_synch_jl_dl u_ctu_dll3_byp_l(
				     .jbus_rx_sync(jbus_rx_sync_gated), 
                                     /*AUTOINST*/
				     // Outputs
				     .syncdata(ctu_dll3_byp_l),	 // Templated
				     // Inputs
				     .cmp_clk(cmp_clk),
				     .coin_edge(coin_edge),
				     .arst_l(io_pwron_rst_l),	 // Templated
				     .presyncdata(ctu_dll3_byp_l_jl)); // Templated

 /*  ctu_synch_jl_dl AUTO_TEMPLATE (
       .presyncdata(ctu_dll@_byp_val_jl[4:0]),
       .syncdata (ctu_dll@_byp_val[4:0]),
       .ctu_dram_tx_sync_early(ctu_dram_tx_sync_early),
       .arst_l(io_pwron_rst_l), 
    );
  */

    ctu_synch_jl_dl #(5) u_ctu_dll0_byp_val(
				            .jbus_rx_sync(jbus_rx_sync_gated), 
                                            /*AUTOINST*/
					    // Outputs
					    .syncdata(ctu_dll0_byp_val[4:0]), // Templated
					    // Inputs
					    .cmp_clk(cmp_clk),
					    .coin_edge(coin_edge),
					    .arst_l(io_pwron_rst_l), // Templated
					    .presyncdata(ctu_dll0_byp_val_jl[4:0])); // Templated
    ctu_synch_jl_dl #(5) u_ctu_dll1_byp_val(
				            .jbus_rx_sync(jbus_rx_sync_gated), 
                                            /*AUTOINST*/
					    // Outputs
					    .syncdata(ctu_dll1_byp_val[4:0]), // Templated
					    // Inputs
					    .cmp_clk(cmp_clk),
					    .coin_edge(coin_edge),
					    .arst_l(io_pwron_rst_l), // Templated
					    .presyncdata(ctu_dll1_byp_val_jl[4:0])); // Templated
    ctu_synch_jl_dl #(5) u_ctu_dll2_byp_val(
				            .jbus_rx_sync(jbus_rx_sync_gated), 
                                            /*AUTOINST*/
					    // Outputs
					    .syncdata(ctu_dll2_byp_val[4:0]), // Templated
					    // Inputs
					    .cmp_clk(cmp_clk),
					    .coin_edge(coin_edge),
					    .arst_l(io_pwron_rst_l), // Templated
					    .presyncdata(ctu_dll2_byp_val_jl[4:0])); // Templated
    ctu_synch_jl_dl #(5) u_ctu_dll3_byp_val(
				            .jbus_rx_sync(jbus_rx_sync_gated), 
                                            /*AUTOINST*/
					    // Outputs
					    .syncdata(ctu_dll3_byp_val[4:0]), // Templated
					    // Inputs
					    .cmp_clk(cmp_clk),
					    .coin_edge(coin_edge),
					    .arst_l(io_pwron_rst_l), // Templated
					    .presyncdata(ctu_dll3_byp_val_jl[4:0])); // Templated

 /*  ctu_synch_cl_dl AUTO_TEMPLATE (
       .presyncdata(ctu_ddr@_cken_cl),
       .syncdata (ctu_ddr@_dram_cken_dl),
       .ctu_dram_tx_sync_early(ctu_dram_tx_sync_early),
    );
  */
    ctu_synch_cl_dl u_ctu_ddr0_dram_cken (/*AUTOINST*/
					  // Outputs
					  .syncdata(ctu_ddr0_dram_cken_dl), // Templated
					  // Inputs
					  .cmp_clk(cmp_clk),
					  .ctu_dram_tx_sync_early(ctu_dram_tx_sync_early), // Templated
					  .presyncdata(ctu_ddr0_cken_cl)); // Templated
    ctu_synch_cl_dl u_ctu_ddr1_dram_cken (/*AUTOINST*/
					  // Outputs
					  .syncdata(ctu_ddr1_dram_cken_dl), // Templated
					  // Inputs
					  .cmp_clk(cmp_clk),
					  .ctu_dram_tx_sync_early(ctu_dram_tx_sync_early), // Templated
					  .presyncdata(ctu_ddr1_cken_cl)); // Templated
    ctu_synch_cl_dl u_ctu_ddr2_dram_cken (/*AUTOINST*/
					  // Outputs
					  .syncdata(ctu_ddr2_dram_cken_dl), // Templated
					  // Inputs
					  .cmp_clk(cmp_clk),
					  .ctu_dram_tx_sync_early(ctu_dram_tx_sync_early), // Templated
					  .presyncdata(ctu_ddr2_cken_cl)); // Templated
    ctu_synch_cl_dl u_ctu_ddr3_dram_cken (/*AUTOINST*/
					  // Outputs
					  .syncdata(ctu_ddr3_dram_cken_dl), // Templated
					  // Inputs
					  .cmp_clk(cmp_clk),
					  .ctu_dram_tx_sync_early(ctu_dram_tx_sync_early), // Templated
					  .presyncdata(ctu_ddr3_cken_cl)); // Templated



   /*  ctu_synch_jl_dl AUTO_TEMPLATE (
       .presyncdata(ctu_ddr@_iodll_rst_jl_l),
       .syncdata (ctu_ddr@_iodll_rst_l),
       .arst_l(io_pwron_rst_l),
    );
  */
      ctu_synch_jl_dl u_ctu_ddr0_iodll_rst_dl_l( 
						 .jbus_rx_sync(jbus_rx_sync_gated),
                                                 /*AUTOINST*/
						// Outputs
						.syncdata(ctu_ddr0_iodll_rst_l), // Templated
						// Inputs
						.cmp_clk(cmp_clk),
						.coin_edge(coin_edge),
						.arst_l(io_pwron_rst_l), // Templated
						.presyncdata(ctu_ddr0_iodll_rst_jl_l)); // Templated
      ctu_synch_jl_dl u_ctu_ddr1_iodll_rst_dl_l( 
						 .jbus_rx_sync(jbus_rx_sync_gated),
                                                 /*AUTOINST*/
						// Outputs
						.syncdata(ctu_ddr1_iodll_rst_l), // Templated
						// Inputs
						.cmp_clk(cmp_clk),
						.coin_edge(coin_edge),
						.arst_l(io_pwron_rst_l), // Templated
						.presyncdata(ctu_ddr1_iodll_rst_jl_l)); // Templated
      ctu_synch_jl_dl u_ctu_ddr2_iodll_rst_dl_l(
						 .jbus_rx_sync(jbus_rx_sync_gated),
                                                 /*AUTOINST*/
						// Outputs
						.syncdata(ctu_ddr2_iodll_rst_l), // Templated
						// Inputs
						.cmp_clk(cmp_clk),
						.coin_edge(coin_edge),
						.arst_l(io_pwron_rst_l), // Templated
						.presyncdata(ctu_ddr2_iodll_rst_jl_l)); // Templated
      ctu_synch_jl_dl u_ctu_ddr3_iodll_rst_dl_l( 
						 .jbus_rx_sync(jbus_rx_sync_gated),
                                                 /*AUTOINST*/
						// Outputs
						.syncdata(ctu_ddr3_iodll_rst_l), // Templated
						// Inputs
						.cmp_clk(cmp_clk),
						.coin_edge(coin_edge),
						.arst_l(io_pwron_rst_l), // Templated
						.presyncdata(ctu_ddr3_iodll_rst_jl_l)); // Templated





endmodule // ctu_clsp_jl_dl


// Local Variables:
// verilog-library-directories:("." "../common/rtl")
// verilog-library-files:("../common/rtl/ctu_lib.v" "../../common/rtl/swrvr_clib.v")
// verilog-auto-sense-defines-constant:t
// End:








