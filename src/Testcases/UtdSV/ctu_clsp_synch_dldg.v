// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: ctu_clsp_synch_dldg.v
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

module ctu_clsp_synch_dldg(/*AUTOARG*/
// Outputs
start_clk_dg, ctu_ddr0_dram_cken_dg, ctu_ddr1_dram_cken_dg, 
ctu_ddr2_dram_cken_dg, ctu_ddr3_dram_cken_dg, 
ctu_dram02_dram_cken_dg, ctu_dram13_dram_cken_dg, a_grst_dg, 
a_dbginit_dg, de_grst_dsync_edge_dg, de_dbginit_dsync_edge_dg, 
// Inputs
io_pwron_rst_l, cmp_gclk, ctu_ddr0_dram_cken_dl, 
ctu_ddr1_dram_cken_dl, ctu_ddr2_dram_cken_dl, ctu_ddr3_dram_cken_dl, 
ctu_dram02_dram_cken_dl, ctu_dram13_dram_cken_dl, start_clk_dl, 
a_grst_dl, a_dbginit_dl, de_grst_dsync_edge_dl, 
de_dbginit_dsync_edge_dl
);

   input      io_pwron_rst_l;
   input      cmp_gclk;

   input ctu_ddr0_dram_cken_dl;
   input ctu_ddr1_dram_cken_dl;
   input ctu_ddr2_dram_cken_dl;
   input ctu_ddr3_dram_cken_dl;
   input ctu_dram02_dram_cken_dl;
   input ctu_dram13_dram_cken_dl;
   input start_clk_dl;
   input a_grst_dl;
   input a_dbginit_dl;
   input de_grst_dsync_edge_dl;
   input de_dbginit_dsync_edge_dl;

   output start_clk_dg;
   output ctu_ddr0_dram_cken_dg;
   output ctu_ddr1_dram_cken_dg;
   output ctu_ddr2_dram_cken_dg;
   output ctu_ddr3_dram_cken_dg;
   output ctu_dram02_dram_cken_dg;
   output ctu_dram13_dram_cken_dg;


   output a_grst_dg;
   output a_dbginit_dg;
   output de_grst_dsync_edge_dg;
   output de_dbginit_dsync_edge_dg;

// -----------------------------------------
// 
//   Signals sync to dram_gclk (clocked on cmp_gclk) first
// 
// -----------------------------------------

     dffrl_async_ns  u_start_clk_dg(
                   .din (start_clk_dl),
                   .clk (cmp_gclk),
                   .rst_l(io_pwron_rst_l),
                   .q (start_clk_dg));

     dff_ns  u_ctu_ddr0_dram_cken_dg(
                   .din (ctu_ddr0_dram_cken_dl),
                   .clk (cmp_gclk),
                   .q (ctu_ddr0_dram_cken_dg));
     dff_ns  u_ctu_ddr1_dram_cken_dg(
                   .din (ctu_ddr1_dram_cken_dl),
                   .clk (cmp_gclk),
                   .q (ctu_ddr1_dram_cken_dg));
     dff_ns  u_ctu_ddr2_dram_cken_dg(
                   .din (ctu_ddr2_dram_cken_dl),
                   .clk (cmp_gclk),
                   .q (ctu_ddr2_dram_cken_dg));

     dff_ns  u_ctu_ddr3_dram_cken_dg(
                   .din (ctu_ddr3_dram_cken_dl),
                   .clk (cmp_gclk),
                   .q (ctu_ddr3_dram_cken_dg));

     dff_ns  u_ctu_dram02_dram_cken_dg(
                   .din (ctu_dram02_dram_cken_dl),
                   .clk (cmp_gclk),
                   .q (ctu_dram02_dram_cken_dg));

     dff_ns  u_ctu_dram13_dram_cken_dg(
                   .din (ctu_dram13_dram_cken_dl),
                   .clk (cmp_gclk),
                   .q (ctu_dram13_dram_cken_dg));

     dff_ns  u_a_grst_dg(
                   .din (a_grst_dl),
                   .clk (cmp_gclk),
                   .q (a_grst_dg));

     dff_ns  u_a_dbginit_dl(
                   .din (a_dbginit_dl),
                   .clk (cmp_gclk),
                   .q (a_dbginit_dg));

     dff_ns  u_de_grst_dsync_edge_dl(
                   .din (de_grst_dsync_edge_dl),
                   .clk (cmp_gclk),
                   .q (de_grst_dsync_edge_dg));

     dff_ns  u_de_dbginit_dsync_edge_dl(
                   .din (de_dbginit_dsync_edge_dl),
                   .clk (cmp_gclk),
                   .q (de_dbginit_dsync_edge_dg));

endmodule // cmpif




// Local Variables:
// verilog-library-directories:("." "../common/rtl") 
// verilog-auto-sense-defines-constant:t
// End:

