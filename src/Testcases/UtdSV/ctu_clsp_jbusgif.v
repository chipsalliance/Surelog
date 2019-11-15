// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: ctu_clsp_jbusgif.v
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

module ctu_clsp_jbusgif(/*AUTOARG*/
// Outputs
ctu_dram02_jbus_cken, ctu_dram13_jbus_cken, ctu_jbi_jbus_cken, 
ctu_iob_jbus_cken, ctu_jbusl_jbus_cken, ctu_jbusr_jbus_cken, 
ctu_misc_jbus_cken, ctu_efc_jbus_cken, ctu_dbg_jbus_cken, 
jbus_grst_out_l, jbus_arst_l, jbus_gdbginit_out_l, jbus_adbginit_l, 
// Inputs
io_pwron_rst_l, start_clk_jl, testmode_l, jbus_gclk, jbus_grst_jl_l, 
jbus_dbginit_jl_l, ctu_dram02_cken_jl, ctu_dram13_cken_jl, 
ctu_iob_cken_jl, ctu_efc_cken_jl, ctu_dbg_cken_jl, ctu_jbusl_cken_jl, 
ctu_jbusr_cken_jl, ctu_jbi_cken_jl, ctu_misc_cken_jl, 
jtag_clsp_force_cken_jbus
);

   input      io_pwron_rst_l;
   input      start_clk_jl;
   input      testmode_l;
   input      jbus_gclk;
  
   input      jbus_grst_jl_l;
   input      jbus_dbginit_jl_l;

   input      ctu_dram02_cken_jl;
   input      ctu_dram13_cken_jl;
   input      ctu_iob_cken_jl;   
   input      ctu_efc_cken_jl;
   input      ctu_dbg_cken_jl;
   input      ctu_jbusl_cken_jl;
   input      ctu_jbusr_cken_jl;
   input      ctu_jbi_cken_jl;
   input      ctu_misc_cken_jl;
   input      jtag_clsp_force_cken_jbus;



   output      ctu_dram02_jbus_cken;
   output      ctu_dram13_jbus_cken;
   output      ctu_jbi_jbus_cken;
   output      ctu_iob_jbus_cken;
   output      ctu_jbusl_jbus_cken;
   output      ctu_jbusr_jbus_cken;
   output      ctu_misc_jbus_cken;
   output      ctu_efc_jbus_cken;
   output      ctu_dbg_jbus_cken;
   
  
   output      jbus_grst_out_l;
   output      jbus_arst_l;
   output      jbus_gdbginit_out_l;         
   output      jbus_adbginit_l;       

   wire      ctu_dram02_cken_muxed;
   wire      ctu_dram13_cken_muxed;
   wire      ctu_iob_cken_muxed;   
   wire      ctu_efc_cken_muxed;
   wire      ctu_dbg_cken_muxed;
   wire      ctu_jbusl_cken_muxed;
   wire      ctu_jbusr_cken_muxed;
   wire      ctu_jbi_cken_muxed;
   wire      ctu_misc_cken_muxed;
   wire      force_cken;

// -----------------------------------------
// 
//  Global signals
// 
// -----------------------------------------

// The following flops needs to be non-scanable:

   assign  jbus_arst_l = io_pwron_rst_l ;
   assign  jbus_adbginit_l = io_pwron_rst_l ;


   dffrl_async_ns    u_dram_dbginit_l(
			   .din (jbus_dbginit_jl_l & start_clk_jl),
			   .clk (jbus_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (jbus_gdbginit_out_l));


   dffrl_async_ns    u_jbus_grst_l(
			   .din (jbus_grst_jl_l & start_clk_jl),
			   .clk (jbus_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (jbus_grst_out_l));




   // Gated cken with testmode_l

   assign force_cken = jtag_clsp_force_cken_jbus | ~testmode_l;


   assign ctu_dram02_cken_muxed = force_cken ? 1'b1:  (ctu_dram02_cken_jl & start_clk_jl);
   assign ctu_dram13_cken_muxed = force_cken ? 1'b1:  (ctu_dram13_cken_jl & start_clk_jl);
   assign ctu_iob_cken_muxed = force_cken ? 1'b1: (ctu_iob_cken_jl  & start_clk_jl);
   assign ctu_jbi_cken_muxed = force_cken ? 1'b1: (ctu_jbi_cken_jl  & start_clk_jl);
   assign ctu_efc_cken_muxed = force_cken ? 1'b1: (ctu_efc_cken_jl & start_clk_jl);

   assign ctu_jbusr_cken_muxed = force_cken? 1'b1:  ((start_clk_jl & ctu_jbusr_cken_jl)  | ~start_clk_jl);
   assign ctu_jbusl_cken_muxed = force_cken?  1'b1: ((start_clk_jl & ctu_jbusl_cken_jl) | ~start_clk_jl);
   assign ctu_dbg_cken_muxed = force_cken ? 1'b1:   ((start_clk_jl & ctu_dbg_cken_jl) | ~start_clk_jl);
   assign ctu_misc_cken_muxed = force_cken? 1'b1:   ((start_clk_jl & ctu_misc_cken_jl) | ~start_clk_jl);

   dffrl_async_ns    u_ctu_dram02_jbus_cken_nsr(
              .din (ctu_dram02_cken_muxed),
              .clk (jbus_gclk),
              .rst_l (io_pwron_rst_l),
              .q (ctu_dram02_jbus_cken));

   dffrl_async_ns    u_ctu_dram13_jbus_cken_nsr(
              .din (ctu_dram13_cken_muxed),
              .clk (jbus_gclk),
              .rst_l (io_pwron_rst_l),
              .q (ctu_dram13_jbus_cken));

   dffrl_async_ns    u_ctu_iob_cken_muxed_nsr(
              .din (ctu_iob_cken_muxed),
              .clk (jbus_gclk),
              .rst_l (io_pwron_rst_l),
              .q (ctu_iob_jbus_cken));

   dffrl_async_ns    u_ctu_jbi_cken_muxed_nsr(
              .din (ctu_jbi_cken_muxed),
              .clk (jbus_gclk),
              .rst_l (io_pwron_rst_l),
              .q (ctu_jbi_jbus_cken));

   dffsl_async_ns    u_ctu_jbusr_cken_muxed_nsr(
              .din (ctu_jbusr_cken_muxed),
              .clk (jbus_gclk),
              .set_l (io_pwron_rst_l),
              .q (ctu_jbusr_jbus_cken));

   dffsl_async_ns    u_ctu_jbusl_cken_muxed_nsr(
              .din (ctu_jbusl_cken_muxed),
              .clk (jbus_gclk),
              .set_l (io_pwron_rst_l),
              .q (ctu_jbusl_jbus_cken));

   dffrl_async_ns    u_ctu_efc_cken_muxed_nsr(
              .din (ctu_efc_cken_muxed),
              .clk (jbus_gclk),
              .rst_l (io_pwron_rst_l),
              .q (ctu_efc_jbus_cken));

   dffsl_async_ns    u_ctu_dbg_cken_muxed_nsr(
              .din (ctu_dbg_cken_muxed),
              .clk (jbus_gclk),
              .set_l (io_pwron_rst_l),
              .q (ctu_dbg_jbus_cken));

   dffsl_async_ns    u_ctu_misc_cken_muxed_nsr(
              .din (ctu_misc_cken_muxed),
              .clk (jbus_gclk),
              .set_l (io_pwron_rst_l),
              .q (ctu_misc_jbus_cken));




endmodule // jbus_f









