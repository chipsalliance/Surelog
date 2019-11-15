// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: ctu_clsp_cmpgif.v
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

module ctu_clsp_cmpgif(/*AUTOARG*/
// Outputs
cmp_grst_out_l, cmp_arst_l, cmp_gdbginit_out_l, cmp_adbginit_l, 
ctu_dram_tx_sync_out, ctu_dram_rx_sync_out, ctu_jbus_tx_sync_out, 
ctu_jbus_rx_sync_out, ctu_ccx_cmp_cken, ctu_dram02_cmp_cken, 
ctu_dram13_cmp_cken, ctu_fpu_cmp_cken, ctu_iob_cmp_cken, 
ctu_jbi_cmp_cken, ctu_scdata0_cmp_cken, ctu_scdata1_cmp_cken, 
ctu_scdata2_cmp_cken, ctu_scdata3_cmp_cken, ctu_sctag0_cmp_cken, 
ctu_sctag1_cmp_cken, ctu_sctag2_cmp_cken, ctu_sctag3_cmp_cken, 
ctu_sparc0_cmp_cken, ctu_sparc1_cmp_cken, ctu_sparc2_cmp_cken, 
ctu_sparc3_cmp_cken, ctu_sparc4_cmp_cken, ctu_sparc5_cmp_cken, 
ctu_sparc6_cmp_cken, ctu_sparc7_cmp_cken, 
// Inputs
io_pwron_rst_l, cmp_gclk, start_clk_cl, cmp_grst_cl_l, 
cmp_dbginit_cl_l, ctu_dram_tx_sync_cl, ctu_dram_rx_sync_cl, 
ctu_jbus_tx_sync_cl, ctu_jbus_rx_sync_cl, ctu_ccx_cmp_cken_cg, 
ctu_dram02_cmp_cken_cg, ctu_dram13_cmp_cken_cg, ctu_fpu_cmp_cken_cg, 
ctu_iob_cmp_cken_cg, ctu_jbi_cmp_cken_cg, ctu_scdata0_cmp_cken_cg, 
ctu_scdata1_cmp_cken_cg, ctu_scdata2_cmp_cken_cg, 
ctu_scdata3_cmp_cken_cg, ctu_sctag0_cmp_cken_cg, 
ctu_sctag1_cmp_cken_cg, ctu_sctag2_cmp_cken_cg, 
ctu_sctag3_cmp_cken_cg, ctu_sparc0_cmp_cken_cg, 
ctu_sparc1_cmp_cken_cg, ctu_sparc2_cmp_cken_cg, 
ctu_sparc3_cmp_cken_cg, ctu_sparc4_cmp_cken_cg, 
ctu_sparc5_cmp_cken_cg, ctu_sparc6_cmp_cken_cg, 
ctu_sparc7_cmp_cken_cg
);

   input      io_pwron_rst_l;
   input      cmp_gclk;
   input      start_clk_cl;
  
   input      cmp_grst_cl_l;
   input      cmp_dbginit_cl_l;

   input      ctu_dram_tx_sync_cl;
   input      ctu_dram_rx_sync_cl;
   input      ctu_jbus_tx_sync_cl;
   input      ctu_jbus_rx_sync_cl;
  


   input      ctu_ccx_cmp_cken_cg;
   input      ctu_dram02_cmp_cken_cg;
   input      ctu_dram13_cmp_cken_cg;
   input      ctu_fpu_cmp_cken_cg;      
   input      ctu_iob_cmp_cken_cg; 
   input      ctu_jbi_cmp_cken_cg;
   input      ctu_scdata0_cmp_cken_cg;
   input      ctu_scdata1_cmp_cken_cg;
   input      ctu_scdata2_cmp_cken_cg;
   input      ctu_scdata3_cmp_cken_cg;
   input      ctu_sctag0_cmp_cken_cg;
   input      ctu_sctag1_cmp_cken_cg;
   input      ctu_sctag2_cmp_cken_cg;
   input      ctu_sctag3_cmp_cken_cg;
   input      ctu_sparc0_cmp_cken_cg;
   input      ctu_sparc1_cmp_cken_cg;
   input      ctu_sparc2_cmp_cken_cg;
   input      ctu_sparc3_cmp_cken_cg;
   input      ctu_sparc4_cmp_cken_cg;
   input      ctu_sparc5_cmp_cken_cg;
   input      ctu_sparc6_cmp_cken_cg;
   input      ctu_sparc7_cmp_cken_cg;


   output      cmp_grst_out_l;
   output      cmp_arst_l;
   output      cmp_gdbginit_out_l;         
   output      cmp_adbginit_l;       

   output      ctu_dram_tx_sync_out;
   output      ctu_dram_rx_sync_out;
   output      ctu_jbus_tx_sync_out;
   output      ctu_jbus_rx_sync_out;

   output      ctu_ccx_cmp_cken;
   output      ctu_dram02_cmp_cken;
   output      ctu_dram13_cmp_cken;
   output      ctu_fpu_cmp_cken;      
   output      ctu_iob_cmp_cken; 
   output      ctu_jbi_cmp_cken;
   output      ctu_scdata0_cmp_cken;
   output      ctu_scdata1_cmp_cken;
   output      ctu_scdata2_cmp_cken;
   output      ctu_scdata3_cmp_cken;
   output      ctu_sctag0_cmp_cken;
   output      ctu_sctag1_cmp_cken;
   output      ctu_sctag2_cmp_cken;
   output      ctu_sctag3_cmp_cken;
   output      ctu_sparc0_cmp_cken;
   output      ctu_sparc1_cmp_cken;
   output      ctu_sparc2_cmp_cken;
   output      ctu_sparc3_cmp_cken;
   output      ctu_sparc4_cmp_cken;
   output      ctu_sparc5_cmp_cken;
   output      ctu_sparc6_cmp_cken;
   output      ctu_sparc7_cmp_cken;

   wire        start_clk_cg;

// -----------------------------------------
// 
//  Global signals
// 
// -----------------------------------------


   assign  cmp_arst_l = io_pwron_rst_l ;
   assign  cmp_adbginit_l = io_pwron_rst_l ;

   dffrl_async_ns    u_start_clk_cg(
			   .din (start_clk_cl),
			   .clk (cmp_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (start_clk_cg));

   dffrl_async_ns    u_cmp_grst_l(
			   .din (cmp_grst_cl_l & start_clk_cg),
			   .clk (cmp_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (cmp_grst_out_l));

   dffrl_async_ns    u_cmp_dbginit_l(
			   .din (cmp_dbginit_cl_l & start_clk_cg),
			   .clk (cmp_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (cmp_gdbginit_out_l));

   dffrl_async_ns    u_ctu_dram_rx_sync_cl(
			   .din (ctu_dram_rx_sync_cl),
			   .clk (cmp_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (ctu_dram_rx_sync_out));

   dffrl_async_ns    u_ctu_dram_tx_sync_cl(
			   .din (ctu_dram_tx_sync_cl),
			   .clk (cmp_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (ctu_dram_tx_sync_out));

   dffrl_async_ns    u_ctu_jbus_rx_sync_cl(
			   .din (ctu_jbus_rx_sync_cl),
			   .clk (cmp_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (ctu_jbus_rx_sync_out));

   dffrl_async_ns    u_ctu_jbus_tx_sync_cl(
			   .din (ctu_jbus_tx_sync_cl),
			   .clk (cmp_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (ctu_jbus_tx_sync_out));


   dffrl_async_ns    u_ctu_sparc0_cmp_cken_nsr(
			   .din (ctu_sparc0_cmp_cken_cg),
			   .clk (cmp_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (ctu_sparc0_cmp_cken));
   dffrl_async_ns    u_ctu_sparc1_cmp_cken_nsr(
			   .din (ctu_sparc1_cmp_cken_cg),
			   .clk (cmp_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (ctu_sparc1_cmp_cken));
   dffrl_async_ns    u_ctu_sparc2_cmp_cken_nsr(
			   .din (ctu_sparc2_cmp_cken_cg),
			   .clk (cmp_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (ctu_sparc2_cmp_cken));
   dffrl_async_ns    u_ctu_sparc3_cmp_cken_nsr(
			   .din (ctu_sparc3_cmp_cken_cg),
			   .clk (cmp_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (ctu_sparc3_cmp_cken));
   dffrl_async_ns    u_ctu_sparc4_cmp_cken_nsr(
			   .din (ctu_sparc4_cmp_cken_cg),
			   .clk (cmp_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (ctu_sparc4_cmp_cken));
   dffrl_async_ns    u_ctu_sparc5_cmp_cken_nsr(
			   .din (ctu_sparc5_cmp_cken_cg),
			   .clk (cmp_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (ctu_sparc5_cmp_cken));
   dffrl_async_ns    u_ctu_sparc6_cmp_cken_nsr(
			   .din (ctu_sparc6_cmp_cken_cg),
			   .clk (cmp_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (ctu_sparc6_cmp_cken));
   dffrl_async_ns    u_ctu_sparc7_cmp_cken_nsr(
			   .din (ctu_sparc7_cmp_cken_cg),
			   .clk (cmp_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (ctu_sparc7_cmp_cken));

   dffrl_async_ns    u_ctu_scdata0_cmp_cken_nsr(
			   .din (ctu_scdata0_cmp_cken_cg),
			   .clk (cmp_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (ctu_scdata0_cmp_cken));
   dffrl_async_ns    u_ctu_scdata1_cmp_cken_nsr(
			   .din (ctu_scdata1_cmp_cken_cg),
			   .clk (cmp_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (ctu_scdata1_cmp_cken));
   dffrl_async_ns    u_ctu_scdata2_cmp_cken_nsr(
			   .din (ctu_scdata2_cmp_cken_cg),
			   .clk (cmp_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (ctu_scdata2_cmp_cken));
   dffrl_async_ns    u_ctu_scdata3_cmp_cken_nsr(
			   .din (ctu_scdata3_cmp_cken_cg),
			   .clk (cmp_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (ctu_scdata3_cmp_cken));

   dffrl_async_ns    u_ctu_sctag0_cmp_cken_nsr(
			   .din (ctu_sctag0_cmp_cken_cg),
			   .clk (cmp_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (ctu_sctag0_cmp_cken));
   dffrl_async_ns    u_ctu_sctag1_cmp_cken_nsr(
			   .din (ctu_sctag1_cmp_cken_cg),
			   .clk (cmp_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (ctu_sctag1_cmp_cken));
   dffrl_async_ns    u_ctu_sctag2_cmp_cken_nsr(
			   .din (ctu_sctag2_cmp_cken_cg),
			   .clk (cmp_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (ctu_sctag2_cmp_cken));
   dffrl_async_ns    u_ctu_sctag3_cmp_cken_nsr(
			   .din (ctu_sctag3_cmp_cken_cg),
			   .clk (cmp_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (ctu_sctag3_cmp_cken));

   dffrl_async_ns    u_ctu_ccx_cmp_cken_nsr(
			   .din (ctu_ccx_cmp_cken_cg),
			   .clk (cmp_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (ctu_ccx_cmp_cken));
   dffrl_async_ns    u_ctu_fpu_cmp_cken_nsr(
			   .din (ctu_fpu_cmp_cken_cg),
			   .clk (cmp_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (ctu_fpu_cmp_cken));
   dffrl_async_ns    u_ctu_iob_cmp_cken_nsr(
			   .din (ctu_iob_cmp_cken_cg),
			   .clk (cmp_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (ctu_iob_cmp_cken));
   dffrl_async_ns    u_ctu_jbi_cmp_cken_nsr(
			   .din (ctu_jbi_cmp_cken_cg),
			   .clk (cmp_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (ctu_jbi_cmp_cken));
   dffrl_async_ns    u_ctu_dram02_cmp_cken_nsr(
			   .din (ctu_dram02_cmp_cken_cg),
			   .clk (cmp_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (ctu_dram02_cmp_cken));
   dffrl_async_ns    u_ctu_dram13_cmp_cken_nsr(
			   .din (ctu_dram13_cmp_cken_cg),
			   .clk (cmp_gclk),
                           .rst_l (io_pwron_rst_l),
			   .q (ctu_dram13_cmp_cken));
endmodule // cmpif




// Local Variables:
// verilog-library-directories:("." "../common/rtl") 
// verilog-auto-sense-defines-constant:t
// End:

