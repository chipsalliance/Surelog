// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: ctu_clsp_clkgn_clksw.v
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
//    Unit Name: ctu_clsp_clkgn_clksel
//
//-----------------------------------------------------------------------------
`include "sys.h"

module ctu_clsp_clkgn_clksw(/*AUTOARG*/
// Outputs
cmp_tst_clk, cmp_clk_sel, dram_tst_clk, dram_clk_sel, jbus_tst_clk, 
jbus_clk_sel, 
// Inputs
io_pwron_rst_l, jtag_clock_dr_cmp, jtag_clock_dr_jbus, 
jtag_clock_dr_dram, capture_l, jtag_clsp_sel_cpu, jtag_clsp_sel_dram, 
jtag_clsp_sel_jbus, jbus_alt_bypsel_l,  
cmp_div_bypass, cmp_gclk_bypass, jbus_div_bypass, jbus_gclk_bypass, 
dram_gclk_bypass, testmode_l, cmp_nstep_sel, jbus_nstep_sel, 
dram_nstep_sel
);


input io_pwron_rst_l;
input jtag_clock_dr_cmp;   
input jtag_clock_dr_jbus;   
input jtag_clock_dr_dram;   
input capture_l;

input [2:0] jtag_clsp_sel_cpu;
input [2:0] jtag_clsp_sel_dram;
input [2:0] jtag_clsp_sel_jbus;
input jbus_alt_bypsel_l;

input cmp_div_bypass;
input cmp_gclk_bypass;
input jbus_div_bypass;
input jbus_gclk_bypass;
input dram_gclk_bypass;
input testmode_l;

input cmp_nstep_sel;
input jbus_nstep_sel;
input dram_nstep_sel;

output cmp_tst_clk;    // to sync mux
output cmp_clk_sel;    // to sync mux

output dram_tst_clk;
output dram_clk_sel;

output jbus_tst_clk;
output jbus_clk_sel;         




/* ctu_clsp_clkgn_clksel AUTO_TEMPLATE (
          .sel (jtag_clsp_sel_cpu[2:0]),
          .sysclk(cmp_gclk_bypass),
          .divbypclk(cmp_div_bypass),
          .clkout(cmp_tst_clk),
          .sysclk_sel(cmp_clk_sel),
          .nstepsel(cmp_nstep_sel),
          .jtag_clock_dr(jtag_clock_dr_cmp),
          .byp_mult_sel_l(1'b0),
          .bypmode(1'b0),
      );
*/

   ctu_clsp_clkgn_clksel u_cmp(/*AUTOINST*/
			       // Outputs
			       .clkout	(cmp_tst_clk),		 // Templated
			       .sysclk_sel(cmp_clk_sel),	 // Templated
			       // Inputs
			       .io_pwron_rst_l(io_pwron_rst_l),
			       .sel	(jtag_clsp_sel_cpu[2:0]), // Templated
			       .testmode_l(testmode_l),
			       .sysclk	(cmp_gclk_bypass),	 // Templated
			       .divbypclk(cmp_div_bypass),	 // Templated
			       .byp_mult_sel_l(1'b0), // Templated
			       .nstepsel(cmp_nstep_sel),	 // Templated
			       .jtag_clock_dr(jtag_clock_dr_cmp), // Templated
			       .capture_l(capture_l),
			       .bypmode	(1'b0));			 // Templated


/* ctu_clsp_clkgn_clksel AUTO_TEMPLATE (
          .sel (jtag_clsp_sel_jbus[2:0]),
          .sysclk(jbus_gclk_bypass),
          .divbypclk(jbus_div_bypass),
          .clkout(jbus_tst_clk),
          .sysclk_sel(jbus_clk_sel),
          .nstepsel(jbus_nstep_sel),
          .jtag_clock_dr(jtag_clock_dr_jbus),
          .byp_mult_sel_l(jbus_alt_bypsel_l),
          .bypmode(jtag_clsp_sel_jbus[2]),
      );
*/
   
   ctu_clsp_clkgn_clksel u_jbus(/*AUTOINST*/
				// Outputs
				.clkout	(jbus_tst_clk),		 // Templated
				.sysclk_sel(jbus_clk_sel),	 // Templated
				// Inputs
				.io_pwron_rst_l(io_pwron_rst_l),
				.sel	(jtag_clsp_sel_jbus[2:0]), // Templated
				.testmode_l(testmode_l),
				.sysclk	(jbus_gclk_bypass),	 // Templated
				.divbypclk(jbus_div_bypass),	 // Templated
				.byp_mult_sel_l(jbus_alt_bypsel_l), // Templated
				.nstepsel(jbus_nstep_sel),	 // Templated
				.jtag_clock_dr(jtag_clock_dr_jbus), // Templated
				.capture_l(capture_l),
				.bypmode(jtag_clsp_sel_jbus[2])); // Templated


/* ctu_clsp_clkgn_clksel AUTO_TEMPLATE (
          .sel (jtag_clsp_sel_dram[2:0]),
          .sysclk(dram_gclk_bypass),
          .divbypclk(1'b0),
          .clkout(dram_tst_clk),
          .sysclk_sel(dram_clk_sel),
          .nstepsel(dram_nstep_sel),
          .jtag_clock_dr(jtag_clock_dr_dram),
          .byp_mult_sel_l(1'b1),
          .bypmode(1'b0),
      );
*/

    ctu_clsp_clkgn_clksel u_dram (/*AUTOINST*/
				  // Outputs
				  .clkout(dram_tst_clk),	 // Templated
				  .sysclk_sel(dram_clk_sel),	 // Templated
				  // Inputs
				  .io_pwron_rst_l(io_pwron_rst_l),
				  .sel	(jtag_clsp_sel_dram[2:0]), // Templated
				  .testmode_l(testmode_l),
				  .sysclk(dram_gclk_bypass),	 // Templated
				  .divbypclk(1'b0),		 // Templated
				  .byp_mult_sel_l(1'b1),	 // Templated
				  .nstepsel(dram_nstep_sel),	 // Templated
				  .jtag_clock_dr(jtag_clock_dr_dram), // Templated
				  .capture_l(capture_l),
				  .bypmode(1'b0));		 // Templated




endmodule
// Local Variables:
// verilog-library-directories:("." "../../common/rtl")
// verilog-library-files:("../common/rtl/ctu_lib.v" "../../common/rtl/swrvr_clib.v")
// verilog-auto-sense-defines-constant:t
// End:
