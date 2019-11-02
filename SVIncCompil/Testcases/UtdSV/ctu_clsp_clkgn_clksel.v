// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: ctu_clsp_clkgn_clksel.v
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

module ctu_clsp_clkgn_clksel(/*AUTOARG*/
// Outputs
clkout, sysclk_sel, 
// Inputs
io_pwron_rst_l, sel, testmode_l, sysclk, divbypclk, byp_mult_sel_l, 
nstepsel, jtag_clock_dr, capture_l, bypmode
);

input io_pwron_rst_l;
input [2:0] sel;
input testmode_l;
input sysclk;
input divbypclk;
input byp_mult_sel_l;
input nstepsel;
input jtag_clock_dr;
input capture_l;
input bypmode;

output clkout;
output sysclk_sel;

wire force_altclk_l;
wire altclk_sync_l;
wire tck_sync;
wire bypclk_sync_pre;
wire bypclk_sync;
wire tck_sync_pre;
wire force_alt_clk_sync;
wire mult_sel;

wire nstep_clock_dr;
wire clock_dr;
wire altclk_sync_l_bar;
wire sysclk_sel_bar;


   // -----------------------------------------------
   //
   //  N-step and jtag_clock_dr mode
   //  When dft_clsp_capture_l is asserted, nstep goes through,
   //  otherwise jtag_clock_dr goes through. 
   //  jtag_clock_dr can be dft_jtag_clock_dr (from dft) or j_clk/io_tck2
   //  if dft_clsp_parallel_scan is asserted
   //
   // -----------------------------------------------
   // Clock gating
   // capture cycle:
   // capture_l is low, let nstep clock through
   // assign nstep_clock_dr = jtag_clock_dr & capture_l;
   // capture_l changes value on neg edge of tck

 
      ctu_and2 u_capture_l_gated (.a (jtag_clock_dr), .b(capture_l), .z(nstep_clock_dr));


      // nstep_clock_dr is undefined in ctu pin base parallel scan  mode

      ctu_mux21 u_jtag_clock_mux_gated( .z(clock_dr), .s(testmode_l), .d0(jtag_clock_dr), 
                                                                      .d1(nstep_clock_dr));

      // Work around Reading macro

       ctu_clksel_async_synchronizer u_mult_sel_clk(
             .presyncdata(mult_sel),
             .syncdata (force_alt_clk_sync),
             .arst_l(io_pwron_rst_l),
             .aset_l(1'b1),
             .clk (sysclk)
                );

       ctu_clksel_async_synchronizer u_byp_mult_sel_sync(
             .presyncdata(altclk_sync_pre),
             .syncdata (altclk_sync_l),
             .arst_l(io_pwron_rst_l),
             .aset_l(1'b1),
             .clk (divbypclk)
                );
       ctu_clksel_async_synchronizer u_bypclk_sync(
             .presyncdata(bypclk_sync_pre),
             .syncdata (bypclk_sync),
             .aset_l(io_pwron_rst_l),
             .arst_l(1'b1),
             .clk(divbypclk)
              );
       ctu_clksel_async_synchronizer u_tck_sync(
             .presyncdata(tck_sync_pre),
             .syncdata (tck_sync),
             .arst_l(io_pwron_rst_l),
             .aset_l(1'b1),
             .clk(jtag_clock_dr)
              );

       assign mult_sel = bypmode | nstepsel;
       assign force_altclk_l =  sel[0];
       assign altclk_sync_pre =  byp_mult_sel_l;
       assign bypclk_sync_pre = sel[2] ;
       assign tck_sync_pre =  sel[1];

       bw_u1_aoi22_4x u_clkout_gated ( .a1(bypclk_sync), .a2(divbypclk),
                                       .b1(tck_sync),.b2(clock_dr), .z(clkout));

       ctu_inv u_altclk_sync_l_gated (.z(altclk_sync_l_bar), .a(altclk_sync_l));
       bw_u1_oai21_4x  u_sysclk_sel_bar_gated (.a  (altclk_sync_l_bar),
                                               .b1 (force_altclk_l),
                                               .b2 (force_alt_clk_sync),
                                               .z (sysclk_sel_bar));
       ctu_inv u_sysclk_sel_gated (.z(sysclk_sel), .a(sysclk_sel_bar));

endmodule
// Local Variables:
// verilog-library-directories:("." "../../common/rtl")
// verilog-library-files:      ("../../common/rtl/swrvr_clib.v")
// verilog-auto-sense-defines-constant:t
// End:
