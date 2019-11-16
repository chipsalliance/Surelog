// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: ctu_clsp_clkgn_ssiclk.v
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
//    Unit Name: ctu_clsp_clkgn_nstep
//
//-----------------------------------------------------------------------------
`include "sys.h"

module ctu_clsp_clkgn_ssiclk(/*AUTOARG*/
// Outputs
ctu_jbi_ssiclk, 
// Inputs
io_pwron_rst_l, jbus_clk, ssiclk_enable
);

input io_pwron_rst_l;
input jbus_clk;
input ssiclk_enable;
output ctu_jbi_ssiclk;


   wire jbus_clk_stage1_nxt;
   wire jbus_clk_stage1;
   wire ctu_jbi_ssiclk;


      assign  jbus_clk_stage1_nxt =  jbus_clk_stage1 | ctu_jbi_ssiclk?
                                     ~ctu_jbi_ssiclk : (~ctu_jbi_ssiclk & ssiclk_enable);

      dffrl_async_ns u_ctu_jbi_ssiclk_d1 (
                      .din (jbus_clk_stage1_nxt),
                      .clk (jbus_clk),
                      .rst_l(io_pwron_rst_l),
                      .q(jbus_clk_stage1));
      dffrl_async_ns u_ctu_jbi_ssiclk_d2 (
                      .din (jbus_clk_stage1),
                      .clk (jbus_clk),
                      .rst_l(io_pwron_rst_l),
                      .q(ctu_jbi_ssiclk));


endmodule
// Local Variables:
// verilog-library-directories:("." "../../common/rtl")
// verilog-library-files:      ("../../common/rtl/swrvr_clib.v")
// verilog-auto-sense-defines-constant:t
// End:
