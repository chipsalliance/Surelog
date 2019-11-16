// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: bw_zzctu_sync.v
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
//    Unit Name: ctu_clsp
//
//-----------------------------------------------------------------------------


module bw_zzctu_sync (/*AUTOARG*/
// Outputs
so, out, sob,
// Inputs
d, si, sib, pll_out, pll_out_l, se
);


input d;
input si;
input sib;
input pll_out;
input pll_out_l;
input se;
output so;
output sob;
output out;

wire ql1, ql2;
wire so1, so2;
wire pll_out_inv;


    assign pll_out_inv = ~pll_out;

 /* bw_u1_soffi_4x AUTO_TEMPLATE (
          .q_l(ql1),
          .d(d),
          .ck(pll_out),
          .sd(si),
          .so(so1),
      );
*/
     bw_u1_soffi_4x u_I0(/*AUTOINST*/
			 // Outputs
			 .q_l		(ql1),			 // Templated
			 .so		(so),			 // Templated
			 // Inputs
			 .ck		(pll_out),		 // Templated
			 .d		(d),			 // Templated
			 .se		(se),
			 .sd		(si));			 // Templated

 /* bw_u1_soffi_4x AUTO_TEMPLATE (
          .q_l(ql2),
          .d(ql1),
          .ck(pll_out_inv),
          .sd(so1),
          .so(so2),
      );

*/
     bw_u1_soffi_4x u_I1(/*AUTOINST*/
			 // Outputs
			 .q_l		(ql2),			 // Templated
			 .so		(sob1),			 // Templated
			 // Inputs
			 .ck		(pll_out_inv),		 // Templated
			 .d		(ql1),			 // Templated
			 .se		(se),
			 .sd		(sib));			 // Templated

 /* bw_u1_soff_8x AUTO_TEMPLATE (
          .q(out),
          .d(ql2),
          .ck(pll_out_l),
          .sd(so2),
          .so(so),
      );

*/

     bw_u1_soff_8x u_I2(/*AUTOINST*/
			// Outputs
			.q		(out),			 // Templated
			.so		(sob ),			 // Templated
			// Inputs
			.ck		(pll_out_l),		 // Templated
			.d		(ql2),			 // Templated
			.se		(se),
			.sd		(sob1));			 // Templated


endmodule

// Local Variables:
// verilog-library-directories:(".")
// verilog-library-files:("../../../common/rtl/u1.behV")
// verilog-auto-sense-defines-constant:t
// End:



