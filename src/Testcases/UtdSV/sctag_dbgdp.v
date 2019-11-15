// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_dbgdp.v
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
`include	"sctag.h"


module sctag_dbgdp (/*AUTOARG*/
   // Outputs
   so, sctag_dbgbus_out, 
   // Inputs
   arbdp_dbg_addr_c3, arbdec_dbgdp_inst_c3, arbctl_dbgdp_inst_vld_c3, 
   l2_dbg_en, rclk, si, se
   );

output	so;


input	[29:0]	arbdp_dbg_addr_c3 ;	
input	[8:0]	arbdec_dbgdp_inst_c3 ;
input		arbctl_dbgdp_inst_vld_c3;
input		l2_dbg_en ;
input	rclk, si, se;


output	[40:0]	sctag_dbgbus_out;


wire	[40:0] 	dbgbus_c3 ;



// MSB is the mux select 
assign	dbgbus_c3 = { l2_dbg_en , 
			arbctl_dbgdp_inst_vld_c3, 
			arbdec_dbgdp_inst_c3,
			arbdp_dbg_addr_c3 };


dff_s     #(41)    ff_sctag_dbgbus_out   (.din(dbgbus_c3[40:0]), .clk(rclk),
                .q(sctag_dbgbus_out[40:0]), .se(se), .si(), .so());

endmodule

