// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_slow_rptr.v
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
module sctag_slow_rptr(/*AUTOARG*/
   // Outputs
   areset_l_0_buf, areset_l_1_buf, greset_l_0_buf, greset_l_1_buf, 
   scan_enable_0_buf, scan_enable_1_buf, sehold_0_buf, sehold_1_buf, 
   mux_drive_disable_0_buf, mux_drive_disable_1_buf, 
   mem_write_disable_0_buf, mem_write_disable_1_buf, sig0_buf, 
   sig1_buf, sig2_buf, sig3_buf, 
   // Inputs
   areset_l_0, areset_l_1, greset_l_0, greset_l_1, scan_enable_0, 
   scan_enable_1, sehold_0, sehold_1, mux_drive_disable_0, 
   mux_drive_disable_1, mem_write_disable_0, mem_write_disable_1, 
   sig0, sig1, sig2, sig3
   );


input	areset_l_0;
input	areset_l_1;
input	greset_l_0;
input	greset_l_1;
input	scan_enable_0;
input	scan_enable_1;
input	sehold_0;
input	sehold_1;
input	mux_drive_disable_0;
input	mux_drive_disable_1;
input	mem_write_disable_0;
input	mem_write_disable_1;
input	sig0;
input	sig1;
input	sig2;
input	sig3;

output	areset_l_0_buf;
output	areset_l_1_buf;
output	greset_l_0_buf;
output	greset_l_1_buf;
output	scan_enable_0_buf;
output	scan_enable_1_buf;
output	sehold_0_buf;
output	sehold_1_buf;
output	mux_drive_disable_0_buf;
output	mux_drive_disable_1_buf;
output	mem_write_disable_0_buf;
output	mem_write_disable_1_buf;
output	sig0_buf;
output	sig1_buf;
output	sig2_buf;
output	sig3_buf;


assign	areset_l_0_buf=areset_l_0;
assign	areset_l_1_buf=areset_l_1;
assign	greset_l_0_buf=greset_l_0;
assign	greset_l_1_buf=greset_l_1;
assign	scan_enable_0_buf=scan_enable_0;
assign	scan_enable_1_buf=scan_enable_1;
assign	sehold_0_buf=sehold_0;
assign	sehold_1_buf=sehold_1;
assign	mux_drive_disable_0_buf=mux_drive_disable_0;
assign	mux_drive_disable_1_buf=mux_drive_disable_1;
assign	mem_write_disable_0_buf=mem_write_disable_0;
assign	mem_write_disable_1_buf=mem_write_disable_1;
assign	sig0_buf=sig0;
assign	sig1_buf=sig1;
assign	sig2_buf=sig2;
assign	sig3_buf=sig3;





endmodule
