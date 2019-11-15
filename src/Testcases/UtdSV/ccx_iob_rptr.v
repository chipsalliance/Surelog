// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: ccx_iob_rptr.v
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
module ccx_iob_rptr (/*AUTOARG*/
   // Outputs
   sig_buf, 
   // Inputs
   sig
   );

// This repeater has 136 bits
output	[135:0]	 sig_buf;
input	[135:0]	 sig;


assign	sig_buf = sig;



endmodule
