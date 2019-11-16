// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: scbuf_slowsig_buf.v
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
module scbuf_slowsig_buf
 (// Outputs
  mem_write_disable_buf,
  sehold_buf,
  se_buf,
  arst_l_buf,

  // Inputs
  mem_write_disable,
  sehold,
  se,
  arst_l
 );


output    mem_write_disable_buf;
output    sehold_buf;
output    se_buf;
output    arst_l_buf;

input     mem_write_disable;
input     sehold;
input     se;
input     arst_l;


assign  mem_write_disable_buf = mem_write_disable;
assign  sehold_buf            = sehold;
assign  se_buf                = se;
assign  arst_l_buf            = arst_l;


endmodule
