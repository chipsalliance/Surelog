// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_scbufrep.v
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
module sctag_scbufrep(/*AUTOARG*/
   // Outputs
   sctag_scbuf_stdecc_c3, so, 
   // Inputs
   rep_store_data_c2, rclk, si, se
   );


output  [77:0]  sctag_scbuf_stdecc_c3;
output		so;

input   [77:0] 	rep_store_data_c2;
input		rclk;
input		si, se;



dff_s   #(78) ff_stdata_c3
              (.q   (sctag_scbuf_stdecc_c3[77:0]),
               .din (rep_store_data_c2[77:0]),
               .clk (rclk),
               .se  (se), .si  (), .so  ()
              ) ;


endmodule
