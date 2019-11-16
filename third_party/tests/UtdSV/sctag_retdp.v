// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_retdp.v
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

module sctag_retdp(/*AUTOARG*/
   // Outputs
   retdp_data_c7_buf, retdp_ecc_c7_buf, so, 
   // Inputs
   scdata_sctag_decc_c6, rclk, si, se
   );


output  [127:0]  retdp_data_c7_buf;
output  [ 27:0]  retdp_ecc_c7_buf;
output		so;

input   [155:0]  scdata_sctag_decc_c6;
input		rclk;
input		si, se;


// Output of the L2$ data array.

wire    [127:0]  retdp_data_c6;
wire    [ 27:0]  retdp_ecc_c6;


assign  {retdp_data_c6[31:0],   retdp_ecc_c6[6:0]}   = scdata_sctag_decc_c6[38:0];
assign  {retdp_data_c6[63:32],  retdp_ecc_c6[13:7]}  = scdata_sctag_decc_c6[77:39];
assign  {retdp_data_c6[95:64],  retdp_ecc_c6[20:14]} = scdata_sctag_decc_c6[116:78];
assign  {retdp_data_c6[127:96], retdp_ecc_c6[27:21]} = scdata_sctag_decc_c6[155:117];

// arrange these flops in 16 rows and 10 columns
// row0 ->{ data[2:0],ecc[6:0]}
// row1 ->{ data[12:3]}
// row2 ->{ data[22:13]}
// row3 ->{ data[31:23]}
// and so 0n. Buffer the outputs of each 
// bit with a 40x buffer/inverter.

dff_s   #(128) ff_data_rtn_c7
              (.q   (retdp_data_c7_buf[127:0]),
               .din (retdp_data_c6[127:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

dff_s   #(28)  ff_ecc_rtn_c7
              (.q   (retdp_ecc_c7_buf[27:0]),
               .din (retdp_ecc_c6[27:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;



endmodule
