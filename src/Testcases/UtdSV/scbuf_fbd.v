// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: scbuf_fbd.v
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
`include   "iop.h"


module scbuf_fbd
 (/*AUTOARG*/
   // Outputs
   so, sctag_scbuf_fbrd_en_c3_v1, sctag_scbuf_fbrd_en_c3_v2, 
   sctag_scbuf_fbrd_en_c3_v3, sctag_scbuf_fbrd_en_c3_v4, 
   sctag_scbuf_fbrd_wl_c3_v1, sctag_scbuf_fbrd_wl_c3_v2, 
   sctag_scbuf_fbrd_wl_c3_v3, sctag_scbuf_fbrd_wl_c3_v4, 
   sctag_scbuf_fbwr_wen_r3, sctag_scbuf_fbwr_wren_r3_v4, 
   sctag_scbuf_fbwr_wren_r3_v3, sctag_scbuf_fbwr_wren_r3_v2, 
   sctag_scbuf_fbwr_wren_r3_v1, sctag_scbuf_fbwr_wl_r3_v1, 
   sctag_scbuf_fbwr_wl_r3_v2, sctag_scbuf_fbwr_wl_r3_v3, 
   sctag_scbuf_fbwr_wl_r3_v4, fb_array_din, 
   // Inputs
   rclk, se, si, sctag_scbuf_fbrd_en_c3, 
   sctag_scbuf_fbrd_wl_c3, sctag_scbuf_fbwr_wen_r2, 
   sctag_scbuf_fbwr_wl_r2, sctag_scbuf_fbd_stdatasel_c3, 
   sctag_scbuf_stdecc_c3, dram_scbuf_data_r2, dram_scbuf_ecc_r2
   ) ;


input            rclk;
input            se, si;

input            sctag_scbuf_fbrd_en_c3;
input   [2:0]    sctag_scbuf_fbrd_wl_c3;
input   [15:0]   sctag_scbuf_fbwr_wen_r2;      // dram Fill or store in OFF mode.
input   [2:0]    sctag_scbuf_fbwr_wl_r2;       // dram Fill entry.
input            sctag_scbuf_fbd_stdatasel_c3; // select store data in OFF mode
input   [77:0]   sctag_scbuf_stdecc_c3;       // store data goes to scbuf and scdata
input   [127:0]  dram_scbuf_data_r2;           // fill data.
input   [27:0]   dram_scbuf_ecc_r2;            // fill ecc

output           so;

output           sctag_scbuf_fbrd_en_c3_v1;
output           sctag_scbuf_fbrd_en_c3_v2;
output           sctag_scbuf_fbrd_en_c3_v3;
output           sctag_scbuf_fbrd_en_c3_v4;
output  [2:0]    sctag_scbuf_fbrd_wl_c3_v1;
output  [2:0]    sctag_scbuf_fbrd_wl_c3_v2;
output  [2:0]    sctag_scbuf_fbrd_wl_c3_v3;
output  [2:0]    sctag_scbuf_fbrd_wl_c3_v4;

output  [15:0]   sctag_scbuf_fbwr_wen_r3;      // dram Fill or store in OFF mode.
output           sctag_scbuf_fbwr_wren_r3_v4;
output           sctag_scbuf_fbwr_wren_r3_v3;
output           sctag_scbuf_fbwr_wren_r3_v2;
output           sctag_scbuf_fbwr_wren_r3_v1;
output  [2:0]    sctag_scbuf_fbwr_wl_r3_v1;    // dram Fill entry.
output  [2:0]    sctag_scbuf_fbwr_wl_r3_v2;
output  [2:0]    sctag_scbuf_fbwr_wl_r3_v3;
output  [2:0]    sctag_scbuf_fbwr_wl_r3_v4;
output  [623:0]  fb_array_din;                 // FB read data



wire    [ 77:0]  sctag_scdata_stdecc_c4;
wire    [155:0]  btu_scbuf_decc_r2, btu_scbuf_decc_r3;
wire    [623:0]  ram_decc;
wire    [623:0]  sctag_decc;

wire    [2:0]    sctag_scbuf_fbwr_wl_r3;

////////////////////////////////////////////////////////////////////////////////

assign  sctag_scbuf_fbrd_en_c3_v1 = sctag_scbuf_fbrd_en_c3 ;
assign  sctag_scbuf_fbrd_en_c3_v2 = sctag_scbuf_fbrd_en_c3 ;
assign  sctag_scbuf_fbrd_en_c3_v3 = sctag_scbuf_fbrd_en_c3 ;
assign  sctag_scbuf_fbrd_en_c3_v4 = sctag_scbuf_fbrd_en_c3 ;

assign  sctag_scbuf_fbrd_wl_c3_v1[2:0] = sctag_scbuf_fbrd_wl_c3[2:0] ;
assign  sctag_scbuf_fbrd_wl_c3_v2[2:0] = sctag_scbuf_fbrd_wl_c3[2:0] ;
assign  sctag_scbuf_fbrd_wl_c3_v3[2:0] = sctag_scbuf_fbrd_wl_c3[2:0] ;
assign  sctag_scbuf_fbrd_wl_c3_v4[2:0] = sctag_scbuf_fbrd_wl_c3[2:0] ;


dff_s   #(16)  ff_fbwr_wen_r3
              (.q   (sctag_scbuf_fbwr_wen_r3[15:0]),
               .din (sctag_scbuf_fbwr_wen_r2[15:0]),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()
              ) ;
assign  sctag_scbuf_fbwr_wren_r3_v4 = (sctag_scbuf_fbwr_wen_r3[6] |
                                       sctag_scbuf_fbwr_wen_r3[4] |
                                       sctag_scbuf_fbwr_wen_r3[2] |
                                       sctag_scbuf_fbwr_wen_r3[0]) ;
assign  sctag_scbuf_fbwr_wren_r3_v3 = (sctag_scbuf_fbwr_wen_r3[7] |
                                       sctag_scbuf_fbwr_wen_r3[5] |
                                       sctag_scbuf_fbwr_wen_r3[3] |
                                       sctag_scbuf_fbwr_wen_r3[1]) ;
assign  sctag_scbuf_fbwr_wren_r3_v2 = (sctag_scbuf_fbwr_wen_r3[14] |
                                       sctag_scbuf_fbwr_wen_r3[12] |
                                       sctag_scbuf_fbwr_wen_r3[10] |
                                       sctag_scbuf_fbwr_wen_r3[8]) ;
assign  sctag_scbuf_fbwr_wren_r3_v1 = (sctag_scbuf_fbwr_wen_r3[15] |
                                       sctag_scbuf_fbwr_wen_r3[13] |
                                       sctag_scbuf_fbwr_wen_r3[11] |
                                       sctag_scbuf_fbwr_wen_r3[9]) ;


dff_s   #(3)   ff_fbwr_wl_r3
              (.q   (sctag_scbuf_fbwr_wl_r3[2:0]),
               .din (sctag_scbuf_fbwr_wl_r2[2:0]),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()
              ) ;
assign sctag_scbuf_fbwr_wl_r3_v1[2:0] = sctag_scbuf_fbwr_wl_r3[2:0] ;
assign sctag_scbuf_fbwr_wl_r3_v2[2:0] = sctag_scbuf_fbwr_wl_r3[2:0] ;
assign sctag_scbuf_fbwr_wl_r3_v3[2:0] = sctag_scbuf_fbwr_wl_r3[2:0] ;
assign sctag_scbuf_fbwr_wl_r3_v4[2:0] = sctag_scbuf_fbwr_wl_r3[2:0] ;



dff_s   #(78)  ff_sctag_scdata_stdecc_c4
              (.q   (sctag_scdata_stdecc_c4[77:0]),
               .din (sctag_scbuf_stdecc_c3[77:0]),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()
              ) ;

assign  sctag_decc = {8{sctag_scdata_stdecc_c4[77:0]}} ;



assign  btu_scbuf_decc_r2  = {dram_scbuf_data_r2[127:96], dram_scbuf_ecc_r2[27:21],
                              dram_scbuf_data_r2[ 95:64], dram_scbuf_ecc_r2[20:14],
                              dram_scbuf_data_r2[ 63:32], dram_scbuf_ecc_r2[13: 7],
                              dram_scbuf_data_r2[ 31: 0], dram_scbuf_ecc_r2[ 6: 0]} ;

dff_s   #(156) ff_btu_scbuf_decc_r3
              (.q   (btu_scbuf_decc_r3[155:0]),
               .din (btu_scbuf_decc_r2[155:0]),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()
              ) ;

assign  ram_decc   = {4{btu_scbuf_decc_r3[155:0]}} ;



dff_s   #(1)   ff_fbd_stdatasel_c4
              (.q   (sctag_scbuf_fbd_stdatasel_c4),
               .din (sctag_scbuf_fbd_stdatasel_c3),
               .clk (rclk),
               .se  (1'b0), .si  (), .so  ()
              ) ;



mux2ds #(624) mux_fb_array_din
              (.dout (fb_array_din[623:0]),
               .in0  (ram_decc[623:0]),     .sel0 (~sctag_scbuf_fbd_stdatasel_c4),
               .in1  (sctag_decc[623:0]),   .sel1 (sctag_scbuf_fbd_stdatasel_c4)
              ) ;


endmodule
