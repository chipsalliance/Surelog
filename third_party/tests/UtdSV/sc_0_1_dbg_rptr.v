// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sc_0_1_dbg_rptr.v
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
module sc_0_1_dbg_rptr(/*AUTOARG*/
   // Outputs
   l2_dbgbus_out, enable_01, so, 
   // Inputs
   dbgbus_b0, dbgbus_b1, rclk, si, se
   );



  output 	[39:0]		l2_dbgbus_out ;
  output			enable_01;
  input		[40:0]		dbgbus_b0;
  input		[40:0]		dbgbus_b1;


   input        rclk;
   input        si, se;
   output       so;

   wire	[39:0]	l2_dbgbus_out_prev ;
   wire	enable_01_prev;

   wire int_scanout;

   // connect scanout of the last flop to int_scanout.
   // The output of the lockup latch is 
   // the scanout of this dbb (so)

   bw_u1_scanlg_2x so_lockup(.so(so), .sd(int_scanout), .ck(rclk), .se(se));


// Row0

    mux2ds  #(20) mux_dbgmuxb01_row0   (.dout (l2_dbgbus_out_prev[19:0]),
                                 .in0(dbgbus_b0[19:0]),
                                 .in1(dbgbus_b1[19:0]),
                                 .sel0(dbgbus_b0[40]),
                                 .sel1(~dbgbus_b0[40]));
 
    dff_s  #(20)   ff_dbgmuxb01_row0   (.q(l2_dbgbus_out[19:0]),
                                  .din(l2_dbgbus_out_prev[19:0]),
                                  .clk(rclk), .se(1'b0), .si(), .so() );


// Row1

    mux2ds  #(20) mux_dbgmuxb01_row1   (.dout (l2_dbgbus_out_prev[39:20]),
                                 .in0(dbgbus_b0[39:20]),
                                 .in1(dbgbus_b1[39:20]),
                                 .sel0(dbgbus_b0[40]),
                                 .sel1(~dbgbus_b0[40]));
 
    dff_s  #(20)   ff_dbgmuxb01_row1   (.q(l2_dbgbus_out[39:20]),
                                  .din(l2_dbgbus_out_prev[39:20]),
                                  .clk(rclk), .se(1'b0), .si(), .so() );

    
   assign	enable_01_prev = dbgbus_b0[40] | dbgbus_b1[40] ;


   dff_s  #(1)   ff_valid   (.q(enable_01),
                           .din(enable_01_prev),
                           .clk(rclk), .se(1'b0), .si(), .so() );

endmodule
    

  

