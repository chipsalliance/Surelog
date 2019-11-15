// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: c2i_buf.v
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
////////////////////////////////////////////////////////////////////////
/*
//  Module Name:	c2i_buf (cpu-to-io UCB buffer)
//  Description:	This is the interface to the UCB modules.
*/
////////////////////////////////////////////////////////////////////////
// Global header file includes
////////////////////////////////////////////////////////////////////////
`include	"sys.h" // system level definition file which contains the 
			// time scale definition
`include        "iop.h"

////////////////////////////////////////////////////////////////////////
// Local header file includes / local defines
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
// Interface signal list declarations
////////////////////////////////////////////////////////////////////////
module c2i_buf (/*AUTOARG*/
   // Outputs
   ucb_buf_acpt, iob_ucb_vld, iob_ucb_data, 
   // Inputs
   rst_l, clk, c2i_packet_vld, ucb_sel, c2i_packet, ucb_iob_stall
   );

   // synopsys template
   
   parameter REG_WIDTH = 64;
   parameter IOB_UCB_WIDTH = 32;
   
   
////////////////////////////////////////////////////////////////////////
// Signal declarations
////////////////////////////////////////////////////////////////////////
   // Global interface
   input                      rst_l;
   input 		      clk;


   // slow control interface
   input 		      c2i_packet_vld;
   input 		      ucb_sel;
   output 		      ucb_buf_acpt;

   
   // slow datapath interface
   input [REG_WIDTH+63:0]     c2i_packet;
   
   
   // UCB interface
   output                     iob_ucb_vld;
   output [IOB_UCB_WIDTH-1:0] iob_ucb_data;
   input 	              ucb_iob_stall;
   
   
   // Internal signals
   wire 		      dbl_buf_wr;
   wire 		      dbl_buf_rd;
   wire 		      dbl_buf_vld;
   wire 		      dbl_buf_full;
   
   wire 		      outdata_buf_wr;
   wire [REG_WIDTH+63:0]      outdata_buf_in;
   wire [(REG_WIDTH+64)/IOB_UCB_WIDTH-1:0] outdata_vec_in;
   wire 		      outdata_buf_busy;

   
////////////////////////////////////////////////////////////////////////
// Code starts here
////////////////////////////////////////////////////////////////////////

   assign 	 dbl_buf_wr = c2i_packet_vld & ucb_sel & ~dbl_buf_full;
   assign 	 ucb_buf_acpt = dbl_buf_wr;
   assign 	 dbl_buf_rd = dbl_buf_vld & ~outdata_buf_busy;
   assign 	 outdata_buf_wr = dbl_buf_rd;
   assign 	 outdata_vec_in = {(REG_WIDTH+64)/IOB_UCB_WIDTH{1'b1}};
   

   dbl_buf #(REG_WIDTH+64) dbl_buf (.rst_l(rst_l),
				    .clk(clk),
				    .wr(dbl_buf_wr),
				    .din(c2i_packet),
				    .rd(dbl_buf_rd),
				    .dout(outdata_buf_in),
				    .vld(dbl_buf_vld),
				    .full(dbl_buf_full));
   
   ucb_bus_out #(IOB_UCB_WIDTH,REG_WIDTH) ucb_bus_out (.rst_l(rst_l),
                                                       .clk(clk),
                                                       .outdata_buf_wr(outdata_buf_wr),
                                                       .outdata_buf_in(outdata_buf_in),
                                                       .outdata_vec_in(outdata_vec_in),
                                                       .outdata_buf_busy(outdata_buf_busy),
                                                       .vld(iob_ucb_vld),
                                                       .data(iob_ucb_data),
                                                       .stall(ucb_iob_stall));


endmodule // c2i_buf

