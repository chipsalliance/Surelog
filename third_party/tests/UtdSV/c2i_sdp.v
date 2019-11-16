// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: c2i_sdp.v
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
//  Module Name:	c2i_sdp (cpu-to-io slow datapath)
//  Description:	Datapath for packets going to the UCB.
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
module c2i_sdp (/*AUTOARG*/
   // Outputs
   pcx_packet, tap_packet, c2i_packet_addr, c2i_packet, 
   c2i_rd_nack_packet, wr_ack_io_buf_din, 
   // Inputs
   clk, tap_iob_packet, cpu_buf_dout_lo, cpu_buf_dout_hi, cpu_buf_rd, 
   tap_sel, cpu_packet_is_req, cpu_packet_type
   );

////////////////////////////////////////////////////////////////////////
// Signal declarations
////////////////////////////////////////////////////////////////////////
   // Global interface
   input 			     clk;


   // TAP interface
   input [`UCB_64PAY_PKT_WIDTH-1:0]  tap_iob_packet;
   

   // CPU buffer interface
   wire [`PCX_WIDTH-1:0] 	     cpu_buf_dout;
   input [64:0] 		     cpu_buf_dout_lo;
   input [64:0] 		     cpu_buf_dout_hi;
   
   assign 	cpu_buf_dout = {cpu_buf_dout_hi[`PCX_WIDTH-64-1:0],cpu_buf_dout_lo[63:0]};

   
   // c2i slow control interface
   output [`PCX_WIDTH-1:0] 	     pcx_packet;
   output [`UCB_64PAY_PKT_WIDTH-1:0] tap_packet;
   input 			     cpu_buf_rd;
   input 			     tap_sel;
   input 			     cpu_packet_is_req;
   input [`UCB_PKT_WIDTH-1:0] 	     cpu_packet_type;

   output [`UCB_ADDR_WIDTH-1:0]      c2i_packet_addr;
   
   
   // UCB buffer interface
   output [`UCB_64PAY_PKT_WIDTH-1:0] c2i_packet;

   
   // Nack buffer interface
   output [`UCB_NOPAY_PKT_WIDTH-1:0] c2i_rd_nack_packet;

   
   // i2c slow datapath interface
   output [`IOB_IO_BUF_WIDTH-1:0]    wr_ack_io_buf_din;

   
   // Internal signals
   wire [`UCB_64PAY_PKT_WIDTH-1:0]   cpu_packet;
   wire [`CPX_WIDTH-1:0] 	     wr_ack_packet;
   wire [`IOB_CPU_WIDTH-1:0] 	     wr_ack_packet_cpu;
   
   wire [`UCB_PKT_WIDTH-1:0] 	     nack_packet_type;
   

////////////////////////////////////////////////////////////////////////
// Code starts here
////////////////////////////////////////////////////////////////////////
   /*****************************************************************
    * Flop data from CPU buffer
    *****************************************************************/
   dffe_ns #(`PCX_WIDTH) pcx_packet_ff (.din(cpu_buf_dout),
					.en(cpu_buf_rd),
					.clk(clk),
					.q(pcx_packet));

   
   // Convert from PCX format to UCB format   
   assign 	cpu_packet = cpu_packet_is_req ?
		             // request packet to IO devices
			     {pcx_packet[`PCX_DA_HI:`PCX_DA_LO], // data
			      `UCB_RSV_WIDTH'b0,                 // reserved bits
			      pcx_packet[`PCX_AD_HI:`PCX_AD_LO], // address
			      pcx_packet[`PCX_SZ_HI:`PCX_SZ_LO], // size
			      `UCB_BID_CMP,                      // buffer ID
			      // Assumption: UCB thread ID is 1 bit wider than PCX thread ID
			      1'b0,                              // thread ID
			      pcx_packet[`PCX_CP_HI:`PCX_CP_LO],
			      pcx_packet[`PCX_TH_HI:`PCX_TH_LO],
			      cpu_packet_type} :                 // packet type
		             // forward reply packet to TAP
		             {pcx_packet[`PCX_DA_HI:`PCX_DA_LO], // data
			      `UCB_RSV_WIDTH'b0,                 // reserved bits
			      `UCB_ADDR_WIDTH'b0,                // address
			      `UCB_SIZE_WIDTH'b0,                // size
			      `UCB_BID_TAP,                      // buffer ID
			      `UCB_THR_WIDTH'b0,                 // thread ID
			      cpu_packet_type};                  // packet type

   
   /*****************************************************************
    * Generate write acks (CPX format) for PCX stores
    *****************************************************************/
   assign 	wr_ack_packet = {1'b1,                              // valid
				 `ST_ACK,                           // return type
				 3'b0,                              // error
				 1'b1,                              // NC
				 pcx_packet[`PCX_TH_HI:`PCX_TH_LO], // thread ID
				 2'b0,                              // XX
				 pcx_packet[`PCX_P_HI:`PCX_P_LO],   // packet ID
				 1'b0,                              // atomic
				 1'b0,                              // X
				 2'b0,                              // XX
				 pcx_packet[109],                   // reflect pcx[109] to cpx[125] for blk-st/binit-st
				 4'b0,                              // XXXX
				 pcx_packet[`PCX_CP_HI:`PCX_CP_LO], // cpu ID
				 118'b0};                           // un-used

   assign 	wr_ack_packet_cpu = 1'b1 << pcx_packet[`PCX_CP_HI:`PCX_CP_LO];
   
   assign 	wr_ack_io_buf_din = {wr_ack_packet_cpu,
				     wr_ack_packet};

   
   /*****************************************************************
    * Packet from TAP
    *****************************************************************/
   assign 	tap_packet = tap_iob_packet;

   
   /*****************************************************************
    * Mux between TAP and CPU packet
    *****************************************************************/
   // TAP packets priority > PCX packets priority
   assign 	c2i_packet = tap_sel ? tap_packet :
		                       cpu_packet;

   assign 	c2i_packet_addr = c2i_packet[`UCB_ADDR_HI:`UCB_ADDR_LO];

   
   /*****************************************************************
    * Generate read nack for read to undefined address space
    *****************************************************************/
   assign 	nack_packet_type = (cpu_packet[`UCB_PKT_HI:`UCB_PKT_LO] == `UCB_IFILL_REQ) ?
				    `UCB_IFILL_NACK :
		                    `UCB_READ_NACK;
   
   assign 	c2i_rd_nack_packet = {`UCB_RSV_WIDTH'b0,                   // reserved bits
				      `UCB_ADDR_WIDTH'b0,                  // address
				      `UCB_SIZE_WIDTH'b0,                  // size
				      c2i_packet[`UCB_BUF_HI:`UCB_BUF_LO], // buffer ID
				      c2i_packet[`UCB_THR_HI:`UCB_THR_LO], // thread ID
				      nack_packet_type};                   // packet type

   
endmodule // c2i_sdp


// Local Variables:
// verilog-auto-sense-defines-constant:t
// End:



