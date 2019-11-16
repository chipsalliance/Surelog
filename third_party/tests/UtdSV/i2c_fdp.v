// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: i2c_fdp.v
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
//  Module Name:	i2c_fdp (io-to-cpu fast datapath)
//  Description:	
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
module i2c_fdp (/*AUTOARG*/
   // Outputs
   iob_cpx_req_cq, iob_cpx_data_ca, int_buf_cpx_req, io_buf_cpx_req, 
   iob_cpx_req_next, 
   // Inputs
   cpu_clk, rx_sync, int_buf_sel_next, io_buf_sel_next, int_buf_rd, 
   io_buf_rd, int_buf_dout_raw, io_buf_dout_raw
   );
   
////////////////////////////////////////////////////////////////////////
// Signal declarations
////////////////////////////////////////////////////////////////////////
   // Global interface
   input 		           cpu_clk;
   input 			   rx_sync;
   
   
   // Crossbar interface
   output [`IOB_CPU_WIDTH-1:0] 	   iob_cpx_req_cq;
   output [`CPX_WIDTH-1:0] 	   iob_cpx_data_ca;
   
    
   // i2c fast control interface
   input 			   int_buf_sel_next;
   input 			   io_buf_sel_next;

   input 			   int_buf_rd;
   input 			   io_buf_rd;

   output [`IOB_CPU_WIDTH-1:0] 	   int_buf_cpx_req;
   output [`IOB_CPU_WIDTH-1:0] 	   io_buf_cpx_req;
   output [`IOB_CPU_WIDTH-1:0] 	   iob_cpx_req_next;

   
   // Interrupt status table read result buffer interface
   wire [`IOB_INT_BUF_WIDTH-1:0]   int_buf_dout;
   input [159:0] 		   int_buf_dout_raw;

   assign 	 int_buf_dout = int_buf_dout_raw[`IOB_INT_BUF_WIDTH-1:0];

   
   // IO buffer interface
   wire [`IOB_IO_BUF_WIDTH-1:0]    io_buf_dout;
   input [159:0] 		   io_buf_dout_raw;
   
   assign 	 io_buf_dout = io_buf_dout_raw[`IOB_IO_BUF_WIDTH-1:0];


   // Internal signals
   wire [`CPX_WIDTH-1:0] 	   iob_cpx_data_next;
   wire [`CPX_WIDTH-1:0] 	   int_buf_cpx_data;
   wire [`CPX_WIDTH-1:0] 	   io_buf_cpx_data;
   wire [`CPX_WIDTH-1:0] 	   iob_cpx_data_cq;
   
   wire [`IOB_INT_BUF_WIDTH-1:0]   int_buf_dout_d1;

   wire [`IOB_IO_BUF_WIDTH-1:0]    io_buf_dout_d1;

   
////////////////////////////////////////////////////////////////////////
// Code starts here
////////////////////////////////////////////////////////////////////////
   /************************************************************
    * IO-to-CPX Mux
    ************************************************************/
   assign 	 iob_cpx_req_next = ({`IOB_CPU_WIDTH{int_buf_sel_next}} & int_buf_cpx_req) |
				    ({`IOB_CPU_WIDTH{io_buf_sel_next}} & io_buf_cpx_req);
   
   dff_ns #(`IOB_CPU_WIDTH) iob_cpx_req_cq_ff (.din(iob_cpx_req_next),
					       .clk(cpu_clk),
					       .q(iob_cpx_req_cq));

   assign 	 iob_cpx_data_next = ({`CPX_WIDTH{int_buf_sel_next}} & int_buf_cpx_data) |
				     ({`CPX_WIDTH{io_buf_sel_next}} & io_buf_cpx_data);
   
   dff_ns #(`CPX_WIDTH) iob_cpx_data_cq_ff (.din(iob_cpx_data_next),
					    .clk(cpu_clk),
					    .q(iob_cpx_data_cq));

   // Flop data bus one cycle to match CPX pipeline
   dff_ns #(`CPX_WIDTH) iob_cpx_data_ca_ff (.din(iob_cpx_data_cq),
					    .clk(cpu_clk),
					    .q(iob_cpx_data_ca));

   
   /************************************************************
    * Interrupt Table Read Result Buffer
    * An 8 deep buffer to store interrupt table read results.
    ************************************************************/
   // Assemble CPX req/data
   // int_buf_dout[144:0] return data
   // int_buf_dout[152:145] cpu ID
   dffe_ns #(`IOB_INT_BUF_WIDTH) int_buf_dout_d1_ff (.din(int_buf_dout),
						     .en(int_buf_rd),
						     .clk(cpu_clk),
						     .q(int_buf_dout_d1));

   assign 	 {int_buf_cpx_req,
		  int_buf_cpx_data} = int_buf_dout_d1;

   
   /************************************************************
    * IO Buffer
    ************************************************************/
   // Assemble CPX req/data
   // io_buf_dout[144:0]   return data
   // io_buf_dout[152:145] cpu ID
   dffe_ns #(`IOB_IO_BUF_WIDTH) io_buf_dout_d1_ff (.din(io_buf_dout),
						   .en(io_buf_rd),
						   .clk(cpu_clk),
						   .q(io_buf_dout_d1));

   assign 	 {io_buf_cpx_req,
		  io_buf_cpx_data} = io_buf_dout_d1;
	  
   
endmodule // i2c_fdp



// Local Variables:
// verilog-auto-sense-defines-constant:t
// End:

