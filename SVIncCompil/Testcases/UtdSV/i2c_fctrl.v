// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: i2c_fctrl.v
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
//  Module Name:	i2c_fctrl (io-to-cpu fast control)
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
module i2c_fctrl (/*AUTOARG*/
   // Outputs
   int_buf_sel_next, io_buf_sel_next, int_buf_rd, io_buf_rd, 
   int_buf_hit_hwm, io_buf_head_f, int_buf_wr, int_buf_tail_ptr, 
   int_buf_head_ptr, io_buf_head_ptr, 
   // Inputs
   cpu_rst_l, cpu_clk, tx_sync, rx_sync, cpx_iob_grant_cx2, 
   int_buf_cpx_req, io_buf_cpx_req, iob_cpx_req_next, 
   cpu_mondo_rd_d2, cpu_mondo_wr_d2, io_buf_tail_s
   );
   
////////////////////////////////////////////////////////////////////////
// Signal declarations
////////////////////////////////////////////////////////////////////////
   // Global interface
   input                           cpu_rst_l;
   input 			   cpu_clk;
   input 			   tx_sync;
   input 			   rx_sync;

   
   // Crossbar interface
   input [`IOB_CPU_WIDTH-1:0] 	   cpx_iob_grant_cx2;
   
    
   // i2c fast datapath interface
   input [`IOB_CPU_WIDTH-1:0] 	   int_buf_cpx_req;
   input [`IOB_CPU_WIDTH-1:0] 	   io_buf_cpx_req;
   input [`IOB_CPU_WIDTH-1:0] 	   iob_cpx_req_next;
   
   output 			   int_buf_sel_next;
   output 			   io_buf_sel_next;
   
   output 			   int_buf_rd;
   output 			   io_buf_rd;

   
   // c2i fast control interface
   input 			   cpu_mondo_rd_d2;
   input 			   cpu_mondo_wr_d2;
   
   output 			   int_buf_hit_hwm;

   
   // i2c slow control interface
   input [`IOB_IO_BUF_INDEX:0] 	   io_buf_tail_s;
   output [`IOB_IO_BUF_INDEX:0]    io_buf_head_f;

   
   // Interrupt table read result buffer interface
   output 			   int_buf_wr;
   output [`IOB_INT_BUF_INDEX-1:0] int_buf_tail_ptr;
   output [`IOB_INT_BUF_INDEX-1:0] int_buf_head_ptr;

   
   // IO buffer interface
   output [`IOB_IO_BUF_INDEX-1:0]  io_buf_head_ptr;

   
   // Internal signals
   wire [`IOB_CPU_WIDTH-1:0] 	   cpx_buf_full;
   wire [`IOB_CPU_WIDTH-1:0] 	   cpx_iob_grant;
   wire 			   cpu_mondo_rdwr_d2;
   wire [`IOB_INT_BUF_INDEX:0] 	   int_buf_tail;
   wire [`IOB_INT_BUF_INDEX:0] 	   int_buf_tail_plus;
   wire [`IOB_INT_BUF_INDEX:0] 	   int_buf_tail_plus10;
   
   wire [`IOB_INT_BUF_INDEX:0] 	   int_buf_head;
   wire [`IOB_INT_BUF_INDEX:0] 	   int_buf_head_prev;
   wire [`IOB_INT_BUF_INDEX:0] 	   int_buf_head_plus1;
   wire 			   int_buf_head_inc;
   wire 			   int_buf_empty;
   wire 			   int_buf_empty_prev;
   wire 			   int_buf_vld;
   wire 			   int_buf_vld_next;

   wire [`IOB_IO_BUF_INDEX:0] 	   io_buf_head;
   wire [`IOB_IO_BUF_INDEX:0] 	   io_buf_head_prev;
   wire [`IOB_IO_BUF_INDEX:0] 	   io_buf_head_plus1;
   wire 			   io_buf_head_inc;
   wire [`IOB_IO_BUF_INDEX:0] 	   io_buf_tail;
   wire 			   io_buf_empty;
   wire 			   io_buf_empty_prev;
   wire 			   io_buf_vld;
   wire 			   io_buf_vld_next;
   
   
////////////////////////////////////////////////////////////////////////
// Code starts here
////////////////////////////////////////////////////////////////////////
   /************************************************************
    * IO-to-CPX Mux Control
    ************************************************************/   
   // Generate mux selects
   assign 	int_buf_sel_next = ~|(cpx_buf_full & ~cpx_iob_grant & int_buf_cpx_req) &
		                   int_buf_vld;
   
   assign 	io_buf_sel_next = ~|(cpx_buf_full & ~cpx_iob_grant & io_buf_cpx_req) &
		                  ~int_buf_sel_next & io_buf_vld;

   
   /************************************************************
    * Flop grant from CPX
    ************************************************************/
   dffrl_ns #(`IOB_CPU_WIDTH) cpx_iob_grant_ff (.din(cpx_iob_grant_cx2),
					       	.clk(cpu_clk),
					       	.rst_l(cpu_rst_l),
					       	.q(cpx_iob_grant));
   

   /************************************************************
    * Counters to keep track of each CPX's buffer level
    ************************************************************/
   // CPX0 Count
   i2c_cpx_cnt count0 (.rst_l(cpu_rst_l),
		       .clk(cpu_clk),
		       .iob_cpx_req_next(iob_cpx_req_next[0]),
		       .cpx_iob_grant(cpx_iob_grant[0]),
		       .cpx_buf_full(cpx_buf_full[0]));
   
   // CPX1 Count
   i2c_cpx_cnt count1 (.rst_l(cpu_rst_l),
		       .clk(cpu_clk),
		       .iob_cpx_req_next(iob_cpx_req_next[1]),
		       .cpx_iob_grant(cpx_iob_grant[1]),
		       .cpx_buf_full(cpx_buf_full[1]));
   
   // CPX2 Count
   i2c_cpx_cnt count2 (.rst_l(cpu_rst_l),
		       .clk(cpu_clk),
		       .iob_cpx_req_next(iob_cpx_req_next[2]),
		       .cpx_iob_grant(cpx_iob_grant[2]),
		       .cpx_buf_full(cpx_buf_full[2]));
   
   // CPX3 Count
   i2c_cpx_cnt count3 (.rst_l(cpu_rst_l),
		       .clk(cpu_clk),
		       .iob_cpx_req_next(iob_cpx_req_next[3]),
		       .cpx_iob_grant(cpx_iob_grant[3]),
		       .cpx_buf_full(cpx_buf_full[3]));
   
   // CPX4 Count
   i2c_cpx_cnt count4 (.rst_l(cpu_rst_l),
		       .clk(cpu_clk),
		       .iob_cpx_req_next(iob_cpx_req_next[4]),
		       .cpx_iob_grant(cpx_iob_grant[4]),
		       .cpx_buf_full(cpx_buf_full[4]));
   
   // CPX5 Count
   i2c_cpx_cnt count5 (.rst_l(cpu_rst_l),
		       .clk(cpu_clk),
		       .iob_cpx_req_next(iob_cpx_req_next[5]),
		       .cpx_iob_grant(cpx_iob_grant[5]),
		       .cpx_buf_full(cpx_buf_full[5]));
   
   // CPX6 Count
   i2c_cpx_cnt count6 (.rst_l(cpu_rst_l),
		       .clk(cpu_clk),
		       .iob_cpx_req_next(iob_cpx_req_next[6]),
		       .cpx_iob_grant(cpx_iob_grant[6]),
		       .cpx_buf_full(cpx_buf_full[6]));
   
   // CPX7 Count
   i2c_cpx_cnt count7 (.rst_l(cpu_rst_l),
		       .clk(cpu_clk),
		       .iob_cpx_req_next(iob_cpx_req_next[7]),
		       .cpx_iob_grant(cpx_iob_grant[7]),
		       .cpx_buf_full(cpx_buf_full[7]));
   
   
   /************************************************************
    * Interrupt Status Table Read Result Buffer Control
    * An 16 deep buffer to store interrupt table read results.
    * 
    *                                               __decode int stat table read
    *                                     flop req |
    *                                         |    |        __read int stat table here      
    *                                         |    |       |
    *                                         |    |       |    __flop read result
    *                                         |    |       |   |
    *                                         |    |       |   |       __tail pointer increment
    *                                         |    |       |   |      |
    *                                         |    |       |   |      |   compute hwm   __stall sent here
    *                                         |    |       |   |      |       |        | 
    *                                         V    V       V   V  d2  V       V        V
    *     PQ      PA      PX1     rptr    PX2     C1      C2      C3      C4      C5      rptr
    *             PQ      PA      PX1     rptr    PX2     C1      C2      C3      C4      C5      rptr
    *                     PQ      PA      PX1     rptr    PX2     C1      C2      C3      C4
    *                             PQ      PA      PX1     rptr    PX2     C1      C2      C3
    *                                     PQ      PA      PX1     rptr    PX2     C1      C2
    *                                             PQ      PA      PX1     rptr    PX2     C1
    *                                                     PQ      PA      PX1     rptr    PX2
    *                                                             PQ      PA      PX1     rptr
    *                                                                     PQ      PA      PX1     rptr
    *                                                                             PQ      PA      PX1     rptr
    *                                                                                     PQ      PA      PX1
    *                                                                                        -->  PQ
    *                                                                                       |
    *                                                                                       |
    *                                                              packet in this PQ is stalled
    * 
    * When stall is signalled, there can potentially be 10 packets in C4, C3,
    * C2, C1, PX2, rptr, PX1, PA, PQ, and PQ-1 that need to be queued in the CPU shared buffer.
    ************************************************************/
   assign 	cpu_mondo_rdwr_d2 = cpu_mondo_rd_d2 | cpu_mondo_wr_d2;
   assign 	int_buf_wr = cpu_mondo_rdwr_d2;
   
   // Tail pointer to interrupt table read result buffer
   dffrle_ns #(`IOB_INT_BUF_INDEX+1) int_buf_tail_ff (.din(int_buf_tail_plus),
						     .rst_l(cpu_rst_l),
						     .en(int_buf_wr),
						     .clk(cpu_clk),
						     .q(int_buf_tail));
   
   assign 	int_buf_tail_plus = int_buf_tail + 5'b1;
   assign 	int_buf_tail_ptr = int_buf_tail[`IOB_INT_BUF_INDEX-1:0];
   
   assign 	int_buf_tail_plus10 = int_buf_tail + 5'b01010;
   assign       int_buf_hit_hwm = ((int_buf_tail_plus10[`IOB_INT_BUF_INDEX] != int_buf_head[`IOB_INT_BUF_INDEX]) &
                                   (int_buf_tail_plus10[`IOB_INT_BUF_INDEX-1:0] >= int_buf_head[`IOB_INT_BUF_INDEX-1:0])) |
                                  ((int_buf_tail_plus10[`IOB_INT_BUF_INDEX] == int_buf_head[`IOB_INT_BUF_INDEX]) &
                                   (int_buf_tail_plus10[`IOB_INT_BUF_INDEX-1:0] <= int_buf_head[`IOB_INT_BUF_INDEX-1:0]));
   
   
   // Head pointer to interrupt table read result buffer
   dffrl_ns #(`IOB_INT_BUF_INDEX+1) int_buf_head_prev_ff (.din(int_buf_head),
							  .clk(cpu_clk),
							  .rst_l(cpu_rst_l),
							  .q(int_buf_head_prev));
   assign     int_buf_head_plus1 = int_buf_head_prev + 4'b1;
   assign     int_buf_head = int_buf_head_inc ? int_buf_head_plus1 :
                                                int_buf_head_prev;
   assign     int_buf_head_ptr = int_buf_head[`IOB_INT_BUF_INDEX-1:0];
   
   // Interrupt table read result buffer is empty if head == tail  
   assign     int_buf_empty = (int_buf_head == int_buf_tail);
   dff_ns #(1) int_buf_empty_prev_ff (.din(int_buf_empty|~cpu_rst_l),
				      .clk(cpu_clk),
                                      .q(int_buf_empty_prev));
   
   assign     int_buf_head_inc = ~int_buf_empty_prev &
                                 ((int_buf_vld & int_buf_sel_next) |
                                  ~int_buf_vld);

   // This read signal corresponds to the access already in the memory
   assign     int_buf_rd = int_buf_head_inc;

   assign     int_buf_vld_next = int_buf_rd |
	                         (int_buf_vld & ~int_buf_sel_next);
   dffrl_ns #(1) int_buf_vld_ff (.din(int_buf_vld_next),
				 .clk(cpu_clk),
				 .rst_l(cpu_rst_l),
				 .q(int_buf_vld));

	  
   /************************************************************
    * IO Buffer Control
    ************************************************************/
   // Head pointer to io buffer
   dffrl_ns #(`IOB_IO_BUF_INDEX+1) io_buf_head_prev_ff (.din(io_buf_head),
							.clk(cpu_clk),
							.rst_l(cpu_rst_l),
							.q(io_buf_head_prev));
   assign     io_buf_head_plus1 = io_buf_head_prev + 5'b1;
   assign     io_buf_head = io_buf_head_inc ? io_buf_head_plus1 :
                                              io_buf_head_prev;
   assign     io_buf_head_ptr = io_buf_head[`IOB_IO_BUF_INDEX-1:0];

   dffrle_ns #(`IOB_IO_BUF_INDEX+1) io_buf_head_f_ff (.din(io_buf_head),
						      .rst_l(cpu_rst_l),
						      .en(tx_sync),
						      .clk(cpu_clk),
						      .q(io_buf_head_f));
   
   
   // Flop tail pointer once to convert to cpu clock domain
   dffrle_ns #(`IOB_IO_BUF_INDEX+1) io_buf_tail_ff (.din(io_buf_tail_s),
						    .rst_l(cpu_rst_l),
						    .en(rx_sync),
						    .clk(cpu_clk),
						    .q(io_buf_tail));


   // IO buffer is empty if head == tail  
   assign     io_buf_empty = (io_buf_head == io_buf_tail);
   dff_ns #(1) io_buf_empty_prev_ff (.din(io_buf_empty|~cpu_rst_l),
				     .clk(cpu_clk),
                                     .q(io_buf_empty_prev));
   
   assign     io_buf_head_inc = ~io_buf_empty_prev &
                                ((io_buf_vld & io_buf_sel_next) |
                                 ~io_buf_vld);

   // This read signal corresponds to the access already in the memory
   assign     io_buf_rd = io_buf_head_inc;

   assign     io_buf_vld_next = io_buf_rd |
	                        (io_buf_vld & ~io_buf_sel_next);
   dffrl_ns #(1) io_buf_vld_ff (.din(io_buf_vld_next),
				.clk(cpu_clk),
				.rst_l(cpu_rst_l),
				.q(io_buf_vld));

   
endmodule // i2c_fctrl


