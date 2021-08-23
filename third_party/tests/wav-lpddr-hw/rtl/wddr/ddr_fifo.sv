
/*********************************************************************************
Copyright (c) 2021 Wavious LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

*********************************************************************************/

`include "ddr_global_define.vh"

import ddr_global_pkg::*;

module ddr_fifo #(
   parameter       WWIDTH    = 32,
   parameter       RWIDTH    = 32,
   parameter       BWIDTH    = 8,
   parameter       DEPTH     = 8,
   parameter [0:0] SYNC      = 1'b0,
   parameter [0:0] RAM_MODEL = 1'b0,
   parameter       AWIDTH    = $clog2(DEPTH)
) (

   input  logic                 i_scan_mode,
   input  logic                 i_scan_rst_ctrl,
   input  logic                 i_scan_cgc_ctrl,

   input   logic                i_clr,
   input   logic                i_loop_mode,
   input   logic                i_load_ptr,
   input   logic [AWIDTH-1:0]   i_stop_ptr,
   input   logic [AWIDTH-1:0]   i_start_ptr,

   input   logic                i_wclk,
   input   logic                i_wrst,
   input   logic                i_write,
   input   logic [WWIDTH-1:0]   i_wdata,
   output  logic                o_full,
   output  logic                o_early_full,

   input   logic                i_rclk,
   input   logic                i_rrst,
   input   logic                i_read,
   output  logic [RWIDTH-1:0]   o_rdata,
   output  logic                o_early_empty_n,
   output  logic                o_empty_n
);

   logic [  AWIDTH:0] rbin_d , wbin_d;
   logic [  AWIDTH:0] rbin_q , wbin_q;
   logic [  AWIDTH:0] rgray_d, wgray_d;
   logic [  AWIDTH:0] wbin_next_d ;
   logic [  AWIDTH:0] wgray_next_d ;
   logic [  AWIDTH:0] rgray_q, wgray_q;
   logic [  AWIDTH:0] rbin_next_d ;
   logic [  AWIDTH:0] rgray_next_q, rgray_next_d;
   logic [  AWIDTH:0] rgray_sync, wgray_sync;
   logic [AWIDTH-1:0] raddr, waddr;

   // ------------------------------------------------------------------------
   // Clock Gate
   // ------------------------------------------------------------------------

   logic rclk_g;
   ddr_cgc_rl u_cgc_rl (.i_clk(i_rclk), .i_clk_en(o_empty_n), .i_cgc_en(i_scan_cgc_ctrl), .o_clk(rclk_g));

   // ------------------------------------------------------------------------
   // Reset
   // ------------------------------------------------------------------------

   logic rrst, rrst_scan;
   logic wrst, wrst_scan;

   assign rrst = i_rrst | i_clr;
   assign wrst = i_wrst | i_clr;

   ddr_scan_rst u_scan_rrst ( .i_scan_rst_ctrl(i_scan_rst_ctrl), .i_rst(rrst), .o_rst(rrst_scan));
   ddr_scan_rst u_scan_wrst ( .i_scan_rst_ctrl(i_scan_rst_ctrl), .i_rst(wrst), .o_rst(wrst_scan));

   // ------------------------------------------------------------------------
   // FIFO Memory
   // ------------------------------------------------------------------------

   // Choose Flip-Flop register file or RAM model
   generate
      if (!RAM_MODEL) begin : REGFILE
         logic [RWIDTH-1:0] mem [DEPTH-1:0];
         always_ff @(posedge i_wclk)
            if (i_write)
               mem[waddr] <= i_wdata;

         assign o_rdata = mem[raddr];
      end else begin : RAM
         ddr_ram_dp #(
            .DWIDTH     (RWIDTH),
            .BWIDTH     (BWIDTH),
            .SIZE       (DEPTH)
         ) u_ram_dp (
            .i_clk_0    (i_wclk),
            .i_addr_0   (waddr),
            .i_en_0     (i_write),
            .i_we_0     (1'b1),
            .i_be_0     ('1),
            .i_wdata_0  (i_wdata),
            .o_rdata_0  (/*OPEN*/),
            .i_clk_1    (rclk_g),
            .i_addr_1   (raddr),
            .i_en_1     (1'b1),
            .i_we_1     (1'b0),
            .i_be_1     ('1),
            .i_wdata_1  ('0),
            .o_rdata_1  (o_rdata)
         );
      end
   endgenerate

   // ------------------------------------------------------------------------
   // Write Counter
   // ------------------------------------------------------------------------
   logic  max_loop_wptr;
   assign max_loop_wptr = i_loop_mode && (wbin_q == i_stop_ptr) ;

// assign wbin_d       = i_write ?  wbin_q + 'b1 : wbin_q;
   assign wbin_d       = i_load_ptr ? i_start_ptr :
                         i_write && max_loop_wptr ? i_start_ptr :
                         i_write ?  wbin_q + 'b1 : wbin_q;

   assign wgray_d      = (wbin_d >> 1) ^ wbin_d;
   assign wbin_next_d  = wbin_d + 'b1 ;
   assign wgray_next_d = (wbin_next_d >> 1) ^ wbin_next_d;

   always_ff @(posedge i_wclk, posedge wrst_scan) begin
      if (wrst_scan) begin
         wbin_q       <= '0;
         wgray_q      <= '0;
      end else begin
         if (i_write || i_load_ptr ) begin
            wbin_q    <= wbin_d;
            wgray_q   <= wgray_d;
         end
      end
   end

   assign o_early_full = wgray_next_d == {~rgray_sync[AWIDTH:AWIDTH-1],rgray_sync[AWIDTH-2:0]};
   assign o_full       = wgray_d == {~rgray_sync[AWIDTH:AWIDTH-1],rgray_sync[AWIDTH-2:0]};
   assign waddr        = wbin_q[AWIDTH-1:0];

   // ------------------------------------------------------------------------
   // Read Counter
   // ------------------------------------------------------------------------
   logic  max_loop_rptr;
   assign max_loop_rptr = i_loop_mode && (rbin_q == i_stop_ptr) ;

//   assign rbin_d  = i_read ? rbin_q + 'b1 : rbin_q;
   assign rbin_d       = i_load_ptr ? i_start_ptr :
                         i_read && max_loop_rptr ? i_start_ptr :
                         i_read ?  rbin_q + 'b1 : rbin_q;

   assign rgray_d = (rbin_d >> 1) ^ rbin_d;
   assign rbin_next_d  = rbin_d + 'b1 ;
   assign rgray_next_d = (rbin_next_d >> 1) ^ rbin_next_d;

   always_ff @(posedge rclk_g, posedge rrst_scan) begin
      if (rrst_scan) begin
         rbin_q       <= '0;
         rgray_q      <= '0;
         rgray_next_q <= '0;
      end else begin
         if (i_read) begin
            rbin_q       <= rbin_d;
            rgray_q      <= rgray_d;
            rgray_next_q <= rgray_next_d;
         end
      end
   end

   assign o_early_empty_n = (rgray_next_q != wgray_sync) & o_empty_n ;
   assign o_empty_n       = rgray_q != wgray_sync;
   assign raddr           = rbin_q[AWIDTH-1:0];
   // ------------------------------------------------------------------------
   // Synchronizers
   // ------------------------------------------------------------------------

   generate
     if (SYNC) begin : WR_SYNC
         assign wgray_sync = wgray_q;
     end else begin : WR_ASYNC
         ddr_demet_r wsync [AWIDTH+1] (
            .i_clk   (i_rclk),
            .i_rst   (rrst_scan),
            .i_d     (wgray_q),
            .o_q     (wgray_sync)
         );
     end
   endgenerate

   generate
     if (SYNC) begin : RD_SYNC
         assign rgray_sync = rgray_q;
     end else begin : RD_ASYNC
         ddr_demet_r rsync [AWIDTH+1] (
            .i_clk   (i_wclk),
            .i_rst   (wrst_scan),
            .i_d     (rgray_q),
            .o_q     (rgray_sync)
         );
     end
   endgenerate

endmodule
