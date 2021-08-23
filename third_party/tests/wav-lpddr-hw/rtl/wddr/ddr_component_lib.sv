
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
`include "ddr_project_define.vh"

import ddr_global_pkg::*;

module ddr_scan_rst (
   input  logic i_scan_rst_ctrl,
   input  logic i_rst,
   output logic o_rst
);

   logic scan_rst_ctrl_n ;
   ddr_inv   u_inv   (.i_a(i_scan_rst_ctrl), .o_z(scan_rst_ctrl_n));
   ddr_and   u_and   (.i_a(scan_rst_ctrl_n), .i_b(i_rst), .o_z(o_rst));

endmodule

module ddr_scan_clk_mux (
   input  logic i_scan_mode,
   input  logic i_scan_clk,
   input  logic i_clk,
   output logic o_clk
);

   ddr_mux u_mux (.i_sel(i_scan_mode), .i_a(i_clk), .i_b(i_scan_clk), .o_z(o_clk));

endmodule

module ddr_edge_det (
   input  logic  i_clk,
   input  logic  i_rst,
   input  logic  i_async,
   output logic  o_sync_pulse,
   output logic  o_sync
);

   logic sync_q;
   logic async_q;
   logic async_reset;

   assign async_reset = i_rst | (~i_async & o_sync);

   ddr_dff_r u_dff0    (.i_clk(i_async), .i_rst(async_reset), .i_d(1'b1) ,   .o_q(async_q));
   ddr_demet_r u_demet (.i_clk(i_clk),   .i_rst(i_rst),       .i_d(async_q), .o_q(o_sync));
   ddr_dff_r u_dff1    (.i_clk(i_clk),   .i_rst(i_rst),       .i_d(o_sync) , .o_q(sync_q));

   assign o_sync_pulse = o_sync & ~sync_q ;

endmodule

module ddr_sticky_reg (
   input  logic  i_clk,
   input  logic  i_rst,
   input  logic  i_clr,
   input  logic  i_d,
   output logic  o_q
);

   logic d_edge, d_sticky, clr_sync;

   ddr_edge_det u_edge_det (.i_clk(i_clk),.i_rst(i_rst),.i_async(i_d),.o_sync(d_edge),.o_sync_pulse());
   ddr_demet_r u_demet (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_clr), .o_q(clr_sync));

   assign d_sticky = d_edge | (~clr_sync & o_q);

   always_ff @(posedge i_clk, posedge i_rst) begin
      if (i_rst)
         o_q <= '0;
      else
         o_q <= d_sticky;
   end

endmodule

`timescale 1ps/1ps

module ddr_jitter_buf (
   input  logic        i_clk,
   input  int unsigned i_skew,
   input  int unsigned i_max_c2c_jit,
   input  int unsigned i_max_accum_jit,
   output logic        o_clk
);

`ifndef SYNTHESIS
   int unsigned accum_jit;
   int unsigned c2c_jit;

   initial begin
      accum_jit = 0;
      c2c_jit = 0;
      o_clk = 0;
   end

   always @(i_clk) begin
      if (i_clk) begin
         // Generate an unsigned random number
         c2c_jit = $urandom_range(i_max_c2c_jit);

         // Pick a random bit (23) bit for direction of jitter.
         accum_jit = c2c_jit[23] ? accum_jit + c2c_jit : accum_jit - c2c_jit;

         // Set accumulated jitter limits
         if (accum_jit > i_max_accum_jit)
            accum_jit = i_max_accum_jit;
         else if (accum_jit < 0)
            accum_jit = 0;

         // Use non-blocking statement to prevent filtering when delay is greater than even time
         o_clk <= #(accum_jit + i_skew) i_clk;
      end else begin
         // Use non-blocking statement to prevent filtering when delay is greater than even time
         o_clk <= #(i_skew) i_clk;
      end
   end
`else
   assign o_clk = i_clk;
`endif

endmodule

module ddr_mux_3to1 #(
   parameter DWIDTH = 1,
   parameter SWIDTH = 2*DWIDTH
) (
   input  logic [SWIDTH-1:0] i_sel,
   input  logic [DWIDTH-1:0] i_0,
   input  logic [DWIDTH-1:0] i_1,
   input  logic [DWIDTH-1:0] i_2,
   output logic [DWIDTH-1:0] o_z
);

   logic [DWIDTH-1:0] int_0;

   genvar i;
   generate
      for (i=0; i<DWIDTH; i++) begin: mux3to1
         ddr_mux u_mux_0 (.i_sel(i_sel[i*SWIDTH+:1]), .i_a(i_0[i]), .i_b(i_1[i]), .o_z(int_0[i]));
         ddr_mux u_mux_2 (.i_sel(i_sel[((i*SWIDTH)+1)+:1]), .i_a(int_0[i]), .i_b(i_2[i]), .o_z(o_z[i]));
      end
   endgenerate

endmodule

module ddr_mux_2to1 #(
   parameter DWIDTH = 1,
   parameter SWIDTH = 1*DWIDTH
) (
   input  logic [SWIDTH-1:0] i_sel,
   input  logic [DWIDTH-1:0] i_0,
   input  logic [DWIDTH-1:0] i_1,
   output logic [DWIDTH-1:0] o_z
);

   genvar i;
   generate
      for (i=0; i<DWIDTH; i++) begin: mux2to1
         ddr_mux u_mux (.i_sel(i_sel[i]), .i_a(i_0[i]), .i_b(i_1[i]), .o_z(o_z[i]));
      end
   endgenerate

endmodule

module ddr_mux_4to1 #(
   parameter DWIDTH = 1,
   parameter SWIDTH = 2*DWIDTH
) (
   input  logic [SWIDTH-1:0] i_sel,
   input  logic [DWIDTH-1:0] i_0,
   input  logic [DWIDTH-1:0] i_1,
   input  logic [DWIDTH-1:0] i_2,
   input  logic [DWIDTH-1:0] i_3,
   output logic [DWIDTH-1:0] o_z
);

   logic [DWIDTH-1:0] int_0, int_1;

   genvar i;
   generate
      for (i=0; i<DWIDTH; i++) begin: mux4to1
         ddr_mux u_mux_0 (.i_sel(i_sel[i*SWIDTH+:1]), .i_a(i_0[i]), .i_b(i_1[i]), .o_z(int_0[i]));
         ddr_mux u_mux_1 (.i_sel(i_sel[i*SWIDTH+:1]), .i_a(i_2[i]), .i_b(i_3[i]), .o_z(int_1[i]));
         ddr_mux u_mux_2 (.i_sel(i_sel[((i*SWIDTH)+1)+:1]), .i_a(int_0[i]), .i_b(int_1[i]), .o_z(o_z[i]));
      end
   endgenerate

endmodule

module ddr_mux_8to1 #(
   parameter DWIDTH = 1,
   parameter SWIDTH = 3*DWIDTH
) (
   input  logic [SWIDTH-1:0] i_sel,
   input  logic [DWIDTH-1:0] i_0,
   input  logic [DWIDTH-1:0] i_1,
   input  logic [DWIDTH-1:0] i_2,
   input  logic [DWIDTH-1:0] i_3,
   input  logic [DWIDTH-1:0] i_4,
   input  logic [DWIDTH-1:0] i_5,
   input  logic [DWIDTH-1:0] i_6,
   input  logic [DWIDTH-1:0] i_7,
   output logic [DWIDTH-1:0] o_z
);

   logic [DWIDTH-1:0] int_0, int_1, int_2, int_3, int_4, int_5;

   genvar i;
   generate
      for (i=0; i<DWIDTH; i++) begin: mux8to1
         ddr_mux u_mux_0 (.i_sel(i_sel[((i*SWIDTH)+0)+:1]), .i_a(i_0[i]), .i_b(i_1[i]), .o_z(int_0[i]));
         ddr_mux u_mux_1 (.i_sel(i_sel[((i*SWIDTH)+0)+:1]), .i_a(i_2[i]), .i_b(i_3[i]), .o_z(int_1[i]));
         ddr_mux u_mux_2 (.i_sel(i_sel[((i*SWIDTH)+0)+:1]), .i_a(i_4[i]), .i_b(i_5[i]), .o_z(int_2[i]));
         ddr_mux u_mux_3 (.i_sel(i_sel[((i*SWIDTH)+0)+:1]), .i_a(i_6[i]), .i_b(i_7[i]), .o_z(int_3[i]));

         ddr_mux u_mux_4 (.i_sel(i_sel[((i*SWIDTH)+1)+:1]), .i_a(int_0[i]), .i_b(int_1[i]), .o_z(int_4[i]));
         ddr_mux u_mux_5 (.i_sel(i_sel[((i*SWIDTH)+1)+:1]), .i_a(int_2[i]), .i_b(int_3[i]), .o_z(int_5[i]));

         ddr_mux u_mux_6 (.i_sel(i_sel[((i*SWIDTH)+2)+:1]), .i_a(int_4[i]), .i_b(int_5[i]), .o_z(o_z[i]));
      end
   endgenerate

endmodule

module ddr_func_mux_2to1 #(
   parameter DWIDTH = 1
) (
   input  logic [DWIDTH-1:0] i_clk_0,
   input  logic [DWIDTH-1:0] i_d0,
   input  logic [DWIDTH-1:0] i_d1,
   output logic [DWIDTH-1:0] o_q
);

   logic [DWIDTH-1:0] i_clk_180;
   logic [DWIDTH-1:0] l0, l1, l2;
   ddr_inv     u_inv_0 [DWIDTH-1:0] (.i_a  (i_clk_0),   .o_z(i_clk_180));
   ddr_latch u_latch_0 [DWIDTH-1:0] (.i_clk(i_clk_180), .i_d(i_d0), .o_q(l0)); // Half cycle setup time to mux
   ddr_latch u_latch_1 [DWIDTH-1:0] (.i_clk(i_clk_180), .i_d(i_d1), .o_q(l1));
   ddr_latch u_latch_2 [DWIDTH-1:0] (.i_clk(i_clk_0  ), .i_d(l1  ), .o_q(l2)); // Half cycle setup time to mux
   ddr_mux   u_mux     [DWIDTH-1:0] (.i_sel(i_clk_0  ), .i_a(l2  ), .i_b(l0), .o_z(o_q));

endmodule

module ddr_div2_rst (
   input  logic i_clk,
   input  logic i_rst,
   input  logic i_div_en,
   input  logic i_div_byp,
   output logic o_div2_clk
);

`ifdef DDR_LATCH_BASED_CDIV
   logic q0, q0_n, q1, q1_n, clk_n;
   logic div_en;

   ddr_inv     u_inv_0   (.i_a(i_clk), .o_z(clk_n));
   ddr_latch_r u_latch_0 (.i_rst(i_rst), .i_clk(clk_n), .i_d(q1), .o_q(q0));
   ddr_latch_r u_latch_1 (.i_rst(i_rst), .i_clk(clk_n), .i_d(i_div_en), .o_q(div_en));
   ddr_nand    u_nand    (.i_a(q0),.i_b(div_en),.o_z(q0_n));
   ddr_latch_s u_latch_2 (.i_set(i_rst), .i_clk(i_clk), .i_d(q0_n), .o_q(q1));
   ddr_inv     u_inv_1   (.i_a(q1), .o_z(q1_n));
   ddr_mux     u_mux     (.i_sel(i_div_byp), .i_a(q1_n), .i_b(i_clk), .o_z(o_div2_clk));
`else
   logic q, q_b, div_en_n, div_en;
   ddr_dff_r u_dff   (.i_clk (i_clk), .i_rst(i_rst), .i_d(q_b), .o_q(q));
   ddr_inv   u_inv_0 (.i_a(q), .o_z(q_b));
   ddr_inv   u_inv_1 (.i_a(i_div_en), .o_z(div_en_n));
   ddr_nor   u_nor   (.i_a(div_en_n), .i_b(i_div_byp),.o_z(div_en));
   ddr_mux   u_mux   (.i_sel(div_en), .i_a(i_clk), .i_b(q), .o_z(o_div2_clk));
`endif

endmodule

module ddr_clk_mux_gf (
   input  wire i_clk_0,
   input  wire i_clk_1,
   input  wire i_clk_rst_0,
   input  wire i_clk_rst_1,
   input  wire i_sel,
   input  wire i_test_en,
   input  wire i_cgc_en,
   output wire o_sel_0,
   output wire o_sel_1,
   output wire o_clk
);

   wire clk_out_or;
   wire clk0_en, clk1_en;
   wire clk0_out, clk1_out;
   wire clk0_en_sync, clk1_en_sync;
   wire clk0_en_sync_ff, clk1_en_sync_ff;
   wire clk0_en_sync_n, clk1_en_sync_n;

   assign clk0_en = ~(~i_sel & clk1_en_sync_ff);

   ddr_demet_r u_demet_0 (.i_clk(i_clk_0), .i_rst(i_clk_rst_0), .i_d(clk0_en), .o_q(clk0_en_sync));

   assign clk0_en_sync_n = ~clk0_en_sync;
   assign o_sel_0 = clk0_en_sync_n;

   ddr_dff_r u_dff_0 (.i_clk (i_clk_0), .i_rst(i_clk_rst_0), .i_d(clk0_en_sync), .o_q(clk0_en_sync_ff));
   ddr_cgc_rl u_cgc_0 (.i_clk(i_clk_0), .i_clk_en(clk0_en_sync_n), .i_cgc_en(i_cgc_en), .o_clk(clk0_out));

   assign clk1_en = ~(i_sel & clk0_en_sync_ff);

   ddr_demet_s u_demet_1 (.i_clk(i_clk_1), .i_set(i_clk_rst_1), .i_d(clk1_en), .o_q(clk1_en_sync));

   assign clk1_en_sync_n = ~clk1_en_sync;
   assign o_sel_1 = clk1_en_sync_n;

   ddr_dff_s u_dff_1 (.i_clk (i_clk_1), .i_set(i_clk_rst_1), .i_d(clk1_en_sync), .o_q(clk1_en_sync_ff));
   ddr_cgc_rl u_cgc_1 (.i_clk(i_clk_1), .i_clk_en(clk1_en_sync_n), .i_cgc_en(i_cgc_en), .o_clk(clk1_out));

   ddr_or u_clkor (.i_a(clk0_out), .i_b(clk1_out), .o_z(clk_out_or));
   ddr_mux u_clkmux (.i_sel(i_test_en), .i_a(clk_out_or), .i_b(i_clk_0), .o_z(o_clk));
   //cadence script_begin
   //set_db [get_db insts *u_dff_0] .preserve true
   //set_db [get_db insts *u_dff_1] .preserve true
   //cadence script_end

endmodule

module ddr_fc_dly #(
   parameter DWIDTH = 1,
   parameter FWIDTH = 2 ,
   parameter MAXDLY = (1 << FWIDTH)-1
) (
   input  logic                     i_clk,
   input  logic [FWIDTH-1:0]        i_delay,
   input  logic [DWIDTH-1:0]        i_d,
   output logic [DWIDTH-1:0]        o_q
);

   localparam integer DLY_WIDTH = 1'd1 << FWIDTH ;

   logic [MAXDLY-1:0] dly ;

   ddr_fc_dly_dec #(.IWIDTH(FWIDTH), .OWIDTH(MAXDLY)) u_fc_dly_dec (.i_dly(i_delay), .o_dly(dly));

   logic [DWIDTH-1:0] q [MAXDLY-1 :0] ;
   logic [DWIDTH-1:0] d [MAXDLY-1 :0] ;
   genvar i ;
   generate
     for (i = MAXDLY-1; i >= 0 ; i-- ) begin : PIPE
        if(i== MAXDLY-1) begin: PIPE1
           ddr_dff u_dff [DWIDTH-1:0] (.i_clk({DWIDTH{i_clk}}), .i_d(i_d), .o_q(q[i]));
        end else begin: PIPE
           ddr_dff u_dff [DWIDTH-1:0] (.i_clk({DWIDTH{i_clk}}), .i_d(d[i]), .o_q(q[i]));
        end
     end
     for (i = MAXDLY-1; i > 0 ; i-- ) begin : MUX
        ddr_mux u_mux [DWIDTH-1:0] (.i_sel({DWIDTH{dly[i]}}), .i_a(i_d), .i_b(q[i])  , .o_z(d[i-1]));
     end
   endgenerate

   ddr_mux u_mux_out [DWIDTH-1:0] (.i_sel({DWIDTH{dly[0]}}), .i_a(i_d), .i_b(q[0])  , .o_z(o_q));

endmodule

module ddr_fc_dly_dec #(
   parameter integer IWIDTH = 2,
   parameter integer OWIDTH = (1 << IWIDTH)-1
)(
   input  logic [IWIDTH-1:0] i_dly,
   output logic [OWIDTH-1:0] o_dly
);

   assign o_dly = ~({OWIDTH{1'b1}} << i_dly) ;

endmodule

module ddr_lpde #(
   parameter LWIDTH = 4,              // Stage delay select width
   parameter WIDTH  = 2 ** LWIDTH,    // Number of stage delays
   parameter PS_DLY = 10              // NAND delay in picoseconds
) (
   input  logic              i_d,     // Input to delay
   input  logic [LWIDTH-1:0] i_delay, // Stage delay selection
   output logic              o_d      // Output to delay
);

   // ------------------------------------------------------------------------
   // Delay Logic
   // ------------------------------------------------------------------------

   logic [WIDTH:0]   r;
   logic [WIDTH-1:0] f;
   logic [WIDTH-1:0] bc, fc;

   // Forward control fixed to 1
   assign fc = '1;
   // Backward control enable only for desired stage delay (single bit)
   assign bc =  i_delay == '0 ? '0 : 'b1 << (i_delay - 'd1);
   // Reverse delay toggled based on bc enable polarity
   assign r[WIDTH] = ~i_delay[0];

   genvar i;
   generate
      for (i=0; i<WIDTH; i++) begin: delay
         if (i==0) begin: stage_0
            // First stage
            ddr_lpde_stage #(.PS_DLY(PS_DLY)) u_nand_stage (.p(i_d)   ,.n(r[i+1]),.fc(fc[i]),.bc(bc[i]),.f(f[i]),.r(r[i]));
         end else begin: stage_x
            // Sequential stage
            ddr_lpde_stage #(.PS_DLY(PS_DLY)) u_nand_stage (.p(f[i-1]),.n(r[i+1]),.fc(fc[i]),.bc(bc[i]),.f(f[i]),.r(r[i]));
         end
      end
   endgenerate

   // Delay from trombone loopback output
   ddr_inv u_inv_0 (.i_a(r[0]),.o_z(o_d));

endmodule

module ddr_lpde_stage #(
   parameter PS_DLY = 0
) (
   input  logic p,   // Previous stage forward
   input  logic n,   // Next stage reverse
   input  logic fc,  // Forward path control
   input  logic bc,  // Backward path control
   output logic f,   // Forward path
   output logic r    // Reverse path
);

   logic b;

   ddr_nand #(.PS_DLY(PS_DLY)) u_nand_f (.i_a(p),.i_b(fc),.o_z(f));
   ddr_nand #(.PS_DLY(PS_DLY)) u_nand_b (.i_a(f),.i_b(bc),.o_z(b));
   ddr_nand #(.PS_DLY(PS_DLY)) u_nand_r (.i_a(b),.i_b(n) ,.o_z(r));

endmodule

module ddr_ram_sp #(
   parameter DWIDTH = 32,              // Data width
   parameter SIZE   = 256,             // RAM size in DWIDTHs
   parameter BWIDTH = 8,               // Byte width
   parameter DWORDS = DWIDTH/BWIDTH,   // Data Words per DWIDTH
   parameter AWIDTH = $clog2(SIZE)     // Address width
) (
   input  logic               i_clk,
   input  logic [AWIDTH-1:0]  i_addr,
   input  logic               i_en,
   input  logic               i_we,
   input  logic [DWORDS-1:0]  i_be,
   input  logic [DWIDTH-1:0]  i_wdata,
   output logic [DWIDTH-1:0]  o_rdata
);

   logic [DWORDS-1:0][BWIDTH-1:0] mem [SIZE-1:0];
   logic write, read;
   logic [AWIDTH-1:0] addr_q;

   assign write = i_en &  i_we;
   assign read  = i_en & ~i_we;

   integer i;
   always_ff @(posedge i_clk) begin
      if (write)
         for (i=0; i<DWORDS; i=i+1)
            if (i_be[i])
               mem[i_addr][i] <= i_wdata[i*BWIDTH +: BWIDTH];
   end

   always_ff @(posedge i_clk) begin
      if (read)
         addr_q <= i_addr;
   end

   assign o_rdata = read ? mem[i_addr] : mem[addr_q];

endmodule

module ddr_ram_dp #(
   parameter DWIDTH = 32,              // Data width
   parameter SIZE   = 256,             // RAM size in DWIDTHs
   parameter BWIDTH = 8,               // Byte width
   parameter DWORDS = DWIDTH/BWIDTH,   // Data Words per DWIDTH
   parameter AWIDTH = $clog2(SIZE)     // Address width
) (
   input  logic               i_clk_0,
   input  logic [AWIDTH-1:0]  i_addr_0,
   input  logic               i_en_0,
   input  logic               i_we_0,
   input  logic [DWORDS-1:0]  i_be_0,
   input  logic [DWIDTH-1:0]  i_wdata_0,
   output logic [DWIDTH-1:0]  o_rdata_0,

   input  logic               i_clk_1,
   input  logic [AWIDTH-1:0]  i_addr_1,
   input  logic               i_en_1,
   input  logic               i_we_1,
   input  logic [DWORDS-1:0]  i_be_1,
   input  logic [DWIDTH-1:0]  i_wdata_1,
   output logic [DWIDTH-1:0]  o_rdata_1
);

   logic [DWORDS-1:0][BWIDTH-1:0] mem [SIZE-1:0];
   logic write_0, read_0;
   logic write_1, read_1;
   logic [AWIDTH-1:0] addr_0_q, addr_1_q;

   assign write_0 = i_en_0 &  i_we_0;
   assign read_0  = i_en_0 & ~i_we_0;

   integer i;
   always_ff @(posedge i_clk_0) begin
      if (write_0)
         for (i=0; i<DWORDS; i=i+1)
            if (i_be_0[i])
               mem[i_addr_0][i] <= i_wdata_0[i*BWIDTH +: BWIDTH];
   end

   always_ff @(posedge i_clk_0) begin
      if (read_0)
         addr_0_q <= i_addr_0;
   end

   assign o_rdata_0 = read_0 ? mem[i_addr_0] : mem[addr_0_q];

   assign write_1 = i_en_1 &  i_we_1;
   assign read_1  = i_en_1 & ~i_we_1;

   integer j;
   always_ff @(posedge i_clk_1) begin
      if (write_1)
         for (j=0; j<DWORDS; j=j+1)
            if (i_be_1[j])
               mem[i_addr_1][j] <= i_wdata_1[j*BWIDTH +: BWIDTH];
   end

   always_ff @(posedge i_clk_1) begin
      if (read_1)
         addr_1_q <= i_addr_1;
   end

   assign o_rdata_1 = read_1 ? mem[i_addr_1] : mem[addr_1_q];

endmodule

module ddr_priority_enc #(
   parameter       DWIDTH   = 4,
   parameter       EWIDTH   = $clog2(DWIDTH),
   parameter [0:0] PIPELINE = 1'b1
) (
   input   logic              i_clk,
   input   logic              i_rst,
   input   logic [DWIDTH-1:0] i_dec,
   output  logic [EWIDTH-1:0] o_enc
);

   logic [DWIDTH-1:0] dec,dec_q;

   always_ff @(posedge i_clk, posedge i_rst) begin
      if (i_rst)
         dec_q <= '0;
      else
         dec_q <= i_dec;
   end

   assign dec = PIPELINE ? dec_q : i_dec;

   integer i;
   always_comb begin
     o_enc = '0;
     for (i = 0; i < DWIDTH; i = i + 1)
         if (dec[i])
            o_enc = i[EWIDTH-1:0];
   end

endmodule

module ddr_pad_tx_se (
   input  logic i_core_eg,
   input  logic i_pad_oe,
   inout  wire  pad
);

   assign pad = i_pad_oe ? i_core_eg : 'bz;

`ifdef DDR_IO_PULL
   pulldown u_pull (pad);
`endif

endmodule

module ddr_pad_tx_diff (
   input  logic i_core_eg,
   input  logic i_pad_oe,
   inout  wire  pad_t,
   inout  wire  pad_c
);

   assign pad_t = i_pad_oe ?  i_core_eg : 'bz;
   assign pad_c = i_pad_oe ? ~i_core_eg : 'bz;

`ifdef DDR_IO_PULL
   pulldown u_pull_t (pad_t);
   pullup   u_pull_c (pad_c);
`endif

endmodule

module ddr_pad_rx_se (
   input  logic i_pad_ie,
   input  logic i_pad_re,
   output logic o_core_ig,
   inout  wire  pad
);

   assign o_core_ig   = i_pad_ie & i_pad_re ? pad : 'b0;

endmodule

module ddr_pad_rx_diff (
   input  logic i_pad_ie,
   input  logic i_pad_re,
   output logic o_core_ig,
   output logic o_core_ig_b,
   inout  wire  pad_t,
   inout  wire  pad_c
);

   assign o_core_ig   = i_pad_ie & i_pad_re ? pad_t : 'b0;
   assign o_core_ig_b = i_pad_ie & i_pad_re ? pad_c : 'b0;

endmodule

module ddr_dp_wop2pow #(
   parameter WIDTH  = 1,             // Parallel bus width
   parameter NUM_PH = 4,             // Number of data phases
   parameter DWIDTH = WIDTH * NUM_PH
) (
   input  logic [DWIDTH-1:0] i_d,
   output logic [DWIDTH-1:0] o_d
);

   integer i,j;
   // Convert Words-Of-Phases (WOP) to Phases-Of-Words (POW)
   always_comb
      for (j=0; j<NUM_PH; j++)
         for (i=0; i<WIDTH; i++)
            o_d[(j*WIDTH)+i] = i_d[(i*NUM_PH)+j];
endmodule

module ddr_dp_pow2wop #(
   parameter WIDTH  = 1,             // Parallel bus width
   parameter NUM_PH = 4,             // Number of data phases
   parameter DWIDTH = WIDTH * NUM_PH
) (
   input  logic [DWIDTH-1:0] i_d,
   output logic [DWIDTH-1:0] o_d
);

   integer i,j;
   // Convert Phases-Of-Words (POW) to Words-Of-Phases (WOP)
   always_comb
      for (i=0; i<WIDTH; i++)
         for (j=0; j<NUM_PH; j++)
            o_d[(i*NUM_PH)+j] = i_d[(j*WIDTH)+i];
endmodule

module ddr_dp_dbi #(
   parameter       WIDTH  = 8,              // Parallel bus width
   parameter       NUM_PH = 4,              // Number of data phases
   parameter [0:0] EGRESS = 1'b0,           // 0: Ingress, 1: Egress
   parameter       DWIDTH = NUM_PH * WIDTH  // Read data width
) (

   input  logic                    i_clk,
   input  logic                    i_rst,

   // Receiver
   input  logic                    i_dbi_en,
   input  logic                    i_dbi_ones,
   input  logic                    i_dbi_pipe_en,
   input  logic [WIDTH-1:0]        i_dbi_mask,
   input  logic [DWIDTH-1:0]       i_sdr,
   output logic [DWIDTH-1:0]       o_sdr,
   input  logic [NUM_PH-1:0]       i_sdr_dbi,
   output logic [NUM_PH-1:0]       o_sdr_dbi
);

   // ------------------------------------------------------------------------
   // DBI
   // ------------------------------------------------------------------------

   genvar i;
   generate
      for (i=0; i<NUM_PH; i++) begin : DBI
         ddr_dbi #(
            .DWIDTH           (WIDTH),
            .EGRESS           (EGRESS)
         ) u_dbi (
            .i_clk            (i_clk),
            .i_rst            (i_rst),
            .i_dbi_en         (i_dbi_en),
            .i_dbi_ones       (i_dbi_ones),
            .i_dbi_mask       (i_dbi_mask),
            .i_dbi_pipe_en    (i_dbi_pipe_en),
            .i_dbi            (i_sdr_dbi[i]),
            .i_bus            (i_sdr[i*WIDTH+:WIDTH]),
            .o_dbi            (o_sdr_dbi[i]),
            .o_bus            (o_sdr[i*WIDTH+:WIDTH])
         );
      end
   endgenerate

endmodule

module ddr_dbi #(
   parameter       DWIDTH = 16,   // Bus Width
   parameter [0:0] EGRESS = 1'b1  // DBI   1: Egress, 0: Ingress
) (
   input  logic              i_clk,
   input  logic              i_rst,
   input  logic              i_dbi_en,
   input  logic              i_dbi_ones,
   input  logic              i_dbi_pipe_en,
   input  logic [DWIDTH-1:0] i_dbi_mask,
   input  logic              i_dbi,
   input  logic [DWIDTH-1:0] i_bus,
   output logic              o_dbi,
   output logic [DWIDTH-1:0] o_bus
);

   localparam AWIDTH = $clog2(DWIDTH) + 'd1;

   logic [AWIDTH-1:0] count, count_msk;
   logic [DWIDTH-1:0] bus, bus_d, bus_q, bus_mask;
   logic dbi_d, dbi_q;

   assign bus_mask = ~i_dbi_mask;

   // Select ONES or ZEROS to count and mask
   assign bus = bus_mask & (i_dbi_ones ? i_bus : ~i_bus);

   // Count the number of ones or zeros
   integer i;
   always_comb begin
      count = 0;                               // Initialize count variable.
      for(i=0; i<DWIDTH; i++)                  // For all the bits...
         count = count + bus[i];               // Add the bit to the count.
   end

   // Count the number of unmasked bits
   integer j;
   always_comb begin
      count_msk = 0;                           // Initialize count variable.
      for(j=0; j<DWIDTH; j++) begin            // For all the bits...
         count_msk = count_msk + bus_mask[j];  // Add the bit to the count.
      end
   end

   // SPEC[GDDR4] :: 4.2 - CABI
   // Determine inversion requirement
   assign dbi_d = i_dbi_en & (EGRESS ? count > (count_msk>>1) : i_dbi);

   // Perform the data bus inversion
   assign bus_d = ({DWIDTH{dbi_d}} & bus_mask) ^ i_bus;

   // Pipeline for timing
   always_ff @(posedge i_clk, posedge i_rst) begin
      if (i_rst) begin
         bus_q <= '0;
         dbi_q <= '0;
      end else begin
         bus_q <= bus_d;
         dbi_q <= dbi_d;
      end
   end

   // Programmable pipeline
   assign o_bus = i_dbi_pipe_en ? bus_q : bus_d;
   assign o_dbi = 1'b0 ? dbi_q : dbi_d;

endmodule

// Clock Branch Cell - Clock/Reset timing for UAR
module ddr_cbc #(
   parameter CLKSTOPRST_ASSERT_EN  = 1,   // Asserts output rst in clock stop window. when 0, asserts reset asynchronous before clock is gated.
   parameter CLK_OFF_CYCLES     = 16,
   parameter RST_ON_CYCLE       = 5,    // Must be < RST_OFF_CYCLE
   parameter RST_OFF_CYCLE      = 9    // Must be > RST_ON_CYCLE
) (
   input  logic               i_clk,
   input  logic               i_rst,
   input  logic               i_cgc_en,
   input  logic               i_scan_rst_ctrl,
   output logic               o_clk,
   output logic               o_rst
);

   localparam CWIDTH = $clog2(CLK_OFF_CYCLES);

   logic [CWIDTH-1:0] cnt_q;
   logic clk_on, rst_on;
   logic rst_q, rst_sync;

  wav_reset_sync u_reset_sync (
    .clk           ( i_clk           ),
    .scan_ctrl     ( i_scan_rst_ctrl ),
    .reset_in      ( i_rst           ),
    .reset_out     ( rst_sync        )
  );

  always_ff @(posedge i_clk, posedge rst_sync) begin
      if (rst_sync)
         cnt_q <= '0;
      else
         if (cnt_q < (CLK_OFF_CYCLES - 1))
            cnt_q <= cnt_q + 'd1;
   end

   assign clk_on = cnt_q == (CLK_OFF_CYCLES - 1);
   ddr_cgc_rl u_cgc (.i_clk(i_clk), .i_clk_en(clk_on), .i_cgc_en(i_cgc_en), .o_clk(o_clk));

   assign rst_on = (CLKSTOPRST_ASSERT_EN == 1) ? ((cnt_q >= RST_ON_CYCLE) & (cnt_q <= RST_OFF_CYCLE)) : (cnt_q <= RST_OFF_CYCLE);

   always_ff @(posedge i_clk, posedge rst_sync) begin
      if (rst_sync)
         rst_q <= !CLKSTOPRST_ASSERT_EN;
      else
         rst_q <= rst_on;
   end

   ddr_scan_rst u_scan_rst     (.i_scan_rst_ctrl(i_scan_rst_ctrl), .i_rst(rst_q), .o_rst(o_rst    ));

endmodule
