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

`ifndef WAV_COMPONENT_LIB
`define WAV_COMPONENT_LIB

module wav_scan_rst_mux (
   input  logic i_scan_mode,
   input  logic i_scan_rst_ctrl,
   input  logic i_rst,
   output logic o_rst
);

   wav_mux u_mux (.i_sel(i_scan_mode), .i_a(i_rst), .i_b(i_scan_rst_ctrl), .o_z(o_rst));

endmodule

module wav_scan_clk_mux (
   input  logic i_scan_mode,
   input  logic i_scan_clk,
   input  logic i_clk,
   output logic o_clk
);

   wav_mux u_mux (.i_sel(i_scan_mode), .i_a(i_clk), .i_b(i_scan_clk), .o_z(o_clk));

endmodule

module wav_edge_det (
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

   wav_dff_r u_dff0    (.i_clk(i_async), .i_rst(async_reset), .i_d(1'b1) ,   .o_q(async_q));
   wav_demet_r u_demet (.i_clk(i_clk),   .i_rst(i_rst),       .i_d(async_q), .o_q(o_sync));
   wav_dff_r u_dff1    (.i_clk(i_clk),   .i_rst(i_rst),       .i_d(o_sync) , .o_q(sync_q));

   assign o_sync_pulse = o_sync & ~sync_q ;

endmodule

module wav_sticky_reg (
   input  logic  i_clk,
   input  logic  i_rst,
   input  logic  i_clr,
   input  logic  i_d,
   output logic  o_q
);

   logic d_edge, d_sticky, clr_sync;

   wav_edge_det u_edge_det (.i_clk(i_clk),.i_rst(i_rst),.i_async(i_d),.o_sync(d_edge),.o_sync_pulse());
   wav_demet_r u_demet (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_clr), .o_q(clr_sync));

   assign d_sticky = d_edge | (~clr_sync & o_q);

   always_ff @(posedge i_clk, posedge i_rst) begin
      if (i_rst)
         o_q <= '0;
      else
         o_q <= d_sticky;
   end

endmodule

`timescale 1ps/1ps

module wav_jitter_buf (
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

module wav_mux_3to1 #(
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
         wav_mux u_mux_0 (.i_sel(i_sel[i*SWIDTH+:1]), .i_a(i_0[i]), .i_b(i_1[i]), .o_z(int_0[i]));
         wav_mux u_mux_2 (.i_sel(i_sel[((i*SWIDTH)+1)+:1]), .i_a(int_0[i]), .i_b(i_2[i]), .o_z(o_z[i]));
      end
   endgenerate

endmodule

module wav_mux_2to1 #(
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
         wav_mux u_mux (.i_sel(i_sel[i]), .i_a(i_0[i]), .i_b(i_1[i]), .o_z(o_z[i]));
      end
   endgenerate

endmodule

module wav_mux_4to1 #(
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
         wav_mux u_mux_0 (.i_sel(i_sel[i*SWIDTH+:1]), .i_a(i_0[i]), .i_b(i_1[i]), .o_z(int_0[i]));
         wav_mux u_mux_1 (.i_sel(i_sel[i*SWIDTH+:1]), .i_a(i_2[i]), .i_b(i_3[i]), .o_z(int_1[i]));
         wav_mux u_mux_2 (.i_sel(i_sel[((i*SWIDTH)+1)+:1]), .i_a(int_0[i]), .i_b(int_1[i]), .o_z(o_z[i]));
      end
   endgenerate

endmodule

module wav_mux_8to1 #(
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
         wav_mux u_mux_0 (.i_sel(i_sel[((i*SWIDTH)+0)+:1]), .i_a(i_0[i]), .i_b(i_1[i]), .o_z(int_0[i]));
         wav_mux u_mux_1 (.i_sel(i_sel[((i*SWIDTH)+0)+:1]), .i_a(i_2[i]), .i_b(i_3[i]), .o_z(int_1[i]));
         wav_mux u_mux_2 (.i_sel(i_sel[((i*SWIDTH)+0)+:1]), .i_a(i_4[i]), .i_b(i_5[i]), .o_z(int_2[i]));
         wav_mux u_mux_3 (.i_sel(i_sel[((i*SWIDTH)+0)+:1]), .i_a(i_6[i]), .i_b(i_7[i]), .o_z(int_3[i]));

         wav_mux u_mux_4 (.i_sel(i_sel[((i*SWIDTH)+1)+:1]), .i_a(int_0[i]), .i_b(int_1[i]), .o_z(int_4[i]));
         wav_mux u_mux_5 (.i_sel(i_sel[((i*SWIDTH)+1)+:1]), .i_a(int_2[i]), .i_b(int_3[i]), .o_z(int_5[i]));

         wav_mux u_mux_6 (.i_sel(i_sel[((i*SWIDTH)+2)+:1]), .i_a(int_4[i]), .i_b(int_5[i]), .o_z(o_z[i]));
      end
   endgenerate

endmodule

module wav_func_mux_2to1 #(
   parameter DWIDTH = 1
) (
   input  logic [DWIDTH-1:0] i_clk_0,
   input  logic [DWIDTH-1:0] i_clk_180,
   input  logic [DWIDTH-1:0] i_d0,
   input  logic [DWIDTH-1:0] i_d1,
   output logic [DWIDTH-1:0] o_q
);

   logic [DWIDTH-1:0] l0, l1, l2;
   wav_latch u_latch_0 [DWIDTH-1:0] (.i_clk(i_clk_180), .i_d(i_d0), .o_q(l0)); // Half cycle setup time to mux
   wav_latch u_latch_1 [DWIDTH-1:0] (.i_clk(i_clk_180), .i_d(i_d1), .o_q(l1));
   wav_latch u_latch_2 [DWIDTH-1:0] (.i_clk(i_clk_0  ), .i_d(l1  ), .o_q(l2)); // Half cycle setup time to mux
   wav_mux   u_mux     [DWIDTH-1:0] (.i_sel(i_clk_0  ), .i_a(l2  ), .i_b(l0), .o_z(o_q));

endmodule

module wav_div2_rst (
   input  logic i_clk,
   input  logic i_rst,
   input  logic i_div_en,
   input  logic i_div_byp,
   output logic o_div2_clk
);

`ifdef WAV_LATCH_BASED_CDIV
   logic q0, q0_n, q1, q1_n, clk_n;
   logic div_en;

   wav_inv     u_inv_0   (.i_a(i_clk), .o_z(clk_n));
   wav_latch_r u_latch_0 (.i_rst(i_rst), .i_clk(clk_n), .i_d(q1), .o_q(q0));
   wav_latch_r u_latch_1 (.i_rst(i_rst), .i_clk(clk_n), .i_d(i_div_en), .o_q(div_en));
   wav_nand    u_nand    (.i_a(q0),.i_b(div_en),.o_z(q0_n));
   wav_latch_s u_latch_2 (.i_set(i_rst), .i_clk(i_clk), .i_d(q0_n), .o_q(q1));
   wav_inv     u_inv_1   (.i_a(q1), .o_z(q1_n));
   wav_mux     u_mux     (.i_sel(i_div_byp), .i_a(q1_n), .i_b(i_clk), .o_z(o_div2_clk));
`else
   logic q, q_b, div_en_n, div_en;
   wav_dff_r u_dff   (.i_clk (i_clk), .i_rst(i_rst), .i_d(q_b), .o_q(q));
   wav_inv   u_inv_0 (.i_a(q), .o_z(q_b));
   wav_inv   u_inv_1 (.i_a(i_div_en), .o_z(div_en_n));
   wav_nor   u_nor   (.i_a(div_en_n), .i_b(i_div_byp),.o_z(div_en));
   wav_mux   u_mux   (.i_sel(div_en), .i_a(i_clk), .i_b(q), .o_z(o_div2_clk));
`endif

endmodule

module wav_clk_mux_gf (
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

   wav_demet_r u_demet_0 (.i_clk(i_clk_0), .i_rst(i_clk_rst_0), .i_d(clk0_en), .o_q(clk0_en_sync));

   assign clk0_en_sync_n = ~clk0_en_sync;
   assign o_sel_0 = clk0_en_sync_n;

   wav_dff_r u_dff_0 (.i_clk (i_clk_0), .i_rst(i_clk_rst_0), .i_d(clk0_en_sync), .o_q(clk0_en_sync_ff));
   wav_cgc_rl u_cgc_0 (.i_clk(i_clk_0), .i_clk_en(clk0_en_sync_n), .i_cgc_en(i_cgc_en), .o_clk(clk0_out));

   assign clk1_en = ~(i_sel & clk0_en_sync_ff);

   wav_demet_s u_demet_1 (.i_clk(i_clk_1), .i_set(i_clk_rst_1), .i_d(clk1_en), .o_q(clk1_en_sync));

   assign clk1_en_sync_n = ~clk1_en_sync;
   assign o_sel_1 = clk1_en_sync_n;

   wav_dff_s u_dff_1 (.i_clk (i_clk_1), .i_set(i_clk_rst_1), .i_d(clk1_en_sync), .o_q(clk1_en_sync_ff));
   wav_cgc_rl u_cgc_1 (.i_clk(i_clk_1), .i_clk_en(clk1_en_sync_n), .i_cgc_en(i_cgc_en), .o_clk(clk1_out));

   wav_or u_clkor (.i_a(clk0_out), .i_b(clk1_out), .o_z(clk_out_or));
   wav_mux u_clkmux (.i_sel(i_test_en), .i_a(clk_out_or), .i_b(i_clk_0), .o_z(o_clk));
   //cadence script_begin
   //set_db [get_db insts *u_dff_0] .preserve true
   //set_db [get_db insts *u_dff_1] .preserve true
   //cadence script_end

endmodule

module wav_fc_dly #(
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

   wav_fc_dly_dec #(.IWIDTH(FWIDTH), .OWIDTH(MAXDLY)) u_fc_dly_dec (.i_dly(i_delay), .o_dly(dly));

   logic [DWIDTH-1:0] q [MAXDLY-1 :0] ;
   logic [DWIDTH-1:0] d [MAXDLY-1 :0] ;
   genvar i ;
   generate
     for (i = MAXDLY-1; i >= 0 ; i-- ) begin : PIPE
        if(i== MAXDLY-1) begin: PIPE1
           wav_dff u_dff [DWIDTH-1:0] (.i_clk({DWIDTH{i_clk}}), .i_d(i_d), .o_q(q[i]));
        end else begin: PIPE
           wav_dff u_dff [DWIDTH-1:0] (.i_clk({DWIDTH{i_clk}}), .i_d(d[i]), .o_q(q[i]));
        end
     end
     for (i = MAXDLY-1; i > 0 ; i-- ) begin : MUX
        wav_mux u_mux [DWIDTH-1:0] (.i_sel({DWIDTH{dly[i]}}), .i_a(i_d), .i_b(q[i])  , .o_z(d[i-1]));
     end
   endgenerate

   wav_mux u_mux_out [DWIDTH-1:0] (.i_sel({DWIDTH{dly[0]}}), .i_a(i_d), .i_b(q[0])  , .o_z(o_q));

endmodule

module wav_fc_dly_dec #(
   parameter integer IWIDTH = 2,
   parameter integer OWIDTH = (1 << IWIDTH)-1
)(
   input  logic [IWIDTH-1:0] i_dly,
   output logic [OWIDTH-1:0] o_dly
);

   assign o_dly = ~({OWIDTH{1'b1}} << i_dly) ;

endmodule

module wav_lpde #(
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
            wav_lpde_stage #(.PS_DLY(PS_DLY)) u_nand_stage (.p(i_d)   ,.n(r[i+1]),.fc(fc[i]),.bc(bc[i]),.f(f[i]),.r(r[i]));
         end else begin: stage_x
            // Sequential stage
            wav_lpde_stage #(.PS_DLY(PS_DLY)) u_nand_stage (.p(f[i-1]),.n(r[i+1]),.fc(fc[i]),.bc(bc[i]),.f(f[i]),.r(r[i]));
         end
      end
   endgenerate

   // Delay from trombone loopback output
   wav_inv u_inv_0 (.i_a(r[0]),.o_z(o_d));

endmodule

module wav_lpde_stage #(
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

   wav_nand #(.PS_DLY(PS_DLY)) u_nand_f (.i_a(p),.i_b(fc),.o_z(f));
   wav_nand #(.PS_DLY(PS_DLY)) u_nand_b (.i_a(f),.i_b(bc),.o_z(b));
   wav_nand #(.PS_DLY(PS_DLY)) u_nand_r (.i_a(b),.i_b(n) ,.o_z(r));

endmodule

module wav_ram_sp #(
   parameter     DWIDTH   = 32,              // Data width
   parameter     SIZE     = 256,             // RAM size in DWIDTHs
   parameter     BWIDTH   = 8,               // Byte width
   parameter     DWORDS   = DWIDTH/BWIDTH,   // Data Words per DWIDTH
   parameter     AWIDTH   = $clog2(SIZE),    // Address width
   parameter bit PIPELINE = 0                // Pipeline enable
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

   assign write = i_en &  i_we;
   assign read  = i_en & ~i_we;

   integer i;
   always_ff @(posedge i_clk) begin
      if (write)
         for (i=0; i<DWORDS; i=i+1)
            if (i_be[i])
               mem[i_addr][i] <= i_wdata[i*BWIDTH +: BWIDTH];
   end

   if (PIPELINE) begin : pipe
      always_ff @(posedge i_clk) begin
         if (read)
            o_rdata <= mem[i_addr];
      end
   end else begin : no_pipe
      logic [AWIDTH-1:0] addr_q;
      always_ff @(posedge i_clk) begin
         if (read)
            addr_q <= i_addr;
      end
      assign o_rdata = read ? mem[i_addr] : mem[addr_q];
   end

`ifndef SYNTHESIS
   task loadmem;
      input [1000*8-1:0] filename;
      begin
         $readmemb(filename, mem);
      end
   endtask
`endif

endmodule

module wav_ram_dp #(
   parameter     DWIDTH   = 32,             // Data width
   parameter     SIZE     = 256,            // RAM size in DWIDTHs
   parameter     BWIDTH   = 8,              // Byte width
   parameter     DWORDS   = DWIDTH/BWIDTH,  // Data Words per DWIDTH
   parameter     AWIDTH   = $clog2(SIZE),   // Address width
   parameter bit PIPELINE = 0               // Pipeline enable
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

   if (PIPELINE) begin : pipe_0
      always_ff @(posedge i_clk_0) begin
         if (read_0)
            o_rdata_0 <= mem[i_addr_0];
      end
   end else begin : no_pipe_0
      logic [AWIDTH-1:0] addr_0_q;
      always_ff @(posedge i_clk_0) begin
         if (read_0)
            addr_0_q <= i_addr_0;
      end
      assign o_rdata_0 = read_0 ? mem[i_addr_0] : mem[addr_0_q];
   end

   assign write_1 = i_en_1 &  i_we_1;
   assign read_1  = i_en_1 & ~i_we_1;

   integer j;
   always_ff @(posedge i_clk_1) begin
      if (write_1)
         for (j=0; j<DWORDS; j=j+1)
            if (i_be_1[j])
               mem[i_addr_1][j] <= i_wdata_1[j*BWIDTH +: BWIDTH];
   end

   if (PIPELINE) begin : pipe_1
      always_ff @(posedge i_clk_1) begin
         if (read_1)
            o_rdata_1 <= mem[i_addr_1];
      end
   end else begin : no_pipe_1
      logic [AWIDTH-1:0] addr_1_q;
      always_ff @(posedge i_clk_1) begin
         if (read_1)
            addr_1_q <= i_addr_1;
      end
      assign o_rdata_1 = read_1 ? mem[i_addr_1] : mem[addr_1_q];
   end

`ifndef SYNTHESIS
   task loadmem;
      input [1000*8-1:0] filename;
      begin
         $readmemb(filename, mem);
      end
   endtask
`endif

endmodule

module wav_priority_enc #(
   parameter       DWIDTH   = 4,      //put it at one, I dare you
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

module wav_pad_tx_se (
   input  logic i_core_eg,
   input  logic i_pad_oe,
   inout  wire  pad
);

   assign pad = i_pad_oe ? i_core_eg : 'bz;

`ifdef wav_IO_PULL
   pulldown u_pull (pad);
`endif

endmodule

module wav_pad_tx_diff (
   input  logic i_core_eg,
   input  logic i_pad_oe,
   inout  wire  pad_t,
   inout  wire  pad_c
);

   assign pad_t = i_pad_oe ?  i_core_eg : 'bz;
   assign pad_c = i_pad_oe ? ~i_core_eg : 'bz;

`ifdef wav_IO_PULL
   pulldown u_pull_t (pad_t);
   pullup   u_pull_c (pad_c);
`endif

endmodule

module wav_pad_rx_se (
   input  logic i_pad_ie,
   input  logic i_pad_re,
   output logic o_core_ig,
   inout  wire  pad
);

   assign o_core_ig   = i_pad_ie & i_pad_re ? pad : 'b0;

endmodule

module wav_pad_rx_diff (
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

module wav_dp_wop2pow #(
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

module wav_dp_pow2wop #(
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

module wav_dp_dbi #(
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
         wav_dbi #(
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

module wav_dbi #(
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

module fifo_top2 #(
  parameter                   DATA_SIZE     = 40,
  parameter                   ADDR_SIZE     = 4
)(
  input  wire                 wclk,
  input  wire                 wreset,
  input  wire                 winc,
  input  wire                 rclk,
  input  wire                 rreset,
  input  wire                 rinc,
  input  wire [DATA_SIZE-1:0] wdata,
  output wire [DATA_SIZE-1:0] rdata,
  output wire                 wfull,
  output wire                 rempty,

  output wire [ADDR_SIZE:0]   rbin_ptr,
  output wire [ADDR_SIZE+1:0] rdiff,
  output wire [ADDR_SIZE:0]   wbin_ptr,
  output wire [ADDR_SIZE+1:0] wdiff,

  input  wire [ADDR_SIZE-1:0] swi_almost_empty,
  input  wire [ADDR_SIZE-1:0] swi_almost_full,
  output wire                 half_full,
  output wire                 almost_empty,
  output wire                 almost_full
);

wire [ADDR_SIZE-1:0]          waddr;
wire [ADDR_SIZE-1:0]          raddr;
wire [ADDR_SIZE:0]            wptr, sync_wptr;
wire [ADDR_SIZE:0]            rptr, sync_rptr;

//demets for ptr sync
demet_reset u_rptr_to_wlogic_demet[ADDR_SIZE:0] (
  .clk      ( wclk        ),
  .reset    ( wreset      ),
  .sig_in   ( rptr        ),
  .sig_out  ( sync_rptr   )
);

demet_reset u_wptr_to_rlogic_demet[ADDR_SIZE:0] (
  .clk      ( rclk        ),
  .reset    ( rreset      ),
  .sig_in   ( wptr        ),
  .sig_out  ( sync_wptr   )
);

//write logic
fifo_ptr_logic2 #(
  .ADDR_SIZE          ( ADDR_SIZE ),
  .IS_WRITE_PTR       ( 1         )
) u_write_ptr_logic (
  .inc               ( winc                 ),
  .clk               ( wclk                 ),
  .reset             ( wreset               ),
  .swi_almost_val    ( swi_almost_full      ),
  .sync_ptr          ( sync_rptr            ),
  .ptr               ( wptr                 ),
  .bin_ptr           ( wbin_ptr             ),
  .diff              ( wdiff                ),
  .addr              ( waddr                ),
  .flag              ( wfull                ),
  .almost_fe         ( almost_full          ),
  .half_full         ( half_full            ));

//read logic
fifo_ptr_logic2 #(
  .ADDR_SIZE          ( ADDR_SIZE ),
  .IS_WRITE_PTR       ( 0         )
) u_read_ptr_logic (
  .inc               ( rinc                 ),
  .clk               ( rclk                 ),
  .reset             ( rreset               ),
  .swi_almost_val    ( swi_almost_empty     ),
  .sync_ptr          ( sync_wptr            ),
  .ptr               ( rptr                 ),
  .bin_ptr           ( rbin_ptr             ),
  .diff              ( rdiff                ),
  .addr              ( raddr                ),
  .flag              ( rempty               ),
  .almost_fe         ( almost_empty         ),
  .half_full         (                      ));

//mem
fifomem #(
  .DATA_SIZE  ( DATA_SIZE    ),
  .ADDR_SIZE  ( ADDR_SIZE    )
) u_mem (
  .wclk       ( wclk         ),
  .rclk       ( rclk         ),
  .wclken     ( winc         ),
  .read_en    ( ~rempty      ),
  .wreset     ( wreset       ),  //1/14/2018 added - sbridges
  .wfull      ( wfull        ),
  .waddr      ( waddr        ),
  .raddr      ( raddr        ),
  .wdata      ( wdata        ),
  .rdata      ( rdata        )
);

endmodule

/*
* Based on sunburst-design.com's fifo design. Removed the need for two separate blocks
* by using generate statements to produce full/empty flag. Also changed reset to active high,
* because active low resets just confuse me
*/

module fifo_ptr_logic2 #(
  parameter                           IS_WRITE_PTR  = 1,      //Determines the output logic
  parameter                           ADDR_SIZE     = 4
)(
  input  wire                         inc,
  input  wire                         clk,
  input  wire                         reset,
  input  wire [ADDR_SIZE-1:0]         swi_almost_val,         //programmable value for almost full/empty. Set to the difference you wish
  input  wire [ADDR_SIZE:0]           sync_ptr,               //pointer from opposite logic block
  output reg  [ADDR_SIZE:0]           ptr,                    //this blocks gray-encoded pointer to opposite block
  output wire [ADDR_SIZE:0]           bin_ptr,                //this blocks binary pointer
  output wire [ADDR_SIZE+1:0]         diff,                   //difference between pointers
  output wire [ADDR_SIZE-1:0]         addr,                   //addr to memory
  output reg                          flag,                   //empty/full flag
  output reg                          almost_fe,              //almost full/empty flag, port representation is based on the setting
  output wire                         half_full               //1 when write pointer - read pointer is >= half of full val (you can think of it as half-empty if your one of those people)
);

reg  [ADDR_SIZE:0]      bin;
wire [ADDR_SIZE:0]      graynext;
wire [ADDR_SIZE:0]      binnext;

wire [ADDR_SIZE:0]      sync_bin;   //binary value of the sync ptr
//wire [ADDR_SIZE+1:0]    diff;

always @(posedge clk or posedge reset) begin
  if(reset) begin
    bin           <= {ADDR_SIZE+1{1'b0}};
    ptr           <= {ADDR_SIZE+1{1'b0}};
  end else begin
    bin           <= binnext;
    ptr           <= graynext;
  end
end

assign addr       = bin[ADDR_SIZE-1:0];
assign binnext    = bin + (inc & ~flag);
assign graynext   = (binnext>>1) ^ binnext;

//gray2bin conversion for size checking
assign sync_bin[ADDR_SIZE:0] = sync_ptr[ADDR_SIZE:0] ^ {1'b0, sync_bin[ADDR_SIZE:1]};

assign bin_ptr = bin;

// Full/Empty logic generation, need to comeback to add in something that describes the almost full/empty cases
// Can't break out the flag register as the reset value is different depending on the mode
generate
  if(IS_WRITE_PTR == 1) begin : gen_full_logic
    //2 MSBs should not equal, lower bits should for full indication
    wire    full_int, half_full_int, almost_fe_int;
    reg     half_full_reg;

    assign  diff            = bin + (~sync_bin + {{ADDR_SIZE-1{1'b0}}, 1'b1});
    assign  full_int        = (graynext == {~sync_ptr[ADDR_SIZE:ADDR_SIZE-1], sync_ptr[ADDR_SIZE-2:0]});
    assign  half_full_int   = (diff[ADDR_SIZE:0]   >= {2'b01, {ADDR_SIZE-1{1'b0}}});    //half of addr area
    assign  almost_fe_int   = (diff[ADDR_SIZE-1:0] >= swi_almost_val);                  //The higher you set this, the later it trips (stays high if full)
    assign  half_full       = half_full_reg;

    always @(posedge clk or posedge reset) begin
      if(reset) begin
        flag          <= 1'b0;
        half_full_reg <= 1'b0;
        almost_fe     <= 1'b0;
      end else begin
        flag          <= full_int;
        half_full_reg <= half_full_int;
        almost_fe     <= almost_fe_int;
      end
    end

  end else begin : gen_empty_logic
    //write pointer should equal read pointer for empty
    wire    empty_int, almost_fe_int;

    assign empty_int        = (graynext == sync_ptr);
    assign half_full        = 1'b0;                                                     //half_full is invalid, so tieoff
    assign diff             = sync_bin + (~bin + {{ADDR_SIZE-1{1'b0}}, 1'b1});
    assign almost_fe_int    = (diff[ADDR_SIZE-1:0] <= swi_almost_val);

    always @(posedge clk or posedge reset) begin
      if(reset) begin
        flag        <= 1'b1;
        almost_fe   <= 1'b1;
      end else begin
        flag        <= empty_int;
        almost_fe   <= almost_fe_int;
      end
    end

  end
endgenerate

endmodule

module fifomem #(
  parameter                     DATA_SIZE        = 40,
  parameter                     ADDR_SIZE        = 4
)(
  input  wire                   wclk,
  input  wire                   rclk,
  input  wire                   wclken,
  input  wire                   read_en,
  input  wire                   wreset,       //1/14/2018 added - sbridges
  input  wire                   wfull,
  input  wire [ADDR_SIZE-1:0]   waddr,
  input  wire [ADDR_SIZE-1:0]   raddr,
  input  wire [DATA_SIZE-1:0]   wdata,
  output wire [DATA_SIZE-1:0]   rdata
);

localparam    DEPTH = 1<<ADDR_SIZE;
wire web;
wire reb;

  reg [DATA_SIZE-1:0]   mem [0:DEPTH-1];

  assign rdata  = mem[raddr];

  integer i;
  always @(posedge wclk or posedge wreset) begin
    if(wreset) begin
      for(i = 0; i< (1<<ADDR_SIZE); i = i + 1) begin
        mem[i]      <= {DATA_SIZE{1'b0}};
      end
    end else begin
      if(wclken & ~wfull) begin
        mem[waddr]  <= wdata;
      end
    end
  end

endmodule

module wav_sigdelt
 #(
   parameter                  WIDTH                    = 7
  )
  (
   input  wire                clk,
   input  wire                reset,
   input  wire                clear,
   input  wire [WIDTH-1:0]    addin,
   output reg  [WIDTH-1:0]    sumout,
   output reg                 polarity,
   output reg                 overflow
  );

  wire [WIDTH:0]              se_addin;
  wire [WIDTH:0]              se_rem;
  wire [WIDTH+1:0]            addout_in;
  reg  [WIDTH:0]              addout_ff;

  assign se_addin   = {addin[WIDTH-1], addin};
  assign se_rem     = {addout_ff[WIDTH], addout_ff[WIDTH], addout_ff[WIDTH-2:0]};
  assign addout_in  = se_addin + se_rem;

  always @(posedge clk or posedge reset) begin
    if (reset) begin
      addout_ff  <= {WIDTH+1{1'b0}};
      sumout     <= {WIDTH{1'b0}};
      polarity   <= 1'b0;
      overflow   <= 1'b0;
    end else begin
      addout_ff  <= clear ? {WIDTH+1{1'b0}} : addout_in[WIDTH:0];
      sumout     <= {addout_in[WIDTH], addout_in[WIDTH-2:0]};
      polarity   <= addout_in[WIDTH];
      overflow   <= addout_in[WIDTH]^addout_in[WIDTH-1];
    end
  end

endmodule

module wav_phase_detector
  #(
    parameter                                        WIDTH                   = 4,
    parameter                                        COUNT_WIDTH             = $clog2(WIDTH)+1,      // Make 2^COUNT_WIDTH > WIDTH
    parameter                                        ILEADQ                  = 0
   )
   (
    input  wire                                      clk,
    input  wire                                      reset,
    input  wire                                      enable,
    input  wire [WIDTH-1:0]                          idata,
    input  wire [WIDTH-1:0]                          qdata,
    output reg                                       up,
    output reg                                       dn
   );

  wire                                enable_ff2;
  reg  [WIDTH-1:0]                    idata_int;
  reg  [WIDTH-1:0]                    qdata_int;
  reg                                 idata_prev;
  reg                                 qdata_prev;
  wire [WIDTH-1:0]                    upxor;
  wire [WIDTH-1:0]                    dnxor;
  reg  [COUNT_WIDTH-1:0]              upsum;
  reg  [COUNT_WIDTH-1:0]              dnsum;

  demet_reset u_demet_enable(
    .clk      ( clk                  ),
    .reset    ( reset                ),
    .sig_in   ( enable               ),
    .sig_out  ( enable_ff2           ));

  reg idata_ff;
  reg qdata_ff;

  always @(posedge clk or posedge reset) begin
    if (reset) begin
      idata_ff     <= 1'b0;
      qdata_ff     <= 1'b0;
    end else begin
      idata_ff     <= enable_ff2 ? idata[WIDTH-1] : 1'b0;
      qdata_ff     <= enable_ff2 ? qdata[WIDTH-1] : 1'b0;
    end
  end

  always @(*) begin
    idata_int    = idata;
    qdata_int    = qdata;
    idata_prev   = idata_ff;
    qdata_prev   = qdata_ff;
  end

  generate
    if (ILEADQ == 0) begin : gen_q_lead_i
      assign upxor = qdata_int^{idata_int[WIDTH-2:0],idata_prev};
      assign dnxor = qdata_int^idata_int;
    end else begin : gen_i_lead_q
      assign upxor = {qdata_int[WIDTH-2:0], qdata_prev}^{idata_int[WIDTH-2:0],idata_prev};
      assign dnxor = {qdata_int[WIDTH-2:0], qdata_prev}^idata_int;
    end
  endgenerate

  always @(*) begin : add_ud
    integer i;
    upsum = {COUNT_WIDTH{1'b0}};
    dnsum = {COUNT_WIDTH{1'b0}};
    for (i = 0; i < WIDTH; i = i + 1) begin
      upsum = upsum + upxor[i];
      dnsum = dnsum + dnxor[i];
    end
  end

  always @(posedge clk or posedge reset) begin
    if (reset) begin
      up           <= 1'b0;
      dn           <= 1'b0;
    end else begin
      up           <= enable_ff2 ? (upsum > dnsum) ? 1'b1 : 1'b0 : 1'b0;
      dn           <= enable_ff2 ? (dnsum > upsum) ? 1'b1 : 1'b0 : 1'b0;
    end
  end

endmodule

module wav_pi_control_encode

  (
   input  wire         clk,
   input  wire         reset,
   input  wire         oneup,
   input  wire         onedown,
   output reg  [5:0]   pi_bin,
   output reg  [15:0]  pi_ctrl,
   output reg  [1:0]   pi_quad
  );

  reg  [1:0]   pi_quad_nxtup;
  reg  [1:0]   pi_quad_nxtdown;
  wire         quaddown;
  wire         quadup;
  wire [1:0]   pi_quad_in;
  wire [15:0]  pi_ctrl_in;
  wire [3:0]   pi_bin_low_in;
  wire [1:0]   pi_bin_high_in;

//  assign pi_ctrl_in = onedown ? {pi_ctrl[14:0], ~pi_ctrl[15]}
//                              : (oneup ? {~pi_ctrl[0], pi_ctrl[15:1]}
//                              : pi_ctrl);

  assign pi_ctrl_in  = oneup   ? (pi_quad[1]^pi_quad[0]) ? {1'b1, pi_ctrl[15:1]} : {1'b0, pi_ctrl[15:1]} :
                       onedown ? {pi_ctrl[14:0], ~pi_ctrl[15]} : pi_ctrl;

  assign quaddown    = onedown & ((pi_ctrl == 16'h0000) || (pi_ctrl == 16'hffff));
  assign quadup      = oneup   & ((pi_ctrl == 16'hFFFE) || (pi_ctrl == 16'h0001));
  assign pi_quad_in  = quaddown ? pi_quad_nxtdown : (quadup ? pi_quad_nxtup : pi_quad);

  //assign pi_bin_in    = oneup ? pi_bin + 1'b1 ? onedown ? pi_bin - 1'b1 : pi_bin;
  assign pi_bin_low_in  = oneup ? pi_bin[3:0] + 1'b1 : onedown ? pi_bin[3:0] - 1'b1 : pi_bin[3:0];
  //assign pi_quad_in   = (pi_bin_in[5:4] == 2'b00) ? 2'b01 : (pi_bin_in[5:4] == 2'b01) ? 2'b00 : pi_bin_in[5:4];
  assign pi_bin_high_in = (pi_quad_in == 2'b01) ? 2'b00 : (pi_quad_in == 2'b00) ? 2'b01 : pi_quad_in;

always @(posedge clk or posedge reset) begin
  if (reset == 1'b1) begin
    pi_bin  <= 6'b000000;
    pi_ctrl <= 16'h0000;
    pi_quad <= 2'b01;
  end else begin
    pi_bin  <= {pi_bin_high_in, pi_bin_low_in};
    pi_ctrl <= pi_ctrl_in;
    pi_quad <= pi_quad_in;
  end
end

// pi_quad is gray coded

always @(*) begin
  case (pi_quad)
    2'b00 : pi_quad_nxtdown = 2'b01;
    2'b01 : pi_quad_nxtdown = 2'b11;
    2'b11 : pi_quad_nxtdown = 2'b10;
    2'b10 : pi_quad_nxtdown = 2'b00;
  endcase
end

always @(*) begin
  case (pi_quad)
    2'b00 : pi_quad_nxtup = 2'b10;
    2'b01 : pi_quad_nxtup = 2'b00;
    2'b11 : pi_quad_nxtup = 2'b01;
    2'b10 : pi_quad_nxtup = 2'b11;
  endcase
end

endmodule

module fifo_top #(
  parameter                   DATA_SIZE     = 40,
  parameter                   ADDR_SIZE     = 4
)(
  input  wire                 wclk,
  input  wire                 wreset,
  input  wire                 winc,
  input  wire                 rclk,
  input  wire                 rreset,
  input  wire                 rinc,
  input  wire [DATA_SIZE-1:0] wdata,
  output wire [DATA_SIZE-1:0] rdata,
  output wire                 wfull,
  output wire                 rempty,

  input  wire [ADDR_SIZE-1:0] swi_almost_empty,
  input  wire [ADDR_SIZE-1:0] swi_almost_full,
  output wire                 half_full,
  output wire                 almost_empty,
  output wire                 almost_full
);

wire [ADDR_SIZE-1:0]          waddr;
wire [ADDR_SIZE-1:0]          raddr;
wire [ADDR_SIZE:0]            wptr, sync_wptr;
wire [ADDR_SIZE:0]            rptr, sync_rptr;

//demets for ptr sync
demet_reset u_rptr_to_wlogic_demet[ADDR_SIZE:0] (
  .clk                          ( wclk                    ),
  .reset                        ( wreset                  ),
  .sig_in                       ( rptr                    ),
  .sig_out                      ( sync_rptr               )
);

demet_reset u_wptr_to_rlogic_demet[ADDR_SIZE:0] (
  .clk                          ( rclk                    ),
  .reset                        ( rreset                  ),
  .sig_in                       ( wptr                    ),
  .sig_out                      ( sync_wptr               )
);

//write logic
fifo_ptr_logic #(
  .IS_WRITE_PTR                 ( 1                       ),
  .ADDR_SIZE                    ( ADDR_SIZE               )
) u_write_ptr_logic (
  .inc                          ( winc                    ),
  .clk                          ( wclk                    ),
  .reset                        ( wreset                  ),
  .swi_almost_val               ( swi_almost_full         ),
  .sync_ptr                     ( sync_rptr               ),
  .ptr                          ( wptr                    ),
  .addr                         ( waddr                   ),
  .flag                         ( wfull                   ),
  .half_full                    ( half_full               ),
  .almost_fe                    ( almost_full             )
);

//read logic
fifo_ptr_logic #(
  .IS_WRITE_PTR                 ( 0                       ),
  .ADDR_SIZE                    ( ADDR_SIZE               )
) u_read_ptr_logic (
  .inc                          ( rinc                    ),
  .clk                          ( rclk                    ),
  .reset                        ( rreset                  ),
  .swi_almost_val               ( swi_almost_empty        ),
  .sync_ptr                     ( sync_wptr               ),
  .ptr                          ( rptr                    ),
  .addr                         ( raddr                   ),
  .flag                         ( rempty                  ),
  .half_full                    ( /*noconn*/              ),
  .almost_fe                    ( almost_empty            )
);

//mem
fifomem #(
  .DATA_SIZE                    ( DATA_SIZE               ),
  .ADDR_SIZE                    ( ADDR_SIZE               )
) u_mem (
  .wclk                         ( wclk                    ),
  .rclk                         ( rclk                    ),
  .wclken                       ( winc                    ),
  .read_en                      ( ~rempty                 ),
  .wreset                       ( wreset                  ), //1/14/2018 added - sbridges
  .wfull                        ( wfull                   ),
  .waddr                        ( waddr                   ),
  .raddr                        ( raddr                   ),
  .wdata                        ( wdata                   ),
  .rdata                        ( rdata                   )
);

endmodule

/*
* Based on sunburst-design.com's fifo design. Removed the need for two separate blocks
* by using generate statements to produce full/empty flag. Also changed reset to active high,
* because active low resets just confuse me
*/

module fifo_ptr_logic #(
  parameter                           IS_WRITE_PTR  = 1,      //Determines the output logic
  parameter                           ADDR_SIZE     = 4
)(
  input  wire                         inc,
  input  wire                         clk,
  input  wire                         reset,
  input  wire [ADDR_SIZE-1:0]         swi_almost_val,         //programmable value for almost full/empty. Set to the difference you wish
  input  wire [ADDR_SIZE:0]           sync_ptr,               //pointer from opposite logic block
  output reg  [ADDR_SIZE:0]           ptr,                    //this blocks gray-encoded pointer to opposite block
  output wire [ADDR_SIZE-1:0]         addr,                   //addr to memory
  output reg                          flag,                   //empty/full flag
  output reg                          almost_fe,              //almost full/empty flag, port representation is based on the setting
  output wire                         half_full               //1 when write pointer - read pointer is >= half of full val (you can think of it as half-empty if your one of those people)
);

reg  [ADDR_SIZE:0]      bin;
wire [ADDR_SIZE:0]      graynext;
wire [ADDR_SIZE:0]      binnext;

wire [ADDR_SIZE:0]      sync_bin;   //binary value of the sync ptr
wire [ADDR_SIZE+1:0]    diff;

always @(posedge clk or posedge reset) begin
  if(reset) begin
    bin           <= {ADDR_SIZE+1{1'b0}};
    ptr           <= {ADDR_SIZE+1{1'b0}};
  end else begin
    bin           <= binnext;
    ptr           <= graynext;
  end
end

assign addr       = bin[ADDR_SIZE-1:0];
assign binnext    = bin + (inc & ~flag);
assign graynext   = (binnext>>1) ^ binnext;

//gray2bin conversion for size checking
assign sync_bin[ADDR_SIZE:0] = sync_ptr[ADDR_SIZE:0] ^ {1'b0, sync_bin[ADDR_SIZE:1]};

// Full/Empty logic generation, need to comeback to add in something that describes the almost full/empty cases
// Can't break out the flag register as the reset value is different depending on the mode
generate
  if(IS_WRITE_PTR == 1) begin : gen_full_logic
    //2 MSBs should not equal, lower bits should for full indication
    wire    full_int, half_full_int, almost_fe_int;
    reg     half_full_reg;

    assign  diff            = bin + (~sync_bin + {{ADDR_SIZE-1{1'b0}}, 1'b1});
    assign  full_int        = (graynext == {~sync_ptr[ADDR_SIZE:ADDR_SIZE-1], sync_ptr[ADDR_SIZE-2:0]});
    assign  half_full_int   = (diff[ADDR_SIZE:0]   >= {2'b01, {ADDR_SIZE-1{1'b0}}});    //half of addr area
    assign  almost_fe_int   = (diff[ADDR_SIZE-1:0] >= swi_almost_val);                  //The higher you set this, the later it trips (stays high if full)
    assign  half_full       = half_full_reg;

    always @(posedge clk or posedge reset) begin
      if(reset) begin
        flag          <= 1'b0;
        half_full_reg <= 1'b0;
        almost_fe     <= 1'b0;
      end else begin
        flag          <= full_int;
        half_full_reg <= half_full_int;
        almost_fe     <= almost_fe_int;
      end
    end

  end else begin : gen_empty_logic
    //write pointer should equal read pointer for empty
    wire    empty_int, almost_fe_int;

    assign empty_int        = (graynext == sync_ptr);
    assign half_full        = 1'b0;                                                     //half_full is invalid, so tieoff
    assign diff             = sync_bin + (~bin + {{ADDR_SIZE-1{1'b0}}, 1'b1});
    assign almost_fe_int    = (diff[ADDR_SIZE-1:0] <= swi_almost_val);

    always @(posedge clk or posedge reset) begin
      if(reset) begin
        flag        <= 1'b1;
        almost_fe   <= 1'b1;
      end else begin
        flag        <= empty_int;
        almost_fe   <= almost_fe_int;
      end
    end

  end
endgenerate

endmodule

module generic_regs32
  #(
    parameter                          ADDR_WIDTH                = 3,
    parameter                          NUM_REGS                  = 5,                                     // Number of Registers that are used
    parameter                          RW_MASK                   = {NUM_REGS{1'b1}},                      // Set to 1 for a RW Register
    parameter                          RESET_VAL                 = {NUM_REGS{32'd0}},                     // Reset value of RW Registers
    parameter                          SWI_MASK_VAL              = {NUM_REGS{32'd0}},                     // Set to 1 to remove register bits
    parameter                          NUM_POSSIBLE_REGS         = 1 << ADDR_WIDTH,
    parameter                          RW_WIDTH                  = 32 * NUM_REGS,                          // Number of '1's in RW_MASK
    parameter                          RO_WIDTH                  = 32 * NUM_REGS                           // Number of '0's in RW_MASK
   )
   (
    input  wire                            RegClk,
    input  wire                            RegReset,
    input  wire [ADDR_WIDTH-1:0]           RegAddr,
    input  wire                            RegWrEn,
    input  wire [31:0]                      RegWrData,
    output reg  [31:0]                      RegRdData,

    input  wire [RO_WIDTH-1:0]             swi_status,
    output wire [RW_WIDTH-1:0]             swi_control
   );

  wire [31:0]                reg_out_vec       [NUM_REGS-1:0];
  reg  [(NUM_REGS*32)-1:0]   rw_reg;
  wire [(NUM_REGS*32)-1:0]   rw_reg_in;
  wire                      tie_lo;

  genvar genloop;
  genvar genloop2;

  assign swi_control = rw_reg;

  always @(*) begin : read_data
    integer i;
    RegRdData    = reg_out_vec[0];
    for (i = 1; i < NUM_REGS; i = i + 1) begin : or_read_data
      RegRdData  = RegRdData | reg_out_vec[i];
    end
  end

  generate
    for (genloop2 = 0; genloop2 < NUM_REGS*32; genloop2 = genloop2 + 1) begin : gen_logic
      if (SWI_MASK_VAL[genloop2] == 1'b1) begin : no_register
        assign tie_lo = 1'b0;
        always @(*) begin
          rw_reg[genloop2]     <= tie_lo;
        end
      end else begin : insert_register
        always @(posedge RegClk or posedge RegReset) begin
          if (RegReset) begin
            rw_reg[genloop2]   <= RESET_VAL[genloop2];
          end else begin
            rw_reg[genloop2]   <= rw_reg_in[genloop2];
          end
        end
      end
    end //for
  endgenerate

  generate
    for (genloop = 0; genloop < NUM_REGS; genloop = genloop + 1) begin : gen_registers
        if (RW_MASK[genloop] == 1'b1) begin : gen_rw_registers

          assign rw_reg_in[((genloop+1)*32)-1:genloop*32] = (RegAddr == genloop && RegWrEn == 1'b1) ? RegWrData : rw_reg[((genloop+1)*32)-1:genloop*32];
          assign reg_out_vec[genloop] = (RegAddr == genloop) ? rw_reg[((genloop+1)*32)-1:genloop*32] : 32'h00000000;

        end else begin : gen_ro_register

          assign rw_reg_in[((genloop+1)*32)-1:genloop*32] = 32'h00000000;
          assign reg_out_vec[genloop] = (RegAddr == genloop) ? swi_status[((genloop+1)*32)-1:genloop*32] : 32'h00000000;

        end
    end //for
  endgenerate

endmodule

`endif
