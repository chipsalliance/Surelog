///////////////////////////////////////////////////////////////////////////////
//     Copyright (c) 1995/2015 Xilinx, Inc.
// 
//    Licensed under the Apache License, Version 2.0 (the "License");
//    you may not use this file except in compliance with the License.
//    You may obtain a copy of the License at
// 
//        http://www.apache.org/licenses/LICENSE-2.0
// 
//    Unless required by applicable law or agreed to in writing, software
//    distributed under the License is distributed on an "AS IS" BASIS,
//    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//    See the License for the specific language governing permissions and
//    limitations under the License.
///////////////////////////////////////////////////////////////////////////////
//   ____  ____
//  /   /\/   /
// /___/  \  /    Vendor      : Xilinx
// \   \   \/     Version     : 2016.1
//  \   \         Description : Xilinx Unified Simulation Library Component
//  /   /                       64-Deep 8-bit Read 1-bit Write Multi Port RAM
// /___/   /\     Filename    : RAM64X8SW.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//    11/09/15 - Initial version.
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps


`celldefine


module RAM64X8SW #(



  parameter [63:0] INIT_A = 64'h0000000000000000,
  parameter [63:0] INIT_B = 64'h0000000000000000,
  parameter [63:0] INIT_C = 64'h0000000000000000,
  parameter [63:0] INIT_D = 64'h0000000000000000,
  parameter [63:0] INIT_E = 64'h0000000000000000,
  parameter [63:0] INIT_F = 64'h0000000000000000,
  parameter [63:0] INIT_G = 64'h0000000000000000,
  parameter [63:0] INIT_H = 64'h0000000000000000,
  parameter [0:0] IS_WCLK_INVERTED = 1'b0
)(
  output [7:0] O,

  input [5:0] A,
  input D,
  input WCLK,
  input WE,
  input [2:0] WSEL
);
  
// define constants
  localparam MODULE_NAME = "RAM64X8SW";









    




// begin behavioral model

  reg [63:0] mem_a, mem_b, mem_c, mem_d;
  reg [63:0] mem_e, mem_f, mem_g, mem_h;
  reg [7:0] O_out;

  assign O = O_out;

  initial begin
    mem_a = INIT_A;
    mem_b = INIT_B;
    mem_c = INIT_C;
    mem_d = INIT_D;
    mem_e = INIT_E;
    mem_f = INIT_F;
    mem_g = INIT_G;
    mem_h = INIT_H;
    #100;
    O_out = {mem_a[A], mem_b[A], mem_c[A], mem_d[A], mem_e[A], mem_f[A], mem_g[A], mem_h[A]};
  end

generate if (IS_WCLK_INVERTED == 1'b0) begin : write_block































  always @(posedge WCLK)
    if ((WE === 1'bz) || WE) begin
      case (WSEL)
        3'b111: begin
          if (mem_a[A] !== D) mem_a[A] <= D;
        end
        3'b110: begin
          if (mem_b[A] !== D) mem_b[A] <= D;
        end
        3'b101: begin
          if (mem_c[A] !== D) mem_c[A] <= D;
        end
        3'b100: begin
          if (mem_d[A] !== D) mem_d[A] <= D;
        end
        3'b011: begin
          if (mem_e[A] !== D) mem_e[A] <= D;
        end
        3'b010: begin
          if (mem_f[A] !== D) mem_f[A] <= D;
        end
        3'b001: begin
          if (mem_g[A] !== D) mem_g[A] <= D;
        end
        3'b000: begin
          if (mem_h[A] !== D) mem_h[A] <= D;
        end
      endcase
    end

end else begin : write_block































  always @(negedge WCLK)
    if ((WE === 1'bz) || WE) begin
      case (WSEL)
        3'b111: begin
          if (mem_a[A] !== D) mem_a[A] <= D;
        end
        3'b110: begin
          if (mem_b[A] !== D) mem_b[A] <= D;
        end
        3'b101: begin
          if (mem_c[A] !== D) mem_c[A] <= D;
        end
        3'b100: begin
          if (mem_d[A] !== D) mem_d[A] <= D;
        end
        3'b011: begin
          if (mem_e[A] !== D) mem_e[A] <= D;
        end
        3'b010: begin
          if (mem_f[A] !== D) mem_f[A] <= D;
        end
        3'b001: begin
          if (mem_g[A] !== D) mem_g[A] <= D;
        end
        3'b000: begin
          if (mem_h[A] !== D) mem_h[A] <= D;
        end
      endcase
    end

end
endgenerate



























   always @ (mem_a[A] or A) begin
     if (O_out[7] !== mem_a[A]) O_out[7] = mem_a[A];
   end
   always @ (mem_b[A] or A) begin
     if (O_out[6] !== mem_b[A]) O_out[6] = mem_b[A];
   end
   always @ (mem_c[A] or A) begin
     if (O_out[5] !== mem_c[A]) O_out[5] = mem_c[A];
   end
   always @ (mem_d[A] or A) begin
     if (O_out[4] !== mem_d[A]) O_out[4] = mem_d[A];
   end
   always @ (mem_e[A] or A) begin
     if (O_out[3] !== mem_e[A]) O_out[3] = mem_e[A];
   end
   always @ (mem_f[A] or A) begin
     if (O_out[2] !== mem_f[A]) O_out[2] = mem_f[A];
   end
   always @ (mem_g[A] or A) begin
     if (O_out[1] !== mem_g[A]) O_out[1] = mem_g[A];
   end
   always @ (mem_h[A] or A) begin
     if (O_out[0] !== mem_h[A]) O_out[0] = mem_h[A];
   end















// end behavioral model















  specify
    (WCLK *> O) = (100:100:100, 100:100:100);
    (A *> O) = (100:100:100, 100:100:100);
















































    specparam PATHPULSE$ = 0;
  endspecify

endmodule

`endcelldefine

