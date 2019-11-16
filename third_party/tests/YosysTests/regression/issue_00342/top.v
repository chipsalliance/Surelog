`timescale 1ns / 1ns
module top #(parameter           AWIDTH=8,
             localparam DEPTH=1<<AWIDTH,
             parameter  DWIDTH=8)
 (output [DWIDTH-1:0] rdata,
 input [DWIDTH-1:0] wdata,
  input [AWIDTH-1:0] addr,
  input              r_wn, cs_n);
  logic [DWIDTH-1:0] mem [DEPTH];
  assign rdata = mem[addr];
  always_latch
    if (!cs_n && !r_wn) mem[addr] <= wdata;
endmodule
