`default_nettype  none
module top(i_clk, jmp, in, out);
  parameter DEFINED=5;
  input  wire  i_clk, in, jmp;
  output  reg  [8-1:0]  out;

  initial  out = 0;
  always @(posedge i_clk)
  if (jmp)
    out <= { out[UNDEFINED-1:0], in };
  else
    out <= { 1'b0, out[UNDEFINED-1:1] };

endmodule
