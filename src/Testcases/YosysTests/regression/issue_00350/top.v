module top (input clk, input i, output o);
  reg q = 0;
  always @(posedge clk) q <= 1;
  assign o = q & i;
endmodule
