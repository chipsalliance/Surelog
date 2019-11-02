module top(clk,d,q);
input clk,d;
output reg q;

always @(posedge clk)
if (!1'h1)
  q <= 0;
else
  q <= d;

endmodule
