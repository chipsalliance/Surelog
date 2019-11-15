module top
(
 input x,
 input y,
 input cin,
 input clk,

 output A,
 output cout
 );

`ifndef BUG
 assign    A =  y + cin;
 assign   cout =  x + A;

`else
assign {cout,A} =  cin - y * x;
`endif

endmodule
