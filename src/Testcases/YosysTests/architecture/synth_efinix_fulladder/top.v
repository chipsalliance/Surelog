module top
(
 input [3:0] x,
 input [3:0] y,
 input [3:0] cin,

 output [4:0] A,
 output [4:0] cout
 );

`ifndef BUG
assign {cout,A} =  cin + y + x;
`else
assign {cout,A} =  cin - y * x;
`endif

endmodule
