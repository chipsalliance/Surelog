module top
(
 input [15:0] x,
 input [15:0] y,

 output [15:0] A,
 output [15:0] B
 );

assign A =  x + y;
assign B =  x - y;

endmodule
