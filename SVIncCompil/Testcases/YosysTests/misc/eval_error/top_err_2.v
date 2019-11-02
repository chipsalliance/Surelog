module top
(
 input [7:0] x,
 input[7:0] y,
 input cin,

 output reg [7:0] A,
 output [7:0] cout
 );
 parameter X = 1;
 wire o;

`ifndef BUG
always @(posedge cin)
	A <= o;

assign cout =  cin? y : x;

middle #(7) u_mid (.x(x),.o(o),.y(1'b0));
middle #(0) u_mid2 (.x(x),.o(o));
`else
assign {cout,A} =  cin - y * x;
`endif

endmodule

module middle
(
	x,
	y,
	o
);

parameter u = 7;

input [u:0] x;
input [u:0] y;
output  [u:0] o;

assign o = x + y;
endmodule

module xiddle
(
	input [1:0] x,
	input y,
	output [1:0] o
);

assign o = x + y;
endmodule
