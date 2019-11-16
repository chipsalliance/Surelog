module top
(
 input x,
 input y,
 input cin,

 output reg A,
 output cout
 );
 parameter X = 1;
 wire o;

`ifndef BUG
always @(posedge cin)
	A <= o;

assign cout =  cin? y : x;

middle #(1'b0) u_mid1 (.x(x),.o(o),.y(1'b0));
middle #(1'b0) u_mid2 (.x(x),.o(o),.y(1'b1));
middle #(1'b0) u_mid3 (.x(x),.o(o),.y(1'bX));
middle #(1'b0) u_mid4 (.x(x),.o(o),.y(1'bX));
`else
assign {cout,A} =  cin - y * x;
`endif

endmodule

module middle
(
	input x,
	input y,
	output o
);

parameter Y = 1'b1;

urtl u_urtl (.x(x),.o(o),.y(Y));
endmodule

module urtl
(
	input x,
	input y,
	output o
);

assign o = x + y;
endmodule
