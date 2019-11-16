module top
(
 input x,
 input y,
 input cin,

 output reg A,
 output cout
 );
 parameter X = 1;
 parameter U = "string";
 wire o;

`ifndef BUG
always @(posedge cin)
	A <= o;

assign cout =  cin? y : x;

middle u_mid1 (.x(x),.o(o),.y(1'b0));
middle u_mid2 (.x(x),.o(o),.y(1'b1));
middle u_mid3 (.x(x),.o(o),.y(1'bX));
middle u_mid4 (.x(x),.o(o),.y(1'bX));


urtl u_urtl (.x(x),.o(o),.y(y));
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

parameter u = 12;

urtl u_urtl (.x(x),.o(o),.y(y));
endmodule

module urtl
(
	input x,
	input y,
	output o
);

assign o = x + y;
endmodule
