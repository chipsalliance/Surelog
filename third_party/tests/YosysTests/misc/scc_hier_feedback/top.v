module top
(
 input x,
 input y,
 input cin,

 output reg A,
 output cout
 );
 parameter X = 1;
 wire o_mid,o_rtl;

always @(posedge cin)
	A <= o_mid;

middle u_mid (.x(x),.y(o_rtl),.o(o_mid));
u_rtl inst_u_rtl (.x(o_mid),.y(y),.o(o_rtl));

endmodule

module middle
(
	input x,
	input y,
	output o
);

wire o1,o2;

assign o1 = x & o2;
assign o2 = y & o1;
assign o = o1;
endmodule

module u_rtl
(
	input x,
	input y,
	output o
);


wire o1,o2;

assign o1 = x & o2;
assign o2 = y & o1;
assign o = o1;
endmodule
