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

 initial A = 0;
 initial cout = 0;



`ifndef BUG
always @(posedge cin)
	A <= o;

assign cout =  cin? y : x;

middle u_mid (.x(x),.o(o));
u_rtl inst_u_rtl (.x(x),.o(o));
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

assign o = x + y;
endmodule

module u_rtl
(
	input x,
	input y,
	output o
);

assign o = x + y;
endmodule
