module top
(
 input x,
 input y,
 input cin,

 output reg A,
 output cout
 );
 wire o;

`ifndef BUG
//always @(posedge cin)
//	A <= o;

assign cout =  cin? y : x;

//middle u_mid (x,y,o);
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
