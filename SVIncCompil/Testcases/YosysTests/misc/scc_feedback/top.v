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

assign o_mid = x & o_rtl;
assign o_rtl = y & o_mid;

endmodule
