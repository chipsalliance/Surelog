`default_nettype none
module mcve2(david);
	output	reg	david;

	always @(*)
		goliath = 4;

	always @(*)
		david = goliath;
endmodule
`default_nettype wire
