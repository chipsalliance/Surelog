module top(
	input signed [7:0] x,
	output y,
);

assign y = x > -$sqrt(9);

endmodule
