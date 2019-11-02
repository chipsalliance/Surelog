/*
:name: real_bit_select
:description: real bit select tests
:should_fail: 1
:tags: 6.12
*/
module top();
	real a = 0.5;
	wire [3:0] b;
	wire c;

	assign c = b[a];
endmodule
