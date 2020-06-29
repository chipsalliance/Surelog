/*
:name: implicit_continuous_assignment
:description: implicit declaration in continuous assignment tests
:tags: 6.10
*/
module top();
	wire [3:0] a = 8;
	wire [3:0] b = 5;

	assign c = | (a | b);
endmodule
