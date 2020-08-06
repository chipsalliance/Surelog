/*
:name: implicit_port
:description: implicit port signal tests
:tags: 6.10
*/
module top(input [3:0] a, input [3:0] b);
	wire [3:0] c;
	assign c = a | b;
endmodule
