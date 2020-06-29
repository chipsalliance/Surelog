/*
:name: 22.7--timescale-module
:description: Test
:tags: 22.7
:type: preprocessing
*/
`timescale 10 ns / 1 ns
module test;
	logic set;
	parameter d = 1.55;
	initial begin
		#d set = 0;
		#d set = 1;
	end
endmodule
