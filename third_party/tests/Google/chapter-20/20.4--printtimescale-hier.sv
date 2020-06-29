/*
:name: printtimescale_hier_task
:description: $printtimescale hierarchy test
:tags: 20.4
:type: simulation parsing
*/

`timescale 1 ms / 1 us

module top();

initial
	$printtimescale(mod0.m);

endmodule

`timescale 1 us / 1 ns

module mod0();
	mod1 m();
endmodule

`timescale 1 ns / 1 ps

module mod1();
initial
	$display("mod1");
endmodule
