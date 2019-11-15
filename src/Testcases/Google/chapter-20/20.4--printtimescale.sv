/*
:name: printtimescale_task
:description: $printtimescale test
:should_fail: 0
:tags: 20.4
:type: simulation parsing
*/

`timescale 1 ms / 1 us

module top();

initial
	$printtimescale;

endmodule
