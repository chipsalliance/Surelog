/*
:name: real_edge
:description: real edge event tests
:should_fail: 1
:tags: 6.12
*/
module top();
	real a = 0.5;
	always @(posedge a)
		$display("posedge");
endmodule
