/*
:name: enum_sequence
:description: enum sequence tests
:should_fail: 0
:tags: 6.19.2
*/
module top();
	enum {start=10, step[10]} e;
endmodule
