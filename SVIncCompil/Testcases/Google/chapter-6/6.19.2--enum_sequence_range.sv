/*
:name: enum_sequence_range
:description: enum sequence range tests
:should_fail: 0
:tags: 6.19.2
*/
module top();
	enum {start=10, stop[11:13]} e;
endmodule
