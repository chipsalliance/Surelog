/*
:name: type_op
:description: type operator tests
:should_fail: 0
:tags: 6.23
*/
module top();
	real a = 4.76;
	real b = 0.74;
	var type(a+b) c;
endmodule
