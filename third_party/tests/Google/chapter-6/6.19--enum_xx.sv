/*
:name: enum_xx
:description: enum with x tests
:should_fail: 0
:tags: 6.19
*/
module top();
	enum integer {a=0, b={32{1'bx}}, c=1} val;
endmodule
