/*
:name: enum_type_checking_inv
:description: invalid enum assignment tests
:should_fail: 1
:tags: 6.19.3
*/
module top();
	typedef enum {a, b, c, d} e;

	initial begin
		e val;
		val = 1;
	end
endmodule
