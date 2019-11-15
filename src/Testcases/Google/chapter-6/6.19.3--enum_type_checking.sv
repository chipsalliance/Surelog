/*
:name: enum_type_checking
:description: enum type checking tests
:should_fail: 0
:tags: 6.19.3
*/
module top();
	typedef enum {a, b, c, d} e;

	initial begin
		e val;
		val = a;
	end
endmodule
