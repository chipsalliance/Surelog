/*
:name: enum_numerical_expr
:description: enum numerical expression tests
:tags: 6.19.4
*/
module top();
	typedef enum {a, b, c, d} e;

	initial begin
		integer i;
		e val;
		val = a;
		i = val * 4;
	end
endmodule
