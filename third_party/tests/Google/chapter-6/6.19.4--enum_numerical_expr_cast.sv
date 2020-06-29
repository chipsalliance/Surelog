/*
:name: enum_numerical_expr_cast
:description: enum numerical expression with casting
:tags: 6.19.4
*/
module top();
	typedef enum {a, b, c, d} e;

	initial begin
		e val;
		val = a;
		val = e'(val+1);
	end
endmodule
