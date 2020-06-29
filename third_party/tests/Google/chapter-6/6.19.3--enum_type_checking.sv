/*
:name: enum_type_checking
:description: enum type checking tests
:tags: 6.19.3
*/
module top();
	typedef enum {a, b, c, d} e;

	initial begin
		e val;
		val = a;
	end
endmodule
