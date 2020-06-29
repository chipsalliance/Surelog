/*
:name: enum_first
:description: enum first method tests
:tags: 6.19.5.1
*/
module top();
	typedef enum {a, b, c, d} e;

	initial begin
		e val = a;
		val = val.first();
	end
endmodule
