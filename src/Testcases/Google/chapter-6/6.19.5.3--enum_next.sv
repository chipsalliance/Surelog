/*
:name: enum_next
:description: enum next method tests
:should_fail: 0
:tags: 6.19.5.3
*/
module top();
	typedef enum {a, b, c, d} e;

	initial begin
		e val = a;
		val = val.next();
	end
endmodule
