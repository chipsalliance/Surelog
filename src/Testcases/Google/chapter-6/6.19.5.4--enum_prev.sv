/*
:name: enum_prev
:description: enum prev method tests
:should_fail: 0
:tags: 6.19.5.4
*/
module top();
	typedef enum {a, b, c, d} e;

	initial begin
		e val = b;
		val = val.prev();
	end
endmodule
