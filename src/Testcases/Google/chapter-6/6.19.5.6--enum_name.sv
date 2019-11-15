/*
:name: enum_name
:description: enum name method tests
:should_fail: 0
:tags: 6.19.5.6
*/
module top();
	typedef enum {a, b, c, d} e;

	initial begin
		e val = a;
		string s = val.name();
	end
endmodule
