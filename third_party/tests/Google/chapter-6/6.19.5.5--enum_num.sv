/*
:name: enum_num
:description: enum num method tests
:tags: 6.19.5.5
*/
module top();
	typedef enum {a, b, c, d} e;

	initial begin
		e val = a;
		int n = val.num();
	end
endmodule
