/*
:name: string_hextoa
:description: string.hextoa()  tests
:should_fail: 0
:tags: 6.16.12
*/
module top();
	string a;
	initial
		a.hextoa(12);
endmodule
