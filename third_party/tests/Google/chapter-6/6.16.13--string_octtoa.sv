/*
:name: string_octtoa
:description: string.octtoa()  tests
:should_fail: 0
:tags: 6.16.13
*/
module top();
	string a;
	initial
		a.octtoa(12);
endmodule
