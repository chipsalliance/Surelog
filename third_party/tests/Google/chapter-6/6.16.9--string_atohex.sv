/*
:name: string_atohex
:description: string.atohex()  tests
:should_fail: 0
:tags: 6.16.9
*/
module top();
	string a = "0xff";
	int b = a.atohex();
endmodule
