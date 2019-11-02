/*
:name: string_getc
:description: string.getc()  tests
:should_fail: 0
:tags: 6.16.3
*/
module top();
	string a = "Test";
	byte b = a.getc(2);
endmodule
