/*
:name: string_compare_fn
:description: string.compare()  tests
:should_fail: 0
:tags: 6.16.6
*/
module top();
	string a = "Test";
	string b = "TEST";
	int c = a.compare(b);
endmodule
