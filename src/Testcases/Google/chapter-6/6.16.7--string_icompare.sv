/*
:name: string_icompare
:description: string.icompare()  tests
:should_fail: 0
:tags: 6.16.7
*/
module top();
	string a = "Test";
	string b = "TEST";
	int c = a.icompare(b);
endmodule
