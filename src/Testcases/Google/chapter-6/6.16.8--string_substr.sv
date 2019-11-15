/*
:name: string_substr
:description: string.substr()  tests
:should_fail: 0
:tags: 6.16.8
*/
module top();
	string a = "Test";
	string b = a.substr(1, 2);
endmodule
