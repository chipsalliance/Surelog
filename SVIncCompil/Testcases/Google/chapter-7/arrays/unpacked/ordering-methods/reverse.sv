/*
:name: ordering-methods-reverse
:description: Test support of reverse method on unpacked arrays
:should_fail: 0
:tags: 7.12.2 7.4.2
*/
module top ();

string s[] = { "hello", "sad", "world" };

initial begin
	$display(":assert: (('%s' == 'hello') and ('%s' == 'sad') and ('%s' == 'world'))",
		s[0], s[1], s[2]);
	s.reverse;
	$display(":assert: (('%s' == 'world') and ('%s' == 'sad') and ('%s' == 'hello'))",
		s[0], s[1], s[2]);
end

endmodule
