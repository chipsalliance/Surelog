/*
:name: mailbox_blocking
:description: blocking mailbox test
:should_fail: 0
:tags: 15.4
*/
module top();

mailbox m;

initial begin
	m = new();
	string msg = "abc";
	string r;
	string r_peek;
	m.put(msg);
	m.peek(r_peek);
	$display(":assert: (%d == 1)", m.num());
	m.get(r);
	$display(":assert: ('%s' == '%s')", r, r_peek);
end

endmodule
