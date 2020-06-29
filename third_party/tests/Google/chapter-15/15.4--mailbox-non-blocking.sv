/*
:name: mailbox_non_blocking
:description: non-blocking mailbox test
:tags: 15.4
*/
module top();

mailbox m;

initial begin
	m = new();
	string msg = "abc";
	string r;
	string r_peek;
	m.try_put(msg);
	m.peek(r_peek);
	$display(":assert: (%d == 1)", m.num());
	m.try_get(r);
	$display(":assert: ('%s' == '%s')", r, r_peek);
end

endmodule
