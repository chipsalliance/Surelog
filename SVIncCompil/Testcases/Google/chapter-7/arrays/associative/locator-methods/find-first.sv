/*
:name: array-locator-methods-find-first
:description: Test support of array locator methods
:should_fail: 0
:tags: 7.12.1 7.12 7.10
*/
module top ();

string s[] = { "hello", "sad", "hello", "world" };
string qs[$];

initial begin
	qs = s.find_first with ( item == "hello" );
    $display(":assert: (%d == 1)", qs.size);
    $display(":assert: ('%s' == 'hello')", qs[0]);
end

endmodule
