/*
:name: array-locator-methods-find
:description: Test support of array locator methods
:tags: 7.12.1 7.12 7.10
:type: simulation parsing
*/
module top ();

string s[] = { "hello", "sad", "world" };
string qs[$];

initial begin
	qs = s.find with ( item == "sad" );
    $display(":assert: (%d == 1)", qs.size);
    $display(":assert: ('%s' == 'sad')", qs[0]);
end

endmodule
