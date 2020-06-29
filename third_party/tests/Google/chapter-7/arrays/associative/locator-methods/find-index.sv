/*
:name: array-locator-methods-find-index
:description: Test support of array locator methods
:tags: 7.12.1 7.12 7.10
:type: simulation parsing
*/
module top ();

string s[] = { "hello", "sad", "world" };
int qi[$];

initial begin
	qi = s.find_index with ( item == "world" );
    $display(":assert: (%d == 1)", qi.size);
    $display(":assert: (%d == 2)", qi[0]);
end

endmodule
