/*
:name: array-locator-methods-find-first-index
:description: Test support of array locator methods
:tags: 7.12.1 7.12 7.10
:type: simulation parsing
*/
module top ();

string s[] = { "hello", "sad", "hello", "world" };
int qi[$];

initial begin
	qi = s.find_first_index with ( item == "hello" );
    $display(":assert: (%d == 1)", qi.size);
    $display(":assert: (%d == 0)", qi[0]);
end

endmodule
