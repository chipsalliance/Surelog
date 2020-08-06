/*
:name: array-locator-methods-min
:description: Test support of array locator methods
:tags: 7.12.1 7.12 7.10
:type: simulation parsing
*/
module top ();

int s[] = { 10, 20, 2, 11, 5 };
int qi[$];

initial begin
	qi = s.min;
    $display(":assert: (%d == 1)", qi.size);
    $display(":assert: (%d == 2)", qi[0]);
end

endmodule
