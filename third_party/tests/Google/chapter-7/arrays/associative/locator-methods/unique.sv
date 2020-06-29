/*
:name: array-locator-methods-unique
:description: Test support of array locator methods
:tags: 7.12.1 7.12 7.10 7.12.2
:type: simulation parsing
*/
module top ();

int s[] = { 10, 10, 3, 20, 20, 10 };
int qi[$];

initial begin
	qi = s.unique;
    $display(":assert: (%d == 3)", qi.size);
	qi.sort;
    $display(":assert: ((%d == 3) and (%d == 10) and (%d == 20))",
		qi[0], qi[1], qi[2]);
end

endmodule
