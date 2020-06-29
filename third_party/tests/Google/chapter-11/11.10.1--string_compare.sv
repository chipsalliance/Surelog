/*
:name: string_compare
:description: string comparison test
:tags: 11.10.1
:type: simulation parsing
*/
module top();

bit [8*14:1] a;
bit [8*14:1] b;

initial begin
	a = "Test";
	b = "Test";
	$display(":assert:('%s' == '%s')", a, b);
end

endmodule
