/*
:name: string_compare
:description: string comparison test
:should_fail: 0
:tags: 11.10.1
*/
module top();

bit [8*14:1] a;
bit [8*14:1] b;

initial begin
	a = "Test";
	b = "Test";
	$display(a == b);
end

endmodule
