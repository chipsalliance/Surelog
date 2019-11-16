/*
:name: string_concat
:description: string concatenation test
:should_fail: 0
:tags: 11.10.1
*/
module top();

bit [8*14:1] a;
bit [8*14:1] b;

initial begin
	a = "Test";
	b = "TEST";
	$display({a, b});
end

endmodule
