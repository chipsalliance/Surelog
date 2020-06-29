/*
:name: array_queries_multi_dim
:description: multi-dimensional array query function tests
:tags: 20.7
:type: simulation parsing
*/

module top();

logic [31:0] arr [15:0];

initial begin
	$display(":assert: (%d == 2)", $dimensions(arr));
	$display(":assert: (%d == 1)", $increment(arr, 2));
	$display(":assert: (%d == 0)", $right(arr, 2));
	$display(":assert: (%d == 31)", $left(arr, 2));
	$display(":assert: (%d == 0)", $right(arr, 1));
	$display(":assert: (%d == 15)", $left(arr, 1));
	$display(":assert: (%d == 0)", $low(arr, 2));
	$display(":assert: (%d == 31)", $high(arr, 2));
	$display(":assert: (%d == 32)", $size(arr, 2));
end

endmodule
