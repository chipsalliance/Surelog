/*
:name: array_queries
:description: array query function tests
:tags: 20.7
:type: simulation parsing
*/

module top();

logic [31:0] arr;

initial begin
	$display(":assert: (%d == 0)", $unpacked_dimensions(arr));
	$display(":assert: (%d == 1)", $dimensions(arr));
	$display(":assert: (%d == 1)", $increment(arr));
	$display(":assert: (%d == 0)", $right(arr));
	$display(":assert: (%d == 31)", $left(arr));
	$display(":assert: (%d == 0)", $low(arr));
	$display(":assert: (%d == 31)", $high(arr));
	$display(":assert: (%d == 32)", $size(arr));
end

endmodule
