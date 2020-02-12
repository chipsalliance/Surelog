/*
:name: isunbounded_function
:description: $isunbounded test
:should_fail: 0
:tags: 20.6
:type: simulation parsing
*/

module top();
parameter int i = $;

initial begin
	$display(":assert: (%d == 0)", $isunbounded(1));
	$display(":assert: (%d == 1)", $isunbounded(i));
end

endmodule
