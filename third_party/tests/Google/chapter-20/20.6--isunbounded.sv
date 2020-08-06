/*
:name: isunbounded_function
:description: $isunbounded test
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
