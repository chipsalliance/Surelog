/*
:name: bits_function
:description: $bits test
:should_fail: 0
:tags: 20.6
:type: simulation parsing
*/

module top();

initial begin
	logic [31:0] val;
	$display(":assert: (%d == 32)", $bits(val));
end

endmodule
