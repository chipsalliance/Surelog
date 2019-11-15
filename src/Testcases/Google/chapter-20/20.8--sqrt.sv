/*
:name: sqrt_function
:description: $sqrt test
:should_fail: 0
:tags: 20.8
:type: simulation parsing
*/

module top();

initial begin
	$display(":assert: (%d == 3)", $sqrt(9));
end

endmodule
