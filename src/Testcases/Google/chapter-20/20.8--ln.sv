/*
:name: ln_function
:description: $ln test
:should_fail: 0
:tags: 20.8
:type: simulation parsing
*/

module top();

initial begin
	$display(":assert: (%d == 0)", $ln(1));
end

endmodule
