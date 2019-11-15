/*
:name: log10_function
:description: $log10 test
:should_fail: 0
:tags: 20.8
:type: simulation parsing
*/

module top();

initial begin
	$display(":assert: (%d == 2)", $log10(100));
end

endmodule
