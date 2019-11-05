/*
:name: itor_function
:description: $itor test
:should_fail: 0
:tags: 20.5
:type: simulation parsing
*/

module top();

initial begin
	$display(":assert: (%f == 20.0)", $itor(20));
end

endmodule
