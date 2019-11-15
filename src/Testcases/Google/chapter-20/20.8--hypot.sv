/*
:name: hypot_function
:description: $hypot test
:should_fail: 0
:tags: 20.8
:type: simulation parsing
*/

module top();

initial begin
	$display("%f", $hypot(2.1, 3.7));
end

endmodule
