/*
:name: random_function
:description: $random test
:should_fail: 0
:tags: 20.15
:type: simulation parsing
*/

module top();

initial begin
	$display("%d", $random);
end

endmodule
