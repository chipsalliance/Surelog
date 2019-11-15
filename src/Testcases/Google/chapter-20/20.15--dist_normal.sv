/*
:name: dist_normal_function
:description: $dist_normal test
:should_fail: 0
:tags: 20.15
:type: simulation parsing
*/

module top();

initial begin
	integer seed = 1234;
	$display("%d", $dist_normal(seed, 0, 100));
end

endmodule
