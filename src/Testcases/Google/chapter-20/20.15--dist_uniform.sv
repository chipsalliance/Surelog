/*
:name: dist_uniform_function
:description: $dist_uniform test
:should_fail: 0
:tags: 20.15
:type: simulation parsing
*/

module top();

initial begin
	integer seed = 1234;
	$display("%d", $dist_uniform(seed, 0, 100));
end

endmodule
