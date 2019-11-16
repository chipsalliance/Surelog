/*
:name: dist_t_function
:description: $dist_t test
:should_fail: 0
:tags: 20.15
:type: simulation parsing
*/

module top();

initial begin
	integer seed = 1234;
	$display("%d", $dist_t(seed, 3));
end

endmodule
