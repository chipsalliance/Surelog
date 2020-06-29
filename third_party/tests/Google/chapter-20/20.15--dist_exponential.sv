/*
:name: dist_exponential_function
:description: $dist_exponential test
:tags: 20.15
:type: simulation parsing
*/

module top();

initial begin
	integer seed = 1234;
	$display("%d", $dist_exponential(seed, 100));
end

endmodule
