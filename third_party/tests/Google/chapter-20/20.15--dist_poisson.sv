/*
:name: dist_poisson_function
:description: $dist_poisson test
:tags: 20.15
:type: simulation parsing
*/

module top();

initial begin
	integer seed = 1234;
	$display("%d", $dist_poisson(seed, 100));
end

endmodule
