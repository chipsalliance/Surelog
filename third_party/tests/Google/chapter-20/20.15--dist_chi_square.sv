/*
:name: dist_chi_square_function
:description: $dist_chi_square test
:should_fail: 0
:tags: 20.15
:type: simulation parsing
*/

module top();

initial begin
	integer seed = 1234;
	$display("%d", $dist_chi_square(seed, 3));
end

endmodule
