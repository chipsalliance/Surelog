/*
:name: dist_erlang_function
:description: $dist_erlang test
:tags: 20.15
:type: simulation parsing
*/

module top();

initial begin
	integer seed = 1234;
	$display("%d", $dist_erlang(seed,  3, 100));
end

endmodule
