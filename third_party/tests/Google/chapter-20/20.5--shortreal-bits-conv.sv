/*
:name: shortrealtobits_bitstoshortreal_functions
:description: $shortrealtobits and $bitstoshortreal test
:tags: 20.5
:type: simulation parsing
*/

module top();

	shortreal s;

initial begin
	s = $bitstoshortreal($shortrealtobits(12.45));
	$display(":assert: (%0d == 1)", (s > 12.449 && s < 12.451));
end

endmodule
