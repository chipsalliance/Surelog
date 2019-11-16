/*
:name: shortrealtobits_bitstoshortreal_functions
:description: $shortrealtobits and $bitstoshortreal test
:should_fail: 0
:tags: 20.5
:type: simulation parsing
*/

module top();

initial begin
	$display(":assert: (%f == 12.45)", $bitstoshortreal($shortrealtobits(12.45)));
end

endmodule
