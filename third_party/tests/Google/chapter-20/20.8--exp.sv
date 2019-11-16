/*
:name: exp_function
:description: $exp test
:should_fail: 0
:tags: 20.8
:type: simulation parsing
*/

module top();

initial begin
	$display(":assert: (%f > 2.718) and (%f < 2.719)", $exp(1), $exp(1));
end

endmodule
