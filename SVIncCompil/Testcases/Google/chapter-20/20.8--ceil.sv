/*
:name: ceil_function
:description: $ceil test
:should_fail: 0
:tags: 20.8
:type: simulation parsing
*/

module top();

initial begin
	$display(":assert: (%f == 4)", $ceil(3.7));
end

endmodule
