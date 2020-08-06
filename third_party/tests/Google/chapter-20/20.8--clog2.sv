/*
:name: clog2_function
:description: $clog2 test
:tags: 20.8
:type: simulation parsing
*/

module top();

initial begin
	$display(":assert: (%d == 5)", $clog2(32));
end

endmodule
