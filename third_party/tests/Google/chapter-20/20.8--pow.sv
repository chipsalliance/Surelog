/*
:name: pow_function
:description: $pow test
:tags: 20.8
:type: simulation parsing
*/

module top();

initial begin
	$display(":assert: (%f == 5.0625)", $pow(2.25, 2));
end

endmodule
