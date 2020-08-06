/*
:name: itor_function
:description: $itor test
:tags: 20.5
:type: simulation parsing
*/

module top();

initial begin
	$display(":assert: (%f == 20.0)", $itor(20));
end

endmodule
