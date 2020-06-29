/*
:name: floor_function
:description: $floor test
:tags: 20.8
:type: simulation parsing
*/

module top();

initial begin
	$display(":assert: (%f == 2)", $floor(2.1));
end

endmodule
