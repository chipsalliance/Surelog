/*
:name: typename_function
:description: $typename test
:tags: 20.6
:type: simulation parsing
*/

module top();

initial begin
	logic val;
	$display(":assert: ('%s' == 'logic')", $typename(val));
end

endmodule
