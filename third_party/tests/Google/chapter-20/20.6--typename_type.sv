/*
:name: typename_type_function
:description: $typename with type as an argument
:tags: 20.6
:type: simulation parsing
*/

module top();

initial begin
	$display(":assert: ('%s' == 'logic')", $typename(logic));
end

endmodule
