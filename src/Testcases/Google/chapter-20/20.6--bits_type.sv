/*
:name: bits_type_function
:description: $bits with type argument
:should_fail: 0
:tags: 20.6
:type: simulation parsing
*/

module top();

typedef struct packed {
	logic val1;
	bit [7:0] val2;
} mystruct;

initial begin
	$display(":assert: (%d == 9)", $bits(mystruct));
end

endmodule
