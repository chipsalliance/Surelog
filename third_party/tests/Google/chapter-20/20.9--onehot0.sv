/*
:name: onehot0_function
:description: $onehot0 test
:tags: 20.9
:type: simulation parsing
*/

module top();

initial begin
	logic [31:0] val0 = 32'h00010000;
	logic [31:0] val1 = 32'h00030000;
	logic [31:0] val2 = 32'h00000000;
	$display(":assert: (%d == 1)", $onehot0(val0));
	$display(":assert: (%d == 0)", $onehot0(val1));
	$display(":assert: (%d == 1)", $onehot0(val2));
end

endmodule
