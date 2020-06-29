/*
:name: isunknown_function
:description: $isunknown test
:tags: 20.9
:type: simulation parsing
*/

module top();

initial begin
	logic [3:0] val0 = 32'b000x;
	logic [3:0] val1 = 32'b000z;
	logic [3:0] val2 = 32'b00xz;
	logic [3:0] val3 = 32'b0000;
	$display(":assert: (%d == 1)", $isunknown(val0));
	$display(":assert: (%d == 1)", $isunknown(val1));
	$display(":assert: (%d == 1)", $isunknown(val2));
	$display(":assert: (%d == 0)", $isunknown(val3));
end

endmodule
