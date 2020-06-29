/*
:name: countbits_function
:description: $countbits test
:tags: 20.9
:type: simulation parsing
*/

module top();

initial begin
	logic [31:0] val = 32'h70008421;
	$display(":assert: (%d == 7)", $countbits(val, '1));
	$display(":assert: (%d == 7)", $countones(val));
	$display(":assert: (%d == 25)", $countbits(val, '0));
	$display(":assert: (%d == 32)", $countbits(val, '0, '1));
	$display(":assert: (%d == 0)", $countbits(val, 'x, 'z));
end

endmodule
