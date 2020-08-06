/*
:name: memories-read-write
:description: Test memories read-write support
:tags: 7.4.4
:type: simulation parsing
*/
module top ();

// one-dimensinal array with elements of types
// reg, logic, bit
logic [7:0] mem [0:255];

initial begin
	mem[5] = 0;
	$display(":assert: (%d == 0)", mem[5]);

	mem[5] = 5;
	$display(":assert: (%d == 5)", mem[5]);
end

endmodule
