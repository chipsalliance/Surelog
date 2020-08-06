/*
:name: basic-union
:description: Test basic union support
:tags: 7.3
:type: simulation parsing
*/
module top ();

union {
	bit [7:0] v1;
	bit [3:0] v2;
} un;

initial begin
	un.v1 = 8'd140;
	$display(":assert: (%d == 140)", un.v1);
	$display(":assert: (%d == 12)", un.v2);
end

endmodule
