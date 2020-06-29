/*
:name: unpacked-array-reduction-method-and
:description: Test support of unpacked arrays reduction method and
:tags: 7.12.3 7.4.2
:type: simulation parsing
*/
module top ();

byte b[] = { 1, 3, 5, 7 };
int y;

initial begin
	$display(":assert: ((%d == 1) and (%d == 3) and (%d == 5) and (%d == 7))",
		b[0], b[1], b[2], b[3]);
	y = b.and;
	$display(":assert: (%d == 1)", y);
end

endmodule
