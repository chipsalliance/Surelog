/*
:name: unpacked-array-reduction-method-sum
:description: Test support of unpacked arrays reduction method sum
:tags: 7.12.3 7.4.2
:type: simulation parsing
*/
module top ();

byte b[] = { 1, 2, 3, 4 };
int y;

initial begin
	$display(":assert: ((%d == 1) and (%d == 2) and (%d == 3) and (%d == 4))",
		b[0], b[1], b[2], b[3]);
	y = b.sum;
	$display(":assert: (%d == 10)", y);
end

endmodule
