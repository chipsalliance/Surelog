/*
:name: ordering-methods-sort
:description: Test support of sort method on unpacked arrays
:tags: 7.12.2 7.4.2
:type: simulation parsing
*/
module top ();

int ia[] = { 4, 5, 3, 1 };

initial begin
	$display(":assert: ((%d == 4) and (%d == 5) and (%d == 3) and (%d == 1))",
		ia[0], ia[1], ia[2], ia[3]);
	ia.sort;
	$display(":assert: ((%d == 1) and (%d == 3) and (%d == 4) and (%d == 5))",
		ia[0], ia[1], ia[2], ia[3]);
end

endmodule
