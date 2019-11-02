/*
:name: ordering-methods-shuffle
:description: Test support of shuffle method on unpacked arrays
:should_fail: 0
:tags: 7.12.2 7.4.2
*/
module top ();

int ia[] = { 1, 2, 3, 4, 5 };

initial begin
	$display(":info: { %d, %d, %d, %d, %d }",
		ia[0], ia[1], ia[2], ia[3], ia[4]);
	ia.shuffle;
	$display(":info: { %d, %d, %d, %d, %d }",
		ia[0], ia[1], ia[2], ia[3], ia[4]);
end

endmodule
