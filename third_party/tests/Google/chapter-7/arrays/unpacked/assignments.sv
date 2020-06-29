/*
:name: array-unpacked-assignments
:description: Test unpacked arrays assignments
:tags: 7.6 7.4.2
:type: simulation parsing
*/
module top ();

int A [3:0];
int B [0:3];

initial begin
	A[0] = 0;
	A[1] = 1;
	A[2] = 2;
	A[3] = 3;

	B = A;

	$display(":assert: ((%d == 0) and (%d == 1) and (%d == 2) and (%d == 3))",
		B[3], B[2], B[1], B[0]);
end

endmodule
