/*
:name: unpacked-arrays-as-arguments-to-subroutines
:description: Test support of arrays as arugments to subroutines
:tags: 7.7 7.4.2
:type: simulation parsing
*/
module top ();

task fun(int a [2:0]);
	$display(":assert: ((%d == 0) and (%d == 1) and (%d == 2))",
		a[0], a[1], a[2]);
endtask;

initial begin
	int b [2:0];
	b[0] = 0;
	b[1] = 1;
	b[2] = 2;
	$display(":assert: ((%d == 0) and (%d == 1) and (%d == 2))",
		b[0], b[1], b[2]);
	fun(b);
end

endmodule
