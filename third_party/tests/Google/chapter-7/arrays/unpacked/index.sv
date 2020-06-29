/*
:name: unpacked-array-iterator-index-querying
:description: Test support of unpacked arrays index querying method
:tags: 7.12.4 7.4.2 7.10 7.12.1
:type: simulation parsing
*/
module top ();

int arr[] = { 0, 1, 3, 3 };
int q[$];

initial begin
	q = arr.find with ( item == item.index );
	$display(":assert: ((%d == 3) and (%d == 0) and (%d == 1) and (%d == 3))",
		q.size, q[0], q[1], q[2]);
end

endmodule
