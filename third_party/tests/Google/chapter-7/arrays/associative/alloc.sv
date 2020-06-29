/*
:name: associative-arrays-allocating-elements
:description: Test associative arrays elements allocation
:tags: 7.8.7 7.8 7.9.1
:type: simulation parsing
*/
module top ();

int arr [ int ];

initial begin
	$display(":assert: (%d == 0)", arr.size);
	arr[10] = 10;
	$display(":assert: (%d == 1)", arr.size);
end

endmodule
