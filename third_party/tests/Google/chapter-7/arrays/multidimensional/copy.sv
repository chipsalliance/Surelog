/*
:name: copy
:description: Test multidimensional word copy
:tags: 7.4.5
:type: simulation parsing
*/

module top ();

bit [3:0] [7:0] arr_a [1:10];
bit [3:0] [7:0] arr_b [1:10];

initial begin
	arr_a[1] = 32'hdeadbeef;
	$display(":assert: ('%h' == 'deadbeef')", arr_a[1]);

	arr_b[2] = arr_a[1];
	$display(":assert: ('%h' == 'deadbeef')", arr_b[2]);
end

endmodule
