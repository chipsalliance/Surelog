/*
:name: operations-on-unpacked-arrays-equality
:description: Test unpacked arrays operations support (equality)
:tags: 7.4.3
:type: simulation parsing
*/
module top ();

bit arr_a [7:0];
bit arr_b [7:0];

initial begin
	arr_a = '{1, 1, 1, 0, 0, 1, 1, 1};
	arr_b = '{1, 1, 1, 0, 0, 1, 1, 1};
	$display(":assert: ('%b%b%b%b_%b%b%b%b' == '1110_0111')",
		arr_a[7], arr_a[6], arr_a[5], arr_a[4], arr_a[3], arr_a[2], arr_a[1], arr_a[0]);
	$display(":assert: ('%b%b%b%b_%b%b%b%b' == '1110_0111')",
		arr_b[7], arr_b[6], arr_b[5], arr_b[4], arr_b[3], arr_b[2], arr_b[1], arr_b[0]);

	$display(":assert: (%d == 1)", (arr_a == arr_b));
	$display(":assert: (%d == 0)", (arr_a != arr_b));
end

endmodule
