/*
:name: operations-on-unpacked-arrays-variable-slice-rw
:description: Test packed arrays operations support (Variable slice)
:tags: 7.4.3 7.4.6
:type: simulation parsing
*/
module top ();

bit arr_a [7:0];
bit arr_b [7:0];

parameter integer c = 3;

initial begin
	arr_a = '{1, 1, 1, 1, 1, 1, 1, 1};
	arr_b = '{0, 0, 0, 0, 0, 0, 0, 0};
	$display(":assert: ('%b%b%b%b_%b%b%b%b' == '1111_1111')",
		arr_a[7], arr_a[6], arr_a[5], arr_a[4], arr_a[3], arr_a[2], arr_a[1], arr_a[0]);
	$display(":assert: ('%b%b%b%b_%b%b%b%b' == '0000_0000')",
		arr_b[7], arr_b[6], arr_b[5], arr_b[4], arr_b[3], arr_b[2], arr_b[1], arr_b[0]);

	arr_b[4+:c] = arr_a[1+:c];
	$display(":assert: ('%b%b%b%b_%b%b%b%b' == '0111_0000')",
		arr_b[7], arr_b[6], arr_b[5], arr_b[4], arr_b[3], arr_b[2], arr_b[1], arr_b[0]);
end

endmodule
