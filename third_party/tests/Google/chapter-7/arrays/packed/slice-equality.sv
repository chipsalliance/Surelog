/*
:name: operations-on-packed-arrays-slice-equality
:description: Test packed arrays operations support (slice equality)
:tags: 7.4.3
:type: simulation parsing
*/
module top ();

bit [7:0] arr_a;
bit [7:0] arr_b;

initial begin
	arr_a = 8'hf0;
	arr_b = 8'h0f;
	$display(":assert: (('%h' == 'f0') and ('%h' == '0f'))", arr_a, arr_b);

	$display(":assert: (%d == 1)", (arr_a[7:4] == arr_b[3:0]));
	$display(":assert: (%d == 0)", (arr_a[7:4] != arr_b[3:0]));
end

endmodule
