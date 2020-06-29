/*
:name: operations-on-packed-arrays-one-bit
:description: Test packed arrays operations support (one bit)
:tags: 7.4.3
:type: simulation parsing
*/
module top ();

bit [7:0] arr_a;
bit [7:0] arr_b;

initial begin
	arr_a = 8'hff;
	arr_b = 8'h00;
	$display(":assert: (('%h' == 'ff') and ('%h' == '00'))", arr_a, arr_b);

	arr_b[5] = arr_a[2];
	$display(":assert: ('%b' == '00100000')", arr_b);
end

endmodule
