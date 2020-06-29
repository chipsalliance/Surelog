/*
:name: operations-on-arrays-variable-slice-zero-rw
:description: Test packed arrays operations support (Variable slice)
:should_fail_because: more info in comments
:tags: 7.4.3
:type: simulation
*/
module top ();

bit [7:0] arr_a;
bit [7:0] arr_b;

// TODO: Not sure if that should fail.
// TODO: Icarus fails with:
// TODO: "error: Indexed part widths must be constant and greater than zero."
// TODO: Info in queue section: "Unlike arrays, the empty queue, {}, is a valid queue"
//
// Found:
//  The term slice refers to a selection of one or more contiguous elements of an array
//  so it should fail
parameter integer c = 0;

initial begin
	arr_a = 8'hff;
	arr_b = 8'h00;
	$display(":assert: (('%h' == 'ff') and ('%h' == '00'))", arr_a, arr_b);

	arr_b[4+:c] = arr_a[1+:c];
	$display(":assert: ('%b' == '00000000')", arr_b);
end

endmodule
