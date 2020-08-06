/*
:name: cast_fn
:description: $cast function
:tags: 6.24.2
*/
module top();
	int a;
	initial
		if (! $cast(a, 2.1 * 3.7))
			$display("cast failed");
endmodule
