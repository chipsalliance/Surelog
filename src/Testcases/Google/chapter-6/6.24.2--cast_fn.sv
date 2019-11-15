/*
:name: cast_fn
:description: $cast function
:should_fail: 0
:tags: 6.24.2
*/
module top();
	int a;
	initial
		if (! $cast(a, 2.1 * 3.7))
			$display("cast failed");
endmodule
