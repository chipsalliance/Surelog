/*
:name: cast_task
:description: $cast task
:tags: 6.24.2 8.16
*/
module top();
	int a;
	initial
		$cast(a, 2.1 * 3.7);
endmodule
