/*
:name: cast_task
:description: $cast task
:should_fail: 0
:tags: 6.24.2 8.16
*/
module top();
	int a;
	initial
		$cast(a, 2.1 * 3.7);
endmodule
