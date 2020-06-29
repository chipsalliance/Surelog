/*
:name: nettype_resolution_fn
:description: user-defined nettype with resolution function tests
:tags: 6.6.7
*/
module top();
	function automatic real real_sum (input real driver[]);
		real_sum = 0.0;
		foreach (driver[i])
			real_sum += driver[i];
	endfunction

	nettype real real_net with real_sum;
endmodule
