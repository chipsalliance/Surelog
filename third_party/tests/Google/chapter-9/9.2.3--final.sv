/*
:name: final
:description: final check
:should_fail: 0
:tags: 9.2.3
*/
module initial_tb ();
	reg a = 0;
	final
		a = 1;
endmodule
