/*
:name: fork_return
:description: illegal return from fork
:should_fail: 1
:tags: 9.3.3
*/
module block_tb ();
	task fork_test;
		fork
			#20;
			return;
		join_none
	endtask
endmodule
