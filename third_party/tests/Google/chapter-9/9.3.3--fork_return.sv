/*
:name: fork_return
:description: illegal return from fork
:should_fail_because: return statement is illegal inside fork-join block
:tags: 9.3.3
:type: simulation
*/
module block_tb ();
	task fork_test;
		fork
			#20;
			return;
		join_none
	endtask
endmodule
