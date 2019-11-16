/*
:name: task_automatic
:description: automatic task test
:should_fail: 0
:tags: 13.3.1
:type: simulation parsing
*/
module top();

task automatic mytask;
	int a = 0;
	a++;
	$display(":assert:(%d == 1)", a);
endtask

initial
	fork
		mytask;
		mytask;
		mytask;
		mytask;
	join

endmodule
