/*
:name: task
:description: task test
:should_fail: 0
:tags: 13.3
:type: simulation parsing
*/
module top();

task mytask;
	$display(":assert: True");
endtask

initial 
	mytask;

endmodule
