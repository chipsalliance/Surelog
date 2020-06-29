/*
:name: task
:description: task test
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
