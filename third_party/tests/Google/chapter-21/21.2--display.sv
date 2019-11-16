/*
:name: display_task
:description: $display test
:should_fail: 0
:tags: 21.2
:type: simulation parsing
*/
module top();

initial begin
	int val = 1234;
	$display(val);
	$displayb(val);
	$displayo(val);
	$displayh(val);
end

endmodule
