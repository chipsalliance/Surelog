/*
:name: write_task
:description: $write test
:should_fail: 0
:tags: 21.2
:type: simulation parsing
*/
module top();

initial begin
	int val = 1234;
	$write(val);
	$writeb(val);
	$writeo(val);
	$writeh(val);
end

endmodule
