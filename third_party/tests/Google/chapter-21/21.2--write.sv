/*
:name: write_task
:description: $write test
:tags: 21.2
:type: simulation parsing
*/
module top();

initial begin
	int val = 1234;
	$write(val);
end

endmodule
