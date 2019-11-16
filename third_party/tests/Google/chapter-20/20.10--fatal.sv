/*
:name: fatal_task
:description: $fatal test
:should_fail: 0
:tags: 20.10
:type: simulation parsing
*/

module top();

initial begin
	$fatal(2, "fatal");
end

endmodule
