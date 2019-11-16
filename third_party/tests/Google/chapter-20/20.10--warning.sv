/*
:name: warning_task
:description: $warning test
:should_fail: 0
:tags: 20.10
:type: simulation parsing
*/

module top();

initial begin
	$warning("warning");
end

endmodule
