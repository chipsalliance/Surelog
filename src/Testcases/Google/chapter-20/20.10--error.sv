/*
:name: error_task
:description: $error test
:should_fail: 0
:tags: 20.10
:type: simulation parsing
*/

module top();

initial begin
	$error("error");
end

endmodule
