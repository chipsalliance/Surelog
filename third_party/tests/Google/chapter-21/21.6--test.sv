/*
:name: test_plusargs
:description: $test$plusargs test
:should_fail: 0
:tags: 21.6
:type: simulation parsing
*/
module top();

initial begin
	if ($test$plusargs("TEST")) $display("TEST argument found");
	else $display("TEST argument not found");
end

endmodule
