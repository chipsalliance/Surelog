/*
:name: test_plusargs
:description: $test$plusargs test
:tags: 21.6
:type: simulation parsing
*/
module top();

initial begin
	if ($test$plusargs("TEST")) $display("TEST argument found");
	else $display("TEST argument not found");
end

endmodule
