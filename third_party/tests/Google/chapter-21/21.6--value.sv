/*
:name: value_plusargs
:description: $value$plusargs test
:should_fail: 0
:tags: 21.6
:type: simulation parsing
*/
module top();

integer i;

initial begin
	if ($value$plusargs("TEST=%d", i)) $display("i=%d", i);
	else
		$display("TEST not found");
end

endmodule
