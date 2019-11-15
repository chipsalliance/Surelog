/*
:name: atan2_function
:description: $atan2 test
:should_fail: 0
:tags: 20.8
:type: simulation parsing
*/

module top();

initial begin
	$display("%f", $atan2(2.1, 3.7));
end

endmodule
