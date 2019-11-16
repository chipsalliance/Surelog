/*
:name: timeformat_task
:description: $timeformat test
:should_fail: 0
:tags: 20.4
:type: simulation parsing
*/

`timescale 1 fs / 1 fs

module top();

initial begin
	$timeformat(-9, 5, "ns", 10);
	$display("%t", $realtime);
end

endmodule
