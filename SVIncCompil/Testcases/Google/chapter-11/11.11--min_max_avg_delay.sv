/*
:name: min_max_avg_delay
:description: minimum, typical and maximum delay expressions test
:should_fail: 0
:tags: 11.11
*/
module top();

initial begin
	#(100:200:300) $display("Done");
end

endmodule
