/*
:name: array_addressing
:description: array addressing test
:should_fail: 0
:tags: 11.5.2
*/
module top();
logic [7:0] mem [0:1023];
logic [7:0] a;

initial begin
	a = mem[123];
end

endmodule
