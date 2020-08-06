/*
:name: multi_dim_array_addressing
:description: multi-dimensional array addressing test
:tags: 11.5.2
*/
module top();
logic [7:0] mem [0:1023][0:3];
logic [7:0] a;

initial begin
	a = mem[123][2];
end

endmodule
