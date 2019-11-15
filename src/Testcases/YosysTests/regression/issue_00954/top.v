module lutbug ( addr, out);
	input [7:0] addr;
	output [3:0] out;
	assign out = addr[7:4] * addr[3:0];
endmodule
