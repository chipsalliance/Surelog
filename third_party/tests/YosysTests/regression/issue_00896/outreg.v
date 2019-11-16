module dut(
	input fast_clk, slow_clk,
	input [3:0] waddr, raddr,
	input [3:0] wdata,
	input wen,
	output [3:0] rdata
);

	reg [3:0] mem[0:15];
	reg [3:0] raddr_reg;

	always @(posedge fast_clk) begin
		if (wen)
			mem[waddr] <= wdata;
	end

	always @(posedge slow_clk)
		raddr_reg <= raddr;

	assign rdata = mem[raddr_reg];
endmodule
