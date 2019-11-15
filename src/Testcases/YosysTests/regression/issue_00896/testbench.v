`include "../outreg.v"

module tb;
	reg fast_clk, slow_clk;

	initial begin
		$dumpfile("testbench.vcd");
		$dumpvars(0, tb);
		repeat (80) @(posedge slow_clk);
		$display("OKAY");
		$finish;
	end

	always #4 fast_clk = (fast_clk === 1'b0);
	always #12 slow_clk = (slow_clk === 1'b0);

	reg [7:0] wdata = 1;
	always @(posedge fast_clk) wdata <= {wdata[6:0], wdata[7] ^ wdata[2]};

	reg [3:0] waddr = 0;
	always @(posedge fast_clk) waddr <= waddr + 1'b1;

	reg [3:0] raddr = 0;
	always @(posedge slow_clk) raddr <= raddr + 1'b1;


	wire [3:0] rdata, rdata_postsyn;

	dut dut_i(
		.fast_clk(fast_clk), .slow_clk(slow_clk),
		.raddr(raddr), .waddr(waddr), .wen(1'b1),
		.wdata(wdata[3:0]), .rdata(rdata)
	);

	dut_syn dut_syn_i(
		.fast_clk(fast_clk), .slow_clk(slow_clk),
		.raddr(raddr), .waddr(waddr), .wen(1'b1),
		.wdata(wdata[3:0]), .rdata(rdata_postsyn)
	);
	always @(posedge fast_clk)
		if (rdata_postsyn != rdata) begin
			$display("ERROR");
			$finish;
		end
endmodule
