
module testbench;

parameter pmem_width = 11;
parameter dmem_width = 13;

// navre inputs
reg clk;
reg rst;
reg [15:0] pmem_d;
reg [7:0] dmem_di;
reg [7:0] io_di;
reg [7:0] irq;

// navre outputs
wire pmem_ce;
wire [pmem_width-1:0] pmem_a;
wire dmem_we;
wire [dmem_width-1:0] dmem_a;
wire [7:0] dmem_do;
wire io_re;
wire io_we;
wire [5:0] io_a;
wire [7:0] io_do;
wire [7:0] irq_ack;
wire [pmem_width-1:0] dbg_pc;

softusb_navre #(
	pmem_width,
	dmem_width
) UUT (
	clk,
	rst,

	pmem_ce,
	pmem_a,
	pmem_d,

	dmem_we,
	dmem_a,
	dmem_di,
	dmem_do,

	io_re,
	io_we,
	io_a,
	io_do,
	io_di,

	irq,
	irq_ack,
	dbg_pc
);

integer cycles;
initial begin
	clk <= 1;
	rst <= 1;
	cycles = 0;
	while (cycles < 8) begin
		#50; clk <= ~clk;
		cycles = cycles + 1;
		#50; clk <= ~clk;
	end
	rst <= #20 0;
	forever begin
		#50; clk <= ~clk;
		cycles = cycles + 1;
		#50; clk <= ~clk;
		if (cycles == 10000) begin
			$display("Reached limit of 10000 cpu cycles.");
			$finish;
		end
	end
end

reg [15:0] addr;
reg [15:0] pmem [2**pmem_width-1:0];
reg [ 7:0] dmem [2**dmem_width-1:0];

integer output_idx;
reg [7:0] output_buf [1023:0];
event output_eof;

integer i;
initial begin
	for (i=0; i < 2**pmem_width; i = i+1) begin
		pmem[i] = 0;
	end
	for (i=0; i < 2**dmem_width; i = i+1) begin
		dmem[i] = 0;
	end
	`include "sieve.v"
	output_idx = 0;
end

always @(posedge clk) begin
	if (rst) begin
		pmem_d <= 0;
		irq <= 0;
	end else if (pmem_ce) begin
		addr = pmem_a * 2;
		$display("+LOG+ %t PR @%x %x", $time, addr, pmem[pmem_a]);
		pmem_d <= pmem[pmem_a];
	end
	if (dmem_we) begin
		addr = dmem_a;
		$display("+LOG+ %t DW @%x   %x", $time, addr, dmem_do);
		dmem[dmem_a] <= dmem_do;
	end
	if (io_we && io_a == 42) begin
		addr = io_a;
		$display("+LOG+ %t IO @%x   %x  <---", $time, addr, io_do);
		if (io_do == 0) begin
			-> output_eof;
		end else begin
			output_buf[output_idx] = io_do;
			output_idx = output_idx + 1;
		end
	end
	dmem_di <= dmem[dmem_a];
	io_di <= 0;
end

always @(output_eof) begin
	#1001;
	$display("Got EOF marker on IO port.");
	for (i = 0; i < output_idx; i = i + 1) begin
		$display("+OUT+ %t %d", $time, output_buf[i]);
	end
	$finish;
end

initial begin
	// $dumpfile("bench.vcd");
	// $dumpvars(0, testbench);
end

endmodule
