
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
	pmem[   0] = 16'hc00c;
pmem[   1] = 16'hc01b;
pmem[   2] = 16'hc01a;
pmem[   3] = 16'hc019;
pmem[   4] = 16'hc018;
pmem[   5] = 16'hc017;
pmem[   6] = 16'hc016;
pmem[   7] = 16'hc015;
pmem[   8] = 16'hc014;
pmem[   9] = 16'hc013;
pmem[  10] = 16'hc012;
pmem[  11] = 16'hc011;
pmem[  12] = 16'hc010;
pmem[  13] = 16'h2411;
pmem[  14] = 16'hbe1f;
pmem[  15] = 16'he5cf;
pmem[  16] = 16'he0d2;
pmem[  17] = 16'hbfde;
pmem[  18] = 16'hbfcd;
pmem[  19] = 16'he010;
pmem[  20] = 16'he6a0;
pmem[  21] = 16'he0b0;
pmem[  22] = 16'hc001;
pmem[  23] = 16'h921d;
pmem[  24] = 16'h36a3;
pmem[  25] = 16'h07b1;
pmem[  26] = 16'hf7e1;
pmem[  27] = 16'hd028;
pmem[  28] = 16'hc059;
pmem[  29] = 16'hcfe2;
pmem[  30] = 16'h2fe8;
pmem[  31] = 16'h95e6;
pmem[  32] = 16'h95e6;
pmem[  33] = 16'h95e6;
pmem[  34] = 16'he0f0;
pmem[  35] = 16'h5ae0;
pmem[  36] = 16'h4fff;
pmem[  37] = 16'h7087;
pmem[  38] = 16'he021;
pmem[  39] = 16'he030;
pmem[  40] = 16'hc001;
pmem[  41] = 16'h0f22;
pmem[  42] = 16'h958a;
pmem[  43] = 16'hf7ea;
pmem[  44] = 16'h8180;
pmem[  45] = 16'h2b82;
pmem[  46] = 16'h8380;
pmem[  47] = 16'h9508;
pmem[  48] = 16'h2fe8;
pmem[  49] = 16'h95e6;
pmem[  50] = 16'h95e6;
pmem[  51] = 16'h95e6;
pmem[  52] = 16'he0f0;
pmem[  53] = 16'h5ae0;
pmem[  54] = 16'h4fff;
pmem[  55] = 16'h8120;
pmem[  56] = 16'he030;
pmem[  57] = 16'h7087;
pmem[  58] = 16'hc002;
pmem[  59] = 16'h9535;
pmem[  60] = 16'h9527;
pmem[  61] = 16'h958a;
pmem[  62] = 16'hf7e2;
pmem[  63] = 16'h2f82;
pmem[  64] = 16'h7081;
pmem[  65] = 16'h9508;
pmem[  66] = 16'hbd8a;
pmem[  67] = 16'h9508;
pmem[  68] = 16'h931f;
pmem[  69] = 16'h93cf;
pmem[  70] = 16'h93df;
pmem[  71] = 16'he082;
pmem[  72] = 16'hdff9;
pmem[  73] = 16'he0c3;
pmem[  74] = 16'he0d0;
pmem[  75] = 16'h2f8d;
pmem[  76] = 16'hdfe3;
pmem[  77] = 16'h1181;
pmem[  78] = 16'hc01b;
pmem[  79] = 16'h2f8c;
pmem[  80] = 16'hdff1;
pmem[  81] = 16'h2f1c;
pmem[  82] = 16'h0f11;
pmem[  83] = 16'hff10;
pmem[  84] = 16'hc013;
pmem[  85] = 16'h2f41;
pmem[  86] = 16'he050;
pmem[  87] = 16'h2f24;
pmem[  88] = 16'h2f35;
pmem[  89] = 16'h5023;
pmem[  90] = 16'h0931;
pmem[  91] = 16'hff37;
pmem[  92] = 16'hc004;
pmem[  93] = 16'h2f24;
pmem[  94] = 16'h2f35;
pmem[  95] = 16'h5022;
pmem[  96] = 16'h0931;
pmem[  97] = 16'h2f82;
pmem[  98] = 16'h2f93;
pmem[  99] = 16'h9595;
pmem[ 100] = 16'h9587;
pmem[ 101] = 16'h3188;
pmem[ 102] = 16'hf418;
pmem[ 103] = 16'hdfb6;
pmem[ 104] = 16'h0f1c;
pmem[ 105] = 16'hcfe9;
pmem[ 106] = 16'h5fdf;
pmem[ 107] = 16'h5fce;
pmem[ 108] = 16'h31d8;
pmem[ 109] = 16'hf6e9;
pmem[ 110] = 16'he080;
pmem[ 111] = 16'hdfd2;
pmem[ 112] = 16'he080;
pmem[ 113] = 16'he090;
pmem[ 114] = 16'h91df;
pmem[ 115] = 16'h91cf;
pmem[ 116] = 16'h911f;
pmem[ 117] = 16'h9508;
pmem[ 118] = 16'h94f8;
pmem[ 119] = 16'hcfff;
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
