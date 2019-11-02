
module testbench;

// Generic Inputs
reg clk;
reg i_irq;              // Interrupt request, active high
reg i_firq;             // Fast Interrupt request, active high
reg i_system_rdy;       // Amber is stalled when this is low
reg globrst;

// Wishbone Inputs
reg [31:0] i_wb_dat;
wire       i_wb_ack;
wire       i_wb_err;

// Wishbone Outputs
wire [31:0] o_wb_adr;
wire [ 3:0] o_wb_sel;
wire        o_wb_we;
wire [31:0] o_wb_dat;
wire        o_wb_cyc;
wire        o_wb_stb;


a23_core UUT (
	clk,
	i_irq,
	i_firq,
	i_system_rdy,
	o_wb_adr,
	o_wb_sel,
	o_wb_we,
	i_wb_dat,
	o_wb_dat,
	o_wb_cyc,
	o_wb_stb,
	i_wb_ack,
	i_wb_err,
	globrst
);


initial begin
	clk <= 0;
	#100;
	forever begin
		clk <= ~clk;
		#50;
	end
end

initial begin
	i_irq <= 0;
	i_firq <= 0;
	i_wb_dat <= 0;
	i_system_rdy <= 0;
	globrst <= 0;
	repeat (5) @(posedge clk);
	globrst <= 1;
	repeat (2) @(posedge clk);
	globrst <= 0;
	repeat (3) @(posedge clk);
	i_system_rdy <= 1;
	repeat (5000) @(posedge clk);
	$display("Reached limit of 5000 cpu cycles.");
	$finish;
end

integer output_idx;
reg [7:0] output_buf [1023:0];
event output_eof;

localparam mem_size = 16*1024; // = 64kB
reg [31:0] mem [0:mem_size-1];
reg [31:0] tmp;
integer i;

initial begin
	output_idx = 0;
	for (i=0; i<mem_size; i=i+1)
		mem[i] = 0;
mem[   0] = 32'he3a00000;
mem[   1] = 32'he13ff000;
mem[   2] = 32'he3a00001;
mem[   3] = 32'hee030f10;
mem[   4] = 32'he3a00001;
mem[   5] = 32'hee020f10;
mem[   6] = 32'he3a0d801;
mem[   7] = 32'heb000000;
mem[   8] = 32'heafffffe;
mem[   9] = 32'he3a01201;
mem[  10] = 32'he3a03002;
mem[  11] = 32'he59f0084;
mem[  12] = 32'he92d40f0;
mem[  13] = 32'he3a02003;
mem[  14] = 32'he5813000;
mem[  15] = 32'he3a0c001;
mem[  16] = 32'he3a03000;
mem[  17] = 32'he1a06001;
mem[  18] = 32'he1a012a3;
mem[  19] = 32'he7901101;
mem[  20] = 32'he203401f;
mem[  21] = 32'he011141c;
mem[  22] = 32'h1a00000e;
mem[  23] = 32'he5862000;
mem[  24] = 32'he1a01082;
mem[  25] = 32'he3110001;
mem[  26] = 32'h0a000008;
mem[  27] = 32'he2414003;
mem[  28] = 32'he1a050a4;
mem[  29] = 32'he355003f;
mem[  30] = 32'h8a000006;
mem[  31] = 32'he1a04324;
mem[  32] = 32'he7907104;
mem[  33] = 32'he205501f;
mem[  34] = 32'he187551c;
mem[  35] = 32'he7805104;
mem[  36] = 32'he0811002;
mem[  37] = 32'heafffff2;
mem[  38] = 32'he2833001;
mem[  39] = 32'he3530040;
mem[  40] = 32'he2822002;
mem[  41] = 32'h1affffe7;
mem[  42] = 32'he3a00000;
mem[  43] = 32'he3a03201;
mem[  44] = 32'he5830000;
mem[  45] = 32'he8bd80f0;
mem[  46] = 32'h000000bc;
mem[  47] = 32'h00000000;
mem[  48] = 32'h00000000;
end

reg wb_start_read_d1;
wire wb_start_write = o_wb_stb &&  o_wb_we && !wb_start_read_d1;
wire wb_start_read  = o_wb_stb && !o_wb_we && !i_wb_ack;
assign i_wb_ack = o_wb_stb && ( wb_start_write || wb_start_read_d1 );
assign i_wb_err = 0;

always @(posedge clk)
	wb_start_read_d1 <= wb_start_read;

always @(posedge clk) begin
	if (wb_start_write || wb_start_read) begin
		if (o_wb_adr < mem_size*4) begin
			tmp = mem[o_wb_adr >> 2];
			if (wb_start_write) begin
				if (o_wb_sel[0]) tmp = { tmp[31:24], tmp[23:16], tmp[15:8], o_wb_dat[7:0] };
				if (o_wb_sel[1]) tmp = { tmp[31:24], tmp[23:16], o_wb_dat[15:8], tmp[7:0] };
				if (o_wb_sel[2]) tmp = { tmp[31:24], o_wb_dat[23:16], tmp[15:8], tmp[7:0] };
				if (o_wb_sel[3]) tmp = { o_wb_dat[31:24], tmp[23:16], tmp[15:8], tmp[7:0] };
				mem[o_wb_adr >> 2] <= tmp;
			end
			if (wb_start_read)
				i_wb_dat <= tmp;
			$display("%t MEM %s ADDR %08x: %08x (%b)", $time, o_wb_we ? "WRITE" : "READ ", o_wb_adr, tmp, o_wb_sel);
		end
		if (wb_start_write && o_wb_adr == 32'h10000000) begin
			$display("%t OUTPUT %d", $time, o_wb_dat);
			if (o_wb_dat == 0) begin
				-> output_eof;
			end else begin
				output_buf[output_idx] = o_wb_dat;
				output_idx = output_idx + 1;
			end
		end
	end
end

always @(output_eof) begin
	#1001;
	$display("Got EOF marker on IO port.");
	for (i = 0; i < output_idx; i = i + 1) begin
		$display("+OUT+ %d", output_buf[i]);
	end
	$finish;
end

initial begin
	// $dumpfile("bench.vcd");
	// $dumpvars(0, testbench);
end

endmodule
