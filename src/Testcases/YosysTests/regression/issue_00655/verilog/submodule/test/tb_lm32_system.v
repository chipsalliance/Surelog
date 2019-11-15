/*
 * LatticeMico32
 * System Test Bench
 *
 * Copyright (c) 2012 Michael Walle <michael@walle.cc>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. The name of the author may not be used to endorse or promote products
 *    derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 * IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

`include "lm32_include.v"

module soc();

integer i;

reg sys_rst;
reg sys_clk;
reg [31:0] interrupt;

reg i_ack;
wire [31:0] i_adr;
wire i_cyc;
wire [31:0] i_dat;
wire i_stb;

reg d_ack;
wire [31:0] d_adr;
wire d_cyc;
wire [31:0] d_dat_i;
wire [31:0] d_dat_o;
wire [3:0] d_sel;
wire d_stb;

lm32_top lm32(
	.clk_i(sys_clk),
	.rst_i(sys_rst),

	.interrupt(interrupt),

	.I_ACK_I(i_ack),
	.I_ADR_O(i_adr),
	.I_BTE_O(),
	.I_CTI_O(),
	.I_CYC_O(i_cyc),
	.I_DAT_I(i_dat),
	.I_DAT_O(),
	.I_ERR_I(1'b0),
	.I_LOCK_O(),
	.I_RTY_I(1'b0),
	.I_SEL_O(),
	.I_STB_O(i_stb),
	.I_WE_O(),

	.D_ACK_I(d_ack),
	.D_ADR_O(d_adr),
	.D_BTE_O(),
	.D_CTI_O(),
	.D_CYC_O(d_cyc),
	.D_DAT_I(d_dat_i),
	.D_DAT_O(d_dat_o),
	.D_ERR_I(1'b0),
	.D_LOCK_O(),
	.D_RTY_I(1'b0),
	.D_SEL_O(d_sel),
	.D_STB_O(d_stb),
	.D_WE_O(d_we)
);

// clock
initial sys_clk = 1'b0;
always #5 sys_clk = ~sys_clk;

// reset
initial begin
	sys_rst = 1'b1;
	#20
	sys_rst = 1'b0;
end

// memory
reg [7:0] mem[0:65536];
initial begin
	for(i=0;i<65536;i=i+1)
		mem[i] = 8'b0;
end

wire [31:0] dmem_dat_i;
reg [31:0] dmem_dat_o;
wire [13:0] dmem_adr;
wire [3:0] dmem_we;
always @(posedge sys_clk) begin
	if(dmem_we[0]) mem[{dmem_adr, 2'b11}] <= dmem_dat_i[7:0];
	if(dmem_we[1]) mem[{dmem_adr, 2'b10}] <= dmem_dat_i[15:8];
	if(dmem_we[2]) mem[{dmem_adr, 2'b01}] <= dmem_dat_i[23:16];
	if(dmem_we[3]) mem[{dmem_adr, 2'b00}] <= dmem_dat_i[31:24];
	dmem_dat_o[7:0]   <= mem[{dmem_adr, 2'b11}];
	dmem_dat_o[15:8]  <= mem[{dmem_adr, 2'b10}];
	dmem_dat_o[23:16] <= mem[{dmem_adr, 2'b01}];
	dmem_dat_o[31:24] <= mem[{dmem_adr, 2'b00}];
end
reg [31:0] pmem_dat_o;
wire [13:0] pmem_adr;
always @(posedge sys_clk) begin
	pmem_dat_o[7:0]   <= mem[{pmem_adr, 2'b11}];
	pmem_dat_o[15:8]  <= mem[{pmem_adr, 2'b10}];
	pmem_dat_o[23:16] <= mem[{pmem_adr, 2'b01}];
	pmem_dat_o[31:24] <= mem[{pmem_adr, 2'b00}];
end

// uart
always @(posedge sys_clk) begin
	if(d_cyc & d_stb & d_we & d_ack)
		if(d_adr == 32'hff000000)
			$write("%c", d_dat_o[7:0]);
end

// wishbone interface for instruction bus
always @(posedge sys_clk) begin
	if(sys_rst)
		i_ack <= 1'b0;
	else begin
		i_ack <= 1'b0;
		if(i_cyc & i_stb & ~i_ack)
			i_ack <= 1'b1;
	end
end

assign i_dat = pmem_dat_o;
assign pmem_adr = i_adr[15:2];

task dump_processor_state;
begin
	$display("Processor state:");
	$display("  PSW=%08x", lm32.cpu.psw);
	$display("  IE=%08x IP=%08x IM=%08x",
		lm32.cpu.interrupt_unit.ie,
		lm32.cpu.interrupt_unit.ip,
		lm32.cpu.interrupt_unit.im
	);
	for(i=0; i<32; i=i+1) begin
		if(i%4 == 0)
			$write("  ");
		$write("r%02d=%08x ", i, lm32.cpu.reg_0.mem[i]);
		if((i+1)%4 == 0)
			$write("\n");
	end
end
endtask

// QEMU test core
reg [15:0] testname_adr;
reg [8*32:0] testname;
reg testname_end;
always @(posedge sys_clk) begin
	if(d_cyc & d_stb & d_we & d_ack)
	begin
		if(d_adr == 32'hffff0000)
			$finish;
		else if(d_adr == 32'hffff0004) begin
			// is there any better way to do this?
			testname_end = 1'b0;
			for(i=0; i<32; i=i+1) begin
				testname = testname << 8;
				if(testname_end == 1'b0) begin
					testname[7:0] = mem[testname_adr+i];
					if(mem[testname_adr+i] == 8'b0)
						testname_end = 1'b1;
				end else
					testname[7:0] = 8'b0;
			end
			$display("TC %-32s %s", testname, (|d_dat_o) ? "FAILED" : "OK");
			if(|d_dat_o)
				dump_processor_state();
		end
		else if(d_adr == 32'hffff0008)
			testname_adr <= d_dat_o[15:0];
	end
end

// wishbone interface for data bus
always @(posedge sys_clk) begin
	if(sys_rst)
		d_ack <= 1'b0;
	else begin
		d_ack <= 1'b0;
		if(d_cyc & d_stb & ~d_ack)
			d_ack <= 1'b1;
	end
end

assign d_dat_i = dmem_dat_o;
assign dmem_dat_i = d_dat_o;
assign dmem_adr = d_adr[15:2];
assign dmem_we = {4{d_cyc & d_stb & d_we & ~|d_adr[31:16]}} & d_sel;

// interrupts
initial interrupt <= 32'b0;

// simulation end request
always @(posedge sys_clk) begin
	if(d_cyc & d_stb & d_we & d_ack)
		if(d_adr == 32'hdead0000 && d_dat_o == 32'hbeef)
			$finish;
end

// traces
`ifdef TB_ENABLE_WB_TRACES
always @(posedge sys_clk) begin
	if(i_cyc & i_stb & i_ack)
		$display("i load  @%08x %08x", i_adr, i_dat);
	if(d_cyc & d_stb & ~d_we & d_ack)
		$display("d load  @%08x %08x", d_adr, d_dat_o);
	if(d_cyc & d_stb & d_we & d_ack)
		$display("d store @%08x %08x", d_adr, d_dat_o);
end
`endif

`ifdef TB_ENABLE_TLB_TRACES
always @(posedge sys_clk)
begin
	if (lm32.cpu.instruction_unit.itlb.write_port_enable)
		$display("itlb write @%04x 0x%08x",
				lm32.cpu.instruction_unit.itlb.write_address,
				lm32.cpu.instruction_unit.itlb.write_data);
	if (lm32.cpu.load_store_unit.dtlb.write_port_enable)
		$display("dtlb write @%04x 0x%08x",
				lm32.cpu.instruction_unit.itlb.write_address,
				lm32.cpu.instruction_unit.itlb.write_data);
end
`endif

// dump signals
reg [256*8:0] vcdfile;
initial begin
	if($value$plusargs("dump=%s", vcdfile)) begin
		$dumpfile(vcdfile);
		$dumpvars(0, soc);
	end
end

// init memory
reg [256*8:0] prog;
initial begin
	if(! $value$plusargs("prog=%s", prog)) begin
		$display("ERROR: please specify +prog=<file>.vh to start.");
		$finish;
	end
end

initial $readmemh(prog, mem);

// trace pipeline
reg [256*8:0] tracefile;
integer trace_started;
integer trace_enabled;
integer cycle;
integer tracefd;
initial begin
	if($value$plusargs("trace=%s", tracefile)) begin
		trace_enabled = 1;
		cycle = 0;
		tracefd = $fopen(tracefile);
		trace_started = 0;
	end else
		trace_enabled = 0;
end
`ifdef CFG_ICACHE_ENABLED
assign icache_ready = lm32.cpu.instruction_unit.icache.state != 1;
`else
assign icache_ready = `TRUE;
`endif
`ifdef CFG_DCACHE_ENABLED
assign dcache_ready = lm32.cpu.load_store_unit.dcache.state != 1;
`else
assign dcache_ready = `TRUE;
`endif
always @(posedge sys_clk) begin
	// wait until icache and dcache init is done
	if(!trace_started && icache_ready && dcache_ready)
		trace_started = 1;
	if(trace_enabled && trace_started) begin
		$fwrite(tracefd, "%-d ", cycle);
`ifdef CFG_ICACHE_ENABLED
		$fwrite(tracefd, "%x ", {lm32.cpu.instruction_unit.pc_a, 2'b00});
		$fwrite(tracefd, "%1d ", lm32.cpu.valid_a);
`endif
		$fwrite(tracefd, "%x ", {lm32.cpu.instruction_unit.pc_f, 2'b00});
		$fwrite(tracefd, "%1d ", lm32.cpu.kill_f);
		$fwrite(tracefd, "%1d ", lm32.cpu.valid_f);
		$fwrite(tracefd, "%x ", {lm32.cpu.instruction_unit.pc_d, 2'b00});
		$fwrite(tracefd, "%1d ", lm32.cpu.kill_d);
		$fwrite(tracefd, "%1d ", lm32.cpu.valid_d);
		$fwrite(tracefd, "%x ", {lm32.cpu.instruction_unit.pc_x, 2'b00});
		$fwrite(tracefd, "%1d ", lm32.cpu.kill_x);
		$fwrite(tracefd, "%1d ", lm32.cpu.valid_x);
		$fwrite(tracefd, "%x ", {lm32.cpu.instruction_unit.pc_m, 2'b00});
		$fwrite(tracefd, "%1d ", lm32.cpu.kill_m);
		$fwrite(tracefd, "%1d ", lm32.cpu.valid_m);
		$fwrite(tracefd, "%x ", {lm32.cpu.instruction_unit.pc_w, 2'b00});
		$fwrite(tracefd, "%1d ", lm32.cpu.kill_w);
		$fwrite(tracefd, "%1d ", lm32.cpu.valid_w);
		$fwrite(tracefd, "\n");
		cycle = cycle + 1;
	end
end

endmodule
