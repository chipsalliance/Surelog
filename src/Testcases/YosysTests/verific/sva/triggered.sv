module sequencer #(
	//                              01234567890123456789012345678901
	parameter [32*8-1:0] trace_a = "________________________________",
	parameter [32*8-1:0] trace_b = "________________________________",
	parameter [32*8-1:0] trace_c = "________________________________",
	parameter [32*8-1:0] trace_d = "________________________________"

) (
	input clock,
	output A, B, C, D
);
	integer t = 0;
	always @(posedge clock) t <= t + (t < 31);

	assign A = trace_a[8*(31-t) +: 8] == "-";
	assign B = trace_b[8*(31-t) +: 8] == "-";
	assign C = trace_c[8*(31-t) +: 8] == "-";
	assign D = trace_d[8*(31-t) +: 8] == "-";
endmodule

module pass_00 (input clock);
	wire A, B, C, D;

	sequencer #(
		//        01234567890123456789012345678901
		.trace_a("_------------___________________"),
		.trace_b("____----------__________________"),
		.trace_c("___-_________-__________________"),
		.trace_d("____________---_________________")
	) uut (clock, A, B, C, D);

	sequence aac;
		@(posedge clock)
		A [+] ##1 C;
	endsequence

	sequence cbb;
		@(posedge clock)
		C ##1 B [+];
	endsequence

	sequence ddd;
		@(posedge clock)
		D [*3];
	endsequence

	assert property (@(posedge clock) aac.triggered && cbb.triggered |=> ddd.triggered);
endmodule

module fail_01 (input clock);
	wire A, B, C, D;

	sequencer #(
		//        01234567890123456789012345678901
		.trace_a("_------------___________________"),
		.trace_b("____----------__________________"),
		.trace_c("___-_________-__________________"),
		.trace_d("___________---__________________")
	) uut (clock, A, B, C, D);

	sequence aac;
		@(posedge clock)
		A [+] ##1 C;
	endsequence

	sequence cbb;
		@(posedge clock)
		C ##1 B [+];
	endsequence

	sequence ddd;
		@(posedge clock)
		D [*3];
	endsequence

	assert property (@(posedge clock) aac.triggered && cbb.triggered |=> ddd.triggered);
endmodule

module pass_02 (input clock);
	wire A, B, C, D;

	sequencer #(
		//        01234567890123456789012345678901
		.trace_a("_------------___________________"),
		.trace_b("_____---------__________________"),
		.trace_c("___-_________-__________________"),
		.trace_d("________________________________")
	) uut (clock, A, B, C, D);

	sequence aac;
		@(posedge clock)
		A [+] ##1 C;
	endsequence

	sequence cbb;
		@(posedge clock)
		C ##1 B [+];
	endsequence

	sequence ddd;
		@(posedge clock)
		D [*3];
	endsequence

	assert property (@(posedge clock) aac.triggered && cbb.triggered |=> ddd.triggered);
endmodule
