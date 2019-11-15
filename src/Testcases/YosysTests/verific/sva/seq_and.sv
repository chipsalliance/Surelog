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
		.trace_a("_---____________________________"),
		.trace_b("_----___________________________"),
		.trace_c("_____-__________________________"),
		.trace_d("________________________________")
	) uut (clock, A, B, C, D);

	assert property (@(posedge clock) (A [*3] and B [*4]) |=> C);
endmodule

module fail_01 (input clock);
	wire A, B, C, D;

	sequencer #(
		//        01234567890123456789012345678901
		.trace_a("_---____________________________"),
		.trace_b("_----___________________________"),
		.trace_c("____-___________________________"),
		.trace_d("________________________________")
	) uut (clock, A, B, C, D);

	assert property (@(posedge clock) (A [*3] and B [*4]) |=> C);
endmodule

module fail_02 (input clock);
	wire A, B, C, D;

	sequencer #(
		//        01234567890123456789012345678901
		.trace_a("_---____________________________"),
		.trace_b("_----___________________________"),
		.trace_c("______-_________________________"),
		.trace_d("________________________________")
	) uut (clock, A, B, C, D);

	assert property (@(posedge clock) (A [*3] and B [*4]) |=> C);
endmodule
