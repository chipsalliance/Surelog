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
		.trace_a("_-______________________________"),
		.trace_b("__-------------_________________"),
		.trace_c("______-________-________________"),
		.trace_d("_______-________________________")
	) uut (clock, A, B, C, D);

	assert property (@(posedge clock) (first_match(A ##1 B [*] ##1 C) |=> D));
endmodule

module fail_01 (input clock);
	wire A, B, C, D;

	sequencer #(
		//        01234567890123456789012345678901
		.trace_a("_-______________________________"),
		.trace_b("__-------------_________________"),
		.trace_c("______-________-________________"),
		.trace_d("_______-________________________")
	) uut (clock, A, B, C, D);

	assert property (@(posedge clock) (A ##1 B [*] ##1 C |=> D));
endmodule

module pass_02 (input clock);
	wire A, B, C, D;

	sequencer #(
		//        01234567890123456789012345678901
		.trace_a("_-___-__________________________"),
		.trace_b("__-------------_________________"),
		.trace_c("______-____-___-________________"),
		.trace_d("_______-________________________")
	) uut (clock, A, B, C, D);

	assert property (@(posedge clock) (first_match(A ##1 B [*] ##1 C) |=> D));
endmodule

module fail_03 (input clock);
	wire A, B, C, D;

	sequencer #(
		//        01234567890123456789012345678901
		.trace_a("_-___-__________________________"),
		.trace_b("__-------------_________________"),
		.trace_c("______-____-___-________________"),
		.trace_d("_______-________________________")
	) uut (clock, A, B, C, D);

	assert property (@(posedge clock) (first_match(A ##1 B [+] ##1 C) |=> D));
endmodule

module pass_04 (input clock);
	wire A, B, C, D;

	sequencer #(
		//        01234567890123456789012345678901
		.trace_a("_-__-___________________________"),
		.trace_b("__-------------_________________"),
		.trace_c("______-____-___-________________"),
		.trace_d("_______-________________________")
	) uut (clock, A, B, C, D);

	assert property (@(posedge clock) (first_match(A ##1 B [*] ##1 C) |=> D));
endmodule

module pass_05 (input clock);
	wire A, B, C, D;

	sequencer #(
		//        01234567890123456789012345678901
		.trace_a("_-___-__________________________"),
		.trace_b("__-------------_________________"),
		.trace_c("______-____-___-________________"),
		.trace_d("_______-____-___________________")
	) uut (clock, A, B, C, D);

	assert property (@(posedge clock) (first_match(A ##1 B [*] ##1 C) |=> D));
endmodule

module fail_06 (input clock);
	wire A, B, C, D;

	sequencer #(
		//        01234567890123456789012345678901
		.trace_a("_-____-_________________________"),
		.trace_b("__-------------_________________"),
		.trace_c("______-____-___-________________"),
		.trace_d("_______-________________________")
	) uut (clock, A, B, C, D);

	assert property (@(posedge clock) (first_match(A ##1 B [*] ##1 C) |=> D));
endmodule
