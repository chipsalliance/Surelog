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
		.trace_b("__------________________________"),
		.trace_c("________-_______________________"),
		.trace_d("___-_-_-________________________")
	) uut (clock, A, B, C, D);

	assert property (@(posedge clock) A |=> (B throughout (D [->3])) ##1 C);
endmodule

module pass_01 (input clock);
	wire A, B, C, D;

	sequencer #(
		//        01234567890123456789012345678901
		.trace_a("_-______________________________"),
		.trace_b("__-------_______________________"),
		.trace_c("_________-______________________"),
		.trace_d("____-_-_-_______________________")
	) uut (clock, A, B, C, D);

	assert property (@(posedge clock) A |=> (B throughout (D [->3])) ##1 C);
endmodule

module pass_02 (input clock);
	wire A, B, C, D;

	sequencer #(
		//        01234567890123456789012345678901
		.trace_a("_-______________________________"),
		.trace_b("__-------_______________________"),
		.trace_c("_________-______________________"),
		.trace_d("___-__-_-_______________________")
	) uut (clock, A, B, C, D);

	assert property (@(posedge clock) A |=> (B throughout (D [->3])) ##1 C);
endmodule

module fail_03 (input clock);
	wire A, B, C, D;

	sequencer #(
		//        01234567890123456789012345678901
		.trace_a("_-______________________________"),
		.trace_b("__-------_______________________"),
		.trace_c("_________-______________________"),
		.trace_d("___-_-_-________________________")
	) uut (clock, A, B, C, D);

	assert property (@(posedge clock) A |=> (B throughout (D [->3])) ##1 C);
endmodule

module fail_04 (input clock);
	wire A, B, C, D;

	sequencer #(
		//        01234567890123456789012345678901
		.trace_a("_-______________________________"),
		.trace_b("__-------_______________________"),
		.trace_c("_________-______________________"),
		.trace_d("___-____-_______________________")
	) uut (clock, A, B, C, D);

	assert property (@(posedge clock) A |=> (B throughout (D [->3])) ##1 C);
endmodule
