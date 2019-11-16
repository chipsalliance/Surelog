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
		.trace_b("__-__________--_________________"),
		.trace_c("__-----------__-________________"),
		.trace_d("_____________-__-_______________")
	) uut (clock, A, B, C, D);

	assert property (@(posedge clock) (A |=> ((B ##1 !B [*] ##1 B) intersect (C [+] ##1 D)) ##1 B ##1 C ##1 D));
endmodule

module fail_01 (input clock);
	wire A, B, C, D;

	sequencer #(
		//        01234567890123456789012345678901
		.trace_a("_-______________________________"),
		.trace_b("__-_________-_-_________________"),
		.trace_c("__-----------__-________________"),
		.trace_d("_____________-__-_______________")
	) uut (clock, A, B, C, D);

	assert property (@(posedge clock) (A |=> ((B ##1 !B [*] ##1 B) intersect (C [+] ##1 D)) ##1 B ##1 C ##1 D));
endmodule

module fail_02 (input clock);
	wire A, B, C, D;

	sequencer #(
		//        01234567890123456789012345678901
		.trace_a("_-______________________________"),
		.trace_b("__-__________--_________________"),
		.trace_c("__----------___-________________"),
		.trace_d("_____________-__-_______________")
	) uut (clock, A, B, C, D);

	assert property (@(posedge clock) (A |=> ((B ##1 !B [*] ##1 B) intersect (C [+] ##1 D)) ##1 B ##1 C ##1 D));
endmodule

module fail_03 (input clock);
	wire A, B, C, D;

	sequencer #(
		//        01234567890123456789012345678901
		.trace_a("_-______________________________"),
		.trace_b("__-__________-_-________________"),
		.trace_c("__-----------___-_______________"),
		.trace_d("_____________-___-______________")
	) uut (clock, A, B, C, D);

	assert property (@(posedge clock) (A |=> ((B ##1 !B [*] ##1 B) intersect (C [+] ##1 D)) ##1 B ##1 C ##1 D));
endmodule

module fail_04 (input clock);
	wire A, B, C, D;

	sequencer #(
		//        01234567890123456789012345678901
		.trace_a("_-______________________________"),
		.trace_b("__-__________--_________________"),
		.trace_c("__----------___-________________"),
		.trace_d("____________-___-_______________")
	) uut (clock, A, B, C, D);

	assert property (@(posedge clock) (A |=> ((B ##1 !B [*] ##1 B) intersect (C [+] ##1 D)) ##1 B ##1 C ##1 D));
endmodule
