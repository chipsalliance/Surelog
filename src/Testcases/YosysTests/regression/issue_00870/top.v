module mux1( select, d, q );

input select;
input[1:0] d;
output     q;

wire      q;
wire      select;
wire[1:0] d;

assign q = d[select];

endmodule

module top(select, d, q);

input[1:0] select;
input[1:0] d;
output     q;

wire      q;
wire[1:0] select;
wire[1:0] d;

wire[1:0] q_tmp;

mux1 m1(
		.select(select[0]),
		.d(d),
		.q(q_tmp[0])
);

mux1 m2(
		.select(select[1]),
		.d(d),
		.q(q_tmp[1])
);

mux1 m3(
		.select(select[0]),
		.d(q_tmp),
		.q(q)
);



endmodule
