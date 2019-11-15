module inst(a,b);
output b;
input a;
assign b = ~a;
endmodule

module top(a,b);
input a;
output b;
inst inst(
.a(a),
.b(1'b1)
);
endmodule
