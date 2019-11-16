module top (
    input a,
    input b,
    output [1:0] z);
wire n1, n2;

middle M1(.a(a), .b(b), .c(n1));
assign n2 = n1;  // z[0] in new.v is different from that in old.v due to this line
assign z[0] = n2;

assign z[1] = a | b;
endmodule

module middle (
    input a,
    input b,
    output c);
assign c = a | b;
endmodule
