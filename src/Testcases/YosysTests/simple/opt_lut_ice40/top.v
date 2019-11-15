module top(
    input [8:0] a,
    input [8:0] b,
    output [8:0] o1,
    output [2:0] o2,
    input [2:0] c,
    input [2:0] d,
    output [2:0] o3,
    output [2:0] o4,
    input s
);
`ifndef BUG
        assign o1 = (s ? 0 : a + b);
		assign o2 = (s ? a : a - b);
		assign o3 = (s ? 4'b1111 : d + c);
		assign o4 = (s ? d : c - d);
`else
        assign o1 = (s ? 0 : a * b);
		assign o2 = (s ? a : a / b);
		assign o3 = (s ? 4'b1111 : d - c);
		assign o4 = (s ? d : c + d);
`endif

endmodule
