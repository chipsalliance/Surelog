module top (en, a, b);
    input en;
	input a;
	output reg b;

    (* keep = "true" *) wire  int_dat;
`ifndef BUG

    always @(en or a)
		b <= (en)? a : 1'bZ;
`else

    always @(en or a)
		b <= (en)? ~a : 1'bZ;
`endif
endmodule
