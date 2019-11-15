module mcve(i_clk, i_value, o_value);
	input	wire		i_clk;
	input	wire	[1:0]	i_value;
	output	reg	[3:0]	o_value;

	initial	o_value = 0;
	always @(posedge i_clk)
	case(i_value)
	2'b00: begin end
`ifndef BUG
	2'b01: o_value <= 4'h2;
`else
	2'b01: o_value <= 4'h3;
`endif
	2'b10: o_value <= 4'h4;
	2'b11: o_value <= 4'h8;
	default: o_value <= 4'h1;
	endcase

endmodule

module top (
input clk,
input [1:0] I,
output [3:0] O
);

mcve u_mcve (
		.i_clk(clk),
        .i_value(I),
        .o_value(O)
    );

endmodule
