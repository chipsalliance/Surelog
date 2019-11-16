module top    (
out,
clk,
in
);
    output [7:0] out;
    input clk, in;
    reg [7:0] out;

    always @(posedge clk)
	begin
`ifndef BUG
		out    <= out << 1;
		out[0] <= in;
`else
	out <= 8'bZZZZZZZZ;
`endif
	end

endmodule
