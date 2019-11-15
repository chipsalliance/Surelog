module top    (
out,
i,
clk,
o,
in
);
    output [7:0] out;
    input clk, in;
    reg [7:0] out;
    input i;
    output o;

    always @(posedge clk)
	begin
		out    <= out << 1;
		out[0] <= in;
	end

endmodule
