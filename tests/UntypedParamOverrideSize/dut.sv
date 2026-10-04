// An UNTYPED parameter (`parameter LFSR_POLY = 31'h10000001`: no data type,
// no range) takes the type and size of its final value (LRM 6.20.2), so
// overridden with `58'h8000000001` it is 58 bits wide.  Read inside a
// generate loop, Surelog resized the override to the DEFAULT's 31 bits and
// bit 39 of the polynomial vanished (verilog-ethernet's 10G scrambler).
module lfsr_like #(
    parameter LFSR_WIDTH = 31,
    parameter LFSR_POLY = 31'h10000001
) (
    input  wire [LFSR_WIDTH-1:0] state_in,
    output wire [LFSR_WIDTH-1:0] state_out
);
genvar n;
generate
for (n = 0; n < LFSR_WIDTH; n = n + 1) begin : g
    wire [LFSR_WIDTH-1:0] mask = LFSR_POLY >> n;
    assign state_out[n] = ^(state_in & mask);
end
endgenerate
endmodule

module dut (input wire [57:0] state_in, output wire [57:0] state_out);
lfsr_like #(
    .LFSR_WIDTH(58),
    .LFSR_POLY(58'h8000000001)
) u (
    .state_in(state_in),
    .state_out(state_out)
);
endmodule
