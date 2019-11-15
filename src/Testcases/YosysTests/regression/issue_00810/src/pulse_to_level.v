
// Latch pulse to level, until cleared

module pulse_to_level
(
    input   wire    clock,
    input   wire    clear,
    input   wire    pulse_in,
    output  reg     level_out
);

    initial begin
        level_out = 1'b0;
    end

    always @(posedge clock) begin
        level_out = pulse_in | level_out;
        level_out = (clear == 1'b1) ? 1'b0 : level_out;
    end

endmodule

