
// Posedge Pulse Generator
// Convert a rising edge to a pulse.
// No output on falling edge.

`default_nettype none

module posedge_pulse_generator
#(
    parameter PULSE_LENGTH = 0
)
(
    input   wire    clock,
    input   wire    level_in,
    output  reg     pulse_out
);

    initial begin
        pulse_out = 0;
    end

    wire level_delayed;

    Delay_Line 
    #(
        .DEPTH  (PULSE_LENGTH), 
        .WIDTH  (1)
    )  
    pulse_length_adjuster
    (
        .clock   (clock),
        .in      (level_in),
        .out     (level_delayed)
    );

    always @(*) begin
        pulse_out <= level_in & ~level_delayed;
    end

endmodule

