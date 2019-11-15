
// Skid Buffer Datapath

// Feed the data_out register either from the data_in, or a buffered copy of
// data_in. Write to registers only if enabled by control.

// Funneling into a single data_out register rather than selecting between two
// equal output registers avoids a mux after registers, fed by two data
// streams (thus more routing and delay). A single output register also
// retimes more easily, without having to figure out ahead of time if the
// logic allows it.

`default_nettype none

module skid_buffer_datapath
#(
    parameter WORD_WIDTH = 0
)
(
    input   wire                        clock,

    // Data
    input   wire    [WORD_WIDTH-1:0]    data_in,
    output  reg     [WORD_WIDTH-1:0]    data_out,

    // Control
    input   wire                        data_out_wren,
    input   wire                        data_buffer_wren,
    input   wire                        use_buffered_data    
);

// --------------------------------------------------------------------------

    localparam WORD_ZERO = {WORD_WIDTH{1'b0}};

    initial begin
        data_out = WORD_ZERO;
    end

// --------------------------------------------------------------------------
// Set-up the default values to match the "empty" state of the skid buffer, so
// the first data_in to arrive ends up in the data_out by default.  We don't
// have to worry about state, just pass the data through unless told
// otherwise.

    reg [WORD_WIDTH-1:0] data_buffer    = WORD_ZERO;
    reg [WORD_WIDTH-1:0] selected_data  = WORD_ZERO;

    always @(*) begin
        selected_data = (use_buffered_data == 1'b1) ? data_buffer : data_in;
    end

    always @(posedge clock) begin
        data_buffer <= (data_buffer_wren == 1'b1) ? data_in       : data_buffer;
        data_out    <= (data_out_wren    == 1'b1) ? selected_data : data_out;
    end

endmodule

