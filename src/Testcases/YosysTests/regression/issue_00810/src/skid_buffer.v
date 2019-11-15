
// Skid Buffer: decouples two sides of a ready/valid handshake to allow
// back-to-back transfers without a combinational path between sender and
// receiver (or master and slave).

// A skid-buffer is a degenerate FIFO with only two entries.  It is useful
// when you need to pipeline the path between a sender and a receiver for
// concurrency and/or timing, but not to smooth-out data rate mismatches.  It
// also only requires two data registers, which at this scale is smaller than
// LUTRAMs or Block RAMs (depending on implementation), and has more freedom
// of placement and routing.

// This skid buffer assumes AXI behaviour for valid/ready handshakes.

`default_nettype none

module skid_buffer
#(
    parameter WORD_WIDTH = 0
)
(
    input   wire                        clock,

    // Slave interface
    input   wire                        s_valid,
    output  wire                        s_ready,
    input   wire    [WORD_WIDTH-1:0]    s_data,

    // Master interface
    output  wire                        m_valid,
    input   wire                        m_ready,
    output  wire    [WORD_WIDTH-1:0]    m_data
);

// --------------------------------------------------------------------------
// The FSM handles the master and slave port handshakes, and provides the
// datapath control signals.

    wire data_out_wren;
    wire data_buffer_wren;
    wire use_buffered_data;

    skid_buffer_fsm
    // No parameters
    controlpath
    (
        .clock              (clock),

        .s_valid            (s_valid),
        .s_ready            (s_ready),

        .m_valid            (m_valid),
        .m_ready            (m_ready),

        .data_out_wren      (data_out_wren),
        .data_buffer_wren   (data_buffer_wren),
        .use_buffered_data  (use_buffered_data)

    );

// --------------------------------------------------------------------------
// The datapath stores and steers the data.

    skid_buffer_datapath
    #(
        .WORD_WIDTH         (WORD_WIDTH)
    )
    datapath
    (
        .clock              (clock),

        .data_in            (s_data),
        .data_out           (m_data),

        .data_out_wren      (data_out_wren), 
        .data_buffer_wren   (data_buffer_wren),
        .use_buffered_data  (use_buffered_data)
    );

endmodule

