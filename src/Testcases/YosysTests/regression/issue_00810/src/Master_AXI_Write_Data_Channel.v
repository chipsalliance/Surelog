
// Master AXI Write Data Channel

// A write channel which connects a system register write to an AXI data write

// The control interface enables the start of a write data transaction by
// raising and holding control_enable until control_done is also raised (AXI
// ready/valid handshake). The control_done signal goes high when all the AXI
// data has been written out, based on the provided write count from
// a preceeding AXI write address transaction.

// Once started, the write channel raises system_ready and accepts a data word
// from the system when it raises system_valid for one cycle. For each
// consecutive cycle that system_valid and system_ready are high, a word of
// data is transfered.

// Writing to the system interface (raising system_valid) while system_ready
// is low and not holding the system_data until system_ready goes high will
// lose the written data. This works just like an AXI valid/ready handshake.

// Once the skid buffer in the write channel has accepted a data word it will
// raise wvalid and transfer the data when wready is also high in the same
// cycle. The skid buffer can transfer consecutive data words in consecutive
// cycles.

// The write channel asserts wlast on the last AXI data word sent out, which
// is calculated based on the axlen input previous set by an AXI write address
// transaction. The counter is initialized by the rising edge of
// control_enable.

// There is no error handling as any write errors are reported on the AXI
// write response interface after the write channel has completed all
// transfers. All write data transfers MUST be performed, else wlast will not
// be raised to complete the write data channel operation.

`default_nettype none

module Master_AXI_Write_Data_Channel
#(
    parameter WORD_WIDTH    = 0,
    parameter BYTE_COUNT    = 0, // set to clog2(WORD_WIDTH)

    // Do not alter at instantiation. Set by AXI4 spec.
    parameter AXLEN_WIDTH   = 8 
)
(
    input   wire                        clock,

    // System interface
    input   wire    [WORD_WIDTH-1:0]    system_data,
    input   wire                        system_valid,
    output  wire                        system_ready,

    // Control interface
    input   wire                        control_enable,
    output  reg                         control_done,

    // Internal, from write address channel
    input   wire    [AXLEN_WIDTH-1:0]   axlen,

    // AXI interface
    output  wire    [WORD_WIDTH-1:0]    wdata,
    output  reg     [BYTE_COUNT-1:0]    wstrb,
    output  wire                        wlast,
    output  wire                        wvalid,
    input   wire                        wready
);

// --------------------------------------------------------------------------
// We only do whole-word transfers, so the write strobe is always all-ones.

    localparam STROBE = {BYTE_COUNT{1'b1}};

    always @(*) begin
        wstrb = STROBE;
    end

// --------------------------------------------------------------------------
// Signal start of new transaction after end of previous one.

    wire transaction_start;

    posedge_pulse_generator
    #(
        .PULSE_LENGTH   (1)
    )
    transaction
    (
        .clock          (clock),
        .level_in       (control_enable),
        .pulse_out      (transaction_start)
    );


// --------------------------------------------------------------------------
// When idle or done, disconnect the system interface from the skid buffer, so
// the system does not initialize a transfer by accident and store data in the
// skid buffer, forever corrupting future data write counts.

// Unlike the read data channel, we don't disconnect the AXI interface as it
// will stop signaling valid data once it empties itself.

    wire system_valid_internal;
    wire system_ready_internal;

    Annuller
    #(
        .WORD_WIDTH (1)
    )
    master_valid
    (
        .annul      (control_enable == 1'b0),
        .in         (system_valid),
        .out        (system_valid_internal)
    );

    Annuller
    #(
        .WORD_WIDTH (1)
    )
    master_ready
    (
        .annul      (control_enable == 1'b0),
        .in         (system_ready_internal),
        .out        (system_ready)
    );

// --------------------------------------------------------------------------
// Signal each system data write (if not disconnected).

    reg system_write_accepted = 1'b0;

    always @(*) begin
        system_write_accepted <= (system_ready == 1'b1) && (system_valid_internal == 1'b1);
    end

// --------------------------------------------------------------------------
// Latch the data word count at transaction start. Counts down to zero.

    localparam COUNT_ZERO = {AXLEN_WIDTH{1'b0}};

    reg  [AXLEN_WIDTH-1:0] remaining_writes = COUNT_ZERO;

    wire [AXLEN_WIDTH-1:0] count_out;
    wire                   count_out_wren;
    wire                   last_word;

    Down_Counter_Zero
    #(
        .WORD_WIDTH     (AXLEN_WIDTH)
    )
    writes
    (
        .run            (system_write_accepted),
        .count_in       (remaining_writes),
        .load_wren      (transaction_start),
        .load_value     (axlen),
        .count_out_wren (count_out_wren),
        .count_out      (count_out),
        .count_zero     (last_word)
    );

    // Storage for counter logic
    always @(posedge clock) begin
        remaining_writes <= (count_out_wren == 1'b1) ? count_out : remaining_writes;
    end

// --------------------------------------------------------------------------
// Receive and buffer the system write data and last data word flag to the AXI
// interface.

    localparam BUFFER_WIDTH = WORD_WIDTH + 1;

    skid_buffer
    #(
        .WORD_WIDTH (BUFFER_WIDTH)
    )
    write_channel
    (
        .clock      (clock),

        .s_valid    (system_valid_internal),
        .s_ready    (system_ready_internal),
        .s_data     ({system_data, last_word}),

        .m_valid    (wvalid),
        .m_ready    (wready),
        .m_data     ({wdata, wlast})
    );

// --------------------------------------------------------------------------
// Finally, signal the control interface that the transaction is done once the
// last data word has entered the skid buffer.

// It would seem neater to do so with the output signals of the skid buffer,
// but then that's a combinational path back from its output, which will limit
// the effectiveness of its pipelining.

    always @(*) begin
        control_done = (last_word == 1'b1) && (system_valid_internal == 1'b1);
    end

endmodule

