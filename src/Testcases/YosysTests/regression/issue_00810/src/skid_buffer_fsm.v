
// FSM for Skid-Buffer

// This FSM assumes the AXI meaning and behaviour of valid/ready handshake
// signals: when both are high, data transfers at the end of the clock cycle.
// It is an error to raise ready when not able to accept data (thus losing the
// incoming data), or to raise valid when not able to send data (thus
// duplicating previously sent data). These error situations are not handled.

// This FSM manages the valid/ready transactions for a sending master
// interface and a receiving slave interface (AXI terminology). 
// The associated data buffers are in the related datapath module.
// The datapath is expected to be one data output register, fed from either
// the data input, or a buffered copy of data input.

// We want to keep the state inside this module, so that the associated
// datapath module does not have to know anything about the current state or
// its encoding.  Output enough control signals to have the datapath steer
// logic as necessary and manage the data buffers themselves.

`default_nettype none

module skid_buffer_fsm
// No parameters
(
    input   wire    clock,

    // Slave interface
    input   wire    s_valid,
    output  reg     s_ready,

    // Master Interface
    output  reg     m_valid,
    input   wire    m_ready,

    // Control to Datapath
    output  reg     data_out_wren,
    output  reg     data_buffer_wren,
    output  reg     use_buffered_data    
);

// --------------------------------------------------------------------------
// Have the initial output values match what they would be for an empty
// datapath.

    initial begin
        s_ready             = 1'b1; // empty at start, so accept data
        m_valid             = 1'b0;
        data_out_wren       = 1'b1; // empty at start, so accept data
        data_buffer_wren    = 1'b0;
        use_buffered_data   = 1'b0;
    end

// --------------------------------------------------------------------------
// Lets describe the possible states of the datapath, and initialize it.

// This describes a binary state encoding, but the CAD tool can re-encode and
// re-number the state encoding. Usually this is beneficial, but if the
// states+inputs fit in a single LUT, forcing binary encoding reduces area.
// See what works best (i.e.: reaches the highest speed) for your given FPGA.

    localparam STATE_BITS = 2;

    localparam [STATE_BITS-1:0] EMPTY = 'd0; // Output and buffer registers empty
    localparam [STATE_BITS-1:0] BUSY  = 'd1; // Output register holds data
    localparam [STATE_BITS-1:0] FULL  = 'd2; // Both output and buffer registers hold data
    // There is no case where only the buffer register would hold data.

    // No handling of erroneous and unreachable state 3.
    // We could check and raise an error flag.

    reg [STATE_BITS-1:0] state      = EMPTY;
    reg [STATE_BITS-1:0] state_next = EMPTY;

// --------------------------------------------------------------------------
// Compute the allowable output read/valid handshake signals based on the
// datapath state. (use state_next so we can have a nice registered output).

// This tiny bit of code is critical since it implies the fundamental
// operating assumptions of a skid buffer: that one interface cannot have its
// current state depend on the current state of the other interface, as that
// would be a combinational path between both interfaces.

// Without this code, we would have to handle many more cases in the upcoming
// datapath transformation and state transition code. If something below is not
// clear, refer back to this code.

    // The slave interface is ready to accept data whenever the datapath is not full.
    // The master interface has data to give whenever the datapath is not empty.
    always @(posedge clock) begin
        s_ready <= (state_next != FULL);
        m_valid <= (state_next != EMPTY); 
    end

// --------------------------------------------------------------------------
// Let's enumerate the possible interface states which transform the contents
// of the datapath. Here, this means the slave interface inserting and the
// master interface removing data items from the datapath.

    reg insert = 1'b0;
    reg remove = 1'b0;

    always @(*) begin
        insert = (s_valid == 1'b1) && (s_ready == 1'b1);
        remove = (m_valid == 1'b1) && (m_ready == 1'b1);
    end

// --------------------------------------------------------------------------
// Let's describe the possible transformations to the datapath, and in which state
// they can happen.

    reg load    = 1'b0; // Empty datapath inserts data into output register.
    reg flow    = 1'b0; // New inserted data into output register as the old data is removed.
    reg fill    = 1'b0; // New inserted data into buffer register. Data not removed from output register.
    reg flush   = 1'b0; // Move data from buffer register into output register. Remove old data. No new data inserted.
    reg unload  = 1'b0; // Remove data from output register, leaving the datapath empty.

    always @(*) begin
        load    = (state == EMPTY) && (insert == 1'b1);
        flow    = (state == BUSY)  && (insert == 1'b1) && (remove == 1'b1);
        fill    = (state == BUSY)  && (insert == 1'b1) && (remove == 1'b0);
        flush   = (state == FULL)  && (insert == 1'b0) && (remove == 1'b1);
        unload  = (state == BUSY)  && (insert == 1'b0) && (remove == 1'b1);
    end

// --------------------------------------------------------------------------
// Lets calculate the next state after each datapath transformation.

    always @(*) begin
        state_next = (load   == 1'b1) ? BUSY  : state;
        state_next = (flow   == 1'b1) ? BUSY  : state_next;
        state_next = (fill   == 1'b1) ? FULL  : state_next;
        state_next = (flush  == 1'b1) ? BUSY  : state_next;
        state_next = (unload == 1'b1) ? EMPTY : state_next;
    end

    always @(posedge clock) begin
        state <= state_next;
    end

// --------------------------------------------------------------------------
// Finally, from the datapath transformations, compute the necessary control
// signals. These are not registered here, as they end at registers in the
// datapath.

    always @(*) begin
        data_out_wren     = (load  == 1'b1) || (flow == 1'b1) || (flush == 1'b1);
        data_buffer_wren  = (fill  == 1'b1);
        use_buffered_data = (flush == 1'b1);
    end

endmodule

