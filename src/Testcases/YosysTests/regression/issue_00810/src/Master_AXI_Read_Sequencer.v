
// Master AXI Read Sequencer

// The sequencer enables the read address and read data AXI transactions in
// turn, as the AXI and system interfaces complete their parts.

// A transaction is started by raising and holding the enable signal until the
// corresponding done signal is also raised, then both drop. (AXI ready/valid
// handshake)

module Master_AXI_Sequencer_Read
// No parameters
(
    input   wire        clock,

    // AXI Address Read
    output  reg         ar_control_enable,
    input   wire        ar_control_done,

    // AXI Data Read
    output  reg        r_control_enable,
    input   wire       r_control_done
);

// --------------------------------------------------------------------------
// States for AXI reads

    localparam STATE_BITS = 1;

    localparam [STATE_BITS-1:0] DO_ADDR = 'd0; // Doing the address transaction
    localparam [STATE_BITS-1:0] DO_DATA = 'd1; // Doing the data transaction

    reg [STATE_BITS-1:0] state      = DO_ADDR;
    reg [STATE_BITS-1:0] state_next = DO_ADDR;

// --------------------------------------------------------------------------
// Enable the transactions based on the states

    always @(*) begin
        ar_control_enable = (state == DO_ADDR);
        r_control_enable  = (state == DO_DATA);
    end

// --------------------------------------------------------------------------
// Describe the conditions which affect transactions (after being enabled)

    reg ar_done = 1'b0;
    reg r_done  = 1'b0;

    always @(*) begin
        ar_done = (state == DO_ADDR) && (ar_control_done == 1'b1);
        r_done  = (state == DO_DATA) && (r_control_done  == 1'b1);
    end

// --------------------------------------------------------------------------
// Do the state transitions

    always @(*) begin
        state_next = (ar_done == 1'b1) ? DO_DATA : state;
        state_next = (r_done  == 1'b1) ? DO_ADDR : state_next;
    end

    always @(posedge clock) begin
        state <= state_next;
    end

endmodule

