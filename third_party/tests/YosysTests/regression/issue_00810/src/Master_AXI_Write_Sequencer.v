
// Master AXI Write Sequencer

// The sequencer enables the write address, write data, and write response
// AXI transactions in turn, as the AXI and system interfaces complete their
// parts.

// A transaction is started by raising and holding the enable signal until the
// corresponding done signal is also raised, then both drop. (AXI ready/valid
// handshake)

module Master_AXI_Sequencer_Write
// No parameters
(
    input   wire        clock,

    // AXI Address Write
    output  reg         aw_control_enable,
    input   wire        aw_control_done,

    // AXI Data Write
    output  reg         w_control_enable,
    input   wire        w_control_done,

    // AXI Write Response
    output  reg         b_control_enable,
    input   wire        b_control_done
);

// --------------------------------------------------------------------------
// States for AXI writes

    localparam STATE_BITS = 2;

    localparam [STATE_BITS-1:0] DO_ADDR = 'd0; // Doing the address transaction
    localparam [STATE_BITS-1:0] DO_DATA = 'd1; // Doing the data transaction
    localparam [STATE_BITS-1:0] DO_RESP = 'd2; // Doing the response transaction

    reg [STATE_BITS-1:0] state      = DO_ADDR;
    reg [STATE_BITS-1:0] state_next = DO_ADDR;

// --------------------------------------------------------------------------
// Enable the transactions based on the states

    always @(*) begin
        aw_control_enable = (state == DO_ADDR);
        w_control_enable  = (state == DO_DATA);
        b_control_enable  = (state == DO_RESP);
    end

// --------------------------------------------------------------------------
// Describe the conditions which affect transactions (after being enabled)

    reg aw_done = 1'b0;
    reg w_done  = 1'b0;
    reg b_done  = 1'b0;

    always @(*) begin
        aw_done = (state == DO_ADDR) && (aw_control_done == 1'b1);
        w_done  = (state == DO_DATA) && (w_control_done  == 1'b1);
        b_done  = (state == DO_RESP) && (b_control_done  == 1'b1);
    end

// --------------------------------------------------------------------------
// Do the state transitions

    always @(*) begin
        state_next = (aw_done == 1'b1) ? DO_DATA : state;
        state_next = (w_done  == 1'b1) ? DO_RESP : state_next;
        state_next = (b_done  == 1'b1) ? DO_ADDR : state_next;
    end

    always @(posedge clock) begin
        state <= state_next;
    end

endmodule

