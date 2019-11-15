
// Master AXI Address Channel

// This module performs a minimal AxADDR handshake, with the minimum number of
// parameters and settings possible (no LOCK, CACHE, PROT, REGION, ID, etc...).
// All transfers are AXI word-wide.

// There are two interfaces: System and Control.

// The System interface is where the host system sets the parameters for the
// transaction. The address, burst length, and burst type are all set by
// pulsing their _wren signal for one cycle. These parameters are persistent.
// Then system_start must be pulsed high for one cycle. The system_ready flag
// will go high when the transaction is done and stay high until a new
// transaction is started.

// The Control interface is internal to the AXI transactor and is controlled
// by another AXI sequencer, which allows the channel to begin operating by
// raising and holding control_enable high, until control_done also goes high
// to signal completion, then both go low. It functions just like
// a valid/ready handshake, thus it is an error to drop control_enable before
// control_done is asserted.

// Once both the System and Control interfaces are active, the address
// transaction begins and any signaling on the system interface is ignored
// until system_ready is raised. Thus, system_ready must be initialized high
// before the first system transaction to avoid a special case.

`default_nettype none

module Master_AXI_Address_Channel
#(
    parameter ADDR_WIDTH    = 0,
    parameter AXSIZE        = 0,

    // Do not alter at instantiation. Set by AXI4 spec.
    parameter AXLEN_WIDTH   = 8,
    parameter AXSIZE_WIDTH  = 3,
    parameter AXBURST_WIDTH = 2
)
(
    input   wire                        clock,

    // System interface
    input   wire    [ADDR_WIDTH-1:0]    system_address,
    input   wire                        system_address_wren,
    input   wire    [AXLEN_WIDTH-1:0]   system_count,
    input   wire                        system_count_wren,
    input   wire    [AXBURST_WIDTH-1:0] system_type,
    input   wire                        system_type_wren,
    input   wire                        system_start,
    output  reg                         system_ready,

    // Control interface
    input   wire                        control_enable,
    output  reg                         control_done,

    // AXI interface
    output  reg     [ADDR_WIDTH-1:0]    axaddr,
    output  reg     [AXLEN_WIDTH-1:0]   axlen,
    output  reg     [AXSIZE_WIDTH-1:0]  axsize,
    output  reg     [AXBURST_WIDTH-1:0] axburst,
    output  reg                         axvalid,
    input   wire                        axready
);

// --------------------------------------------------------------------------

    localparam AXADDR_ZERO  = {ADDR_WIDTH{1'b0}};
    localparam AXLEN_ZERO   = {AXLEN_WIDTH{1'b0}};
    localparam AXBURST_ZERO = {AXBURST_WIDTH{1'b0}};

    // AXI word-wide transfers, so this never changes.
    localparam [AXSIZE_WIDTH-1:0] AXSIZE_INIT = AXSIZE [AXSIZE_WIDTH-1:0];

    initial begin
        system_ready    = 1'b0;
        control_done    = 1'b0;
        axaddr          = AXADDR_ZERO;
        axlen           = AXLEN_ZERO;
        axsize          = AXSIZE_INIT;
        axburst         = AXBURST_ZERO;
        axvalid         = 1'b0;
    end

// --------------------------------------------------------------------------

    reg transaction_complete = 1'b0;

    always @(*) begin
        transaction_complete = (axvalid == 1'b1) && (axready == 1'b1);
        control_done         = transaction_complete;
    end

// --------------------------------------------------------------------------
// Latch activation of system interface. Hold until transaction complete.

    wire system_start_set;

    pulse_to_level
    system_enable
    (
        .clock      (clock),
        .clear      (transaction_complete),
        .pulse_in   (system_start),
        .level_out  (system_start_set)
    );

    always @(*) begin
        system_ready = (system_start_set == 1'b0);
    end

// --------------------------------------------------------------------------
// Once both interfaces are set, start the transaction.

    always @(*) begin
        axvalid = (control_enable == 1'b1) && (system_start_set == 1'b1);
    end

// --------------------------------------------------------------------------
// If the system interface has not signaled to start a transaction, update the
// AXI ports on a system write.

    always @(posedge clock) begin
        axaddr  <= (system_address_wren == 1'b1) && (system_start_set == 1'b0) ? system_address : axaddr;
        axlen   <= (system_count_wren   == 1'b1) && (system_start_set == 1'b0) ? system_count   : axlen;
        axburst <= (system_type_wren    == 1'b1) && (system_start_set == 1'b0) ? system_type    : axburst;
    end

endmodule

