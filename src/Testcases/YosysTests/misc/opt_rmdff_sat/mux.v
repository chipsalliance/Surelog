
module mux
(
    input clk,
    input rst,
    output reg  ctrl_ready,
    input  wire ctrl_valid,
    input  wire [0:0] ctrl_data,
    output reg  din0_ready,
    input  wire din0_valid,
    input  wire [0:0] din0_data,
    output reg  din1_ready,
    input  wire din1_valid,
    input  wire [1:0] din1_data,
    input  wire         dout_ready,
    output reg          dout_valid,
    output wire  [2:0] dout_data

);
    wire [0:0] ctrl_s; // u1

    wire [0:0] din0_s; // u1

    wire [1:0] din1_s; // u2

    reg [2:0] dout_s; // u1 | u2
    reg [1:0] dout_s_data; // u2
    assign dout_s[1:0] = dout_s_data;
    reg [0:0] dout_s_ctrl; // u1
    assign dout_s[2:2] = dout_s_ctrl;


    assign ctrl_s = ctrl_data;
    assign din0_s = din0_data;
    assign din1_s = din1_data;

    assign dout_data = dout_s;

    wire handshake;
    reg din_valid_sel;

    assign handshake = dout_valid && dout_ready;

    always @*
    begin
        din0_ready = din0_valid ? 0 : dout_ready;
        din1_ready = din1_valid ? 0 : dout_ready;
        dout_s_data = { 2 {1'bx}};
        din_valid_sel = 0;
        if (ctrl_valid) begin
            case( ctrl_data )
                0 : begin
                    din_valid_sel = din0_valid;
                    dout_s_data[0:0] = din0_s;
                    din0_ready = din0_valid ? handshake : dout_ready;
                end
                1 : begin
                    din_valid_sel = din1_valid;
                    dout_s_data[1:0] = din1_s;
                    din1_ready = din1_valid ? handshake : dout_ready;
                end
                default: begin
                    din0_ready = dout_ready;
                    din1_ready = dout_ready;
                    din_valid_sel = 1'bx;
                end
            endcase
        end
    end

    assign ctrl_ready = ctrl_valid ? handshake : dout_ready;
    assign dout_s_ctrl = ctrl_s;
    assign dout_valid = ctrl_valid && din_valid_sel;



endmodule