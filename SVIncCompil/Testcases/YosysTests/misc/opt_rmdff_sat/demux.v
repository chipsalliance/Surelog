
module demux
(
    input clk,
    input rst,
    output reg  din_ready,
    input  wire din_valid,
    input  wire [2:0] din_data,
    input  wire         dout0_ready,
    output reg          dout0_valid,
    output wire  [0:0] dout0_data,
    input  wire         dout1_ready,
    output reg          dout1_valid,
    output wire  [1:0] dout1_data

);
    wire [2:0] din_s; // u1 | u2
    wire [1:0] din_s_data; // u2
    assign din_s_data = din_s[1:0];
    wire [0:0] din_s_ctrl; // u1
    assign din_s_ctrl = din_s[2:2];


    assign din_s = din_data;


    assign dout0_data = din_data;
    assign dout1_data = din_data;

    always @*
    begin
        din_ready = 1'bx;
        dout0_valid = 0;
        dout1_valid = 0;

        if (din_valid) begin
            case(din_s_ctrl)
                0 : begin
                    din_ready = dout0_ready;
                    dout0_valid = din_valid;
                end
                1 : begin
                    din_ready = dout1_ready;
                    dout1_valid = din_valid;
                end
                default: begin
                    din_ready = 1'bx;
                    dout0_valid = 1'bx;
                    dout1_valid = 1'bx;
                end
            endcase
        end
    end



endmodule
