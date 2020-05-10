`timescale 1ns / 1ps

module test
(
    // Programmable Clock
    input CLK
);

    localparam FRAME_LENGTH = 15;
    localparam ESTABLISHED  = 16'h0003;

    wire RAMRST;
    wire [15:0] UserReadData;
    wire UserReadDataValid;

    reg [23:0] Delay;
    reg [10:0] UserState;
    reg [15:0] UserValidCount;
    reg [5:0] ConnectionState;
    reg [15:0] InterruptStatus;
    reg [15:0] FrameLength;
    reg [3:0] LatencyDelay;

    localparam USER_DELAY_INIT  = 11'h001;
    localparam USER_CLEAN       = 11'h002;
    localparam USER_CLEAN_CHECK = 11'h004;
    localparam USER_CLEAR_INTS  = 11'h008;
    localparam USER_INIT        = 11'h010;
    localparam USER_IDLE        = 11'h020;
    localparam USER_CHECK_STATE = 11'h040;
    localparam USER_CHECK_SPACE = 11'h080;
    localparam USER_WRITE_DATA  = 11'h100;
    localparam USER_READ_LENGTH = 11'h200;
    localparam USER_READ_DATA   = 11'h400;


    always @ (posedge RAMRST or posedge CLK) begin
        if (RAMRST==1) begin
            UserState <= USER_DELAY_INIT;
            Delay <= 0;
            UserValidCount <= 0;
            ConnectionState <= 0;
            InterruptStatus <= 0;
            FrameLength <= 0;
            LatencyDelay <= 0;
        end else begin

            case (UserState)

                USER_DELAY_INIT: begin
                    Delay <= Delay + 1;
                    if (Delay==24'hffffff) begin
                        UserState <= USER_CHECK_STATE;
                    end
                end

                USER_CHECK_STATE: begin

                    if (UserReadDataValid==1 && UserValidCount==1) begin

                        ConnectionState <= UserReadData[5:0];

                        if (LatencyDelay!=0 || InterruptStatus[0]==0) begin
                            UserState <= USER_CHECK_SPACE;
                        end else begin
                            UserState <= FrameLength==0 ? USER_READ_LENGTH :
                                                              USER_READ_DATA;
                        end
                    end
                end

                USER_CHECK_SPACE: begin
                    if (ConnectionState[3:0]!=ESTABLISHED) begin
                        UserState <= USER_IDLE;
                    end else begin

                        UserState <= USER_WRITE_DATA;
                    end
                end
                
            endcase
        end
    end

endmodule // test
