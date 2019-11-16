module top(p1h, p1l, p2h, p2l, p3h, p3l);

    (* LOC="P3" *) output p1h;
    (* LOC="P4" *) output p1l;
    (* LOC="P5" *) output p2h;
    (* LOC="P6" *) output p2l;
    (* LOC="P7" *) output p3h;
    (* LOC="P8" *) output p3l;

    wire clk;
    GP_LFOSC #(
        .AUTO_PWRDN(0),
        .OUT_DIV(1)
    ) osc (
        .CLKOUT(clk)
    );

    localparam DIVIDER = 1;//400;
    reg [13:0] divcnt = DIVIDER;
    always @(posedge clk)
        if(divcnt == 0)
            divcnt <= DIVIDER;
        else
            divcnt <= divcnt - 1;

    wire reset;
    GP_POR por(
        .RST_DONE(reset)
    );

    reg  [2:0] state;
    always @(posedge divcnt or negedge reset)
        if(!reset)
            state <= 0;
        else
            case(state)
                0: state <= 1;
                1: state <= 2;
                2: state <= 3;
                3: state <= 4;
                4: state <= 5;
                5: state <= 0;
            endcase

    reg  [5:0] phases;
    always @(*) begin
        phases <= 6'b000000;
        case(state)
            0: phases <= 6'b100100;
            1: phases <= 6'b000110;
            2: phases <= 6'b010010;
            3: phases <= 6'b011000;
            4: phases <= 6'b001001;
            5: phases <= 6'b100001;
        endcase
    end

    wire p1i, p2i, p3i;
    assign {p1i, p1l, p2i, p2l, p3i, p3l} = phases;
    assign {p1h, p2h, p3h} = ~{p1i, p2i, p3i};

endmodule
