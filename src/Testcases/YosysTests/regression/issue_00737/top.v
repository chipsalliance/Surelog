module top (
    input wire iw,
    output wire ow
);

    localparam j = 2;

    (* A=2 *)
    (* B=j+1 *)
    SB_LUT4 #(
        .LUT_INIT(16'h0001)
    ) test_I (
        .I0(iw),
        .I1(),
        .I2(),
        .I3(),
        .O(ow)
    );

endmodule
