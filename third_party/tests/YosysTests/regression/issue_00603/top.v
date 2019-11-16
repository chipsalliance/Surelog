//K-input Look-Up Table
module top #(
    //The Look-up Table size (number of inputs)
    parameter K,

    //The lut mask.
    //Left-most (MSB) bit corresponds to all inputs logic one.
    //Defaults to always false.
    parameter LUT_MASK={2**K{1'b0}}
) (
    input [K-1:0] in,
    output out
);

    specify
        (in *> out) = "";
    endspecify

    assign out = LUT_MASK[in];

endmodule
