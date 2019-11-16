module top(
    inout  a,
    inout  b,
    input  dir,
);

    wire aout, bout;
    GP_IOBUF iobufa(
        .IO(a),
        .OUT(aout),
        .IN(bout),
        .OE(dir)
    );
    GP_IOBUF iobufb(
        .IO(b),
        .OUT(bout),
        .IN(aout),
        .OE(!dir)
    );

endmodule
