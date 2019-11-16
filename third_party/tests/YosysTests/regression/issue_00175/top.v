module top (
    C,
    GC,
    E
);

    input  C;
    output GC;
    input  E;

    reg ED;

always@(*) begin
    if(~C)
        ED = E;
end

    assign GC = C & ED;

endmodule
