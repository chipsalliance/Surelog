module test (
    input i,
    output o
);
    wire w1;
    wire w2;

    assign w1 = ~i;
    assign w2 = w1;
    assign o = ~w2;
endmodule
