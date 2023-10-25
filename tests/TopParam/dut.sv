module top #(
    parameter param
);

    test #(
        .param(param)
    ) test_i (
    );

endmodule

module test #(
    parameter param
)();

endmodule
