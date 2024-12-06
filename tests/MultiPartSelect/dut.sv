typedef struct packed {
    logic [1:0][3:0] a;
} tier1;

module top();

    tier1 xx;
    assign xx.a[1][3:2] = 2;
    assign xx.a[1][1:0] = 3;

endmodule
