module top;
    parameter integer A = 0;
    parameter integer B = (A >= 0) ? 8/A : 1;
    parameter integer C = (A > 0) ? 8/A : 1;
endmodule
