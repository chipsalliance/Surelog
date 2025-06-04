
module top;
    logic [63:0] s1c;
    assign s1c = ('1 << 8) + 1 + A + (2 + 3);
endmodule

