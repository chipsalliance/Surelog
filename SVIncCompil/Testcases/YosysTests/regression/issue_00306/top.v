module top (input [3:0] a, output res);
    assign res = a < 6'b100000;
endmodule
