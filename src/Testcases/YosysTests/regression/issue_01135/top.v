module top(input [7:0] i, output o);
always @*
case (i[6:3])
    4: o <= i[0];
    3: o <= i[2];
    7: o <= i[3];
    default: o <= 1'b0;
endcase
endmodule
