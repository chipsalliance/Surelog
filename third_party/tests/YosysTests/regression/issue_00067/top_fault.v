module top(input en, output reg y);
  always @*
    y = en & !y;
endmodule
