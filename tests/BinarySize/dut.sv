module top();
  logic       [31:0] first;
  assign first = 32'b1;
  assign first = 1'b0;
  assign first = 2'b00;
  assign first = 1'b1;
  assign first = 2'b01;
  assign first = 1'bx;
  assign first = 2'b0x;
  assign first = 1'bz;
  assign first = 2'b0z;

endmodule
