module gold(input i1, input i2, output o2, output o1);
 wire _1_;
 assign o2 = i1 & i2;
 assign _1_ = i1 | i2;
 assign o1 = _1_ & o2;
endmodule

module top_r( i1, i2, o1, o2 );
  input i1, i2;
  output o1, o2;
  wire w4;
  assign o2 = (i2 & i1);
  assign w4 = ((i2 && i1) | (i2) | (i1));
  assign o1 = ((w4 & o2));
endmodule

module top_w( i1, i2, o1, o2 );
  input i1, i2;
  output o1, o2;
  wire w4;
  assign o2 = (i2 & i1);
  assign w4 = ((i2 & i1) | (i2) | (i1));
  assign o1 = ((w4 & o2));
endmodule
