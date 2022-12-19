module bottom();
  parameter P = 0;
  logic product_exponent[10:0];

  assign p = product_exponent[P:0] == '1;

endmodule

module top();
  bottom #(.P(5)) u1();
  bottom #(.P(8)) u2(); 
endmodule
