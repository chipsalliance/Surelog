
module bottom();
  assign o = medium.c;
endmodule

module medium();
  wire c;
  bottom b1();
endmodule

module top();
   medium u1();
endmodule   

