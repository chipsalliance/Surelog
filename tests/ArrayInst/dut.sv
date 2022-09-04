module qq();
endmodule

module flop ();
  qq q[1:0]();
endmodule

module top();
  flop flop_instances1[1:0](), flop_instances2[2:0][1:0]();
endmodule
