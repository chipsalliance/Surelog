module qq();
endmodule

module flop ();
  qq q[1:0]();
endmodule

module top();
  flop flop_instances[3:0] ();
endmodule
