module top(a,b);
input a;
output b;

  module sub (a, b);
    input a;
    output b;
  endmodule

  sub sub1(a, b);

endmodule
