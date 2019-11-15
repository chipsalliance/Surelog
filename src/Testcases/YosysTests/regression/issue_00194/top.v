module top(input a, output y);
  demo_sub sub (y, , 1'b1, a);
endmodule

module demo_sub(output y, z, input a, b);
  assign y = a & b, z = a | b;
endmodule
