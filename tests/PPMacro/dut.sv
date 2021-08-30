`define FOO1 $clog2
module top1();
  assign a = `FOO1(123);
endmodule

`define FOO2 42
module top2();
  assign a = `FOO2(123);
endmodule


