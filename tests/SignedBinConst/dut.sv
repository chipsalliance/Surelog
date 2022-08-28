module top1();
  parameter [1:0] p1 =  1'sb1;
  parameter [1:0] p2 =  2'sb10;
  parameter int p3 =  2'sb10;
endmodule


module top2();
  reg [1:0] p1 =  1'sb1;
  reg [1:0] p2 =  2'sb10;
  int p3 =  2'sb10;
endmodule
