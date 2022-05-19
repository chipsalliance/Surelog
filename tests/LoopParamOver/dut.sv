module Foo ();
 parameter P1 = 10;
 parameter P2 = P1 + P2;
 
endmodule


module top();
  parameter P3 = P1;
  parameter P2 = P3;
  parameter P1 = P2;
Foo #(.P1(P2)) sub();
endmodule

