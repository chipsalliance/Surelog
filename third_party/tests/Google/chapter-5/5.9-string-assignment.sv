/*
:name: string-assignment
:description: String assignment tests
:tags: 5.9
*/
module top();
  byte        a;
  bit   [7:0] b;
  logic [7:0] c;

  initial begin;
    a = "a";
    b = "b";
    c = "c";
  end

endmodule
