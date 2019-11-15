/*
:name: attributes-operator
:description: Assing attributes to an operator
:should_fail: 0
:tags: 5.12
*/

module top();
  logic [7:0] a;
  logic [7:0] b;
  logic [7:0] c;

  initial begin;
    a = b + (* mode = "cla" *) c;
  end

endmodule
