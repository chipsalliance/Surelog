/*
:name: attributes-conditional
:description: Assing attributes to a conditional operator
:should_fail: 0
:tags: 5.12
*/

module top();
  bit a, b, c, d;

  initial begin;
    a = b ? (* no_glitch *) c : d;
  end

endmodule
