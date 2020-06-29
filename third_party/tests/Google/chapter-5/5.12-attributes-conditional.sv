/*
:name: attributes-conditional
:description: Assing attributes to a conditional operator
:tags: 5.12
*/

module top();
  bit a, b, c, d;

  initial begin;
    a = b ? (* no_glitch *) c : d;
  end

endmodule
