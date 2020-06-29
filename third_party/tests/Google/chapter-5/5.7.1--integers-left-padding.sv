/*
:name: integers-left-padding
:description: Automatic left padding of literal constant numbers
:tags: 5.7.1
*/
module top();
  logic [11:0] a, b, c, d;
  logic [84:0] e, f, g;

  initial begin
    a = 'h x;   // yields xxx
    b = 'h 3x;  // yields 03x
    c = 'h z3;  // yields zz3
    d = 'h 0z3; // yields 0z3
    e = 'h5;    // yields {82{1'b0},3'b101}
    f = 'hx;    // yields {85{1'hx}}
    g = 'hz;    // yields {85{1'hz}}
  end

endmodule
