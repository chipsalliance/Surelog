/*
:name: real-constants-illegal
:description: Examples of real literal constants
:should_fail_because: at least one digit at each side of decimal point is required
:tags: 5.7.2
*/
module top();
  logic [31:0] a;

  initial begin;
    a = .12;
    a = 9.;
    a = 4.E3;
    a = .2e-7;
  end

endmodule
