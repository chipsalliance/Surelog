/*
:name: integers-unsized-illegal
:description: Integer literal constants
:should_fail: 1
:tags: 5.7.1
*/
module top();
  logic [31:0] a;

  initial begin
    a = 4af; // is illegal (hexadecimal format requires 'h)
  end

endmodule
