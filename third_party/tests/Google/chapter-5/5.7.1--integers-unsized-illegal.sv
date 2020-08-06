/*
:name: integers-unsized-illegal
:description: Integer literal constants
:should_fail_because: hexadecimal format requires 'h
:tags: 5.7.1
*/
module top();
  logic [31:0] a;

  initial begin
    a = 4af;
  end

endmodule
