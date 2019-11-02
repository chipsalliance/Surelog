/*
:name: integers-sized-illegal
:description: Integer literal constants
:should_fail: 1
:tags: 5.7.1
*/
module top();
  logic  [7:0] a;

  initial begin
    a = 8'd-6;
  end

endmodule
