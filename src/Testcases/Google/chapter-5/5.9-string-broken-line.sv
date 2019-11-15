/*
:name: string-broken-line
:description: Basic broken line string example
:should_fail: 0
:tags: 5.9
*/
module top();

  initial begin;
    $display("broken \
              line");
  end

endmodule
