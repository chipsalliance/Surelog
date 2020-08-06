/*
:name: builtin-methods-arrays
:description: Check if built-in methods can be called
:tags: 5.13
*/
module top();
  reg [7:0] array [3];

  initial begin;
    $display ("Array size %d\n", array.size());
  end

endmodule
