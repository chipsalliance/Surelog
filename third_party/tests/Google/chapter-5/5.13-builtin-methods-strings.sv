/*
:name: builtin-methods-string
:description: Check if built-in methods can be called
:tags: 5.13
*/
module top();
  string a = "test";

  initial begin;
    $display("length check: %d\n", a.len());
  end
endmodule
