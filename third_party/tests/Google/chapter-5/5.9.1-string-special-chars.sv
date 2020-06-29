/*
:name: string-special-chars
:description: Special characters in strings
:tags: 5.9.1
*/
module top();

  initial begin
    $display("newline \n");
    $display("tab \t");
    $display("backslash \\");
    $display("quote \"");
    $display("vertical tab \v");
    $display("form feed \f");
    $display("bell \a");
    $display("octal \123");
    $display("hex \x12");
  end

endmodule
