/*
:name: integers-unsized
:description: Integer literal constantsa
:tags: 5.7.1
*/
module top();
  logic [31:0] a;

  initial begin
    a = 659;      // is a decimal number
    a = 'h 837FF; // is a hexadecimal number
    a = 'o7460;   // is an octal number
  end

endmodule
