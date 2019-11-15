// top.v
`define N 4

`include "my_incl.vh"

`include "bar.vh"

`INCLUSION_FILES

`define single 11
`define multiple 20

`default_nettype wire

`undef multipl

 $display("Internal error: null handle at %s, line %d.",`__FILE__, `__LINE__); 

module top(input clk, input [`N-1:0] in1, output [`M-1:0] q);
 m1 u1(.clk(clk), .in1(in1), .q(q));
 wire a[`single:`multiple];
`BLOB

`xyz(1,a)

`xyz(1)

`MACRO1 ( 1 , , 3 ) 

$display(`msg(left side,right side));

`macro_with_args( out, in)

`WB_DUT_U_ASSIGN(12,34)

 /* 
  comment
  */ 

$display("Humpty Dumpty sat on a wall. \
Humpty Dumpty had a great fall.");

`define first_half "start of string

$display(`first_half end of string ");

$display("Hum\pty \\"Dumpty" sat \\on a wall. Humpty Dumpty had a great fall.");

endmodule // top

`define home(filename) `"filename`"
`include `home(inc.sv) 

`wxyz(A,B)
