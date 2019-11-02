// top.v
`define N 4

`include "my_incl.vh"

`include "bar.vh"

`INCLUSION_FILES

`define single 11
`define multiple 20

`default_nettype 

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
endmodule // top

`define append(f) g``_master 

`define DD(x,y,a,b) initial $display("start", ``a``x , k``z, y``"end");
