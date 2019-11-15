// top.v
`define N 4
`timescale 10ns/10ps
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
`resetall
endmodule // top



`define BOTTOM `TOP 
`define TOP `BOTTOM1
`define BOTTOM1 `BOTTOM
`TOP