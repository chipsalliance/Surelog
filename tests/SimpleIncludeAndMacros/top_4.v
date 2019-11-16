// top.v
`define N 4

`include "my_incl.vh"

`include "bar.vh"

`INCLUSION_FILES

`define single 11
`define multiple 20

`default_nettype wire

`undef multipl

`define my_macro(CK,DATA)\
   reg CK,rd,wr,ce; \
   reg [7:0]  addr,data_wr,``DATA``_rd; \
   reg [7:0]  read_``DATA``; 

   `my_macro(clk,data)


`define append(f) f``_master 

`append(a)

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

`define TOTO(a=100,b=200, c, d, e) a+b+c+d+e

`TOTO([a,b], (300,400), {500,600}, "400,600", \escaped,here )


 /* 
  comment
  */ 
endmodule // top
