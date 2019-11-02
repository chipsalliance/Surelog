module top
(
 input [7:0] x,

 output o_and,
 output o_or,
 output o_xor,
 output o_nand,
 output o_nor,
 output o_xnor
 );

`ifndef BUG
assign o_and =  &x;
assign o_or =  |x;
assign o_xor =  ^x;
assign o_nand =  ~&x;
assign o_nor =  ~|x;
assign o_xnor =  ~^x;
`else
assign o_and =  ~&x;
assign o_or =  &x;
assign o_xor =  ~^x;
assign o_nand =  &x;
assign o_nor =  ^x;
assign o_xnor =  ~&x;
`endif

endmodule
