module top
(
 input x,
 input y,
 input cin,

 output A,
 output cout
 );

 wire pow,p,n;

`ifndef BUG
assign {cout,A} =  cin % y / x;

assign pow =  y ** x;

assign p =  +x;
assign n =  -x;
`else
assign {cout,A} =  2'bZZ;
`endif

endmodule
