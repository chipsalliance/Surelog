module top
(
 input x,
 input y,
 input cin,

 output A,
 output cout
 );

`ifndef BUG
assign {cout,A} =  cin % y / x;
`else
assign {cout,A} =  2'bZZ;
`endif

endmodule
