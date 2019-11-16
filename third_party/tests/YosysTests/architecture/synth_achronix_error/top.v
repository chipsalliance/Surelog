module top
(
 input x,
 input y,
 input cin,

 output A,
 output cout
 );

`ifndef BUG
assign {cout,A} =  cin + y + x;
`else
assign {cout,A} =  cin - y * x;
`endif

endmodule

module top2
(
 input x,
 input y,
 input cin,

 output A,
 output cout
 );

`ifndef BUG
assign {cout,A} =  cin + y + x;
`else
assign {cout,A} =  cin - y * x;
`endif

endmodule
