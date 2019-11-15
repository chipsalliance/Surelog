module top
(
 input x,
 input y,
 input cin,

 output A,
 output cout
 );
 
 wire A1,cout1;
 
//  initial begin
//     A = 0;
//     cout = 0;
//  end

`ifndef BUG
assign A1 =  ~y + &cin;
assign cout1 = cin ? |y : ^A;

assign A =  A1|y~&cin~^A1;
assign cout =  cout1&cin~|y;
`else
assign {cout,A} =  1'bZ;
`endif

endmodule
