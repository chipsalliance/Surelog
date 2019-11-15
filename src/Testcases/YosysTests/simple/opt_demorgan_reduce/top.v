module top
(
 input x,
 input [2:0] y,
 input [2:0] cin,

 output A,
 output cout,
 output control
 );

 wire A1,cout1;
 wire [2:0] n_y;

 wire [2:0] n_cin;

//  initial begin
//     A = 0;
//     cout = 0;
//  end

assign n_y[0] = ~y[0];
assign n_y[1] = y[1];
assign n_y[2] = ~y[2];

assign n_cin[0] = ~cin[0];
assign n_cin[1] = cin[1];
assign n_cin[2] = ~cin[2];

`ifndef BUG
assign A1 =  n_y + &(~cin);
assign cout1 = cin ? |n_y : ^A;

assign A =  A1|y~&(~cin)~^A1;
assign cout =  cout1&cin~|(~y);

assign control = x & y & cin;
`else
assign A1 =  n_y + &(cin);
assign cout1 = cin ? |n_y : ^A;

assign A =  A1|y~&(~cin)~^A1;
assign cout =  cout1&cin~|(~y);

assign control = x | y | cin;
`endif

endmodule
