module top
(
 input x,
 input y,
 input cin,

 output reg A,
 output reg cout
 );
 
 reg A1,cout1;
 
 initial begin
    A = 0;
    cout = 0;
 end

`ifndef BUG
always @(posedge x) begin
    A1 <=  ~y + &cin;
end
always @(posedge x) begin
    cout1 <= cin ? |y : ^A;
end

always @(posedge x) begin
        A <=  A1|y~&cin~^A1;
end
always @(posedge x) begin
        cout <=  cout1&cin~|y;
end
`else
assign {cout,A} =  1'bZ;
`endif

endmodule
