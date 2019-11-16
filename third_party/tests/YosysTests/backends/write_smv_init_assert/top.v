module top
(
 input x,
 input y,
 input cin,

 output reg A,
 output reg cout,
 output reg B,C
 );
 
 reg ASSERT = 1;
 
 initial begin
    begin
        A = 0;
        cout = 0;
    end
 end

`ifndef BUG
assign    A =  y + cin;
assign    cout =  y + A;
    always @*
    assert(ASSERT);
assign {B,C} =  {cout,A} <<< 1;
`else
assign {cout,A} =  cin - y * x;
`endif

endmodule
