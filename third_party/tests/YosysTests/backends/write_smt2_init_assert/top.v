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
 (* allconst *) reg foo;
 (* allseq *) reg too;




 initial begin
    begin
        A = 0;
        cout = 0;
    end
 end

`ifndef BUG
always @(posedge x) begin
    if ($initstate)
        A <= 0;
    A <=  y + cin + too;
    assume(too);
    assume(s_eventually too);
end
always @(posedge x) begin
    if ($initstate)
        cout <= 0;
        cout <=  y + A + foo;
    assert(ASSERT);
    assert(s_eventually ASSERT);
end
assign {B,C} =  {cout,A} << 1;
`else
assign {cout,A} =  cin - y * x;
`endif

endmodule
