module top
(
 input x,
 input y,
 input cin,

 output reg A,
 output reg cout,
 output X
 );

 reg ASSERT = 1'bX;
 (* anyconst *) reg foo;
 (* anyseq *) reg too;



 initial begin
    begin
        A = 1'bX;
        cout = 1'bZ;
    end
 end

`ifndef BUG
always @(posedge x) begin
    if ($initstate)
        A <= 1'bX;
    A <=  y + cin + too;
    assume(too);
    assume(s_eventually too);
end
always @(negedge x) begin
    if ($initstate)
        cout <= 1'bZ;
        cout <=  y + A + foo;
    assert(ASSERT);
    assert(s_eventually ASSERT);
end

assign X = 1'bX;
`else
assign {cout,A} =  cin - y * x;
`endif

endmodule

