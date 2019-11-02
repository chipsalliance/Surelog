module top
(
 input x,
 input y,
 input cin,

 output reg A,
 output reg cout
 );

 reg ASSERT = 1;
 (* anyconst *) reg foo;
 (* anyseq *) reg too;



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
always @(negedge x) begin
    if ($initstate)
        cout <= 0;
        cout <=  y + A + foo;
    assert(ASSERT);
    assert(s_eventually ASSERT);
end
`else
assign {cout,A} =  cin - y * x;
`endif

endmodule

module top2
(
 input x,
 input y,
 input cin,

 output reg A,
 output reg cout
 );

 reg ASSERT = 1;
 (* anyconst *) reg foo;
 (* anyseq *) reg too;



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
always @(negedge x) begin
    if ($initstate)
        cout <= 0;
        cout <=  y + A + foo;
    assert(ASSERT);
    assert(s_eventually ASSERT);
end
`else
assign {cout,A} =  cin - y * x;
`endif

endmodule
