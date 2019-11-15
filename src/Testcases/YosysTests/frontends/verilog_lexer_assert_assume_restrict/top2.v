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

 const integer Gsize = 10e2;

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
    assert(eventually ASSERT);

//checker request_granted(y,cin);
	r1: restrict property (y == cin);
//endchecker : request_granted
end
`else
assign {cout,A} =  cin - y * x;

`endif

endmodule
