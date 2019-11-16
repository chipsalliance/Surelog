module top
(
 input x,
 input y,
 input cin,

 output reg A,
 output cout
 );
 parameter X = 1;
 wire o;

`ifndef BUG
always @(posedge cin)
	A <= o;

assign cout =  cin? y : x;

middle u_mid1 (.x(x),.A(o),.y(1'b0));
middle u_mid2 (.x(x),.A(o),.y(1'b1));
middle u_mid3 (.x(x),.A(o),.y(1'bX));
middle u_mid4 (.x(x),.A(o),.y(1'bX));
`else
assign {cout,A} =  cin - y * x;
`endif

endmodule

module middle
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
