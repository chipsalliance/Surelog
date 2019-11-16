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
    A <=  y / too;
end
always @(posedge x) begin
        cout <=  y + A % foo;
end
assign {B,C} =  {cout,A} << 1;
`else
assign {cout,A} =  cin - y * x;
`endif

endmodule
