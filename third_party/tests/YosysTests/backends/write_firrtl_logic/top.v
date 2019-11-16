module top
(
 input x,
 input y,
 input cin,

 output reg A,
 output reg cout
 );

 reg A1,cout1;
 reg int1,int2,int3;

 initial begin
    A = 0;
    cout = 0;
 end

`ifndef BUG
always @(posedge x) begin
    A1 <=  ~y + &cin;
end
always @(posedge x) begin
    cout1 <= cin ? |y : ~^A;
end

always @(posedge x) begin
        A <=  A1|y~&cin~^A1;
end
always @(posedge x) begin
        cout <=  cout1&cin~|y;
end

always @(posedge x)
begin
 if (x == 1'b1) begin
	int1 = x ^ y;
 end
 if (x != 1'b1) begin
	if (y > 1'b0) begin
		if (cin < 1'b1) begin
			int2 = cout1;
		end
	end
 end
end
 always @(posedge x)
 if (x >= 1'b1) begin
	if (y <= 1'b0) begin
		int3 = A1;
	end
 end

`else
assign {cout,A} =  1'bZ;
`endif

endmodule
