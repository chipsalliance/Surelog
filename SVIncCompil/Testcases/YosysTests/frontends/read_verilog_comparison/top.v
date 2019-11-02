module top (
input clk,
input [15:0] I0,
input [15:0] I1,
output reg A,B,C,D,E,F
);

always @(posedge clk)
begin
    if (I0 < I1)
		A <= 1'b1;
	else
		A <= 1'b0;

	if (I0 <= I1)
		B <= 1'b1;
	else
		B <= 1'b0;

	if (I0 != I1)
		C <= 1'b1;
	else
		C <= 1'b0;

	if (I0 === I1)
		D <= 1'b1;
	else
		D <= 1'b0;

	if (I0 !== I1)
		E <= 1'b1;
	else
		E <= 1'b0;

	if (I0 >= I1)
		F <= 1'b1;
	else
		F <= 1'b0;

end


endmodule
