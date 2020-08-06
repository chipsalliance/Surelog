/*
:name: case_constant
:description: A module testing case statement with constant expression
:tags: 12.5.2
*/
module case_tb ();
	wire [3:0] a = 0;
	reg [3:0] b = 0;
	always @* begin
		case(1)
			a[0] : b = 1;
			a[1] : b = 2;
			a[2] : b = 3;
			a[3] : b = 4;
			default b = 0;
		endcase
	end
endmodule
