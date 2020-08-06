/*
:name: case
:description: A module testing case statement
:tags: 12.5
*/
module case_tb ();
	wire [3:0] a = 0;
	reg [3:0] b = 0;
	always @* begin
		case(a)
			4'h0: b = 12;
			4'h3: b = 4;
			4'hf: b = 8;
			default b = 0;
		endcase
	end
endmodule
