/*
:name: unique0_if
:description: A module testing unique0-if statement
:tags: 12.4.2
*/
module if_tb ();
	wire [3:0] a = 0;
	reg [1:0] b = 0;
	always @* begin
		unique0 if(a == 0) b = 1;
		else if(a == 1) b = 2;
	end
endmodule
