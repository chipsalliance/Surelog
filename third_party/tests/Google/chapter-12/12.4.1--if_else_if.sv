/*
:name: if_else_if
:description: A module testing if-else-if statement
:tags: 12.4.1
*/
module if_tb ();
	wire a = 0;
	reg b = 0;
	wire c = 0;
	reg d = 0;
	always @* begin
		if(a) b = 1;
		else if(c) d = 1;
		else b = 0;
	end
endmodule
