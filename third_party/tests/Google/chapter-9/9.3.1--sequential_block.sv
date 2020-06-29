/*
:name: sequential_block
:description: sequential block check
:tags: 9.3.1
*/
module sequential_tb ();
	reg a = 0;
	reg b = 0;
	reg c = 0;
	initial begin
		a = 1;
		b = a;
		c = b;
	end
endmodule
