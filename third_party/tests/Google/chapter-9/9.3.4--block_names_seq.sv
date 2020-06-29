/*
:name: block_names_seq
:description: sequential block names check
:tags: 9.3.4
*/
module block_tb ();
	reg a = 0;
	reg b = 0;
	reg c = 0;
	initial
		begin: name
			a = 1;
			b = a;
			c = b;
		end: name
endmodule
