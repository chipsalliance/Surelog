/*
:name: statement_labels_seq
:description: sequential block labels check
:tags: 9.3.5
*/
module block_tb ();
	reg a = 0;
	reg b = 0;
	reg c = 0;
	initial
		name: begin
			a = 1;
			b = a;
			c = b;
		end: name
endmodule
