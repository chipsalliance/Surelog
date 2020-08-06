/*
:name: statement_labels_par
:description: parallel block labels check
:tags: 9.3.5
*/
module block_tb ();
	reg a = 0;
	reg b = 0;
	reg c = 0;
	initial
		name: fork
			a = 1;
			b = 0;
			c = 1;
		join: name
endmodule
