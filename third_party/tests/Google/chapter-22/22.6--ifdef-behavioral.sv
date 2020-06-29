/*
:name: 22.6--ifdef-behavioral
:description: Test
:tags: 22.6
:type: preprocessing
*/
module and_op (a, b, c);
	output a;
	input b, c;
	`ifdef behavioral
		wire a = b & c;
	`else
		and a1 (a,b,c);
	`endif
endmodule
