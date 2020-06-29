/*
:name: casez_pattern
:description: A module testing pattern matching in casez statements
:tags: 12.6.1
*/
module case_tb ();

	typedef union tagged {
		struct {
			bit [3:0] val1, val2;
		} a;
		struct {
			bit [7:0] val1, val2;
		} b;
		struct {
			bit [15:0] val1, val2;
		} c;
	} u;

	u tmp;

	initial casez (v) matches
		tagged a '{.v, 4'bzz0?} : $display("a %d", v);
		tagged a '{.v1, .v2} : $display("a %d %d", v1, v2);
		tagged b '{.v1, .v2} : $display("b %d %d", v1, v2);
		tagged c '{4'hz00?, .v} : $display("c %d", v);
	endcase
endmodule
