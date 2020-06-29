/*
:name: if_pattern
:description: A module testing pattern matching in if statements
:tags: 12.6.2
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

	initial if (tmp matches tagged a '{4'b01zx, .v})
		$display("a %d", v);
		
		
endmodule
