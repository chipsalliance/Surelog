/*
:name: conditional_pattern
:description: A module testing pattern matching in conditional expressions
:tags: 12.6.3
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

	bit [3:0] val;

	initial begin
          val = tmp matches tagged a '{4'b01zx, .v} ? 1 : 2;
	end
endmodule
