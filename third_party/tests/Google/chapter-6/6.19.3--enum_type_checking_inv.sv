/*
:name: enum_type_checking_inv
:description: invalid enum assignment tests
:should_fail_because: enum cannot be assigned value from outside its defined type
:tags: 6.19.3
:type: simulation
*/
module top();
	typedef enum {a, b, c, d} e;

	initial begin
		e val;
		val = 1;
	end
endmodule
