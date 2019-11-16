/*
:name: enum_xx_inv_order
:description: unassigned name following enum with x tests
:should_fail: 1
:tags: 6.19
:type: simulation
*/
module top();
	enum integer {a=0, b={32{1'bx}}, c} val;
endmodule
