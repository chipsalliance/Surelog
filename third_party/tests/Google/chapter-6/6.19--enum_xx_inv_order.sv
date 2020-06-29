/*
:name: enum_xx_inv_order
:description: unassigned name following enum with x tests
:should_fail_because: an unassigned enumerated name that follows an enum name with x or z assignments shall be an error
:tags: 6.19
:type: simulation
*/
module top();
	enum integer {a=0, b={32{1'bx}}, c} val;
endmodule
