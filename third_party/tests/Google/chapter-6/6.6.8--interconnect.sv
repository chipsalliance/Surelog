/*
:name: interconnect
:description: generic interconnect tests
:tags: 6.6.8
*/
module top();
	interconnect bus;

	mod_i m1(bus);
	mod_o m2(bus);
endmodule

module mod_i(input in);

endmodule

module mod_o(output out);

endmodule
