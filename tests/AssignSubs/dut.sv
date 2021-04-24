package pkg;
	typedef enum logic [3:0] {
		PRIV_LVL_M = 4'b11
		} priv_lvl_e;
endpackage

module dut(a0);
	input a0;

	import pkg::*;

	logic [3:0] c [4];

	for (genvar i = 0; i < 1; i++) begin
		always @(posedge a0) begin
			c[i] = {PRIV_LVL_M};
		end
	end
endmodule // dut
