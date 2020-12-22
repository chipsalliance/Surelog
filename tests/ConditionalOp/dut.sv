module top();
        localparam int unsigned NrHarts = 1;

	localparam int unsigned NrHarts2 = 8;
 
	localparam int unsigned HartSelLen1 = (NrHarts == 1) ? 1 : $clog2(NrHarts);
	
	localparam int unsigned HartSelLen2 = (NrHarts == 1) ? 1 : 0;

	localparam int unsigned HartSelLen3 = (NrHarts == 1) ? 1 : $clog2(NrHarts2);

endmodule

module ibex_register_file #(
    parameter bit          RV32E             = 0,
    parameter int unsigned DataWidth         = 32
);
  localparam int unsigned ADDR_WIDTH = RV32E ? 4 : 5;
  localparam int unsigned NUM_WORDS  = 2**ADDR_WIDTH;

  logic [NUM_WORDS-1:0][DataWidth-1:0] rf_reg;
  logic [NUM_WORDS-1:1][DataWidth-1:0] rf_reg_q;
  logic [NUM_WORDS-1:1]                we_a_dec;
endmodule // ibex_register_file
