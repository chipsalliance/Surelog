module testbench;
    reg [7:0] in;

	wire pi_and,i_and;
	wire pi_or,i_or;
	wire pi_xor,i_xor;
	wire pi_nand,i_nand;
	wire pi_nor,i_nor;
	wire pi_xnor,i_xnor;

    initial begin
        // $dumpfile("testbench.vcd");
        // $dumpvars(0, testbench);

        #5 in = 0;
        repeat (10000) begin
            #5 in = in + 1;
        end

        $display("OKAY");
    end

    top uut (
	.x(in),
	.o_and(i_and),
	.o_or(i_or),
	.o_xor(i_xor),
	.o_nand(i_nand),
	.o_nor(i_nor),
	.o_xnor(i_xnor)
	);
	
	assign pi_and =  &in;
	assign pi_or =  |in;
	assign pi_xor =  ^in;
	assign pi_nand =  ~&in;
	assign pi_nor =  ~|in;
	assign pi_xnor =  ~^in;

	assert_comb and_test(.A(pi_and), .B(i_and));

endmodule
