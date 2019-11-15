module testbench;
    reg [0:1] in;

	wire pat,pat1;
	wire c,s;

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
	.c(c),
	.s(s),
	.x(in[0]),
	.y(in[1])
	);

  assign pat = in[1] ^ in[0];
  assign pat1 = in[1] & in[0];

	assert_comb out_test(.A(pat), .B(s));
	assert_comb out1_test(.A(pat1), .B(c));

endmodule
