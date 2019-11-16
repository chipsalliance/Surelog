module testbench;
    reg [31:0] in;

	wire [15:0] outA,outB;
	wire [15:0] poutA,poutB;

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
	.x(in[15:0]),
	.y(in[31:16]),
	.A(outA),
	.B(outB)
	);


	assign poutA =  in[15:0] + in[31:16];
	assign poutB =  in[15:0] - in[31:16];

	check_comb add_test(outA, poutA);
	check_comb sub_test(outB, poutB);
	assert_comb sub0_test(outB[2], poutB[2]);

endmodule

module check_comb(input [15:0] test, input [15:0] pat);
    always @*
    begin
        #1;
        if (test != pat)
        begin
            $display("ERROR: ASSERTION FAILED in %m:",$time," ",test," ",pat);
            $stop;
        end
    end
endmodule

