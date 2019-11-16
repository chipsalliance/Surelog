module testbench;
    reg [4:0] in;

    initial begin
        // $dumpfile("testbench.vcd");
        // $dumpvars(0, testbench);

        #5 in = 0;
        repeat (10000) begin
            #5 in = in + 1;
        end

        $display("OKAY");
    end

    wire out,y;

    top uut (
	.a(in),
	.y(out)
	);

	integer i, j;
	reg [31:0] lut;

	initial begin
		for (i = 0; i < 32; i = i+1) begin
			lut[i] = i > 1;
			for (j = 2; j*j <= i; j = j+1)
				if (i % j == 0)
					lut[i] = 0;
		end
	end

	assign y = lut[in];

	assert_comb out_test(.A(y), .B(out));

endmodule
