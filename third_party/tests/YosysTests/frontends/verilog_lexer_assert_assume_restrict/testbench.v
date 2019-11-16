module testbench;
    reg [2:0] in;

	wire patt_out = 0;
	wire patt_carry_out = 0;
	wire out = 0;
    wire carryout = 0;

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
	.x(in[0]),
	.y(in[1]),
	.cin(in[2]),
	.A(out),
	.cout(carryout)
	);

    assign    patt_out =  in[1] + in[2];
    assign    patt_carry_out =  in[1] + patt_out;

	assert_comb out_test(.A(patt_out), .B(out));
	assert_comb carry_test(.A(patt_carry_out), .B(carryout));

endmodule
