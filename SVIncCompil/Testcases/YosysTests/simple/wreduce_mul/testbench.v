module testbench;
    reg [2:0] in;

	wire patt_out,out;
	wire patt_carry_out,carryout;

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

	assign {patt_carry_out,patt_out} =  in[2] * in[1] * in[0];

	assert_comb out_test(.A(patt_out), .B(out));
	//assert_comb carry_test(.A(patt_carry_out), .B(carryout));

endmodule
