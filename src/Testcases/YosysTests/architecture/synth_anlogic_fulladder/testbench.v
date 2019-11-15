module testbench;
    reg [11:0] in;

	wire [4:0] patt_out,out;
	wire [4:0] patt_carry_out,carryout;

    initial begin
        // $dumpfile("testbench.vcd");
        // $dumpvars(0, testbench);

        in = 0;
        repeat (10000) begin
            #5 in = in + 1;
        end

        $display("OKAY");
    end

    top uut (
	.x(in[3:0]),
	.y(in[7:4]),
	.cin(in[11:8]),
	.A(out),
	.cout(carryout)
	);

	assign {patt_carry_out,patt_out} =  in[11:8] + in[7:4] + in[3:0];

	assert_comb out_test(.A(patt_out[3]), .B(out[3]));
	assert_comb carry_test(.A(patt_carry_out[3]), .B(carryout[3]));

endmodule

