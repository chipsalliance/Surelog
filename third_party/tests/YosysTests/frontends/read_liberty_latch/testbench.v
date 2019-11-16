module testbench;
    reg [2:0] in;

	reg patt_out = 0;
	wire out = 0;

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
	.CLK(in[0]),
	.D(in[1]),
	.CLR(in[2]),
	.Q(out)
	);



   always @(posedge in[0] or posedge in[2])
    if (in[2])
      patt_out <= 0;
    else
      patt_out <= in[1];

	assert_dff dff_test(.clk(in[0]),.test(out),.pat(patt_out));

endmodule
