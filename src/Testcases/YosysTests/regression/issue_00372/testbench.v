module testbench;
    reg clk;

    initial begin
       // $dumpfile("testbench.vcd");
       // $dumpvars(0, testbench);

        #0 clk = 0;
        repeat (10000) begin
            #5 clk = 1;
            #5 clk = 0;
        end

        $display("OKAY");
    end


	reg d = 0;
	wire q;
	reg q_p = 0;

    always @(posedge clk)
		q_p <= d;

	top uut (clk,d,q);

	assert_dff q_test(clk,q,q_p);

endmodule
