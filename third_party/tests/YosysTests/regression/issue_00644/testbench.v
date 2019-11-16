module testbench;
    reg clk;

    initial begin
        $dumpfile("testbench.vcd");
        $dumpvars(0, testbench);

        #0 clk = 0;
        repeat (10000) begin
            #5 clk = 1;
            #5 clk = 0;
        end

        $display("OKAY");
    end

    reg i = 0;
    reg out;
	wire b;

	always @(posedge clk)
	begin
		i = i + 1;
	end


	top uut (clk,i,b);

	always @(posedge clk)
        out <= $past(i,9);

	assert_dff b1_test(.clk(clk), .test(b), .pat(out));

endmodule
