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

    reg [4:0] i = 0;
	wire [4:0] b;

	always @(posedge clk)
	begin
		i = i + 1;
	end


	main uut (b,clk);

	assert_Z b_test(.clk(clk), .A(b[0]));

endmodule
