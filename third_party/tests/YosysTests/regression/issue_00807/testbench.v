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


	reg [7:0] x = 0;
	wire y;

	always @(posedge clk)
	begin
		x = x + 1;
	end


	top uut (x,y);

	assert_X out_test (clk,y);

endmodule
