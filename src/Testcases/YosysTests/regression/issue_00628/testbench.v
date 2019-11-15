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
	wire b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17;

	always @(posedge clk)
	begin
		i = i + 1;
	end


	top uut (clk,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17);

	assert_Z b1_test(.clk(clk), .A(b1));

	assert_Z b17_test(.clk(clk), .A(b17));

endmodule
