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

    reg  [3:0] A;
    reg  [3:0] B;
    wire [3:0] O;
    wire [3:0] O_p;
    wire       C;
    wire       C_p;

    assign {C_p, O_p} = A + B;

	top uut (C,O,A,B);

	assert_comb c_test (C,C_p);
	assert_comb o0_test (O[0],O_p[0]);
	assert_comb o1_test (O[1],O_p[1]);
	assert_comb o2_test (O[2],O_p[2]);
	assert_comb o3_test (O[3],O_p[3]);

endmodule
