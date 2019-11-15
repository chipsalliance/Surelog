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

	reg [1:0] c = 0;
   reg  in, jmp = 0;
   wire  [8-1:0]  out,out_o;

   always @(posedge clk)
   begin
	c = c + 1;
   end

   assign in = c[0];
   assign jmp = c[1];

	initial  out = 0;
	always @(posedge clk)
	if (jmp)
		out <= { out[UNDEFINED-1:0], in };
	else
		out <= { 1'b0, out[UNDEFINED-1:1] };

	top uut (clk, jmp, in, out_o);

	assert_comb o0_test (out[0],out_o[0]);
	assert_comb o1_test (out[1],out_o[1]);
	assert_comb o2_test (out[2],out_o[2]);
	assert_comb o3_test (out[3],out_o[3]);
	assert_comb o4_test (out[4],out_o[4]);
	assert_comb o5_test (out[5],out_o[5]);
	assert_comb o6_test (out[6],out_o[6]);
	assert_comb o7_test (out[7],out_o[7]);

endmodule
