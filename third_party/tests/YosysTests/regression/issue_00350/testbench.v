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



	reg i;
	wire o_p;
	wire o;

    always @(posedge clk) begin
		#2
		i <= ~i;
    end

	reg q = 0;
	always @(posedge clk) q <= 1;
	assign o_p = q & i;

    top uut (clk,i,o);

	assert_dff z_test(clk,o,o_p);
endmodule
