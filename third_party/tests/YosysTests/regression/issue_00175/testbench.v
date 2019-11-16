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


    wire GC;
    wire GC_p;
    reg  E = 0;

    always @(posedge clk)
		E = ~E;

    reg ED;

	always@(*) begin
		if(~clk)
			ED = E;
	end

    assign GC_p = clk & ED;

	top uut (clk,CG,E);

	assert_dff check_output(clk,GC,GC_p);

endmodule
