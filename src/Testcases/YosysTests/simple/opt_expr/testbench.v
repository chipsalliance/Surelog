module testbench;
    reg clk;

    initial begin
        // $dumpfile("testbench.vcd");
        // $dumpvars(0, testbench);

        #5 clk = 0;
        repeat (10000) begin
            #5 clk = 1;
            #5 clk = 0;
        end

        $display("OKAY");
    end


    reg dinA = 0;
    wire doutB;
    wire pre,clr;
    reg q = 0;

    top uut (
        .clk (clk ),
        .clr (1'b0 ),
        .pre (1'b0 ),
        .a (dinA ),
        .b (doutB )
    );

    always @(negedge clk) begin
    #3;
    dinA <= !dinA;
    end

    assign pre = 1'b0;
    assign clr = 1'b0;

    	always @( negedge clk, posedge pre, negedge clr )
		if ( pre )
			q <= 1'b1;
		else if ( clr )
			q <= 1'b0;
		else
            q <= dinA;

	assert_dff ff_test(.clk(~clk), .test(doutB), .pat(q));

endmodule
