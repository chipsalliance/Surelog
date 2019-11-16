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


    reg [2:0] dinA = 0;
    wire doutB,doutB1;
	reg dffs,dffr = 0;

    top uut (
        .clk (clk ),
        .a (dinA[0] ),
        .pre (dinA[1] ),
        .clr (dinA[2] ),
        .b (doutB ),
        .b1 (doutB1 )
    );

    always @(posedge clk) begin
    #3;
    dinA <= dinA + 1;
    end

	always @( posedge clk, negedge dinA[1] )
		if ( !dinA[1] )
			dffs <= 1'b1;
		else
            dffs <= dinA[0];

    always @( posedge clk, negedge dinA[2] )
		if ( !dinA[2] )
			dffr <= 1'b0;
		else
            dffr <= dinA[0];

	assert_dff dffs_test(.clk(clk), .test(doutB), .pat(dffs));
    assert_dff dffr_test(.clk(clk), .test(doutB1), .pat(dffr));

endmodule
