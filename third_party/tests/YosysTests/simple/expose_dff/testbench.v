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

    top uut (
        .clk (clk ),
        .a (dinA ),
        .b (doutB )
    );

    always @(posedge clk) begin
    //#3;
    dinA <= !dinA;
    end

	assert_dff ff_test(.clk(clk), .test(doutB), .pat(!dinA));

endmodule
