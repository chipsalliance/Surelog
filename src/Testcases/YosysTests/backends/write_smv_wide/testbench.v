module testbench;
    reg en;

    initial begin
        // $dumpfile("testbench.vcd");
        // $dumpvars(0, testbench);

        #5 en = 0;
        repeat (10000) begin
            #5 en = 1;
            #5 en = 0;
        end

        $display("OKAY");
    end


    reg [3:0] dinA = 0;
    wire [3:0] dioB;
    wire [1:0] doutC;

    top uut (
        .en (en ),
        .a (dinA ),
        .b (dioB ),
        .c (doutC )
    );

    always @(posedge en) begin
    #3;
    dinA <= dinA + 1;
    end

	assert_dff b_test(.clk(en), .test(dinA[0]), .pat(dioB[0]));

	//assert_dff c_test(.clk(en), .test(dinA[0]), .pat(doutC[0]));

	assert_dff cz_test(.clk(!en), .test(1'bZ), .pat(doutC[0]));

endmodule
