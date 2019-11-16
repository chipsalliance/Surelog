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

    reg [7:0] a = 0;
    wire [7:0] z;
    wire o1,o2,o3;

    always @(clk)
		a <= a + 1;

    top uut (
        .in (a),
        .out (z),
        .out1 (o1),
        .out2 (o2),
        .out3 (o3)
    );

    assert_Z check_output1(clk,o1);
    assert_Z check_output2(clk,o2);
    assert_Z check_output3(clk,o3);

endmodule
