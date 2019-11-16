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

    wire [35:0] b;

    top uut (
        .a (clk),
        .b (b)
    );

    assert_Z check_output1(clk,b[0]);

endmodule
