module testbench;
    reg clk;

    initial begin
        //$dumpfile("testbench.vcd");
        //$dumpvars(0, testbench);

        #0 clk = 0;
        repeat (10000) begin
            #5 clk = 1;
            #5 clk = 0;
        end

        $display("OKAY");
    end

    wire out;

    top uut (clk,out);

    assert_dff check_output (clk,out,1'b1);

endmodule
