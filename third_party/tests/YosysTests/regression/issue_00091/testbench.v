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

    wire rst = 0;
    wire A;


    top uut (
		.A (A),
        .clk (clk),
        .rst (rst)
    );

endmodule
