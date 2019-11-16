`timescale 1ns/1ps

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

    wire a,b,c,d,e,f;

    top uut(clk,a,b,c,d,e,f);

endmodule
