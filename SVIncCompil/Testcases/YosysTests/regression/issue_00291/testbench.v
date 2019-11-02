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

    reg rst = 0;
    reg any_pop = 0;
    reg any_push = 0;

    always @(posedge clk)
    begin
		rst = 1;
		#1
		any_pop = ~any_pop;
		#3
		any_push = ~any_push;
    end



    top uut(rst,clk,any_push,any_pop);

endmodule
