module testbench;
    reg clk;

    initial begin
        $dumpfile("testbench.vcd");
        $dumpvars(0, testbench);

        #0 clk = 0;
        repeat (10000) begin
            #5 clk = 1;
            #5 clk = 0;
        end

        $display("OKAY");
    end

    reg i = 0;
    reg out;
	reg b,u = 0;

	always @(posedge clk)
	begin
		b = b + 1;
	    u = ~u;
	end


	top uut (clk,b,u,out);



endmodule
