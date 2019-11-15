module testbench;
    reg [0:1] in;

	wire pat,pat1;
	wire c,s;

    initial begin
        // $dumpfile("testbench.vcd");
        // $dumpvars(0, testbench);

        #5 in = 0;
        repeat (10000) begin
            #5 in = in + 1;
        end

        $display("OKAY");
    end



endmodule
