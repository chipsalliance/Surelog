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

    wire [7:0] dbr;   // Data bus READ
    reg  [7:0] addr = 0;  // Address bus - eight bits

	always @(posedge clk)
	begin
		addr = addr + 1;
	end


	top uut (
    dbr,   // Data bus READ
    addr,  // Address bus - eight bits
    clk          // Clock
    );

	assert_Z b1_test(clk,dbr[7]);

endmodule
