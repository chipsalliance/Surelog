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

    reg a = 0;
    reg ce = 1;
    wire d;

    always @(posedge clk)
    begin
		a = a + 1;
	end

	top uut (
        .CLKIN(clk),
        .A (a ),
        .CE (ce),
        .D1 (d)
    );

		assert_X check_output(clk,d);

endmodule
