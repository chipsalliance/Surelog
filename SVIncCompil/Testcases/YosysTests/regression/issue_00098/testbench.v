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

    always @(clk)
		a <= a + 1;

    top uut (
        .a (a),
        .z (z)
    );

    assert_Z check_output(clk,z[0]);

endmodule
