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

    reg [1:0] in = 0;
    always @(posedge clk)
		in = in + 1;

    top uut (
        .in_a(in),
        .out_vt(out)
    );
endmodule
