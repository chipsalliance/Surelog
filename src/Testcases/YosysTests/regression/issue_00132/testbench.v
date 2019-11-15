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
    wire [7:0] y;

    always @(posedge clk)
    begin
		a = a + 3;
	end

    top uut (
        .a (a ),
        .y (y )
    );

    genvar index;
	generate
	for (index=0; index <= 7; index=index+1)
	begin: gen_code_label
		assert_Z check_output(clk,y[index]);
	end
	endgenerate

endmodule
