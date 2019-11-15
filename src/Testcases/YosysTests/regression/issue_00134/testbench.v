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

    reg [15:0] a = 0;
    wire [15:0] y;

    always @(posedge clk)
    begin
		a = a + 3;
	end

    top uut (
        .in_data (a ),
        .do (y )
    );

    genvar index;
	generate
	for (index=0; index <= 15; index=index+1)
	begin: gen_code_label
		assert_X check_output(clk,y[index]);
	end
	endgenerate

endmodule
