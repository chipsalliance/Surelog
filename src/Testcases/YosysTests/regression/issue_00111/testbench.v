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

    reg [127:0] state,key = 0;
    wire [127:0] out;

    /*always @(posedge clk)
    begin
		state = state + 2300;
		key = key + 2500;
	end*/

    top uut (
        .state (state ),
        .key (key ),
        .out (out )
    );

    /*genvar index;
	generate
	for (index=0; index < 128; index=index+25)
	begin: gen_code_label
		assert_Z check_output(clk,out[index]);
	end
	endgenerate*/

	assert_Z check_output(clk,out[0]);

endmodule
