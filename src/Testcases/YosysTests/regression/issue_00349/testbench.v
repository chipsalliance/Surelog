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
	reg z_p;
	wire z;

    always @(posedge clk) begin
		in <= in + 1;
    end


    always @*
     z_p <= in[0] ~& in[1];

     top uut (in[0],in[1],z);


	assert_dff z_test(clk,z,z_p);
endmodule
