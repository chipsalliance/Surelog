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

    wire [2:0] o;
    reg [2:0] i;


	always @(posedge clk)
         i <= i + 1;

	top uut (i[0],i[1],i[2],o[0],o[1],o[2]);

	genvar index;
	generate
	for (index=0; index <= 2; index=index+1)
	begin: gen_code_label
		assert_dff check_output(clk,o[index],i[index]);
	end
	endgenerate

endmodule
