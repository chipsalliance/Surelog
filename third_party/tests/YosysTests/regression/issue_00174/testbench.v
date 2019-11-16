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

    wire [5:0] o;
    reg [5:0] i;
    wire [5:0] wave_out;


	always @(posedge clk)
         i <= i + 1;

    wire [31:0] w = 1-i;
	assign wave_out = w/2;

	top uut (i,o);

	genvar index;
	generate
	for (index=0; index <= 2; index=index+1)
	begin: gen_code_label
		assert_dff check_output(clk,o[index],wave_out[index]);
	end
	endgenerate

endmodule
