`timescale 1ns/1ps

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
	reg [7:0] b = 0;
	wire [7:0] z;

	always @(posedge clk)
	begin
		a = a + 1;
		b = b + 7;
	end

    top uut(a,b,z);

	genvar index;
	generate
	for (index=0; index <= 7; index=index+1)
	begin: gen_code_label
		assert_Z check_output(clk,z[index]);
	end
	endgenerate

endmodule
