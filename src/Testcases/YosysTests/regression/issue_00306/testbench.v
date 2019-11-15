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

	reg [3:0] a = 0;
	wire res_p;
	wire res;

	always @(posedge clk)
	begin
		a = a + 1;
	end

	assign res_p = a < 6'b100000;

    top uut(a,res);

	assert_dff check_res (clk,res, res_p);

endmodule
