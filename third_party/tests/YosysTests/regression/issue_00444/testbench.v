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


	reg [4:0] a;
	wire [31:0] c;

	always @(posedge clk)
	begin
		a = a + 3;
	end
	top uut (clk, a, c);

	uut_checker c_test(.clk(clk), .A(c), .B(c));

endmodule

module uut_checker(input clk, input [31:0] A, input [31:0] B);
    always @(posedge clk)
    begin
        #1;
        if (A != B)
        begin
            $display("ERROR: ASSERTION FAILED in %m:",$time,"      ",A," != ",B);
            $stop;
        end
    end
endmodule
