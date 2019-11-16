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

	wire clk_o;
	reg [4:0] a;
	wire [31:0] c;

	always @(posedge clk)
	begin
		a = a + 3;
	end
	top uut (clk, a, c,clk_o);

	uut_checker c_test(.clk(clk), .A(clk), .B(clk_o));

endmodule

module uut_checker(input clk, input A, input B);
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
