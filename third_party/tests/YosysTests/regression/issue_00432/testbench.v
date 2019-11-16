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


	reg [7:0] a;
	reg [7:0] b;
	wire [7:0] c_p;
	wire [7:0] c;

	always @(posedge clk)
	begin
		a = a + 3;
		b = b + 7;
	end

	assign c_p = a[$signed(b) +: 8];

	top uut (a, b, c);

	uut_checker c_test(.clk(clk), .A(c_p), .B(c));

endmodule

module uut_checker(input clk, input [7:0] A, input [7:0] B);
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
