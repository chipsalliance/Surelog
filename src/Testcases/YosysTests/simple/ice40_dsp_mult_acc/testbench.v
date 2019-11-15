module testbench;
    reg clk;

    initial begin
        // $dumpfile("testbench.vcd");
        // $dumpvars(0, testbench);

        #5 clk = 0;
        repeat (10000) begin
            #5 clk = 1;
            #5 clk = 0;
        end

        $display("OKAY");
    end


    reg [7:0] dinA;
    reg [7:0] dinB;
    reg carryin;
    reg rst;
	wire [15:0] p;

    top uut_macc (.clk(clk), .dataa(dinA), .datab(dinB), .aclr(1'b0), .clken(1'b1), .sload(1'b1), .adder_out(p));

    initial begin
        rst <= 0;
        #5
        rst <= 1;
        #5

        @(posedge clk);

        dinA <= 38;
        dinB <= 22;
        carryin <= 1;

        repeat (10) @(posedge clk);

        dinA <= 0;
        dinB <= 0;
        carryin <= 0;

        repeat (10) @(posedge clk);

        dinA <= 33;
        dinB <= 12;
        carryin <= 0;

        repeat (10) @(posedge clk);

        dinA <= 0;
        dinB <= 0;
        carryin <= 0;
    end

	uut_macc_checker macc_check(.clk(clk), .A(dinA), .B(dinB), .C(1'b0), .P(p));

endmodule


module uut_macc_checker(input clk, input [7:0] A, input [7:0] B, input C, input [15:0] P);
	reg [15:0] p;
	always @(posedge clk)
    begin
		#20
		p <= (A * B) + C;
        if (P != p)
        begin
            $display("ERROR: ASSERTION FAILED in %m:",$time," ",P," ",p);
            $stop;
        end
    end
endmodule
