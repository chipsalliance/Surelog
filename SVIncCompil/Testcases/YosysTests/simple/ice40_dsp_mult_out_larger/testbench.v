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


    reg [15:0] dinA;
    reg [15:0] dinB;
    reg carryin;
    reg rst;
	wire [47:0] p;

    top uut_macc (
        .p (p),
        .a (dinA),
        .b (dinB),
        .carryin (carryin ),
        .clk (clk),
        .rst (rst)
    );

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

	uut_macc_checker macc_check(.clk(clk), .A(dinA), .B(dinB), .C(carryin), .P(p));

endmodule


module uut_macc_checker(input clk, input [15:0] A, input [15:0] B, input C, input [47:0] P);
	reg [47:0] p;
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
