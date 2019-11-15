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


	reg [63:0] A, B, C, D = 0;
	reg [127:0] E, F = 0;
	reg [127:0] X_p, Y_p;
	wire [127:0] X,Y;

    always @(posedge clk)
    begin
		A = A + 248;
		B = B + 338;
		C = C + 435;
		D = D + 282;
		E = E + 1248;
		F = F + 2148;
    end


    integer i;
        always @* begin
                X_p = A*B + E;
                Y_p = F;
                for (i = 0; i < 64; i=i+1)
                        Y_p = Y_p + C[i]*D[i];
        end

	top uut (A,B,C,D,E,F,X,Y);

	uut_checker X_test(.clk(clk), .A(X), .B(X_p));
	uut_checker Y_test(.clk(clk), .A(Y), .B(Y_p));

endmodule

module uut_checker(input clk, input [127:0] A, input [127:0] B);
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
