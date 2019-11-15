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


    reg [15:0] I0 = 1;
    reg [15:0] I1 = 0;
    wire A,B,C,D,E,F;
    reg Ap,Bp,Cp,Dp,Ep,Fp;

    top uut (
		.clk (clk),
        .I0 (I0 ),
        .I1 (I1 ),
        .A (A ),
        .B (B ),
        .C (C ),
        .D (D ),
        .E (E ),
        .F (F )
    );

    always @(posedge clk)
	begin
		if (I0 < I1)
			Ap <= 1'b1;
		else
			Ap <= 1'b0;

		if (I0 <= I1)
			Bp <= 1'b1;
		else
			Bp <= 1'b0;

		if (I0 != I1)
			Cp <= 1'b1;
		else
			Cp <= 1'b0;

		if (I0 === I1)
			Dp <= 1'b1;
		else
			Dp <= 1'b0;

		if (I0 !== I1)
			Ep <= 1'b1;
		else
			Ep <= 1'b0;

		if (I0 >= I1)
			Fp <= 1'b1;
		else
			Fp <= 1'b0;
	end

    always @(posedge clk) begin
    //#3;
	I0 <= {I0[14:0],I0[15]};
    //D <= D <<< 1;
    I1 <= I1 + 1;
    end

	assert_tri A_test(.en(clk), .A(A), .B(Ap));
	assert_tri B_test(.en(clk), .A(B), .B(Bp));
	assert_tri C_test(.en(clk), .A(C), .B(Cp));
	//assert_tri D_test(.en(clk), .A(D), .B(Dp));
	assert_tri E_test(.en(clk), .A(E), .B(Ep));
	assert_tri F_test(.en(clk), .A(F), .B(Fp));

endmodule
