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


    reg [63:0] D = 1;
    reg [5:0] S = 0;
    wire M256;

    top uut (
        .S (S ),
        .D (D ),
        .M256 (M256 )
    );

    always @(posedge clk) begin
    //#3;
	D <= {D[62:0],D[63]};
    S <= S + 1;
    end

	assert_tri m16_test(.en(clk), .A(1'b1), .B(M256));

endmodule
