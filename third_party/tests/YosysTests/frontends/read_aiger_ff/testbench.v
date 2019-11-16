module testbench;
    reg clk;

    initial begin
         $dumpfile("testbench.vcd");
         $dumpvars(0, testbench);

        #5 clk = 0;
        repeat (10000) begin
            #5 clk = 1;
            #5 clk = 0;
        end

        $display("OKAY");
    end


    reg n1,n2 = 0;
    wire n3,n3_inv;
    reg n3p;
    wire n3ip;

    top uut (
        .clk (clk ),
        .__1__ (n1 ),
        .__2__ (n2 ),
        .__3__ (n3 ),
        .__3b__ (n3_inv )
    );

    always @(posedge clk) begin
    #3;
    n1 <= n1 + 1;
    #1;
    n2 <= n2 + 1;
    end

	wire _0_;
	wire n4p;


		assign _0_ = ~(n3p ^ n1);
		assign n4p = n2 & ~(_0_);
		assign n3ip = ~n3p;
		always @(posedge clk)
			n3p <= n4p;



	assert_dff dff_test(.clk(clk), .test(n3), .pat(n3p));

endmodule
