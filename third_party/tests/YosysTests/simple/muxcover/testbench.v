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
   
    
    reg [255:0] D = 1;
    reg [7:0] S = 0;
    wire M256;

    top uut (
        .S (S ),
        .D (D ),
        .M256 (M256 )
    );
    
    always @(posedge clk) begin
    //#3;
	D <= {D[254:0],D[255]};
    S <= S + 1;
    end
	
	assert_tri m16_test(.en(clk), .A(1'b1), .B(M256));
  
endmodule
