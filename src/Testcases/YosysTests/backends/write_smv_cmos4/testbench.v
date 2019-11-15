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
   
    
    reg [15:0] D = 1;
    reg [3:0] S = 0;
    wire M16;

    top uut (
        .S (S ),
        .D (D ),
        .M16 (M16 )
    );
    
    always @(posedge clk) begin
    //#3;
	D <= {D[14:0],D[15]};
    //D <= D <<< 1;
    S <= S + 1;
    end
	
	assert_tri m16_test(.en(clk), .A(1'b1), .B(M16));
  
endmodule
