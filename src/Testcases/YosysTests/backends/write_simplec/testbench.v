module testbench;
    reg en;

    initial begin
        // $dumpfile("testbench.vcd");
        // $dumpvars(0, testbench);

        #5 en = 0;
        repeat (10000) begin
            #5 en = 1;
            #5 en = 0;
        end

        $display("OKAY");    
    end
   
    
    reg dinA = 0;
    wire [1:0] dioB;    
    wire [1:0] doutC;

    top uut (
        .en (en ),
        .a (dinA ),
        .b (dioB ),
        .c (doutC )
    );
    
    always @(posedge en) begin
    #3;
    dinA <= !dinA;
    end
	
	assert_equal b_test(.clk(en), .test(dinA), .pat(dioB[0]));
	
	assert_equal c_test(.clk(en), .test(dinA), .pat(doutC[0]));
	
	assert_equal cz_test(.clk(!en), .test(1'bZ), .pat(doutC[0]));
    
endmodule
