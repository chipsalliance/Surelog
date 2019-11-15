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
   
    
    reg a = 0;
    reg b = 0;
    reg rst;    
    reg en;
    wire s;
    wire bs;
    wire f;
    
    top uut ( .clk(clk),
              .rst(rst), 
              .en(en), 
              .a(a), 
              .b(b), 
              .s(s), 
              .bs(bs), 
              .f(f));
              
    always @(posedge clk)
    begin
        #2
        a <= ~a;
    end
    
    always @(posedge clk)
    begin
        #4
        b <= ~b;
    end
    
    initial begin
        en <= 1;
        rst <= 1;
        #5
        rst <= 0;
    end
    
    
    assert_expr s_test(.clk(clk), .A(s));
	assert_expr bs_test(.clk(clk), .A(bs));
	assert_expr f_test(.clk(clk), .A(f));
  
endmodule


module assert_expr(input clk, input A);
    always @(posedge clk)
    begin
        //#1;
        if (A == 1'bZ)
        begin
            $display("ERROR: ASSERTION FAILED in %m:",$time," ",A);
            $stop;
        end
    end
endmodule
