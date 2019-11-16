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


    reg rst;
    wire f;

    top uut ( .clk(clk),
              .rst(rst),
              .count(f));

    initial begin
        rst <= 1;
        #5
        rst <= 0;
    end


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
