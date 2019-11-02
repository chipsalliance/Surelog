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


    reg in = 0;
    wire [7:0] f;


    top uut ( .clk(clk),
              .in(in),
              .out(f));

    always @(posedge clk) begin
    #3
    in <= ~in;
    end



	assert_expr f_test(.clk(clk), .A(f[0]));

endmodule


module assert_expr(input clk, input A);
    always @(posedge clk)
    begin
        //#1;
        if (A === 1'bZ)
        begin
            $display("ERROR: ASSERTION FAILED in %m:",$time," ",A);
            $stop;
        end
    end
endmodule
