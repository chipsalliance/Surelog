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
   
    reg [1:0] S = 0;
    wire [3:0] Y;

    top uut (
        .C (clk),
        .S (S ),
        .Y (Y )
    );
    
    always @(posedge clk) begin
    //#3;
    S <= S + 1;
    end
	
	assert_tri m16_test(.en(clk), .A(1'b1), .B(Y[0]|Y[1]|Y[2]|Y[3]));
  
endmodule
