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
   
    
    reg [4:0] a;
    reg [4:0] b;    
    reg [4:0] c;
    reg rst;
    wire [4:0] x;
    wire [4:0] y;
    wire [4:0] z;
        
    top uut_fsm (
        .clk (clk),
        .rst (rst),
        .a (a),
        .b (b),
        .c (c),
        .x(x),
        .y(y),
        .z(z)
    );
    
    initial begin
		rst <= 0;
        #5
        rst <= 1;
        #5
        rst <= 0;
        #5
        
        @(posedge clk);
        
        a <= 4'b1111;
        b <= 4'b1010;        
        c <= 4'b1011;
        
        repeat (10) @(posedge clk);
        
        a <= 4'b1000;
        b <= 4'b1100;        
        c <= 4'b1010;
        
        repeat (10) @(posedge clk);
        
        a <= 4'b1100;
        b <= 4'b0100;
        c <= 4'b1011;
        
        repeat (10) @(posedge clk);
        
        a <= 4'b1101;
        b <= 4'b1110;
        c <= 4'b0000;
    end
    
    uut_fsm_checker x_test(.clk(clk), .A(x));
	uut_fsm_checker y_test(.clk(clk), .A(y));
	uut_fsm_checker z_test(.clk(clk), .A(z));
  
endmodule


module uut_fsm_checker(input clk, input [4:0] A);
    always @(posedge clk)
    begin
        //#1;
        if (A == 4'b0000)
        begin
            $display("ERROR: ASSERTION FAILED in %m:",$time," ",A);
            $stop;
        end
    end
endmodule
