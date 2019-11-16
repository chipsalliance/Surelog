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
   
    function [31:0] xorshift32;
        input [31:0] arg;
        begin
                xorshift32 = arg;
                // Xorshift32 RNG, doi:10.18637/jss.v008.i14
                xorshift32 = xorshift32 ^ (xorshift32 << 13);
                xorshift32 = xorshift32 ^ (xorshift32 >> 17);
                xorshift32 = xorshift32 ^ (xorshift32 <<  5);
        end
    endfunction

    reg [31:0] rng = 123456789;
    always @(posedge clk) rng <= xorshift32(rng);

    wire a = xorshift32(rng * 5);
    wire b = xorshift32(rng * 7);
    reg rst;
    wire g0;
    wire g1;
    
    top uut (
        .a (a),
        .b (b),
        .clk (clk),
        .rst (rst),
        .g0(g0),
        .g1(g1)
    );
    
    initial begin
        rst <= 1;
        #5
        rst <= 0;
    end
	
    assert_Z g0_test(.clk(clk), .A(g0));
	assert_Z g1_test(.clk(clk), .A(g1));
  
endmodule
