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

    wire dinA = xorshift32(rng * 5);
    wire dinC = xorshift32(rng * 7);
    
    wire doutB;

    top uut (
        .clk (clk ),
        .a (dinA ),
        .c (dinC),
        .b (doutB )
    );
    
	assert_dff ff_test(.clk(clk), .test(doutB), .pat(1'b1));
    
endmodule
