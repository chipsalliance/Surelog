module testbench;
    reg clk;

    initial begin
       // $dumpfile("testbench.vcd");
       // $dumpvars(0, testbench);

        #0 clk = 0;
        repeat (10000) begin
            #5 clk = 1;
            #5 clk = 0;
        end

        $display("OKAY");
    end

    reg [1:0] a = 0;
    reg rst = 0;


    top uut (
		.x(x),
		.clk(clk),
		.rst(rst),
		.a(a)
    );


    always @(posedge clk) begin

    a <= a + 1;
    end

	always @(posedge clk) begin
    #2;
	rst <= !rst;
    end

	uut_checker q_test(.clk(clk), .en(rst), .A(x));
endmodule



module uut_checker(input clk, input en, input A);
    always @(posedge clk)
    begin
        #1;
        if (en == 1 & A === 1'bz)
        begin
            $display("ERROR: ASSERTION FAILED in %m:",$time," ",A);
            $stop;
        end
    end
endmodule
