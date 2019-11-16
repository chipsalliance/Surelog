module testbench;
    reg clk;

    initial begin
         $dumpfile("testbench.vcd");
         $dumpvars(0, testbench);

        #5 clk = 0;
        repeat (10000) begin
            #5 clk = 1;
            #5 clk = 0;
        end

        $display("OKAY");
    end


	reg [9:0] addr = 0;
    reg ce = 0;
	wire [7:0] q;

    top uut (
	.clk(clk),
	.addr(addr),
	.ce(ce),
	.q(q)
    );

    always @(posedge clk) begin

    addr <= addr + 1;
    end

	always @(posedge clk) begin
    #3;
	ce <= !ce;
    end

	uut_mem_checker q_test(.clk(clk), .en(ce), .A(q));

endmodule

module uut_mem_checker(input clk, input en, input [7:0] A);
    always @(posedge clk)
    begin
        #1;
        if (en == 1 & A === 8'b00000000)
        begin
            $display("ERROR: ASSERTION FAILED in %m:",$time," ",A);
            $stop;
        end
    end
endmodule
