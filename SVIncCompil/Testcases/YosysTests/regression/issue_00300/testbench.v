`timescale 1ns/1ps

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

	reg [7:0] addr = 0;
	reg [7:0] wdata = 0;
	wire [7:0] rdata;
	wire [7:0] rdata_o;

	always @(posedge clk)
	begin
		addr = addr + 1;
		wdata = wdata + 17;
	end

	reg [7:0] memory [255:0];
	assign rdata = memory[addr];
	always @(posedge clk) memory[addr] <= wdata;



    top uut(clk,addr,wdata,rdata_o);

	uut_mem_checker port_b_test(.clk(clk), .A(rdata), .B(rdata_o));

endmodule

module uut_mem_checker(input clk, input [7:0] A, input [7:0] B);
    always @(posedge clk)
    begin
        #1;
        if (A == B)
        begin
            $display("ERROR: ASSERTION FAILED in %m:",$time,"      ",A," != ",B);
            $stop;
        end
    end
endmodule
