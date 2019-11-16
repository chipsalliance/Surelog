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

    reg [3:0] in = 2;
    reg [1:0] count = 0;
    reg init = 0;
    wire [7:0] out;

    always @(posedge clk)
    begin
		in = in + 7;
		count = count + 1;
		if (count == 2'b11)
			init = 1;
	end

    top uut(clk,in,out);

    genvar index;
	generate
	for (index=0; index <= 7; index=index+1)
	begin: gen_code_label
		check_X check_output(clk,init,out[index]);
	end
	endgenerate

endmodule

module check_X(input clk,input init, input A);
    always @(posedge clk)
    begin
        #1;
        if (A === 1'bX && init == 1'b1)
        begin
            $display("ERROR: ASSERTION FAILED in %m:",$time," ",A);
            $stop;
        end
    end
endmodule
