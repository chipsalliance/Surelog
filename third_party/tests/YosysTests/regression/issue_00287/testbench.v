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

    reg [6:0] D = 0;
    reg [1:0] S = 0;
    wire [1:0] Y;
	reg [1:0] Y_p;

    always @(posedge clk)
    begin
		D = D + 3;
		S = S + 1;
    end

    always @* begin : block
		reg [3:0] data [0:3];
		data[0] = D[3:0];
		data[1] = D[4:1];
		data[2] = D[5:2];
		data[3] = D[6:3];
		Y_p = data[S];
	end

    top uut(D,S,Y);

    assert_dff check_Y0 (clk,Y[0],Y_p[0]);
    assert_dff check_Y1 (clk,Y[1],Y_p[1]);

endmodule
