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

	reg [7:0] in = 0;
	wire [7:0] out;

    always @(posedge clk) begin
		in <= in + 1;
    end

    top uut (
        .alu_data_d_in (in ),
        .alu_data_d_out (out )
    );


	uut_checker q_test(.clk(clk), .A(out));

endmodule

module uut_checker(input clk, input [7:0] A);
    always @(posedge clk)
    begin
        #1;
        if (A === 8'bXXXXXXXX)
        begin
            $display("ERROR: ASSERTION FAILED in %m:",$time," ",A);
            $stop;
        end
    end
endmodule
