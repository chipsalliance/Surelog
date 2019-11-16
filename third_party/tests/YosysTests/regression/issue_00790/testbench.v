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


    wire [3:0] D;
    reg [1:0] S = 0;
    reg	[3:0] control = 0;

	always @(posedge clk)
	case(S)
	2'b00: begin end
	2'b01: control <= 4'h2;
	2'b10: control <= 4'h4;
	2'b11: control <= 4'h8;
	default: control <= 4'h0;
	endcase

    top uut (
        .clk (clk ),
        .I (S ),
        .O (D )
    );

    always @(posedge clk) begin
    //#3;
    S <= S + 1;
    end

	check_output out_test( .A(control), .B(D));

endmodule

module check_output(input [3:0] A, input [3:0] B);
    always @(*)
    begin
        #1;
        if (A !== B)
        begin
            $display("ERROR: ASSERTION FAILED in %m:",$time," ",A," ",B);
            $stop;
        end
    end
endmodule
