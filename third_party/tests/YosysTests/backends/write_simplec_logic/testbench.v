module testbench;
    reg [0:7] in;

	wire patt_B;
	wire B;
	wire x,y,z,A;

    initial begin
        // $dumpfile("testbench.vcd");
        // $dumpvars(0, testbench);

        #5 in = 0;
        repeat (10000) begin
            #5 in = in + 1;
        end

        $display("OKAY");
    end

    top uut (
	.x(in[1:2]),
	.y(in[3:4]),
	.z(in[5:6]),
	.clk(in[0]),
	.A(in[7]),
	.B(B)
	);
	
    assign  patt_B = (x || y || !z)?  (A & z) : ~x;
    assign x = in[1:2];
    assign y = in[3:4];
    assign z = in[5:6];
    assign A = in[7];

	
	assert_comb out_test(.A(patt_B), .B(B));

endmodule
