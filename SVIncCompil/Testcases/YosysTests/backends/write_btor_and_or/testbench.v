module testbench;
    reg [0:7] in;

	reg patt_B = 0;
	wire B;

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
	
	always @(negedge in[0]) begin
    if (in[1:2] || in[3:4] && in[5:6])
        patt_B <=  in[7] & in[5:6];
    if (in[1:2] || in[3:4] && !in[5:6])
        patt_B <=  in[7] | in[1:2];
end
	
	assert_tri out_test(.A(patt_B), .B(B), .en(1'b1));

endmodule
