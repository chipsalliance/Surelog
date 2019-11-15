module testbench;
    reg [2:0] in;

	reg patt_out = 0;
	reg patt_carry_out = 0;
	wire out;
    wire carryout;

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
	.x(in[0]),
	.y(in[1]),
	.cin(in[2]),
	.A(out),
	.cout(carryout)
	);
	
	always @(posedge in[0]) 
        patt_out <=  in[1] + in[2];
    always @(negedge in[0])
        patt_carry_out <=  in[1] + patt_out;

	assert_tri out_test(.A(patt_out), .B(out), .en(1'b1));
	assert_tri carry_test(.A(patt_carry_out), .B(carryout), .en(1'b1));

endmodule
