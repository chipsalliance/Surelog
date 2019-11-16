module testbench;
    reg a;

	wire b;

    initial begin
        // $dumpfile("testbench.vcd");
        // $dumpvars(0, testbench);

        #5 a = 0;
        repeat (10000) begin
            #5 a = ~a;
        end

        $display("OKAY");
    end

    top uut (
	.A(a),
	.Y(b)
	);

	assert_comb b_test(.A(~a),.B(b));

endmodule
