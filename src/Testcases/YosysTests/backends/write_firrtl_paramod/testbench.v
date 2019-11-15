module middle_tb
(
	input x,
	input y,
	output o
);

parameter Y = 1'b1;

urtl_tb u_urtl (.x(x),.o(o),.y(Y));
endmodule

module urtl_tb
(
	input x,
	input y,
	output o
);

assign o = x + y;
endmodule

module testbench;
    reg [0:2] in;

	reg patt_A = 1'bX;
	wire patt_cout;
	wire cout,o;
    wire A;

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
	.A(A),
	.cout(cout)
	);

	always @(posedge in[2])
	patt_A <= o;

assign pattcout =  in[2]? in[1] : in[0];

middle_tb #(1'b0) u_mid1 (.x(in[0]),.o(o),.y(1'b0));
middle_tb #(1'b0) u_mid2 (.x(in[0]),.o(o),.y(1'b1));
middle_tb #(1'b0) u_mid3 (.x(in[0]),.o(o),.y(1'bX));
middle_tb #(1'b0) u_mid4 (.x(in[0]),.o(o),.y(1'bX));

	assert_comb out_test(.A(patt_A), .B(A));

endmodule
