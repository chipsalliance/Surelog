module testbench;
    reg [6:0] in;

	wire x;
	wire [2:0] y;
	wire [2:0] cin;

	wire patt_out = 0;
	wire patt_carry_out = 0;
	wire patt_out1 = 0;
	wire patt_carry_out1 = 0;
	wire out = 0;
    wire carryout = 0;
    wire control;
	wire control_patt;

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
	.x(x),
	.y(y),
	.cin(cin),
	.A(out),
	.cout(carryout),
	.control(control)
	);

	wire A1,cout1;
	wire [2:0] n_y;

	wire [2:0] n_cin;

//  initial begin
//     A = 0;
//     cout = 0;
//  end

assign x = in[0];
assign y = in[3:1];
assign cin = in[6:4];

assign control_patt = x & y & cin;

    assert_dff out_test(.clk(in[0]), .test(control),.pat(control_patt));

endmodule
