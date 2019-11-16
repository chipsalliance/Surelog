module testbench;
    reg clk;

    initial begin
        // $dumpfile("testbench.vcd");
        // $dumpvars(0, testbench);

        #5 clk = 0;
        repeat (10000) begin
            #5 clk = 1;
            #5 clk = 0;
        end

        $display("OKAY");
    end

    reg [8:0] a = 0;
    reg [8:0] b = 0;
    wire [8:0] o1,o1p;
    wire [2:0] o2,o2p;
    reg [2:0] c = 0;
    reg [2:0] d = 0;
    wire [2:0] o3,o3p;
    wire [2:0] o4,o4p;
    reg s = 0;

    top uut_top (
    .a(a),
    .b(b),
    .o1(o1),
    .o2(o2),
    .c(c),
    .d(d),
    .o3(o3),
    .o4(o4),
    .s(s)
    );




    always @(posedge clk)
    begin
		s <= ~s;
		a <= a + 12;
		b <= b + 33;
		c <= c + 17;
		d <= d + 22;
    end

    assign o1p = (s ? 0 : a + b);
	assign o2p = (s ? a : a - b);
	assign o3p = (s ? 4'b1111 : d + c);
	assign o4p = (s ? d : c - d);

	uut_top_checker o1_check(.clk(clk), .A(o1), .B(o1p));
	uut_top_checker o2_check(.clk(clk), .A(o2), .B(o2p));
	uut_top_checker o3_check(.clk(clk), .A(o3), .B(o3p));
	uut_top_checker o4_check(.clk(clk), .A(o4), .B(o4p));

endmodule


module uut_top_checker(input clk, input [2:0] A, input [2:0] B);
	always @(posedge clk)
    begin
		//#20
        if (A != B)
        begin
            $display("ERROR: ASSERTION FAILED in %m:",$time," ",A," ",B);
            $stop;
        end
    end
endmodule
