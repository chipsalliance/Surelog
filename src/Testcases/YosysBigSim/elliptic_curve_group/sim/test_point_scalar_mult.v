// `timescale 1ns / 1ps
`include "../rtl/inc.v"
`define SKIP_SLOW

module test_point_scalar_mult(input start, output reg stop = 0);

    // Inputs
    reg clk;
    reg reset;
    reg [`WIDTH:0] x1, y1;
    reg zero1;
    reg [`SCALAR_WIDTH:0] c;

    // Outputs
    wire done;
    wire zero3;
    wire [`WIDTH:0] x3, y3;

    // Instantiate the Unit Under Test (UUT)
    point_scalar_mult uut (
        .clk(clk), 
        .reset(reset), 
        .x1(x1), 
        .y1(y1), 
        .zero1(zero1), 
        .c(c), 
        .done(done), 
        .x3(x3), 
        .y3(y3), 
        .zero3(zero3)
    );

    initial begin
    	@(posedge start);

        // Initialize Inputs
        clk = 0;
        reset = 0;
        x1 = 0;
        y1 = 0;
        zero1 = 0;
        c = 0;

        // Wait 100 ns for global reset to finish
        #100;

        // Add stimulus here
        // if scalar value is zero, then the result is inf point
        x1 = 194'h2a4290286121261a82446a41200622024988295015114486;
        y1 = 194'h16595a61040a8611209820112a1582a081a1a182264601252;
        zero1 = 0;
        c = 0;
        go;
        $write("%b %x %x %t ", zero3, x3, y3, $time);
        if (zero3 !== 1) begin $display("E"); $finish; end else $display(":D    <1>");

        // if scalar value is one, then the result is the input point, test case 1
        x1 = 194'h2a4290286121261a82446a41200622024988295015114486;
        y1 = 194'h16595a61040a8611209820112a1582a081a1a182264601252;
        zero1 = 0;
        c = 1;
        go;
        $write("%b %x %x %t ", zero3, x3, y3, $time);
        if (zero3 !== 0 ||
            x3 !== 194'h2a4290286121261a82446a41200622024988295015114486 ||
            y3 !== 194'h16595a61040a8611209820112a1582a081a1a182264601252
            ) begin $display("E"); $finish; end else $display(":D    <2>");

        // if scalar value is one, then the result is the input point, test case 2
        x1 = 194'h2a4290286121261a82446a41200622024988295015114486;
        y1 = 194'h16595a61040a8611209820112a1582a081a1a182264601252;
        zero1 = 1;
        c = 1;
        go;
        $write("%b %x %x %t ", zero3, x3, y3, $time);
        if (zero3 !== 1) begin $display("E"); $finish; end else $display(":D    <3>");

`ifndef SKIP_SLOW
        // if scalar value is one thousand. test case 1
        x1 = 194'h126569286a9860859046680265109015266416aa984082610;
        y1 = 194'h2a41880890628944a6844a269258216041061196854181160;
        zero1 = 0;
        c = 1000;
        go;
        $write("%b %x %x %t ", zero3, x3, y3, $time);
        if (zero3 !== 0 ||
            x3 !== 194'h221495405a9425682104a6a005a42a562564469158a962019 ||
            y3 !== 194'h1048569408a2846964811161095218005098aa06582419a46
            ) begin $display("E"); $finish; end else $display(":D    <4>");
`endif

        // if scalar value is one thousand. test case 2
        x1 = 194'h126569286a9860859046680265109015266416aa984082610;
        y1 = 194'h2a41880890628944a6844a269258216041061196854181160;
        zero1 = 1;
        c = 1000;
        go;
        $write("%b %x %x %t ", zero3, x3, y3, $time);
        if (zero3 !== 1) begin $display("E"); $finish; end else $display(":D    <5>");

`ifndef SKIP_SLOW
        // if scalar value is the order of the generator point, then the result is the inf point
        x1 = 194'h288162298554054820552a05426081a1842886a58916a6249;
        y1 = 194'h2895955069089214054596a189a4420556589054140941695;
        zero1 = 0;
        c = 152'd2726865189058261010774960798134976187171462721;
        go;
        $write("%b %x %x %t ", zero3, x3, y3, $time);
        if (zero3 !== 1) begin $display("E"); $finish; end else $display(":D    <6>");
`endif

        // good work, buddy
	stop = 1;
    end

	initial begin
		@(posedge start);
		while (!stop) begin
			#5;
			clk = ~clk;
		end
	end

    task go;
      begin
        @ (negedge clk); reset = 1; @ (negedge clk); reset = 0;
	while (done == 0) begin @(posedge done); #1; end
      end
    endtask
endmodule

