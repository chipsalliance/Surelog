
module tb_left_rotation;
    reg clk, reset;
    reg [7:0] in_data;
    wire [7:0] out_data;

    // Instantiate the left_rotation module
    left_rotation left_rotation_inst(
        .clk(clk),
        .reset(reset),
        .in_data(in_data),
        .out_data(out_data)
    );

    // Clock generator
    always begin
        #5 clk = ~clk;
    end

    // Test procedure
    initial begin
        // Initial conditions
        clk = 0;
        reset = 1;
        in_data = 8'b0;
        #10 reset = 0;
        #10;

        // Start VCD dumping
        $dumpfile("left_rotation.vcd");
        $dumpvars(0, tb_left_rotation);

        // Apply random inputs and observe the output
        repeat(20) begin
            in_data = $random & 8'b11111111;
            #10;
        end

        // Assert reset to observe reset behavior
        #10 reset = 1;
        #10 reset = 0;

        // Finish the simulation
        $finish;
    end
endmodule

