// Code your testbench here
// or browse Examples
module tb_UART;
    reg clk, rst_n, send;
    reg rx; // Not used in this testbench
    reg [7:0] data;
    wire tx, done;

    // Instantiate the UART module
    UART uart_inst(
        .clk(clk),
        .rst_n(rst_n),
        .rx(rx),
        .tx(tx),
        .data(data),
        .send(send),
        .done(done)
    );


    // Clock generator
    always begin
        #5 clk = ~clk;
    end

    // Test procedure
    initial begin
               // Start VCD dumping
        $dumpfile("UART.vcd");
        $dumpvars(0, tb_UART);
        // Initial conditions
        clk = 0;
        rst_n = 0;
        send = 0;
        data = 8'b00000000;
        rx = 1; // Assuming no data is received during the test
        #10 rst_n = 1;
        #10;



        // Apply random inputs and observe the output
        repeat(10) begin
            data = $random & 8'b11111111;
            send = 1;
            #10 while(!done) #10; // Wait for transmission to complete
            send = 0;
            #10;
        end

        // Finish the simulation
        $finish;
    end
endmodule
