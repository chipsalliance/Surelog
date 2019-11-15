module top(
    output reg [7:0] dbr,   // Data bus READ
    input  [7:0] addr,  // Address bus - eight bits
    input  clk          // Clock
    );

    reg [7:0] rom_data[0:255];

    always @(posedge clk)
        dbr <= rom_data[addr];

endmodule
