`default_nettype none

module Device(
    input wire [7:0] doubleNibble,
    output wire [3:0] sum
);

  
    Helper instance1(doubleNibble[7:4], doubleNibble[3:0], sum);
    
    wire [3:0] ignored;
    Helper instance2(
        .a(doubleNibble[7:4]),
        .b(doubleNibble[3:0]),
        .result(ignored)
    );


endmodule

module Helper(
    input wire [3:0] a, b,
    output wire [3:0] result
);

    assign result = a + b;

endmodule
