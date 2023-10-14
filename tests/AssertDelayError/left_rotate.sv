module left_rotation (
    input wire clk,     // Clock input
    input wire reset,   // Active-high synchronous reset
    input wire [7:0] in_data, // 8-bit input data
    output reg [7:0] out_data  // 8-bit output data after rotation
);

always @(posedge clk or posedge reset) begin
    if (reset) begin
        out_data <= 8'b0000_0000;  // Reset value
    end else begin
        // Perform left rotation
        out_data <= {out_data[6:0], out_data[7]};
    end
end

initial begin
    out_data = 8'b0000_0000;  // Initial value
end

endmodule

