module top #(
    parameter int CounterWidth = 32
) (
    input logic clk,
    output logic [CounterWidth-1:0] out
);

    logic [63:0] counter;
    logic [CounterWidth-1:0] counter_upd;

    initial
        counter = 0;
    always @(posedge clk) begin
        counter_upd = counter[CounterWidth-1:0] + {{CounterWidth-1{1'b0}},1'b1};
    end
    assign out = counter_upd;

endmodule // top
