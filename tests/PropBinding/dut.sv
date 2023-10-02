

module clock_divider_assertions (
    input clk,
    input reset,
    input clk_out
);

    // Prop
    property p_reset;
        @(posedge clk)
        reset |-> ##1 !clk_out;  // clk_out should be low if counter is reset
    endproperty
  
    // Assert Property
    assert property (p_reset);

endmodule


