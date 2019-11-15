// 256-level PWM generator
// Author: Niels A. Moseley
//         Symbiotic EDA / Moseley Instruments
//         10-11-2018

module pwm256(
    input clk, 
    input rst_n, 
    input [7:0] d_in,
    output reg pwm_out
);

reg signed [7:0] counter;

always @(posedge clk or negedge rst_n)
begin
    if (rst_n == 1'b0)
    begin
        counter <= 8'd0;
        pwm_out <= 1'b0;
    end
    else
    begin
        counter <= counter + 8'd1;
        if (counter >= d_in)
            pwm_out <= 1'b1;
        else
            pwm_out <= 1'b0;
    end
end

endmodule
