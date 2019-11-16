// 5th order CIC filter with decimation factor of 5
// Author: Niels A. Moseley
//         Symbiotic EDA / Moseley Instruments
// 12-11-2018

module cic5(
    input  clk, 
    input  rst_n, 
    input  signed [15:0] d_in, 
    output reg signed [27:0] d_out, 
    output reg d_out_valid
    );

reg signed [27:0] int_s  [1:5]; // integrator states
reg signed [27:0] comb_s [1:5]; // comb filter states
reg signed [27:0] tmp    [1:5];    // temporary var
reg [2:0]  decimation_count;

integer i;

    always @(posedge clk)
    begin
        if (rst_n == 1'b0)
        begin
            for (i=1; i<=5; i=i+1) begin
                int_s[i]  <= 16'd0;
                comb_s[i] <= 28'd0;
            end
            decimation_count <= 0;            
            d_out_valid <= 0;
            d_out <= 0;
        end
        else
        begin
            // default updates
            d_out_valid <= 1'b0;
            decimation_count <= decimation_count + 1;

            // update the integrator filter states
            int_s[1] <= int_s[1] + d_in;
            for (i=2; i<=5; i=i+1) begin
                int_s[i] <= int_s[i] + int_s[i-1];
            end

            // check if we can output new data
            // at the decimated rate
            
            if (decimation_count == 3'd4)
            begin
                // update the comb filter states
                tmp[1] = int_s[5] - comb_s[1];
                comb_s[1] <= int_s[5];
                for (i=2; i<=5; i=i+1) begin
                    tmp[i] = tmp[i-1] - comb_s[i];
                    comb_s[i] <= tmp[i-1];
                end

                decimation_count <= 0;
                d_out_valid <= 1'b1;
                d_out <= tmp[5];
            end;
        end;
    end

endmodule