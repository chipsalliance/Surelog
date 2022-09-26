module dut(input clk, output logic [31:0] data[4][4]);
    always @(posedge clk) begin
        foreach(data[i])
            foreach(data[i][j])
                data[i][j] = i * j;
    end
endmodule

module top(input clk, output bit [1:0][3:0] B [3:0][2]);
    always @(posedge clk) begin
        foreach(B[q, r, , s]) begin
            B[q][r][0][s] = r;
            B[q][r][1][s] = 0;
        end
    end
endmodule // top
