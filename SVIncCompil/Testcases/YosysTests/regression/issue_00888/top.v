module top (CLK, CE, SEL, SI, DO);
parameter SELWIDTH = 1;
parameter DATAWIDTH = 2;
input    CLK, CE;
input [DATAWIDTH-1:0] SI;
input [SELWIDTH-1:0] SEL;
output [DATAWIDTH-1:0] DO;
localparam DATADEPTH = 2**SELWIDTH;
reg [0:DATADEPTH-1] data1 [DATAWIDTH-1:0];
reg [DATADEPTH-1:0] data2 [DATAWIDTH-1:0];

generate
    genvar i;
    for (i = 0; i < DATAWIDTH; i=i+1) begin
        always @(posedge CLK)
        begin
            if (CE == 1'b1) begin
`ifdef BROKEN
                data1[i] <= {SI[i], data1[i][0:DATADEPTH-2]};
`else
                data2[i] <= {data2[i][DATADEPTH-2:0], SI[i]};
`endif
            end
        end
`ifdef BROKEN
        assign DO[i] = data1[i][SEL];
`else
        assign DO[i] = data2[i][SEL];
`endif
    end
endgenerate
endmodule
