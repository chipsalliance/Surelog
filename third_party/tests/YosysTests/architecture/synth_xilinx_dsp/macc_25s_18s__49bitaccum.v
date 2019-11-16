(* top *)
module macc_25s_18s__49bitaccum #(parameter AW=25, BW=18, AREG=0, BREG=0, MREG=0) (input clk, CEA, CEB, CEM, CEP, input signed [AW-1:0] A, input signed [BW-1:0] B, output reg signed [49-1:0] P);
reg signed [AW-1:0] Ar;
reg signed [BW-1:0] Br;
reg signed [AW+BW-1:0] Mr;
generate
    if (AREG) begin
        always @(posedge clk) if (1) Ar <= A;
    end
    else
        always @* Ar <= A;
    if (BREG) begin
        always @(posedge clk) if (1) Br <= B;
    end
    else
        always @* Br <= B;
    if (MREG) begin
        always @(posedge clk) if (1) Mr <= Ar * Br;
    end
    else
        always @* Mr <= Ar * Br;
    always @(posedge clk) if (1) P <= P + Mr;
endgenerate
endmodule

`ifndef _AUTOTB
module __test ;
    wire [4095:0] assert_area = "cd macc_25s_18s__49bitaccum; select t:DSP48E1 -assert-count 1; select t:FD* -assert-count 49; select t:XORCY -assert-count 49; select t:LUT2 -assert-count 97";
endmodule
`endif

